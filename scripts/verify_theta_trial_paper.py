"""Rebuild the theta-trial-paper development and its local dependencies.

The claim map identifies the paper's formal statements. Verification requires
a source-manifest check, rebuild, axiom audit, and complete kernel replay.
The paper itself is not bundled; --paper optionally checks an external TeX
file against the map's expected manuscript hash and complete claim-label set.
Run from any directory after fetching the pinned mathlib dependency cache.
All output is written under this repository's build/verification directory.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re
import subprocess
import sys
import shutil
import threading
import time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "build/verification"
COVERAGE = ROOT / "verification/coverage.json"
SOURCE_MANIFEST = ROOT / "verification/source_manifest.json"
PROJECT_PREFIX = "ThetaTrial"
PREFIX = PROJECT_PREFIX + ".Paper"
PAPER_DIR = ROOT.joinpath(*PREFIX.split("."))
EXPECTED_LABELS = {
    "deriv:archimedean", "deriv:exact-modes", "deriv:first-mode-tail", "deriv:full-tail",
    "deriv:laguerre-moment", "deriv:log-uncertainty", "deriv:main", "deriv:pole-primes",
    "deriv:weighted-l1", "avg:contour", "avg:factorization", "avg:interior",
    "avg:large-space", "avg:main", "avg:spaces", "pre:bv", "pre:form",
    "pre:radical", "pre:theta",
}
LEAN_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*")


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate_claim_map(coverage):
    """Validate the fixed paper label set and safe, nonempty Lean references."""
    if not re.fullmatch(r"[0-9a-f]{64}", coverage.get("paper_sha256", "")):
        raise RuntimeError("Claim map has no valid expected manuscript SHA-256")
    claims = coverage.get("claims", [])
    labels = [claim.get("label") for claim in claims]
    if len(labels) != len(EXPECTED_LABELS) or set(labels) != EXPECTED_LABELS:
        raise RuntimeError("Claim map must contain exactly the paper's 19 distinct claim labels")
    theorems = set()
    for claim in claims:
        references = claim.get("theorems", [])
        if not isinstance(references, list) or not references:
            raise RuntimeError(f"No theorem references for {claim['label']}")
        for name in references:
            if not isinstance(name, str) or not LEAN_NAME.fullmatch(name):
                raise RuntimeError(f"Invalid theorem reference for {claim['label']}: {name!r}")
        if len(references) != len(set(references)):
            raise RuntimeError(f"Duplicate theorem reference for {claim['label']}")
        theorems.update(references)
        for name in claim.get("modules", []):
            if not isinstance(name, str) or not LEAN_NAME.fullmatch(name):
                raise RuntimeError(f"Invalid module reference for {claim['label']}: {name!r}")
    return sorted(theorems)


def validate_external_manuscript(path, expected_sha256):
    if sha(path) != expected_sha256:
        raise RuntimeError("External manuscript does not match the claim map's expected SHA-256")
    labels = re.findall(
        r"\\begin\{(?:theorem|lemma|proposition|corollary)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}",
        path.read_text(encoding="utf-8"))
    if len(labels) != len(EXPECTED_LABELS) or set(labels) != EXPECTED_LABELS:
        raise RuntimeError("External manuscript labels do not exactly match the paper's 19 claims")


def strip_comments_strings(text):
    """Mask nested Lean comments and strings for a conservative token scan."""
    out = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(" ")
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise RuntimeError("Unclosed source comment")
    return "".join(out)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--jobs", type=int, default=3, choices=range(1, 5))
    parser.add_argument("--paper", type=Path,
        help="Optionally check an external manuscript TeX file against the expected hash and claim labels")
    parser.add_argument("--resume-build", action="store_true",
        help="Reuse only a complete previous rebuild after checking every frozen source and object hash")
    args = parser.parse_args()
    if hasattr(sys.stdout, "reconfigure"):
        sys.stdout.reconfigure(encoding="utf-8")
    OUT.mkdir(parents=True, exist_ok=True)
    previous = None
    previous_receipt = None
    if args.resume_build:
        previous = json.loads((OUT / "report.json").read_text(encoding="utf-8"))
        stamp = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%SZ")
        previous_receipt = OUT / f"previous_rebuild_{stamp}.json"
        for run_info in previous.get("runs", []):
            if run_info["exit_code"] != 0:
                old_log = ROOT / run_info["log"]
                saved_log = OUT / f"{run_info['label']}_failed_{stamp}.log"
                if old_log.exists():
                    shutil.copyfile(old_log, saved_log)
                    run_info["log"] = saved_log.relative_to(ROOT).as_posix()
        previous_receipt.write_text(json.dumps(previous, indent=2), encoding="utf-8")
    report = {
        "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "formalization_verified": False,
        "external_manuscript_checked": False,
        "coverage_is_separate_from_compile_status": True,
        "modules": {}, "runs": [], "status": "running",
    }
    modules = {}
    deps = {}
    initial = {}
    seen = set()
    ordered = []
    visiting = set()

    def visit(name):
        if name in seen:
            return
        if name in visiting:
            raise RuntimeError(f"Import cycle at {name}")
        visiting.add(name)
        path = ROOT.joinpath(*name.split(".")).with_suffix(".lean")
        if not path.exists():
            raise RuntimeError(f"Missing project source: {name}")
        if name.startswith(PREFIX + ".") and (name not in paper_inventory):
            raise RuntimeError(f"Paper import not inventoried: {name}")
        modules[name] = path
        initial[name] = sha(path)
        code = strip_comments_strings(path.read_text(encoding="utf-8-sig"))
        bad = sorted(set(re.findall(r"\b(sorry|admit|axiom|unsafe|partial|native_decide|sorryAx)\b", code)))
        if bad and (name == PREFIX or name.startswith(PREFIX + ".")):
            raise RuntimeError(f"Forbidden source tokens {bad} in {path}")
        if bad:
            report.setdefault("inherited_source_scan_findings", {})[name] = bad
        deps[name] = set()
        for line in code.splitlines():
            match = re.match(r"^\s*(?:(?:public|meta)\s+)*import\s+(.+)$", line)
            if match:
                for dep in match.group(1).split():
                    if dep == PROJECT_PREFIX or dep.startswith(PROJECT_PREFIX + "."):
                        deps[name].add(dep)
                        visit(dep)
        visiting.remove(name)
        seen.add(name)
        ordered.append(name)

    runner = ROOT / "scripts/lean_check.py"

    def save():
        (OUT / "report.json").write_text(json.dumps(report, indent=2), encoding="utf-8")

    def execute(label, argv, env=None):
        print(label, flush=True)
        log = OUT / f"{label}.log"
        started = time.monotonic()
        with log.open("w", encoding="utf-8") as output:
            with subprocess.Popen([sys.executable, "-u", str(runner), *argv], cwd=ROOT,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                    encoding="utf-8", errors="replace", env=env, bufsize=1) as proc:
                reader_errors = []

                def drain_output():
                    try:
                        for line in proc.stdout:
                            output.write(line)
                            output.flush()
                            if label == "kernel_replay":
                                print(line, end="", flush=True)
                    except Exception as exc:
                        reader_errors.append(exc)
                        proc.terminate()

                reader = threading.Thread(target=drain_output, daemon=True)
                reader.start()
                while True:
                    try:
                        returncode = proc.wait(timeout=30)
                        break
                    except subprocess.TimeoutExpired:
                        print(f"{label}: still running ({time.monotonic() - started:.0f}s)", flush=True)
                reader.join()
                if reader_errors:
                    raise RuntimeError(f"Could not capture output for {label}") from reader_errors[0]
        return label, returncode, log, log.read_text(encoding="utf-8")

    def record(result):
        label, returncode, log, output = result
        report["runs"].append({"label": label, "exit_code": returncode,
            "log": log.relative_to(ROOT).as_posix()})
        save()
        if returncode:
            print(output[-12000:], flush=True)
            raise RuntimeError(f"Failed: {label}")
        return output

    def run(label, argv, env=None):
        return record(execute(label, argv, env))

    save()
    try:
        report["toolchain"] = (ROOT / "lean-toolchain").read_text().strip()
        report["lake_manifest_sha256"] = sha(ROOT / "lake-manifest.json")
        verifier_files = [Path(__file__).resolve(), runner,
            ROOT / "scripts/ReplayThetaPaper.lean", ROOT / "lakefile.toml"]
        report["verification_tool_hashes"] = {
            p.relative_to(ROOT).as_posix(): sha(p) for p in verifier_files}
        report["coverage_sha256"] = sha(COVERAGE)
        report["coverage"] = json.loads(COVERAGE.read_text(encoding="utf-8"))
        mapped_theorems = validate_claim_map(report["coverage"])
        report["paper_sha256"] = report["coverage"]["paper_sha256"]
        report["paper_sha256_origin"] = "Expected manuscript hash recorded in the claim map"
        report["mapped_paper_claims"] = sorted(EXPECTED_LABELS)
        report["mapped_theorem_references"] = len(mapped_theorems)
        if args.paper is not None:
            validate_external_manuscript(args.paper, report["paper_sha256"])
            report["external_manuscript_sha256"] = report["paper_sha256"]
            report["external_manuscript_checked"] = True
        report["source_manifest_sha256"] = sha(SOURCE_MANIFEST)
        source_manifest = json.loads(SOURCE_MANIFEST.read_text(encoding="utf-8"))
        if source_manifest.get("paper_sha256") != report["paper_sha256"]:
            raise RuntimeError("Source manifest and claim map identify different manuscript hashes")
        if source_manifest.get("lean_toolchain") != report["toolchain"]:
            raise RuntimeError("Source manifest and installed project specify different Lean toolchains")
        lake_manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
        mathlib_revisions = [p["rev"] for p in lake_manifest["packages"] if p["name"] == "mathlib"]
        if mathlib_revisions != [source_manifest.get("mathlib_revision")]:
            raise RuntimeError("Source manifest and dependency manifest specify different Mathlib revisions")
        paper_inventory = {f"{PREFIX}.{p.stem}" for p in
            PAPER_DIR.glob("*.lean")}
        if not paper_inventory:
            raise RuntimeError("No paper modules found")
        for name in sorted(paper_inventory):
            visit(name)
        # Preserve every proof source byte-for-byte, including the entry point.
        visit(PREFIX)
        if deps[PREFIX] != paper_inventory:
            raise RuntimeError("Entry-point imports do not exactly match the paper module inventory")
        for claim in report["coverage"]["claims"]:
            if any(f"{PREFIX}.{name}" not in paper_inventory for name in claim.get("modules", [])):
                raise RuntimeError(f"Claim map references a missing paper module: {claim['label']}")
        frozen_sources = source_manifest.get("sources", {})
        actual_sources = {path.relative_to(ROOT).as_posix(): initial[name]
                          for name, path in modules.items()}
        if source_manifest.get("source_count") != len(frozen_sources):
            raise RuntimeError("Source manifest count does not match its source inventory")
        if frozen_sources != actual_sources:
            raise RuntimeError("Source manifest hashes/inventory do not match the exact paper import closure")
        report["source_manifest_verified"] = True
        report["initial_source_hashes"] = initial
        report["project_import_graph"] = {k: sorted(v) for k, v in deps.items()}
        report["compile_jobs"] = args.jobs
        report["rebuild_scope"] = "All recursively imported ThetaTrial project sources; Mathlib remains the pinned compiled dependency baseline."
        save()
        pending = set(ordered)
        completed = set()
        running = {}
        if previous is not None:
            for field in ["paper_sha256", "coverage_sha256", "source_manifest_sha256",
                          "external_manuscript_checked", "external_manuscript_sha256",
                          "toolchain", "lake_manifest_sha256",
                          "initial_source_hashes", "project_import_graph", "verification_tool_hashes"]:
                if previous.get(field) != report.get(field):
                    raise RuntimeError(f"Cannot resume changed rebuild input: {field}")
            if set(previous.get("modules", {})) != set(modules):
                raise RuntimeError("Cannot resume an incomplete or different project rebuild")
            for name, info in previous["modules"].items():
                if info["source"] != modules[name].relative_to(ROOT).as_posix() or info["source_sha256"] != initial[name]:
                    raise RuntimeError(f"Inconsistent previous source receipt: {name}")
                if sha(ROOT / info["source"]) != info["source_sha256"]:
                    raise RuntimeError(f"Cannot resume changed source: {name}")
                dest = ROOT.joinpath(".lake/build/lib/lean", *name.split(".")).with_suffix(".olean")
                parts = {p.relative_to(ROOT).as_posix() for p in
                    [dest, Path(str(dest) + ".server"), Path(str(dest) + ".private")] if p.exists()}
                if parts != set(info["objects"]):
                    raise RuntimeError(f"Cannot resume changed object inventory: {name}")
                for path, checksum in info["objects"].items():
                    if sha(ROOT / path) != checksum:
                        raise RuntimeError(f"Cannot resume changed object: {path}")
            compile_runs = [ri for ri in previous["runs"] if ri["label"] in modules]
            if any(ri["exit_code"] != 0 for ri in compile_runs) or {ri["label"] for ri in compile_runs} != set(modules):
                raise RuntimeError("Cannot resume without all successful compile receipts")
            report["modules"] = previous["modules"]
            report["runs"] = compile_runs
            report["rebuild_reused_after_full_hash_validation"] = {
                "receipt": previous_receipt.relative_to(ROOT).as_posix(),
                "receipt_sha256": sha(previous_receipt),
                "original_started_utc": previous["started_utc"],
                "reason": "Resume the audit/replay stage; all proof sources and compiled objects are unchanged."}
            pending.clear()
            completed = set(ordered)
            save()
            print(f"REUSED_VERIFIED_REBUILD modules={len(completed)} (all source/object hashes rechecked)", flush=True)
        with ThreadPoolExecutor(max_workers=args.jobs) as pool:
            while pending or running:
                ready = sorted(name for name in pending if deps[name] <= completed)
                for name in ready[:args.jobs - len(running)]:
                    path = modules[name]
                    if sha(path) != initial[name]:
                        raise RuntimeError(f"Source changed before compile: {name}")
                    dest = ROOT.joinpath(".lake/build/lib/lean", *name.split(".")).with_suffix(".olean")
                    dest.parent.mkdir(parents=True, exist_ok=True)
                    future = pool.submit(execute, name,
                        [str(path.relative_to(ROOT)), "-j2", "-o", str(dest)])
                    running[future] = (name, dest)
                    pending.remove(name)
                if not running:
                    raise RuntimeError(f"Unresolved import dependencies: {sorted(pending)}")
                done, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in done:
                    name, dest = running.pop(future)
                    record(future.result())
                    path = modules[name]
                    if sha(path) != initial[name]:
                        raise RuntimeError(f"Source changed while compiling {name}; rerun")
                    report["modules"][name] = {"source": path.relative_to(ROOT).as_posix(),
                        "source_sha256": initial[name], "olean_sha256": sha(dest),
                        "objects": {p.relative_to(ROOT).as_posix(): sha(p) for p in
                            [dest, Path(str(dest) + ".server"), Path(str(dest) + ".private")]
                            if p.exists()},
                        "paper_module": name == PREFIX or name in paper_inventory}
                    completed.add(name)
                    save()
        audit = OUT / "PaperAudit.lean"
        coverage_checks = "\n".join(f"#check {PREFIX}." + theorem
                                    for theorem in mapped_theorems)
        audit.write_text('''import ThetaTrial.Paper
import Lean.Util.CollectAxioms
import Lean.Elab.Command

''' + coverage_checks + '''

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut names : Array Name := #[]
  for (name, _) in env.constants do
    let paperModule := match env.getModuleIdxFor? name with
      | some idx => (`ThetaTrial.Paper).isPrefixOf env.header.moduleNames[idx]!
      | none => false
    if paperModule then names := names.push name
  names := names.qsort Name.lt
  let mut count : Nat := 0
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Disallowed logical dependency: {name} uses {ax}"
    let some info := env.find? name | throwError "Missing declaration {name}"
    if info.isTheorem then
      count := count + 1
      logInfo m!"THETA_THEOREM {name} AXIOMS {axioms}"
      logInfo m!"THETA_STATEMENT {name} : {info.type}"
  if count == 0 then throwError "No paper theorems found"
  logInfo m!"THETA_AXIOM_AUDIT_PASS theorems={count} declarations={names.size}"
''', encoding="utf-8")
        audit_text = run("axiom_audit", [str(audit), "-j2"])
        counts = re.findall(r"^THETA_AXIOM_AUDIT_PASS theorems=(\d+) declarations=(\d+)\s*$",
                            audit_text, re.MULTILINE)
        if len(counts) != 1 or int(counts[0][0]) == 0:
            raise RuntimeError("Missing or inconsistent audit success marker")
        report["paper_theorems_audited"] = int(counts[0][0])
        report["paper_declarations_audited"] = int(counts[0][1])
        report["mapped_theorem_references_checked"] = len(mapped_theorems)
        report["allowed_logical_axioms"] = ["propext", "Classical.choice", "Quot.sound"]
        replay = run("kernel_replay", ["scripts/ReplayThetaPaper.lean", "-j2"])
        replay_pass = re.findall(r"^THETA_KERNEL_REPLAY_PASS modules=(\d+)\s*$", replay, re.MULTILINE)
        if replay_pass != [str(len(modules))]:
            raise RuntimeError("Missing or inconsistent kernel replay success marker")
        replay_list = re.findall(r"^THETA_REPLAY_CHECKED (\S+)\s*$", replay, re.MULTILINE)
        replayed = set(replay_list)
        if len(replay_list) != len(replayed) or replayed != set(modules):
            raise RuntimeError(f"Replay inventory mismatch: missing={set(modules)-replayed}, extra={replayed-set(modules)}")
        report["project_modules_replayed"] = len(replayed)
        final_inventory = {f"{PREFIX}.{p.stem}" for p in
            PAPER_DIR.glob("*.lean")}
        if final_inventory != paper_inventory:
            raise RuntimeError("Paper source inventory changed during verification")
        for name, info in report["modules"].items():
            if sha(ROOT / info["source"]) != info["source_sha256"]:
                raise RuntimeError(f"Source changed after compile: {name}; rerun")
            for path, checksum in info["objects"].items():
                if sha(ROOT / path) != checksum:
                    raise RuntimeError(f"Compiled object changed after compile: {path}")
            dest = ROOT.joinpath(".lake/build/lib/lean", *name.split(".")).with_suffix(".olean")
            parts = {p.relative_to(ROOT).as_posix() for p in
                [dest, Path(str(dest) + ".server"), Path(str(dest) + ".private")] if p.exists()}
            if parts != set(info["objects"]):
                raise RuntimeError(f"Compiled object-part inventory changed: {name}")
        for path, checksum in report["verification_tool_hashes"].items():
            if sha(ROOT / path) != checksum:
                raise RuntimeError(f"Verification tool changed: {path}")
        if args.paper is not None and sha(args.paper) != report["external_manuscript_sha256"]:
            raise RuntimeError("External manuscript changed during verification; rerun")
        if sha(COVERAGE) != report["coverage_sha256"]:
            raise RuntimeError("Coverage changed during verification; rerun")
        if sha(SOURCE_MANIFEST) != report["source_manifest_sha256"]:
            raise RuntimeError("Source manifest changed during verification; rerun")
        if (ROOT / "lean-toolchain").read_text().strip() != report["toolchain"]:
            raise RuntimeError("Lean toolchain changed during verification")
        if sha(ROOT / "lake-manifest.json") != report["lake_manifest_sha256"]:
            raise RuntimeError("Dependency manifest changed during verification")
        report["status"] = "passed"
        report["kernel_replay_performed"] = True
        report["formalization_verified"] = True
    except Exception as exc:
        report["status"] = "failed"
        report["error"] = str(exc)
        raise
    finally:
        report["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()
    print("THETA_MODULE_VERIFICATION_PASS", flush=True)


if __name__ == "__main__":
    main()
