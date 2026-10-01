import LeanChecker

/-! Replays every `ThetaTrial` module imported by `ThetaTrial.Paper` through the
Lean kernel, using `replayFromImports` from the pinned Lean distribution.
Progress is written to stderr, since `#eval` buffers stdout until it finishes. -/

set_option stderrAsMessages false

open Lean

private def replayProgress (message : String) : IO Unit := do
  let stream ← IO.getStderr
  stream.putStrLn message
  stream.flush

unsafe def replayThetaPaperProject : IO Unit := do
  initSearchPath (← findSysroot)
  let entry := `ThetaTrial.Paper
  withImportModules #[{module := entry}] {} fun env => do
    let modules := env.header.moduleNames.filter (fun name => (`ThetaTrial).isPrefixOf name)
    unless modules.contains entry do
      throw <| IO.userError "Paper entry absent from imported module inventory"
    for mod in modules do
      replayProgress s!"THETA_REPLAY_MODULE {mod}"
      replayFromImports mod
      replayProgress s!"THETA_REPLAY_CHECKED {mod}"
    replayProgress s!"THETA_KERNEL_REPLAY_PASS modules={modules.size}"

#eval replayThetaPaperProject
