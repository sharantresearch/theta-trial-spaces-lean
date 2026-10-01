# Imported files from anthropics/formal-math

`ThetaTrial/Imported/Zeta23/` contains the files of
[anthropics/formal-math](https://github.com/anthropics/formal-math) (tag `v1.0`,
commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, Apache-2.0) that this
formalization needs, mainly for the Weil explicit formula. The original
license, notices and copyright headers are kept.

Changes from upstream:

- **Import paths.** Imports were moved from `Zeta23` to
  `ThetaTrial.Imported.Zeta23`; declaration namespaces are unchanged.
- **Deprecated names.** Upstream builds with Lean `v4.33.0-rc2`; this
  repository uses Lean 4.33.0 and Mathlib `db584cd`. A few deprecated Mathlib
  aliases were replaced by their current names (for example `mem_setOf_eq` by
  `mem_ofPred_eq`).
- **One extracted lemma.** `Tail/LocalCount.lean` contains the unchanged proof
  of `LocalCount.ofWindowCount`, extracted from the larger `Tail` module, and
  `WeilEF.GoodHeights` and `WeilEF.ZeroSummability` import it from there.

[`zeta23_port_manifest.json`](zeta23_port_manifest.json) lists every imported
file with its original and current SHA-256 hash, and each replacement made.
