# Provenance

The files outside `ThetaTrial/Imported/` were written by Sharan Thota, with AI
assistance as described in the acknowledgments of the paper.

`ThetaTrial/Imported/Zeta23/` contains a subset of
[anthropics/formal-math](https://github.com/anthropics/formal-math), tag `v1.0`,
commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`, used under the Apache License
2.0. The original copyright headers, `LICENSE` and `NOTICE` are kept. The changes
from upstream are:

- imports were moved from `Zeta23` to `ThetaTrial.Imported.Zeta23` (declaration
  namespaces are unchanged), and an attribution header was added to each file;
- a few deprecated Mathlib names were replaced by their current equivalents, so
  the files build with Lean 4.33.0 and the Mathlib commit pinned here;
- the lemma `LocalCount.ofWindowCount` was moved, unchanged, into its own file
  `Tail/LocalCount.lean`, so that the rest of `Tail` is not needed.

`ThetaTrial/XiZeros.lean` contains a shorter proof, adapted from
`analyticOrderNatAt_xi` upstream, that `ξ` and `ζ` have the same zeros with the
same multiplicities.

[docs/ZETA23_PORT_STATUS.md](docs/ZETA23_PORT_STATUS.md) describes the port, and
[docs/zeta23_port_manifest.json](docs/zeta23_port_manifest.json) lists every
imported file with its original and current SHA-256 hash and each edit made.
