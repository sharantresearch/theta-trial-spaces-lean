# Theta trial spaces: Lean formalization

This repository contains a Lean 4 formalization of the paper

> Sharan Thota, *Explicit theta trial spaces for the truncated Weil quadratic form*.

The paper studies the Weil quadratic form `Q` restricted to functions supported
in an interval `[-a, a]`, and builds explicit trial functions from the Riemann
theta density `Φ` (the even function whose Fourier transform is
`Ξ(z) = ξ(1/2 + iz)`).

- **Theta averages (Section 3).** An imaginary-shift average of `Φ` with a von
  Mises weight, cut off to `[-a, a]`, has `|Q(f)| ≤ C exp(-4π e^{2a} + 34a) ‖f‖²`.
  Polynomial derivatives of the average give spaces of dimension of order
  `e^{2a}/a` on which `|Q|` is similarly small.
- **Theta derivatives (Section 4).** On the truncations of `P(D)Φ`, for complex
  polynomials `P` of degree up to `c e^a`, the form `Q` is positive definite.

Both constructions rest on a truncation identity: if the Fourier transform of
`F` is divisible by `Ξ`, then `F` cut off to `[-a, a]` and its exterior tail have
the same Weil energy. None of the results assume the Riemann hypothesis.

Every lemma, proposition, theorem and corollary of the paper (Lemma 2.1
through Lemma 4.9) is proved here, as are the eigenvalue bounds of Remark 3.7.
[`verification/coverage.json`](verification/coverage.json) lists, for each
result, the Lean theorems that prove it. The main ones are:

| Paper | Lean theorem |
|---|---|
| Proposition 2.4 (truncation identity) | `ThetaTrial.Paper.polynomialDerivative_theta_hardCutoff`, `ThetaTrial.Paper.ComplexShiftMeasure.polynomial_hardCutoff` |
| Theorem 3.1 | `ThetaTrial.Paper.thetaAvg_main` |
| Theorem 3.5 | `ThetaTrial.Paper.thetaAvg_spaces` |
| Corollary 3.6 | `ThetaTrial.Paper.thetaAvg_large_space` |
| Theorem 4.1 | `ThetaTrial.Paper.thetaDeriv_main` |

## Layout

- `ThetaTrial/Paper/`: the proofs of the paper's results. Files named
  `ThetaAvg*` belong to Section 3, `ThetaDeriv*` to Section 4.
  `ThetaTrial/Paper.lean` imports all of them.
- `ThetaTrial/` (other files): supporting material on the xi function, the
  theta series, digamma, the gamma factor and the explicit formula.
- `ThetaTrial/Imported/Zeta23/`: a subset of
  [anthropics/formal-math](https://github.com/anthropics/formal-math), which
  provides the Weil explicit formula and related analytic facts. See
  [PROVENANCE.md](PROVENANCE.md).
- `verification/`: the result-to-theorem map and the hashes of all sources.
- `scripts/`: the verification script, which CI runs on every push.

## Building

Install [elan](https://github.com/leanprover/elan), then run

```sh
lake exe cache get
lake build
```

The project uses Lean 4.33.0 and Mathlib commit `db584cd`, both pinned in
`lean-toolchain` and `lake-manifest.json`.

## Verification

```sh
python scripts/verify_theta_trial_paper.py --jobs 1
```

This script (Python 3.10 or later):

- checks the sources against `verification/source_manifest.json`;
- rebuilds every module;
- checks that each theorem listed in `coverage.json` exists;
- checks that the proofs use no axioms other than `propext`,
  `Classical.choice` and `Quot.sound`;
- replays every module through the Lean kernel.

It takes a while; `--jobs 3` is faster if you have the memory. Logs are written
to `build/verification/`.

To also check a copy of the paper's LaTeX source against the map, add
`--paper path/to/Theta_trial_spaces_for_the_Weil_form.tex`. The check compares
the file's SHA-256 hash with the one recorded in `coverage.json`, and its
theorem labels with the 19 labels in the map.

## Citing

Please cite the paper together with the commit or release of this repository
that you used; see [CITATION.cff](CITATION.cff). Licensing is described in
[LICENSING.md](LICENSING.md).
