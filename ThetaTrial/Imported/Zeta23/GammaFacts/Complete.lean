/- Local port: module imports relocated under ThetaTrial.Imported.Zeta23.
Original: anthropics/formal-math tag v1.0, commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510.
Original authors and Apache-2.0 notices are retained below. Proof compatibility edits,
if any, are recorded in docs/ZETA23_PORT_STATUS.md. -/
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Complete.lean — assembly of H-Γ:
All nine fields of Zeta23.GammaFacts ([eq:mufacts] + the Γ-halves of [eq:muints])
are proved: even/smooth (Zeta23/GammaFacts.lean), monotoneOn/mu_zero_le/
neg_one_lt_mu_zero/deriv_bound (Zeta23/GammaFacts/Mu.lean, via the digamma
partial-fraction series), stirling (Zeta23/GammaFacts/StirlingVert.lean, C = 20/2π),
int_mu/int_mu_sq (Zeta23/GammaFacts/IntMu.lean, from stirling + FTC).
-/
import ThetaTrial.Imported.Zeta23.Hypotheses
import ThetaTrial.Imported.Zeta23.GammaFacts
import ThetaTrial.Imported.Zeta23.GammaFacts.Mu
import ThetaTrial.Imported.Zeta23.GammaFacts.IntMu
import ThetaTrial.Imported.Zeta23.GammaFacts.StirlingVert

noncomputable section

namespace Zeta23

/-- GammaFacts from any Stirling bound for μ (the only analytically deep field). -/
theorem gammaFacts_of_stirling (hst : MuInts.StirlingHyp) : GammaFacts :=
  ⟨mu_even, mu_smooth, MuFields.mu_monotoneOn, MuFields.mu_zero_le, MuFields.neg_one_lt_mu_zero,
    hst, MuFields.mu_deriv_bound, MuInts.int_mu_of_stirling hst, MuInts.int_mu_sq_of_stirling hst⟩

/-- **H-Γ, unconditionally.** -/
theorem gammaFacts : GammaFacts := gammaFacts_of_stirling StirlingVert.mu_stirling

end Zeta23
