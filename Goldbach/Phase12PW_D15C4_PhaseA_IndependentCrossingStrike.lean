/-
  Phase12PW_D15C4_PhaseA_IndependentCrossingStrike.lean

  Binary Goldbach research program
  Phase12PW / D15C4 / Phase A

  INDEPENDENT LEVEL-4 CROSSING — DIRECT SIGNED STRIKE
  ====================================================

  THIS IS NOT A NEW CAMPAIGN STAGE.

  The integrated closure architecture is already GREEN.
  This file states the one source theorem we now have to prove independently
  and connects it immediately to the Level-4 crossing.

  CRITICAL SHARPENING
  -------------------
  We DO NOT split

      FULL VAUGHAN
        and
      VAUGHAN-TO-PRIME CORRECTION

  by a final triangle inequality.

  Instead we preserve their exact signed combination

      FULL VAUGHAN - CORRECTION
        =
      ACTUAL PRIME-LOG OFF-DIAGONAL.

  The only new analytic remainder budget is therefore attached to the
  CORRELATED signed object:

      | (FULL VAUGHAN - CORRECTION) - c4_controlled_source |
        <= BRest

  in the weaker norm-envelope form used below:

      |FULL VAUGHAN - CORRECTION|
        <= ||c4_hyperbolic|| + BRest.

  The already-GREEN exact-b_U Type-II theorem supplies

      ||c4_hyperbolic|| <= Bc4 + BResidual.

  Hence the one strict budget

      Bc4 + BResidual + BRest < ACTUAL MAJOR

  fires the genuine D15C4 strict crossing.

  FIREWALL
  --------
  * no Goldbach diagonal positivity premise;
  * no primeLogGoldbachCorrelation positivity premise;
  * no existing prime pair premise;
  * no sampled-N positivity premise;
  * no separate |Vaughan| + |correction| budget;
  * no sorry / admit;
  * no new axiom.

  STATUS DISCIPLINE
  -----------------
  A clean build of this file proves only the implication

      INDEPENDENT SOURCE -> LEVEL-4 CROSSING.

  Level 4 becomes GREEN only when
  `D15C4PhaseAIndependentCrossingSource` itself is proved independently.
-/

import Goldbach.Phase12PW_D15C4_PhaseA_IntegratedLevel4Closure
import Mathlib.Tactic

namespace Goldbach.Phase12PW

noncomputable section

open scoped BigOperators

/--
THE ONE REMAINING INDEPENDENT LEVEL-4 SOURCE THEOREM.

The global Phase-A fixed-root and prefix sources are supplied once.
For every N in the already-selected large-N mod-6-two subclass, the theorem
must produce ONE source-faithful Type-II geometry together with:

  * an explicit residual Type-II budget;
  * ONE correlated signed remainder budget after Vaughan-to-prime translation;
  * ONE strict total budget below the actual major term.

Everything else is already GREEN infrastructure.
-/
def D15C4PhaseAIndependentCrossingSource : Prop :=
  D15C4PhaseAAnalyticSource
  ∧
  D15C4PhaseAPrefixAnalyticSource
  ∧
  ∀ N : ℕ,
    D15C3BLargeNMod6Two N →
      ∃
        (U V : ℕ)
        (blocks : Finset (ℕ × ℕ))
        (α : ℝ)
        (BResidual BRest : ℝ),

        D15C4PhaseAP2C4BlocksInsideFullSupport
          N V blocks
        ∧
        D15C4PhaseAP2C4BlocksPairwiseDisjoint
          blocks
        ∧
        D15C4PhaseAP2BaseArc N α
        ∧
        (∀ KK ∈ blocks,
          4309 ≤ KK.1)
        ∧
        (∀ KK ∈ blocks,
          KK.2 = 2 * KK.1 - 1)
        ∧
        (∀ KK ∈ blocks,
          ∀ m ∈ d15c4PhaseAP2C4FullM
              N U KK.2,
            d15c4PhaseAWeakMUpper N m)
        ∧
        (∀ KK ∈ blocks,
          ∀ m ∈ d15c4PhaseAP2C4ActiveEdgeM
              N U KK.1 KK.2,
            d15c4PhaseAWeakMUpper N m)
        ∧

        -- Exact uncovered Type-II support.
        ‖d15c4PhaseAP2C4ResidualTypeIISum
            N U V blocks
            (d15c4PhaseAVaughanB U)
            α‖
          ≤ BResidual
        ∧

        -- THE SIGNED SNIPER INEQUALITY.
        --
        -- Vaughan and the exact translation correction remain correlated.
        -- No |Vaughan| + |correction| split is permitted here.
        |d15c4fFullSignedVaughanOffDiagonal N
            - d15c4fVaughanToPrimeCorrection N|
          ≤
        ‖d15c4PhaseAVaughanC4HyperbolicSum
            N U V α‖
          + BRest
        ∧

        -- ONE final independent analytic budget.
        d15c4PhaseAP2C4ControlledDyadicBudget
            N U blocks
            (d15c4PhaseAVaughanB U)
          + BResidual
          + BRest
          <
        (goldbachMajorArcIntegral
          N 3 (d15c3Q N)).re

/--
DIRECT INDEPENDENT CROSSING.

Once the single source theorem above is discharged, the Level-4 crossing
follows immediately.  There is no intervening campaign gate.
-/
theorem d15c4_phaseA_INDEPENDENT_LEVEL4
    (hIndependent :
      D15C4PhaseAIndependentCrossingSource) :
    D15C4CLevel4Crossing := by

  intro N hS

  rcases hIndependent with
    ⟨hSource, hPrefix, hPerN⟩

  rcases hPerN N hS with
    ⟨U, V, blocks, α, BResidual, BRest,
      hInside, hPair, hArc,
      hK, hDyadic, hmFull, hmEdge,
      hResidual, hSigned, hBudget⟩

  let Bc4 : ℝ :=
    d15c4PhaseAP2C4ControlledDyadicBudget
      N U blocks
      (d15c4PhaseAVaughanB U)

  have hC4 :
      ‖d15c4PhaseAVaughanC4HyperbolicSum
          N U V α‖
        ≤
      Bc4 + BResidual := by
    dsimp [Bc4]
    exact
      d15c4_phaseA_sources_imply_vaughanB_c4Hyperbolic_bound
        hSource hPrefix
        N U V blocks
        α BResidual
        hInside hPair
        hArc hK hDyadic hmFull hmEdge
        hResidual

  have hPrimeAbs :
      |(goldbachMajorOffDiagonalKernelContribution
          N 3 (d15c3Q N)).re|
        ≤
      Bc4 + BResidual + BRest := by

    rw [
      d15c4f_actualPrimeOffDiagonal_eq_vaughan_sub_correction
        N
    ]

    calc
      |d15c4fFullSignedVaughanOffDiagonal N
          - d15c4fVaughanToPrimeCorrection N|
          ≤
        ‖d15c4PhaseAVaughanC4HyperbolicSum
            N U V α‖
          + BRest :=
            hSigned

      _ ≤
        (Bc4 + BResidual) + BRest := by
          exact add_le_add_left hC4 BRest

      _ =
        Bc4 + BResidual + BRest := by
          ring

  have hBudget' :
      Bc4 + BResidual + BRest
        <
      (goldbachMajorArcIntegral
        N 3 (d15c3Q N)).re := by
    simpa [Bc4] using hBudget

  have hPrimeLtMajor :
      (goldbachMajorOffDiagonalKernelContribution
          N 3 (d15c3Q N)).re
        <
      (goldbachMajorArcIntegral
          N 3 (d15c3Q N)).re := by

    have hSelf :
        (goldbachMajorOffDiagonalKernelContribution
            N 3 (d15c3Q N)).re
          ≤
        |(goldbachMajorOffDiagonalKernelContribution
            N 3 (d15c3Q N)).re| :=
      le_abs_self _

    linarith

  rcases hS with
    ⟨hEven, hN, hMod⟩

  have hPK :
      (3 : ℝ) ≤ ((3 : ℕ) : ℝ) := by
    norm_num

  have hglobal :
      2 * (3 : ℝ) ^ 2 < d15c3Q N :=
    d15c4c_global_packet_of_largeN N hN

  have hGap :
      0 < d15c_majorSideGap
        N 3 (d15c3Q N) := by
    unfold d15c_majorSideGap
    linarith

  rw [
    d15c_majorSideGap_eq_mod3Gain01_sub_residual2
      3 N 3 (d15c3Q N) hPK hglobal
  ] at hGap

  linarith

/--
Per-N endpoint, useful while attacking the source theorem one fixed N-symbol
at a time.
-/
theorem d15c4_phaseA_INDEPENDENT_LEVEL4_at
    (hIndependent :
      D15C4PhaseAIndependentCrossingSource)
    (N : ℕ)
    (hS : D15C3BLargeNMod6Two N) :
    d15c_mod3Residual2
        3 N 3 (d15c3Q N)
      <
    d15c_mod3Gain01
        3 N 3 (d15c3Q N) := by
  exact
    d15c4_phaseA_INDEPENDENT_LEVEL4
      hIndependent N hS

/-!
AUDIT
-/

#check D15C4PhaseAIndependentCrossingSource
#check d15c4_phaseA_INDEPENDENT_LEVEL4
#check d15c4_phaseA_INDEPENDENT_LEVEL4_at

#print axioms d15c4_phaseA_INDEPENDENT_LEVEL4
#print axioms d15c4_phaseA_INDEPENDENT_LEVEL4_at

end

end Goldbach.Phase12PW
