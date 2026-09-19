/-
  Phase12PW_D15C4_PhaseA_IndependentCrossingSourceAttack.lean

  Binary Goldbach research program
  Phase12PW / D15C4 / Phase A

  INDEPENDENT CROSSING SOURCE ATTACK — EXACT SIGNED REMAINDER NORMAL FORM
  =======================================================================

  THIS IS NOT A NEW CAMPAIGN STAGE.

  PURPOSE
  -------
  The direct signed Level-4 implication is already GREEN in

      Phase12PW_D15C4_PhaseA_IndependentCrossingStrike.lean.

  Its remaining source proposition uses two existential real budgets

      BResidual, BRest.

  This file removes that slack.  We choose

      BResidual := || exact uncovered Type-II residual ||

  and define the correlated signed remainder exactly by

      Rsigned
        :=
      (FULL VAUGHAN - VAUGHAN-TO-PRIME CORRECTION)
        - Re(c4 hyperbolic source object).

  Therefore

      FULL VAUGHAN - CORRECTION
        =
      Re(c4 hyperbolic source object) + Rsigned

  identically, and hence

      |FULL VAUGHAN - CORRECTION|
        <=
      ||c4 hyperbolic source object|| + |Rsigned|.

  No |Vaughan| + |correction| split occurs.

  The remaining per-N analytic target is consequently the single sharp budget

      Bc4
        + || exact Type-II residual ||
        + | exact correlated signed remainder |
      <
      ACTUAL MAJOR.

  STATUS DISCIPLINE
  -----------------
  This file does NOT prove the external Phase-A source interfaces and does NOT
  prove the final sharp budget.  It proves that those genuine analytic inputs,
  once supplied, discharge D15C4PhaseAIndependentCrossingSource directly.

  No Goldbach positivity premise.
  No existing prime-pair premise.
  No sampled-N premise.
  No sorry / admit.
  No new axiom.
-/

import Goldbach.Phase12PW_D15C4_PhaseA_IndependentCrossingStrike
import Mathlib.Tactic

namespace Goldbach.Phase12PW

noncomputable section

open scoped BigOperators

/--
The exact correlated real signed object already identified with the actual
prime-log off-diagonal contribution by the GREEN D15C4F identity.
-/
noncomputable def d15c4PhaseAIndependentPrimeSigned
    (N : ℕ) : ℝ :=
  d15c4fFullSignedVaughanOffDiagonal N
    - d15c4fVaughanToPrimeCorrection N

/--
The real component of the exact source-faithful Vaughan-c4 hyperbolic object.
Its absolute value is bounded by the complex norm already controlled by the
GREEN Type-II machinery.
-/
noncomputable def d15c4PhaseAIndependentC4Real
    (N U V : ℕ)
    (α : ℝ) : ℝ :=
  (d15c4PhaseAVaughanC4HyperbolicSum
      N U V α).re

/--
Exact correlated remainder after removing the real c4 source contribution
from the signed prime-log off-diagonal object.

This is a DEFINITION, not a new analytic hypothesis.
-/
noncomputable def d15c4PhaseAIndependentExactSignedRest
    (N U V : ℕ)
    (α : ℝ) : ℝ :=
  d15c4PhaseAIndependentPrimeSigned N
    - d15c4PhaseAIndependentC4Real N U V α

/--
Exact signed decomposition.  No triangle inequality has yet been used.
-/
theorem d15c4_phaseA_independent_signed_exact_decomposition
    (N U V : ℕ)
    (α : ℝ) :
    d15c4PhaseAIndependentPrimeSigned N
      =
    d15c4PhaseAIndependentC4Real N U V α
      +
    d15c4PhaseAIndependentExactSignedRest
      N U V α := by
  unfold
    d15c4PhaseAIndependentExactSignedRest
  ring

/--
The sniper inequality follows from the EXACT correlated decomposition.

Crucially, the triangle inequality is used only AFTER Vaughan and the
Vaughan-to-prime correction have already been combined with their correct
sign.  We do NOT form |Vaughan| + |correction|.
-/
theorem d15c4_phaseA_independent_signed_sniper_of_exactRest
    (N U V : ℕ)
    (α : ℝ) :
    |d15c4fFullSignedVaughanOffDiagonal N
        - d15c4fVaughanToPrimeCorrection N|
      ≤
    ‖d15c4PhaseAVaughanC4HyperbolicSum
        N U V α‖
      +
    |d15c4PhaseAIndependentExactSignedRest
        N U V α| := by

  change
    |d15c4PhaseAIndependentPrimeSigned N|
      ≤
    ‖d15c4PhaseAVaughanC4HyperbolicSum N U V α‖
      +
    |d15c4PhaseAIndependentExactSignedRest N U V α|

  rw [
    d15c4_phaseA_independent_signed_exact_decomposition
      N U V α
  ]

  calc
    |d15c4PhaseAIndependentC4Real N U V α
        +
      d15c4PhaseAIndependentExactSignedRest N U V α|
        ≤
      |d15c4PhaseAIndependentC4Real N U V α|
        +
      |d15c4PhaseAIndependentExactSignedRest N U V α| := by
          have haUpper :
              d15c4PhaseAIndependentC4Real N U V α
                ≤
              |d15c4PhaseAIndependentC4Real N U V α| :=
            le_abs_self _
          have hbUpper :
              d15c4PhaseAIndependentExactSignedRest N U V α
                ≤
              |d15c4PhaseAIndependentExactSignedRest N U V α| :=
            le_abs_self _
          have haLower :
              -|d15c4PhaseAIndependentC4Real N U V α|
                ≤
              d15c4PhaseAIndependentC4Real N U V α := by
            have h :=
              le_abs_self
                (-d15c4PhaseAIndependentC4Real N U V α)
            have hn := neg_le_neg h
            simpa only [abs_neg, neg_neg] using hn
          have hbLower :
              -|d15c4PhaseAIndependentExactSignedRest N U V α|
                ≤
              d15c4PhaseAIndependentExactSignedRest N U V α := by
            have h :=
              le_abs_self
                (-d15c4PhaseAIndependentExactSignedRest N U V α)
            have hn := neg_le_neg h
            simpa only [abs_neg, neg_neg] using hn
          apply (abs_le).2
          constructor <;> linarith

    _ ≤
      ‖d15c4PhaseAVaughanC4HyperbolicSum N U V α‖
        +
      |d15c4PhaseAIndependentExactSignedRest N U V α| := by
          have hRe :
              |d15c4PhaseAIndependentC4Real N U V α|
                ≤
              ‖d15c4PhaseAVaughanC4HyperbolicSum N U V α‖ := by
            simpa [d15c4PhaseAIndependentC4Real] using
              (Complex.abs_re_le_norm
                (d15c4PhaseAVaughanC4HyperbolicSum
                  N U V α))
          linarith

/--
DIRECT SOURCE DISCHARGE FROM THE EXACT-REMAINDER BUDGET.

There are no arbitrary BResidual/BRest witnesses left in the premise.

For every target N we require:
  * the already-defined source-faithful c4 geometry;
  * ONE strict inequality using the exact residual norm and exact correlated
    signed remainder.

Those exact quantities are inserted into
D15C4PhaseAIndependentCrossingSource automatically.
-/
theorem d15c4_phaseA_independentSource_of_exactRemainderBudget
    (hSource : D15C4PhaseAAnalyticSource)
    (hPrefix : D15C4PhaseAPrefixAnalyticSource)
    (hPerN :
      ∀ N : ℕ,
        D15C3BLargeNMod6Two N →
          ∃
            (U V : ℕ)
            (blocks : Finset (ℕ × ℕ))
            (α : ℝ),

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

            d15c4PhaseAP2C4ControlledDyadicBudget
                N U blocks
                (d15c4PhaseAVaughanB U)
              +
            ‖d15c4PhaseAP2C4ResidualTypeIISum
                N U V blocks
                (d15c4PhaseAVaughanB U)
                α‖
              +
            |d15c4PhaseAIndependentExactSignedRest
                N U V α|
              <
            (goldbachMajorArcIntegral
              N 3 (d15c3Q N)).re) :
    D15C4PhaseAIndependentCrossingSource := by

  refine ⟨hSource, hPrefix, ?_⟩

  intro N hS

  rcases hPerN N hS with
    ⟨U, V, blocks, α,
      hInside, hPair, hArc,
      hK, hDyadic, hmFull, hmEdge,
      hBudget⟩

  refine
    ⟨U, V, blocks, α,
      ‖d15c4PhaseAP2C4ResidualTypeIISum
          N U V blocks
          (d15c4PhaseAVaughanB U)
          α‖,
      |d15c4PhaseAIndependentExactSignedRest
          N U V α|,
      hInside, hPair, hArc,
      hK, hDyadic, hmFull, hmEdge,
      ?_, ?_, ?_⟩

  · exact le_rfl

  · exact
      d15c4_phaseA_independent_signed_sniper_of_exactRest
        N U V α

  · exact hBudget

/--
HEADLINE DIRECT CROSSING FROM THE EXACT-REMAINDER BUDGET.

This merely composes the source discharge above with the already-GREEN
IndependentCrossingStrike theorem.  No intervening campaign gate is created.
-/
theorem d15c4_phaseA_INDEPENDENT_LEVEL4_of_exactRemainderBudget
    (hSource : D15C4PhaseAAnalyticSource)
    (hPrefix : D15C4PhaseAPrefixAnalyticSource)
    (hPerN :
      ∀ N : ℕ,
        D15C3BLargeNMod6Two N →
          ∃
            (U V : ℕ)
            (blocks : Finset (ℕ × ℕ))
            (α : ℝ),

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

            d15c4PhaseAP2C4ControlledDyadicBudget
                N U blocks
                (d15c4PhaseAVaughanB U)
              +
            ‖d15c4PhaseAP2C4ResidualTypeIISum
                N U V blocks
                (d15c4PhaseAVaughanB U)
                α‖
              +
            |d15c4PhaseAIndependentExactSignedRest
                N U V α|
              <
            (goldbachMajorArcIntegral
              N 3 (d15c3Q N)).re) :
    D15C4CLevel4Crossing := by

  apply d15c4_phaseA_INDEPENDENT_LEVEL4

  exact
    d15c4_phaseA_independentSource_of_exactRemainderBudget
      hSource hPrefix hPerN

/-!
AUDIT
-/

#check d15c4PhaseAIndependentPrimeSigned
#check d15c4PhaseAIndependentC4Real
#check d15c4PhaseAIndependentExactSignedRest
#check d15c4_phaseA_independent_signed_exact_decomposition
#check d15c4_phaseA_independent_signed_sniper_of_exactRest
#check d15c4_phaseA_independentSource_of_exactRemainderBudget
#check d15c4_phaseA_INDEPENDENT_LEVEL4_of_exactRemainderBudget

#print axioms d15c4_phaseA_independent_signed_exact_decomposition
#print axioms d15c4_phaseA_independent_signed_sniper_of_exactRest
#print axioms d15c4_phaseA_independentSource_of_exactRemainderBudget
#print axioms d15c4_phaseA_INDEPENDENT_LEVEL4_of_exactRemainderBudget

end

end Goldbach.Phase12PW
