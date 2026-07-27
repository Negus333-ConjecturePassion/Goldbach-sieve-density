import Goldbach.Phase4d_EulerMaclaurinBound
import Goldbach.Phase4e_LogPolynomialGrowth

-- ==========================================
-- PHASE 4f: Combining Phase4d + Phase4e
-- (Modularized Solution Effort)
-- ==========================================
--
-- HONEST SCOPE NOTE: This does NOT produce MinorArcStrictlyDominated
-- (which requires dominance for ALL n >= 8). exists_N0_log_polynomial_
-- dominance only pins down SOME N0 for which EventualLogPolynomialDominance
-- holds -- it does not guarantee N0 = 8, so this combination yields
-- dominance for n >= N0 only, leaving the finitely many n in [8, N0)
-- unaddressed. That gap is real, not a Lean artifact, and is separate
-- from the still-fully-open ErrorTermPolynomialBound itself.

theorem errorTermBound_implies_eventual_dominance
    (C α : ℝ) (hC : 0 ≤ C) (hα : α < 1)
    (hbound : ErrorTermPolynomialBound C α) :
    ∃ N0 : ℕ, 8 ≤ N0 ∧
      ∀ (n : ℕ), IsValidEven n → N0 ≤ n → |errorTerm n| < MajorArcTerm n := by
  obtain ⟨N0, hN0⟩ := exists_N0_log_polynomial_dominance C α hC hα
  refine ⟨max N0 8, le_max_right _ _, ?_⟩
  have hgrowth : EventualLogPolynomialDominance C α (max N0 8) := by
    intro n hn
    exact hN0 n (le_trans (le_max_left _ _) hn)
  exact errorTermBound_implies_dominance C α (max N0 8) (le_max_right _ _) hbound hgrowth