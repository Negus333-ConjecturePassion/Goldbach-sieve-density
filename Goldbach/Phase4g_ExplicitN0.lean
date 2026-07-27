import Goldbach.Phase4d_EulerMaclaurinBound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==========================================
-- PHASE 4g: Explicit N0 via an elementary log bound
-- ==========================================
--
-- STATUS: Third iteration. Build 2 surfaced four remaining errors: (1) `simp`
-- alone (no args) left goal `0 < δ` unsolved in the x=1 case -- fixed with
-- `simpa using hδ`; (2) `le_refl (1:ℝ)` has type `1≤1`, not the required
-- `0≤1` -- replaced with `zero_le_one`; (3) `Real.rpow_le_rpow` was given
-- `0≤K` where it needed `0≤K^(2/(1-α))` -- fixed by inserting an explicit
-- `Real.rpow_nonneg` step; (4) a `ring` call failed because one side's
-- denominator was `((1-α)/4)*((1-α)/4)` and the other was `(1-α)^2` --
-- mathematically equal (both = (1-α)²/16) but not recognized as such by
-- `ring`, which does not automatically equate differently-scaled inverted
-- polynomials. Fixed by rewriting the denominator into the exact same shape
-- before calling ring, via a pure (inverse-free) `ring` fact plus
-- `div_div_eq_mul_div` (confirmed at Mathlib/Algebra/Group/Basic.lean:492).
--
-- PURPOSE: unchanged -- gives EventualLogPolynomialDominance an explicit,
-- computable N0(C, alpha) formula, replacing Phase4e's noncomputable
-- existence proof via Filter.atTop/isLittleO.

open Real

/-- Elementary bound: log x < x^δ / δ for all x > 0, δ > 0. -/
lemma log_lt_rpow_div (x δ : ℝ) (hx : 0 < x) (hδ : 0 < δ) :
    Real.log x < x ^ δ / δ := by
  rcases eq_or_ne x 1 with rfl | hx1
  · simpa using hδ
  · have hxδ_ne : x ^ δ ≠ 1 := by
      rcases lt_or_gt_of_ne hx1 with hlt | hgt
      · have h := (Real.rpow_lt_rpow_iff hx.le zero_le_one hδ).mpr hlt
        rw [Real.one_rpow] at h
        exact h.ne
      · have h := (Real.rpow_lt_rpow_iff (by norm_num : (0:ℝ) ≤ 1) hx.le hδ).mpr hgt
        rw [Real.one_rpow] at h
        exact h.ne'
    have h1 : Real.log (x ^ δ) < x ^ δ - 1 :=
      Real.log_lt_sub_one_of_pos (Real.rpow_pos_of_pos hx δ) hxδ_ne
    rw [Real.log_rpow hx] at h1
    rw [lt_div_iff₀ hδ, mul_comm]
    linarith

/-- Explicit N0 formula: closed-form, no existence quantifier. -/
noncomputable def explicitN0 (C α : ℝ) : ℕ :=
  max 8 ⌈(8 * C / ((1 - α) ^ 2 * twinPrimeConstant)) ^ (2 / (1 - α))⌉₊

theorem eventualLogPolynomialDominance_explicitN0
    (C α : ℝ) (hC : 0 ≤ C) (hα : α < 1) :
    EventualLogPolynomialDominance C α (explicitN0 C α) := by
  have htwin : 0 < twinPrimeConstant := Real.exp_pos _
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · intro n hn
    have hn8 : 8 ≤ n := le_trans (le_max_left _ _) hn
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    rw [← hC0]
    simp only [zero_mul]
    positivity
  · intro n hn
    have hε : 0 < 1 - α := by linarith
    have hε_ne : (1 - α) ≠ 0 := hε.ne'
    have hδ : 0 < (1 - α) / 4 := by linarith
    have hn8 : (8 : ℕ) ≤ n := le_trans (le_max_left _ _) hn
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have : (0:ℕ) < n := by omega
      exact_mod_cast this
    have hn1 : (1:ℝ) < (n:ℝ) := by
      have h8R : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
      linarith
    have hlogpos : 0 < Real.log n := Real.log_pos hn1
    have hstep1 : Real.log n < (n:ℝ) ^ ((1-α)/4) / ((1-α)/4) :=
      log_lt_rpow_div (n:ℝ) ((1-α)/4) hnR hδ
    have hpow_pos : 0 < (n:ℝ) ^ ((1-α)/4) / ((1-α)/4) :=
      div_pos (Real.rpow_pos_of_pos hnR _) hδ
    have hstep2 : (Real.log n) * (Real.log n)
        < ((n:ℝ) ^ ((1-α)/4) / ((1-α)/4)) * ((n:ℝ) ^ ((1-α)/4) / ((1-α)/4)) :=
      mul_lt_mul'' hstep1 hstep1 hlogpos.le hlogpos.le
    have hcombine : (n:ℝ) ^ ((1-α)/4) * (n:ℝ) ^ ((1-α)/4) = (n:ℝ) ^ ((1-α)/2) := by
      rw [← Real.rpow_add hnR]; ring_nf
    have hthreshold : (8 * C / ((1 - α) ^ 2 * twinPrimeConstant)) ^ (2 / (1 - α)) ≤ (n:ℝ) := by
      have h1 : ⌈(8 * C / ((1 - α) ^ 2 * twinPrimeConstant)) ^ (2 / (1 - α))⌉₊ ≤ n :=
        le_trans (le_max_right _ _) hn
      calc (8 * C / ((1 - α) ^ 2 * twinPrimeConstant)) ^ (2 / (1 - α))
          ≤ (⌈(8 * C / ((1 - α) ^ 2 * twinPrimeConstant)) ^ (2 / (1 - α))⌉₊ : ℝ) :=
            Nat.le_ceil _
        _ ≤ (n:ℝ) := by exact_mod_cast h1
    have hfinal_rpow : 8 * C / ((1-α)^2 * twinPrimeConstant) ≤ (n:ℝ) ^ ((1-α)/2) := by
      have hK_nonneg : 0 ≤ 8 * C / ((1-α)^2 * twinPrimeConstant) := by positivity
      have hK_rpow_nonneg :
          0 ≤ (8 * C / ((1-α)^2 * twinPrimeConstant)) ^ (2/(1-α)) :=
        Real.rpow_nonneg hK_nonneg _
      have hexp_pos : 0 < (1-α)/2 := by linarith
      have hraised := Real.rpow_le_rpow hK_rpow_nonneg hthreshold hexp_pos.le
      rw [← Real.rpow_mul hK_nonneg] at hraised
      have hexp_simplify : (2/(1-α)) * ((1-α)/2) = 1 := by field_simp
      rw [hexp_simplify, Real.rpow_one] at hraised
      exact hraised
    have hstep_mul : (16 * C / (1-α)^2) ≤ 2 * twinPrimeConstant * (n:ℝ) ^ ((1-α)/2) := by
      have h2twin_pos : 0 < 2 * twinPrimeConstant := by positivity
      have hraw := mul_le_mul_of_nonneg_left hfinal_rpow h2twin_pos.le
      have heq : 2 * twinPrimeConstant * (8 * C / ((1-α)^2 * twinPrimeConstant))
          = 16 * C / (1-α)^2 := by
        field_simp
        ring
      rw [heq] at hraw
      exact hraw
    have hcombine2 : (n:ℝ) ^ ((1-α)/2) * (n:ℝ) ^ ((1-α)/2) = (n:ℝ) ^ (1-α) := by
      rw [← Real.rpow_add hnR]; ring_nf
    have hδsq : ((1-α:ℝ)/4) * ((1-α)/4) = (1-α)^2/16 := by ring
    calc C * (Real.log n) ^ 2
        = C * (Real.log n * Real.log n) := by ring
      _ < C * (((n:ℝ) ^ ((1-α)/4) / ((1-α)/4)) * ((n:ℝ) ^ ((1-α)/4) / ((1-α)/4))) :=
          mul_lt_mul_of_pos_left hstep2 hCpos
      _ = (16 * C / (1-α)^2) * (n:ℝ) ^ ((1-α)/2) := by
          rw [div_mul_div_comm, hcombine, hδsq, div_div_eq_mul_div]
          ring
      _ ≤ (2 * twinPrimeConstant * (n:ℝ) ^ ((1-α)/2)) * (n:ℝ) ^ ((1-α)/2) :=
          mul_le_mul_of_nonneg_right hstep_mul (Real.rpow_nonneg hnR.le _)
      _ = 2 * twinPrimeConstant * ((n:ℝ) ^ ((1-α)/2) * (n:ℝ) ^ ((1-α)/2)) := by ring
      _ = 2 * twinPrimeConstant * (n:ℝ) ^ (1-α) := by rw [hcombine2]
