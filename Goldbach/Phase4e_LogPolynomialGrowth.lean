import Goldbach.Phase4d_EulerMaclaurinBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- ==========================================
-- PHASE 4e: Existence of N0 for EventualLogPolynomialDominance
-- (Modularized Solution Effort)
-- ==========================================
--
-- STATUS: UNVERIFIED, the most experimental file yet in this chain.
-- Uses Asymptotics.IsLittleO / Filter.atTop machinery, which is the
-- territory where lemma names and exact API shapes are hardest to cite
-- correctly without a local Mathlib to check against. Isolated in its
-- own file per the established workflow -- imports but never edits any
-- prior file, so a failure here cannot contaminate the existing clean
-- build. Expect this one may need several fix-iterations.
--
-- PURPOSE: EventualLogPolynomialDominance (Phase4d_EulerMaclaurinBound.lean)
-- was left as an explicit hypothesis rather than derived, specifically
-- to avoid this exact risk. This file attempts to actually discharge
-- that hypothesis unconditionally: for ANY constants C > 0 and alpha < 1,
-- an N0 exists making the dominance hold. Unlike ErrorTermPolynomialBound
-- (the genuinely open number-theoretic content -- see project notes on
-- Montgomery-Vaughan 1975 and successors, which bound only the
-- EXCEPTIONAL SET size, not a per-n error term), this IS standard real
-- analysis ("polynomial beats any power of log"), not open mathematics.
-- Only the Lean derivation is uncertain here, not the underlying fact.
--
-- REFERENCE: E. T. Whittaker and G. N. Watson, A Course of Modern
-- Analysis, 4th ed., Cambridge University Press, 1963. Ch. XIII
-- SS13.5-13.51 (growth bounds on zeta(s,a) via Maclaurin-Cauchy) is the
-- classical source for the "polynomial beats log" phenomenon this file
-- discharges directly. See Chapter13_WhittakerWatson_Summary.pdf.

open Filter Asymptotics

/-- For any exponent ε > 0, (log x)^2 = o(x^ε) as x → ∞. Direct instance
    of Mathlib's `isLittleO_log_rpow_rpow_atTop`, confirmed via Mathlib
    docs search (Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics) --
    NOTE: this lemma is declared top-level in that file, not inside
    `namespace Real`, despite its statement referencing `Real.log`;
    confirmed by two failed `Real.`-prefixed attempts before this fix:
    `isLittleO_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
      (fun x => log x ^ r) =o[atTop] fun x => x ^ s`.
    Applying with r = 2 gives exactly what is needed, with no manual
    combination of two little-o facts required. -/
lemma log_sq_isLittleO_rpow (ε : ℝ) (hε : 0 < ε) :
    (fun x : ℝ => (Real.log x) ^ 2) =o[atTop] (fun x : ℝ => x ^ ε) := by
  simpa [Real.rpow_two] using isLittleO_log_rpow_rpow_atTop 2 hε

/-- Unconditional existence of N0 for EventualLogPolynomialDominance,
    for any C ≥ 0 and α < 1. This is the payoff: it discharges the
    hypothesis that Phase4d_EulerMaclaurinBound.lean left open, for the
    "polynomial beats log-squared" fact specifically (NOT for
    ErrorTermPolynomialBound, which remains genuinely open number
    theory). -/
theorem exists_N0_log_polynomial_dominance
    (C α : ℝ) (hC : 0 ≤ C) (hα : α < 1) :
    ∃ N0 : ℕ, EventualLogPolynomialDominance C α N0 := by
  have htwin : 0 < twinPrimeConstant := Real.exp_pos _
  have hε : 0 < 1 - α := by linarith
  have hlittleo := log_sq_isLittleO_rpow (1 - α) hε
  rcases eq_or_lt_of_le hC with hC0 | hCpos
  · -- C = 0 case: goal trivial since LHS is 0 and RHS is positive.
    refine ⟨8, fun n hn8 => ?_⟩
    have hnpos : 0 < n := by omega
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
    rw [← hC0]
    simp only [zero_mul]
    positivity
  · -- C > 0 case: unfold IsLittleO with ε' = twinPrimeConstant / C.
    -- RISK POINT 3: the exact statement shape of `IsLittleO.def` /
    -- `isLittleO_iff` and how it interacts with `eventually_atTop` is
    -- the least certain part of this branch; the surrounding algebra
    -- (extracting N0 : ℕ from an eventual-in-ℝ statement) is more
    -- routine but still unverified.
    have hpos_ratio : 0 < twinPrimeConstant / C := by positivity
    have hev : ∀ᶠ x in atTop, ‖(Real.log x) ^ 2‖ ≤ (twinPrimeConstant / C) * ‖x ^ (1 - α)‖ :=
      isLittleO_iff.mp hlittleo hpos_ratio
    obtain ⟨N0R, hN0R⟩ := eventually_atTop.mp hev
    obtain ⟨N0, hN0⟩ := exists_nat_ge (max N0R 8)
    refine ⟨N0, fun n hn => ?_⟩
    have hnN0R : N0R ≤ (n : ℝ) := by
      have h1 : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h2 : N0R ≤ (N0 : ℝ) := le_trans (le_max_left _ _) hN0
      linarith
    have hbd := hN0R n hnN0R
    have hnR : (0 : ℝ) < (n : ℝ) := by
      have h8 : (8:ℝ) ≤ (N0:ℝ) := le_trans (le_max_right _ _) hN0
      have : (N0:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hlogsq_nonneg : 0 ≤ (Real.log n) ^ 2 := sq_nonneg _
    have hpow_pos : 0 < (n : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos hnR _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogsq_nonneg,
        abs_of_pos hpow_pos] at hbd
    have hfinal : C * (Real.log n) ^ 2 ≤ twinPrimeConstant * (n:ℝ) ^ (1 - α) := by
      have := mul_le_mul_of_nonneg_left hbd hC
      rwa [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hCpos)] at this
    have hstrict : twinPrimeConstant * (n:ℝ) ^ (1 - α)
        < 2 * twinPrimeConstant * (n:ℝ) ^ (1 - α) := by nlinarith [htwin, hpow_pos]
    linarith
