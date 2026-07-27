import Goldbach.Phase4c_MinorArc
import Mathlib.Analysis.SpecialFunctions.Pow.Real

-- ==========================================
-- PHASE 4d: Euler-Maclaurin-Style Polynomial Bound on errorTerm
-- (Modularized Solution Effort)
-- ==========================================
--
-- STATUS: UNVERIFIED, higher risk than Phase4c_MinorArc.lean. This file
-- involves Real.rpow / Real.log inequality manipulation, which is
-- exactly the territory where lemma names are hardest to cite
-- correctly without a local Mathlib to check against. Isolated in its
-- own file per the established workflow -- imports but never edits
-- Basic.lean, Phase4b_Draft.lean, or Phase4c_MinorArc.lean, so a
-- failure here cannot contaminate the existing clean build. Expect to
-- need more than one fix-iteration on this file.
--
-- PURPOSE: narrow MinorArcStrictlyDominated (Phase4c_MinorArc.lean, an
-- abstract inequality with no specified shape) into a concrete,
-- checkable form matching what an actual Euler-Maclaurin remainder
-- analysis (Whittaker & Watson Ch. VII S7.21, applied to zeta-type
-- growth as in Ch. XIII S13.5-13.51) would need to supply. This file
-- does NOT prove errorTerm actually satisfies such a bound -- that
-- remains the genuinely open analytic content, on par with
-- bridge_from_circle_method itself. What IS proven here (modulo the
-- caveats in the docstrings below) is the algebraic fact that IF such
-- a bound holds, strict minor-arc dominance follows for n large enough.
--
-- REFERENCE: E. T. Whittaker and G. N. Watson, A Course of Modern
-- Analysis, 4th ed., Cambridge University Press, 1963. Ch. VII S7.21
-- (Euler-Maclaurin sum formula) motivates ErrorTermPolynomialBound's
-- shape; Ch. XIII SS13.5-13.51 (growth bounds on zeta(s,a) via the
-- Maclaurin-Cauchy formula) motivates EventualLogPolynomialDominance.
-- See Chapter7_WhittakerWatson_Summary.pdf and
-- Chapter13_WhittakerWatson_Summary.pdf for full derivations.

/-- The Euler-Maclaurin template: a concrete polynomial-growth bound on
    errorTerm, with exponent strictly less than 1 (so it grows strictly
    slower than the linear leading order of MajorArcTerm). This is the
    shape an actual Euler-Maclaurin / zeta-growth-bound proof would need
    to establish. NOT proven here -- an explicit hypothesis, same honest
    pattern as AnalyticDensityBridge and MinorArcErrorBound. -/
def ErrorTermPolynomialBound (C α : ℝ) : Prop :=
  0 ≤ C ∧ α < 1 ∧
  ∀ (n : ℕ), IsValidEven n → 8 ≤ n → |errorTerm n| ≤ C * (n : ℝ) ^ α

/-- Companion growth-rate hypothesis: C*(log n)^2 is eventually (for
    n ≥ N0) beaten by 2*twinPrimeConstant*n^(1-α). This is the standard
    real-analysis fact "polynomial beats any power of log" (true for any
    fixed exponent 1-α > 0), made explicit and numeric here rather than
    derived via Filter.Tendsto machinery -- deliberately deferred to
    avoid depending on asymptotic-comparison lemma names that could not
    be verified against the local toolchain in this environment. The
    mathematical content is standard; only the specific Lean derivation
    of existence is deferred to the person running this file. -/
def EventualLogPolynomialDominance (C α : ℝ) (N0 : ℕ) : Prop :=
  ∀ (n : ℕ), N0 ≤ n →
    C * (Real.log n) ^ 2 < 2 * twinPrimeConstant * (n : ℝ) ^ (1 - α)

/-- Main result: given the polynomial bound on errorTerm and the
    companion growth-dominance hypothesis, strict minor-arc dominance
    follows unconditionally for all n ≥ N0. Replaces the abstract
    MinorArcStrictlyDominated with two concrete hypotheses whose shape
    matches known analytic techniques rather than an unstructured
    assumption. -/
theorem errorTermBound_implies_dominance
    (C α : ℝ) (N0 : ℕ) (hN0 : 8 ≤ N0)
    (hbound : ErrorTermPolynomialBound C α)
    (hgrowth : EventualLogPolynomialDominance C α N0) :
    ∀ (n : ℕ), IsValidEven n → N0 ≤ n → |errorTerm n| < MajorArcTerm n := by
  intro n hn hN0n
  obtain ⟨hC, hα, hbd⟩ := hbound
  have h8 : 8 ≤ n := le_trans hN0 hN0n
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have hpos : (0 : ℕ) < n := by omega
    exact_mod_cast hpos
  have hlogpos : 0 < Real.log n := by
    apply Real.log_pos
    have h8R : (8 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h8
    linarith
  have hlogsq_pos : 0 < (Real.log n) ^ 2 := by positivity
  have hnalpha_pos : 0 < (n : ℝ) ^ α := Real.rpow_pos_of_pos hnR α
  have hbd_n : |errorTerm n| ≤ C * (n : ℝ) ^ α := hbd n hn h8
  have hgrow_n := hgrowth n hN0n
  -- RISK POINT 1: rpow addition identity. If Real.rpow_add's argument
  -- order or the ring_nf step doesn't close (1-α)+α = 1 automatically,
  -- this is the first place to look.
  have hpow_comb : (n : ℝ) ^ (1 - α) * (n : ℝ) ^ α = (n : ℝ) ^ (1 : ℝ) := by
    rw [← Real.rpow_add hnR]
    ring_nf
  have step1 : C * (Real.log n) ^ 2 * (n : ℝ) ^ α
      < 2 * twinPrimeConstant * (n : ℝ) := by
    have hraw := mul_lt_mul_of_pos_right hgrow_n hnalpha_pos
    rw [mul_assoc (2 * twinPrimeConstant) ((n : ℝ) ^ (1 - α)) ((n : ℝ) ^ α),
        hpow_comb, Real.rpow_one] at hraw
    exact hraw
  -- RISK POINT 2 (confirmed, fixed): lt_div_iff was renamed lt_div_iff₀
  -- in this Mathlib version.
  have step2 : C * (n : ℝ) ^ α < 2 * twinPrimeConstant * (n : ℝ) / (Real.log n) ^ 2 := by
    rw [lt_div_iff₀ hlogsq_pos]
    nlinarith [step1]
  have hS : 2 * twinPrimeConstant ≤ singularSeries n := singular_series_lower_bound n hn
  -- RISK POINT 3: gcongr is used here for its robustness to exact
  -- lemma-name drift; if unavailable, replace with
  -- (div_le_div_right hlogsq_pos).mpr (mul_le_mul_of_nonneg_right hS hnR.le).
  have step3 : 2 * twinPrimeConstant * (n : ℝ) / (Real.log n) ^ 2
      ≤ singularSeries n * (n : ℝ) / (Real.log n) ^ 2 := by
    gcongr
  calc |errorTerm n| ≤ C * (n : ℝ) ^ α := hbd_n
    _ < 2 * twinPrimeConstant * (n : ℝ) / (Real.log n) ^ 2 := step2
    _ ≤ singularSeries n * (n : ℝ) / (Real.log n) ^ 2 := step3
    _ = MajorArcTerm n := rfl
