import Goldbach.Basic
import Mathlib.Analysis.PSeries

-- ==========================================
-- PHASE 4b: Circle-Method Decomposition of the Analytic Bridge
-- (Hardy-Littlewood, "Partitio Numerorum III", 1922)
-- ==========================================
--
-- This section does NOT close Hypothesis 5.2. It restates it in the
-- classical major-arc / minor-arc language of the circle method, so
-- that the single remaining open gap is expressed in the same terms
-- the analytic number theory literature uses -- making it easier for
-- a reviewer to see exactly which piece is genuinely open.

/-- The actual (unweighted) count of Goldbach representations of `n`:
    the number of primes `p` less than or equal to `n` such that
    `n - p` is also prime. This is the concrete quantity the circle
    method estimates. -/
def GoldbachRepresentationCount (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (n - p))).card

/-- The exact Hardy-Littlewood major-arc asymptotic main term
    ("Conjecture A", Partitio Numerorum III, 1922, eq. 4.11):
      MajorArcTerm(n) = S(n) * n / (log n)^2
    where S(n) is the singular series -- this matches `singularSeries`
    exactly, with no extra constant needed; Hardy and Littlewood's own
    formula already has this shape. This part is unconditionally
    bounded below via `singular_series_lower_bound`. -/
noncomputable def MajorArcTerm (n : ℕ) : ℝ :=
  singularSeries n * (n : ℝ) / (Real.log n) ^ 2

/-- errorTerm is left as an unspecified real-valued function, in the
    same spirit as `AnalyticDensityBridge` in `Goldbach.Basic`, which
    is stated as a Prop with no proof term ever supplied. Defining
    errorTerm concretely (e.g. as 0, or as any fixed formula) would
    either make MinorArcErrorBound provably false (too strong) or
    silently assume the open result (too weak / circular). Any genuine
    proof of MinorArcErrorBound must supply BOTH a specific errorTerm
    satisfying o(MajorArcTerm n) AND a proof the bound holds -- that
    pair is precisely the 100-year-open problem documented below.
    No value is assigned here.

    KNOWN LIMITATION: because errorTerm is opaque, MinorArcErrorBound
    as currently stated carries no usable content (the bound could be
    arbitrarily large). See the note on `bridge_from_circle_method`. -/
noncomputable opaque errorTerm (n : ℕ) : ℝ

/-- The Minor-Arc Error Bound: the precise, classical open hypothesis
    that the true representation count never deviates from the
    major-arc prediction by more than an error term smaller than the
    main term itself.

    HISTORICAL NOTE (not a placeholder -- this is the documented state
    of the problem): Hardy and Littlewood explicitly place binary
    Goldbach (r = 2) in a distinct, harder class from ternary Goldbach
    and Waring's problem. They state plainly that even assuming their
    generalized-Riemann-type Hypothesis R at its strongest admissible
    value, they cannot control the minor-arc error term for r = 2: the
    best bound their method gives is too large, relative to the main
    term, by roughly a factor of n^(1/4) (Partitio Numerorum III,
    Section 4.1). This is a historical fact about the limits of the
    circle method for this problem, not merely an estimate we have not
    yet found -- it is why this gap (later understood as the "parity
    problem" in sieve theory) has resisted proof for a century, GRH
    included. -/
def MinorArcErrorBound : Prop :=
  ∀ (n : ℕ), IsValidEven n → 8 ≤ n →
    |(GoldbachRepresentationCount n : ℝ) - MajorArcTerm n| ≤ errorTerm n

/-- The Analytic Density Bridge, restated via the classical major-arc /
    minor-arc decomposition.

    NOT PROVABLE AS STATED. Because `errorTerm` is opaque, the
    hypothesis `h_minor` places no actual constraint on the
    representation count, so positivity cannot be derived from it.
    Closing this requires first restating MinorArcErrorBound with the
    error strictly bounded by the main term (i.e. `< MajorArcTerm n`),
    which is the honest form of the open hypothesis. This `sorry` is
    a design gap, not merely unfinished transcription. -/
theorem bridge_from_circle_method
    (h_minor : MinorArcErrorBound) :
    AnalyticDensityBridge := by
  sorry

/-- The defining sum for `twinPrimeConstant` is summable.

    Proof sketch: for prime p >= 3 we have (p-1)^2 >= 4, so
    x := 1/(p-1)^2 lies in (0, 1/4]. On that range
    |log(1 - x)| <= x/(1-x) <= 2x, and the comparison series
    sum 2/(p-1)^2 converges. -/
lemma twinPrimeConstant_summable :
    Summable (fun p : { p : ℕ // Nat.Prime p ∧ p > 2 } =>
      Real.log (1 - 1 / ((p.val : ℝ) - 1) ^ 2)) := by
  apply Summable.of_norm
  have hdom : Summable (fun p : { p : ℕ // Nat.Prime p ∧ p > 2 } =>
      2 / ((p.val : ℝ) - 1) ^ 2) := by
    have hN : Summable (fun n : ℕ => 2 / ((n : ℝ) - 1) ^ 2) := by
      rw [← summable_nat_add_iff 2]
      have hcast : ∀ n : ℕ, 2 / (((n + 2 : ℕ) : ℝ) - 1) ^ 2 = 2 / ((n : ℝ) + 1) ^ 2 := by
        intro n
        push_cast
        ring_nf
      simp only [hcast]
      have h1 : Summable (fun m : ℕ => 1 / (m : ℝ) ^ 2) :=
        Real.summable_one_div_nat_pow.mpr (by norm_num)
      have h2 : Summable (fun m : ℕ => 2 / (m : ℝ) ^ 2) := by
        simpa [div_eq_mul_inv] using h1.mul_left 2
      have h3 := h2.comp_injective (add_left_injective 1)
      simpa [Function.comp_def] using h3
    exact hN.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun p => norm_nonneg _) ?_ hdom
  intro p
  obtain ⟨hp_prime, hp_gt⟩ := p.property
  have hp3 : (3:ℝ) ≤ (p.val : ℝ) := by exact_mod_cast hp_gt
  have hd : (2:ℝ) ≤ (p.val : ℝ) - 1 := by linarith
  have hsq : (4:ℝ) ≤ ((p.val : ℝ) - 1) ^ 2 := by nlinarith
  set x : ℝ := 1 / ((p.val : ℝ) - 1) ^ 2 with hx
  have hx_pos : 0 < x := by positivity
  have hx_le : x ≤ 1/4 := by rw [hx]; rw [div_le_iff₀ (by positivity)]; linarith
  have h1x : (3:ℝ)/4 ≤ 1 - x := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/(1-x) by positivity)
  rw [Real.log_div one_ne_zero (by linarith), Real.log_one] at hlog
  rw [Real.norm_eq_abs, abs_of_nonpos (Real.log_nonpos (by linarith) (by linarith))]
  have hfrac : 1/(1-x) - 1 = x/(1-x) := by field_simp; ring
  have hstep : x/(1-x) ≤ 2*x := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2x : 2*x = 2/((p.val : ℝ) - 1)^2 := by rw [hx]; ring
  linarith
