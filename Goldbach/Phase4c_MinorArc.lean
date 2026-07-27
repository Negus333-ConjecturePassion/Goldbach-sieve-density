import Goldbach.Phase4b_Draft

-- ==========================================
-- PHASE 4c: Strict Minor-Arc Dominance (Modularized Solution Effort)
-- ==========================================
--
-- STATUS: UNVERIFIED. This file has not been run through `lake build`.
-- It is deliberately isolated in its own file, importing but never
-- modifying Goldbach.Basic or Goldbach.Phase4b_Draft, so that if
-- anything here fails to compile, the existing clean build (1944
-- jobs, one honest `sorry` in bridge_from_circle_method) is entirely
-- unaffected. Verify this file independently before considering
-- folding any of it back into Phase4b_Draft.lean.
--
-- PURPOSE: `MinorArcErrorBound` in Phase4b_Draft.lean uses `≤`, which
-- (as documented there) gives the hypothesis no usable content --
-- an error bounded by an arbitrarily large quantity constrains
-- nothing. This file explores the STRICT (`<`) version of that
-- hypothesis, which is the honest form of the open circle-method
-- problem, and checks how far it can be pushed unconditionally
-- from there. It does NOT close MinorArcErrorBound or
-- bridge_from_circle_method -- it isolates a second, more usable
-- open hypothesis and proves what follows *from* it.

/-- The strict form of minor-arc dominance: the error term is
    strictly smaller in absolute value than the major-arc main term,
    for every valid even n >= 8. This is the honest statement of the
    classical open hypothesis -- strict, not `≤` -- expressed in
    terms of the REAL `MajorArcTerm` and `errorTerm` from
    Phase4b_Draft.lean, not stand-in opaques. -/
def MinorArcStrictlyDominated : Prop :=
  ∀ (n : ℕ), IsValidEven n → 8 ≤ n →
    |errorTerm n| < MajorArcTerm n

/-- If the representation count equals the major-arc term plus the
    error term (the circle-method decomposition), and the error is
    strictly dominated, then the actual representation count is
    strictly positive. -/
theorem representationCount_pos_of_strict_dominance
    (n : ℕ) (hn : IsValidEven n) (h8 : 8 ≤ n)
    (h_decomp : (GoldbachRepresentationCount n : ℝ) = MajorArcTerm n + errorTerm n)
    (h_dom : MinorArcStrictlyDominated) :
    0 < (GoldbachRepresentationCount n : ℝ) := by
  have h_lt := h_dom n hn h8
  have h_neg_lt := neg_lt_of_abs_lt h_lt
  rw [h_decomp]
  linarith

/-- Connective step: a positive representation count implies the
    existence of a witnessed symmetry offset k. This is the piece
    the standalone GoldbachFramework draft was missing -- it proved
    `r_Λ(n) > 0` but never bridged that to `∃ k, IsSymmetryOffset n k`,
    which is what AnalyticDensityBridge actually requires.

    NOTE: `GoldbachRepresentationCount n > 0` as a real number implies
    the underlying Finset.filter card is nonzero as a natural number,
    which gives an actual witnessing prime p via Finset.card_pos. From
    p we construct k by the standard symmetric-offset identification:
    if p ≤ n/2, take k = n/2 - p; if p > n/2, take k = p - n/2. Both
    cases reduce to the same pair {n/2 - k, n/2 + k} = {p, n - p}. -/
theorem exists_offset_of_representationCount_pos
    (n : ℕ) (hn : IsValidEven n)
    (h_pos : 0 < (GoldbachRepresentationCount n : ℝ)) :
    ∃ (k : ℕ), IsSymmetryOffset n k := by
  have h_pos_nat : 0 < GoldbachRepresentationCount n := by
    exact_mod_cast h_pos
  unfold GoldbachRepresentationCount at h_pos_nat
  rw [Finset.card_pos] at h_pos_nat
  obtain ⟨p, hp_mem⟩ := h_pos_nat
  rw [Finset.mem_filter] at hp_mem
  obtain ⟨hp_range, hp_prime, hnp_prime⟩ := hp_mem
  have hp_le_n : p ≤ n := by
    have := Finset.mem_range.mp hp_range
    omega
  have hn_even : n % 2 = 0 := hn.2
  by_cases hle : p ≤ n / 2
  · refine ⟨n / 2 - p, ?_⟩
    constructor
    · rw [Nat.sub_sub_self hle]
      exact hp_prime
    · have heq : n / 2 + (n / 2 - p) = n - p := by omega
      rw [heq]
      exact hnp_prime
  · push_neg at hle
    refine ⟨p - n / 2, ?_⟩
    constructor
    · have heq : n / 2 - (p - n / 2) = n - p := by omega
      rw [heq]
      exact hnp_prime
    · have heq : n / 2 + (p - n / 2) = p := by omega
      rw [heq]
      exact hp_prime

/-- Full conditional bridge: IF the circle-method decomposition holds
    AND the error is strictly dominated by the major-arc term, THEN
    the Analytic Density Bridge's actual conclusion follows --
    ∃ k, IsSymmetryOffset n k -- not merely a positive count.

    This is still conditional on `MinorArcStrictlyDominated`, which
    remains open (same status as MinorArcErrorBound in
    Phase4b_Draft.lean, just usable rather than vacuous). It is NOT
    a proof of bridge_from_circle_method, and does not discharge that
    file's `sorry`. It is a second, cleanly isolated conditional
    result showing exactly how much closer the strict hypothesis gets
    you. -/
theorem symmetryOffset_of_strict_dominance
    (n : ℕ) (hn : IsValidEven n) (h8 : 8 ≤ n)
    (h_decomp : (GoldbachRepresentationCount n : ℝ) = MajorArcTerm n + errorTerm n)
    (h_dom : MinorArcStrictlyDominated) :
    ∃ (k : ℕ), IsSymmetryOffset n k :=
  exists_offset_of_representationCount_pos n hn
    (representationCount_pos_of_strict_dominance n hn h8 h_decomp h_dom)
