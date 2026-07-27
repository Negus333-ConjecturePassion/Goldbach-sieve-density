import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

-- ==========================================
-- PHASE 5: Vaughan's Identity -- Algebraic Core
-- (R.C. Vaughan, 1977; as presented in W.W.L. Chen,
--  "Goldbach's Problem", Chapter 2, Section 2.5, equation (2.23))
-- ==========================================
--
-- STATUS: UNVERIFIED DRAFT. Written without access to a Lean toolchain
-- in this session -- following the established modularized-solution
-- workflow, this is a NEW standalone file. It imports but does not
-- touch Basic.lean or any prior Phase file, so a failure here cannot
-- contaminate the existing clean build. Expect several fix-iterations
-- once built locally, same as every other Phase file so far.
--
-- PURPOSE: Chen's equation (2.23) states Vaughan's identity with
-- INFINITE sums (over all z, all x), which is not directly a Lean
-- statement without a finiteness/support assumption on F. This file
-- formalizes the fully rigorous FINITE version: fix a bound N, and
-- assume F is only being summed over x in [1, N] (matching how the
-- identity is actually used in practice -- F itself vanishes outside
-- a finite range once y and the arc are fixed). This is a genuinely
-- new formalization target: no evidence found (web search, this
-- session) that Vaughan's identity has been formalized in Lean or
-- Mathlib anywhere. It is PURELY ALGEBRAIC -- a Mobius-function
-- reindexing identity -- not an open estimate, so unlike
-- ErrorTermPolynomialBound this is fully within reach.
--
-- WHAT THIS FILE DOES NOT DO: it does not touch any exponential-sum
-- estimate (Type I / Type II bounds, S1/S2/S3 in Chen Ch.2 Section 2.5).
-- Those ARE open/hard estimates requiring Weyl differencing and the
-- large sieve -- this file only formalizes the underlying IDENTITY
-- those estimates are built on top of.

open Nat ArithmeticFunction Finset BigOperators

/-- Real-valued Mobius function. Cast via explicit `Int.cast` function
    application rather than a `(... : ℝ)` type ascription -- the
    ascription form failed to elaborate in this build (twice: once
    inline inside a `∑` binder, once even as a standalone top-level
    definition), so the coercion is likely not being resolved via
    plain ascription for this particular ℤ→ℝ case in this Mathlib
    version. Plain function application avoids that path entirely:
    `Int.cast : ℤ → R` unifies its own implicit `{R}` directly against
    the declared return type ℝ, with no ascription/coercion-insertion
    step involved at all. -/
noncomputable def moebiusR (n : ℕ) : ℝ :=
  Int.cast (ArithmeticFunction.moebius n)

/-!
## The core Mobius fact

The standard fact underlying Vaughan's identity: summing the Mobius
function over all divisors of `x` gives 1 if `x = 1` and 0 otherwise.
This is the Dirichlet-convolution identity `ζ * μ = 1` (the
multiplicative identity of the Dirichlet ring of arithmetic functions),
restricted to a single value.

CONFIRMED via grep of the local Mathlib clone
(NumberTheory/ArithmeticFunction/{Moebius,Zeta}.lean):
  - `ArithmeticFunction.coe_zeta_mul_moebius : (ζ * μ : ArithmeticFunction ℤ) = 1`
  - `ArithmeticFunction.coe_zeta_mul_apply [Semiring R] {f : ArithmeticFunction R}
     {x : ℕ} : (ζ * f) x = ∑ i ∈ divisors x, f i`
  - `ArithmeticFunction.one_apply : (1 : ArithmeticFunction R) x = ite (x = 1) 1 0`
`coe_zeta_mul_apply` already does the full divisorsAntidiagonal-to-
divisors reindexing internally (see its proof via `coe_zeta_smul_apply`
in Zeta.lean) -- no separate reindexing lemma needed on our end for
this particular fact. RISK POINT 1 is therefore resolved.
-/

/-- Integer-valued version of the Mobius-sum fact. Proof is a direct
    three-lemma chain, all confirmed against source (see note above) --
    no divisorsAntidiagonal reindexing needed on our end, since
    `coe_zeta_mul_apply` already does that internally. -/
lemma sum_moebius_divisors_int (x : ℕ) (_hx : 0 < x) :
    (∑ d ∈ x.divisors, (ArithmeticFunction.moebius d : ℤ)) =
      if x = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_moebius,
      ArithmeticFunction.one_apply]

/-- The elementary Mobius-sum fact, ℝ-valued: `Σ_{d | x} μ(d) = 1` if
    `x = 1`, else `0`. Derived from the integer version above by a
    single clean cast at the end -- no binder-cast ambiguity here,
    since sum_moebius_divisors_int is already fully computed to a
    concrete ℤ value before this cast happens. -/
lemma sum_moebius_divisors (x : ℕ) (hx : 0 < x) :
    (∑ d ∈ x.divisors, moebiusR d) = if x = 1 then 1 else 0 := by
  simp only [moebiusR]
  exact_mod_cast sum_moebius_divisors_int x hx

/-!
## The reindexing lemma

The heart of Vaughan's identity: summing `F` over divisor pairs
`(d, z)` with `d ≤ X` and `d * z = x` is the same as summing, for each
`x`, `F(x)` weighted by the partial divisor-Mobius-sum `c(x) := Σ_{d |
x, d ≤ X} μ(d)`. This is a pure reindexing statement -- no analysis,
just a bijection between the pair-indexed sum and the x-indexed sum.

RISK POINT 2: split into two sub-lemmas below for modularity, matching
the project's established workflow. The bijection call in
`reindex_multiples` is left pending a grep of the exact
`Finset.sum_bij'` (or `sum_nbij'`) signature -- this has been
refactored across Mathlib versions and is not worth guessing a third
time given how many rounds earlier lemma-name guesses cost.
-/

/-- Bridges the two ways of writing "divisors of `x` that are `≤ X`":
    as a filtered divisor set, or as a filtered interval. Needed to
    connect `swap_divisor_sum`'s output shape to `vaughan_reindex`'s
    stated shape. Uses only long-standing, stable Mathlib lemmas
    (`Nat.mem_divisors`, `Finset.mem_filter`, `Finset.mem_Icc`,
    `Nat.zero_dvd` via `simp`) -- lower risk than the bijection lemmas
    below. -/
lemma divisors_filter_eq (x X : ℕ) (hx : 1 ≤ x) :
    (x.divisors.filter (fun d => d ≤ X)) = (Finset.Icc 1 X).filter (fun d => d ∣ x) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hdX⟩
    refine ⟨⟨?_, hdX⟩, hdvd⟩
    rcases Nat.eq_zero_or_pos d with rfl | hpos
    · simp at hdvd; omega
    · exact hpos
  · rintro ⟨⟨hd1, hdX⟩, hdvd⟩
    exact ⟨⟨hdvd, by omega⟩, hdX⟩

/-- Per-`d` reindex: summing `F(z·d)` over `z ∈ [1, N/d]` equals summing
    `F(x)` over multiples of `d` in `[1, N]`. Proved via `Finset.sum_image`
    (expressing the multiples-set as the image of `Icc 1 (N/d)` under the
    injective map `z ↦ z·d`) rather than a general bijection lemma, since
    `sum_image` is older and less likely to have changed signature across
    Mathlib versions. RISK: the exact names/argument order of
    `Nat.le_div_iff_mul_le`, `Nat.div_mul_le_self`, and
    `Nat.eq_of_mul_eq_mul_right` are not double-checked against this
    Mathlib version -- likely candidates for a fix-iteration. -/
lemma reindex_multiples (N d : ℕ) (hd : 1 ≤ d) (F : ℕ → ℝ) :
    (∑ z ∈ Finset.Icc 1 (N / d), F (z * d)) =
      ∑ x ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x), F x := by
  have hset : (Finset.Icc 1 N).filter (fun x => d ∣ x)
      = (Finset.Icc 1 (N / d)).image (· * d) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hx1, hxN⟩, z, hz⟩
      refine ⟨z, ⟨?_, ?_⟩, by rw [hz]; ring⟩
      · rcases Nat.eq_zero_or_pos z with rfl | hzpos
        · simp at hz; omega
        · exact hzpos
      · rw [Nat.le_div_iff_mul_le hd]
        rw [hz] at hxN
        linarith [hxN]
    · rintro ⟨z, ⟨hz1, hzN⟩, rfl⟩
      refine ⟨⟨by nlinarith, ?_⟩, z, by ring⟩
      calc z * d ≤ (N / d) * d := Nat.mul_le_mul_right d hzN
        _ ≤ N := Nat.div_mul_le_self N d
  rw [hset, Finset.sum_image]
  intro a _ b _ hab
  exact Nat.eq_of_mul_eq_mul_right hd hab

/-- Order-swap: the double sum over `d ∈ [1,X]` with inner sum over
    multiples of `d` in `[1,N]` equals the double sum over `x ∈ [1,N]`
    with inner sum over divisors of `x` that are `≤ X`. Proved by first
    turning each filtered inner sum into a sum over the FULL range with
    an `if d ∣ x then ... else 0` weight (via `Finset.sum_filter`), which
    makes both sides the same plain double sum over the rectangle
    `Icc 1 X × Icc 1 N` -- at that point `Finset.sum_comm` (an ordinary
    swap over two independent, unfiltered Finsets) closes it directly.
    Chosen over a sigma/biUnion/bijection approach since `sum_filter`
    and `sum_comm` are among the most foundational, long-stable lemmas
    in Mathlib -- a grep for `sum_sigma`/`sum_biUnion` in the expected
    location came back empty, so this route was chosen specifically to
    avoid needing those names at all. -/
lemma swap_divisor_sum (N X : ℕ) (hX : 1 ≤ X) (hXN : X ≤ N) (F : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X,
        ∑ x ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x), moebiusR d * F x) =
      ∑ x ∈ Finset.Icc 1 N,
        ∑ d ∈ (Finset.Icc 1 X).filter (fun d => d ∣ x), moebiusR d * F x := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- Assembly: combines `reindex_multiples`, `swap_divisor_sum`, and
    `divisors_filter_eq` into the full reindexing lemma. Stated with
    `x.divisors.filter (fun d => d ≤ X)` rather than the `∑ d ∈ s with p d`
    notation used in the very first draft -- the same set, spelled out
    explicitly rather than relying on that filter-sum macro parsing as
    expected in this Mathlib version. -/
lemma vaughan_reindex (N X : ℕ) (hX : 1 ≤ X) (hXN : X ≤ N) (F : ℕ → ℝ) :
    (∑ d ∈ Finset.Icc 1 X, moebiusR d *
        (∑ z ∈ Finset.Icc 1 (N / d), F (z * d))) =
      ∑ x ∈ Finset.Icc 1 N,
        (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x := by
  have step1 : ∀ d ∈ Finset.Icc 1 X,
      moebiusR d * ∑ z ∈ Finset.Icc 1 (N / d), F (z * d)
        = ∑ x ∈ (Finset.Icc 1 N).filter (fun x => d ∣ x), moebiusR d * F x := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    rw [reindex_multiples N d hd.1 F, Finset.mul_sum]
  rw [Finset.sum_congr rfl step1, swap_divisor_sum N X hX hXN F]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Icc] at hx
  rw [Finset.sum_mul, divisors_filter_eq x X hx.1]

/-!
## Vaughan's identity (finite form)

The main result: `F(1)` can be recovered from the double sum over
`d ≤ X` together with a correction term over the "tail" `x > X`. This
is exactly Chen's equation (2.23), specialized to a finite range
`[1, N]` so it is a genuine, unconditional Lean theorem rather than a
statement about formal/infinite series.
-/

theorem vaughan_identity_finite (N X : ℕ) (hX : 1 ≤ X) (hXN : X ≤ N)
    (F : ℕ → ℝ) :
    F 1 =
      (∑ d ∈ Finset.Icc 1 X, moebiusR d *
          (∑ z ∈ Finset.Icc 1 (N / d), F (z * d))) -
      (∑ x ∈ Finset.Ioc X N,
          (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x) := by
  rw [vaughan_reindex N X hX hXN F]
  have hsplit : Finset.Icc 1 N = Finset.Icc 1 X ∪ Finset.Ioc X N := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 X) (Finset.Ioc X N) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1
    simp only [Finset.mem_Ioc] at hx2
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hcancel :
      (∑ x ∈ Finset.Icc 1 X, (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x)
        + (∑ x ∈ Finset.Ioc X N, (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x)
        - (∑ x ∈ Finset.Ioc X N, (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x)
      = ∑ x ∈ Finset.Icc 1 X, (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x := by
    ring
  rw [hcancel]
  have hicc : Finset.Icc 1 X = insert 1 (Finset.Ioc 1 X) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hicc, Finset.sum_insert (by simp only [Finset.mem_Ioc]; omega)]
  have hzero : ∀ x ∈ Finset.Ioc 1 X,
      (∑ d ∈ x.divisors.filter (fun d => d ≤ X), moebiusR d) * F x = 0 := by
    intro x hx
    simp only [Finset.mem_Ioc] at hx
    have hfilter : x.divisors.filter (fun d => d ≤ X) = x.divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      have hd_dvd : d ∣ x := (Nat.mem_divisors.mp hd).1
      exact le_trans (Nat.le_of_dvd (by omega) hd_dvd) hx.2
    rw [hfilter, sum_moebius_divisors x (by omega), if_neg (by omega : x ≠ 1)]
    ring
  rw [Finset.sum_eq_zero hzero]
  have h1 : (∑ d ∈ (1 : ℕ).divisors.filter (fun d => d ≤ X), moebiusR d) = 1 := by
    have hfilter1 : (1 : ℕ).divisors.filter (fun d => d ≤ X) = (1 : ℕ).divisors := by
      apply Finset.filter_true_of_mem
      intro d hd
      have hd_dvd : d ∣ 1 := (Nat.mem_divisors.mp hd).1
      have : d = 1 := Nat.dvd_one.mp hd_dvd
      omega
    rw [hfilter1]
    simpa using sum_moebius_divisors 1 (by norm_num)
  rw [h1]
  ring

/-!
## Correspondence to Chen's Chapter 2, Section 2.5

  Chen's F(1, y)                    ↔ this file's F 1
  Chen's Σ_{d≤X} Σ_z μ(d)F(zd,y)     ↔ the first sum on the RHS above
  Chen's Σ_{x>X} (Σ_{d|x,d≤X}μ(d))F(x,y)
                                     ↔ the second (correction) sum above
  Chen's y-dependence                ↔ folded into F itself (curry F
                                       as `fun x => Λ y * e(α x y)` etc.
                                       at the call site; not needed for
                                       the identity itself)

Chen's own next step (S1, S2, S3 decomposition, Theorem 2.2's Type I/
Type II estimates) is NOT attempted here -- that is the genuinely open,
hard exponential-sum estimation step. This file stops at the identity.
-/
