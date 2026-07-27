import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Algebra.Order.Round
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.ZMod.Units

open Real

/-! # Phase 6a: nearest-integer distance -/

/-- Distance from a real number to the nearest integer. -/
noncomputable def nearestIntDist (β : ℝ) : ℝ := |β - round β|

theorem nearestIntDist_le_half (β : ℝ) : nearestIntDist β ≤ 1 / 2 :=
  abs_sub_round β

theorem nearestIntDist_nonneg (β : ℝ) : 0 ≤ nearestIntDist β :=
  abs_nonneg _

theorem nearestIntDist_eq_min (β : ℝ) :
    nearestIntDist β = min (Int.fract β) (1 - Int.fract β) :=
  abs_sub_round_eq_min β

/-! # Phase 6b: elementary harmonic bound (fully closed, zero sorry) -/

/-- `harmonic n ≤ log(n+1) + 1`, from `eulerMascheroniSeq`'s established bounds
(`Mathlib.NumberTheory.Harmonic.EulerMascheroni`). No new analytic content --
pure composition of two existing Mathlib facts. -/
theorem harmonic_le_log_add_one (n : ℕ) :
    (harmonic n : ℝ) ≤ Real.log (n + 1) + 1 := by
  have h1 := eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have h2 := eulerMascheroniConstant_lt_two_thirds
  have h3 : eulerMascheroniSeq n < 2 / 3 := h1.trans h2
  unfold eulerMascheroniSeq at h3
  linarith

/-! # Phase 6c: the two specializations -/

/-- **(H1), corrected.** The original target `log(2X)` fails for `1 ≤ X < 2`
(`⌊X/q⌋₊ + 2 ≤ 2X` is false there). `log(X+2)` is always true and is the
same asymptotic order. -/
theorem sum_one_div_succ_le (X : ℝ) (q : ℕ) (hX : 1 ≤ X) (hq : 0 < q) :
    (harmonic (⌊X / q⌋₊ + 1) : ℝ) ≤ Real.log (X + 2) + 1 := by
  have h := harmonic_le_log_add_one (⌊X / q⌋₊ + 1)
  have hqpos : (0:ℝ) < q := by exact_mod_cast hq
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hXq_nonneg : (0:ℝ) ≤ X / q := by positivity
  have hfloor : (⌊X / q⌋₊ : ℝ) ≤ X / q := Nat.floor_le hXq_nonneg
  have hXq_le : X / q ≤ X := by
    rw [div_le_iff₀ hqpos]
    calc X = X * 1 := by ring
      _ ≤ X * q := mul_le_mul_of_nonneg_left hq1 (by linarith)
  have hle : (⌊X / q⌋₊ : ℝ) + 1 + 1 ≤ X + 2 := by linarith [hfloor, hXq_le]
  have hpos : (0:ℝ) < (⌊X / q⌋₊ : ℝ) + 1 + 1 := by positivity
  calc (harmonic (⌊X / q⌋₊ + 1) : ℝ)
      ≤ Real.log ((⌊X / q⌋₊ : ℝ) + 1 + 1) + 1 := by
        push_cast at h ⊢
        linarith
    _ ≤ Real.log (X + 2) + 1 := by
        linarith [Real.log_le_log hpos hle]

/-- **(H2), as originally drafted -- no correction needed.** -/
theorem sum_q_div_h_le (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) * (harmonic (q / 2) : ℝ) ≤ (q : ℝ) * (Real.log q + 1) := by
  have h := harmonic_le_log_add_one (q / 2)
  have hqpos : (0:ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hfloor : ((q / 2 : ℕ) : ℝ) ≤ (q : ℝ) / 2 := Nat.cast_div_le
  have hqR : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hle : ((q / 2 : ℕ) : ℝ) + 1 ≤ (q : ℝ) := by linarith [hfloor, hqR]
  have hpos : (0:ℝ) < ((q / 2 : ℕ) : ℝ) + 1 := by positivity
  have hlog : Real.log (((q / 2 : ℕ) : ℝ) + 1) ≤ Real.log q := Real.log_le_log hpos hle
  calc (q : ℝ) * (harmonic (q / 2) : ℝ)
      ≤ (q : ℝ) * (Real.log (((q / 2 : ℕ) : ℝ) + 1) + 1) :=
        mul_le_mul_of_nonneg_left h hqpos.le
    _ ≤ (q : ℝ) * (Real.log q + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hqpos.le

/-! # Phase 6d: the residue-decomposition core -/

/-- **Reverse triangle inequality for `nearestIntDist`** (1-Lipschitz).
Built from `round_le`'s optimality over ℤ plus the three-point triangle
inequality `abs_sub_le`. -/
theorem nearestIntDist_sub_abs_le (x δ : ℝ) :
    nearestIntDist x - |δ| ≤ nearestIntDist (x + δ) := by
  have h := round_le x (round (x + δ))
  have htri : |x - (round (x + δ) : ℝ)| ≤ |x - (x + δ)| + |(x + δ) - (round (x + δ) : ℝ)| :=
    abs_sub_le x (x + δ) (round (x + δ) : ℝ)
  have hδeq : |x - (x + δ)| = |δ| := by
    rw [show x - (x + δ) = -δ by ring, abs_neg]
  have hbound : |x - (round (x + δ) : ℝ)| ≤ |δ| + |(x + δ) - round (x + δ)| := by
    rw [← hδeq]; exact htri
  unfold nearestIntDist
  linarith [h.trans hbound]

/-- For coprime `a, q` and `1 ≤ r < q`, `ar/q` is never an integer, so its
nearest-integer distance is bounded below by `1/q`. -/
theorem nearestIntDist_ar_ge (a : ℤ) (q : ℕ) (r : ℕ)
    (hq : 0 < q) (haq : IsCoprime a (q : ℤ)) (hr1 : 1 ≤ r) (hrq : r < q) :
    (1 : ℝ) / q ≤ nearestIntDist ((a : ℝ) * r / q) := by
  set n : ℤ := round ((a : ℝ) * r / q) with hn
  have hqZ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hnonzero : (a * (r : ℤ) - n * q : ℤ) ≠ 0 := by
    intro hzero
    have hdvd : (q : ℤ) ∣ a * r := ⟨n, by linear_combination hzero⟩
    have hdvdr : (q : ℤ) ∣ (r : ℤ) := haq.symm.dvd_of_dvd_mul_left hdvd
    have hrpos : (0 : ℤ) < r := by exact_mod_cast hr1
    have hle : (q : ℤ) ≤ r := Int.le_of_dvd hrpos hdvdr
    have h1 : (q : ℝ) ≤ (r : ℝ) := by exact_mod_cast hle
    have h2 : (r : ℝ) < q := by exact_mod_cast hrq
    linarith
  have hint : (1 : ℝ) ≤ |((a * r - n * q : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hnonzero
  have hfrac : (a : ℝ) * r / q - n = ((a * r - n * q : ℤ) : ℝ) / q := by
    push_cast; field_simp
  have heqn : nearestIntDist ((a : ℝ) * r / q) = |(a : ℝ) * r / q - n| := rfl
  rw [heqn, hfrac, abs_div, abs_of_pos hqZ]
  gcongr

/-- **The core case-split lemma.** For `j = 0`, `1 ≤ r ≤ q/2`, `α` close to `a/q`,
the rational part `ar/q` dominates the perturbation. -/
theorem nearestIntDist_ar_dominates (a : ℤ) (q : ℕ) (α : ℝ) (r : ℕ)
    (hq : 0 < q) (haq : IsCoprime a (q : ℤ)) (hr1 : 1 ≤ r) (hrq : 2 * r ≤ q)
    (hα : |α - (a : ℝ) / q| ≤ ((q : ℝ) ^ 2)⁻¹) :
    (1 : ℝ) / 2 * nearestIntDist ((a : ℝ) * r / q) ≤ nearestIntDist (α * r) := by
  have hqZ : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrq' : r < q := by omega
  have hlb := nearestIntDist_ar_ge a q r hq haq hr1 hrq'
  set δ := (α - (a : ℝ) / q) * r with hδ
  have hrR : (2 * (r : ℝ)) ≤ q := by exact_mod_cast hrq
  have habs : |δ| = |α - (a : ℝ) / q| * r := by
    rw [hδ, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (r:ℝ))]
  have step1 : |α - (a : ℝ) / q| * r ≤ (r : ℝ) / (q : ℝ) ^ 2 := by
    calc |α - (a : ℝ) / q| * r ≤ ((q : ℝ) ^ 2)⁻¹ * r :=
          mul_le_mul_of_nonneg_right hα (by positivity)
      _ = (r : ℝ) / (q : ℝ) ^ 2 := by ring
  have step2 : (r : ℝ) / (q : ℝ) ^ 2 ≤ 1 / (2 * (q : ℝ)) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hrR, hqZ]
  have hδbound : |δ| ≤ 1 / (2 * q) := by
    rw [habs]; linarith [step1, step2]
  have hsplit : α * r = (a : ℝ) * r / q + δ := by
    rw [hδ]; field_simp; ring
  rw [hsplit]
  have hlip := nearestIntDist_sub_abs_le ((a : ℝ) * r / q) δ
  have hqhalf : (1 : ℝ) / (2 * (q : ℝ)) = (1 / 2) * (1 / (q : ℝ)) := by ring
  linarith [hδbound, hlb, hlip, hqhalf]

/-! # Phase 6e: residue-completeness (bijection lemma for the general-j case) -/

/-- As `r` ranges over `ZMod q`, `a*r + K` also ranges over all of `ZMod q`
(a bijection), whenever `a` is coprime to `q`. Constructed directly via the
unit's inverse.

Two fixes applied here versus the first draft:
(1) `ZMod.coe_int_isUnit_iff_isCoprime` wants `IsCoprime (q:ℤ) a`, not
`IsCoprime a (q:ℤ)` -- `haq.symm` reorders it (`IsCoprime` is symmetric).
(2) After `intro r` / `intro s`, the goal is two composed lambdas that
haven't been beta-reduced yet, so `rw` can't find its pattern until
`dsimp only` forces that reduction first. -/
theorem residue_shift_bijective (a : ℤ) (q : ℕ) (K : ZMod q) (haq : IsCoprime a (q : ℤ)) :
    Function.Bijective (fun r : ZMod q => (a : ZMod q) * r + K) := by
  have hu : IsUnit (a : ZMod q) := (ZMod.coe_int_isUnit_iff_isCoprime a q).mpr haq.symm
  obtain ⟨u, hu_eq⟩ := hu
  apply Function.bijective_iff_has_inverse.mpr
  refine ⟨fun s => (↑u⁻¹ : ZMod q) * (s - K), ?_, ?_⟩
  · intro r
    dsimp only
    have step : (↑u⁻¹ : ZMod q) * ((a : ZMod q) * r + K - K)
        = (↑u⁻¹ : ZMod q) * ((a : ZMod q) * r) := by ring
    rw [step, ← hu_eq]
    have huu : (↑u⁻¹ : ZMod q) * ↑u = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (↑u⁻¹ : ZMod q) * (↑u * r) = ((↑u⁻¹ : ZMod q) * ↑u) * r := by ring
      _ = 1 * r := by rw [huu]
      _ = r := by ring
  · intro s
    dsimp only
    rw [← hu_eq]
    have huu : (↑u : ZMod q) * ↑u⁻¹ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc (↑u : ZMod q) * ((↑u⁻¹ : ZMod q) * (s - K)) + K
        = ((↑u : ZMod q) * ↑u⁻¹) * (s - K) + K := by ring
      _ = 1 * (s - K) + K := by rw [huu]
      _ = s := by ring

/-! # Phase 6f: exceptional-residue counting lemma -/

/-- At most 8 residues `c ∈ ZMod q` fail "not within 4 of the boundary"
(`c.val < 4` or `c.val ≥ q-4`). Pure `Finset.card` bookkeeping -- no
analytic content. -/
theorem near_boundary_card_le (q : ℕ) [NeZero q] (hq : 8 ≤ q) :
    (Finset.univ.filter (fun c : ZMod q => c.val < 4 ∨ q - 4 ≤ c.val)).card ≤ 8 := by
  rw [Finset.filter_or]
  have h1 : (Finset.univ.filter (fun c : ZMod q => c.val < 4)).card ≤ 4 := by
    calc (Finset.univ.filter (fun c : ZMod q => c.val < 4)).card
        ≤ (Finset.range 4).card :=
          Finset.card_le_card_of_injOn ZMod.val
            (fun c hc => by
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
              simpa using hc)
            (fun a _ b _ hab => ZMod.val_injective q hab)
      _ = 4 := Finset.card_range 4
  have h2 : (Finset.univ.filter (fun c : ZMod q => q - 4 ≤ c.val)).card ≤ 4 := by
    calc (Finset.univ.filter (fun c : ZMod q => q - 4 ≤ c.val)).card
        ≤ (Finset.Ico (q - 4) q).card :=
          Finset.card_le_card_of_injOn ZMod.val
            (fun c hc => by
              simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hc
              simp only [Finset.mem_coe, Finset.mem_Ico]
              exact ⟨hc, ZMod.val_lt c⟩)
            (fun a _ b _ hab => ZMod.val_injective q hab)
      _ = 4 := by rw [Nat.card_Ico]; omega
  calc (Finset.univ.filter (fun c : ZMod q => c.val < 4)
        ∪ Finset.univ.filter (fun c : ZMod q => q - 4 ≤ c.val)).card
      ≤ (Finset.univ.filter (fun c : ZMod q => c.val < 4)).card
        + (Finset.univ.filter (fun c : ZMod q => q - 4 ≤ c.val)).card :=
        Finset.card_union_le _ _
    _ ≤ 4 + 4 := add_le_add h1 h2
    _ = 8 := rfl

/-! # Theorem 1.16 (Weyl-type Diophantine sum bound) -/

/-- **Theorem 1.16** (W.W.L. Chen, *Hardy–Littlewood Method*, Ch. 1 §1.6).
Assembled from Phases 6a-6f: the harmonic bound (6b/6c), the residue-decomposition
case-split showing the rational part dominates for `j=0` (6d), the residue-completeness
bijection needed for general `j` (6e), and the exceptional-residue count bounding how
many residues per `j` fail that domination (6f). The final combination -- splitting
each `j`'s inner sum into "good" residues (bounded via the harmonic sum) and "bad"
residues (at most 8, bounded trivially), then summing over `j` -- is genuine new
bookkeeping not yet carried out. This is the one honest gap in this phase, in the same
spirit as Phase 4b's `bridge_from_circle_method`: everything needed to close it is now
in place (6a-6f), but the assembly itself is a separate, substantial piece of work. -/
theorem weyl_sum_bound (X Y α : ℝ) (a : ℤ) (q : ℕ) [NeZero q]
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hq : 0 < q) (haq : IsCoprime a (q : ℤ))
    (hα : |α - (a : ℝ) / q| ≤ ((q : ℝ) ^ 2)⁻¹) :
    ∃ C : ℝ, 0 < C ∧
      (∑ x ∈ Finset.Icc 1 ⌊X⌋₊,
          min (X * Y / (x : ℝ)) (nearestIntDist (α * x))⁻¹)
        ≤ C * (X * Y * ((q : ℝ)⁻¹ + Y⁻¹ + (q : ℝ) / (X * Y))
                * Real.log (2 * X * q)) := by
  sorry -- the one honest gap: assembling 6a-6f's pieces (good/bad residue split per j,
        -- summed over j via 6c's harmonic bound) into the final quantitative bound.
        -- All analytic and combinatorial machinery needed is now in place (6a-6f);
        -- what remains is bookkeeping-heavy assembly, not new mathematical content.
