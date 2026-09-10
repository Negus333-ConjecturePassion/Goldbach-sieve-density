import Goldbach.OffDiagonalCertificate.Definitions
import Mathlib.Tactic

open scoped BigOperators

namespace Goldbach.OffDiagonalCertificate

/-- Every real displacement weight is positive-part minus negative-part. -/
theorem weight_eq_positivePart_sub_negativePart
    (τ : ℤ → ℝ) (k : ℤ) :
    τ k = positivePart τ k - negativePart τ k := by
  unfold positivePart negativePart
  by_cases h : 0 ≤ τ k
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
    ring
  · have h' : τ k ≤ 0 := le_of_not_ge h
    rw [max_eq_right h', max_eq_left (neg_nonneg.mpr h')]
    ring

/-- Positive signed imbalance is exactly negative mass < positive mass. -/
theorem mod3SignedImbalance_pos_iff_negativeMass_lt_positiveMass
    (N : ℕ)
    (τ : ℤ → ℝ)
    (r : ℤ) :
    0 < mod3SignedImbalance N τ r
      ↔ mod3NegativeMass N τ r < mod3PositiveMass N τ r := by
  unfold mod3SignedImbalance
  constructor <;> intro h <;> linarith

/-- If every populated displacement lies in the chosen window, the intrinsic
favorable core equals the complete positive mass in that residue. -/
theorem intrinsicFavorableCore_eq_mod3PositiveMass_of_all_mem_window
    (N : ℕ)
    (τ : ℤ → ℝ)
    (Q : ℝ)
    (M : ℕ)
    (r : ℤ)
    (hwindow :
      ∀ k ∈ displacementFinset N,
        LobePairCoreWindow Q M k) :
    intrinsicFavorableLobePairCore N τ Q M r
      =
    mod3PositiveMass N τ r := by
  classical
  unfold intrinsicFavorableLobePairCore mod3PositiveMass mod3CellSum
  apply Finset.sum_congr rfl
  intro k hk
  have hwin : LobePairCoreWindow Q M k := hwindow k hk
  by_cases hres : k % (3 : ℤ) = r
  · simp [hres, hwin]
  · simp [hres]

/-- Structural certificate bridge: full-window containment plus Δ_r > 0
forces negative mass below the intrinsic favorable core. -/
theorem negativeMass_lt_intrinsicCore_of_all_mem_window_of_signedImbalance_pos
    (N : ℕ)
    (τ : ℤ → ℝ)
    (Q : ℝ)
    (M : ℕ)
    (r : ℤ)
    (hwindow :
      ∀ k ∈ displacementFinset N,
        LobePairCoreWindow Q M k)
    (hDelta :
      0 < mod3SignedImbalance N τ r) :
    mod3NegativeMass N τ r
      <
    intrinsicFavorableLobePairCore N τ Q M r := by
  have hmass :
      mod3NegativeMass N τ r < mod3PositiveMass N τ r :=
    (mod3SignedImbalance_pos_iff_negativeMass_lt_positiveMass
      N τ r).1 hDelta
  rw [
    intrinsicFavorableCore_eq_mod3PositiveMass_of_all_mem_window
      N τ Q M r hwindow
  ]
  exact hmass

end Goldbach.OffDiagonalCertificate
