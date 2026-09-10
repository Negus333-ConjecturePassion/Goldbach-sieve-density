import Goldbach.OffDiagonalCertificate.StructuralBridge
import Mathlib.Tactic

namespace Goldbach.OffDiagonalCertificate

/-- If the target N is not prime, every populated prime-pair displacement
satisfies |k| < N. -/
theorem displacement_abs_lt_target_of_mem_of_not_prime
    (N : ℕ)
    (hNnotprime : ¬ Nat.Prime N)
    (k : ℤ)
    (hk : k ∈ displacementFinset N) :
    |(k : ℝ)| < (N : ℝ) := by
  classical

  have hkImage :
      k ∈ (primeSupportPairFinset N).image (pairDisplacement N) := by
    simpa [displacementFinset] using hk

  rcases Finset.mem_image.mp hkImage with ⟨x, hxPair, hxDisp⟩

  have hxprod :
      x.1 ∈ primeSupportFinset N ∧
      x.2 ∈ primeSupportFinset N := by
    simpa [primeSupportPairFinset] using hxPair

  have hpData : x.1 ≤ N ∧ Nat.Prime x.1 :=
    (mem_primeSupportFinset_iff N x.1).1 hxprod.1

  have hqData : x.2 ≤ N ∧ Nat.Prime x.2 :=
    (mem_primeSupportFinset_iff N x.2).1 hxprod.2

  have hpNe : x.1 ≠ N := by
    intro hpEq
    apply hNnotprime
    simpa [hpEq] using hpData.2

  have hqNe : x.2 ≠ N := by
    intro hqEq
    apply hNnotprime
    simpa [hqEq] using hqData.2

  have hpLt : x.1 < N := by omega
  have hqLt : x.2 < N := by omega

  have hpTwo : 2 ≤ x.1 := hpData.2.two_le
  have hqTwo : 2 ≤ x.2 := hqData.2.two_le

  have hpairBounds :
      -(N : ℤ) < pairDisplacement N x ∧
      pairDisplacement N x < (N : ℤ) := by
    unfold pairDisplacement displacementInt
    constructor <;> omega

  have hkBounds :
      -(N : ℤ) < k ∧ k < (N : ℤ) := by
    rw [← hxDisp]
    exact hpairBounds

  have hlowR : -(N : ℝ) < (k : ℝ) := by
    exact_mod_cast hkBounds.1

  have huppR : (k : ℝ) < (N : ℝ) := by
    exact_mod_cast hkBounds.2

  exact (abs_lt).2 ⟨hlowR, huppR⟩

/-- Every even N >= 4 is composite. -/
theorem even_target_not_prime_of_four_le
    (N : ℕ)
    (hN : 4 ≤ N)
    (hEven : Even N) :
    ¬ Nat.Prime N := by
  intro hPrime
  have hEqTwo : N = 2 := (hPrime.even_iff).1 hEven
  omega

/-- For even N >= 4, every actual displacement satisfies |k| < N. -/
theorem displacement_abs_lt_target_of_mem_of_even
    (N : ℕ)
    (hN : 4 ≤ N)
    (hEven : Even N)
    (k : ℤ)
    (hk : k ∈ displacementFinset N) :
    |(k : ℝ)| < (N : ℝ) := by
  exact
    displacement_abs_lt_target_of_mem_of_not_prime
      N (even_target_not_prime_of_four_le N hN hEven) k hk

/-- Fixed P=K=3, Q=N/3, M=2 support saturation. -/
theorem fixedP3_M2_all_displacements_mem_window_of_even
    (N : ℕ)
    (hN : 4 ≤ N)
    (hEven : Even N) :
    ∀ k ∈ displacementFinset N,
      LobePairCoreWindow ((N : ℝ) / 3) 2 k := by
  intro k hk

  have habs : |(k : ℝ)| < (N : ℝ) :=
    displacement_abs_lt_target_of_mem_of_even N hN hEven k hk

  unfold LobePairCoreWindow

  have hscale :
      (((2 : ℕ) : ℝ) + 1) * ((N : ℝ) / 3) = (N : ℝ) := by
    norm_num
    ring

  rw [hscale]
  exact habs

/-- Exact support saturation identity: at M=2, the intrinsic favorable core
contains all positive mass in each residue class for even N >= 4. -/
theorem fixedP3_M2_intrinsicCore_eq_mod3PositiveMass_of_even
    (N : ℕ)
    (hN : 4 ≤ N)
    (hEven : Even N)
    (τ : ℤ → ℝ)
    (r : ℤ) :
    intrinsicFavorableLobePairCore N τ ((N : ℝ) / 3) 2 r
      =
    mod3PositiveMass N τ r := by
  exact
    intrinsicFavorableCore_eq_mod3PositiveMass_of_all_mem_window
      N τ ((N : ℝ) / 3) 2 r
      (fixedP3_M2_all_displacements_mem_window_of_even N hN hEven)

/-- Paper-facing structural endpoint.  For every even N >= 56 and every
real displacement weight τ, Δ_r > 0 implies negative mass is strictly
smaller than the full intrinsic favorable core. -/
theorem fixedP3_M2_negativeMass_lt_intrinsicCore_of_ge56_even_of_signedImbalance_pos
    (N : ℕ)
    (hN : 56 ≤ N)
    (hEven : Even N)
    (τ : ℤ → ℝ)
    (r : ℤ)
    (hDelta : 0 < mod3SignedImbalance N τ r) :
    mod3NegativeMass N τ r
      <
    intrinsicFavorableLobePairCore N τ ((N : ℝ) / 3) 2 r := by
  exact
    negativeMass_lt_intrinsicCore_of_all_mem_window_of_signedImbalance_pos
      N τ ((N : ℝ) / 3) 2 r
      (fixedP3_M2_all_displacements_mem_window_of_even
        N (by omega) hEven)
      hDelta

end Goldbach.OffDiagonalCertificate
