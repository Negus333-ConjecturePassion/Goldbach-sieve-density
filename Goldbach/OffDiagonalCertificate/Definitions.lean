import Mathlib.Tactic

open scoped BigOperators

namespace Goldbach.OffDiagonalCertificate

/-- Prime support up to the target N. -/
def primeSupportFinset (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

theorem mem_primeSupportFinset_iff
    (N p : ℕ) :
    p ∈ primeSupportFinset N ↔ p ≤ N ∧ Nat.Prime p := by
  simp [primeSupportFinset]

/-- Ordered prime-support pairs. -/
def primeSupportPairFinset
    (N : ℕ) : Finset (ℕ × ℕ) :=
  primeSupportFinset N ×ˢ primeSupportFinset N

/-- Integer Goldbach displacement k = p + q - N. -/
def displacementInt
    (N p q : ℕ) : ℤ :=
  (p : ℤ) + (q : ℤ) - (N : ℤ)

/-- Displacement attached to an ordered prime-support pair. -/
def pairDisplacement
    (N : ℕ) (x : ℕ × ℕ) : ℤ :=
  displacementInt N x.1 x.2

/-- Finite set of displacements actually produced by ordered prime-support pairs. -/
def displacementFinset
    (N : ℕ) : Finset ℤ :=
  (primeSupportPairFinset N).image (pairDisplacement N)

/-- Zero displacement is exactly the Goldbach representation fiber p + q = N. -/
theorem pairDisplacement_eq_zero_iff
    (N : ℕ) (x : ℕ × ℕ) :
    pairDisplacement N x = 0 ↔ x.1 + x.2 = N := by
  unfold pairDisplacement displacementInt
  constructor
  · intro h
    have hz : (x.1 : ℤ) + (x.2 : ℤ) = (N : ℤ) := by
      omega
    exact_mod_cast hz
  · intro h
    have hz : (x.1 : ℤ) + (x.2 : ℤ) = (N : ℤ) := by
      exact_mod_cast h
    omega

/-- Sum of a real displacement weight over one residue class modulo 3. -/
noncomputable def mod3CellSum
    (s : Finset ℤ)
    (f : ℤ → ℝ)
    (r : ℤ) : ℝ :=
  ∑ k ∈ s, if k % (3 : ℤ) = r then f k else 0

/-- Positive part of one signed displacement weight. -/
noncomputable def positivePart
    (τ : ℤ → ℝ) (k : ℤ) : ℝ :=
  max (τ k) 0

/-- Negative-magnitude part of one signed displacement weight. -/
noncomputable def negativePart
    (τ : ℤ → ℝ) (k : ℤ) : ℝ :=
  max (-τ k) 0

/-- Positive mass in one mod-3 displacement cell. -/
noncomputable def mod3PositiveMass
    (N : ℕ) (τ : ℤ → ℝ) (r : ℤ) : ℝ :=
  mod3CellSum (displacementFinset N) (positivePart τ) r

/-- Negative-magnitude mass in one mod-3 displacement cell. -/
noncomputable def mod3NegativeMass
    (N : ℕ) (τ : ℤ → ℝ) (r : ℤ) : ℝ :=
  mod3CellSum (displacementFinset N) (negativePart τ) r

/-- Signed residue imbalance Δ_r = positive mass - negative-magnitude mass. -/
noncomputable def mod3SignedImbalance
    (N : ℕ) (τ : ℤ → ℝ) (r : ℤ) : ℝ :=
  mod3PositiveMass N τ r - mod3NegativeMass N τ r

/-- First M+1 paired centered-kernel lobes occupy |k| < (M+1)Q. -/
def LobePairCoreWindow
    (Q : ℝ) (M : ℕ) (k : ℤ) : Prop :=
  |(k : ℝ)| < ((M : ℝ) + 1) * Q

/-- Favorable positive mass restricted to one residue and the selected lobe-pair window. -/
noncomputable def intrinsicFavorableLobePairCore
    (N : ℕ)
    (τ : ℤ → ℝ)
    (Q : ℝ)
    (M : ℕ)
    (r : ℤ) : ℝ := by
  classical
  exact
    ∑ k ∈ displacementFinset N,
      if k % (3 : ℤ) = r then
        if LobePairCoreWindow Q M k then
          positivePart τ k
        else
          0
      else
        0

end Goldbach.OffDiagonalCertificate