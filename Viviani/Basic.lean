import Mathlib.Geometry.Euclidean.Incenter

/-!
# Viviani's theorem, generalised to simplices

For a simplex `s` in a Euclidean affine space and a point `p` in its affine span,
the signed distance from `p` to the facet opposite vertex `i`, divided by the
height `s.height i`, is the `i`-th barycentric coordinate of `p`. Summing gives
`∑ i, s.signedInfDist i p / s.height i = 1`.
-/

open Finset EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

variable {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n)

/-- The signed distance to facet `i` of an affine combination is its weight times the height. -/
theorem signedInfDist_affineCombination_eq_mul_height {w : Fin (n + 1) → ℝ}
    (hw : ∑ i, w i = 1) (i : Fin (n + 1)) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w) = w i * s.height i := by
  rw [s.signedInfDist_affineCombination i hw, Affine.Simplex.height, dist_eq_norm_vsub V]
  rfl

/-- Barycentric coordinates are signed distances divided by heights. -/
theorem signedInfDist_div_height_affineCombination {w : Fin (n + 1) → ℝ}
    (hw : ∑ i, w i = 1) (i : Fin (n + 1)) :
    s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w) / s.height i = w i := by
  rw [signedInfDist_affineCombination_eq_mul_height s hw, mul_div_assoc,
    div_self (s.height_pos i).ne', mul_one]

/-- **Generalised Viviani identity.** For any point `p` in the affine span of a simplex,
the signed distances to the facets, each divided by the corresponding height, sum to `1`. -/
theorem sum_signedInfDist_div_height {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    ∑ i, s.signedInfDist i p / s.height i = 1 := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  simp_rw [signedInfDist_div_height_affineCombination s hw]
  exact hw

end Affine.Simplex
