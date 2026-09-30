import Viviani.Heights
import Mathlib.Geometry.Euclidean.Simplex
import Mathlib.Geometry.Euclidean.PerpBisector

/-!
# Equilateral simplices have equal heights

For an equilateral simplex, the reflection in the perpendicular bisector of the edge
`[pᵢ, pⱼ]` swaps `pᵢ` and `pⱼ` and fixes all other vertices; since heights are
invariant under isometries, `hᵢ = hⱼ`. Hence Viviani's theorem applies to every
equilateral (in particular every regular) simplex, and to the equilateral triangle.
-/

open Finset EuclideanGeometry AffineSubspace

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Viviani

/-- The reflection of `P` in the perpendicular bisector of `[a, b]`. -/
noncomputable def perpReflection (a b : P) : P ≃ᵃⁱ[ℝ] P :=
  ((AffineIsometryEquiv.vaddConst ℝ (midpoint ℝ a b)).symm.trans
      (Submodule.reflection (ℝ ∙ (b -ᵥ a))ᗮ).toAffineIsometryEquiv).trans
    (AffineIsometryEquiv.vaddConst ℝ (midpoint ℝ a b))

theorem perpReflection_apply (a b x : P) :
    perpReflection a b x =
      Submodule.reflection (ℝ ∙ (b -ᵥ a))ᗮ (x -ᵥ midpoint ℝ a b) +ᵥ midpoint ℝ a b :=
  rfl

theorem left_vsub_midpoint_eq_neg (a b : P) :
    a -ᵥ midpoint ℝ a b = -((⅟2 : ℝ) • (b -ᵥ a)) := by
  rw [left_vsub_midpoint, ← smul_neg, neg_vsub_eq_vsub_rev]

theorem perpReflection_left (a b : P) : perpReflection a b a = b := by
  rw [perpReflection_apply, left_vsub_midpoint_eq_neg, map_neg, map_smul,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg, smul_neg, neg_neg,
    ← right_vsub_midpoint, vsub_vadd]

theorem perpReflection_right (a b : P) : perpReflection a b b = a := by
  rw [perpReflection_apply, right_vsub_midpoint, map_smul,
    Submodule.reflection_orthogonalComplement_singleton_eq_neg, smul_neg,
    ← left_vsub_midpoint_eq_neg, vsub_vadd]

theorem perpReflection_of_dist_eq {a b c : P} (h : dist c a = dist c b) :
    perpReflection a b c = c := by
  have hc : c ∈ perpBisector a b := mem_perpBisector_iff_dist_eq.2 h
  rw [mem_perpBisector_iff_inner_eq_zero'] at hc
  rw [perpReflection_apply, Submodule.reflection_mem_subspace_eq_self, vsub_vadd]
  exact (Submodule.mem_orthogonal_singleton_iff_inner_right).2 hc

end Viviani

namespace Affine.Simplex

open Viviani

variable {n : ℕ} [NeZero n]

/-- **Equilateral simplices have equal heights.** -/
theorem Equilateral.height_eq {s : Affine.Simplex ℝ P n} (he : s.Equilateral)
    (i j : Fin (n + 1)) : s.height i = s.height j := by
  rcases eq_or_ne i j with rfl | hij
  · rfl
  let f := perpReflection (s.points i) (s.points j)
  have hmap : s.map f.toAffineIsometry.toAffineMap f.toAffineIsometry.injective =
      s.reindex (Equiv.swap i j) := by
    ext k
    rw [Affine.Simplex.map_points, Affine.Simplex.reindex_points, Function.comp_apply,
      Function.comp_apply, Equiv.symm_swap]
    rcases eq_or_ne k i with rfl | hki
    · rw [Equiv.swap_apply_left]
      exact perpReflection_left _ _
    rcases eq_or_ne k j with rfl | hkj
    · rw [Equiv.swap_apply_right]
      exact perpReflection_right _ _
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    exact perpReflection_of_dist_eq (he.dist_eq hki hkj)
  have h1 := s.height_map f.toAffineIsometry i
  rw [hmap, Affine.Simplex.height_reindex, Function.comp_apply, Equiv.symm_swap,
    Equiv.swap_apply_left] at h1
  exact h1.symm

/-- Viviani's theorem for equilateral simplices (signed form, whole affine span). -/
theorem Equilateral.sum_signedInfDist_eq_height {s : Affine.Simplex ℝ P n}
    (he : s.Equilateral) {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points))
    (k : Fin (n + 1)) : ∑ i, s.signedInfDist i p = s.height k :=
  s.sum_signedInfDist_eq_height he.height_eq hp k

/-- Viviani's theorem for regular simplices (unsigned form, closed simplex). -/
theorem Regular.sum_dist_eq_height {s : Affine.Simplex ℝ P n} (hr : s.Regular)
    {p : P} (hp : p ∈ s.closedInterior) (k : Fin (n + 1)) :
    ∑ i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = s.height k :=
  s.sum_dist_eq_height hr.equilateral.height_eq hp k

end Affine.Simplex

namespace Viviani

/-- **Viviani's theorem (classical).** In an equilateral triangle, the sum of the distances
from any point of the closed triangle to the three side lines equals the altitude. -/
theorem equilateral_triangle {t : Affine.Triangle ℝ P} (he : t.Equilateral)
    {p : P} (hp : p ∈ t.closedInterior) (k : Fin 3) :
    ∑ i, dist p ((t.faceOpposite i).orthogonalProjectionSpan p) = t.height k :=
  t.sum_dist_eq_height he.height_eq hp k

/-- The classical statement written out with the three sides. -/
theorem equilateral_triangle' {t : Affine.Triangle ℝ P} (he : t.Equilateral)
    {p : P} (hp : p ∈ t.closedInterior) :
    dist p ((t.faceOpposite 0).orthogonalProjectionSpan p) +
      dist p ((t.faceOpposite 1).orthogonalProjectionSpan p) +
      dist p ((t.faceOpposite 2).orthogonalProjectionSpan p) = t.height 0 := by
  rw [← equilateral_triangle he hp 0, Fin.sum_univ_three]

end Viviani
