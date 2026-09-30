import Viviani.Basic

/-!
# Viviani's theorem for simplices with equal heights
-/

open Finset EuclideanGeometry

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

namespace Affine.Simplex

variable {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n)

/-- The signed distance from a vertex to its opposite facet is the height. -/
theorem signedInfDist_points_self (i : Fin (n + 1)) :
    s.signedInfDist i (s.points i) = s.height i := by
  rw [s.signedInfDist_apply_self i, Affine.Simplex.height, dist_eq_norm_vsub V]
  rfl

/-- The sum of the signed distances from a vertex to all facets is the height at that vertex. -/
theorem sum_signedInfDist_points (j : Fin (n + 1)) :
    ∑ i, s.signedInfDist i (s.points j) = s.height j := by
  rw [Finset.sum_eq_single j]
  · exact s.signedInfDist_points_self j
  · intro i _ hij
    exact s.signedInfDist_apply_of_ne (Ne.symm hij)
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- **Viviani's theorem, generalised.** If all heights of a simplex are equal, the sum of
the signed distances from any point of its affine span to the facets equals the height. -/
theorem sum_signedInfDist_eq_height (hh : ∀ i j, s.height i = s.height j)
    {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) (k : Fin (n + 1)) :
    ∑ i, s.signedInfDist i p = s.height k := by
  have h1 := s.sum_signedInfDist_div_height hp
  simp_rw [hh _ k, ← Finset.sum_div] at h1
  exact (div_eq_one_iff_eq (s.height_pos k).ne').1 h1

/-- Converse flavour: the sum of the signed distances is constant on the affine span
if and only if all heights are equal. -/
theorem exists_forall_sum_signedInfDist_eq_iff :
    (∃ c : ℝ, ∀ p ∈ affineSpan ℝ (Set.range s.points), ∑ i, s.signedInfDist i p = c) ↔
      ∀ i j, s.height i = s.height j := by
  constructor
  · rintro ⟨c, hc⟩ i j
    rw [← s.sum_signedInfDist_points i, ← s.sum_signedInfDist_points j,
      hc _ (mem_affineSpan ℝ (Set.mem_range_self i)),
      hc _ (mem_affineSpan ℝ (Set.mem_range_self j))]
  · intro hh
    exact ⟨s.height 0, fun p hp ↦ s.sum_signedInfDist_eq_height hh hp 0⟩

/-- For a point of the closed simplex, signed distances to the facets are nonnegative. -/
theorem signedInfDist_nonneg_of_mem_closedInterior {p : P} (hp : p ∈ s.closedInterior)
    (i : Fin (n + 1)) : 0 ≤ s.signedInfDist i p := by
  simp only [Affine.Simplex.closedInterior, Affine.Simplex.setInterior, Set.mem_ofPred_eq] at hp
  obtain ⟨w, hw, hI, rfl⟩ := hp
  rw [signedInfDist_affineCombination_eq_mul_height s hw]
  exact mul_nonneg (hI i).1 (s.height_pos i).le

/-- For a point of the closed simplex, the signed distance to a facet is the (unsigned)
distance to the affine span of that facet. -/
theorem signedInfDist_eq_dist_of_mem_closedInterior {p : P} (hp : p ∈ s.closedInterior)
    (i : Fin (n + 1)) :
    s.signedInfDist i p = dist p ((s.faceOpposite i).orthogonalProjectionSpan p) := by
  rw [← Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range i
    (Affine.Simplex.closedInterior_subset_affineSpan hp),
    abs_of_nonneg (s.signedInfDist_nonneg_of_mem_closedInterior hp i)]

/-- **Viviani's theorem (unsigned form).** For a simplex with all heights equal and any point
of the closed simplex, the distances to the (affine spans of the) facets sum to the height. -/
theorem sum_dist_eq_height (hh : ∀ i j, s.height i = s.height j)
    {p : P} (hp : p ∈ s.closedInterior) (k : Fin (n + 1)) :
    ∑ i, dist p ((s.faceOpposite i).orthogonalProjectionSpan p) = s.height k := by
  simp_rw [← s.signedInfDist_eq_dist_of_mem_closedInterior hp]
  exact s.sum_signedInfDist_eq_height hh (Affine.Simplex.closedInterior_subset_affineSpan hp) k

end Affine.Simplex
