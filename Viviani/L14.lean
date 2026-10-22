import Viviani.Equilateral
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Layer 14: Mathlib-only restatements and a witness for Viviani's theorem

The statements `l14_*` mention only Mathlib notions. The distance from `p` to the hyperplane of
the facet opposite vertex `i` is `Metric.infDist p (affineSpan ℝ (s.points '' {i}ᶜ))`, and the
height at `k` is the same distance from the vertex `s.points k` to its opposite facet hyperplane.
The closed simplex is Mathlib's `closedInterior` (or `convexHull` when the ambient space is a
vector space).

`l14w_viviani` is the equilateral triangle `e₀, e₁, e₂` in `EuclideanSpace ℝ (Fin 3)` (side `√2`,
rational coordinates) with the point of weights `(1/2, 1/4, 1/4)`. The three distances are
`h/2, h/4, h/4`, hence not all equal, and they sum to the height `h > 0`.
-/

namespace Viviani

open Affine Affine.Simplex

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P]
  [NormedAddTorsor V P]

/-! ### Bridges -/

theorem l14b_dist_eq_infDist {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) (p : P) :
    dist p ((s.faceOpposite i).orthogonalProjectionSpan p) =
      Metric.infDist p (affineSpan ℝ (s.points '' {i}ᶜ)) := by
  rw [orthogonalProjectionSpan, EuclideanGeometry.dist_orthogonalProjection_eq_infDist,
    range_faceOpposite_points]

theorem l14b_height_eq_infDist {n : ℕ} [NeZero n] (s : Simplex ℝ P n) (i : Fin (n + 1)) :
    s.height i = Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) :=
  l14b_dist_eq_infDist s i (s.points i)

/-! ### Mathlib-only statements -/

/-- **Generalised Viviani (barycentric form).** `∑ dᵢ(p)/hᵢ = 1` on the affine span. -/
theorem l14_sum_signedInfDist_div_height {n : ℕ} [NeZero n] (s : Simplex ℝ P n) {p : P}
    (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    ∑ i, s.signedInfDist i p / Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) =
      1 := by
  simp_rw [← l14b_height_eq_infDist]
  exact s.sum_signedInfDist_div_height hp

/-- **Viviani for equal heights (signed form).** -/
theorem l14_sum_signedInfDist_eq_height {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (hh : ∀ i j, Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) =
      Metric.infDist (s.points j) (affineSpan ℝ (s.points '' {j}ᶜ)))
    {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) (k : Fin (n + 1)) :
    ∑ i, s.signedInfDist i p = Metric.infDist (s.points k) (affineSpan ℝ (s.points '' {k}ᶜ)) := by
  simp_rw [← l14b_height_eq_infDist] at hh ⊢
  exact s.sum_signedInfDist_eq_height hh hp k

/-- **Converse.** The signed distance sum is constant on the affine span iff all heights agree. -/
theorem l14_exists_forall_sum_signedInfDist_eq_iff {n : ℕ} [NeZero n] (s : Simplex ℝ P n) :
    (∃ c : ℝ, ∀ p ∈ affineSpan ℝ (Set.range s.points), ∑ i, s.signedInfDist i p = c) ↔
      ∀ i j, Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) =
        Metric.infDist (s.points j) (affineSpan ℝ (s.points '' {j}ᶜ)) := by
  simp_rw [← l14b_height_eq_infDist]
  exact s.exists_forall_sum_signedInfDist_eq_iff

/-- **Viviani for equal heights (unsigned form, closed simplex).** -/
theorem l14_sum_infDist_eq_height {n : ℕ} [NeZero n] (s : Simplex ℝ P n)
    (hh : ∀ i j, Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) =
      Metric.infDist (s.points j) (affineSpan ℝ (s.points '' {j}ᶜ)))
    {p : P} (hp : p ∈ s.closedInterior) (k : Fin (n + 1)) :
    ∑ i, Metric.infDist p (affineSpan ℝ (s.points '' {i}ᶜ)) =
      Metric.infDist (s.points k) (affineSpan ℝ (s.points '' {k}ᶜ)) := by
  simp_rw [← l14b_height_eq_infDist, ← l14b_dist_eq_infDist] at hh ⊢
  exact s.sum_dist_eq_height hh hp k

/-- **Equilateral simplices have equal heights.** -/
theorem l14_equilateral_height_eq {n : ℕ} [NeZero n] {s : Simplex ℝ P n} (he : s.Equilateral)
    (i j : Fin (n + 1)) :
    Metric.infDist (s.points i) (affineSpan ℝ (s.points '' {i}ᶜ)) =
      Metric.infDist (s.points j) (affineSpan ℝ (s.points '' {j}ᶜ)) := by
  rw [← l14b_height_eq_infDist, ← l14b_height_eq_infDist]
  exact he.height_eq i j

/-- **Viviani for regular simplices.** -/
theorem l14_regular_sum_infDist {n : ℕ} [NeZero n] {s : Simplex ℝ P n} (hr : s.Regular)
    {p : P} (hp : p ∈ s.closedInterior) (k : Fin (n + 1)) :
    ∑ i, Metric.infDist p (affineSpan ℝ (s.points '' {i}ᶜ)) =
      Metric.infDist (s.points k) (affineSpan ℝ (s.points '' {k}ᶜ)) :=
  l14_sum_infDist_eq_height s (l14_equilateral_height_eq hr.equilateral) hp k

/-- **Viviani's theorem (classical).** In an equilateral triangle in a real inner product space,
for every point `p` of the convex hull, the distances to the three side lines sum to the distance
from vertex `0` to the opposite side line. -/
theorem l14_viviani_triangle {a b c : V} (hi : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b = dist b c) (hbc : dist b c = dist c a) {p : V}
    (hp : p ∈ convexHull ℝ {a, b, c}) :
    Metric.infDist p (line[ℝ, b, c]) + Metric.infDist p (line[ℝ, a, c]) +
        Metric.infDist p (line[ℝ, a, b]) = Metric.infDist a (line[ℝ, b, c]) := by
  set t : Triangle ℝ V := ⟨![a, b, c], hi⟩
  have he : t.Equilateral := by
    refine ⟨dist a b, fun i j hij => ?_⟩
    fin_cases i <;> fin_cases j <;> simp_all [t, dist_comm]
  have hp' : p ∈ t.closedInterior := by
    rw [← convexHull_eq_closedInterior]
    convert hp using 2
    ext x; simp [t, Matrix.range_cons]; tauto
  have h := l14_sum_infDist_eq_height t (l14_equilateral_height_eq he) hp' 0
  have i0 : t.points '' {0}ᶜ = {b, c} := by
    ext x; simp [t, Fin.exists_fin_succ, eq_comm]
  have i1 : t.points '' {1}ᶜ = {a, c} := by
    ext x; simp [t, Fin.exists_fin_succ, eq_comm]
  have i2 : t.points '' {2}ᶜ = {a, b} := by
    ext x; simp [t, Fin.exists_fin_succ, eq_comm]
  rw [Fin.sum_univ_three, i0, i1, i2] at h
  exact h

/-! ### Witness -/

/-- The witness triangle: the standard basis `e₀, e₁, e₂` of `ℝ³`. -/
theorem l14b_witness_indep :
    AffineIndependent ℝ (fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ)) := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.linearIndependent
  simp only [OrthonormalBasis.coe_toBasis] at this
  have e : ⇑(EuclideanSpace.basisFun (Fin 3) ℝ) = fun i : Fin 3 => EuclideanSpace.single i (1 : ℝ) :=
    funext fun i => EuclideanSpace.basisFun_apply (Fin 3) ℝ i
  rw [e] at this
  exact this.affineIndependent

/-- **Witness.** The triangle `e₀, e₁, e₂` in `ℝ³` is equilateral (nondegenerate by
construction), and the point `p = e₀/2 + e₁/4 + e₂/4` of the closed triangle has distances
`d₀ = 2 d₁`, `d₁ = d₂ > 0` to the three side lines (so the distances are not all equal), and
they sum to the distance from `e₀` to the opposite side line. -/
theorem l14w_viviani : ∃ t : Triangle ℝ (EuclideanSpace ℝ (Fin 3)),
    t.points = (fun i => EuclideanSpace.single i 1) ∧ t.Equilateral ∧
    ∃ p ∈ t.closedInterior,
      p = Finset.univ.affineCombination ℝ t.points ![1 / 2, 1 / 4, 1 / 4] ∧
      Metric.infDist p (affineSpan ℝ (t.points '' {0}ᶜ)) =
        2 * Metric.infDist p (affineSpan ℝ (t.points '' {1}ᶜ)) ∧
      Metric.infDist p (affineSpan ℝ (t.points '' {1}ᶜ)) =
        Metric.infDist p (affineSpan ℝ (t.points '' {2}ᶜ)) ∧
      0 < Metric.infDist p (affineSpan ℝ (t.points '' {1}ᶜ)) ∧
      ∑ i, Metric.infDist p (affineSpan ℝ (t.points '' {i}ᶜ)) =
        Metric.infDist (t.points 0) (affineSpan ℝ (t.points '' {0}ᶜ)) := by
  set t : Triangle ℝ (EuclideanSpace ℝ (Fin 3)) := ⟨_, l14b_witness_indep⟩
  have he : t.Equilateral := by
    refine ⟨√2, fun i j hij => ?_⟩
    rw [EuclideanSpace.dist_eq]
    congr 1
    fin_cases i <;> fin_cases j <;> simp_all [t, Fin.sum_univ_three] <;> norm_num
  have hw : ∑ i, (![1 / 2, 1 / 4, 1 / 4] : Fin 3 → ℝ) i = 1 := by
    simp [Fin.sum_univ_three]; norm_num
  set p := Finset.univ.affineCombination ℝ t.points ![1 / 2, 1 / 4, 1 / 4]
  have hp : p ∈ t.closedInterior := by
    rw [affineCombination_mem_closedInterior_iff hw]
    intro i; fin_cases i <;> simp <;> norm_num
  have hd : ∀ i, Metric.infDist p (affineSpan ℝ (t.points '' {i}ᶜ)) =
      (![1 / 2, 1 / 4, 1 / 4] : Fin 3 → ℝ) i * t.height 0 := fun i => by
    rw [← l14b_dist_eq_infDist, ← t.signedInfDist_eq_dist_of_mem_closedInterior hp,
      t.signedInfDist_affineCombination_eq_mul_height hw, he.height_eq i 0]
  have hh := t.height_pos 0
  refine ⟨t, rfl, he, p, hp, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hd, hd]; simp; ring
  · rw [hd, hd]; simp
  · rw [hd]; simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; positivity
  · exact l14_sum_infDist_eq_height t (l14_equilateral_height_eq he) hp 0

end Viviani
