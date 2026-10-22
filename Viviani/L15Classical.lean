import Viviani.Basic
import Viviani.Heights
import Viviani.Equilateral

/-!
# Layer 15: classical statements

Layer 15. These definitions and statements were written independently, from textbook statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves (or proves part of) one of them from this development.
-/

open EuclideanGeometry

noncomputable section

open scoped Classical

namespace Viviani.Classical

variable {V : Type*} {P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [MetricSpace P] [NormedAddTorsor V P]

/-- OWN DEFINITION (writer, verbatim). -/
def signedDistLine (l : AffineSubspace ℝ P) (ref p : P) : ℝ :=
  if l.SOppSide p ref then -Metric.infDist p (l : Set P) else Metric.infDist p (l : Set P)

/-! ## Writer statements, verbatim, packaged as `Prop`s. -/

def classical_TriSimplex3_a : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (heq : (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).Equilateral)
    (X : P) (hX : X ∈ (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).interior),
    Metric.infDist X (line[ℝ, B, C] : Set P) + Metric.infDist X (line[ℝ, C, A] : Set P) +
      Metric.infDist X (line[ℝ, A, B] : Set P) = Real.sqrt 3 / 2 * dist A B

def classical_TriSimplex3_b_closed : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (heq : (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).Equilateral)
    (X : P) (hX : X ∈ (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).closedInterior),
    Metric.infDist X (line[ℝ, B, C] : Set P) + Metric.infDist X (line[ℝ, C, A] : Set P) +
      Metric.infDist X (line[ℝ, A, B] : Set P) = Real.sqrt 3 / 2 * dist A B

def classical_TriSimplex3_b [Fact (Module.finrank ℝ V = 2)] : Prop :=
  ∀ (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (heq : (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).Equilateral) (X : P),
    signedDistLine line[ℝ, B, C] A X + signedDistLine line[ℝ, C, A] B X +
      signedDistLine line[ℝ, A, B] C X = Real.sqrt 3 / 2 * dist A B

/-! ## Bridge: the writer's `signedDistLine` against the face equals Mathlib's
`Affine.Simplex.signedInfDist` on the affine span of the simplex. -/

theorem signedDistLine_face_eq {n : ℕ} [NeZero n] (s : Affine.Simplex ℝ P n) (i : Fin (n + 1))
    {p : P} (hp : p ∈ affineSpan ℝ (Set.range s.points)) :
    signedDistLine (affineSpan ℝ (s.points '' {i}ᶜ)) (s.points i) p = s.signedInfDist i p := by
  obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  have hinf : Metric.infDist (Finset.univ.affineCombination ℝ s.points w)
      ((affineSpan ℝ (s.points '' {i}ᶜ) : AffineSubspace ℝ P) : Set P) =
      |s.signedInfDist i (Finset.univ.affineCombination ℝ s.points w)| := by
    rw [Affine.Simplex.abs_signedInfDist_eq_dist_of_mem_affineSpan_range i hp,
      Affine.Simplex.orthogonalProjectionSpan, dist_orthogonalProjection_eq_infDist,
      Affine.Simplex.range_faceOpposite_points]
  have hside := s.sOppSide_affineSpan_faceOpposite_point_right_iff hw (i := i)
  rw [Affine.Simplex.range_faceOpposite_points] at hside
  rw [signedDistLine, hinf, Affine.Simplex.signedInfDist_affineCombination _ _ hw]
  have hpos : 0 < ‖s.points i -ᵥ (s.faceOpposite i).orthogonalProjectionSpan (s.points i)‖ := by
    rw [norm_pos_iff, vsub_ne_zero]
    exact s.ne_altitudeFoot i
  split_ifs with h
  · have := hside.1 h
    rw [abs_of_neg (mul_neg_of_neg_of_pos this hpos), neg_neg]
  · have : 0 ≤ w i := by
      by_contra h'; exact h (hside.2 (lt_of_not_ge h'))
    rw [abs_of_nonneg (mul_nonneg this hpos.le)]

lemma face_eq (A B C : P) :
    affineSpan ℝ (![A, B, C] '' {0}ᶜ) = line[ℝ, B, C] ∧
    affineSpan ℝ (![A, B, C] '' {1}ᶜ) = line[ℝ, C, A] ∧
    affineSpan ℝ (![A, B, C] '' {2}ᶜ) = line[ℝ, A, B] := by
  have e0 : ({0}ᶜ : Set (Fin 3)) = {1, 2} := by ext j; fin_cases j <;> simp
  have e1 : ({1}ᶜ : Set (Fin 3)) = {2, 0} := by ext j; fin_cases j <;> simp
  have e2 : ({2}ᶜ : Set (Fin 3)) = {0, 1} := by ext j; fin_cases j <;> simp
  refine ⟨?_, ?_, ?_⟩
  · rw [e0, Set.image_pair]; rfl
  · rw [e1, Set.image_pair]; rfl
  · rw [e2, Set.image_pair]; rfl

/-- NEW PROOF. In an equilateral triangle the altitude from vertex `2` is `(√3/2)·|AB|`. -/
theorem height_two_eq (A B C : P) (h : AffineIndependent ℝ ![A, B, C])
    (heq : (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).Equilateral) :
    (⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).height 2 = Real.sqrt 3 / 2 * dist A B := by
  set t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩ with ht
  obtain ⟨d, hd⟩ := heq
  have dAB : dist A B = d := hd 0 1 (by decide)
  have dAC : dist A C = d := hd 0 2 (by decide)
  have dBC : dist B C = d := hd 1 2 (by decide)
  set F := t.altitudeFoot 2 with hFdef
  have hF : F ∈ line[ℝ, A, B] := by
    have := t.altitudeFoot_mem_affineSpan_image_compl 2
    rwa [(face_eq A B C).2.2] at this
  obtain ⟨r, hr⟩ := (mem_affineSpan_pair_iff_exists_lineMap_eq).1 hF
  have o0 := t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 2) (j := 0) (by decide)
  have o1 := t.inner_vsub_altitudeFoot_vsub_altitudeFoot_eq_zero (i := 2) (j := 1) (by decide)
  change inner ℝ (A -ᵥ F) (C -ᵥ F) = 0 at o0
  change inner ℝ (B -ᵥ F) (C -ᵥ F) = 0 at o1
  set u := B -ᵥ A
  set v := C -ᵥ A
  have hFA : F -ᵥ A = r • u := by rw [← hr, AffineMap.lineMap_vsub_left]
  have eA : A -ᵥ F = -(r • u) := by rw [← hFA, neg_vsub_eq_vsub_rev]
  have eB : B -ᵥ F = u - r • u := by rw [← hFA, vsub_sub_vsub_cancel_right]
  have eC : C -ᵥ F = v - r • u := by rw [← hFA, vsub_sub_vsub_cancel_right]
  have nu : ‖u‖ ^ 2 = d ^ 2 := by rw [← dAB, dist_comm, dist_eq_norm_vsub V]
  have nv : ‖v‖ ^ 2 = d ^ 2 := by rw [← dAC, dist_comm, dist_eq_norm_vsub V]
  have nvu : ‖v - u‖ ^ 2 = d ^ 2 := by
    rw [← dBC, dist_comm, dist_eq_norm_vsub V, vsub_sub_vsub_cancel_right]
  rw [norm_sub_sq_real, nu, nv] at nvu
  have huv : inner ℝ u v = d ^ 2 / 2 := by rw [real_inner_comm]; linarith
  rw [eA, eC] at o0
  rw [eB, eC] at o1
  simp only [inner_neg_left, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, huv, nu] at o0 o1
  have hd0 : 0 < d := by
    rw [← dAB]; exact dist_pos.2 (h.injective.ne (show (0 : Fin 3) ≠ 1 by decide))
  have hr2 : r = 1 / 2 := by
    have : d ^ 2 * (1 - 2 * r) = 0 := by linear_combination 2 * (o1 - o0)
    rcases mul_eq_zero.1 this with h0 | h0
    · nlinarith
    · linarith
  have hh : t.height 2 ^ 2 = 3 / 4 * d ^ 2 := by
    rw [Affine.Simplex.height, dist_eq_norm_vsub V]
    change ‖C -ᵥ F‖ ^ 2 = _
    rw [eC, norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, nu, nv, real_inner_comm, huv, hr2]
    ring
  have h3 : (Real.sqrt 3 / 2 * d) ^ 2 = 3 / 4 * d ^ 2 := by
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
  rw [dAB]
  exact (pow_left_inj₀ (t.height_pos 2).le (by positivity) two_ne_zero).1 (hh.trans h3.symm)

lemma infDist_face (A B C : P) (h : AffineIndependent ℝ ![A, B, C]) (X : P) :
    let t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
    dist X ((t.faceOpposite 0).orthogonalProjectionSpan X) =
        Metric.infDist X (line[ℝ, B, C] : Set P) ∧
      dist X ((t.faceOpposite 1).orthogonalProjectionSpan X) =
        Metric.infDist X (line[ℝ, C, A] : Set P) ∧
      dist X ((t.faceOpposite 2).orthogonalProjectionSpan X) =
        Metric.infDist X (line[ℝ, A, B] : Set P) := by
  intro t
  obtain ⟨f0, f1, f2⟩ := face_eq A B C
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [Affine.Simplex.orthogonalProjectionSpan, dist_orthogonalProjection_eq_infDist,
      Affine.Simplex.range_faceOpposite_points]
    first | (change Metric.infDist X (affineSpan ℝ (![A, B, C] '' {0}ᶜ) : Set P) = _; rw [f0])
          | (change Metric.infDist X (affineSpan ℝ (![A, B, C] '' {1}ᶜ) : Set P) = _; rw [f1])
          | (change Metric.infDist X (affineSpan ℝ (![A, B, C] '' {2}ᶜ) : Set P) = _; rw [f2])

theorem cov_TriSimplex3_b_closed : classical_TriSimplex3_b_closed (P := P) := by
  intro A B C h heq X hX
  obtain ⟨e0, e1, e2⟩ := infDist_face A B C h X
  rw [← e0, ← e1, ← e2, Viviani.equilateral_triangle' heq hX,
    heq.height_eq 0 2, height_two_eq A B C h heq]

theorem cov_TriSimplex3_a : classical_TriSimplex3_a (P := P) := fun A B C h heq X hX =>
  cov_TriSimplex3_b_closed A B C h heq X
    ((⟨![A, B, C], h⟩ : Affine.Triangle ℝ P).interior_subset_closedInterior hX)

theorem cov_TriSimplex3_b [Fact (Module.finrank ℝ V = 2)] : classical_TriSimplex3_b (P := P) := by
  intro A B C h heq X
  set t : Affine.Triangle ℝ P := ⟨![A, B, C], h⟩
  have : FiniteDimensional ℝ V := FiniteDimensional.of_fact_finrank_eq_two
  have htop : affineSpan ℝ (Set.range t.points) = ⊤ := by
    rw [t.independent.affineSpan_eq_top_iff_card_eq_finrank_add_one,
      (Fact.out : Module.finrank ℝ V = 2), Fintype.card_fin]
  have hX : X ∈ affineSpan ℝ (Set.range t.points) := by rw [htop]; exact AffineSubspace.mem_top _ _ _
  obtain ⟨f0, f1, f2⟩ := face_eq A B C
  have g0 := signedDistLine_face_eq t 0 hX
  have g1 := signedDistLine_face_eq t 1 hX
  have g2 := signedDistLine_face_eq t 2 hX
  change signedDistLine (affineSpan ℝ (![A, B, C] '' {0}ᶜ)) A X = _ at g0
  change signedDistLine (affineSpan ℝ (![A, B, C] '' {1}ᶜ)) B X = _ at g1
  change signedDistLine (affineSpan ℝ (![A, B, C] '' {2}ᶜ)) C X = _ at g2
  rw [f0] at g0; rw [f1] at g1; rw [f2] at g2
  rw [g0, g1, g2, ← height_two_eq A B C h heq, ← heq.sum_signedInfDist_eq_height hX 2,
    Fin.sum_univ_three]

end Viviani.Classical
