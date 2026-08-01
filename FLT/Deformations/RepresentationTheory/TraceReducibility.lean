/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Trace criteria for reducibility in dimension two

This file develops the elementary linear-algebra part of the argument that a two-dimensional
representation satisfying `trace(g) = 1 + det(g)` is reducible.  The two lemmas below handle the
normal forms which arise from a nonidentity element having `1` as an eigenvalue.
-/

@[expose] public section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

namespace GaloisRep

variable {K k : Type*} [Field K] [Field k] [TopologicalSpace k] [IsTopologicalRing k]

private abbrev e₀ : Fin 2 → k := Pi.single 0 1
private abbrev e₁ : Fin 2 → k := Pi.single 1 1

/-- The elementary upper-triangular change of coordinates used to diagonalize a matrix with
distinct diagonal entries. -/
private def shear (c : k) : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) where
  toFun v := ![v 0 + c * v 1, v 1]
  invFun v := ![v 0 - c * v 1, v 1]
  map_add' x y := by
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;> simp <;> ring
  left_inv x := by
    funext i
    fin_cases i <;> simp <;> ring
  right_inv x := by
    funext i
    fin_cases i <;> simp <;> ring

/-- If a framed two-dimensional representation satisfies `trace = 1 + det` and contains a
nonidentity unipotent in standard upper-triangular form, then the first coordinate line is
invariant and the representation is reducible. -/
theorem not_isIrreducible_of_unipotent_normal_form
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det)
    (g : Γ K) (a : k) (ha : a ≠ 0)
    (hg : (ρ.GL g).1 = !![1, a; 0, 1]) :
    ¬ ρ.IsIrreducible := by
  let M : Γ K → Matrix (Fin 2) (Fin 2) k := fun h ↦ (ρ.GL h).1
  have hMmul (x y : Γ K) : M (x * y) = M x * M y := by
    change LinearMap.toMatrix' (ρ (x * y)) =
      LinearMap.toMatrix' (ρ x) * LinearMap.toMatrix' (ρ y)
    rw [map_mul]
    exact LinearMap.toMatrixAlgEquiv'_mul _ _
  have h10 (h : Γ K) : M h 1 0 = 0 := by
    have hprod := hchar (g * h)
    have hh := hchar h
    rw [show (ρ.GL (g * h)).1 = M g * M h by simpa [M] using hMmul g h,
      show M g = !![1, a; 0, 1] by simpa [M] using hg,
      Matrix.trace_fin_two, Matrix.det_fin_two] at hprod
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two] at hh
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hprod
    have haz : a * M h 1 0 = 0 := by
      linear_combination hprod - hh
    exact (mul_eq_zero.mp haz).resolve_left ha
  apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
    (show Module.rank k (Fin 2 → k) = 2 by simp) e₀
  · simp [e₀]
  · intro h
    refine Submodule.mem_span_singleton.mpr ⟨M h 0 0, ?_⟩
    funext i
    fin_cases i
    · simp [M, e₀, FramedGaloisRep.GL_apply]
    · simpa [M, e₀, FramedGaloisRep.GL_apply] using (h10 h).symm

/-- If a framed two-dimensional representation satisfies `trace = 1 + det` and contains an
element in standard diagonal form with distinct eigenvalues `1` and `d`, then one of the two
coordinate lines is invariant and the representation is reducible. -/
theorem not_isIrreducible_of_diagonal_normal_form
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det)
    (g : Γ K) (d : k) (hd : d ≠ 1)
    (hg : (ρ.GL g).1 = !![1, 0; 0, d]) :
    ¬ ρ.IsIrreducible := by
  let M : Γ K → Matrix (Fin 2) (Fin 2) k := fun h ↦ (ρ.GL h).1
  have hMmul (x y : Γ K) : M (x * y) = M x * M y := by
    change LinearMap.toMatrix' (ρ (x * y)) =
      LinearMap.toMatrix' (ρ x) * LinearMap.toMatrix' (ρ y)
    rw [map_mul]
    exact LinearMap.toMatrixAlgEquiv'_mul _ _
  have h00 (h : Γ K) : M h 0 0 = 1 := by
    have hprod := hchar (g * h)
    have hh := hchar h
    rw [show (ρ.GL (g * h)).1 = M g * M h by simpa [M] using hMmul g h,
      show M g = !![1, 0; 0, d] by simpa [M] using hg,
      Matrix.trace_fin_two, Matrix.det_fin_two] at hprod
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two] at hh
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hprod
    have hx : (1 - d) * (M h 0 0 - 1) = 0 := by
      linear_combination hprod - d * hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hd.symm))
  have hoffdiag (h : Γ K) : M h 0 1 * M h 1 0 = 0 := by
    have hh := hchar h
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two,
      h00 h] at hh
    linear_combination hh
  by_cases hu : ∀ h : Γ K, M h 1 0 = 0
  · apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
      (show Module.rank k (Fin 2 → k) = 2 by simp) e₀
    · simp [e₀]
    · intro h
      refine Submodule.mem_span_singleton.mpr ⟨M h 0 0, ?_⟩
      funext i
      fin_cases i
      · simp [M, e₀, FramedGaloisRep.GL_apply]
      · simpa [M, e₀, FramedGaloisRep.GL_apply] using (hu h).symm
  · push_neg at hu
    obtain ⟨h₀, hh₀⟩ := hu
    have hh₀01 : M h₀ 0 1 = 0 :=
      (mul_eq_zero.mp (hoffdiag h₀)).resolve_right hh₀
    have h01 (h : Γ K) : M h 0 1 = 0 := by
      by_contra hh
      have hh10 : M h 1 0 = 0 :=
        (mul_eq_zero.mp (hoffdiag h)).resolve_left hh
      have hprod := hoffdiag (h₀ * h)
      rw [hMmul] at hprod
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hh₀01, hh10, h00, mul_zero,
        zero_mul, add_zero, zero_add, one_mul] at hprod
      exact hh₀ (by simpa using (mul_eq_zero.mp hprod).resolve_left hh)
    apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
      (show Module.rank k (Fin 2 → k) = 2 by simp) e₁
    · simp [e₁]
    · intro h
      refine Submodule.mem_span_singleton.mpr ⟨M h 1 1, ?_⟩
      funext i
      fin_cases i
      · simpa [M, e₁, FramedGaloisRep.GL_apply] using (h01 h).symm
      · simp [M, e₁, FramedGaloisRep.GL_apply]

/-- An upper-triangular element with distinct diagonal entries can be diagonalized by a shear, so
the diagonal normal-form criterion applies. -/
theorem not_isIrreducible_of_upper_normal_form_of_ne
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det)
    (g : Γ K) (a d : k) (hd : d ≠ 1)
    (hg : (ρ.GL g).1 = !![1, a; 0, d]) :
    ¬ ρ.IsIrreducible := by
  let c : k := -a / (d - 1)
  let e : (Fin 2 → k) ≃ₗ[k] (Fin 2 → k) := shear c
  let τ : FramedGaloisRep K k (Fin 2) := ρ.conj e
  have hcharLin (x : Γ K) : LinearMap.trace k (Fin 2 → k) (ρ x) =
      1 + LinearMap.det (ρ x) := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
      ← LinearMap.det_toMatrix (Pi.basisFun k (Fin 2))]
    exact hchar x
  have hcharτLin (x : Γ K) : LinearMap.trace k (Fin 2 → k) (τ x) =
      1 + LinearMap.det (τ x) := by
    rw [show τ x = ρ.conj e x by rfl, GaloisRep.trace_conj]
    change LinearMap.trace k (Fin 2 → k) (ρ x) =
      1 + LinearMap.det (e.conj (ρ x))
    have hdet : LinearMap.det (e.conj (ρ x)) = LinearMap.det (ρ x) := by
      simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
        LinearMap.det_conj (ρ x) e
    rw [hdet]
    exact hcharLin x
  have hcharτ (x : Γ K) : (τ.GL x).1.trace = 1 + (τ.GL x).1.det := by
    have hx := hcharτLin x
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
      ← LinearMap.det_toMatrix (Pi.basisFun k (Fin 2))] at hx
    exact hx
  have hact (v : Fin 2 → k) : ρ g v = Matrix.toLin' !![1, a; 0, d] v := by
    have hmat : LinearMap.toMatrix' (ρ g) = !![1, a; 0, d] := by
      simpa only [← FramedGaloisRep.GL_apply] using hg
    conv_lhs => rw [← Matrix.toLin'_toMatrix' (ρ g)]
    rw [hmat]
  have hτe₀ : τ g e₀ = e₀ := by
    rw [show τ g e₀ = e (ρ g (e.symm e₀)) by
      simp [τ, GaloisRep.conj_apply_apply], hact]
    funext i
    fin_cases i <;>
      simp [e, shear, c, e₀, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  have hτe₁ : τ g e₁ = d • e₁ := by
    rw [show τ g e₁ = e (ρ g (e.symm e₁)) by
      simp [τ, GaloisRep.conj_apply_apply], hact]
    funext i
    fin_cases i
    · simp [e, shear, c, e₁, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
      field_simp [sub_ne_zero.mpr hd]
      ring
    · simp [e, shear, c, e₁, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]
  have hτg : (τ.GL g).1 = !![1, 0; 0, d] := by
    ext i j
    rw [FramedGaloisRep.GL_apply, LinearMap.toMatrix'_apply]
    fin_cases j
    · have hi := congrFun hτe₀ i
      fin_cases i <;> simpa [e₀] using hi
    · have hi := congrFun hτe₁ i
      fin_cases i <;> simpa [e₁] using hi
  intro hρ
  exact not_isIrreducible_of_diagonal_normal_form τ hcharτ g d hd hτg
    ((GaloisRep.isIrreducible_conj_iff ρ e).mp hρ)

/-- A two-dimensional representation for which every element satisfies
`trace(g) = 1 + det(g)` is reducible.  This is the elementary representation-theoretic part of
the Chebotarev--Brauer--Nesbitt step. -/
theorem not_isIrreducible_of_trace_eq_one_add_det
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det) :
    ¬ ρ.IsIrreducible := by
  by_cases hid : ∀ g : Γ K, (ρ.GL g).1 = 1
  · apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
      (show Module.rank k (Fin 2 → k) = 2 by simp) e₀
    · simp [e₀]
    · intro g
      have hlin : ρ g = LinearMap.id := by
        apply LinearMap.toMatrix'.injective
        rw [LinearMap.toMatrix'_id]
        exact hid g
      rw [hlin]
      exact Submodule.mem_span_singleton_self e₀
  · push_neg at hid
    obtain ⟨g, hgne⟩ := hid
    let A : Matrix (Fin 2) (Fin 2) k := (ρ.GL g).1
    have hdet : (A - 1).det = 0 := by
      have hgchar := hchar g
      rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hgchar
      change A 0 0 + A 1 1 = 1 + (A 0 0 * A 1 1 - A 0 1 * A 1 0) at hgchar
      calc
        (A - 1).det = A 0 0 * A 1 1 - A 0 0 - A 1 1 + 1 - A 0 1 * A 1 0 := by
          rw [Matrix.det_fin_two]
          simp [Matrix.sub_apply]
          ring
        _ = 0 := by linear_combination -hgchar
    obtain ⟨v, hv, hvker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    have hAv : A.mulVec v = v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hvker
      exact hvker
    have hρv : ρ g v = v := by
      have hmat : LinearMap.toMatrix' (ρ g) = A := by rfl
      conv_lhs => rw [← Matrix.toLin'_toMatrix' (ρ g)]
      rw [hmat, Matrix.toLin'_apply, hAv]
    let vv : Unit → (k ∙ v) := fun _ ↦ ⟨v, Submodule.mem_span_singleton_self v⟩
    let v₀ : Unit → (k ∙ (e₀ : Fin 2 → k)) := fun _ ↦
      ⟨(e₀ : Fin 2 → k), Submodule.mem_span_singleton_self (e₀ : Fin 2 → k)⟩
    have hvli : LinearIndependent k vv := by
      rw [linearIndependent_unique_iff]
      exact Subtype.coe_ne_coe.mp hv
    have h₀li : LinearIndependent k v₀ := by
      rw [linearIndependent_unique_iff]
      simp [v₀, e₀]
    have hvsp : (⊤ : Submodule k (k ∙ v)) ≤ Submodule.span k (Set.range vv) := by
      intro x _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.prop
      have hx : x = c • vv () := by
        apply Subtype.ext
        simpa [vv] using hc.symm
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ()))
    have h₀sp : (⊤ : Submodule k (k ∙ (e₀ : Fin 2 → k))) ≤
        Submodule.span k (Set.range v₀) := by
      intro x _
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp x.prop
      have hx : x = c • v₀ () := by
        apply Subtype.ext
        simpa [v₀] using hc.symm
      rw [hx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self ()))
    let bv : Module.Basis Unit k (k ∙ v) := Module.Basis.mk hvli hvsp
    let b₀ : Module.Basis Unit k (k ∙ (e₀ : Fin 2 → k)) := Module.Basis.mk h₀li h₀sp
    let f : (k ∙ v) ≃ₗ[k] (k ∙ (e₀ : Fin 2 → k)) := bv.equiv b₀ (Equiv.refl Unit)
    have hf : f ⟨v, Submodule.mem_span_singleton_self v⟩ =
        ⟨(e₀ : Fin 2 → k), Submodule.mem_span_singleton_self (e₀ : Fin 2 → k)⟩ := by
      change (bv.equiv b₀ (Equiv.refl Unit)) _ = _
      rw [show (⟨v, Submodule.mem_span_singleton_self v⟩ : k ∙ v) = bv () by
        simp [bv, vv], Module.Basis.equiv_apply]
      simp [b₀, v₀]
    obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
    have hev : e v = e₀ := by
      have he' := he ⟨v, Submodule.mem_span_singleton_self v⟩
      rw [hf] at he'
      exact he'.symm
    let τ : FramedGaloisRep K k (Fin 2) := ρ.conj e
    have hcharLin (x : Γ K) : LinearMap.trace k (Fin 2 → k) (ρ x) =
        1 + LinearMap.det (ρ x) := by
      rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
        ← LinearMap.det_toMatrix (Pi.basisFun k (Fin 2))]
      exact hchar x
    have hcharτLin (x : Γ K) : LinearMap.trace k (Fin 2 → k) (τ x) =
        1 + LinearMap.det (τ x) := by
      rw [show τ x = ρ.conj e x by rfl, GaloisRep.trace_conj]
      change LinearMap.trace k (Fin 2 → k) (ρ x) =
        1 + LinearMap.det (e.conj (ρ x))
      have hdet' : LinearMap.det (e.conj (ρ x)) = LinearMap.det (ρ x) := by
        simpa only [LinearEquiv.conj_apply, LinearMap.comp_assoc] using
          LinearMap.det_conj (ρ x) e
      rw [hdet']
      exact hcharLin x
    have hcharτ (x : Γ K) : (τ.GL x).1.trace = 1 + (τ.GL x).1.det := by
      have hx := hcharτLin x
      rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2)),
        ← LinearMap.det_toMatrix (Pi.basisFun k (Fin 2))] at hx
      exact hx
    have hτe₀ : τ g e₀ = e₀ := by
      rw [show τ g e₀ = e (ρ g (e.symm e₀)) by
        simp [τ, GaloisRep.conj_apply_apply], ← hev]
      simp [hρv]
    let a : k := (τ.GL g).1 0 1
    let d : k := (τ.GL g).1 1 1
    have hτg : (τ.GL g).1 = !![1, a; 0, d] := by
      ext i j
      fin_cases j
      · have hi := congrFun hτe₀ i
        rw [FramedGaloisRep.GL_apply, LinearMap.toMatrix'_apply] at ⊢
        fin_cases i <;> simpa [e₀] using hi
      · fin_cases i <;> rfl
    have hτgne : (τ.GL g).1 ≠ 1 := by
      intro hτone
      apply hgne
      have hτlin : τ g = LinearMap.id := by
        apply LinearMap.toMatrix'.injective
        rw [LinearMap.toMatrix'_id]
        exact hτone
      have hρlin : ρ g = LinearMap.id := by
        apply LinearMap.ext
        intro x
        apply e.injective
        have hx := congrArg (fun u : Module.End k (Fin 2 → k) ↦ u (e x)) hτlin
        simpa [τ, GaloisRep.conj_apply_apply] using hx
      change LinearMap.toMatrix' (ρ g) = 1
      rw [hρlin, LinearMap.toMatrix'_id]
    intro hρ
    have hτirred : τ.IsIrreducible := (GaloisRep.isIrreducible_conj_iff ρ e).mp hρ
    by_cases hd : d = 1
    · have ha : a ≠ 0 := by
        intro ha
        apply hτgne
        rw [hτg, ha, hd]
        ext i j
        fin_cases i <;> fin_cases j <;> simp
      have hτg' : (τ.GL g).1 = !![1, a; 0, 1] := by simpa [hd] using hτg
      exact (not_isIrreducible_of_unipotent_normal_form τ hcharτ g a ha hτg') hτirred
    · exact (not_isIrreducible_of_upper_normal_form_of_ne τ hcharτ g a d hd hτg)
        hτirred

end GaloisRep
