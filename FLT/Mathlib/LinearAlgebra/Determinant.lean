/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Yunzhou Xie
-/
module

public import FLT.Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Central.Defs
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import FLT.Mathlib.RingTheory.SimpleRing.TensorProduct
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.SimpleModule.IsAlgClosed
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Determinant

Material destined for Mathlib.
-/

@[expose] public section

variable (k : Type*) [Field k] {D : Type*} [Ring D] [Algebra k D]
open scoped TensorProduct

lemma mulLeft_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulLeft K (e x) = e ∘ₗ LinearMap.mulLeft K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma mulRight_conj (K : Type*) [Field K] [Algebra k K] (n : ℕ) (x : K ⊗[k] D)
    (e : K ⊗[k] D ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    LinearMap.mulRight K (e x) = e ∘ₗ LinearMap.mulRight K x ∘ₗ e.symm := by
  apply LinearMap.ext
  simp

lemma mulLeft_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    (((Matrix.ofLinearEquiv K ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K K).symm.toLinearMap
    ∘ₗ (LinearMap.mulLeft K N) ∘ₗ ((Matrix.ofLinearEquiv K) ≪≫ₗ Matrix.transposeLinearEquiv
    (Fin n) (Fin n) K K).toLinearMap)) = LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N) i).comp
    (LinearMap.proj i) := rfl

lemma mulRight_conj_ofLinear (K : Type*) [Field K] (n : ℕ) (N : Matrix (Fin n) (Fin n) K) :
    ((Matrix.ofLinearEquiv K).symm.toLinearMap ∘ₗ
    LinearMap.mulRight K N ∘ₗ (Matrix.ofLinearEquiv K).toLinearMap :
    (Fin n → Fin n → K) →ₗ[K] (Fin n) → Fin n → K) =
    LinearMap.pi fun i ↦ ((fun _ ↦ Matrix.toLin' N.transpose) i).comp (LinearMap.proj i) := by
  apply LinearMap.ext
  intro M
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]

variable [Algebra.IsCentral k D] [IsSimpleRing D] [FiniteDimensional k D]

/-- This is instance is in a repo on brauergroup which has been PRed into mathlib
at https://github.com/leanprover-community/mathlib4/pull/26377 .
  The associated FLT issue is #631.
  For now it's in `import FLT.Mathlib.RingTheory.SimpleRing.TensorProduct`.
-/
instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (B ⊗[k] A) :=
  inferInstance

instance (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]
    [Algebra.IsCentral k B] [IsSimpleRing A] [IsSimpleRing B] : IsSimpleRing (A ⊗[k] B) :=
  IsSimpleRing.of_ringEquiv
    (Algebra.TensorProduct.comm k B A).toRingEquiv inferInstance

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det (d : D) :
    (LinearMap.mulLeft k d).det = (LinearMap.mulRight k d).det := by
  let K' := AlgebraicClosure k
  obtain ⟨n, hn, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_of_isAlgClosed K' (K' ⊗[k] D)
  have h1 : (LinearMap.mulLeft k d).baseChange K' = LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  have h2 : (LinearMap.mulRight k d).baseChange K' = LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d) := by
    ext; simp
  apply FaithfulSMul.algebraMap_injective k K'
  rw [LinearMap.det_baseChange (LinearMap.mulLeft k d) |>.symm, LinearMap.det_baseChange
    (LinearMap.mulRight k d) |>.symm, h1, h2]
  have h5 : LinearMap.det (LinearMap.mulLeft K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulLeft K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulLeft _ _) e.toLinearEquiv, mulLeft_conj]
    rfl
  have h6: LinearMap.det (LinearMap.mulRight K' ((1 : K') ⊗ₜ[k] d)) =
    LinearMap.det (LinearMap.mulRight K' (e ((1 : K') ⊗ₜ d))) := by
    rw [← LinearMap.det_conj (LinearMap.mulRight _ _) e.toLinearEquiv, mulRight_conj]
    rfl
  rw [h5, h6, ← LinearMap.det_conj (LinearMap.mulRight K' (e (1 ⊗ₜ[k] d))) <|
    (Matrix.ofLinearEquiv K').symm, LinearEquiv.symm_symm, mulRight_conj_ofLinear,
    LinearMap.det_pi, ← LinearMap.det_conj (LinearMap.mulLeft K' (e (1 ⊗ₜ[k] d))) <|
    (((Matrix.ofLinearEquiv K') ≪≫ₗ Matrix.transposeLinearEquiv (Fin n) (Fin n) K' K')).symm,
    LinearEquiv.symm_symm, mulLeft_conj_ofLinear, LinearMap.det_pi]
  simp [LinearMap.det_toLin', Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma IsSimpleRing.mulLeft_det_eq_mulRight_det' (d : Dˣ) :
    (LinearEquiv.mulLeft k d).det = (LinearEquiv.mulRight k d).det := by
  ext
  simp [mulLeft_det_eq_mulRight_det]


/-!
### Auxiliary lemmas about linear equivalences and matrices
-/
section LinearEquiv

variable {F : Type*} [CommRing F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : Type*} [AddCommGroup V] [Module F V]

lemma LinearEquiv.det_ne_zero
  {F : Type*} [CommRing F] [Nontrivial F] {V : Type*} [AddCommGroup V] [Module F V]
  (e : V ≃ₗ[F] V) : e.toLinearMap.det ≠ 0 := (isUnit_det' e).ne_zero

lemma Matrix.toLinearEquiv_toLinearMap
    (b : Module.Basis ι F V) (M : Matrix ι ι F) (h : IsUnit M.det) :
    (toLinearEquiv b M h).toLinearMap = Matrix.toLin b b M := rfl

lemma LinearEquiv.det_toLinearEquiv
    (b : Module.Basis ι F V) {M : Matrix ι ι F} (h : IsUnit M.det) :
    LinearEquiv.det (M.toLinearEquiv b h) = h.unit := by
  refine Units.val_inj.mp ?_
  simp [Matrix.toLinearEquiv_toLinearMap]

end LinearEquiv

/-!
### Alternating similitudes in dimension two

The determinant of an endomorphism of a two-dimensional vector space is the factor by
which it scales a nondegenerate alternating form.  This is the linear-algebra step used
to pass from Galois equivariance of the Weil pairing to the cyclotomic determinant of
the torsion representation.
-/

section AlternatingSimilitude

universe u v

variable {F : Type u} [Field F]
variable {V : Type v} [AddCommGroup V] [Module F V]

/-- In an ordered basis of a two-dimensional vector space, an alternating form applied
to the two images of the basis vectors is scaled by the determinant. -/
theorem LinearMap.BilinForm.map_basis_fin_two_eq_det_mul
    (B : LinearMap.BilinForm F V) (hB : B.IsAlt) (b : Module.Basis (Fin 2) F V)
    (f : V →ₗ[F] V) :
    B (f (b 0)) (f (b 1)) = LinearMap.det f * B (b 0) (b 1) := by
  let M := LinearMap.toMatrix b b f
  have hf (i : Fin 2) : f (b i) = M 0 i • b 0 + M 1 i • b 1 := by
    rw [← b.sum_repr (f (b i)), Fin.sum_univ_two]
    simp only [M, LinearMap.toMatrix_apply]
  rw [hf 0, hf 1]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  rw [hB.self_eq_zero, hB.self_eq_zero, ← hB.neg_eq (b 0) (b 1)]
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  dsimp only [M]
  ring

/-- An endomorphism which scales a nonzero alternating coordinate by `c` has
determinant `c`. -/
theorem LinearMap.det_eq_of_alternating_similitude_basis
    (B : LinearMap.BilinForm F V) (hB : B.IsAlt) (b : Module.Basis (Fin 2) F V)
    (f : V →ₗ[F] V) (c : F) (hpair : B (b 0) (b 1) ≠ 0)
    (hsim : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f = c := by
  apply mul_right_cancel₀ hpair
  rw [← B.map_basis_fin_two_eq_det_mul hB b f]
  exact hsim (b 0) (b 1)

/-- A similitude of a nondegenerate alternating form on a rank-two vector space has
determinant equal to its similitude factor. -/
theorem LinearMap.det_eq_of_nondegenerate_alternating_similitude
    [Module.Finite F V] (hV : Module.rank F V = 2)
    (B : LinearMap.BilinForm F V) (hB : B.IsAlt) (f : V →ₗ[F] V) (c : F)
    (hBnd : B.Nondegenerate) (hsim : ∀ x y, B (f x) (f y) = c * B x y) :
    LinearMap.det f = c := by
  have hfin : Module.finrank F V = 2 := Module.finrank_eq_of_rank_eq hV
  let b : Module.Basis (Fin 2) F V := Module.finBasisOfFinrankEq F V hfin
  apply LinearMap.det_eq_of_alternating_similitude_basis B hB b f c
  · intro hpair
    have hzero : ∀ y, B (b 0) y = 0 := by
      intro y
      rw [← b.sum_repr y, Fin.sum_univ_two]
      simp [hB.self_eq_zero, hpair]
    exact b.ne_zero 0 (hBnd.1 (b 0) hzero)
  · exact hsim

end AlternatingSimilitude
