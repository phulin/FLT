/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.QuadraticDescent
public import FLT.GroupScheme.TateKummer
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Quadratic twists of Tate--Kummer coordinate algebras

This file starts the explicit descent of a Tate--Kummer finite-flat group scheme along
`R[X] / (X² - tX + n)`.  Quadratic conjugation on the cover is paired with inversion on
the group scheme.  Their tensor product is the descent involution, and its fixed subalgebra
is the coordinate algebra of the quadratic twist.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace HopfAlgebra

open Coalgebra WithConv
open scoped RingTheory.LinearMap

/-- On a commutative, cocommutative Hopf algebra, the antipode commutes with
comultiplication.  This is the usual uniqueness-of-convolution-inverses proof. -/
lemma comul_comp_antipode_of_isCocomm
    {R A : Type*} [CommSemiring R] [CommSemiring A]
    [HopfAlgebra R A] [Coalgebra.IsCocomm R A] :
    (Coalgebra.comul (R := R) (A := A)).comp (HopfAlgebra.antipode R) =
      (TensorProduct.map (HopfAlgebra.antipode R) (HopfAlgebra.antipode R)).comp
        (Coalgebra.comul (R := R) (A := A)) := by
  let S : A →ₗ[R] A := HopfAlgebra.antipode R
  let comulMap : A →ₗ[R] A ⊗[R] A := Coalgebra.comul
  let comulHom : A →ₗc[R] A ⊗[R] A := Coalgebra.comulCoalgHom R A
  let sTensor : A ⊗[R] A →ₗ[R] A ⊗[R] A := TensorProduct.map S S
  let idTensor : A ⊗[R] A →ₗ[R] A ⊗[R] A :=
    TensorProduct.map LinearMap.id LinearMap.id
  have hcomul : comulHom.toLinearMap = comulMap := rfl
  have htensor :
      toConv sTensor * toConv idTensor =
        (1 : WithConv ((A ⊗[R] A) →ₗ[R] (A ⊗[R] A))) := by
    rw [TensorProduct.map_convMul_map]
    simp only [LinearMap.antipode_mul_id]
    ext x y
    simp [Algebra.algebraMap_eq_smul_one]
    change
      ((Coalgebra.counit (R := R) y) •
          ((Coalgebra.counit (R := R) x) • (1 : A))) ⊗ₜ[R] (1 : A) =
        (Coalgebra.counit (R := R) y * Coalgebra.counit (R := R) x) •
          ((1 : A) ⊗ₜ[R] (1 : A))
    calc
      ((Coalgebra.counit (R := R) y) •
            ((Coalgebra.counit (R := R) x) • (1 : A))) ⊗ₜ[R] (1 : A) =
          ((Coalgebra.counit (R := R) y * Coalgebra.counit (R := R) x) •
            (1 : A)) ⊗ₜ[R] (1 : A) := by rw [smul_smul]
      _ = (Coalgebra.counit (R := R) y * Coalgebra.counit (R := R) x) •
          ((1 : A) ⊗ₜ[R] (1 : A)) :=
        (TensorProduct.smul_tmul' _ _ _).symm
  have hid : idTensor.comp comulHom.toLinearMap = comulMap := by
    rw [hcomul]
    simp [idTensor]
  have hleft :
      toConv (sTensor.comp comulHom.toLinearMap) *
          toConv (idTensor.comp comulHom.toLinearMap) =
        (1 : WithConv (A →ₗ[R] (A ⊗[R] A))) := by
    apply WithConv.ofConv_injective
    rw [← LinearMap.convMul_comp_coalgHom_distrib]
    rw [htensor]
    ext x
    simp [comulHom]
  rw [hid] at hleft
  have hright :
      toConv comulMap * toConv (comulMap.comp S) =
        (1 : WithConv (A →ₗ[R] (A ⊗[R] A))) := by
    simpa only [S, comulMap] using
      (LinearMap.comul_right_inv (R := R) (C := A))
  have hinv := left_inv_eq_right_inv (a := toConv comulMap) hleft hright
  rw [hcomul] at hinv
  apply LinearMap.ext
  intro x
  have hx := congrArg (fun f : WithConv (A →ₗ[R] A ⊗[R] A) ↦ f.ofConv x) hinv
  simpa only [S, comulMap, sTensor, idTensor,
    CoalgHom.toLinearMap_eq_coe,
    LinearMap.comp_apply, TensorProduct.map_id] using hx.symm

end HopfAlgebra

namespace TateKummer.QuadraticTwist

variable (R : Type u) [CommRing R]
variable (N : ℕ) [NeZero N] (u : Rˣ) (t n : R)

/-- The Tate--Kummer coordinate algebra after extension to the quadratic cover. -/
abbrev CoverCoordinateAlgebra :=
  QuadraticDescent.Algebra R t n ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u

/-- Quadratic conjugation on the cover paired with inversion on the Tate--Kummer group. -/
noncomputable def descentAlgEquiv :
    CoverCoordinateAlgebra R N u t n ≃ₐ[R] CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.congr
    (QuadraticDescent.conjugationAlgEquiv R t n)
    (TateKummer.antipodeAlgEquiv N u)

@[simp]
lemma descentAlgEquiv_tmul
    (a : QuadraticDescent.Algebra R t n)
    (h : TateKummer.CoordinateAlgebra (R := R) N u) :
    descentAlgEquiv R N u t n (a ⊗ₜ[R] h) =
      QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R]
        TateKummer.antipodeAlgEquiv N u h := by
  rfl

/-- The descent automorphism has order two. -/
@[simp]
lemma descentAlgEquiv_symm :
    (descentAlgEquiv R N u t n).symm = descentAlgEquiv R N u t n := by
  unfold descentAlgEquiv
  rw [← Algebra.TensorProduct.congr_symm]
  simp only [QuadraticDescent.conjugationAlgEquiv_symm,
    TateKummer.antipodeAlgEquiv_symm]

lemma descentAlgEquiv_involutive :
    Function.Involutive (descentAlgEquiv R N u t n) := by
  intro z
  have h := (descentAlgEquiv R N u t n).symm_apply_apply z
  rwa [descentAlgEquiv_symm] at h

@[simp]
lemma descentAlgEquiv_apply_apply (z : CoverCoordinateAlgebra R N u t n) :
    descentAlgEquiv R N u t n (descentAlgEquiv R N u t n z) = z :=
  descentAlgEquiv_involutive R N u t n z

/-- The fixed algebra for the conjugation--inversion descent datum. -/
noncomputable def fixedSubalgebra :
    Subalgebra R (CoverCoordinateAlgebra R N u t n) :=
  AlgHom.equalizer (descentAlgEquiv R N u t n).toAlgHom
    (AlgHom.id R (CoverCoordinateAlgebra R N u t n))

@[simp]
lemma mem_fixedSubalgebra (z : CoverCoordinateAlgebra R N u t n) :
    z ∈ fixedSubalgebra R N u t n ↔ descentAlgEquiv R N u t n z = z :=
  Iff.rfl

/-- Averaging over the order-two descent action. -/
noncomputable def fixedProjection (h2 : IsUnit (2 : R)) :
    CoverCoordinateAlgebra R N u t n →ₗ[R] CoverCoordinateAlgebra R N u t n :=
  (↑(h2.unit⁻¹) : R) •
    ((descentAlgEquiv R N u t n).toLinearMap + LinearMap.id)

lemma fixedProjection_apply (h2 : IsUnit (2 : R))
    (z : CoverCoordinateAlgebra R N u t n) :
    fixedProjection R N u t n h2 z =
      (↑(h2.unit⁻¹) : R) • (descentAlgEquiv R N u t n z + z) :=
  rfl

lemma fixedProjection_mem (h2 : IsUnit (2 : R))
    (z : CoverCoordinateAlgebra R N u t n) :
    fixedProjection R N u t n h2 z ∈ fixedSubalgebra R N u t n := by
  rw [mem_fixedSubalgebra, fixedProjection_apply]
  simp only [map_smul, map_add, descentAlgEquiv_apply_apply]
  rw [add_comm]

lemma fixedProjection_of_mem (h2 : IsUnit (2 : R))
    (z : CoverCoordinateAlgebra R N u t n)
    (hz : z ∈ fixedSubalgebra R N u t n) :
    fixedProjection R N u t n h2 z = z := by
  have hhalf : (↑(h2.unit⁻¹) : R) * 2 = 1 := by
    calc
      (↑(h2.unit⁻¹) : R) * 2 =
          (↑(h2.unit⁻¹) : R) * (h2.unit : R) :=
        congrArg (fun x : R ↦ (↑(h2.unit⁻¹) : R) * x) h2.unit_spec.symm
      _ = 1 := h2.unit.inv_mul
  rw [fixedProjection_apply, (mem_fixedSubalgebra R N u t n z).mp hz]
  calc
    (↑(h2.unit⁻¹) : R) • (z + z) =
        (↑(h2.unit⁻¹) : R) • ((2 : R) • z) := by rw [two_smul]
    _ = ((↑(h2.unit⁻¹) : R) * 2) • z := by rw [smul_smul]
    _ = z := by rw [hhalf, one_smul]

/-- The averaging projector, with codomain restricted to the fixed algebra. -/
noncomputable def fixedRetraction (h2 : IsUnit (2 : R)) :
    CoverCoordinateAlgebra R N u t n →ₗ[R] fixedSubalgebra R N u t n :=
  (fixedProjection R N u t n h2).codRestrict
    (fixedSubalgebra R N u t n).toSubmodule
    (fixedProjection_mem R N u t n h2)

lemma fixedRetraction_comp_subtype (h2 : IsUnit (2 : R)) :
    (fixedRetraction R N u t n h2).comp
        (fixedSubalgebra R N u t n).toSubmodule.subtype =
      LinearMap.id := by
  ext z
  change fixedProjection R N u t n h2 z = z
  exact fixedProjection_of_mem R N u t n h2 z z.property

/-- The fixed algebra is projective because it is a direct summand of the finite-free
cover algebra. -/
theorem fixedModuleProjective (h2 : IsUnit (2 : R)) :
    Module.Projective R (fixedSubalgebra R N u t n) := by
  let _ : Module.Projective R (CoverCoordinateAlgebra R N u t n) := inferInstance
  exact Module.Projective.of_split
    (fixedSubalgebra R N u t n).toSubmodule.subtype
    (fixedRetraction R N u t n h2)
    (fixedRetraction_comp_subtype R N u t n h2)

/-- The fixed algebra is finite as a quotient of the finite cover algebra under the
averaging retraction. -/
theorem fixedModuleFinite (h2 : IsUnit (2 : R)) :
    Module.Finite R (fixedSubalgebra R N u t n) := by
  apply Module.Finite.of_surjective (fixedRetraction R N u t n h2)
  intro z
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact fixedProjection_of_mem R N u t n h2 z z.property

/-- Consequently the fixed algebra is flat. -/
theorem fixedModuleFlat (h2 : IsUnit (2 : R)) :
    Module.Flat R (fixedSubalgebra R N u t n) := by
  let _ : Module.Projective R (fixedSubalgebra R N u t n) :=
    fixedModuleProjective R N u t n h2
  infer_instance

/-- The coordinate ring of the quadratic twist, realized as fixed points on the cover. -/
noncomputable abbrev CoordinateAlgebra := fixedSubalgebra R N u t n

end TateKummer.QuadraticTwist
