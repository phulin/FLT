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

@[simp]
lemma descentAlgEquiv_algebraMap_cover
    (a : QuadraticDescent.Algebra R t n) :
    descentAlgEquiv R N u t n
        (algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) a) =
      algebraMap (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n)
        (QuadraticDescent.conjugationAlgEquiv R t n a) := by
  change
    descentAlgEquiv R N u t n
        (a ⊗ₜ[R] (1 : TateKummer.CoordinateAlgebra (R := R) N u)) =
      QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R] 1
  rw [descentAlgEquiv_tmul, map_one]

/-- The trace-zero quadratic generator, embedded in the cover coordinate algebra. -/
noncomputable def coverAntiInvariant : CoverCoordinateAlgebra R N u t n :=
  QuadraticDescent.antiInvariant R t n ⊗ₜ[R]
    (1 : TateKummer.CoordinateAlgebra (R := R) N u)

/-- Its explicit inverse, embedded in the cover coordinate algebra. -/
noncomputable def coverAntiInvariantInv
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    CoverCoordinateAlgebra R N u t n :=
  QuadraticDescent.antiInvariantInv R t n hdisc ⊗ₜ[R]
    (1 : TateKummer.CoordinateAlgebra (R := R) N u)

@[simp]
lemma descentAlgEquiv_coverAntiInvariant :
    descentAlgEquiv R N u t n (coverAntiInvariant R N u t n) =
      -coverAntiInvariant R N u t n := by
  rw [coverAntiInvariant, descentAlgEquiv_tmul, map_one]
  change
    QuadraticDescent.conjugationAlgEquiv R t n
        (QuadraticDescent.antiInvariant R t n) ⊗ₜ[R] 1 = _
  rw [QuadraticDescent.conjugationAlgEquiv_antiInvariant]
  rw [TensorProduct.neg_tmul]

@[simp]
lemma descentAlgEquiv_coverAntiInvariantInv
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    descentAlgEquiv R N u t n
        (coverAntiInvariantInv R N u t n hdisc) =
      -coverAntiInvariantInv R N u t n hdisc := by
  rw [coverAntiInvariantInv, descentAlgEquiv_tmul, map_one]
  change
    QuadraticDescent.conjugationAlgEquiv R t n
        (QuadraticDescent.antiInvariantInv R t n hdisc) ⊗ₜ[R] 1 = _
  rw [QuadraticDescent.conjugationAlgEquiv_antiInvariantInv]
  rw [TensorProduct.neg_tmul]

lemma coverAntiInvariantInv_mul
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    coverAntiInvariantInv R N u t n hdisc * coverAntiInvariant R N u t n = 1 := by
  simp [coverAntiInvariantInv, coverAntiInvariant,
    Algebra.TensorProduct.tmul_mul_tmul,
    QuadraticDescent.antiInvariantInv_mul,
    Algebra.TensorProduct.one_def]

lemma coverAntiInvariant_mul_inv
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    coverAntiInvariant R N u t n * coverAntiInvariantInv R N u t n hdisc = 1 := by
  rw [mul_comm]
  exact coverAntiInvariantInv_mul R N u t n hdisc

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

/-- The anti-invariant coefficient of an element on the quadratic cover. -/
noncomputable def oddPart (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) :
    CoverCoordinateAlgebra R N u t n :=
  (↑(h2.unit⁻¹) : R) •
    (coverAntiInvariantInv R N u t n hdisc *
      (z - descentAlgEquiv R N u t n z))

lemma oddPart_mem_fixedSubalgebra (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) :
    oddPart R N u t n h2 hdisc z ∈ fixedSubalgebra R N u t n := by
  rw [mem_fixedSubalgebra]
  simp only [oddPart, map_smul, map_mul, map_sub,
    descentAlgEquiv_coverAntiInvariantInv, descentAlgEquiv_apply_apply]
  apply congrArg ((↑(h2.unit⁻¹) : R) • ·)
  ring

/-- The invariant half of an element, regarded as an element of the fixed algebra. -/
noncomputable def evenPart (h2 : IsUnit (2 : R))
    (z : CoverCoordinateAlgebra R N u t n) : fixedSubalgebra R N u t n :=
  ⟨fixedProjection R N u t n h2 z, fixedProjection_mem R N u t n h2 z⟩

/-- The anti-invariant coefficient, regarded as an element of the fixed algebra. -/
noncomputable def oddPartFixed (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) : fixedSubalgebra R N u t n :=
  ⟨oddPart R N u t n h2 hdisc z,
    oddPart_mem_fixedSubalgebra R N u t n h2 hdisc z⟩

/-- Every cover element is its invariant half plus the trace-zero generator times an invariant
coefficient. -/
lemma evenPart_add_coverAntiInvariant_mul_oddPart (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) :
    (evenPart R N u t n h2 z : CoverCoordinateAlgebra R N u t n) +
        coverAntiInvariant R N u t n *
          (oddPartFixed R N u t n h2 hdisc z :
            CoverCoordinateAlgebra R N u t n) = z := by
  have hhalf : (↑(h2.unit⁻¹) : R) * 2 = 1 := by
    calc
      (↑(h2.unit⁻¹) : R) * 2 =
          (↑(h2.unit⁻¹) : R) * (h2.unit : R) :=
        congrArg (fun x : R ↦ (↑(h2.unit⁻¹) : R) * x) h2.unit_spec.symm
      _ = 1 := h2.unit.inv_mul
  change
    fixedProjection R N u t n h2 z +
        coverAntiInvariant R N u t n * oddPart R N u t n h2 hdisc z = z
  rw [fixedProjection_apply, oddPart, mul_smul_comm,
    ← mul_assoc, coverAntiInvariant_mul_inv, one_mul]
  calc
    (↑(h2.unit⁻¹) : R) • (descentAlgEquiv R N u t n z + z) +
          (↑(h2.unit⁻¹) : R) • (z - descentAlgEquiv R N u t n z) =
        (↑(h2.unit⁻¹) : R) •
          ((descentAlgEquiv R N u t n z + z) +
            (z - descentAlgEquiv R N u t n z)) :=
      (smul_add (↑(h2.unit⁻¹) : R)
        (descentAlgEquiv R N u t n z + z)
        (z - descentAlgEquiv R N u t n z)).symm
    _ = (↑(h2.unit⁻¹) : R) • ((2 : R) • z) := by
      congr 1
      rw [two_smul]
      abel
    _ = z := by rw [smul_smul, hhalf, one_smul]

/-- The canonical map from the scalar extension of the fixed algebra back to the cover algebra. -/
noncomputable def baseChangeToCover :
    QuadraticDescent.Algebra R t n ⊗[R] fixedSubalgebra R N u t n →ₐ[
      QuadraticDescent.Algebra R t n] CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.liftEquivRight R (QuadraticDescent.Algebra R t n)
    (fixedSubalgebra R N u t n) (CoverCoordinateAlgebra R N u t n)
    (Subalgebra.val (fixedSubalgebra R N u t n))

@[simp]
lemma baseChangeToCover_tmul (a : QuadraticDescent.Algebra R t n)
    (z : fixedSubalgebra R N u t n) :
    baseChangeToCover R N u t n (a ⊗ₜ[R] z) =
      algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) a *
        (z : CoverCoordinateAlgebra R N u t n) := by
  rfl

/-- The canonical base-change map is surjective: invariant and anti-invariant averaging gives an
explicit preimage of every cover element. -/
lemma baseChangeToCover_surjective (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Function.Surjective (baseChangeToCover R N u t n) := by
  intro z
  refine ⟨
    (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] evenPart R N u t n h2 z +
      QuadraticDescent.antiInvariant R t n ⊗ₜ[R]
        oddPartFixed R N u t n h2 hdisc z, ?_⟩
  rw [map_add, baseChangeToCover_tmul, baseChangeToCover_tmul, map_one, one_mul]
  change
    (evenPart R N u t n h2 z : CoverCoordinateAlgebra R N u t n) +
      coverAntiInvariant R N u t n *
        (oddPartFixed R N u t n h2 hdisc z :
          CoverCoordinateAlgebra R N u t n) = z
  exact evenPart_add_coverAntiInvariant_mul_oddPart R N u t n h2 hdisc z

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

lemma coe_fixedRetraction_baseChangeToCover_tmul (h2 : IsUnit (2 : R))
    (a : QuadraticDescent.Algebra R t n) (z : fixedSubalgebra R N u t n) :
    (fixedRetraction R N u t n h2
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) :
      CoverCoordinateAlgebra R N u t n) =
      algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n)
          (QuadraticDescent.evenPart R t n h2 a) *
        (z : CoverCoordinateAlgebra R N u t n) := by
  change
    fixedProjection R N u t n h2
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = _
  rw [fixedProjection_apply, baseChangeToCover_tmul, map_mul,
    descentAlgEquiv_algebraMap_cover,
    (mem_fixedSubalgebra R N u t n z).mp z.property]
  rw [QuadraticDescent.evenPart]
  simp only [Algebra.smul_def, map_mul, map_add]
  rw [IsScalarTower.algebraMap_apply R (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n)]
  ring

/-- The anti-invariant coefficient as an `R`-linear map. -/
noncomputable def oddProjectionLinear (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    CoverCoordinateAlgebra R N u t n →ₗ[R] CoverCoordinateAlgebra R N u t n :=
  (↑(h2.unit⁻¹) : R) •
    (LinearMap.mulLeft R (coverAntiInvariantInv R N u t n hdisc)).comp
      (LinearMap.id - (descentAlgEquiv R N u t n).toLinearMap)

lemma oddProjectionLinear_apply (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) :
    oddProjectionLinear R N u t n h2 hdisc z = oddPart R N u t n h2 hdisc z := by
  rfl

/-- The anti-invariant coefficient with codomain restricted to the fixed algebra. -/
noncomputable def oddRetraction (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    CoverCoordinateAlgebra R N u t n →ₗ[R] fixedSubalgebra R N u t n :=
  (oddProjectionLinear R N u t n h2 hdisc).codRestrict
    (fixedSubalgebra R N u t n).toSubmodule
    (oddPart_mem_fixedSubalgebra R N u t n h2 hdisc)

lemma coe_oddRetraction_baseChangeToCover_tmul (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : QuadraticDescent.Algebra R t n) (z : fixedSubalgebra R N u t n) :
    (oddRetraction R N u t n h2 hdisc
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) :
      CoverCoordinateAlgebra R N u t n) =
      algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n)
          (QuadraticDescent.oddPart R t n h2 hdisc a) *
        (z : CoverCoordinateAlgebra R N u t n) := by
  change
    oddPart R N u t n h2 hdisc
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = _
  rw [oddPart, baseChangeToCover_tmul, map_mul,
    descentAlgEquiv_algebraMap_cover,
    (mem_fixedSubalgebra R N u t n z).mp z.property]
  change
    (↑(h2.unit⁻¹) : R) •
        (algebraMap (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n)
            (QuadraticDescent.antiInvariantInv R t n hdisc) *
          (algebraMap (QuadraticDescent.Algebra R t n)
                (CoverCoordinateAlgebra R N u t n) a * (z : CoverCoordinateAlgebra R N u t n) -
            algebraMap (QuadraticDescent.Algebra R t n)
                (CoverCoordinateAlgebra R N u t n)
                (QuadraticDescent.conjugationAlgEquiv R t n a) * z)) = _
  rw [QuadraticDescent.oddPart]
  simp only [Algebra.smul_def, map_mul, map_sub]
  rw [IsScalarTower.algebraMap_apply R (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n)]
  ring

/-- The explicit `R`-linear inverse candidate to the canonical base-change map. -/
noncomputable def descentLinearInverse (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    CoverCoordinateAlgebra R N u t n →ₗ[R]
      QuadraticDescent.Algebra R t n ⊗[R] fixedSubalgebra R N u t n :=
  (TensorProduct.mk R (QuadraticDescent.Algebra R t n)
      (fixedSubalgebra R N u t n) 1).comp
      (fixedRetraction R N u t n h2) +
    (TensorProduct.mk R (QuadraticDescent.Algebra R t n)
      (fixedSubalgebra R N u t n) (QuadraticDescent.antiInvariant R t n)).comp
      (oddRetraction R N u t n h2 hdisc)

lemma descentLinearInverse_apply (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : CoverCoordinateAlgebra R N u t n) :
    descentLinearInverse R N u t n h2 hdisc z =
      (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          fixedRetraction R N u t n h2 z +
        QuadraticDescent.antiInvariant R t n ⊗ₜ[R]
          oddRetraction R N u t n h2 hdisc z := by
  rfl

/-- Applying the canonical base-change map after the explicit inverse recovers every cover
element. -/
lemma baseChangeToCover_comp_descentLinearInverse (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    ((baseChangeToCover R N u t n).toLinearMap.restrictScalars R).comp
        (descentLinearInverse R N u t n h2 hdisc) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, descentLinearInverse_apply, map_add]
  change
    baseChangeToCover R N u t n
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
            fixedRetraction R N u t n h2 z) +
        baseChangeToCover R N u t n
          (QuadraticDescent.antiInvariant R t n ⊗ₜ[R]
            oddRetraction R N u t n h2 hdisc z) = z
  rw [baseChangeToCover_tmul, baseChangeToCover_tmul, map_one, one_mul]
  change
    (evenPart R N u t n h2 z : CoverCoordinateAlgebra R N u t n) +
      coverAntiInvariant R N u t n *
        (oddPartFixed R N u t n h2 hdisc z :
          CoverCoordinateAlgebra R N u t n) = z
  exact evenPart_add_coverAntiInvariant_mul_oddPart R N u t n h2 hdisc z

lemma descentLinearInverse_baseChangeToCover_tmul (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : QuadraticDescent.Algebra R t n) (z : fixedSubalgebra R N u t n) :
    descentLinearInverse R N u t n h2 hdisc
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = a ⊗ₜ[R] z := by
  let ae := QuadraticDescent.evenPart R t n h2 a
  let ao := QuadraticDescent.oddPart R t n h2 hdisc a
  let re := QuadraticDescent.reCoeff R t n ae
  let ro := QuadraticDescent.reCoeff R t n ao
  have hae : ae = algebraMap R (QuadraticDescent.Algebra R t n) re := by
    exact QuadraticDescent.evenPart_eq_algebraMap R t n h2 a
  have hao : ao = algebraMap R (QuadraticDescent.Algebra R t n) ro := by
    exact QuadraticDescent.oddPart_eq_algebraMap R t n h2 hdisc a
  have heven :
      fixedRetraction R N u t n h2
          (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = re • z := by
    apply Subtype.ext
    rw [coe_fixedRetraction_baseChangeToCover_tmul]
    change
      algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) ae *
          (z : CoverCoordinateAlgebra R N u t n) =
        re • (z : CoverCoordinateAlgebra R N u t n)
    rw [hae, ← IsScalarTower.algebraMap_apply R
      (QuadraticDescent.Algebra R t n) (CoverCoordinateAlgebra R N u t n)]
    rw [Algebra.smul_def]
  have hodd :
      oddRetraction R N u t n h2 hdisc
          (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = ro • z := by
    apply Subtype.ext
    rw [coe_oddRetraction_baseChangeToCover_tmul]
    change
      algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) ao *
          (z : CoverCoordinateAlgebra R N u t n) =
        ro • (z : CoverCoordinateAlgebra R N u t n)
    rw [hao, ← IsScalarTower.algebraMap_apply R
      (QuadraticDescent.Algebra R t n) (CoverCoordinateAlgebra R N u t n)]
    rw [Algebra.smul_def]
  rw [descentLinearInverse_apply, heven, hodd]
  calc
    (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] (re • z) +
          QuadraticDescent.antiInvariant R t n ⊗ₜ[R] (ro • z) =
        (re • (1 : QuadraticDescent.Algebra R t n)) ⊗ₜ[R] z +
          (ro • QuadraticDescent.antiInvariant R t n) ⊗ₜ[R] z := by
      rw [TensorProduct.tmul_smul, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', TensorProduct.smul_tmul']
    _ = ae ⊗ₜ[R] z +
          (QuadraticDescent.antiInvariant R t n * ao) ⊗ₜ[R] z := by
      rw [Algebra.smul_def, mul_one, ← hae, Algebra.smul_def, mul_comm, ← hao]
    _ = (ae + QuadraticDescent.antiInvariant R t n * ao) ⊗ₜ[R] z := by
      rw [TensorProduct.add_tmul]
    _ = a ⊗ₜ[R] z := by
      rw [QuadraticDescent.evenPart_add_antiInvariant_mul_oddPart R t n h2 hdisc a]

lemma descentLinearInverse_comp_baseChangeToCover (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (descentLinearInverse R N u t n h2 hdisc).comp
        ((baseChangeToCover R N u t n).toLinearMap.restrictScalars R) = LinearMap.id := by
  apply TensorProduct.ext'
  intro a z
  rw [LinearMap.comp_apply]
  change
    descentLinearInverse R N u t n h2 hdisc
        (baseChangeToCover R N u t n (a ⊗ₜ[R] z)) = a ⊗ₜ[R] z
  exact descentLinearInverse_baseChangeToCover_tmul R N u t n h2 hdisc a z

lemma baseChangeToCover_injective (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Function.Injective (baseChangeToCover R N u t n) := by
  apply Function.LeftInverse.injective
    (g := descentLinearInverse R N u t n h2 hdisc)
  intro z
  have hz := LinearMap.congr_fun
    (descentLinearInverse_comp_baseChangeToCover R N u t n h2 hdisc) z
  change
    descentLinearInverse R N u t n h2 hdisc
        (baseChangeToCover R N u t n z) = z at hz
  exact hz

lemma baseChangeToCover_bijective (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Function.Bijective (baseChangeToCover R N u t n) :=
  ⟨baseChangeToCover_injective R N u t n h2 hdisc,
    baseChangeToCover_surjective R N u t n h2 hdisc⟩

/-- Extending the fixed algebra back to the quadratic cover recovers the original Tate--Kummer
coordinate algebra. -/
noncomputable def baseChangeEquiv (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    QuadraticDescent.Algebra R t n ⊗[R] fixedSubalgebra R N u t n ≃ₐ[
      QuadraticDescent.Algebra R t n] CoverCoordinateAlgebra R N u t n :=
  AlgEquiv.ofBijective (baseChangeToCover R N u t n)
    (baseChangeToCover_bijective R N u t n h2 hdisc)

@[simp]
lemma baseChangeEquiv_apply (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : QuadraticDescent.Algebra R t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeEquiv R N u t n h2 hdisc z = baseChangeToCover R N u t n z :=
  rfl

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
