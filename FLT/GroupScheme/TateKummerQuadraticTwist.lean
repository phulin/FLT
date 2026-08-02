/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.QuadraticDescent
public import FLT.GroupScheme.TateKummer
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
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

/-! ## Descent of inversion -/

/-- Inversion on the Tate--Kummer factor, viewed as an algebra endomorphism over the
quadratic cover. -/
noncomputable def coverAntipodeAlgHom :
    CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.map
    (AlgHom.id (QuadraticDescent.Algebra R t n) (QuadraticDescent.Algebra R t n))
    (TateKummer.antipodeAlgHom N u)

@[simp]
lemma coverAntipodeAlgHom_tmul
    (a : QuadraticDescent.Algebra R t n)
    (h : TateKummer.CoordinateAlgebra (R := R) N u) :
    coverAntipodeAlgHom R N u t n (a ⊗ₜ[R] h) =
      a ⊗ₜ[R] TateKummer.antipodeAlgHom N u h := by
  rfl

/-- Inversion on the cover is an involution. -/
lemma coverAntipodeAlgHom_involutive :
    Function.Involutive (coverAntipodeAlgHom R N u t n) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
      simp only [coverAntipodeAlgHom_tmul]
      rw [TateKummer.antipodeAlgHom_involutive N u h]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Quadratic descent commutes with inversion on the cover.  Both composites apply
quadratic conjugation to the first factor and apply inversion twice to the second. -/
lemma descentAlgEquiv_coverAntipodeAlgHom
    (z : CoverCoordinateAlgebra R N u t n) :
    descentAlgEquiv R N u t n (coverAntipodeAlgHom R N u t n z) =
      coverAntipodeAlgHom R N u t n (descentAlgEquiv R N u t n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
      simp only [coverAntipodeAlgHom_tmul, descentAlgEquiv_tmul]
      simp only [TateKummer.antipodeAlgEquiv_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

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

/-- The antipode preserves the descent condition, hence restricts to inversion on the
quadratic-twist coordinate algebra. -/
noncomputable def antipodeAlgHom :
    fixedSubalgebra R N u t n →ₐ[R] fixedSubalgebra R N u t n :=
  AlgHom.codRestrict
    (((coverAntipodeAlgHom R N u t n).restrictScalars R).comp
      (Subalgebra.val (fixedSubalgebra R N u t n)))
    (fixedSubalgebra R N u t n) fun z => by
      rw [mem_fixedSubalgebra]
      change
        descentAlgEquiv R N u t n (coverAntipodeAlgHom R N u t n z) =
          coverAntipodeAlgHom R N u t n z
      rw [descentAlgEquiv_coverAntipodeAlgHom]
      exact congrArg (coverAntipodeAlgHom R N u t n)
        ((mem_fixedSubalgebra R N u t n z).mp z.property)

@[simp]
lemma coe_antipodeAlgHom (z : fixedSubalgebra R N u t n) :
    (antipodeAlgHom R N u t n z : CoverCoordinateAlgebra R N u t n) =
      coverAntipodeAlgHom R N u t n z :=
  rfl

/-- The descended inversion remains involutive. -/
lemma antipodeAlgHom_involutive :
    Function.Involutive (antipodeAlgHom R N u t n) := by
  intro z
  apply Subtype.ext
  change
    coverAntipodeAlgHom R N u t n (coverAntipodeAlgHom R N u t n z) = z
  exact coverAntipodeAlgHom_involutive R N u t n z

/-! ## Descent of the counit -/

/-- The counit of the tensor-product Hopf algebra over the quadratic cover. -/
noncomputable def coverCounitAlgHom :
    CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      QuadraticDescent.Algebra R t n :=
  Bialgebra.counitAlgHom (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n)

@[simp]
lemma coverCounitAlgHom_tmul
    (a : QuadraticDescent.Algebra R t n)
    (h : TateKummer.CoordinateAlgebra (R := R) N u) :
    coverCounitAlgHom R N u t n (a ⊗ₜ[R] h) =
      a * algebraMap R (QuadraticDescent.Algebra R t n)
        (Bialgebra.counitAlgHom R
          (TateKummer.CoordinateAlgebra (R := R) N u) h) := by
  simp [coverCounitAlgHom, Bialgebra.TensorProduct.counitAlgHom_def,
    Algebra.smul_def]
  rw [mul_comm]

/-- The cover counit is equivariant for the semilinear descent datum. -/
lemma conjugationAlgEquiv_coverCounitAlgHom
    (z : CoverCoordinateAlgebra R N u t n) :
    QuadraticDescent.conjugationAlgEquiv R t n
        (coverCounitAlgHom R N u t n z) =
      coverCounitAlgHom R N u t n (descentAlgEquiv R N u t n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
      have hcounit :
          Bialgebra.counitAlgHom R (TateKummer.CoordinateAlgebra (R := R) N u)
              (TateKummer.antipodeAlgHom N u h) =
            Bialgebra.counitAlgHom R
              (TateKummer.CoordinateAlgebra (R := R) N u) h :=
        HopfAlgebra.counit_antipode h
      rw [coverCounitAlgHom_tmul, map_mul,
        (QuadraticDescent.conjugationAlgEquiv R t n).commutes,
        descentAlgEquiv_tmul, coverCounitAlgHom_tmul,
        TateKummer.antipodeAlgEquiv_apply, hcounit]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The cover counit of a descended element is fixed by quadratic conjugation. -/
lemma conjugationAlgEquiv_coverCounitAlgHom_fixed
    (z : fixedSubalgebra R N u t n) :
    QuadraticDescent.conjugationAlgEquiv R t n
        (coverCounitAlgHom R N u t n z) =
      coverCounitAlgHom R N u t n z := by
  rw [conjugationAlgEquiv_coverCounitAlgHom]
  exact congrArg (coverCounitAlgHom R N u t n)
    ((mem_fixedSubalgebra R N u t n z).mp z.property)

/-- A descended counit value is the scalar given by its explicit quadratic coefficient. -/
lemma coverCounitAlgHom_eq_algebraMap_reCoeff (h2 : IsUnit (2 : R))
    (z : fixedSubalgebra R N u t n) :
    coverCounitAlgHom R N u t n z =
      algebraMap R (QuadraticDescent.Algebra R t n)
        (QuadraticDescent.reCoeff R t n (coverCounitAlgHom R N u t n z)) :=
  QuadraticDescent.eq_algebraMap_of_conjugationAlgEquiv_eq R t n h2 _
    (conjugationAlgEquiv_coverCounitAlgHom_fixed R N u t n z)

/-- The counit on the quadratic-twist coordinate algebra, obtained by descending the
cover counit to the base ring. -/
noncomputable def counitAlgHom (h2 : IsUnit (2 : R)) :
    fixedSubalgebra R N u t n →ₐ[R] R where
  toFun z := QuadraticDescent.reCoeff R t n (coverCounitAlgHom R N u t n z)
  map_zero' := by simp
  map_one' := by
    change
      QuadraticDescent.reCoeff R t n
        (coverCounitAlgHom R N u t n
          (1 : CoverCoordinateAlgebra R N u t n)) = 1
    rw [map_one]
    simpa only [map_one] using QuadraticDescent.reCoeff_algebraMap R t n (1 : R)
  map_add' x y := by simp
  map_mul' x y := by
    change
      QuadraticDescent.reCoeff R t n
          (coverCounitAlgHom R N u t n
            ((x : CoverCoordinateAlgebra R N u t n) * y)) =
        QuadraticDescent.reCoeff R t n (coverCounitAlgHom R N u t n x) *
          QuadraticDescent.reCoeff R t n (coverCounitAlgHom R N u t n y)
    rw [map_mul, coverCounitAlgHom_eq_algebraMap_reCoeff R N u t n h2 x,
      coverCounitAlgHom_eq_algebraMap_reCoeff R N u t n h2 y,
      ← map_mul]
    simp only [QuadraticDescent.reCoeff_algebraMap]
  commutes' r := by
    change
      QuadraticDescent.reCoeff R t n
          (coverCounitAlgHom R N u t n
            (algebraMap R (fixedSubalgebra R N u t n) r)) = r
    rw [show coverCounitAlgHom R N u t n
          (algebraMap R (fixedSubalgebra R N u t n) r) =
        algebraMap R (QuadraticDescent.Algebra R t n) r by
      change coverCounitAlgHom R N u t n
          (algebraMap R (CoverCoordinateAlgebra R N u t n) r) = _
      change coverCounitAlgHom R N u t n
          (algebraMap R (QuadraticDescent.Algebra R t n) r ⊗ₜ[R]
            (1 : TateKummer.CoordinateAlgebra (R := R) N u)) = _
      rw [coverCounitAlgHom_tmul, map_one, map_one, mul_one]]
    exact QuadraticDescent.reCoeff_algebraMap R t n r

@[simp]
lemma counitAlgHom_apply (h2 : IsUnit (2 : R))
    (z : fixedSubalgebra R N u t n) :
    counitAlgHom R N u t n h2 z =
      QuadraticDescent.reCoeff R t n (coverCounitAlgHom R N u t n z) :=
  rfl

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

/-! ## Tensor-square base change -/

/-- Scalar extension of the descended coordinate algebra. -/
noncomputable abbrev BaseChangedFixedAlgebra :=
  QuadraticDescent.Algebra R t n ⊗[R] fixedSubalgebra R N u t n

/-- The tensor square of the scalar-extended descended coordinate algebra. -/
noncomputable abbrev BaseChangedFixedTensorSquare :=
  BaseChangedFixedAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
    BaseChangedFixedAlgebra R N u t n

/-- Embed the left descended tensor factor into the tensor square after scalar extension. -/
noncomputable def baseChangeTensorLeftEmbedding :
    fixedSubalgebra R N u t n →ₐ[R] BaseChangedFixedTensorSquare R N u t n :=
  ((Algebra.TensorProduct.includeLeft :
      BaseChangedFixedAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
        BaseChangedFixedTensorSquare R N u t n).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight :
      fixedSubalgebra R N u t n →ₐ[R] BaseChangedFixedAlgebra R N u t n)

/-- Embed the right descended tensor factor into the tensor square after scalar extension. -/
noncomputable def baseChangeTensorRightEmbedding :
    fixedSubalgebra R N u t n →ₐ[R] BaseChangedFixedTensorSquare R N u t n :=
  ((Algebra.TensorProduct.includeRight :
      BaseChangedFixedAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
        BaseChangedFixedTensorSquare R N u t n).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight :
      fixedSubalgebra R N u t n →ₐ[R] BaseChangedFixedAlgebra R N u t n)

/-- Embed the descended tensor square into the tensor square after scalar extension. -/
noncomputable def baseChangeTensorEmbedding :
    fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n →ₐ[R]
      BaseChangedFixedTensorSquare R N u t n :=
  Algebra.TensorProduct.lift
    (baseChangeTensorLeftEmbedding R N u t n)
    (baseChangeTensorRightEmbedding R N u t n)
    fun _ _ => Commute.all _ _

@[simp]
lemma baseChangeTensorLeftEmbedding_apply (x : fixedSubalgebra R N u t n) :
    baseChangeTensorLeftEmbedding R N u t n x =
      ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] x) ⊗ₜ[
        QuadraticDescent.Algebra R t n]
        (1 : BaseChangedFixedAlgebra R N u t n) := by
  rfl

@[simp]
lemma baseChangeTensorRightEmbedding_apply (y : fixedSubalgebra R N u t n) :
    baseChangeTensorRightEmbedding R N u t n y =
      (1 : BaseChangedFixedAlgebra R N u t n) ⊗ₜ[
        QuadraticDescent.Algebra R t n]
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] y) := by
  rfl

@[simp]
lemma baseChangeTensorEmbedding_tmul
    (x y : fixedSubalgebra R N u t n) :
    baseChangeTensorEmbedding R N u t n (x ⊗ₜ[R] y) =
      ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] x) ⊗ₜ[
        QuadraticDescent.Algebra R t n]
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] y) := by
  simp [baseChangeTensorEmbedding, baseChangeTensorLeftEmbedding,
    baseChangeTensorRightEmbedding, Algebra.TensorProduct.one_def,
    Algebra.TensorProduct.tmul_mul_tmul]

/-- The multiplicative base-change distribution map for the descended tensor square. -/
noncomputable def baseChangeTensorMap :
    QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) →ₐ[
      QuadraticDescent.Algebra R t n] BaseChangedFixedTensorSquare R N u t n :=
  Algebra.TensorProduct.liftEquivRight R (QuadraticDescent.Algebra R t n)
    (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)
    (BaseChangedFixedTensorSquare R N u t n)
    (baseChangeTensorEmbedding R N u t n)

@[simp]
lemma baseChangeTensorMap_tmul (a : QuadraticDescent.Algebra R t n)
    (x y : fixedSubalgebra R N u t n) :
    baseChangeTensorMap R N u t n (a ⊗ₜ[R] (x ⊗ₜ[R] y)) =
      (a ⊗ₜ[R] x) ⊗ₜ[QuadraticDescent.Algebra R t n]
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] y) := by
  simp [baseChangeTensorMap, baseChangeTensorEmbedding,
    baseChangeTensorLeftEmbedding, baseChangeTensorRightEmbedding,
    Algebra.TensorProduct.one_def, Algebra.TensorProduct.tmul_mul_tmul]

/-- The underlying linear map is Mathlib's standard distribution of scalar extension over a
tensor product. -/
lemma baseChangeTensorMap_toLinearMap :
    (baseChangeTensorMap R N u t n).toLinearMap =
      (TensorProduct.AlgebraTensorModule.distribBaseChange R
        (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
        (fixedSubalgebra R N u t n)).toLinearMap := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero =>
      change
        baseChangeTensorMap R N u t n 0 =
          TensorProduct.AlgebraTensorModule.distribBaseChange R
            (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
            (fixedSubalgebra R N u t n) 0
      exact (baseChangeTensorMap R N u t n).map_zero.trans
        (TensorProduct.AlgebraTensorModule.distribBaseChange R
          (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
          (fixedSubalgebra R N u t n)).map_zero.symm
  | tmul a w =>
      induction w using TensorProduct.induction_on with
      | zero =>
          change
            baseChangeTensorMap R N u t n (a ⊗ₜ[R] 0) =
              TensorProduct.AlgebraTensorModule.distribBaseChange R
                (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
                (fixedSubalgebra R N u t n) (a ⊗ₜ[R] 0)
          rw [TensorProduct.tmul_zero]
          exact (baseChangeTensorMap R N u t n).map_zero.trans
            (TensorProduct.AlgebraTensorModule.distribBaseChange R
              (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
              (fixedSubalgebra R N u t n)).map_zero.symm
      | tmul x y =>
          change
            baseChangeTensorMap R N u t n (a ⊗ₜ[R] (x ⊗ₜ[R] y)) =
              TensorProduct.AlgebraTensorModule.distribBaseChange R
                (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
                (fixedSubalgebra R N u t n) (a ⊗ₜ[R] (x ⊗ₜ[R] y))
          rw [baseChangeTensorMap_tmul,
            TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma baseChangeTensorMap_bijective :
    Function.Bijective (baseChangeTensorMap R N u t n) := by
  have hfun :
      (baseChangeTensorMap R N u t n :
        QuadraticDescent.Algebra R t n ⊗[R]
            (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) →
          BaseChangedFixedTensorSquare R N u t n) =
        TensorProduct.AlgebraTensorModule.distribBaseChange R
          (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
          (fixedSubalgebra R N u t n) := by
    funext z
    exact LinearMap.congr_fun (baseChangeTensorMap_toLinearMap R N u t n) z
  rw [hfun]
  exact (TensorProduct.AlgebraTensorModule.distribBaseChange R
    (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
    (fixedSubalgebra R N u t n)).bijective

/-- Scalar extension distributes over the descended tensor square as an algebra
equivalence. -/
noncomputable def baseChangeTensorEquiv :
    QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) ≃ₐ[
      QuadraticDescent.Algebra R t n] BaseChangedFixedTensorSquare R N u t n :=
  AlgEquiv.ofBijective (baseChangeTensorMap R N u t n)
    (baseChangeTensorMap_bijective R N u t n)

@[simp]
lemma baseChangeTensorEquiv_apply
    (z : QuadraticDescent.Algebra R t n ⊗[R]
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) :
    baseChangeTensorEquiv R N u t n z = baseChangeTensorMap R N u t n z :=
  rfl

/-- After distributing scalar extension, apply the fixed-algebra base-change equivalence in
both tensor factors. -/
noncomputable def baseChangeTensorCoverEquiv (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) ≃ₐ[
      QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
          CoverCoordinateAlgebra R N u t n :=
  (baseChangeTensorEquiv R N u t n).trans
    (Algebra.TensorProduct.congr
      (baseChangeEquiv R N u t n h2 hdisc)
      (baseChangeEquiv R N u t n h2 hdisc))

/-! ## Semilinear descent on tensor squares -/

/-- The descent involution, regarded as a semilinear map for quadratic conjugation on the
covering ring. -/
noncomputable def descentSemilinearMap :
    CoverCoordinateAlgebra R N u t n →ₛₗ[
      (QuadraticDescent.conjugationAlgEquiv R t n).toRingEquiv.toRingHom]
      CoverCoordinateAlgebra R N u t n where
  toFun := descentAlgEquiv R N u t n
  map_add' x y := map_add (descentAlgEquiv R N u t n) x y
  map_smul' a z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b h =>
        change descentAlgEquiv R N u t n ((a * b) ⊗ₜ[R] h) =
          (QuadraticDescent.conjugationAlgEquiv R t n a *
            QuadraticDescent.conjugationAlgEquiv R t n b) ⊗ₜ[R]
              TateKummer.antipodeAlgEquiv N u h
        rw [descentAlgEquiv_tmul, map_mul]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]

@[simp]
lemma descentSemilinearMap_apply (z : CoverCoordinateAlgebra R N u t n) :
    descentSemilinearMap R N u t n z = descentAlgEquiv R N u t n z :=
  rfl

/-- Apply the semilinear descent involution in both factors of the cover tensor square. -/
noncomputable def coverTensorDescentSemilinearMap :
    (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n) →ₛₗ[
        (QuadraticDescent.conjugationAlgEquiv R t n).toRingEquiv.toRingHom]
      (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n) :=
  TensorProduct.map (descentSemilinearMap R N u t n)
    (descentSemilinearMap R N u t n)

@[simp]
lemma coverTensorDescentSemilinearMap_tmul
    (x y : CoverCoordinateAlgebra R N u t n) :
    coverTensorDescentSemilinearMap R N u t n
        (x ⊗ₜ[QuadraticDescent.Algebra R t n] y) =
      descentAlgEquiv R N u t n x ⊗ₜ[QuadraticDescent.Algebra R t n]
        descentAlgEquiv R N u t n y := by
  rfl

/-- Conjugate the quadratic scalar in the scalar extension of the fixed algebra. -/
noncomputable def baseChangeConjugationAlgEquiv :
    BaseChangedFixedAlgebra R N u t n ≃ₐ[R]
      BaseChangedFixedAlgebra R N u t n :=
  Algebra.TensorProduct.congr (QuadraticDescent.conjugationAlgEquiv R t n)
    (AlgEquiv.refl)

@[simp]
lemma baseChangeConjugationAlgEquiv_tmul
    (a : QuadraticDescent.Algebra R t n)
    (x : fixedSubalgebra R N u t n) :
    baseChangeConjugationAlgEquiv R N u t n (a ⊗ₜ[R] x) =
      QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R] x := by
  rfl

/-- The one-factor base-change equivalence intertwines scalar conjugation with the cover
descent involution. -/
lemma descentAlgEquiv_baseChangeEquiv (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : BaseChangedFixedAlgebra R N u t n) :
    descentAlgEquiv R N u t n (baseChangeEquiv R N u t n h2 hdisc z) =
      baseChangeEquiv R N u t n h2 hdisc
        (baseChangeConjugationAlgEquiv R N u t n z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
      rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_mul,
        descentAlgEquiv_algebraMap_cover,
        (mem_fixedSubalgebra R N u t n x).mp x.property,
        baseChangeConjugationAlgEquiv_tmul, baseChangeEquiv_apply,
        baseChangeToCover_tmul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Conjugate the quadratic scalar after extending the descended tensor square. -/
noncomputable def baseChangeTensorConjugationAlgEquiv :
    QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) ≃ₐ[R]
      QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  Algebra.TensorProduct.congr (QuadraticDescent.conjugationAlgEquiv R t n)
    (AlgEquiv.refl)

@[simp]
lemma baseChangeTensorConjugationAlgEquiv_tmul
    (a : QuadraticDescent.Algebra R t n)
    (x y : fixedSubalgebra R N u t n) :
    baseChangeTensorConjugationAlgEquiv R N u t n (a ⊗ₜ[R] (x ⊗ₜ[R] y)) =
      QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R] (x ⊗ₜ[R] y) := by
  rfl

@[simp]
lemma baseChangeTensorCoverEquiv_tmul (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : QuadraticDescent.Algebra R t n)
    (x y : fixedSubalgebra R N u t n) :
    baseChangeTensorCoverEquiv R N u t n h2 hdisc (a ⊗ₜ[R] (x ⊗ₜ[R] y)) =
      baseChangeEquiv R N u t n h2 hdisc (a ⊗ₜ[R] x) ⊗ₜ[
        QuadraticDescent.Algebra R t n]
      baseChangeEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] y) := by
  simp [baseChangeTensorCoverEquiv, baseChangeTensorEquiv_apply,
    baseChangeTensorMap_tmul]

/-- The two-factor base-change equivalence intertwines scalar conjugation with the
semilinear descent map on the cover tensor square. -/
lemma coverTensorDescentSemilinearMap_baseChangeTensorCoverEquiv
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : QuadraticDescent.Algebra R t n ⊗[R]
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) :
    coverTensorDescentSemilinearMap R N u t n
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc z) =
      baseChangeTensorCoverEquiv R N u t n h2 hdisc
        (baseChangeTensorConjugationAlgEquiv R N u t n z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      change coverTensorDescentSemilinearMap R N u t n 0 = 0
      exact (coverTensorDescentSemilinearMap R N u t n).map_zero
  | tmul a w =>
      induction w using TensorProduct.induction_on with
      | zero =>
          rw [TensorProduct.tmul_zero]
          simpa only [map_zero] using
            (coverTensorDescentSemilinearMap R N u t n).map_zero
      | tmul x y =>
          rw [baseChangeTensorCoverEquiv_tmul,
            coverTensorDescentSemilinearMap_tmul,
            descentAlgEquiv_baseChangeEquiv,
            descentAlgEquiv_baseChangeEquiv,
            baseChangeTensorConjugationAlgEquiv_tmul,
            baseChangeTensorCoverEquiv_tmul]
          simp only [baseChangeConjugationAlgEquiv_tmul, map_one]
      | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
  | add x y hx hy => simp only [map_add, hx, hy]

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
