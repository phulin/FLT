/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.QuadraticDescent
public import FLT.GroupScheme.TateKummer
public import FLT.GroupScheme.TateKummerPoints
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

universe u v

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

namespace Algebra.TensorProduct

variable (R A B C : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommSemiring B] [Algebra R B] [CommSemiring C] [Algebra R C]

/-- Algebraic form of the standard linear equivalence distributing scalar extension over a
tensor product. -/
noncomputable def distribBaseChangeAlgEquiv :
    A ⊗[R] (B ⊗[R] C) ≃ₐ[A] (A ⊗[R] B) ⊗[A] (A ⊗[R] C) :=
  AlgEquiv.ofLinearEquiv
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A B C)
    (by
      simp [Algebra.TensorProduct.one_def,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul])
    (by
      intro x y
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂]
      | tmul a p =>
          induction p using TensorProduct.induction_on with
          | zero => simp
          | add p₁ p₂ hp₁ hp₂ =>
              simp only [TensorProduct.tmul_add, add_mul, map_add, hp₁, hp₂]
          | tmul b c =>
              induction y using TensorProduct.induction_on with
              | zero => simp
              | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂]
              | tmul a' q =>
                  induction q using TensorProduct.induction_on with
                  | zero => simp
                  | add q₁ q₂ hq₁ hq₂ =>
                      simp only [TensorProduct.tmul_add, mul_add, map_add, hq₁, hq₂]
                  | tmul b' c' =>
                      simp [Algebra.TensorProduct.tmul_mul_tmul,
                        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul])

@[simp]
lemma distribBaseChangeAlgEquiv_tmul (a : A) (b : B) (c : C) :
    distribBaseChangeAlgEquiv R A B C (a ⊗ₜ[R] (b ⊗ₜ[R] c)) =
      (a ⊗ₜ[R] b) ⊗ₜ[A] ((1 : A) ⊗ₜ[R] c) := by
  rfl

end Algebra.TensorProduct

namespace Algebra.TensorProduct

section Convolution

variable (R : Type u) [CommRing R]
variable (K : Type u) [CommRing K] [Algebra R K]
variable (H : Type u) [CommRing H] [Bialgebra R H]
variable (S : Type v) [CommRing S]
  [Algebra R S] [Algebra K S] [IsScalarTower R K S]

/-- Restricting a point of a scalar-extended bialgebra to the original bialgebra
preserves convolution. -/
lemma liftEquivRight_symm_convMul
    (φ ψ : K ⊗[R] H →ₐ[K] S) :
    (liftEquivRight R K H S).symm
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      (WithConv.toConv ((liftEquivRight R K H S).symm φ) *
        WithConv.toConv ((liftEquivRight R K H S).symm ψ)).ofConv := by
  let e := liftEquivRight R K H S
  let φR := e.symm φ
  let ψR := e.symm ψ
  have heval (z : H ⊗[R] H) :
      Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _)
          (Algebra.TensorProduct.mapRingHom (algebraMap R K)
            (RingHomClass.toRingHom
              (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
            (RingHomClass.toRingHom
              (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
            (by simp [← IsScalarTower.algebraMap_eq])
            (by simp [← IsScalarTower.algebraMap_eq]) z) =
        Algebra.TensorProduct.lift φR ψR (fun _ _ ↦ Commute.all _ _) z := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [φR, ψR, e]
    | add a b ha hb => simp only [map_add, ha, hb]
  apply AlgHom.ext
  intro h
  change (WithConv.toConv φ * WithConv.toConv ψ)
      (Algebra.TensorProduct.includeRight h) =
    (WithConv.toConv φR * WithConv.toConv ψR) h
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply]
  have hcomul := DFunLike.congr_fun
    (Bialgebra.comul_includeRight (R := R) (A := K) (B := H)) h
  change Algebra.TensorProduct.lift φ ψ (fun _ _ ↦ Commute.all _ _)
      (Bialgebra.comulAlgHom K (K ⊗[R] H)
        (Algebra.TensorProduct.includeRight h)) =
    Algebra.TensorProduct.lift φR ψR (fun _ _ ↦ Commute.all _ _)
      (Bialgebra.comulAlgHom R H h)
  rw [show Bialgebra.comulAlgHom K (K ⊗[R] H)
      (Algebra.TensorProduct.includeRight h) =
        Algebra.TensorProduct.mapRingHom (algebraMap R K)
          (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
          (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight : H →ₐ[R] K ⊗[R] H))
          (by simp [← IsScalarTower.algebraMap_eq])
          (by simp [← IsScalarTower.algebraMap_eq])
          (Bialgebra.comulAlgHom R H h) by
    convert hcomul using 1 <;> rfl]
  exact heval (Bialgebra.comulAlgHom R H h)

/-- Extending a point to a scalar-extended bialgebra preserves convolution. -/
lemma liftEquivRight_convMul (φ ψ : H →ₐ[R] S) :
    liftEquivRight R K H S
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      (WithConv.toConv (liftEquivRight R K H S φ) *
        WithConv.toConv (liftEquivRight R K H S ψ)).ofConv := by
  apply (liftEquivRight R K H S).symm.injective
  rw [liftEquivRight_symm_convMul R K H S]
  simp

end Convolution

end Algebra.TensorProduct

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

section ScalarExtendedCover

variable (S : Type v) [CommRing S] [Algebra R S]
  [Algebra (QuadraticDescent.Algebra R t n) S]
  [IsScalarTower R (QuadraticDescent.Algebra R t n) S]

/-- After any further scalar extension of the quadratic cover, the descended coordinate
algebra becomes the ordinary Tate--Kummer coordinate algebra. -/
noncomputable def scalarExtendedCoverEquiv
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    S ⊗[R] fixedSubalgebra R N u t n ≃ₐ[S]
      S ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u :=
  (Algebra.TensorProduct.cancelBaseChange R
    (QuadraticDescent.Algebra R t n) S S
      (fixedSubalgebra R N u t n)).symm.trans
    ((Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S)
      (baseChangeEquiv R N u t n h2 hdisc)).trans
        (Algebra.TensorProduct.cancelBaseChange R
          (QuadraticDescent.Algebra R t n) S S
            (TateKummer.CoordinateAlgebra (R := R) N u)))

@[simp]
lemma scalarExtendedCoverEquiv_tmul
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (s : S) (z : fixedSubalgebra R N u t n) :
    scalarExtendedCoverEquiv R N u t n S h2 hdisc (s ⊗ₜ[R] z) =
      (Algebra.TensorProduct.cancelBaseChange R
        (QuadraticDescent.Algebra R t n) S S
          (TateKummer.CoordinateAlgebra (R := R) N u))
        (s ⊗ₜ[QuadraticDescent.Algebra R t n]
          baseChangeEquiv R N u t n h2 hdisc
            ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] z)) := by
  rfl

end ScalarExtendedCover

section QuadraticFieldCover

variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L]

/-- Over the quadratic field supplied by a trace--norm generator, the descended
coordinate algebra is the split Tate--Kummer coordinate algebra. -/
noncomputable def fieldExtendedCoverEquiv (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    L ⊗[R] fixedSubalgebra R N u t n ≃ₐ[L]
      L ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u := by
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  letI : Algebra (QuadraticDescent.Algebra R t n) L := f.toRingHom.toAlgebra
  letI : IsScalarTower R (QuadraticDescent.Algebra R t n) L :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (f.commutes r).symm
  exact scalarExtendedCoverEquiv R N u t n L h2 hdisc

/-- After first forming the generic fiber over `K` and then passing to its quadratic
splitting field `L`, the descended coordinate algebra becomes the split Tate--Kummer
coordinate algebra. -/
noncomputable def genericFiberFieldExtendedCoverEquiv (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    L ⊗[K] (K ⊗[R] fixedSubalgebra R N u t n) ≃ₐ[L]
      L ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u :=
  (Algebra.TensorProduct.cancelBaseChange R K L L
      (fixedSubalgebra R N u t n)).trans
    (fieldExtendedCoverEquiv R N u t n K L θ htrace hnorm h2 hdisc)

end QuadraticFieldCover

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

/-! ## Compatibility of cover comultiplication with descent -/

/-- Comultiplication on the tensor-product cover is the scalar extension of
comultiplication on the Tate--Kummer algebra. -/
lemma coverComulAlgHom_tmul (a : QuadraticDescent.Algebra R t n)
    (h : TateKummer.CoordinateAlgebra (R := R) N u) :
    Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n) (a ⊗ₜ[R] h) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R
        (QuadraticDescent.Algebra R t n)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (a ⊗ₜ[R] Bialgebra.comulAlgHom R
          (TateKummer.CoordinateAlgebra (R := R) N u) h) := by
  rw [Bialgebra.TensorProduct.comulAlgHom_def]
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul]
  rw [show Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
      (QuadraticDescent.Algebra R t n) a =
        (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[QuadraticDescent.Algebra R t n]
          a by rfl]
  change
    Algebra.TensorProduct.tensorTensorTensorComm R
        (QuadraticDescent.Algebra R t n) R (QuadraticDescent.Algebra R t n)
        (QuadraticDescent.Algebra R t n) (QuadraticDescent.Algebra R t n)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[
            QuadraticDescent.Algebra R t n] a)
          ⊗ₜ[R] Bialgebra.comulAlgHom R
            (TateKummer.CoordinateAlgebra (R := R) N u) h) = _
  generalize Bialgebra.comulAlgHom R
    (TateKummer.CoordinateAlgebra (R := R) N u) h = q
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [Algebra.TensorProduct.tensorTensorTensorComm_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      have hsmul (z : TateKummer.CoordinateAlgebra (R := R) N u) :
          a • ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] z) = a ⊗ₜ[R] z := by
        rw [TensorProduct.AlgebraTensorModule.smul_eq_lsmul_rTensor]
        simp
      rw [← hsmul x, ← hsmul y]
      exact (TensorProduct.smul_tmul a
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] x)
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] y)).symm
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- Semilinear descent commutes with the base-change distribution map. -/
lemma coverTensorDescentSemilinearMap_distribBaseChange
    (a : QuadraticDescent.Algebra R t n)
    (q : TateKummer.CoordinateAlgebra (R := R) N u ⊗[R]
      TateKummer.CoordinateAlgebra (R := R) N u) :
    coverTensorDescentSemilinearMap R N u t n
        (TensorProduct.AlgebraTensorModule.distribBaseChange R
          (QuadraticDescent.Algebra R t n)
          (TateKummer.CoordinateAlgebra (R := R) N u)
          (TateKummer.CoordinateAlgebra (R := R) N u) (a ⊗ₜ[R] q)) =
      TensorProduct.AlgebraTensorModule.distribBaseChange R
        (QuadraticDescent.Algebra R t n)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (TateKummer.CoordinateAlgebra (R := R) N u)
        (QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R]
          TensorProduct.map (TateKummer.antipodeAlgHom N u).toLinearMap
            (TateKummer.antipodeAlgHom N u).toLinearMap q) := by
  induction q using TensorProduct.induction_on with
  | zero =>
      change coverTensorDescentSemilinearMap R N u t n 0 = 0
      exact (coverTensorDescentSemilinearMap R N u t n).map_zero
  | tmul x y =>
      rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        coverTensorDescentSemilinearMap_tmul,
        descentAlgEquiv_tmul, descentAlgEquiv_tmul,
        TensorProduct.map_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul]
      simp only [TateKummer.antipodeAlgEquiv_apply, map_one]
      rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The cover comultiplication is equivariant for the quadratic descent datum. -/
lemma coverComulAlgHom_descentAlgEquiv
    (z : CoverCoordinateAlgebra R N u t n) :
    coverTensorDescentSemilinearMap R N u t n
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) z) =
      Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n) (descentAlgEquiv R N u t n z) := by
  induction z using TensorProduct.induction_on with
  | zero =>
      change coverTensorDescentSemilinearMap R N u t n 0 = 0
      exact (coverTensorDescentSemilinearMap R N u t n).map_zero
  | tmul a h =>
      have hc := LinearMap.congr_fun
        (HopfAlgebra.comul_comp_antipode_of_isCocomm
          (R := R) (A := TateKummer.CoordinateAlgebra (R := R) N u)) h
      simp only [LinearMap.comp_apply] at hc
      change
        Bialgebra.comulAlgHom R (TateKummer.CoordinateAlgebra (R := R) N u)
            (TateKummer.antipodeAlgHom N u h) =
          TensorProduct.map (TateKummer.antipodeAlgHom N u).toLinearMap
            (TateKummer.antipodeAlgHom N u).toLinearMap
            (Bialgebra.comulAlgHom R
              (TateKummer.CoordinateAlgebra (R := R) N u) h) at hc
      rw [coverComulAlgHom_tmul,
        coverTensorDescentSemilinearMap_distribBaseChange,
        descentAlgEquiv_tmul, coverComulAlgHom_tmul]
      change
        TensorProduct.AlgebraTensorModule.distribBaseChange R
            (QuadraticDescent.Algebra R t n)
            (TateKummer.CoordinateAlgebra (R := R) N u)
            (TateKummer.CoordinateAlgebra (R := R) N u)
            (QuadraticDescent.conjugationAlgEquiv R t n a ⊗ₜ[R]
              TensorProduct.map (TateKummer.antipodeAlgHom N u).toLinearMap
                (TateKummer.antipodeAlgHom N u).toLinearMap
                (Bialgebra.comulAlgHom R
                  (TateKummer.CoordinateAlgebra (R := R) N u) h)) = _
      rw [TateKummer.antipodeAlgEquiv_apply]
      rw [← hc]
  | add x y hx hy => simp only [map_add, hx, hy]

/-! ## Descent of comultiplication -/

/-- Transport cover comultiplication through the one- and two-factor base-change
equivalences. -/
noncomputable def transportedCoverComulAlgHom (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    BaseChangedFixedAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  (baseChangeTensorCoverEquiv R N u t n h2 hdisc).symm.toAlgHom.comp
    ((Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n)).comp
        (baseChangeEquiv R N u t n h2 hdisc).toAlgHom)

/-- Transported cover comultiplication is equivariant for conjugation on the quadratic
scalar. -/
lemma transportedCoverComulAlgHom_equivariant (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : BaseChangedFixedAlgebra R N u t n) :
    baseChangeTensorConjugationAlgEquiv R N u t n
        (transportedCoverComulAlgHom R N u t n h2 hdisc z) =
      transportedCoverComulAlgHom R N u t n h2 hdisc
        (baseChangeConjugationAlgEquiv R N u t n z) := by
  apply (baseChangeTensorCoverEquiv R N u t n h2 hdisc).injective
  rw [← coverTensorDescentSemilinearMap_baseChangeTensorCoverEquiv]
  simp only [transportedCoverComulAlgHom, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  rw [coverComulAlgHom_descentAlgEquiv,
    descentAlgEquiv_baseChangeEquiv]

/-- The algebraic conjugation map on the scalar extension is its previously defined
module-linear conjugation map. -/
lemma baseChangeTensorConjugationAlgEquiv_eq_conjugationTensorLinear
    (z : QuadraticDescent.Algebra R t n ⊗[R]
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) :
    baseChangeTensorConjugationAlgEquiv R N u t n z =
      QuadraticDescent.conjugationTensorLinear R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a q =>
      rw [QuadraticDescent.conjugationTensorLinear_tmul]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Restrict transported cover comultiplication to descended inputs.  Its codomain is
still scalar-extended; the next lemmas show that its quadratic coefficient vanishes. -/
noncomputable def baseChangedComulAlgHom (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    fixedSubalgebra R N u t n →ₐ[R]
      QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  ((transportedCoverComulAlgHom R N u t n h2 hdisc).restrictScalars R).comp
    (Algebra.TensorProduct.includeRight :
      fixedSubalgebra R N u t n →ₐ[R] BaseChangedFixedAlgebra R N u t n)

/-- Base-changed comultiplication of a descended element is fixed by conjugation on the
quadratic scalar. -/
lemma baseChangedComulAlgHom_fixed (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    QuadraticDescent.conjugationTensorLinear R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
        (baseChangedComulAlgHom R N u t n h2 hdisc z) =
      baseChangedComulAlgHom R N u t n h2 hdisc z := by
  rw [← baseChangeTensorConjugationAlgEquiv_eq_conjugationTensorLinear]
  change
    baseChangeTensorConjugationAlgEquiv R N u t n
        (transportedCoverComulAlgHom R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] z)) = _
  rw [transportedCoverComulAlgHom_equivariant,
    baseChangeConjugationAlgEquiv_tmul, map_one]
  rfl

/-- Therefore base-changed comultiplication has scalar quadratic coefficient. -/
lemma baseChangedComulAlgHom_eq_one_tmul (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    baseChangedComulAlgHom R N u t n h2 hdisc z =
      (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
        QuadraticDescent.tensorReCoeff R
          (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
          (baseChangedComulAlgHom R N u t n h2 hdisc z) :=
  QuadraticDescent.eq_one_tmul_tensorReCoeff_of_conjugationTensorLinear_eq R
    (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n h2 _
    (baseChangedComulAlgHom_fixed R N u t n h2 hdisc z)

/-- Comultiplication on the descended quadratic-twist coordinate algebra. -/
noncomputable def comulAlgHom (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n where
  toFun z := QuadraticDescent.tensorReCoeff R
    (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
    (baseChangedComulAlgHom R N u t n h2 hdisc z)
  map_zero' := by simp
  map_one' := by
    let coeff := QuadraticDescent.tensorReCoeff R
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
    calc
      coeff (baseChangedComulAlgHom R N u t n h2 hdisc 1) = coeff 1 :=
        congrArg coeff (baseChangedComulAlgHom R N u t n h2 hdisc).map_one
      _ = 1 := by
        change QuadraticDescent.tensorReCoeff R
            (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
            ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
              (1 : fixedSubalgebra R N u t n ⊗[R]
                fixedSubalgebra R N u t n)) = 1
        rw [QuadraticDescent.tensorReCoeff_tmul,
          QuadraticDescent.reCoeff_one, one_smul]
  map_add' x y := by
    let coeff := QuadraticDescent.tensorReCoeff R
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
    calc
      coeff (baseChangedComulAlgHom R N u t n h2 hdisc (x + y)) =
          coeff (baseChangedComulAlgHom R N u t n h2 hdisc x +
            baseChangedComulAlgHom R N u t n h2 hdisc y) :=
        congrArg coeff
          ((baseChangedComulAlgHom R N u t n h2 hdisc).map_add x y)
      _ = coeff (baseChangedComulAlgHom R N u t n h2 hdisc x) +
          coeff (baseChangedComulAlgHom R N u t n h2 hdisc y) :=
        coeff.map_add _ _
  map_mul' x y := by
    change QuadraticDescent.tensorReCoeff R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
        (baseChangedComulAlgHom R N u t n h2 hdisc (x * y)) = _
    rw [map_mul, baseChangedComulAlgHom_eq_one_tmul R N u t n h2 hdisc x,
      baseChangedComulAlgHom_eq_one_tmul R N u t n h2 hdisc y]
    simp only [Algebra.TensorProduct.tmul_mul_tmul,
      QuadraticDescent.tensorReCoeff_tmul, mul_one,
      QuadraticDescent.reCoeff_one, one_smul]
  commutes' r := by
    rw [(baseChangedComulAlgHom R N u t n h2 hdisc).commutes]
    change QuadraticDescent.tensorReCoeff R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
        (algebraMap R (QuadraticDescent.Algebra R t n) r ⊗ₜ[R]
          (1 : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) =
      algebraMap R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) r
    rw [QuadraticDescent.tensorReCoeff_tmul,
      QuadraticDescent.reCoeff_algebraMap]
    exact (Algebra.algebraMap_eq_smul_one r).symm

@[simp]
lemma comulAlgHom_apply (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    comulAlgHom R N u t n h2 hdisc z =
      QuadraticDescent.tensorReCoeff R
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) t n
        (baseChangedComulAlgHom R N u t n h2 hdisc z) :=
  rfl

/-- The base-changed descended comultiplication is a pure scalar tensor. -/
lemma baseChangedComulAlgHom_eq_one_tmul_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    baseChangedComulAlgHom R N u t n h2 hdisc z =
      (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
        comulAlgHom R N u t n h2 hdisc z := by
  rw [baseChangedComulAlgHom_eq_one_tmul]
  rfl

/-- After applying the tensor-square base-change equivalence, descended comultiplication
is exactly comultiplication on the cover. -/
lemma baseChangeTensorCoverEquiv_one_tmul_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    baseChangeTensorCoverEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          comulAlgHom R N u t n h2 hdisc z) =
      Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n) z := by
  rw [← baseChangedComulAlgHom_eq_one_tmul_comulAlgHom]
  change baseChangeTensorCoverEquiv R N u t n h2 hdisc
      (transportedCoverComulAlgHom R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] z)) = _
  simp only [transportedCoverComulAlgHom, AlgHom.comp_apply,
    AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  change Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n)
      (baseChangeEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] z)) = _
  rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul]

/-- The descended counit recovers the cover counit after applying the scalar map. -/
lemma coverCounitAlgHom_eq_algebraMap_counitAlgHom
    (h2 : IsUnit (2 : R)) (z : fixedSubalgebra R N u t n) :
    coverCounitAlgHom R N u t n z =
      algebraMap R (QuadraticDescent.Algebra R t n)
        (counitAlgHom R N u t n h2 z) := by
  rw [coverCounitAlgHom_eq_algebraMap_reCoeff R N u t n h2 z]
  rfl

/-- The descended antipode is the restriction of the cover antipode. -/
lemma coverAntipodeAlgHom_coe (z : fixedSubalgebra R N u t n) :
    coverAntipodeAlgHom R N u t n z =
      (antipodeAlgHom R N u t n z : CoverCoordinateAlgebra R N u t n) := by
  rfl

/-! ## Counit identities -/

noncomputable def rightCounitContraction (h2 : IsUnit (2 : R)) :
    fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n :=
  (Algebra.TensorProduct.lid R (fixedSubalgebra R N u t n)).toAlgHom.comp
    (Algebra.TensorProduct.map (counitAlgHom R N u t n h2)
      (AlgHom.id R (fixedSubalgebra R N u t n)))

@[simp]
lemma rightCounitContraction_tmul (h2 : IsUnit (2 : R))
    (x y : fixedSubalgebra R N u t n) :
    rightCounitContraction R N u t n h2 (x ⊗ₜ[R] y) =
      counitAlgHom R N u t n h2 x • y := by
  rfl

noncomputable def coverRightCounitContraction :
    CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n :=
  (Algebra.TensorProduct.lid (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n)).toAlgHom.comp
      (Algebra.TensorProduct.map (coverCounitAlgHom R N u t n)
        (AlgHom.id (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n)))

@[simp]
lemma coverRightCounitContraction_tmul
    (x y : CoverCoordinateAlgebra R N u t n) :
    coverRightCounitContraction R N u t n
        (x ⊗ₜ[QuadraticDescent.Algebra R t n] y) =
      coverCounitAlgHom R N u t n x • y := by
  rfl

lemma baseChangeEquiv_rightCounitContraction
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          rightCounitContraction R N u t n h2 q) =
      coverRightCounitContraction R N u t n
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [rightCounitContraction_tmul, baseChangeTensorCoverEquiv_tmul,
        coverRightCounitContraction_tmul,
        baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, baseChangeToCover_tmul, map_one, one_mul,
        coverCounitAlgHom_eq_algebraMap_counitAlgHom R N u t n h2 x]
      rw [IsScalarTower.algebraMap_smul, one_mul]
      exact (Subalgebra.val (fixedSubalgebra R N u t n)).toLinearMap.map_smul
        (counitAlgHom R N u t n h2 x) y
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

lemma coverRightCounitContraction_comul (z : CoverCoordinateAlgebra R N u t n) :
    coverRightCounitContraction R N u t n
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) z) = z := by
  change TensorProduct.lid (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n)
      ((Coalgebra.counit (R := QuadraticDescent.Algebra R t n)).rTensor
        (CoverCoordinateAlgebra R N u t n)
        (Coalgebra.comul (R := QuadraticDescent.Algebra R t n) z)) = z
  rw [Coalgebra.rTensor_counit_comul]
  simp

lemma rightCounitContraction_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    rightCounitContraction R N u t n h2
        (comulAlgHom R N u t n h2 hdisc z) = z := by
  have h := baseChangeEquiv_rightCounitContraction R N u t n h2 hdisc
    (comulAlgHom R N u t n h2 hdisc z)
  rw [baseChangeTensorCoverEquiv_one_tmul_comulAlgHom,
    coverRightCounitContraction_comul] at h
  change baseChangeEquiv R N u t n h2 hdisc
      ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
        rightCounitContraction R N u t n h2
          (comulAlgHom R N u t n h2 hdisc z)) =
        (z : CoverCoordinateAlgebra R N u t n) at h
  rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul] at h
  exact Subtype.ext h

lemma rightCounit_comp_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (Algebra.TensorProduct.map (counitAlgHom R N u t n h2)
      (AlgHom.id R (fixedSubalgebra R N u t n))).comp
        (comulAlgHom R N u t n h2 hdisc) =
      (Algebra.TensorProduct.lid R (fixedSubalgebra R N u t n)).symm.toAlgHom := by
  apply AlgHom.ext
  intro z
  apply (Algebra.TensorProduct.lid R (fixedSubalgebra R N u t n)).injective
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [(Algebra.TensorProduct.lid R
    (fixedSubalgebra R N u t n)).apply_symm_apply]
  change rightCounitContraction R N u t n h2
    (comulAlgHom R N u t n h2 hdisc z) = z
  exact rightCounitContraction_comulAlgHom R N u t n h2 hdisc z

noncomputable def leftCounitContraction (h2 : IsUnit (2 : R)) :
    fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n :=
  (Algebra.TensorProduct.rid R R (fixedSubalgebra R N u t n)).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id R (fixedSubalgebra R N u t n))
      (counitAlgHom R N u t n h2))

@[simp]
lemma leftCounitContraction_tmul (h2 : IsUnit (2 : R))
    (x y : fixedSubalgebra R N u t n) :
    leftCounitContraction R N u t n h2 (x ⊗ₜ[R] y) =
      counitAlgHom R N u t n h2 y • x := by
  rfl

noncomputable def coverLeftCounitContraction :
    CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n :=
  (Algebra.TensorProduct.rid (QuadraticDescent.Algebra R t n)
    (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n)).toAlgHom.comp
      (Algebra.TensorProduct.map
        (AlgHom.id (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n))
        (coverCounitAlgHom R N u t n))

@[simp]
lemma coverLeftCounitContraction_tmul
    (x y : CoverCoordinateAlgebra R N u t n) :
    coverLeftCounitContraction R N u t n
        (x ⊗ₜ[QuadraticDescent.Algebra R t n] y) =
      coverCounitAlgHom R N u t n y • x := by
  rfl

lemma baseChangeEquiv_leftCounitContraction
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          leftCounitContraction R N u t n h2 q) =
      coverLeftCounitContraction R N u t n
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [leftCounitContraction_tmul, baseChangeTensorCoverEquiv_tmul,
        coverLeftCounitContraction_tmul,
        baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, baseChangeToCover_tmul, map_one, one_mul,
        coverCounitAlgHom_eq_algebraMap_counitAlgHom R N u t n h2 y]
      rw [IsScalarTower.algebraMap_smul, one_mul]
      exact (Subalgebra.val (fixedSubalgebra R N u t n)).toLinearMap.map_smul
        (counitAlgHom R N u t n h2 y) x
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

lemma coverLeftCounitContraction_comul (z : CoverCoordinateAlgebra R N u t n) :
    coverLeftCounitContraction R N u t n
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) z) = z := by
  change TensorProduct.rid (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n)
      ((Coalgebra.counit (R := QuadraticDescent.Algebra R t n)).lTensor
        (CoverCoordinateAlgebra R N u t n)
        (Coalgebra.comul (R := QuadraticDescent.Algebra R t n) z)) = z
  rw [Coalgebra.lTensor_counit_comul]
  simp

lemma leftCounitContraction_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    leftCounitContraction R N u t n h2
        (comulAlgHom R N u t n h2 hdisc z) = z := by
  have h := baseChangeEquiv_leftCounitContraction R N u t n h2 hdisc
    (comulAlgHom R N u t n h2 hdisc z)
  rw [baseChangeTensorCoverEquiv_one_tmul_comulAlgHom,
    coverLeftCounitContraction_comul] at h
  change baseChangeEquiv R N u t n h2 hdisc
      ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
        leftCounitContraction R N u t n h2
          (comulAlgHom R N u t n h2 hdisc z)) =
        (z : CoverCoordinateAlgebra R N u t n) at h
  rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul] at h
  exact Subtype.ext h

lemma leftCounit_comp_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (Algebra.TensorProduct.map (AlgHom.id R (fixedSubalgebra R N u t n))
      (counitAlgHom R N u t n h2)).comp
        (comulAlgHom R N u t n h2 hdisc) =
      (Algebra.TensorProduct.rid R R (fixedSubalgebra R N u t n)).symm.toAlgHom := by
  apply AlgHom.ext
  intro z
  apply (Algebra.TensorProduct.rid R R (fixedSubalgebra R N u t n)).injective
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  rw [(Algebra.TensorProduct.rid R R
    (fixedSubalgebra R N u t n)).apply_symm_apply]
  change leftCounitContraction R N u t n h2
    (comulAlgHom R N u t n h2 hdisc z) = z
  exact leftCounitContraction_comulAlgHom R N u t n h2 hdisc z

/-! ## Coassociativity -/

section Coassociativity

noncomputable local instance fixedTensorCommSemiring :
    CommSemiring (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  inferInstance

noncomputable local instance fixedTensorAlgebra :
    Algebra R (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  inferInstance

noncomputable local instance coverTensorCommSemiring :
    CommSemiring (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n) :=
  inferInstance

noncomputable local instance coverTensorAlgebra :
    Algebra (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n) :=
  inferInstance

noncomputable local instance fixedTripleCommSemiring :
    CommSemiring (fixedSubalgebra R N u t n ⊗[R]
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) :=
  inferInstance

noncomputable local instance fixedTripleAlgebra :
    Algebra R (fixedSubalgebra R N u t n ⊗[R]
      (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) :=
  inferInstance

noncomputable local instance coverTripleCommSemiring :
    CommSemiring (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
      (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n)) :=
  inferInstance

/-- Scalar extension of the right-associated tensor cube of the fixed algebra is the
right-associated tensor cube of the cover algebra. -/
noncomputable def baseChangeTripleCoverEquiv (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    QuadraticDescent.Algebra R t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R]
          (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) ≃ₐ[
      QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
          CoverCoordinateAlgebra R N u t n) :=
  (Algebra.TensorProduct.distribBaseChangeAlgEquiv R
    (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n)
    (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)).trans
      (Algebra.TensorProduct.congr
        (baseChangeEquiv R N u t n h2 hdisc)
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc))

@[simp]
lemma baseChangeTripleCoverEquiv_tmul (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : QuadraticDescent.Algebra R t n)
    (x : fixedSubalgebra R N u t n)
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeTripleCoverEquiv R N u t n h2 hdisc
        (a ⊗ₜ[R] (x ⊗ₜ[R] q)) =
      baseChangeEquiv R N u t n h2 hdisc (a ⊗ₜ[R] x) ⊗ₜ[
        QuadraticDescent.Algebra R t n]
        baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q) := by
  rfl

/-- Comultiply the second tensor factor after comultiplying once. -/
noncomputable def rightIteratedComulAlgHom (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  (Algebra.TensorProduct.map (AlgHom.id R (fixedSubalgebra R N u t n))
    (comulAlgHom R N u t n h2 hdisc)).comp
      (comulAlgHom R N u t n h2 hdisc)

/-- The right-iterated cover comultiplication. -/
noncomputable def coverRightIteratedComulAlgHom :
    CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
          CoverCoordinateAlgebra R N u t n) :=
  (Algebra.TensorProduct.map
    (AlgHom.id (QuadraticDescent.Algebra R t n) (CoverCoordinateAlgebra R N u t n))
    (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n))).comp
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n))

/-- Base change intertwines comultiplication of the second tensor factor. -/
lemma baseChangeTripleCoverEquiv_map_id_comul
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeTripleCoverEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          Algebra.TensorProduct.map (AlgHom.id R (fixedSubalgebra R N u t n))
            (comulAlgHom R N u t n h2 hdisc) q) =
      Algebra.TensorProduct.map
          (AlgHom.id (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n))
          (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n))
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        baseChangeTripleCoverEquiv_tmul,
        baseChangeTensorCoverEquiv_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, map_one, one_mul,
        baseChangeTensorCoverEquiv_one_tmul_comulAlgHom,
        baseChangeToCover_tmul, map_one, one_mul]
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]

/-- Comultiply the first tensor factor after comultiplying once, then reassociate. -/
noncomputable def leftIteratedComulAlgHom (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :=
  (Algebra.TensorProduct.assoc R R R
    (fixedSubalgebra R N u t n) (fixedSubalgebra R N u t n)
      (fixedSubalgebra R N u t n)).toAlgHom.comp
    ((Algebra.TensorProduct.map (comulAlgHom R N u t n h2 hdisc)
      (AlgHom.id R (fixedSubalgebra R N u t n))).comp
        (comulAlgHom R N u t n h2 hdisc))

/-- The left-iterated cover comultiplication, reassociated to the right. -/
noncomputable def coverLeftIteratedComulAlgHom :
    CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        (CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
          CoverCoordinateAlgebra R N u t n) :=
  (Algebra.TensorProduct.assoc (QuadraticDescent.Algebra R t n)
    (QuadraticDescent.Algebra R t n) (QuadraticDescent.Algebra R t n)
    (CoverCoordinateAlgebra R N u t n) (CoverCoordinateAlgebra R N u t n)
      (CoverCoordinateAlgebra R N u t n)).toAlgHom.comp
    ((Algebra.TensorProduct.map
      (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n))
      (AlgHom.id (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n))).comp
          (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n)))

/-- Base change intertwines comultiplication of the first tensor factor and the
associator. -/
lemma baseChangeTripleCoverEquiv_assoc_map_comul_id
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeTripleCoverEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          (Algebra.TensorProduct.assoc R R R
            (fixedSubalgebra R N u t n) (fixedSubalgebra R N u t n)
              (fixedSubalgebra R N u t n))
            (Algebra.TensorProduct.map (comulAlgHom R N u t n h2 hdisc)
              (AlgHom.id R (fixedSubalgebra R N u t n)) q)) =
      (Algebra.TensorProduct.assoc (QuadraticDescent.Algebra R t n)
        (QuadraticDescent.Algebra R t n) (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n) (CoverCoordinateAlgebra R N u t n)
          (CoverCoordinateAlgebra R N u t n))
        (Algebra.TensorProduct.map
          (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n))
          (AlgHom.id (QuadraticDescent.Algebra R t n)
            (CoverCoordinateAlgebra R N u t n))
          (baseChangeTensorCoverEquiv R N u t n h2 hdisc
            ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q))) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        baseChangeTensorCoverEquiv_tmul,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, map_one, one_mul,
        ← baseChangeTensorCoverEquiv_one_tmul_comulAlgHom R N u t n h2 hdisc x]
      generalize comulAlgHom R N u t n h2 hdisc x = p
      induction p using TensorProduct.induction_on with
      | zero => simp
      | tmul x₁ x₂ =>
          rw [Algebra.TensorProduct.assoc_tmul,
            baseChangeTripleCoverEquiv_tmul,
            baseChangeTensorCoverEquiv_tmul,
            baseChangeTensorCoverEquiv_tmul,
            Algebra.TensorProduct.assoc_tmul]
          simp only [baseChangeEquiv_apply]
      | add p q hp hq =>
          simp only [map_add, TensorProduct.add_tmul, TensorProduct.tmul_add, hp, hq]
  | add p q hp hq => simp only [map_add, TensorProduct.tmul_add, hp, hq]

/-- Right-iterated descended comultiplication becomes the cover operation after scalar
extension. -/
lemma baseChangeTripleCoverEquiv_one_tmul_rightIterated
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    baseChangeTripleCoverEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          rightIteratedComulAlgHom R N u t n h2 hdisc z) =
      coverRightIteratedComulAlgHom R N u t n z := by
  rw [rightIteratedComulAlgHom, AlgHom.comp_apply,
    baseChangeTripleCoverEquiv_map_id_comul,
    baseChangeTensorCoverEquiv_one_tmul_comulAlgHom]
  rfl

/-- Left-iterated descended comultiplication becomes the cover operation after scalar
extension. -/
lemma baseChangeTripleCoverEquiv_one_tmul_leftIterated
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    baseChangeTripleCoverEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          leftIteratedComulAlgHom R N u t n h2 hdisc z) =
      coverLeftIteratedComulAlgHom R N u t n z := by
  change baseChangeTripleCoverEquiv R N u t n h2 hdisc
      ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
        (Algebra.TensorProduct.assoc R R R
          (fixedSubalgebra R N u t n) (fixedSubalgebra R N u t n)
            (fixedSubalgebra R N u t n))
          (Algebra.TensorProduct.map (comulAlgHom R N u t n h2 hdisc)
            (AlgHom.id R (fixedSubalgebra R N u t n))
            (comulAlgHom R N u t n h2 hdisc z))) = _
  rw [
    baseChangeTripleCoverEquiv_assoc_map_comul_id,
    baseChangeTensorCoverEquiv_one_tmul_comulAlgHom]
  rfl

/-- The cover's two iterated comultiplications agree. -/
lemma coverLeftIteratedComulAlgHom_eq_right
    (z : CoverCoordinateAlgebra R N u t n) :
    coverLeftIteratedComulAlgHom R N u t n z =
      coverRightIteratedComulAlgHom R N u t n z := by
  change TensorProduct.assoc (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n) (CoverCoordinateAlgebra R N u t n)
        (CoverCoordinateAlgebra R N u t n)
      ((Coalgebra.comul (R := QuadraticDescent.Algebra R t n)).rTensor
        (CoverCoordinateAlgebra R N u t n)
        (Coalgebra.comul (R := QuadraticDescent.Algebra R t n) z)) =
    (Coalgebra.comul (R := QuadraticDescent.Algebra R t n)).lTensor
      (CoverCoordinateAlgebra R N u t n)
      (Coalgebra.comul (R := QuadraticDescent.Algebra R t n) z)
  exact Coalgebra.coassoc_apply z

/-- Coassociativity descends from the quadratic cover, since extracting the scalar
coefficient reflects equality of pure scalar tensors. -/
lemma leftIteratedComulAlgHom_eq_right_apply
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    leftIteratedComulAlgHom R N u t n h2 hdisc z =
      rightIteratedComulAlgHom R N u t n h2 hdisc z := by
  have hcover :
      baseChangeTripleCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
            leftIteratedComulAlgHom R N u t n h2 hdisc z) =
        baseChangeTripleCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
            rightIteratedComulAlgHom R N u t n h2 hdisc z) := by
    rw [baseChangeTripleCoverEquiv_one_tmul_leftIterated,
      baseChangeTripleCoverEquiv_one_tmul_rightIterated,
      coverLeftIteratedComulAlgHom_eq_right]
  have htensor :
      (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          leftIteratedComulAlgHom R N u t n h2 hdisc z =
        (1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          rightIteratedComulAlgHom R N u t n h2 hdisc z :=
    (baseChangeTripleCoverEquiv R N u t n h2 hdisc).injective hcover
  have hcoeff := congrArg
    (QuadraticDescent.tensorReCoeff R
      (fixedSubalgebra R N u t n ⊗[R]
        (fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n)) t n)
    htensor
  simpa using hcoeff

/-- The descended comultiplication is coassociative. -/
lemma coassoc_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (Algebra.TensorProduct.assoc R R R
      (fixedSubalgebra R N u t n) (fixedSubalgebra R N u t n)
        (fixedSubalgebra R N u t n)).toAlgHom.comp
      ((Algebra.TensorProduct.map (comulAlgHom R N u t n h2 hdisc)
        (AlgHom.id R (fixedSubalgebra R N u t n))).comp
          (comulAlgHom R N u t n h2 hdisc)) =
    (Algebra.TensorProduct.map (AlgHom.id R (fixedSubalgebra R N u t n))
      (comulAlgHom R N u t n h2 hdisc)).comp
        (comulAlgHom R N u t n h2 hdisc) := by
  apply AlgHom.ext
  intro z
  exact leftIteratedComulAlgHom_eq_right_apply R N u t n h2 hdisc z

end Coassociativity

/-! ## The descended bialgebra -/

/-- The fixed quadratic-twist coordinate algebra, equipped with the comultiplication
and counit descended from the quadratic cover. -/
@[instance_reducible]
noncomputable def coordinateBialgebra (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Bialgebra R (fixedSubalgebra R N u t n) :=
  Bialgebra.ofAlgHom (comulAlgHom R N u t n h2 hdisc)
    (counitAlgHom R N u t n h2)
    (coassoc_comulAlgHom R N u t n h2 hdisc)
    (rightCounit_comp_comulAlgHom R N u t n h2 hdisc)
    (leftCounit_comp_comulAlgHom R N u t n h2 hdisc)

/-- Scalar extension to the quadratic cover identifies the descended bialgebra with the
split Tate--Kummer bialgebra. -/
noncomputable def baseChangeBialgEquiv
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    letI := coordinateBialgebra R N u t n h2 hdisc
    BaseChangedFixedAlgebra R N u t n ≃ₐc[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n := by
  letI := coordinateBialgebra R N u t n h2 hdisc
  apply BialgEquiv.ofAlgEquiv (baseChangeEquiv R N u t n h2 hdisc)
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro z
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.includeRight_apply]
    rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul]
    have hz := coverCounitAlgHom_eq_algebraMap_counitAlgHom
      R N u t n h2 z
    change CoalgebraStruct.counit
        (R := QuadraticDescent.Algebra R t n)
          (z : CoverCoordinateAlgebra R N u t n) =
        algebraMap R (QuadraticDescent.Algebra R t n)
          (CoalgebraStruct.counit (R := R) z) at hz
    have hcounit := DFunLike.congr_fun
      (Bialgebra.counitAlgHom_comp_includeRight
        (R := R) (A := QuadraticDescent.Algebra R t n)
        (B := fixedSubalgebra R N u t n)) z
    change CoalgebraStruct.counit
        (R := QuadraticDescent.Algebra R t n)
          (z : CoverCoordinateAlgebra R N u t n) =
      (((Bialgebra.counitAlgHom (QuadraticDescent.Algebra R t n)
        (BaseChangedFixedAlgebra R N u t n)).restrictScalars R).comp
          (Algebra.TensorProduct.includeRight :
            fixedSubalgebra R N u t n →ₐ[R]
              BaseChangedFixedAlgebra R N u t n)) z
    rw [hcounit]
    exact hz
  · apply Algebra.TensorProduct.ext_ring
    apply AlgHom.ext
    intro z
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
      AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.includeRight_apply]
    have hcomul := DFunLike.congr_fun
      (Bialgebra.comul_includeRight (R := R)
        (A := QuadraticDescent.Algebra R t n)
        (B := fixedSubalgebra R N u t n)) z
    have hcoordinateComul :
        Bialgebra.comulAlgHom R (fixedSubalgebra R N u t n) =
          comulAlgHom R N u t n h2 hdisc := rfl
    rw [hcoordinateComul] at hcomul
    have hinclude :
        (Algebra.TensorProduct.includeRight :
          fixedSubalgebra R N u t n →ₐ[R]
            BaseChangedFixedAlgebra R N u t n).toRingHom.comp
            (algebraMap R (fixedSubalgebra R N u t n)) =
          (algebraMap (QuadraticDescent.Algebra R t n)
            (BaseChangedFixedAlgebra R N u t n)).comp
              (algebraMap R (QuadraticDescent.Algebra R t n)) := by
      ext r
      simp [← IsScalarTower.algebraMap_apply R
        (QuadraticDescent.Algebra R t n)]
    have hcomul' :
        Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (BaseChangedFixedAlgebra R N u t n)
            (Algebra.TensorProduct.includeRight z) =
          baseChangeTensorEmbedding R N u t n
            (comulAlgHom R N u t n h2 hdisc z) := by
      let q := comulAlgHom R N u t n h2 hdisc z
      change
        (((RingHomClass.toRingHom
          (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (BaseChangedFixedAlgebra R N u t n))).comp
          (RingHomClass.toRingHom
            (Algebra.TensorProduct.includeRight :
              fixedSubalgebra R N u t n →ₐ[R]
                BaseChangedFixedAlgebra R N u t n))) z) =
          baseChangeTensorEmbedding R N u t n q
      have hq : (comulAlgHom R N u t n h2 hdisc).toRingHom z = q := rfl
      simp only [RingHom.comp_apply] at hcomul ⊢
      change _ = Algebra.TensorProduct.mapRingHom
        (algebraMap R (QuadraticDescent.Algebra R t n))
        (Algebra.TensorProduct.includeRight :
          fixedSubalgebra R N u t n →ₐ[R]
            BaseChangedFixedAlgebra R N u t n).toRingHom
        (Algebra.TensorProduct.includeRight :
          fixedSubalgebra R N u t n →ₐ[R]
            BaseChangedFixedAlgebra R N u t n).toRingHom
        hinclude hinclude ((comulAlgHom R N u t n h2 hdisc).toRingHom z)
          at hcomul
      rw [hq] at hcomul
      rw [hcomul]
      let f : (fixedSubalgebra R N u t n ⊗[R]
          fixedSubalgebra R N u t n) →+*
            BaseChangedFixedTensorSquare R N u t n :=
        Algebra.TensorProduct.mapRingHom
          (algebraMap R (QuadraticDescent.Algebra R t n))
          (Algebra.TensorProduct.includeRight :
            fixedSubalgebra R N u t n →ₐ[R]
              BaseChangedFixedAlgebra R N u t n).toRingHom
          (Algebra.TensorProduct.includeRight :
            fixedSubalgebra R N u t n →ₐ[R]
              BaseChangedFixedAlgebra R N u t n).toRingHom
          hinclude hinclude
      change f q = baseChangeTensorEmbedding R N u t n q
      induction q using TensorProduct.induction_on with
      | zero =>
          exact f.map_zero.trans
            (baseChangeTensorEmbedding R N u t n).map_zero.symm
      | add x y hx hy =>
          calc
            f (x + y) = f x + f y := f.map_add x y
            _ = baseChangeTensorEmbedding R N u t n x +
                baseChangeTensorEmbedding R N u t n y :=
              congrArg₂ (fun a b ↦ a + b) hx hy
            _ = baseChangeTensorEmbedding R N u t n (x + y) :=
              (baseChangeTensorEmbedding R N u t n).map_add x y |>.symm
      | tmul x y => simp [f, baseChangeTensorEmbedding_tmul]
    have hmap (q : fixedSubalgebra R N u t n ⊗[R]
        fixedSubalgebra R N u t n) :
        (Algebra.TensorProduct.map
          (baseChangeEquiv R N u t n h2 hdisc).toAlgHom
          (baseChangeEquiv R N u t n h2 hdisc).toAlgHom)
            (baseChangeTensorEmbedding R N u t n q) =
          baseChangeTensorCoverEquiv R N u t n h2 hdisc
            ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q) := by
      induction q using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
      | tmul x y =>
          simp [baseChangeTensorCoverEquiv_tmul]
    change
      (Algebra.TensorProduct.map
        (baseChangeEquiv R N u t n h2 hdisc).toAlgHom
        (baseChangeEquiv R N u t n h2 hdisc).toAlgHom)
          (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
            (BaseChangedFixedAlgebra R N u t n)
            (Algebra.TensorProduct.includeRight z)) = _
    rw [hcomul']
    rw [hmap]
    rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul]
    rw [baseChangeTensorCoverEquiv_one_tmul_comulAlgHom]

/-- Transporting points contravariantly across the quadratic-cover bialgebra equivalence
preserves convolution. -/
lemma baseChangeArrowCongr_convMul
    (S : Type v) [CommRing S]
    [Algebra (QuadraticDescent.Algebra R t n) S]
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (α β : BaseChangedFixedAlgebra R N u t n →ₐ[
      QuadraticDescent.Algebra R t n] S) :
    letI := coordinateBialgebra R N u t n h2 hdisc
    (AlgEquiv.arrowCongr (baseChangeEquiv R N u t n h2 hdisc)
      (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S))
        (WithConv.toConv α * WithConv.toConv β).ofConv =
      (WithConv.toConv
          ((AlgEquiv.arrowCongr (baseChangeEquiv R N u t n h2 hdisc)
            (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)) α) *
        WithConv.toConv
          ((AlgEquiv.arrowCongr (baseChangeEquiv R N u t n h2 hdisc)
            (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)) β)).ofConv := by
  letI := coordinateBialgebra R N u t n h2 hdisc
  change (WithConv.toConv α * WithConv.toConv β).ofConv.comp
      (baseChangeEquiv R N u t n h2 hdisc).symm.toAlgHom = _
  exact AlgHom.convMul_comp_bialgHom_distrib
    (WithConv.toConv α) (WithConv.toConv β)
    (baseChangeBialgEquiv R N u t n h2 hdisc).symm.toBialgHom

section QuadraticFieldPoints

variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L]
variable (S : Type v) [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra K S] [Algebra L S]
  [IsScalarTower R K S] [IsScalarTower R L S]

/-- Geometric points of the descended generic fiber are Kummer points.  The construction
restricts a `K`-generic point to the fixed algebra, extends it to the integral quadratic
cover using the chosen trace--norm generator, transports it across `baseChangeBialgEquiv`,
and finally restricts it to the split Tate--Kummer coordinate algebra. -/
noncomputable def genericFiberAlgHomUnitEquiv (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (K ⊗[R] fixedSubalgebra R N u t n →ₐ[K] S) ≃
      TateKummer.KummerUnitPoint R S N u := by
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  let g : QuadraticDescent.Algebra R t n →+* S :=
    (algebraMap L S).comp f.toRingHom
  letI : Algebra (QuadraticDescent.Algebra R t n) S := g.toAlgebra
  letI : IsScalarTower R (QuadraticDescent.Algebra R t n) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R S r = algebraMap L S (f (algebraMap R
        (QuadraticDescent.Algebra R t n) r))
      rw [f.commutes, IsScalarTower.algebraMap_apply R L S]
  exact
    (Algebra.TensorProduct.liftEquivRight R K
      (fixedSubalgebra R N u t n) S).symm |>.trans
    ((Algebra.TensorProduct.liftEquivRight R
      (QuadraticDescent.Algebra R t n)
      (fixedSubalgebra R N u t n) S).trans
    ((AlgEquiv.arrowCongr (baseChangeEquiv R N u t n h2 hdisc)
      (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)).trans
    ((Algebra.TensorProduct.liftEquivRight R
      (QuadraticDescent.Algebra R t n)
      (TateKummer.CoordinateAlgebra (R := R) N u) S).symm.trans
      (TateKummer.coordinateAlgHomUnitEquiv R S N u))))

/-- The generic-fiber point classification sends convolution on the descended Hopf algebra
to carry-corrected Kummer multiplication. -/
lemma genericFiberAlgHomUnitEquiv_convMul (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (φ ψ : K ⊗[R] fixedSubalgebra R N u t n →ₐ[K] S) :
    letI := coordinateBialgebra R N u t n h2 hdisc
    genericFiberAlgHomUnitEquiv R N u t n K L S θ htrace hnorm h2 hdisc
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      TateKummer.kummerUnitPointMul R S N u
        (genericFiberAlgHomUnitEquiv R N u t n K L S θ
          htrace hnorm h2 hdisc φ)
        (genericFiberAlgHomUnitEquiv R N u t n K L S θ
          htrace hnorm h2 hdisc ψ) := by
  letI := coordinateBialgebra R N u t n h2 hdisc
  let f := QuadraticDescent.integralFieldAlgHom K L R t n θ htrace hnorm
  let g : QuadraticDescent.Algebra R t n →+* S :=
    (algebraMap L S).comp f.toRingHom
  letI : Algebra (QuadraticDescent.Algebra R t n) S := g.toAlgebra
  letI : IsScalarTower R (QuadraticDescent.Algebra R t n) S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change algebraMap R S r = algebraMap L S (f (algebraMap R
        (QuadraticDescent.Algebra R t n) r))
      rw [f.commutes, IsScalarTower.algebraMap_apply R L S]
  let eK := Algebra.TensorProduct.liftEquivRight R K
    (fixedSubalgebra R N u t n) S
  let eA := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n) S
  let eH := Algebra.TensorProduct.liftEquivRight R
    (QuadraticDescent.Algebra R t n)
      (TateKummer.CoordinateAlgebra (R := R) N u) S
  let eCover := AlgEquiv.arrowCongr
    (baseChangeEquiv R N u t n h2 hdisc)
    (AlgEquiv.refl : S ≃ₐ[QuadraticDescent.Algebra R t n] S)
  change TateKummer.coordinateAlgHomUnitEquiv R S N u
      (eH.symm (eCover (eA (eK.symm
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv)))) =
    TateKummer.kummerUnitPointMul R S N u
      (TateKummer.coordinateAlgHomUnitEquiv R S N u
        (eH.symm (eCover (eA (eK.symm φ)))))
      (TateKummer.coordinateAlgHomUnitEquiv R S N u
        (eH.symm (eCover (eA (eK.symm ψ)))))
  rw [Algebra.TensorProduct.liftEquivRight_symm_convMul R K
      (fixedSubalgebra R N u t n) S,
    Algebra.TensorProduct.liftEquivRight_convMul R
      (QuadraticDescent.Algebra R t n) (fixedSubalgebra R N u t n) S,
    baseChangeArrowCongr_convMul R N u t n S h2 hdisc,
    Algebra.TensorProduct.liftEquivRight_symm_convMul R
      (QuadraticDescent.Algebra R t n)
      (TateKummer.CoordinateAlgebra (R := R) N u) S,
    TateKummer.coordinateAlgHomUnitEquiv_convMul]

end QuadraticFieldPoints

/-! ## Antipode identities -/

/-- Apply the descended antipode to the left tensor factor and multiply. -/
noncomputable def antipodeLeftContraction :
    fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n :=
  Algebra.TensorProduct.lift (antipodeAlgHom R N u t n)
    (AlgHom.id R (fixedSubalgebra R N u t n)) fun _ _ ↦ Commute.all _ _

/-- Apply the cover antipode to the left tensor factor and multiply. -/
noncomputable def coverAntipodeLeftContraction :
    CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.lift (coverAntipodeAlgHom R N u t n)
    (AlgHom.id (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n)) fun _ _ ↦ Commute.all _ _

@[simp]
lemma antipodeLeftContraction_tmul
    (x y : fixedSubalgebra R N u t n) :
    antipodeLeftContraction R N u t n (x ⊗ₜ[R] y) =
      antipodeAlgHom R N u t n x * y := by
  rfl

@[simp]
lemma coverAntipodeLeftContraction_tmul
    (x y : CoverCoordinateAlgebra R N u t n) :
    coverAntipodeLeftContraction R N u t n
        (x ⊗ₜ[QuadraticDescent.Algebra R t n] y) =
      coverAntipodeAlgHom R N u t n x * y := by
  rfl

/-- Scalar extension intertwines the left antipode contractions. -/
lemma baseChangeEquiv_antipodeLeftContraction
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          antipodeLeftContraction R N u t n q) =
      coverAntipodeLeftContraction R N u t n
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [antipodeLeftContraction_tmul, baseChangeTensorCoverEquiv_tmul,
        coverAntipodeLeftContraction_tmul]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, baseChangeToCover_tmul,
        baseChangeToCover_tmul, map_one, one_mul, map_mul,
        coverAntipodeAlgHom_coe]
      simp only [map_one, one_mul]
      exact rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The explicit cover inversion is the antipode of its tensor-product Hopf algebra. -/
lemma coverAntipodeAlgHom_eq_hopfAntipodeAlgHom :
    coverAntipodeAlgHom R N u t n =
      HopfAlgebra.antipodeAlgHom (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n) := by
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a h =>
      change a ⊗ₜ[R] TateKummer.antipodeAlgHom N u h =
        a ⊗ₜ[R] TateKummer.antipodeAlgHom N u h
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The algebraic left contraction is the linear contraction in the cover Hopf
axiom. -/
lemma coverAntipodeLeftContraction_eq_hopfApply
    (q : CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n) :
    coverAntipodeLeftContraction R N u t n q =
      LinearMap.mul' (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n)
        ((HopfAlgebra.antipode (QuadraticDescent.Algebra R t n)).rTensor
          (CoverCoordinateAlgebra R N u t n) q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [coverAntipodeLeftContraction_tmul]
      rw [coverAntipodeAlgHom_eq_hopfAntipodeAlgHom]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Left antipode cancellation on the cover. -/
lemma coverAntipodeLeftContraction_comul
    (z : CoverCoordinateAlgebra R N u t n) :
    coverAntipodeLeftContraction R N u t n
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) z) =
      algebraMap (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n)
        (coverCounitAlgHom R N u t n z) := by
  rw [coverAntipodeLeftContraction_eq_hopfApply]
  exact HopfAlgebra.mul_antipode_rTensor_comul_apply z

/-- Left antipode cancellation descends from the quadratic cover. -/
lemma antipodeLeftContraction_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    antipodeLeftContraction R N u t n
        (comulAlgHom R N u t n h2 hdisc z) =
      algebraMap R (fixedSubalgebra R N u t n)
        (counitAlgHom R N u t n h2 z) := by
  have h := baseChangeEquiv_antipodeLeftContraction R N u t n h2 hdisc
    (comulAlgHom R N u t n h2 hdisc z)
  rw [baseChangeTensorCoverEquiv_one_tmul_comulAlgHom,
    coverAntipodeLeftContraction_comul,
    coverCounitAlgHom_eq_algebraMap_counitAlgHom R N u t n h2 z] at h
  rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul] at h
  apply Subtype.ext
  calc
    (↑(antipodeLeftContraction R N u t n
        (comulAlgHom R N u t n h2 hdisc z)) :
      CoverCoordinateAlgebra R N u t n) =
        algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n)
          (algebraMap R (QuadraticDescent.Algebra R t n)
            (counitAlgHom R N u t n h2 z)) := h
    _ = ↑(algebraMap R (fixedSubalgebra R N u t n)
          (counitAlgHom R N u t n h2 z)) := by
      rw [← IsScalarTower.algebraMap_apply R (QuadraticDescent.Algebra R t n)]
      rfl

/-- Left antipode cancellation in the form required by `HopfAlgebra.ofAlgHom`. -/
lemma mul_antipode_rTensor_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (antipodeLeftContraction R N u t n).comp
        (comulAlgHom R N u t n h2 hdisc) =
      (Algebra.ofId R (fixedSubalgebra R N u t n)).comp
        (counitAlgHom R N u t n h2) := by
  apply AlgHom.ext
  intro z
  exact antipodeLeftContraction_comulAlgHom R N u t n h2 hdisc z

/-- Apply the descended antipode to the right tensor factor and multiply. -/
noncomputable def antipodeRightContraction :
    fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n →ₐ[R]
      fixedSubalgebra R N u t n :=
  Algebra.TensorProduct.lift (AlgHom.id R (fixedSubalgebra R N u t n))
    (antipodeAlgHom R N u t n) fun _ _ ↦ Commute.all _ _

/-- Apply the cover antipode to the right tensor factor and multiply. -/
noncomputable def coverAntipodeRightContraction :
    CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
        CoverCoordinateAlgebra R N u t n →ₐ[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n :=
  Algebra.TensorProduct.lift
    (AlgHom.id (QuadraticDescent.Algebra R t n)
      (CoverCoordinateAlgebra R N u t n))
    (coverAntipodeAlgHom R N u t n) fun _ _ ↦ Commute.all _ _

@[simp]
lemma antipodeRightContraction_tmul
    (x y : fixedSubalgebra R N u t n) :
    antipodeRightContraction R N u t n (x ⊗ₜ[R] y) =
      x * antipodeAlgHom R N u t n y := by
  rfl

@[simp]
lemma coverAntipodeRightContraction_tmul
    (x y : CoverCoordinateAlgebra R N u t n) :
    coverAntipodeRightContraction R N u t n
        (x ⊗ₜ[QuadraticDescent.Algebra R t n] y) =
      x * coverAntipodeAlgHom R N u t n y := by
  rfl

/-- Scalar extension intertwines the right antipode contractions. -/
lemma baseChangeEquiv_antipodeRightContraction
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q : fixedSubalgebra R N u t n ⊗[R] fixedSubalgebra R N u t n) :
    baseChangeEquiv R N u t n h2 hdisc
        ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R]
          antipodeRightContraction R N u t n q) =
      coverAntipodeRightContraction R N u t n
        (baseChangeTensorCoverEquiv R N u t n h2 hdisc
          ((1 : QuadraticDescent.Algebra R t n) ⊗ₜ[R] q)) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [antipodeRightContraction_tmul, baseChangeTensorCoverEquiv_tmul,
        coverAntipodeRightContraction_tmul]
      simp only [baseChangeEquiv_apply]
      rw [baseChangeToCover_tmul, baseChangeToCover_tmul,
        baseChangeToCover_tmul, map_one, one_mul, map_mul,
        coverAntipodeAlgHom_coe]
      simp only [map_one, one_mul]
      exact rfl
  | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]

/-- The algebraic right contraction is the linear contraction in the cover Hopf
axiom. -/
lemma coverAntipodeRightContraction_eq_hopfApply
    (q : CoverCoordinateAlgebra R N u t n ⊗[QuadraticDescent.Algebra R t n]
      CoverCoordinateAlgebra R N u t n) :
    coverAntipodeRightContraction R N u t n q =
      LinearMap.mul' (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n)
        ((HopfAlgebra.antipode (QuadraticDescent.Algebra R t n)).lTensor
          (CoverCoordinateAlgebra R N u t n) q) := by
  induction q using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
      rw [coverAntipodeRightContraction_tmul]
      rw [coverAntipodeAlgHom_eq_hopfAntipodeAlgHom]
      rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Right antipode cancellation on the cover. -/
lemma coverAntipodeRightContraction_comul
    (z : CoverCoordinateAlgebra R N u t n) :
    coverAntipodeRightContraction R N u t n
        (Bialgebra.comulAlgHom (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n) z) =
      algebraMap (QuadraticDescent.Algebra R t n)
        (CoverCoordinateAlgebra R N u t n)
        (coverCounitAlgHom R N u t n z) := by
  rw [coverAntipodeRightContraction_eq_hopfApply]
  exact HopfAlgebra.mul_antipode_lTensor_comul_apply z

/-- Right antipode cancellation descends from the quadratic cover. -/
lemma antipodeRightContraction_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (z : fixedSubalgebra R N u t n) :
    antipodeRightContraction R N u t n
        (comulAlgHom R N u t n h2 hdisc z) =
      algebraMap R (fixedSubalgebra R N u t n)
        (counitAlgHom R N u t n h2 z) := by
  have h := baseChangeEquiv_antipodeRightContraction R N u t n h2 hdisc
    (comulAlgHom R N u t n h2 hdisc z)
  rw [baseChangeTensorCoverEquiv_one_tmul_comulAlgHom,
    coverAntipodeRightContraction_comul,
    coverCounitAlgHom_eq_algebraMap_counitAlgHom R N u t n h2 z] at h
  rw [baseChangeEquiv_apply, baseChangeToCover_tmul, map_one, one_mul] at h
  apply Subtype.ext
  calc
    (↑(antipodeRightContraction R N u t n
        (comulAlgHom R N u t n h2 hdisc z)) :
      CoverCoordinateAlgebra R N u t n) =
        algebraMap (QuadraticDescent.Algebra R t n)
          (CoverCoordinateAlgebra R N u t n)
          (algebraMap R (QuadraticDescent.Algebra R t n)
            (counitAlgHom R N u t n h2 z)) := h
    _ = ↑(algebraMap R (fixedSubalgebra R N u t n)
          (counitAlgHom R N u t n h2 z)) := by
      rw [← IsScalarTower.algebraMap_apply R (QuadraticDescent.Algebra R t n)]
      rfl

/-- Right antipode cancellation in the form required by `HopfAlgebra.ofAlgHom`. -/
lemma mul_antipode_lTensor_comulAlgHom
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    (antipodeRightContraction R N u t n).comp
        (comulAlgHom R N u t n h2 hdisc) =
      (Algebra.ofId R (fixedSubalgebra R N u t n)).comp
        (counitAlgHom R N u t n h2) := by
  apply AlgHom.ext
  intro z
  exact antipodeRightContraction_comulAlgHom R N u t n h2 hdisc z

/-- The descended fixed algebra is a Hopf algebra, hence represents the quadratic
twist of the Tate--Kummer affine group scheme. -/
@[instance_reducible]
noncomputable def coordinateHopfAlgebra
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    HopfAlgebra R (fixedSubalgebra R N u t n) := by
  letI : Bialgebra R (fixedSubalgebra R N u t n) :=
    coordinateBialgebra R N u t n h2 hdisc
  exact HopfAlgebra.ofAlgHom (antipodeAlgHom R N u t n)
    (mul_antipode_rTensor_comulAlgHom R N u t n h2 hdisc)
    (mul_antipode_lTensor_comulAlgHom R N u t n h2 hdisc)

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
