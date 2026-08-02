/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummer
public import FLT.Mathlib.Algebra.Algebra.Pi
public import Mathlib.RingTheory.Bialgebra.Convolution

/-!
# Geometric points of the Tate--Kummer model

This file identifies algebra maps out of the Tate--Kummer coordinate algebra with the
expected Kummer data: a component index `i : Fin N` and an element `x` satisfying
`x ^ N = u ^ i`.  It then transports the description to the generic fiber by the
universal property of the tensor product.
-/

@[expose] public section

open Polynomial
open scoped TensorProduct

universe u v

namespace TateKummer

/-- A root of the equation defining component `i`, valued in an `R`-algebra `S`. -/
def KummerRoot (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N i : ℕ) (u : Rˣ) :=
  {x : S // x ^ N = algebraMap R S ((u : R) ^ i)}

/-- A geometric point of the Tate--Kummer model: a component together with its Kummer
coordinate. -/
def KummerPoint (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : ℕ) (u : Rˣ) :=
  Σ i : Fin N, KummerRoot R S N i u

/-- The unit-valued form of a Kummer root.  This is the form naturally used by Tate
uniformization. -/
def KummerUnitRoot (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N i : ℕ) (u : Rˣ) :=
  {x : Sˣ // x ^ N = Units.map (algebraMap R S) (u ^ i)}

/-- A component together with a unit-valued Kummer coordinate. -/
def KummerUnitPoint (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : ℕ) (u : Rˣ) :=
  Σ i : Fin N, KummerUnitRoot R S N i u

/-- Carry-corrected multiplication of two unit-valued Kummer roots. -/
noncomputable def kummerUnitRootMul
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N)
    (x : KummerUnitRoot R S N i u) (y : KummerUnitRoot R S N j u) :
    KummerUnitRoot R S N (addIndex N i j) u := by
  let uS : Sˣ := Units.map (algebraMap R S) u
  refine ⟨x.1 * y.1 * (uS⁻¹) ^ addCarry N i j, ?_⟩
  rw [mul_pow, mul_pow, x.2, y.2]
  simpa [uS, map_pow] using
    unit_mul_unit_mul_invCarry_pow (R := S) N uS i j

/-- Carry-corrected multiplication on Kummer points. -/
noncomputable def kummerUnitPointMul
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : ℕ) [NeZero N] (u : Rˣ)
    (x y : KummerUnitPoint R S N u) : KummerUnitPoint R S N u :=
  ⟨addIndex N x.1 y.1, kummerUnitRootMul R S N u x.1 y.1 x.2 y.2⟩

/-- Apply an automorphism of the value algebra to the root coordinate of a Kummer
point. -/
noncomputable def kummerUnitPointMap
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    (N : ℕ) (u : Rˣ) (σ : S ≃ₐ[R] S)
    (x : KummerUnitPoint R S N u) : KummerUnitPoint R S N u := by
  refine ⟨x.1, ⟨Units.map σ.toRingEquiv.toMonoidHom x.2.1, ?_⟩⟩
  apply Units.ext
  simp only [Units.val_pow_eq_pow_val, Units.coe_map]
  rw [← map_pow]
  have hx : (x.2.1 : S) ^ N = algebraMap R S ((u : R) ^ x.1.1) := by
    simpa using congrArg Units.val x.2.2
  rw [hx]
  exact σ.commutes ((u : R) ^ x.1.1)

section Component

variable (R : Type u) [CommRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/-- Algebra maps from one Kummer component are exactly roots of its defining equation. -/
noncomputable def componentAlgHomEquiv (N i : ℕ) (u : Rˣ) :
    (Component R N i u →ₐ[R] S) ≃ KummerRoot R S N i u where
  toFun φ := ⟨φ (AdjoinRoot.root (componentPolynomial R N i u)), by
    rw [← map_pow, root_pow]
    exact φ.commutes ((u : R) ^ i)⟩
  invFun x := AdjoinRoot.liftAlgHom (componentPolynomial R N i u)
    (Algebra.ofId R S) x.1 (by
      simp [componentPolynomial, x.2])
  left_inv φ := by
    apply AdjoinRoot.algHom_ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
lemma componentAlgHomEquiv_apply_val (N i : ℕ) (u : Rˣ)
    (φ : Component R N i u →ₐ[R] S) :
    (componentAlgHomEquiv R S N i u φ).1 =
      φ (AdjoinRoot.root (componentPolynomial R N i u)) :=
  rfl

/-- Unit-valued version of `componentAlgHomEquiv`. -/
noncomputable def componentAlgHomUnitEquiv
    (N : ℕ) [NeZero N] (i : Fin N) (u : Rˣ) :
    (Component R N i u →ₐ[R] S) ≃ KummerUnitRoot R S N i u where
  toFun φ := ⟨Units.map φ.toRingHom.toMonoidHom (componentRootUnit N u i), by
    apply Units.ext
    change (φ (AdjoinRoot.root (componentPolynomial R N i u))) ^ N =
      algebraMap R S ((u : R) ^ i.1)
    rw [← map_pow, root_pow]
    exact φ.commutes ((u : R) ^ i.1)⟩
  invFun x := AdjoinRoot.liftAlgHom (componentPolynomial R N i u)
    (Algebra.ofId R S) x.1.1 (by
      have hx : (x.1 : S) ^ N = algebraMap R S ((u : R) ^ i.1) := by
        simpa using congrArg Units.val x.2
      simp [componentPolynomial, hx])
  left_inv φ := by
    apply AdjoinRoot.algHom_ext
    simp
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    simp

@[simp]
lemma componentAlgHomUnitEquiv_apply_val
    (N : ℕ) [NeZero N] (i : Fin N) (u : Rˣ)
    (φ : Component R N i u →ₐ[R] S) :
    ((componentAlgHomUnitEquiv R S N i u φ).1 : S) =
      φ (AdjoinRoot.root (componentPolynomial R N i u)) := by
  change φ (componentRootUnit N u i : Component R N i u) = _
  rw [componentRootUnit_val]

/-- Algebra maps from the product coordinate algebra to a domain select exactly one
component and then a root on that component. -/
noncomputable def coordinateAlgHomEquiv [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) :
    (CoordinateAlgebra (R := R) N u →ₐ[R] S) ≃ KummerPoint R S N u :=
  (Pi.algHomEquivOfIsDomain (R₀ := R) (S := S)
      (R := fun i : Fin N ↦ Component R N i u)).trans
    (Equiv.sigmaCongrRight fun i ↦ componentAlgHomEquiv R S N i u)

/-- Unit-valued form of the geometric-point classification. -/
noncomputable def coordinateAlgHomUnitEquiv [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) :
    (CoordinateAlgebra (R := R) N u →ₐ[R] S) ≃
      KummerUnitPoint R S N u :=
  (Pi.algHomEquivOfIsDomain (R₀ := R) (S := S)
      (R := fun i : Fin N ↦ Component R N i u)).trans
    (Equiv.sigmaCongrRight fun i ↦ componentAlgHomUnitEquiv R S N i u)

/-- The algebra map corresponding to unit-valued Kummer data on a fixed component. -/
noncomputable def componentPointAlgHom
    (N : ℕ) [NeZero N] (u : Rˣ) (i : Fin N)
    (x : KummerUnitRoot R S N i u) :
    CoordinateAlgebra (R := R) N u →ₐ[R] S :=
  (componentAlgHomUnitEquiv R S N i u).symm x |>.comp
    (Pi.evalAlgHom R (Components (R := R) N u) i)

@[simp]
lemma coordinateAlgHomUnitEquiv_symm_apply [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) (x : KummerUnitPoint R S N u) :
    (coordinateAlgHomUnitEquiv R S N u).symm x =
      componentPointAlgHom R S N u x.1 x.2 :=
  rfl

/-- Convolution of points supported on components `i` and `j` is supported on their sum,
and its root coordinate is the carry-corrected product. -/
lemma componentPointAlgHom_convMul [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) (i j : Fin N)
    (x : KummerUnitRoot R S N i u) (y : KummerUnitRoot R S N j u) :
    (WithConv.toConv (componentPointAlgHom R S N u i x) *
      WithConv.toConv (componentPointAlgHom R S N u j y)).ofConv =
        componentPointAlgHom R S N u (addIndex N i j)
          (kummerUnitRootMul R S N u i j x y) := by
  let α := (componentAlgHomUnitEquiv R S N i u).symm x
  let β := (componentAlgHomUnitEquiv R S N j u).symm y
  let γ := (componentAlgHomUnitEquiv R S N (addIndex N i j) u).symm
    (kummerUnitRootMul R S N u i j x y)
  have hlift (z : CoordinateAlgebra (R := R) N u ⊗[R]
      CoordinateAlgebra (R := R) N u) :
      Algebra.TensorProduct.lift
          (α.comp (Pi.evalAlgHom R (Components (R := R) N u) i))
          (β.comp (Pi.evalAlgHom R (Components (R := R) N u) j))
          (fun _ _ ↦ Commute.all _ _) z =
        Algebra.TensorProduct.lift α β (fun _ _ ↦ Commute.all _ _)
          (tensorCoordinateEquiv N u z j i) := by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  have hαroot :
      α (AdjoinRoot.root (componentPolynomial R N i u)) = (x.1 : S) := by
    calc
      _ = ((componentAlgHomUnitEquiv R S N i u α).1 : S) :=
        (componentAlgHomUnitEquiv_apply_val R S N i u α).symm
      _ = _ := congrArg (fun z : KummerUnitRoot R S N i u ↦ (z.1 : S))
        ((componentAlgHomUnitEquiv R S N i u).apply_symm_apply x)
  have hβroot :
      β (AdjoinRoot.root (componentPolynomial R N j u)) = (y.1 : S) := by
    calc
      _ = ((componentAlgHomUnitEquiv R S N j u β).1 : S) :=
        (componentAlgHomUnitEquiv_apply_val R S N j u β).symm
      _ = _ := congrArg (fun z : KummerUnitRoot R S N j u ↦ (z.1 : S))
        ((componentAlgHomUnitEquiv R S N j u).apply_symm_apply y)
  have hγroot :
      γ (AdjoinRoot.root
        (componentPolynomial R N (addIndex N i j) u)) =
        ((kummerUnitRootMul R S N u i j x y).1 : S) := by
    calc
      _ = ((componentAlgHomUnitEquiv R S N (addIndex N i j) u γ).1 : S) :=
        (componentAlgHomUnitEquiv_apply_val R S N (addIndex N i j) u γ).symm
      _ = _ := congrArg
        (fun z : KummerUnitRoot R S N (addIndex N i j) u ↦ (z.1 : S))
        ((componentAlgHomUnitEquiv R S N (addIndex N i j) u).apply_symm_apply
          (kummerUnitRootMul R S N u i j x y))
  have hαu : α (AdjoinRoot.of (componentPolynomial R N i u) (u⁻¹ : Rˣ)) =
      algebraMap R S (u⁻¹ : Rˣ) :=
    α.commutes (u⁻¹ : Rˣ)
  have hcomponent :
      (Algebra.TensorProduct.lift α β (fun _ _ ↦ Commute.all _ _)).comp
          (componentMulAlgHom N u i j) = γ := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, componentMulAlgHom_root]
    simp [componentMulRoot, hαroot, hβroot, hγroot, hαu,
      kummerUnitRootMul, map_pow, mul_comm,
      mul_left_comm, mul_assoc]
  apply AlgHom.ext
  intro f
  rw [AlgHom.convMul_apply]
  change Algebra.TensorProduct.lift
      (α.comp (Pi.evalAlgHom R (Components (R := R) N u) i))
      (β.comp (Pi.evalAlgHom R (Components (R := R) N u) j))
      (fun _ _ ↦ Commute.all _ _) (comulAlgHom N u f) =
    γ (f (addIndex N i j))
  rw [hlift, tensorCoordinateEquiv_comulAlgHom_apply]
  exact DFunLike.congr_fun hcomponent (f (addIndex N i j))

/-- Under the geometric-point classification, convolution is carry-corrected Kummer
multiplication. -/
lemma coordinateAlgHomUnitEquiv_convMul [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ)
    (φ ψ : CoordinateAlgebra (R := R) N u →ₐ[R] S) :
    coordinateAlgHomUnitEquiv R S N u
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      kummerUnitPointMul R S N u
        (coordinateAlgHomUnitEquiv R S N u φ)
        (coordinateAlgHomUnitEquiv R S N u ψ) := by
  let e := coordinateAlgHomUnitEquiv R S N u
  let x := e φ
  let y := e ψ
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
    componentPointAlgHom R S N u (addIndex N x.1 y.1)
      (kummerUnitRootMul R S N u x.1 y.1 x.2 y.2)
  rw [show φ = componentPointAlgHom R S N u x.1 x.2 by
        exact (e.symm_apply_apply φ).symm,
      show ψ = componentPointAlgHom R S N u y.1 y.2 by
        exact (e.symm_apply_apply ψ).symm]
  exact componentPointAlgHom_convMul R S N u x.1 y.1 x.2 y.2

/-- Postcomposition by an automorphism applies that automorphism to the Kummer root and
leaves the component index unchanged. -/
lemma coordinateAlgHomUnitEquiv_comp [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) (σ : S ≃ₐ[R] S)
    (φ : CoordinateAlgebra (R := R) N u →ₐ[R] S) :
    coordinateAlgHomUnitEquiv R S N u (σ.toAlgHom.comp φ) =
      kummerUnitPointMap R S N u σ
        (coordinateAlgHomUnitEquiv R S N u φ) := by
  let e := coordinateAlgHomUnitEquiv R S N u
  let x := e φ
  let α := (componentAlgHomUnitEquiv R S N x.1 u).symm x.2
  let xσ := (kummerUnitPointMap R S N u σ x).2
  let β := (componentAlgHomUnitEquiv R S N x.1 u).symm xσ
  have hαroot :
      α (AdjoinRoot.root (componentPolynomial R N x.1 u)) = (x.2.1 : S) := by
    calc
      _ = ((componentAlgHomUnitEquiv R S N x.1 u α).1 : S) :=
        (componentAlgHomUnitEquiv_apply_val R S N x.1 u α).symm
      _ = _ := congrArg
        (fun z : KummerUnitRoot R S N x.1 u ↦ (z.1 : S))
        ((componentAlgHomUnitEquiv R S N x.1 u).apply_symm_apply x.2)
  have hβroot :
      β (AdjoinRoot.root (componentPolynomial R N x.1 u)) = (xσ.1 : S) := by
    calc
      _ = ((componentAlgHomUnitEquiv R S N x.1 u β).1 : S) :=
        (componentAlgHomUnitEquiv_apply_val R S N x.1 u β).symm
      _ = _ := congrArg
        (fun z : KummerUnitRoot R S N x.1 u ↦ (z.1 : S))
        ((componentAlgHomUnitEquiv R S N x.1 u).apply_symm_apply xσ)
  have hcomponent : σ.toAlgHom.comp α = β := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, hαroot, hβroot]
    rfl
  apply e.symm.injective
  rw [e.symm_apply_apply]
  change σ.toAlgHom.comp φ = componentPointAlgHom R S N u x.1 xσ
  rw [show φ = componentPointAlgHom R S N u x.1 x.2 by
    exact (e.symm_apply_apply φ).symm]
  change σ.toAlgHom.comp (α.comp
      (Pi.evalAlgHom R (Components (R := R) N u) x.1)) =
    β.comp (Pi.evalAlgHom R (Components (R := R) N u) x.1)
  rw [← AlgHom.comp_assoc, hcomponent]

end Component

section GenericFiber

variable (R : Type u) [CommRing R]
variable (K : Type u) [CommRing K] [Algebra R K]
variable (S : Type v) [CommRing S] [IsDomain S]
  [Algebra R S] [Algebra K S] [IsScalarTower R K S]

/-- Geometric points of the generic fiber are Kummer points. -/
noncomputable def genericFiberAlgHomEquiv
    (N : ℕ) [NeZero N] (u : Rˣ) :
    (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) ≃
      KummerPoint R S N u :=
  (Algebra.TensorProduct.liftEquivRight R K
      (CoordinateAlgebra (R := R) N u) S).symm.trans
    (coordinateAlgHomEquiv R S N u)

/-- Unit-valued classification of geometric points of the generic fiber. -/
noncomputable def genericFiberAlgHomUnitEquiv
    (N : ℕ) [NeZero N] (u : Rˣ) :
    (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) ≃
      KummerUnitPoint R S N u :=
  (Algebra.TensorProduct.liftEquivRight R K
      (CoordinateAlgebra (R := R) N u) S).symm.trans
    (coordinateAlgHomUnitEquiv R S N u)

omit [IsDomain S] in
/-- Restricting a generic-fiber point to the integral coordinate algebra preserves
convolution. -/
lemma liftEquivRight_symm_convMul
    (N : ℕ) [NeZero N] (u : Rˣ)
    (φ ψ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    (Algebra.TensorProduct.liftEquivRight R K
        (CoordinateAlgebra (R := R) N u) S).symm
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      (WithConv.toConv
          ((Algebra.TensorProduct.liftEquivRight R K
            (CoordinateAlgebra (R := R) N u) S).symm φ) *
        WithConv.toConv
          ((Algebra.TensorProduct.liftEquivRight R K
            (CoordinateAlgebra (R := R) N u) S).symm ψ)).ofConv := by
  let H := CoordinateAlgebra (R := R) N u
  let e := Algebra.TensorProduct.liftEquivRight R K H S
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
    | tmul a b =>
        simp [φR, ψR, e]
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

/-- The unit-valued generic-fiber classification sends convolution to carry-corrected
Kummer multiplication. -/
lemma genericFiberAlgHomUnitEquiv_convMul
    (N : ℕ) [NeZero N] (u : Rˣ)
    (φ ψ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    genericFiberAlgHomUnitEquiv R K S N u
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      kummerUnitPointMul R S N u
        (genericFiberAlgHomUnitEquiv R K S N u φ)
        (genericFiberAlgHomUnitEquiv R K S N u ψ) := by
  change coordinateAlgHomUnitEquiv R S N u
      ((Algebra.TensorProduct.liftEquivRight R K
        (CoordinateAlgebra (R := R) N u) S).symm
          (WithConv.toConv φ * WithConv.toConv ψ).ofConv) =
    kummerUnitPointMul R S N u
      (coordinateAlgHomUnitEquiv R S N u
        ((Algebra.TensorProduct.liftEquivRight R K
          (CoordinateAlgebra (R := R) N u) S).symm φ))
      (coordinateAlgHomUnitEquiv R S N u
        ((Algebra.TensorProduct.liftEquivRight R K
          (CoordinateAlgebra (R := R) N u) S).symm ψ))
  rw [liftEquivRight_symm_convMul R K S N u,
    coordinateAlgHomUnitEquiv_convMul]

/-- The generic-fiber point classification is natural under automorphisms of the value
field over the generic-fiber base. -/
lemma genericFiberAlgHomUnitEquiv_comp
    (N : ℕ) [NeZero N] (u : Rˣ) (σ : S ≃ₐ[K] S)
    (φ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    genericFiberAlgHomUnitEquiv R K S N u (σ.toAlgHom.comp φ) =
      kummerUnitPointMap R S N u (σ.restrictScalars R)
        (genericFiberAlgHomUnitEquiv R K S N u φ) := by
  let e := Algebra.TensorProduct.liftEquivRight R K
    (CoordinateAlgebra (R := R) N u) S
  have hrestrict : e.symm (σ.toAlgHom.comp φ) =
      (σ.restrictScalars R).toAlgHom.comp (e.symm φ) := by
    apply AlgHom.ext
    intro f
    rfl
  change coordinateAlgHomUnitEquiv R S N u (e.symm (σ.toAlgHom.comp φ)) =
    kummerUnitPointMap R S N u (σ.restrictScalars R)
      (coordinateAlgHomUnitEquiv R S N u (e.symm φ))
  rw [hrestrict]
  exact coordinateAlgHomUnitEquiv_comp R S N u (σ.restrictScalars R) (e.symm φ)

end GenericFiber

end TateKummer
