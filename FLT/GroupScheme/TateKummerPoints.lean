/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummer
public import FLT.Mathlib.Algebra.Algebra.Pi

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

/-- Algebra maps from the product coordinate algebra to a domain select exactly one
component and then a root on that component. -/
noncomputable def coordinateAlgHomEquiv [IsDomain S]
    (N : ℕ) [NeZero N] (u : Rˣ) :
    (CoordinateAlgebra (R := R) N u →ₐ[R] S) ≃ KummerPoint R S N u :=
  (Pi.algHomEquivOfIsDomain (R₀ := R) (S := S)
      (R := fun i : Fin N ↦ Component R N i u)).trans
    (Equiv.sigmaCongrRight fun i ↦ componentAlgHomEquiv R S N i u)

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

end GenericFiber

end TateKummer
