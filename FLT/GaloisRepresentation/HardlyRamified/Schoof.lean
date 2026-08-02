/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Generic fibers of Schoof's finite-flat category

Schoof's category for the pair `(ell, p) = (2, 3)` consists of finite flat commutative
`3`-power group schemes over `Z[1/2]` whose inertia at `2` is tame.  Before constructing a
global integral model, its generic fiber is a finite `3`-primary Galois module which is
finite-flat at `3`, unramified away from `2` and `3`, and has odd inertia image at `2`.

This file packages those four logically separate conditions.  The global finite-flat gluing
theorem and Schoof's classification theorem are intentionally separate obligations.
-/

@[expose] public section

open IsLocalRing
open scoped NumberField
open scoped TensorProduct

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The base ring `ℤ[1/2]` of Schoof's `(2, 3)` category. -/
abbrev SchoofThreeBase := Localization.Away (2 : ℤ)

/-- The canonical inclusion `ℤ[1/2] → ℚ`. -/
noncomputable def schoofThreeBaseToRat : SchoofThreeBase →+* ℚ :=
  Localization.awayLift (Int.castRingHom ℚ) (2 : ℤ)
    (isUnit_iff_ne_zero.mpr (by norm_num))

/-- The generic-fiber conditions satisfied by an object of Schoof's `(2, 3)` category.

The last field states tameness in the finite Galois extension cut out by the representation:
at residue characteristic `2`, a finite Galois extension is tame precisely when its inertia
subgroup has odd order. -/
structure GaloisRep.IsSchoofThreeGenericFiber
    {A W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (rho : GaloisRep ℚ A W) : Prop where
  threePrimary : ∃ n : ℕ, ∀ x : W, (3 ^ n) • x = 0
  finiteFlatAtThree :
    rho.HasFlatProlongationAt
      (Nat.Prime.toHeightOneSpectrumRingOfIntegersRat (show Nat.Prime 3 by decide))
  unramifiedOutsideTwoThree :
    ∀ p (hp : p.Prime), p ≠ 2 ∧ p ≠ 3 →
      localInertiaGroup hp.toHeightOneSpectrumRingOfIntegersRat ≤
        (rho.fieldCutOutLocalAction hp.toHeightOneSpectrumRingOfIntegersRat).ker
  tameAtTwo :
    Odd
      (Nat.card
        ((AddSubgroup.inertia
          ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ ℚ_[2])).map
            (rho.fieldCutOutAction (algebraMap ℚ ℚ_[2]))))

/-- A global finite-flat Hopf-algebra model over `ℤ[1/2]` for a finite Galois module.
The chosen equivariant bijection identifies the geometric points of its generic fiber with
the given representation. -/
def GaloisRep.HasFiniteFlatModelAwayTwo
    {A W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (rho : GaloisRep ℚ A W) : Prop :=
  letI : Algebra SchoofThreeBase ℚ := schoofThreeBaseToRat.toAlgebra
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra SchoofThreeBase G)
    (_ : Module.Flat SchoofThreeBase G) (_ : Module.Finite SchoofThreeBase G)
    (_ : Algebra.Etale ℚ (ℚ ⊗[SchoofThreeBase] G))
    (e : Additive (ℚ ⊗[SchoofThreeBase] G →ₐ[ℚ] AlgebraicClosure ℚ) →+ W),
    Function.Bijective e ∧
      ∀ (sigma : Γ ℚ) (x : Additive
        (ℚ ⊗[SchoofThreeBase] G →ₐ[ℚ] AlgebraicClosure ℚ)),
        e (Additive.ofMul (sigma.toAlgHom.comp x.toMul)) = rho sigma (e x)

/-- A represented object of Schoof's `(2, 3)` category: the four arithmetic generic-fiber
conditions together with an actual global finite-flat model over `ℤ[1/2]`. -/
def GaloisRep.IsSchoofThreeObject
    {A W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (rho : GaloisRep ℚ A W) : Prop :=
  GaloisRep.IsSchoofThreeGenericFiber rho ∧
    GaloisRep.HasFiniteFlatModelAwayTwo rho

end GaloisRepresentation
