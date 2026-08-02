/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

import Mathlib.GroupTheory.PGroup

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

namespace GaloisRepresentation

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

/-- The generic-fiber conditions satisfied by an object of Schoof's `(2, 3)` category.

The last field states tameness in the finite Galois extension cut out by the representation:
at residue characteristic `2`, a finite Galois extension is tame precisely when its inertia
subgroup has odd order. -/
structure GaloisRep.IsSchoofThreeGenericFiber
    {A W : Type*} [CommRing A] [TopologicalSpace A]
    [AddCommGroup W] [Module A W] (rho : GaloisRep ℚ A W) : Prop where
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

end GaloisRepresentation
