/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Instances.ZMod

/-!
# Rank-one representations from quadratic characters

This file packages the sign character of a quadratic extension as a continuous rank-one
Galois representation over `ZMod N`.
-/

@[expose] public section

noncomputable section

/-- The trivial rank-one representation over `ZMod N`. -/
def trivialRankOneGaloisRep (K : Type*) [Field K] (N : ℕ) :
    GaloisRep K (ZMod N) (ZMod N) := by
  letI : TopologicalSpace (Module.End (ZMod N) (ZMod N)) :=
    moduleTopology (ZMod N) (Module.End (ZMod N) (ZMod N))
  exact ⟨1, continuous_const⟩

@[simp]
theorem trivialRankOneGaloisRep_apply (K : Type*) [Field K] (N : ℕ)
    (σ : Field.absoluteGaloisGroup K) (x : ZMod N) :
    trivialRankOneGaloisRep K N σ x = x :=
  rfl

variable (K L : Type*) [Field K] [Field L] [Algebra K L]
variable [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
variable [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- Multiplication by the integral value of the quadratic character, reduced modulo `N`. -/
def quadraticCharacterEnd (N : ℕ) (σ : Field.absoluteGaloisGroup K) :
    Module.End (ZMod N) (ZMod N) :=
  LinearMap.lsmul (ZMod N) (ZMod N)
    ((quadraticCharacter K L (AlgebraicClosure K) σ : ℤ) : ZMod N)

@[simp]
theorem quadraticCharacterEnd_apply (N : ℕ) (σ : Field.absoluteGaloisGroup K)
    (x : ZMod N) :
    quadraticCharacterEnd K L N σ x =
      ((quadraticCharacter K L (AlgebraicClosure K) σ : ℤ) : ZMod N) * x :=
  rfl

/-- The scalar endomorphisms defined by a quadratic character form a monoid homomorphism. -/
def quadraticCharacterEndMonoidHom (N : ℕ) :
    Field.absoluteGaloisGroup K →* Module.End (ZMod N) (ZMod N) where
  toFun := quadraticCharacterEnd K L N
  map_one' := by
    apply LinearMap.ext
    intro x
    simp [quadraticCharacterEnd]
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    simp [quadraticCharacterEnd, Module.End.mul_apply, mul_assoc]

/-- The rank-one `ZMod N`-representation afforded by a quadratic extension. -/
def quadraticCharacterGaloisRep (N : ℕ) : GaloisRep K (ZMod N) (ZMod N) := by
  letI : TopologicalSpace (Module.End (ZMod N) (ZMod N)) :=
    moduleTopology (ZMod N) (Module.End (ZMod N) (ZMod N))
  letI : ContinuousMul (Module.End (ZMod N) (ZMod N)) :=
    ⟨IsModuleTopology.continuous_mul_of_finite
      (ZMod N) (Module.End (ZMod N) (ZMod N))⟩
  refine ContinuousMonoidHom.mk (quadraticCharacterEndMonoidHom K L N) ?_
  apply MonoidHom.continuous_of_isOpen_ker
  apply Subgroup.isOpen_mono _
    ((MonoidHom.continuous_iff_isOpen_ker.mp
      (quadraticCharacter_continuous K L (AlgebraicClosure K))))
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  apply LinearMap.ext
  intro x
  simp [quadraticCharacterEndMonoidHom, quadraticCharacterEnd, hσ]

@[simp]
theorem quadraticCharacterGaloisRep_apply (N : ℕ)
    (σ : Field.absoluteGaloisGroup K) (x : ZMod N) :
    quadraticCharacterGaloisRep (K := K) (L := L) N σ x =
      ((quadraticCharacter K L (AlgebraicClosure K) σ : ℤ) : ZMod N) * x :=
  rfl

/-- Every value of the quadratic rank-one representation has square one. -/
theorem quadraticCharacterGaloisRep_mul_self (N : ℕ)
    (σ : Field.absoluteGaloisGroup K) :
    quadraticCharacterGaloisRep (K := K) (L := L) N σ *
        quadraticCharacterGaloisRep (K := K) (L := L) N σ = 1 := by
  apply LinearMap.ext
  intro x
  rcases Int.units_eq_one_or (quadraticCharacter K L (AlgebraicClosure K) σ) with hχ | hχ
  · simp [quadraticCharacterGaloisRep_apply, Module.End.mul_apply, hχ]
  · simp [quadraticCharacterGaloisRep_apply, Module.End.mul_apply, hχ]

end
