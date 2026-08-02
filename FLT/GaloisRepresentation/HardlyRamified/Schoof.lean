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

/-- The finite etale `ℚ`-algebra attached to the underlying finite Galois set of `rho`.
It consists of the Galois-equivariant functions from the representation space to
`AlgebraicClosure ℚ`. -/
abbrev GaloisRep.GenericEtaleAlgebra
    {A W : Type} [CommRing A] [TopologicalSpace A]
    [AddCommGroup W] [Module A W] (rho : GaloisRep ℚ A W) :=
  rho.Space →[Γ ℚ] AlgebraicClosure ℚ

set_option backward.isDefEq.respectTransparency false in
/-- The generic coordinate algebra of a finite discrete Galois representation is finite
etale over `ℚ`. -/
theorem GaloisRep.genericEtaleAlgebra_isEtale
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    Algebra.Etale ℚ (GaloisRep.GenericEtaleAlgebra rho) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The tensor square of the generic coordinate algebra is again finite etale. -/
theorem GaloisRep.genericEtaleTensorSquare_isEtale
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    Algebra.Etale ℚ (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho) := by
  letI : Algebra.Etale ℚ (GaloisRep.GenericEtaleAlgebra rho) :=
    GaloisRep.genericEtaleAlgebra_isEtale rho
  letI : Algebra (GaloisRep.GenericEtaleAlgebra rho)
      (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
        GaloisRep.GenericEtaleAlgebra rho) := Algebra.TensorProduct.leftAlgebra
  exact Algebra.Etale.comp ℚ (GaloisRep.GenericEtaleAlgebra rho)
    (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho)

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation identifies the representation's underlying finite Galois set with the
geometric points of its generic coordinate algebra. -/
noncomputable def GaloisRep.genericEtalePointsEquiv
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    rho.Space ≃
      (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) :=
  Equiv.ofBijective
    (MulActionHom.evalAlgHom (Γ ℚ) ℚ rho.Space (AlgebraicClosure ℚ))
    (InfiniteGalois.evalAlgHom_bijective ℚ (AlgebraicClosure ℚ) rho.Space)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.genericEtalePointsEquiv_apply
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) (x : rho.Space) :
    GaloisRep.genericEtalePointsEquiv rho x =
      MulActionHom.evalAlgHom (Γ ℚ) ℚ rho.Space (AlgebraicClosure ℚ) x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation is Galois-equivariant in the forward direction. -/
theorem GaloisRep.genericEtalePointsEquiv_smul
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) (sigma : Γ ℚ) (x : rho.Space) :
    GaloisRep.genericEtalePointsEquiv rho (sigma • x) =
      sigma • GaloisRep.genericEtalePointsEquiv rho x := by
  exact (MulActionHom.evalAlgHom (Γ ℚ) ℚ rho.Space
    (AlgebraicClosure ℚ)).map_smul sigma x

set_option backward.isDefEq.respectTransparency false in
/-- The inverse evaluation bijection is Galois-equivariant. -/
theorem GaloisRep.genericEtalePointsEquiv_symm_smul
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) (sigma : Γ ℚ)
    (x : GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) :
    (GaloisRep.genericEtalePointsEquiv rho).symm (sigma • x) =
      sigma • (GaloisRep.genericEtalePointsEquiv rho).symm x := by
  apply (GaloisRep.genericEtalePointsEquiv rho).injective
  rw [Equiv.apply_symm_apply, GaloisRep.genericEtalePointsEquiv_apply,
    MulActionHom.map_smul]
  change sigma • x =
    sigma • GaloisRep.genericEtalePointsEquiv rho
      ((GaloisRep.genericEtalePointsEquiv rho).symm x)
  rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- The map on geometric points dual to addition on the representation space. -/
noncomputable def GaloisRep.genericEtaleAddPoints
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    ((GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
        GaloisRep.GenericEtaleAlgebra rho) →ₐ[ℚ] AlgebraicClosure ℚ) →[Γ ℚ]
      (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) where
  toFun q :=
    GaloisRep.genericEtalePointsEquiv rho
      ((GaloisRep.genericEtalePointsEquiv rho).symm
          (q.comp Algebra.TensorProduct.includeLeft) +
        (GaloisRep.genericEtalePointsEquiv rho).symm
          (q.comp Algebra.TensorProduct.includeRight))
  map_smul' sigma q := by
    have h_left :
        (sigma • q).comp Algebra.TensorProduct.includeLeft =
          sigma • (q.comp Algebra.TensorProduct.includeLeft) := by
      rfl
    have h_right :
        (sigma • q).comp Algebra.TensorProduct.includeRight =
          sigma • (q.comp Algebra.TensorProduct.includeRight) := by
      rfl
    rw [h_left, h_right,
      GaloisRep.genericEtalePointsEquiv_symm_smul,
      GaloisRep.genericEtalePointsEquiv_symm_smul, ← smul_add,
      GaloisRep.genericEtalePointsEquiv_smul]
    simp only [id_eq]

set_option backward.isDefEq.respectTransparency false in
/-- The map on geometric points dual to the zero element of the representation space. -/
noncomputable def GaloisRep.genericEtaleZeroPoints
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    (ℚ →ₐ[ℚ] AlgebraicClosure ℚ) →[Γ ℚ]
      (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) where
  toFun _ := GaloisRep.genericEtalePointsEquiv rho 0
  map_smul' sigma q := by
    rw [← GaloisRep.genericEtalePointsEquiv_smul]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- The map on geometric points dual to negation on the representation space. -/
noncomputable def GaloisRep.genericEtaleNegPoints
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) →[Γ ℚ]
      (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) where
  toFun q := GaloisRep.genericEtalePointsEquiv rho
    (- (GaloisRep.genericEtalePointsEquiv rho).symm q)
  map_smul' sigma q := by
    rw [GaloisRep.genericEtalePointsEquiv_symm_smul, ← smul_neg,
      GaloisRep.genericEtalePointsEquiv_smul]
    simp only [id_eq]

set_option backward.isDefEq.respectTransparency false in
/-- Comultiplication on the generic coordinate algebra, obtained by finite-etale full
faithfulness from addition on geometric points. -/
noncomputable def GaloisRep.genericEtaleComul
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ]
      (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
        GaloisRep.GenericEtaleAlgebra rho) := by
  letI : Algebra.Etale ℚ (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho) :=
    GaloisRep.genericEtaleTensorSquare_isEtale rho
  exact InfiniteGalois.algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho)
      (B := GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
        GaloisRep.GenericEtaleAlgebra rho) (GaloisRep.genericEtaleAddPoints rho)

set_option backward.isDefEq.respectTransparency false in
/-- Counit on the generic coordinate algebra, obtained from its zero geometric point. -/
noncomputable def GaloisRep.genericEtaleCounit
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] ℚ :=
  InfiniteGalois.algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho) (B := ℚ)
      (GaloisRep.genericEtaleZeroPoints rho)

set_option backward.isDefEq.respectTransparency false in
/-- Antipode on the generic coordinate algebra, obtained from negation on geometric points. -/
noncomputable def GaloisRep.genericEtaleAntipode
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ]
      GaloisRep.GenericEtaleAlgebra rho :=
  InfiniteGalois.algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho)
      (B := GaloisRep.GenericEtaleAlgebra rho) (GaloisRep.genericEtaleNegPoints rho)

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.comp_genericEtaleComul
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W)
    (q : (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho) →ₐ[ℚ] AlgebraicClosure ℚ) :
    q.comp (GaloisRep.genericEtaleComul rho) =
      GaloisRep.genericEtaleAddPoints rho q := by
  letI : Algebra.Etale ℚ (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho) :=
    GaloisRep.genericEtaleTensorSquare_isEtale rho
  exact InfiniteGalois.comp_algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho)
      (B := GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
        GaloisRep.GenericEtaleAlgebra rho) (GaloisRep.genericEtaleAddPoints rho) q

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.comp_genericEtaleCounit
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) (q : ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
    q.comp (GaloisRep.genericEtaleCounit rho) =
      GaloisRep.genericEtaleZeroPoints rho q := by
  exact InfiniteGalois.comp_algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho) (B := ℚ)
      (GaloisRep.genericEtaleZeroPoints rho) q

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.comp_genericEtaleAntipode
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W)
    (q : GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) :
    q.comp (GaloisRep.genericEtaleAntipode rho) =
      GaloisRep.genericEtaleNegPoints rho q := by
  exact InfiniteGalois.comp_algHomOfMulActionHom ℚ (AlgebraicClosure ℚ)
    (GaloisRep.GenericEtaleAlgebra rho)
      (B := GaloisRep.GenericEtaleAlgebra rho) (GaloisRep.genericEtaleNegPoints rho) q

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.genericEtaleAddPoints_symm
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W)
    (q : (GaloisRep.GenericEtaleAlgebra rho ⊗[ℚ]
      GaloisRep.GenericEtaleAlgebra rho) →ₐ[ℚ] AlgebraicClosure ℚ) :
    (GaloisRep.genericEtalePointsEquiv rho).symm
        (GaloisRep.genericEtaleAddPoints rho q) =
      (GaloisRep.genericEtalePointsEquiv rho).symm
          (q.comp Algebra.TensorProduct.includeLeft) +
        (GaloisRep.genericEtalePointsEquiv rho).symm
          (q.comp Algebra.TensorProduct.includeRight) := by
  exact (GaloisRep.genericEtalePointsEquiv rho).symm_apply_apply _

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.genericEtaleZeroPoints_symm
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) (q : ℚ →ₐ[ℚ] AlgebraicClosure ℚ) :
    (GaloisRep.genericEtalePointsEquiv rho).symm
        (GaloisRep.genericEtaleZeroPoints rho q) = 0 := by
  exact (GaloisRep.genericEtalePointsEquiv rho).symm_apply_apply 0

set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem GaloisRep.genericEtaleNegPoints_symm
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W)
    (q : GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) :
    (GaloisRep.genericEtalePointsEquiv rho).symm
        (GaloisRep.genericEtaleNegPoints rho q) =
      - (GaloisRep.genericEtalePointsEquiv rho).symm q := by
  exact (GaloisRep.genericEtalePointsEquiv rho).symm_apply_apply _

set_option backward.isDefEq.respectTransparency false in
/-- The counit obtained from the zero geometric point is a right counit for addition. -/
theorem GaloisRep.genericEtale_rTensor_counit
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    (Algebra.TensorProduct.map (GaloisRep.genericEtaleCounit rho)
      (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))).comp
        (GaloisRep.genericEtaleComul rho) =
      (Algebra.TensorProduct.lid ℚ
        (GaloisRep.GenericEtaleAlgebra rho)).symm.toAlgHom := by
  let E := GaloisRep.GenericEtaleAlgebra rho
  letI : Algebra.Etale ℚ E := GaloisRep.genericEtaleAlgebra_isEtale rho
  letI : Algebra.Etale ℚ (ℚ ⊗[ℚ] E) := Algebra.Etale.of_equiv
    (Algebra.TensorProduct.lid ℚ E).symm
  apply InfiniteGalois.algHom_ext_of_comp_eq ℚ (AlgebraicClosure ℚ) E
  intro q
  rw [← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul]
  apply (GaloisRep.genericEtalePointsEquiv rho).symm.injective
  rw [GaloisRep.genericEtaleAddPoints_symm]
  have h_left :
      ((q.comp (Algebra.TensorProduct.map (GaloisRep.genericEtaleCounit rho)
        (.id ℚ E))).comp Algebra.TensorProduct.includeLeft) =
        GaloisRep.genericEtaleZeroPoints rho
          (q.comp Algebra.TensorProduct.includeLeft) := by
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft,
      ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleCounit]
  have h_right :
      ((q.comp (Algebra.TensorProduct.map (GaloisRep.genericEtaleCounit rho)
        (.id ℚ E))).comp Algebra.TensorProduct.includeRight) =
        q.comp (Algebra.TensorProduct.lid ℚ E).symm.toAlgHom := by
    ext x
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one]
    change q (1 ⊗ₜ[ℚ] x) = q ((Algebra.TensorProduct.lid ℚ E).symm x)
    rw [Algebra.TensorProduct.lid_symm_apply]
  rw [h_left, h_right, GaloisRep.genericEtaleZeroPoints_symm, zero_add]

set_option backward.isDefEq.respectTransparency false in
/-- The counit obtained from the zero geometric point is a left counit for addition. -/
theorem GaloisRep.genericEtale_lTensor_counit
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Finite W]
    (rho : GaloisRep ℚ A W) :
    (Algebra.TensorProduct.map (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))
      (GaloisRep.genericEtaleCounit rho)).comp
        (GaloisRep.genericEtaleComul rho) =
      (Algebra.TensorProduct.rid ℚ ℚ
        (GaloisRep.GenericEtaleAlgebra rho)).symm.toAlgHom := by
  let E := GaloisRep.GenericEtaleAlgebra rho
  letI : Algebra.Etale ℚ E := GaloisRep.genericEtaleAlgebra_isEtale rho
  letI : Algebra.Etale ℚ (E ⊗[ℚ] ℚ) := Algebra.Etale.of_equiv
    (Algebra.TensorProduct.rid ℚ ℚ E).symm
  apply InfiniteGalois.algHom_ext_of_comp_eq ℚ (AlgebraicClosure ℚ) E
  intro q
  rw [← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul]
  apply (GaloisRep.genericEtalePointsEquiv rho).symm.injective
  rw [GaloisRep.genericEtaleAddPoints_symm]
  have h_left :
      ((q.comp (Algebra.TensorProduct.map (.id ℚ E)
        (GaloisRep.genericEtaleCounit rho))).comp
          Algebra.TensorProduct.includeLeft) =
        q.comp (Algebra.TensorProduct.rid ℚ ℚ E).symm.toAlgHom := by
    ext x
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul, map_one]
    change q (x ⊗ₜ[ℚ] 1) = q ((Algebra.TensorProduct.rid ℚ ℚ E).symm x)
    rw [Algebra.TensorProduct.rid_symm_apply]
  have h_right :
      ((q.comp (Algebra.TensorProduct.map (.id ℚ E)
        (GaloisRep.genericEtaleCounit rho))).comp
          Algebra.TensorProduct.includeRight) =
        GaloisRep.genericEtaleZeroPoints rho
          (q.comp Algebra.TensorProduct.includeRight) := by
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight,
      ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleCounit]
  rw [h_left, h_right, GaloisRep.genericEtaleZeroPoints_symm, add_zero]

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
