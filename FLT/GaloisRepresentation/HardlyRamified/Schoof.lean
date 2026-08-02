/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs

import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Equiv

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

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev genericEtaleTensorCubeCommRing
    (E : Type) [CommRing E] [Algebra ℚ E] :
    CommRing (E ⊗[ℚ] (E ⊗[ℚ] E)) := by
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev genericEtaleTensorCubeLeftAlgebra
    (E : Type) [CommRing E] [Algebra ℚ E] :
    Algebra E (E ⊗[ℚ] (E ⊗[ℚ] E)) :=
  Algebra.TensorProduct.leftAlgebra

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev genericEtaleTensorCubeRatAlgebra
    (E : Type) [CommRing E] [Algebra ℚ E] :
    Algebra ℚ (E ⊗[ℚ] (E ⊗[ℚ] E)) := by
  infer_instance

set_option maxHeartbeats 1000000 in
-- Normalizing the three nested tensor-product algebra structures needs extra elaboration time.
set_option backward.isDefEq.respectTransparency false in
/-- The comultiplication obtained from addition on geometric points is coassociative. -/
theorem GaloisRep.genericEtale_coassoc
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ
      (GaloisRep.GenericEtaleAlgebra rho)
      (GaloisRep.GenericEtaleAlgebra rho)
      (GaloisRep.GenericEtaleAlgebra rho)).toAlgHom.comp
        ((Algebra.TensorProduct.map (GaloisRep.genericEtaleComul rho)
          (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))).comp
            (GaloisRep.genericEtaleComul rho)) =
      (Algebra.TensorProduct.map
        (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))
        (GaloisRep.genericEtaleComul rho)).comp
          (GaloisRep.genericEtaleComul rho) := by
  let E := GaloisRep.GenericEtaleAlgebra rho
  let lhs :=
    (Algebra.TensorProduct.assoc ℚ ℚ ℚ E E E).toAlgHom.comp
      ((Algebra.TensorProduct.map (GaloisRep.genericEtaleComul rho) (.id ℚ E)).comp
        (GaloisRep.genericEtaleComul rho))
  let rhs :=
    (Algebra.TensorProduct.map (.id ℚ E) (GaloisRep.genericEtaleComul rho)).comp
      (GaloisRep.genericEtaleComul rho)
  change lhs = rhs
  suffices H : ∀ q : _ →ₐ[ℚ] AlgebraicClosure ℚ,
      q.comp lhs = q.comp rhs by
    let T := E ⊗[ℚ] (E ⊗[ℚ] E)
    letI : CommRing T := genericEtaleTensorCubeCommRing E
    letI : Algebra.Etale ℚ E := GaloisRep.genericEtaleAlgebra_isEtale rho
    letI : Algebra.Etale ℚ (E ⊗[ℚ] E) :=
      GaloisRep.genericEtaleTensorSquare_isEtale rho
    letI : Algebra ℚ T := genericEtaleTensorCubeRatAlgebra E
    letI : Algebra E T := genericEtaleTensorCubeLeftAlgebra E
    letI : Algebra.Etale E T := Algebra.Etale.baseChange ℚ (E ⊗[ℚ] E) E
    letI : Algebra.Etale ℚ T := Algebra.Etale.comp ℚ E T
    exact InfiniteGalois.algHom_ext_of_comp_eq ℚ (AlgebraicClosure ℚ) E H
  intro q
  let assoc := (Algebra.TensorProduct.assoc ℚ ℚ ℚ E E E).toAlgHom
  let qAssocParts :=
    (Algebra.TensorProduct.liftEquiv (R := ℚ) (S := ℚ)
      (A := E ⊗[ℚ] E) (B := E) (C := AlgebraicClosure ℚ)).symm (q.comp assoc)
  let qParts :=
    (Algebra.TensorProduct.liftEquiv (R := ℚ) (S := ℚ)
      (A := E) (B := E ⊗[ℚ] E) (C := AlgebraicClosure ℚ)).symm q
  let q12 : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    qAssocParts.val.1
  let q23 : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    qParts.val.2
  have hq12 : q12 = (q.comp assoc).comp Algebra.TensorProduct.includeLeft := by
    rfl
  have hq23 : q23 = q.comp Algebra.TensorProduct.includeRight := by
    rfl
  let qL : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    (q.comp assoc).comp
      (Algebra.TensorProduct.map (GaloisRep.genericEtaleComul rho) (.id ℚ E))
  let qR : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    q.comp (Algebra.TensorProduct.map (.id ℚ E) (GaloisRep.genericEtaleComul rho))
  change qL.comp (GaloisRep.genericEtaleComul rho) =
    qR.comp (GaloisRep.genericEtaleComul rho)
  rw [GaloisRep.comp_genericEtaleComul, GaloisRep.comp_genericEtaleComul]
  apply (GaloisRep.genericEtalePointsEquiv rho).symm.injective
  rw [GaloisRep.genericEtaleAddPoints_symm,
    GaloisRep.genericEtaleAddPoints_symm]
  have hL_left : qL.comp Algebra.TensorProduct.includeLeft =
      GaloisRep.genericEtaleAddPoints rho q12 := by
    rw [hq12]
    dsimp only [qL]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeLeft,
      ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul]
  have hL_right : qL.comp Algebra.TensorProduct.includeRight =
      q23.comp Algebra.TensorProduct.includeRight := by
    rw [hq23]
    ext x
    simp only [qL, AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    change q (assoc ((1 ⊗ₜ[ℚ] 1) ⊗ₜ[ℚ] x)) =
      q (1 ⊗ₜ[ℚ] (1 ⊗ₜ[ℚ] x))
    dsimp only [assoc]
    rfl
  have hR_left : qR.comp Algebra.TensorProduct.includeLeft =
      q12.comp Algebra.TensorProduct.includeLeft := by
    rw [hq12]
    ext x
    simp only [qR, AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
    change q (x ⊗ₜ[ℚ] (1 ⊗ₜ[ℚ] 1)) =
      q (assoc ((x ⊗ₜ[ℚ] 1) ⊗ₜ[ℚ] 1))
    dsimp only [assoc]
    rfl
  have hR_right : qR.comp Algebra.TensorProduct.includeRight =
      GaloisRep.genericEtaleAddPoints rho q23 := by
    rw [hq23]
    dsimp only [qR]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.map_comp_includeRight,
      ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul]
  rw [hL_left, hL_right, hR_left, hR_right,
    GaloisRep.genericEtaleAddPoints_symm,
    GaloisRep.genericEtaleAddPoints_symm]
  have h12_right : q12.comp Algebra.TensorProduct.includeRight =
      q23.comp Algebra.TensorProduct.includeLeft := by
    rw [hq12, hq23]
    ext x
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeRight_apply,
      Algebra.TensorProduct.includeLeft_apply]
    change q (assoc ((1 ⊗ₜ[ℚ] x) ⊗ₜ[ℚ] 1)) =
      q (1 ⊗ₜ[ℚ] (x ⊗ₜ[ℚ] 1))
    dsimp only [assoc]
    rfl
  exact (add_assoc _ _ _).trans
    (congrArg
      (fun z =>
        (GaloisRep.genericEtalePointsEquiv rho).symm
            (q12.comp Algebra.TensorProduct.includeLeft) +
          (z + (GaloisRep.genericEtalePointsEquiv rho).symm
            (q23.comp Algebra.TensorProduct.includeRight)))
      (congrArg (GaloisRep.genericEtalePointsEquiv rho).symm h12_right))

set_option backward.isDefEq.respectTransparency false in
/-- The bialgebra structure on the generic coordinate algebra induced by addition and zero. -/
@[instance_reducible]
noncomputable def GaloisRep.genericEtaleBialgebra
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    Bialgebra ℚ (GaloisRep.GenericEtaleAlgebra rho) :=
  Bialgebra.ofAlgHom (GaloisRep.genericEtaleComul rho)
    (GaloisRep.genericEtaleCounit rho)
    (GaloisRep.genericEtale_coassoc rho)
    (GaloisRep.genericEtale_rTensor_counit rho)
    (GaloisRep.genericEtale_lTensor_counit rho)

set_option backward.isDefEq.respectTransparency false in
/-- Negation is a right convolution inverse to the identity on the generic coordinate algebra. -/
theorem GaloisRep.genericEtale_mul_antipode_rTensor_comul
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    letI := GaloisRep.genericEtaleBialgebra rho
    ((Algebra.TensorProduct.lift (GaloisRep.genericEtaleAntipode rho)
      (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))
      (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom ℚ (GaloisRep.GenericEtaleAlgebra rho))) =
      (Algebra.ofId ℚ (GaloisRep.GenericEtaleAlgebra rho)).comp
        (Bialgebra.counitAlgHom ℚ (GaloisRep.GenericEtaleAlgebra rho)) := by
  let E := GaloisRep.GenericEtaleAlgebra rho
  letI := GaloisRep.genericEtaleBialgebra rho
  change ((Algebra.TensorProduct.lift (GaloisRep.genericEtaleAntipode rho)
    (.id ℚ E) (fun _ _ => Commute.all _ _)).comp
      (GaloisRep.genericEtaleComul rho)) =
    (Algebra.ofId ℚ E).comp (GaloisRep.genericEtaleCounit rho)
  apply InfiniteGalois.algHom_ext_of_comp_eq ℚ (AlgebraicClosure ℚ) E
  intro q
  rw [← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul,
    ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleCounit]
  apply (GaloisRep.genericEtalePointsEquiv rho).symm.injective
  rw [GaloisRep.genericEtaleAddPoints_symm,
    GaloisRep.genericEtaleZeroPoints_symm]
  let qT : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    q.comp (Algebra.TensorProduct.lift
      (GaloisRep.genericEtaleAntipode rho) (.id ℚ E)
        (fun _ _ => Commute.all _ _))
  have h_left : qT.comp Algebra.TensorProduct.includeLeft =
      GaloisRep.genericEtaleNegPoints rho q := by
    dsimp only [qT]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft,
      GaloisRep.comp_genericEtaleAntipode]
  have h_right : qT.comp Algebra.TensorProduct.includeRight = q := by
    dsimp only [qT]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight']
    simp
  rw [h_left, h_right, GaloisRep.genericEtaleNegPoints_symm]
  exact neg_add_cancel _

set_option backward.isDefEq.respectTransparency false in
/-- Negation is a left convolution inverse to the identity on the generic coordinate algebra. -/
theorem GaloisRep.genericEtale_mul_antipode_lTensor_comul
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    letI := GaloisRep.genericEtaleBialgebra rho
    ((Algebra.TensorProduct.lift
      (.id ℚ (GaloisRep.GenericEtaleAlgebra rho))
      (GaloisRep.genericEtaleAntipode rho)
      (fun _ _ => Commute.all _ _)).comp
        (Bialgebra.comulAlgHom ℚ (GaloisRep.GenericEtaleAlgebra rho))) =
      (Algebra.ofId ℚ (GaloisRep.GenericEtaleAlgebra rho)).comp
        (Bialgebra.counitAlgHom ℚ (GaloisRep.GenericEtaleAlgebra rho)) := by
  let E := GaloisRep.GenericEtaleAlgebra rho
  letI := GaloisRep.genericEtaleBialgebra rho
  change ((Algebra.TensorProduct.lift (.id ℚ E)
    (GaloisRep.genericEtaleAntipode rho) (fun _ _ => Commute.all _ _)).comp
      (GaloisRep.genericEtaleComul rho)) =
    (Algebra.ofId ℚ E).comp (GaloisRep.genericEtaleCounit rho)
  apply InfiniteGalois.algHom_ext_of_comp_eq ℚ (AlgebraicClosure ℚ) E
  intro q
  rw [← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleComul,
    ← AlgHom.comp_assoc, GaloisRep.comp_genericEtaleCounit]
  apply (GaloisRep.genericEtalePointsEquiv rho).symm.injective
  rw [GaloisRep.genericEtaleAddPoints_symm,
    GaloisRep.genericEtaleZeroPoints_symm]
  let qT : (E ⊗[ℚ] E) →ₐ[ℚ] AlgebraicClosure ℚ :=
    q.comp (Algebra.TensorProduct.lift (.id ℚ E)
      (GaloisRep.genericEtaleAntipode rho)
        (fun _ _ => Commute.all _ _))
  have h_left : qT.comp Algebra.TensorProduct.includeLeft = q := by
    dsimp only [qT]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeLeft]
    simp
  have h_right : qT.comp Algebra.TensorProduct.includeRight =
      GaloisRep.genericEtaleNegPoints rho q := by
    dsimp only [qT]
    rw [AlgHom.comp_assoc, Algebra.TensorProduct.lift_comp_includeRight',
      GaloisRep.comp_genericEtaleAntipode]
  rw [h_left, h_right, GaloisRep.genericEtaleNegPoints_symm]
  exact add_neg_cancel _

set_option backward.isDefEq.respectTransparency false in
/-- The Hopf-algebra structure on the generic coordinate algebra of a finite Galois module. -/
@[instance_reducible]
noncomputable def GaloisRep.genericEtaleHopfAlgebra
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    HopfAlgebra ℚ (GaloisRep.GenericEtaleAlgebra rho) := by
  letI := GaloisRep.genericEtaleBialgebra rho
  exact HopfAlgebra.ofAlgHom (GaloisRep.genericEtaleAntipode rho)
    (GaloisRep.genericEtale_mul_antipode_rTensor_comul rho)
    (GaloisRep.genericEtale_mul_antipode_lTensor_comul rho)

set_option backward.isDefEq.respectTransparency false in
/-- Convolution of geometric points agrees with the addition map used to define the
generic comultiplication. -/
theorem GaloisRep.genericEtale_convMul
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W)
    (q₁ q₂ : WithConv (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ]
      AlgebraicClosure ℚ)) :
    letI := GaloisRep.genericEtaleBialgebra rho
    (q₁ * q₂).ofConv = GaloisRep.genericEtaleAddPoints rho
      (Algebra.TensorProduct.lift q₁.ofConv q₂.ofConv
        (fun _ _ => Commute.all _ _)) := by
  letI := GaloisRep.genericEtaleBialgebra rho
  rw [AlgHom.convMul_def]
  change ((Algebra.TensorProduct.lmul' ℚ).comp
      (Algebra.TensorProduct.map q₁.ofConv q₂.ofConv)).comp
        (GaloisRep.genericEtaleComul rho) = _
  rw [Algebra.TensorProduct.lmul'_comp_map,
    GaloisRep.comp_genericEtaleComul]

set_option backward.isDefEq.respectTransparency false in
/-- The additive group of geometric points of the generic Hopf algebra is the original
finite Galois module. -/
noncomputable def GaloisRep.genericEtalePointsAddEquiv
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) :
    letI := GaloisRep.genericEtaleHopfAlgebra rho
    Additive (WithConv (GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ]
      AlgebraicClosure ℚ)) ≃+ rho.Space := by
  letI := GaloisRep.genericEtaleHopfAlgebra rho
  exact
    { toFun := fun q => (GaloisRep.genericEtalePointsEquiv rho).symm q.toMul.ofConv
      invFun := fun x => Additive.ofMul
        (WithConv.toConv (GaloisRep.genericEtalePointsEquiv rho x))
      left_inv := fun q => by
        apply Additive.toMul.injective
        apply WithConv.ofConv_injective
        exact (GaloisRep.genericEtalePointsEquiv rho).apply_symm_apply q.toMul.ofConv
      right_inv := fun x => (GaloisRep.genericEtalePointsEquiv rho).symm_apply_apply x
      map_add' := fun q₁ q₂ => by
        change (GaloisRep.genericEtalePointsEquiv rho).symm
            ((q₁.toMul * q₂.toMul).ofConv) =
          (GaloisRep.genericEtalePointsEquiv rho).symm q₁.toMul.ofConv +
            (GaloisRep.genericEtalePointsEquiv rho).symm q₂.toMul.ofConv
        rw [GaloisRep.genericEtale_convMul,
          GaloisRep.genericEtaleAddPoints_symm]
        simp }

set_option backward.isDefEq.respectTransparency false in
/-- The additive identification of generic geometric points is Galois-equivariant. -/
theorem GaloisRep.genericEtalePointsAddEquiv_smul
    {R W : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [DiscreteTopology R] [AddCommGroup W] [Module R W] [Finite W]
    (rho : GaloisRep ℚ R W) (sigma : Γ ℚ)
    (q : GaloisRep.GenericEtaleAlgebra rho →ₐ[ℚ] AlgebraicClosure ℚ) :
    letI := GaloisRep.genericEtaleHopfAlgebra rho
    GaloisRep.genericEtalePointsAddEquiv rho
        (Additive.ofMul (WithConv.toConv (sigma.toAlgHom.comp q))) =
      rho sigma (GaloisRep.genericEtalePointsAddEquiv rho
        (Additive.ofMul (WithConv.toConv q))) := by
  letI := GaloisRep.genericEtaleHopfAlgebra rho
  change (GaloisRep.genericEtalePointsEquiv rho).symm (sigma • q) =
    sigma • (GaloisRep.genericEtalePointsEquiv rho).symm q
  exact GaloisRep.genericEtalePointsEquiv_symm_smul rho sigma q

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
    (e : Additive (WithConv
      (ℚ ⊗[SchoofThreeBase] G →ₐ[ℚ] AlgebraicClosure ℚ)) →+ W),
    Function.Bijective e ∧
      ∀ (sigma : Γ ℚ) (x : Additive (WithConv
        (ℚ ⊗[SchoofThreeBase] G →ₐ[ℚ] AlgebraicClosure ℚ))),
        e (Additive.ofMul (WithConv.toConv
          (sigma.toAlgHom.comp x.toMul.ofConv))) = rho sigma (e x)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def precompBialgEquivPoints
    {R A B C : Type*} [CommSemiring R] [CommSemiring A] [CommSemiring B]
    [CommSemiring C] [Bialgebra R A] [Bialgebra R B] [Algebra R C]
    (e : A ≃ₐc[R] B) :
    Additive (WithConv (A →ₐ[R] C)) ≃+ Additive (WithConv (B →ₐ[R] C)) where
  toFun q := Additive.ofMul (WithConv.toConv
    (q.toMul.ofConv.comp e.symm.toAlgEquiv.toAlgHom))
  invFun q := Additive.ofMul (WithConv.toConv
    (q.toMul.ofConv.comp e.toAlgEquiv.toAlgHom))
  left_inv q := by
    apply Additive.toMul.injective
    apply WithConv.ofConv_injective
    change (q.toMul.ofConv.comp e.symm.toAlgEquiv.toAlgHom).comp
      e.toAlgEquiv.toAlgHom = q.toMul.ofConv
    rw [AlgHom.comp_assoc, show
      e.symm.toAlgEquiv.toAlgHom.comp e.toAlgEquiv.toAlgHom = .id R A by
        exact congrArg BialgHom.toAlgHom (BialgEquiv.symm_comp e)]
    simp
  right_inv q := by
    apply Additive.toMul.injective
    apply WithConv.ofConv_injective
    change (q.toMul.ofConv.comp e.toAlgEquiv.toAlgHom).comp
      e.symm.toAlgEquiv.toAlgHom = q.toMul.ofConv
    rw [AlgHom.comp_assoc, show
      e.toAlgEquiv.toAlgHom.comp e.symm.toAlgEquiv.toAlgHom = .id R B by
        exact congrArg BialgHom.toAlgHom (BialgEquiv.comp_symm e)]
    simp
  map_add' q₁ q₂ := by
    apply Additive.toMul.injective
    apply WithConv.ofConv_injective
    exact AlgHom.convMul_comp_bialgHom_distrib q₁.toMul q₂.toMul e.symm.toBialgHom

/-- An integral Hopf order for the canonical generic coordinate algebra.  This isolates the
globalization step: the finite-flat Hopf algebra is over `ℤ[1/2]`, and its rational base change
is required to be the canonical generic bialgebra constructed from `rho`. -/
def GaloisRep.HasIntegralHopfOrderAwayTwo
    {A W : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [DiscreteTopology A] [AddCommGroup W] [Module A W] [Module.Finite A W]
    [Module.Free A W] [Finite W] (rho : GaloisRep ℚ A W) : Prop :=
  letI : Algebra SchoofThreeBase ℚ := schoofThreeBaseToRat.toAlgebra
  ∃ (G : Type) (_ : CommRing G) (_ : HopfAlgebra SchoofThreeBase G)
    (_ : Module.Flat SchoofThreeBase G) (_ : Module.Finite SchoofThreeBase G)
    (_ : Algebra.Etale ℚ (ℚ ⊗[SchoofThreeBase] G)),
    letI := GaloisRep.genericEtaleBialgebra rho
    Nonempty ((ℚ ⊗[SchoofThreeBase] G) ≃ₐc[ℚ]
      GaloisRep.GenericEtaleAlgebra rho)

/-- Global finite-flat gluing over the Dedekind ring `ℤ[1/2]`.  The generic finite etale
group scheme extends uniquely etale at primes away from `3`; the supplied finite-flat model
at `3` is glued to those models, and schematic closure transports the Hopf operations.

This is the classical local-to-global theory of finite flat commutative group schemes over a
Dedekind base (SGA 3, Exposés VIB and VIII, together with the finite-flat closure/gluing
theorems of Raynaud).  Only this pre-1990 geometric existence theorem is deferred here; the
canonical generic Hopf algebra and the recovery of its Galois module are formalized above and
below. -/
theorem GaloisRep.IsSchoofThreeGenericFiber.toIntegralHopfOrderAwayTwo
    {A W : Type} [Finite W] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    {rho : GaloisRep ℚ A W} (h : GaloisRep.IsSchoofThreeGenericFiber rho) :
    GaloisRep.HasIntegralHopfOrderAwayTwo rho := by
  knownin1980s

set_option backward.isDefEq.respectTransparency false in
/-- An integral Hopf order supplies the global finite-flat model, including the additive and
Galois-equivariant identification of its rational geometric points with the representation. -/
theorem GaloisRep.HasIntegralHopfOrderAwayTwo.toFiniteFlatModel
    {A W : Type} [Finite W] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    {rho : GaloisRep ℚ A W} (h : GaloisRep.HasIntegralHopfOrderAwayTwo rho) :
    GaloisRep.HasFiniteFlatModelAwayTwo rho := by
  letI : Algebra SchoofThreeBase ℚ := schoofThreeBaseToRat.toAlgebra
  rcases h with ⟨G, hG, hHopf, hFlat, hFinite, hEtale, ⟨b⟩⟩
  letI : CommRing G := hG
  letI : HopfAlgebra SchoofThreeBase G := hHopf
  letI : Module.Flat SchoofThreeBase G := hFlat
  letI : Module.Finite SchoofThreeBase G := hFinite
  letI : Algebra.Etale ℚ (ℚ ⊗[SchoofThreeBase] G) := hEtale
  letI := GaloisRep.genericEtaleHopfAlgebra rho
  let pointEquiv := (precompBialgEquivPoints b).trans
    (GaloisRep.genericEtalePointsAddEquiv rho)
  let e : Additive (WithConv
      (ℚ ⊗[SchoofThreeBase] G →ₐ[ℚ] AlgebraicClosure ℚ)) →+ W :=
    pointEquiv.toAddMonoidHom
  refine ⟨G, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, e, pointEquiv.bijective, ?_⟩
  intro sigma x
  change GaloisRep.genericEtalePointsAddEquiv rho
      (Additive.ofMul (WithConv.toConv
        ((sigma.toAlgHom.comp x.toMul.ofConv).comp
          b.symm.toAlgEquiv.toAlgHom))) =
    rho sigma (GaloisRep.genericEtalePointsAddEquiv rho
      (Additive.ofMul (WithConv.toConv
        (x.toMul.ofConv.comp b.symm.toAlgEquiv.toAlgHom))))
  rw [AlgHom.comp_assoc]
  exact GaloisRep.genericEtalePointsAddEquiv_smul rho sigma
    (x.toMul.ofConv.comp b.symm.toAlgEquiv.toAlgHom)

/-- A represented object of Schoof's `(2, 3)` category: the four arithmetic generic-fiber
conditions together with an actual global finite-flat model over `ℤ[1/2]`. -/
def GaloisRep.IsSchoofThreeObject
    {A W : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    (rho : GaloisRep ℚ A W) : Prop :=
  GaloisRep.IsSchoofThreeGenericFiber rho ∧
    GaloisRep.HasFiniteFlatModelAwayTwo rho

/-- The classical global gluing theorem upgrades the four generic-fiber conditions to an
actual object of Schoof's finite-flat category. -/
theorem GaloisRep.IsSchoofThreeGenericFiber.toSchoofThreeObject
    {A W : Type} [Finite W] [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A]
    [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Free A W]
    {rho : GaloisRep ℚ A W} (h : GaloisRep.IsSchoofThreeGenericFiber rho) :
    GaloisRep.IsSchoofThreeObject rho :=
  ⟨h, h.toIntegralHopfOrderAwayTwo.toFiniteFlatModel⟩

end GaloisRepresentation
