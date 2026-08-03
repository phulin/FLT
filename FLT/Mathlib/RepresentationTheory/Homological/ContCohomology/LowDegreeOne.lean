/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic

/-!
# First continuous cohomology in terms of continuous crossed homomorphisms

This file gives a concrete degree-one interface to the homogeneous complex used to define
continuous group cohomology.  A homogeneous cocycle `F` is evaluated at `(1, g)`; invariance
recovers all its values from this function, and the homogeneous cocycle equation becomes

`c (g * h) = X.ρ g (c h) + c g`.

We retain the homogeneous cocycle as the bundled object.  This avoids imposing joint continuity
of the action, which `TopRep` deliberately does not assume, while still exposing precisely the
inhomogeneous formula needed in deformation theory.
-/

@[expose] public section

universe u

open CategoryTheory ContRepresentation TopRep

namespace ContinuousCohomology

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Degree-one continuous cocycles, using the kernel model of the homogeneous complex. -/
noncomputable abbrev Cocycles₁ (X : TopRep k G) : TopModuleCat k :=
  TopModuleCat.ker ((homogeneousCochains X).d 1 2)

/-- Evaluate a homogeneous degree-one cocycle at `(1, g)`. -/
def Cocycles₁.toInhomogeneous (X : TopRep k G) :
    Cocycles₁ X →ₗ[k] C(G, X) where
  toFun σ := σ.1.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
lemma Cocycles₁.toInhomogeneous_apply (X : TopRep k G) (σ : Cocycles₁ X) (g : G) :
    Cocycles₁.toInhomogeneous X σ g = σ.1.1 1 g := rfl

/-- Homogeneous invariance recovers every value from the inhomogeneous cocycle. -/
lemma Cocycles₁.eq_rho_toInhomogeneous (X : TopRep k G) (σ : Cocycles₁ X)
    (x y : G) :
    σ.1.1 x y = X.ρ x (Cocycles₁.toInhomogeneous X σ (x⁻¹ * y)) := by
  have hσ := congrArg (fun F : C(G, C(G, X)) ↦ F x y) (σ.1.2 x)
  simpa [ContRepresentation.coind₁_apply_apply] using hσ.symm

/-- Evaluation at `(1, -)` is injective on homogeneous degree-one cocycles. -/
lemma Cocycles₁.toInhomogeneous_injective (X : TopRep k G) :
    Function.Injective (Cocycles₁.toInhomogeneous X) := by
  intro σ τ h
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  apply ContinuousMap.ext
  intro y
  rw [Cocycles₁.eq_rho_toInhomogeneous X σ,
    Cocycles₁.eq_rho_toInhomogeneous X τ, h]

noncomputable instance (X : TopRep k G) : FunLike (Cocycles₁ X) G X where
  coe σ := Cocycles₁.toInhomogeneous X σ
  coe_injective := Cocycles₁.toInhomogeneous_injective X

@[simp]
lemma Cocycles₁.coe_apply (X : TopRep k G) (σ : Cocycles₁ X) (g : G) :
    σ g = σ.1.1 1 g := rfl

@[ext]
lemma Cocycles₁.ext (X : TopRep k G) {σ τ : Cocycles₁ X}
    (h : ∀ g, σ g = τ g) : σ = τ :=
  DFunLike.ext σ τ h

/-- The homogeneous kernel condition is the usual crossed-homomorphism identity. -/
lemma Cocycles₁.map_mul (X : TopRep k G) (σ : Cocycles₁ X) (g h : G) :
    σ (g * h) = X.ρ g (σ h) + σ g := by
  have hd := congrArg
    (fun F : (homogeneousCochains X).X 2 ↦ F.1 1 g (g * h))
    (LinearMap.mem_ker.mp σ.2)
  change σ.1.1 g (g * h) - σ.1.1 1 (g * h) + σ.1.1 1 g = 0 at hd
  rw [Cocycles₁.eq_rho_toInhomogeneous X σ g (g * h)] at hd
  simpa [sub_add_eq_add_sub, sub_eq_zero, eq_comm] using hd

@[simp]
lemma Cocycles₁.map_one (X : TopRep k G) (σ : Cocycles₁ X) : σ 1 = 0 := by
  have h := Cocycles₁.map_mul X σ 1 1
  simpa using h

@[simp]
lemma Cocycles₁.map_inv (X : TopRep k G) (σ : Cocycles₁ X) (g : G) :
    X.ρ g (σ g⁻¹) = -σ g := by
  rw [← add_eq_zero_iff_eq_neg, ← Cocycles₁.map_one X σ, ← mul_inv_cancel g,
    Cocycles₁.map_mul X σ]

/-- Degree-one continuous coboundaries inside the kernel model. -/
noncomputable def Coboundaries₁ (X : TopRep k G) : Submodule k (Cocycles₁ X) :=
  LinearMap.range (bdryKer X 1).hom

/-- The canonical map from continuous cocycles to first continuous cohomology. -/
noncomputable def H1π (X : TopRep k G) :
    Cocycles₁ X →L[k] continuousCohomology 1 X :=
  ((cohomologyIsoQuot X 1).inv.hom.comp (TopModuleCat.cokerπ (bdryKer X 1)).hom)

lemma H1π_surjective (X : TopRep k G) : Function.Surjective (H1π X) := by
  exact (cohomologyIsoQuot X 1).inv.hom.surjective.comp
    (TopModuleCat.cokerπ_surjective (bdryKer X 1))

lemma H1π_eq_zero_iff (X : TopRep k G) (σ : Cocycles₁ X) :
    H1π X σ = 0 ↔ σ ∈ Coboundaries₁ X := by
  rw [H1π, ContinuousLinearMap.comp_apply, ← map_zero (cohomologyIsoQuot X 1).inv.hom,
    (cohomologyIsoQuot X 1).inv.hom.injective.eq_iff]
  change Submodule.mkQ (LinearMap.range (bdryKer X 1).hom) σ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  rfl

/-- Every first continuous cohomology class has a continuous crossed-homomorphism
representative. -/
theorem H1_induction_on (X : TopRep k G) {P : continuousCohomology 1 X → Prop}
    (x : continuousCohomology 1 X) (h : ∀ σ : Cocycles₁ X, P (H1π X σ)) : P x := by
  obtain ⟨σ, rfl⟩ := H1π_surjective X x
  exact h σ

/-- Evaluating a homogeneous coboundary at `(1, g)` gives the difference of its endpoint
values. -/
lemma bdryKer_one_apply (X : TopRep k G) (a : (homogeneousCochains X).X 0) (g : G) :
    (bdryKer X 1 a : Cocycles₁ X) g = a.1 g - a.1 1 := by
  rfl

/-- Invariance rewrites the endpoint formula for a homogeneous coboundary as the usual
`g · a - a` formula. -/
lemma bdryKer_one_apply_eq_action_sub (X : TopRep k G)
    (a : (homogeneousCochains X).X 0) (g : G) :
    (bdryKer X 1 a : Cocycles₁ X) g = X.ρ g (a.1 1) - a.1 1 := by
  rw [bdryKer_one_apply]
  have ha := congrArg (fun f : C(G, X) ↦ f g) (a.2 g)
  simpa [ContRepresentation.coind₁_apply_apply] using congrArg (fun z ↦ z - a.1 1) ha.symm

end ContinuousCohomology
