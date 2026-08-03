/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree

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
  TopModuleCat.ker ((homogeneousCochains X).d 1 (1 + 1))

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
  change σ.1.1 x y = (resolutionX X 0).ρ x (σ.1.1 1 (x⁻¹ * y))
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
  coe_injective := by
    intro σ τ h
    apply Cocycles₁.toInhomogeneous_injective X
    apply ContinuousMap.ext
    exact congrFun h

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
  have hd0 := σ.2
  rw [LinearMap.mem_ker] at hd0
  have hd0' := congrArg Subtype.val hd0
  have hd1 := (homogeneousCochains.d_apply X 1 σ.1).symm.trans hd0'
  change (d X 2).hom σ.1.1 = 0 at hd1
  have hd : (d X 2).hom σ.1.1 1 g (g * h) = 0 :=
    congrArg (fun F : resolutionX X 3 ↦ F 1 g (g * h)) hd1
  have hinner :
      (d X 1).hom (σ.1.1 1) g (g * h) = σ.1.1 1 (g * h) - σ.1.1 1 g := by
    calc
      (d X 1).hom (σ.1.1 1) g (g * h) =
          (σ.1.1 1 - (d X 0).hom (σ.1.1 1 g)) (g * h) := by
            exact congrArg (fun F : resolutionX X 1 ↦ F (g * h))
              (d_hom_succ_apply X 0 (σ.1.1 1) g)
      _ = σ.1.1 1 (g * h) - σ.1.1 1 g := by
        rw [d_hom_zero]
        rfl
  have houter :
      (d X 2).hom σ.1.1 1 g (g * h) =
        σ.1.1 g (g * h) - (d X 1).hom (σ.1.1 1) g (g * h) := by
    exact congrArg (fun F : resolutionX X 2 ↦ F g (g * h))
      (d_hom_succ_apply X 1 σ.1.1 1)
  have hcocycle :
      σ.1.1 g (g * h) - σ.1.1 1 (g * h) + σ.1.1 1 g = 0 := by
    calc
      σ.1.1 g (g * h) - σ.1.1 1 (g * h) + σ.1.1 1 g =
          σ.1.1 g (g * h) -
            (σ.1.1 1 (g * h) - σ.1.1 1 g) := by abel
      _ = σ.1.1 g (g * h) - (d X 1).hom (σ.1.1 1) g (g * h) := by rw [hinner]
      _ = (d X 2).hom σ.1.1 1 g (g * h) := houter.symm
      _ = 0 := hd
  rw [Cocycles₁.eq_rho_toInhomogeneous X σ g (g * h)] at hcocycle
  rw [inv_mul_cancel_left] at hcocycle
  change X.ρ g (σ h) - σ (g * h) + σ g = 0 at hcocycle
  symm
  calc
    X.ρ g (σ h) + σ g =
        (X.ρ g (σ h) - σ (g * h) + σ g) + σ (g * h) := by abel
    _ = 0 + σ (g * h) := congrArg (fun z ↦ z + σ (g * h)) hcocycle
    _ = σ (g * h) := zero_add _

@[simp]
lemma Cocycles₁.map_one (X : TopRep k G) (σ : Cocycles₁ X) : σ 1 = 0 := by
  have h := Cocycles₁.map_mul X σ 1 1
  simpa using h

@[simp]
lemma Cocycles₁.map_inv (X : TopRep k G) (σ : Cocycles₁ X) (g : G) :
    X.ρ g (σ g⁻¹) = -σ g := by
  rw [← add_eq_zero_iff_eq_neg, ← Cocycles₁.map_one X σ, ← mul_inv_cancel g,
    Cocycles₁.map_mul X σ]

/-- A degree-one continuous cocycle is a coboundary if it is the differential of a homogeneous
degree-zero cochain. -/
def IsCoboundary₁ (X : TopRep k G) (σ : Cocycles₁ X) : Prop :=
  ∃ a : (homogeneousCochains X).X 0, bdryKer X 1 a = σ

/-- The canonical map from continuous cocycles to first continuous cohomology. -/
noncomputable def H1π (X : TopRep k G) :
    Cocycles₁ X →L[k] continuousCohomology 1 X :=
  ((cohomologyIsoQuot X 1).inv.hom.comp (TopModuleCat.cokerπ (bdryKer X 1)).hom)

lemma H1π_surjective (X : TopRep k G) : Function.Surjective (H1π X) := by
  intro x
  obtain ⟨σ, hσ⟩ := TopModuleCat.cokerπ_surjective (bdryKer X 1)
    ((cohomologyIsoQuot X 1).hom x)
  refine ⟨σ, ?_⟩
  change (cohomologyIsoQuot X 1).inv (TopModuleCat.cokerπ (bdryKer X 1) σ) = x
  rw [hσ]
  simp

set_option maxHeartbeats 800000 in
-- Unfolding the concrete topological cokernel model across the comparison isomorphism is costly.
lemma H1π_eq_zero_iff (X : TopRep k G) (σ : Cocycles₁ X) :
    H1π X σ = 0 ↔ IsCoboundary₁ X σ := by
  constructor
  · intro h
    have h' := congrArg (cohomologyIsoQuot X 1).hom h
    have hq : TopModuleCat.cokerπ (bdryKer X 1) σ = 0 := by
      simpa [H1π] using h'
    obtain ⟨a, ha⟩ := (TopModuleCat.cokerπ_eq_zero_iff (bdryKer X 1) σ).1 hq
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    have hq : TopModuleCat.cokerπ (bdryKer X 1) (bdryKer X 1 a) = 0 :=
      (TopModuleCat.cokerπ_eq_zero_iff (bdryKer X 1) (bdryKer X 1 a)).2 ⟨a, rfl⟩
    change (cohomologyIsoQuot X 1).inv
      (TopModuleCat.cokerπ (bdryKer X 1) (bdryKer X 1 a)) = 0
    rw [hq, map_zero]

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
  have ha' : a.1 g = X.ρ g (a.1 1) := by
    change a.1 g = (resolutionX X 0).ρ g (a.1 1)
    simpa [ContRepresentation.coind₁_apply_apply] using ha.symm
  rw [ha']

end ContinuousCohomology
