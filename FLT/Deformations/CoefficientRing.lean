/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Mathlib.RingTheory.Unramified.LocalRing
public import FLT.Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.Module.ModuleTopology

import FLT.Deformations.Lemmas
import Mathlib.RingTheory.LocalRing.ResidueField.Instances

/-!
# Coefficient rings for deformation problems

This file constructs a finite free unramified coefficient ring over the `p`-adic integers with
a prescribed finite residue field.
-/

@[expose] public section

open IsLocalRing

namespace Deformation

universe u

variable {k : Type u} [Finite k] [Field k]
    {p : ℕ} [Fact p.Prime]
    [TopologicalSpace k] [DiscreteTopology k]
    [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]

set_option linter.style.haveILetI false

/-- A surjection from a local ring to a field identifies that field with the residue field. -/
noncomputable def residueFieldEquivOfSurjective
    (R : Type*) [CommRing R] [IsLocalRing R]
    (k : Type*) [Field k] (f : R →+* k) (hf : Function.Surjective f) :
    ResidueField R ≃+* k :=
  (Ideal.quotEquivOfEq (IsLocalRing.ker_eq_maximalIdeal f hf).symm).trans
    (RingHom.quotientKerEquivOfSurjective hf)

@[simp]
lemma residueFieldEquivOfSurjective_residue
    (R : Type*) [CommRing R] [IsLocalRing R]
    (k : Type*) [Field k] (f : R →+* k) (hf : Function.Surjective f) (r : R) :
    residueFieldEquivOfSurjective R k f hf (residue R r) = f r := rfl

/-- A finite field receiving a local map from `ℤ_[p]` admits an unramified
coefficient ring.  The ring is a finite free local domain over `ℤ_[p]`, its
residue map is the prescribed map to `k`, and it carries the finite-module
topology.  The construction first lifts `k / 𝔽_p` to an unramified DVR and
then universe-lifts that DVR so that it can serve as coefficients for a
representation on a `Type u` module. -/
theorem exists_unramified_coefficientRing :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k),
      ∃ (_ : IsLocalHom (algebraMap R k)) (e : ResidueField R ≃+* k),
        ∀ r, e (residue R r) = algebraMap R k r := by
  letI : Finite (ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) PadicInt.residueField.symm.toEquiv
  obtain ⟨L, hLf, hQpL, hLfin, hLsep, hZpL, hZpQpL, S, hScomm, hSdom, hSdvr,
      hZpS, hSfin, hSL, hZpSL, hSfrac, hSloc, _, ⟨e⟩⟩ :=
    exists_unramified_extension_of_residueField (R := ℤ_[p]) (K := ℚ_[p]) k
  letI : CommRing S := hScomm
  letI : IsDomain S := hSdom
  letI : IsDiscreteValuationRing S := hSdvr
  letI : Algebra ℤ_[p] S := hZpS
  letI : Module.Finite ℤ_[p] S := hSfin
  letI : IsLocalHom (algebraMap ℤ_[p] S) := hSloc
  letI : Field L := hLf
  letI : Algebra ℚ_[p] L := hQpL
  letI : Algebra ℤ_[p] L := hZpL
  letI : IsScalarTower ℤ_[p] ℚ_[p] L := hZpQpL
  letI : Algebra S L := hSL
  letI : IsScalarTower ℤ_[p] S L := hZpSL
  have hZpSinj : Function.Injective (algebraMap ℤ_[p] S) := by
    intro x y hxy
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    apply (algebraMap ℚ_[p] L).injective
    calc
      (algebraMap ℚ_[p] L) (algebraMap ℤ_[p] ℚ_[p] x) = algebraMap ℤ_[p] L x :=
        (IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L x).symm
      _ = (algebraMap S L) (algebraMap ℤ_[p] S x) :=
        IsScalarTower.algebraMap_apply ℤ_[p] S L x
      _ = (algebraMap S L) (algebraMap ℤ_[p] S y) := congrArg (algebraMap S L) hxy
      _ = algebraMap ℤ_[p] L y := (IsScalarTower.algebraMap_apply ℤ_[p] S L y).symm
      _ = (algebraMap ℚ_[p] L) (algebraMap ℤ_[p] ℚ_[p] y) :=
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] L y
  letI : Module.IsTorsionFree ℤ_[p] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hZpSinj
  letI : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  let R := ULift.{u} S
  letI : CommRing R := inferInstance
  letI : IsDomain R := (ULift.ringEquiv : R ≃+* S).isDomain
  letI : IsDiscreteValuationRing R :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (ULift.ringEquiv : R ≃+* S).symm
  letI : IsLocalRing R := (ULift.ringEquiv : R ≃+* S).symm.isLocalRing
  letI : Algebra ℤ_[p] R := inferInstance
  letI : Module.Finite ℤ_[p] R := inferInstance
  letI : Module.Free ℤ_[p] R := inferInstance
  letI : IsLocalHom (algebraMap ℤ_[p] R) :=
    isLocalHom_of_comp (algebraMap ℤ_[p] R)
      (ULift.algEquiv (R := ℤ_[p])).toRingHom
  letI : Algebra R k :=
    ((e.toRingEquiv.toRingHom.comp (residue S)).comp
      (ULift.ringEquiv : R ≃+* S).toRingHom).toAlgebra
  have hRksurj : Function.Surjective (algebraMap R k) :=
    e.surjective.comp
      (IsLocalRing.residue_surjective.comp (ULift.ringEquiv : R ≃+* S).surjective)
  letI : IsLocalHom (algebraMap R k) :=
    IsLocalHom.of_surjective _ hRksurj
  letI : IsScalarTower ℤ_[p] R k := IsScalarTower.of_algebraMap_eq fun x ↦ by
    symm
    change e (residue S (algebraMap ℤ_[p] S x)) = algebraMap ℤ_[p] k x
    calc
      _ = e (algebraMap (ResidueField ℤ_[p]) (ResidueField S) (residue ℤ_[p] x)) := by
        rw [ResidueField.algebraMap_residue]
      _ = algebraMap (ResidueField ℤ_[p]) k (residue ℤ_[p] x) := e.commutes _
      _ = algebraMap ℤ_[p] k x :=
        (IsScalarTower.algebraMap_apply ℤ_[p] (ResidueField ℤ_[p]) k x).symm
  letI : TopologicalSpace R := moduleTopology ℤ_[p] R
  letI : IsModuleTopology ℤ_[p] R := ⟨rfl⟩
  letI : IsTopologicalRing R := IsModuleTopology.isTopologicalRing ℤ_[p] R
  have hmaxOpen : IsOpen (X := ℤ_[p]) (maximalIdeal ℤ_[p] : Set ℤ_[p]) := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    have hopen : IsOpen {x : ℤ_[p] | ‖x‖ < (1 : ℝ)} :=
      isOpen_lt continuous_norm continuous_const
    convert hopen using 1
    ext x
    change (x ∈ Ideal.span {(p : ℤ_[p])}) ↔ ‖x‖ < 1
    rw [Ideal.mem_span_singleton, PadicInt.norm_lt_one_iff_dvd]
  have hker : RingHom.ker (algebraMap ℤ_[p] k) = maximalIdeal ℤ_[p] := by
    simpa only [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot] using
      (IsLocalRing.maximalIdeal_comap (algebraMap ℤ_[p] k))
  have hZpk : Continuous (algebraMap ℤ_[p] k) := by
    apply RingHom.continuous_iff_isOpen_ker.mpr
    rw [hker]
    exact hmaxOpen
  have hRk : Continuous (algebraMap R k) :=
    IsModuleTopology.continuous_of_ringHom (R := ℤ_[p]) (A := R) (B := k)
      (algebraMap R k) (by
        rw [show (algebraMap R k).comp (algebraMap ℤ_[p] R) = algebraMap ℤ_[p] k by
          ext x
          exact (IsScalarTower.algebraMap_apply ℤ_[p] R k x).symm]
        exact hZpk)
  letI : ContinuousSMul R k :=
    ⟨(hRk.comp continuous_fst).mul continuous_snd⟩
  let residueEquiv : ResidueField R ≃+* k :=
    residueFieldEquivOfSurjective R k (algebraMap R k) hRksurj
  exact ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, residueEquiv,
    residueFieldEquivOfSurjective_residue R k (algebraMap R k) hRksurj⟩


end Deformation
