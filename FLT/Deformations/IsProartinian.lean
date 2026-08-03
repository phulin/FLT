/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Kevin Buzzard, Ruben Van de Velde
-/
module

public import FLT.Patching.Utils.AdicTopology
public import FLT.Deformations.IsResidueAlgebra
public import Mathlib.Topology.Algebra.TopologicallyNilpotent
import FLT.Deformations.Lemmas
import Mathlib.CategoryTheory.Category.Init
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.Topology.Connected.Separation

/-!
# Proartinian topological rings

A topological ring is *proartinian* if it is linearly topologized, complete
and Hausdorff, and every open ideal is the open kernel of a continuous
homomorphism to a finite (Artinian) ring. We provide the basic API and
show that complete Noetherian local rings with finite residue field are
proartinian under their adic topology.
-/

@[expose] public section

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

variable (R) in
/-- A topological ring is proartinian if it is linearly topologized, complete hausdorff,
and all its discrete quotients are artinian.

This is also called the category of "pseudo-compact" rings in section 0 of Exp VII_B of SGA3. -/
class IsProartinian : Prop extends IsLinearTopology R R, T0Space R,
    letI := IsTopologicalAddGroup.rightUniformSpace R; CompleteSpace R where
  isArtinianRing_quotient (I : Ideal R) : IsOpen (X := R) I → IsArtinianRing (R ⧸ I)

attribute [instance low] IsProartinian.toIsLinearTopology
  IsProartinian.toT0Space IsProartinian.toCompleteSpace

lemma isProartinian_iff_isArtinianRing [DiscreteTopology R] :
    IsProartinian R ↔ IsArtinianRing R := by
  constructor <;> intro
  · have := IsProartinian.isArtinianRing_quotient (⊥ : Ideal R) (isOpen_discrete _)
    exact (RingEquiv.quotientBot R).surjective.isArtinianRing
  · exact ⟨fun I _ ↦ inferInstance⟩

instance [DiscreteTopology R] [IsArtinianRing R] : IsProartinian R := by
  rwa [isProartinian_iff_isArtinianRing]

instance [IsLocalRing R] [IsLocalRing.IsAdicTopology R] [IsNoetherianRing R] [CompactSpace R] :
    IsProartinian R where
  isArtinianRing_quotient I hI :=
    have : Finite (R ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
    inferInstance

section IsLocalRing

open Filter IsLocalRing

variable [IsLocalRing R] [IsLocalRing S]

lemma isOpen_maximalIdeal_of_isProartinian [IsProartinian R] :
    IsOpen (X := R) (maximalIdeal R) := by
  obtain ⟨I, hI, hI'⟩ := IsLinearTopology.exists_ideal_isMaximal_and_isOpen R
  exact (isMaximal_iff _).mp hI ▸ hI'

lemma exists_maximalIdeal_pow_le_of_isProartinian [IsProartinian R]
    (I : Ideal R) (hI : IsOpen (X := R) I) :
    ∃ n, maximalIdeal R ^ n ≤ I := by
  by_cases hI' : I = ⊤
  · exact ⟨1, by simp [hI']⟩
  have := IsProartinian.isArtinianRing_quotient I hI
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI'
  have : IsLocalRing (R ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R ⧸ I)
  rw [jacobson_eq_maximalIdeal _ bot_ne_top,
    ← IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective,
    ← Ideal.map_pow, Ideal.zero_eq_bot, ← le_bot_iff, Ideal.map_le_iff_le_comap,
    ← RingHom.ker, Ideal.mk_ker] at hn
  exact ⟨n, hn⟩

/-- Every element of the maximal ideal of a local pro-Artinian ring is topologically
nilpotent.  Indeed, every open ideal contains a power of the maximal ideal. -/
theorem isTopologicallyNilpotent_of_mem_maximalIdeal [IsProartinian R]
    {x : R} (hx : x ∈ maximalIdeal R) : IsTopologicallyNilpotent x := by
  simp only [IsTopologicallyNilpotent,
    atTop_basis.tendsto_iff IsLinearTopology.hasBasis_open_ideal, true_and]
  intro I hI
  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  exact ⟨m, fun n hn ↦ hm (Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n))⟩

lemma isContinuous_of_isProartinian_of_isLocalHom
    [IsLocalRing.IsAdicTopology R]
    (f : R →+* S) [IsProartinian S] [IsLocalHom f] : Continuous f := by
  apply continuous_of_continuousAt_zero
  simp only [ContinuousAt, map_zero]
  rw [(IsLocalRing.hasBasis_maximalIdeal_pow R).tendsto_iff
    (IsLinearTopology.hasBasis_open_ideal (R := S))]
  intro I hI
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  replace hn := (Ideal.pow_right_mono (((local_hom_TFAE f).out 0 2).mp ‹_›) n).trans hn
  rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap] at hn
  exact ⟨n, trivial, hn⟩

lemma isLocalHom_of_isContinuous_of_isProartinian
    [IsProartinian R] (f : R →+* S) [IsProartinian S] (h : Continuous f) : IsLocalHom f := by
  constructor
  intro a ha
  by_contra ha'
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_le_of_isProartinian ((maximalIdeal S).comap f)
    (isOpen_maximalIdeal_of_isProartinian.preimage h)
  refine hn (Ideal.pow_mem_pow ha' n) (by simpa using ha.pow n)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- If a local pro-Artinian residue algebra is quotiented by an open ideal, then the
resulting quotient is finite as a module over the quotient of the source by the pulled-back
ideal. The residue-field quotient is finite because the two rings have the same residue field;
Hopkins--Levitzki then lifts this through the Artinian target ring. -/
lemma moduleFinite_quotient_comap_of_isResidueAlgebra [IsProartinian S]
    [Algebra R S] [IsResidueAlgebra R S]
    (J : Ideal S) (hJ : IsOpen (X := S) (J : Set S)) :
    let I := J.comap (algebraMap R S)
    letI : Algebra (R ⧸ I) (S ⧸ J) :=
      Ideal.Quotient.algebraQuotientOfLEComap (le_refl I)
    Module.Finite (R ⧸ I) (S ⧸ J) := by
  dsimp only
  let I : Ideal R := J.comap (algebraMap R S)
  let : Algebra (R ⧸ I) (S ⧸ J) :=
    Ideal.Quotient.algebraQuotientOfLEComap (le_refl I)
  let : IsArtinianRing (S ⧸ J) := IsProartinian.isArtinianRing_quotient J hJ
  by_cases hJtop : J = ⊤
  · subst J
    let : Finite (S ⧸ (⊤ : Ideal S)) := inferInstance
    exact Module.Finite.of_finite
  · let : Nontrivial (S ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
    have hItop : I ≠ ⊤ := Ideal.comap_ne_top _ hJtop
    let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
    let : IsLocalRing (R ⧸ I) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    let : IsLocalRing (S ⧸ J) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    let : IsScalarTower R (R ⧸ I) (S ⧸ J) := inferInstance
    let : IsResidueAlgebra R (S ⧸ J) := inferInstance
    let : IsResidueAlgebra R (R ⧸ I) := inferInstance
    let : IsResidueAlgebra (R ⧸ I) (S ⧸ J) :=
      IsResidueAlgebra.of_restrictScalars (𝓞 := R) (A := R ⧸ I) (B := S ⧸ J)
    let : Module.Finite (R ⧸ I) (ResidueField (S ⧸ J)) :=
      Module.Finite.of_surjective (Algebra.linearMap _ _)
        (IsResidueAlgebra.algebraMap_surjective (R ⧸ I) (S ⧸ J))
    let : Module.Finite (R ⧸ I) ((S ⧸ J) ⧸ Ring.jacobson (S ⧸ J)) := by
      rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      change Module.Finite (R ⧸ I) (ResidueField (S ⧸ J))
      infer_instance
    exact IsSemiprimaryRing.finite_of_isArtinian (R ⧸ I) (S ⧸ J) (S ⧸ J)

end IsLocalRing
