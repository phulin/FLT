/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/

-- if I can get all imports as FLT.Mathlib then I can upstream
module

public import FLT.Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import FLT.Mathlib.LinearAlgebra.Countable
import FLT.Mathlib.RingTheory.DedekindDomain.AdicValuation
public import FLT.NumberField.Completion.Finite
import FLT.NumberField.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Finite Adele Ring

Material destined for Mathlib.
-/

@[expose] public section

/-

# The finite adele ring of a number field is locally compact.

-/
open scoped TensorProduct

universe u

open NumberField IsDedekindDomain RestrictedProduct

section Instances

variable (K : Type*) [Field K] [NumberField K]

open HeightOneSpectrum

/-- `𝔸ᶠ[K]` is notation for `FiniteAdeleRing (𝓞 K) K`. -/
scoped[Adele] notation:max "𝔸ᶠ[" K "]" =>
  IsDedekindDomain.FiniteAdeleRing (𝓞 K) K

open scoped Adele

namespace IsDedekindDomain.FiniteAdeleRing

open IsDedekindDomain HeightOneSpectrum RestrictedProduct in
instance : LocallyCompactSpace 𝔸ᶠ[K] :=
  haveI : Fact (∀ (i : HeightOneSpectrum (𝓞 K)),
      IsOpen (adicCompletionIntegers K i : Set (adicCompletion K i))) :=
    ⟨isOpenAdicCompletionIntegers K⟩
  inferInstanceAs <| LocallyCompactSpace (Πʳ _, [_, _])

instance : CompactSpace (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.1 <|
  isCompact_range RestrictedProduct.isEmbedding_structureMap.continuous

lemma isCompact_integralAdeles : IsCompact (X := 𝔸ᶠ[K]) (integralAdeles (𝓞 K) K) :=
  isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace (integralAdeles (𝓞 K) K)))

instance : T2Space (FiniteAdeleRing (𝓞 K) K) :=
  inferInstanceAs <| T2Space (Πʳ _, [_, _])

instance : SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) :=
  RestrictedProduct.secondCountableTopology (isOpenAdicCompletionIntegers K)

lemma HeightOneSpectrum.nonempty {R : Type*} [CommRing R] (hR : ¬ IsField R) [Nontrivial R] :
    Nonempty (HeightOneSpectrum R) := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  exact ⟨⟨I, inferInstance, by rintro rfl; exact hR (Ring.isField_iff_maximal_bot.mpr hI)⟩⟩

instance {R : Type*} [CommRing R] [Algebra.IsIntegral ℤ R] [FaithfulSMul ℤ R] :
    Nonempty (HeightOneSpectrum R) :=
  have := (FaithfulSMul.algebraMap_injective ℤ R).nontrivial
  HeightOneSpectrum.nonempty fun h ↦
    Int.not_isField
      (isField_of_isIntegral_of_isField (FaithfulSMul.algebraMap_injective ℤ R) h)

instance : Nontrivial (FiniteAdeleRing (𝓞 K) K) :=
  RingHom.domain_nontrivial (FiniteAdeleRing.evalAlgebraMap _ _
    (Nonempty.some inferInstance)).toRingHom

section GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The standard integral subgroup `GLₙ(𝒪ᵥ)` of `GLₙ(Kᵥ)`. -/
noncomputable abbrev generalLinearLocalFullLevel
    (v : HeightOneSpectrum (𝓞 K)) : Subgroup (GL n (v.adicCompletion K)) :=
  ((v.adicCompletionIntegers K).matrix (n := n)).units

/-- The restricted-product description of `GLₙ` over the finite adeles. -/
noncomputable def generalLinearRestrictedProduct :
    GL n 𝔸ᶠ[K] ≃ₜ*
      Πʳ (v : HeightOneSpectrum (𝓞 K)),
        [GL n (v.adicCompletion K), generalLinearLocalFullLevel K (n := n) v] :=
  ContinuousMulEquiv.restrictedProductMatrixUnits
    (isOpenAdicCompletionIntegers K)

/-- The standard maximal compact subgroup `∏ᵥ GLₙ(𝒪ᵥ)` of `GLₙ(𝔸ᶠ_K)`. -/
noncomputable def generalLinearMaximalCompact : Subgroup (GL n 𝔸ᶠ[K]) where
  carrier := {g | ∀ v, generalLinearRestrictedProduct K (n := n) g v ∈
    generalLinearLocalFullLevel K (n := n) v}
  one_mem' v := by
    rw [map_one]
    exact Subgroup.one_mem _
  mul_mem' {g h} hg hh v := by
    rw [map_mul]
    exact (generalLinearLocalFullLevel K (n := n) v).mul_mem (hg v) (hh v)
  inv_mem' {g} hg v := by
    rw [map_inv]
    exact (generalLinearLocalFullLevel K (n := n) v).inv_mem (hg v)

theorem generalLinearMaximalCompact.isOpen :
    IsOpen (X := GL n 𝔸ᶠ[K]) (generalLinearMaximalCompact K (n := n)) := by
  classical
  rw [← (generalLinearRestrictedProduct K (n := n)).toHomeomorph.symm.isOpen_preimage]
  change IsOpen {g : Πʳ (v : HeightOneSpectrum (𝓞 K)),
    [GL n (v.adicCompletion K), generalLinearLocalFullLevel K (n := n) v] |
      ∀ v, g v ∈ generalLinearLocalFullLevel K (n := n) v}
  exact RestrictedProduct.isOpen_forall_mem fun v ↦
    Submonoid.isOpen_units (isOpenAdicCompletionIntegers K v).matrix

theorem generalLinearMaximalCompact.isCompact :
    IsCompact (X := GL n 𝔸ᶠ[K]) (generalLinearMaximalCompact K (n := n)) := by
  classical
  rw [← (generalLinearRestrictedProduct K (n := n)).toHomeomorph.symm.isCompact_preimage]
  change IsCompact {g : Πʳ (v : HeightOneSpectrum (𝓞 K)),
    [GL n (v.adicCompletion K), generalLinearLocalFullLevel K (n := n) v] |
      ∀ v, g v ∈ generalLinearLocalFullLevel K (n := n) v}
  exact RestrictedProduct.isCompact_forall_mem_of_eventually_subset
    (fun v ↦ Submonoid.isOpen_units (isOpenAdicCompletionIntegers K v).matrix)
    (generalLinearLocalFullLevel K (n := n))
    (fun v ↦ Submonoid.units_isCompact
      (NumberField.isCompact_adicCompletionIntegers K v).matrix)
    (by simp)

end GeneralLinearGroup

end IsDedekindDomain.FiniteAdeleRing

end Instances
