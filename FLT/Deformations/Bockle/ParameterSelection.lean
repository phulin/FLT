/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.UniversalParameters
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Selecting deformation parameters from cotangent functionals

A finite linearly independent family of linear functionals gives a surjective evaluation
map.  Choosing inverse images of the standard coordinate vectors produces a dual family.
For a relative cotangent space these vectors can then be lifted to actual elements of the
ring using `relativeCotangentDerivation_surjective`.
-/

@[expose] public section

universe u

namespace Deformation

section LinearAlgebra

variable {k V : Type u} [Field k] [AddCommGroup V] [Module k V]
/-- Over a finite field, a set-theoretic injection from a finite-dimensional vector space into
an arbitrary vector space forces the target to contain an independent family of the source
dimension.  The target need not itself be finite-dimensional. -/
theorem exists_linearIndependent_finrank_of_injective_over_finite_field
    [Finite k] {W : Type u} [AddCommGroup W] [Module k W] [Module.Finite k V]
    (f : V → W) (hf : Function.Injective f) :
    ∃ v : Fin (Module.finrank k V) → W, LinearIndependent k v := by
  classical
  by_cases hW : Module.Finite k W
  · letI : Module.Finite k W := hW
    letI : Finite W := Module.finite_of_finite k
    have hcard : Nat.card V ≤ Nat.card W :=
      Nat.card_le_card_of_injective f hf
    rw [Module.natCard_eq_pow_finrank (K := k) (V := V),
      Module.natCard_eq_pow_finrank (K := k) (V := W)] at hcard
    have hk : 1 < Nat.card k :=
      Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    exact exists_linearIndependent_of_le_finrank
      ((Nat.pow_le_pow_iff_right hk).mp hcard)
  · have hrank : Cardinal.aleph0 ≤ Module.rank k W := by
      apply not_lt.mp
      intro hlt
      exact hW ((Module.rank_lt_aleph0_iff).mp hlt)
    exact Module.le_rank_iff.mp (Cardinal.natCast_le_aleph0.trans hrank)


/-- Simultaneous evaluation against a finite family of linear functionals. -/
noncomputable def cotangentEvaluationMap {n : ℕ} (f : Fin n → V →ₗ[k] k) :
    V →ₗ[k] (Fin n → k) :=
  LinearMap.pi f

@[simp]
theorem cotangentEvaluationMap_apply {n : ℕ} (f : Fin n → V →ₗ[k] k)
    (x : V) (i : Fin n) :
    cotangentEvaluationMap f x i = f i x :=
  rfl

/-- Independent functionals can attain arbitrary simultaneous values. -/
theorem cotangentEvaluationMap_surjective_of_linearIndependent
    {n : ℕ} (f : Fin n → V →ₗ[k] k) (hf : LinearIndependent k f) :
    Function.Surjective (cotangentEvaluationMap f) := by
  rw [← LinearMap.dualMap_injective_iff]
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro g hg
    rw [LinearMap.mem_ker] at hg
    let b : Module.Basis (Fin n) k (Fin n → k) := Pi.basisFun k (Fin n)
    have hcomb :
        Fintype.linearCombination k f (fun i ↦ g (b i)) =
          (cotangentEvaluationMap f).dualMap g := by
      apply LinearMap.ext
      intro x
      calc
        Fintype.linearCombination k f (fun i ↦ g (b i)) x =
            ∑ i, f i x • g (b i) := by
              simp only [Fintype.linearCombination_apply, LinearMap.sum_apply,
                LinearMap.smul_apply, smul_eq_mul]
              apply Finset.sum_congr rfl
              intro i _
              exact mul_comm _ _
        _ = ∑ i, g (f i x • b i) := by
              apply Finset.sum_congr rfl
              intro i _
              rw [map_smul]
        _ = g (∑ i, f i x • b i) := by rw [map_sum]
        _ = g (cotangentEvaluationMap f x) := by
              congr 1
              rw [← b.sum_repr (cotangentEvaluationMap f x)]
              apply Finset.sum_congr rfl
              intro i _
              congr 1
        _ = (cotangentEvaluationMap f).dualMap g x := rfl
    have hcoeff : (fun i ↦ g (b i)) = 0 := by
      funext i
      apply (Fintype.linearIndependent_iff.mp hf (fun i ↦ g (b i)))
      · change Fintype.linearCombination k f (fun i ↦ g (b i)) = 0
        rw [hcomb, hg]
    apply b.ext
    intro i
    change g (b i) = 0
    exact congrFun hcoeff i
  · exact bot_le

/-- A vector family dual to a finite independent family of functionals. -/
noncomputable def cotangentDualVector {n : ℕ} (f : Fin n → V →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) : V :=
  Classical.choose
    (cotangentEvaluationMap_surjective_of_linearIndependent f hf (Pi.single j 1))

/-- The selected vectors have the Kronecker-delta evaluation matrix. -/
theorem cotangentDualVector_evaluation {n : ℕ} (f : Fin n → V →ₗ[k] k)
    (hf : LinearIndependent k f) (i j : Fin n) :
    f i (cotangentDualVector f hf j) = if i = j then 1 else 0 := by
  have h := congrFun
    (Classical.choose_spec
      (cotangentEvaluationMap_surjective_of_linearIndependent f hf (Pi.single j 1))) i
  simpa [cotangentDualVector, Pi.single_apply, eq_comm] using h

end LinearAlgebra

section RelativeCotangent

variable {R D k : Type u} [CommRing R] [CommRing D] [Field k]
  [Algebra R D] [Algebra R k]

/-- Lift the dual cotangent vectors to actual ring elements. -/
noncomputable def relativeCotangentParameter
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) : D :=
  Classical.choose
    (relativeCotangentDerivation_surjective aug hRk (cotangentDualVector f hf j))

/-- The differential of the selected ring element is the chosen dual cotangent vector. -/
theorem relativeCotangentDerivation_parameter
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) :
    relativeCotangentDerivation aug (relativeCotangentParameter aug hRk f hf j) =
      cotangentDualVector f hf j :=
  Classical.choose_spec
    (relativeCotangentDerivation_surjective aug hRk (cotangentDualVector f hf j))

/-- The selected ring parameters have the Kronecker-delta evaluation matrix. -/
theorem relativeCotangentParameter_evaluation
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (i j : Fin n) :
    f i (relativeCotangentDerivation aug
      (relativeCotangentParameter aug hRk f hf j)) =
        if i = j then 1 else 0 := by
  rw [relativeCotangentDerivation_parameter]
  exact cotangentDualVector_evaluation f hf i j

/-- Normalize a selected cotangent parameter to have zero augmentation.  Surjectivity of the
coefficient map lets us subtract a coefficient with the same residue; relative differentials
are unchanged because they vanish on coefficients. -/
noncomputable def normalizedRelativeCotangentParameter
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) : D :=
  let x := relativeCotangentParameter aug hRk f hf j
  x - algebraMap R D
    (Classical.choose (hRk (aug x)))

/-- The normalized parameter has zero residue at the chosen augmentation. -/
theorem normalizedRelativeCotangentParameter_augmentation
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) :
    aug (normalizedRelativeCotangentParameter aug hRk f hf j) = 0 := by
  rw [normalizedRelativeCotangentParameter, map_sub, aug.commutes]
  exact sub_eq_zero.mpr
    (Classical.choose_spec
      (hRk (aug (relativeCotangentParameter aug hRk f hf j)))).symm

/-- Normalization does not change the selected cotangent vector. -/
theorem relativeCotangentDerivation_normalizedParameter
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) :
    relativeCotangentDerivation aug
        (normalizedRelativeCotangentParameter aug hRk f hf j) =
      cotangentDualVector f hf j := by
  rw [normalizedRelativeCotangentParameter, map_sub, Derivation.map_algebraMap, sub_zero]
  exact relativeCotangentDerivation_parameter aug hRk f hf j

/-- Consequently the normalized parameters retain the Kronecker evaluation matrix. -/
theorem normalizedRelativeCotangentParameter_evaluation
    (aug : D →ₐ[R] k) (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (i j : Fin n) :
    f i (relativeCotangentDerivation aug
      (normalizedRelativeCotangentParameter aug hRk f hf j)) =
        if i = j then 1 else 0 := by
  rw [relativeCotangentDerivation_normalizedParameter]
  exact cotangentDualVector_evaluation f hf i j

section Local

variable [IsLocalRing D]

/-- For a surjective local augmentation to a field, normalized parameters lie in the
maximal ideal. -/
theorem normalizedRelativeCotangentParameter_mem_maximalIdeal
    (aug : D →ₐ[R] k) [IsLocalHom aug] (haug : Function.Surjective aug)
    (hRk : Function.Surjective (algebraMap R k))
    {n : ℕ} (f : Fin n → RelativeCotangentSpace aug →ₗ[k] k)
    (hf : LinearIndependent k f) (j : Fin n) :
    normalizedRelativeCotangentParameter aug hRk f hf j ∈
      IsLocalRing.maximalIdeal D := by
  rw [← IsLocalRing.ker_eq_maximalIdeal aug.toRingHom haug, RingHom.mem_ker]
  exact normalizedRelativeCotangentParameter_augmentation aug hRk f hf j

end Local

end RelativeCotangent


section UniversalParameters

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

variable (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [Finite (IsLocalRing.ResidueField R)]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable (K : Type u) [Field K] [NumberField K]
variable (rhoRes : (repnFunctor (Fin 2) (Γ K) R).obj .residueField)
variable [Representation.IsAbsolutelyIrreducible.{u} (toRepresentation rhoRes)]
variable [Module.Finite (ProartinianCat.residueFieldType R)
  (BockleTangentSpace (toRepresentation rhoRes))]
variable [NeZero (2 : ProartinianCat.residueFieldType R)]

local instance : Finite (ProartinianCat.residueFieldType R) :=
  inferInstanceAs (Finite (IsLocalRing.ResidueField R))

/-- Choose as many independent universal cotangent functionals as the dimension of the adjoint
tangent space.  No finite-dimensionality assumption on the cotangent space is needed. -/
noncomputable def bockleIndependentCotangentFunctional :
    Fin (BockleTangentParameterCount (toRepresentation rhoRes)) →
      RelativeCotangentSpace (unrestrictedUniversalAugmentation R K rhoRes) →ₗ[
        ProartinianCat.residueFieldType R] ProartinianCat.residueFieldType R :=
  Classical.choose
    (exists_linearIndependent_finrank_of_injective_over_finite_field
      (bockleTangentClassCotangentFunctional R K rhoRes)
      (bockleTangentClassCotangentFunctional_injective R K rhoRes))

/-- The selected universal cotangent functionals are linearly independent. -/
theorem bockleIndependentCotangentFunctional_linearIndependent :
    LinearIndependent (ProartinianCat.residueFieldType R)
      (bockleIndependentCotangentFunctional R K rhoRes) :=
  Classical.choose_spec
    (exists_linearIndependent_finrank_of_injective_over_finite_field
      (bockleTangentClassCotangentFunctional R K rhoRes)
      (bockleTangentClassCotangentFunctional_injective R K rhoRes))

/-- The canonical augmentation of the unrestricted universal ring is surjective. -/
theorem unrestrictedUniversalAugmentation_surjective :
    Function.Surjective (unrestrictedUniversalAugmentation R K rhoRes) :=
  ProartinianCat.toResidueField_surjective
    (unrestrictedUniversalRing R K (Fin 2) rhoRes)

/-- Universal-ring parameters dual to an independent family of adjoint tangent directions. -/
noncomputable def bockleUniversalParameter
    (j : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    unrestrictedUniversalRing R K (Fin 2) rhoRes :=
  normalizedRelativeCotangentParameter
    (unrestrictedUniversalAugmentation R K rhoRes)
    (IsLocalRing.residue_surjective (R := R))
    (bockleIndependentCotangentFunctional R K rhoRes)
    (bockleIndependentCotangentFunctional_linearIndependent R K rhoRes) j

/-- The selected universal parameters lie in the maximal ideal. -/
theorem bockleUniversalParameter_mem_maximalIdeal
    (j : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    bockleUniversalParameter R K rhoRes j ∈
      IsLocalRing.maximalIdeal (unrestrictedUniversalRing R K (Fin 2) rhoRes) := by
  let aug := unrestrictedUniversalAugmentation R K rhoRes
  have haug : Function.Surjective aug :=
    unrestrictedUniversalAugmentation_surjective R K rhoRes
  have hlocal : IsLocalHom aug.toRingHom :=
    IsLocalHom.of_surjective aug.toRingHom haug
  letI : IsLocalHom aug := ⟨hlocal.map_nonunit⟩
  exact normalizedRelativeCotangentParameter_mem_maximalIdeal
    aug haug (IsLocalRing.residue_surjective (R := R))
    (bockleIndependentCotangentFunctional R K rhoRes)
    (bockleIndependentCotangentFunctional_linearIndependent R K rhoRes) j

/-- Evaluation of the selected tangent functionals on the selected parameters is the
Kronecker delta. -/
theorem bockleUniversalParameter_evaluation
    (i j : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    bockleIndependentCotangentFunctional R K rhoRes i
        (relativeCotangentDerivation
          (unrestrictedUniversalAugmentation R K rhoRes)
          (bockleUniversalParameter R K rhoRes j)) =
      if i = j then 1 else 0 :=
  normalizedRelativeCotangentParameter_evaluation
    (unrestrictedUniversalAugmentation R K rhoRes)
    (IsLocalRing.residue_surjective (R := R))
    (bockleIndependentCotangentFunctional R K rhoRes)
    (bockleIndependentCotangentFunctional_linearIndependent R K rhoRes) i j

end UniversalParameters

end Deformation
