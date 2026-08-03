/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.UniversalParameters
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Dual.Lemmas

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

end Deformation
