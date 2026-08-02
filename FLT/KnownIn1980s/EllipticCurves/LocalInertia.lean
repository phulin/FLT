/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!

# Elementary fixed-point lemmas for local inertia

This file records the prime-to-residue-characteristic part of the elementary Kummer
calculation used in the Tate-curve description of multiplicative reduction.  An inertia
element acts trivially on the residue field.  Consequently, a root of unity of order invertible
in the residue field is fixed: its quotient with its conjugate is both congruent to `1` and a
root of unity of invertible order.

-/

@[expose] public section

open NumberField

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- Local inertia fixes every root of unity whose order is nonzero in the residue field.

This is the elementary injectivity of prime-to-residue-characteristic roots of unity under
reduction.  It is stated for elements rather than `rootsOfUnity` so that it can be used directly
with Kummer generators. -/
theorem localInertia_fixed_of_pow_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    [NeZero (n : IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v)
    (z : AlgebraicClosure (v.adicCompletion K)) (hz : z ^ n = 1) :
    σ z = z := by
  let k := v.adicCompletion K
  let R := v.adicCompletionIntegers K
  let Ω := AlgebraicClosure k
  let S := IntegralClosure R Ω
  have hn0 : n ≠ 0 := by
    intro hn
    apply NeZero.ne (n : IsLocalRing.ResidueField R)
    simp [hn]
  have hzint : _root_.IsIntegral R z :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_one)
  let z0 : S := ⟨z, hzint⟩
  have hz0pow : z0 ^ n = 1 := by
    apply Subtype.ext
    exact hz
  have hz0unit : IsUnit z0 := IsUnit.of_pow_eq_one hz0pow hn0
  let u : Sˣ := hz0unit.unit
  have hu : (u : S) = z0 := hz0unit.unit_spec
  have hσzpow : (σ • z0) ^ n = 1 := by
    apply Subtype.ext
    change (σ z) ^ n = 1
    rw [← map_pow, hz, map_one]
  have huinvpow : (↑(u⁻¹) : S) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, inv_pow,
      show u ^ n = 1 by apply Units.ext; simpa [hu] using hz0pow, inv_one]
    rfl
  let y : S := (σ • z0) * (↑(u⁻¹) : S)
  have hypow : y ^ n = 1 := by
    rw [show y = (σ • z0) * (↑(u⁻¹) : S) from rfl, mul_pow, hσzpow,
      huinvpow, mul_one]
  have hymem : y - 1 ∈ IsLocalRing.maximalIdeal S := by
    have hdiff : σ • z0 - z0 ∈ IsLocalRing.maximalIdeal S := hσ z0
    have hy : y - 1 = (σ • z0 - z0) * (↑(u⁻¹) : S) := by
      simp [y, sub_mul, ← hu]
    rw [hy]
    exact (IsLocalRing.maximalIdeal S).mul_mem_right _ hdiff
  have hnR : IsUnit (n : R) := IsLocalRing.notMem_maximalIdeal.mp fun hn ↦ by
    apply NeZero.ne (n : IsLocalRing.ResidueField R)
    simpa using (IsLocalRing.residue_eq_zero_iff (n : R)).mpr hn
  have hnS : IsUnit (n : S) := by
    simpa only [map_natCast] using hnR.map (algebraMap R S)
  have hyone : y = 1 :=
    IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hnS hypow hymem
  have hfix : σ • z0 = z0 := calc
    σ • z0 = ((σ • z0) * (↑(u⁻¹) : S)) * (u : S) := by simp
    _ = y * (u : S) := rfl
    _ = 1 * (u : S) := by rw [hyone]
    _ = z0 := by simpa using hu
  exact congrArg Subtype.val hfix

/-- Local inertia fixes an `n`-th root of a unit of the base valuation ring when `n` is
nonzero in the residue field.

The root is integral and a unit.  Its conjugate has the same `n`-th power and the same
reduction, so tame Hensel uniqueness applies.  This is the unit-Kummer step in the standard
proof that the Frey representation is unramified at its bad odd primes. -/
theorem localInertia_fixed_of_pow_eq_algebraMap_unit
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    [NeZero (n : IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v)
    (u : (v.adicCompletionIntegers K)ˣ)
    (z : AlgebraicClosure (v.adicCompletion K))
    (hz : z ^ n = algebraMap (v.adicCompletionIntegers K)
      (AlgebraicClosure (v.adicCompletion K)) (u : v.adicCompletionIntegers K)) :
    σ z = z := by
  let k := v.adicCompletion K
  let R := v.adicCompletionIntegers K
  let Ω := AlgebraicClosure k
  let S := IntegralClosure R Ω
  have hn0 : n ≠ 0 := by
    intro hn
    apply NeZero.ne (n : IsLocalRing.ResidueField R)
    simp [hn]
  have hzint : _root_.IsIntegral R z :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hn0) (hz ▸ isIntegral_algebraMap)
  let z0 : S := ⟨z, hzint⟩
  have hz0pow : z0 ^ n = algebraMap R S (u : R) := by
    apply Subtype.ext
    change z ^ n = algebraMap R Ω (u : R)
    exact hz
  have hz0unit : IsUnit z0 := (isUnit_pow_iff hn0).mp <| by
    rw [hz0pow]
    exact u.isUnit.map (algebraMap R S)
  have hσzpow : (σ • z0) ^ n = z0 ^ n := by
    apply Subtype.ext
    change (σ z) ^ n = z ^ n
    rw [← map_pow, hz]
    change σ (algebraMap R Ω (u : R)) = algebraMap R Ω (u : R)
    rw [IsScalarTower.algebraMap_apply R k Ω, σ.commutes]
  have hnR : IsUnit (n : R) := IsLocalRing.notMem_maximalIdeal.mp fun hn ↦ by
    apply NeZero.ne (n : IsLocalRing.ResidueField R)
    simpa using (IsLocalRing.residue_eq_zero_iff (n : R)).mpr hn
  have hnS : IsUnit (n : S) := by
    simpa only [map_natCast] using hnR.map (algebraMap R S)
  have hfix : σ • z0 = z0 :=
    IsLocalRing.eq_of_pow_eq_pow_of_isUnit_of_sub_mem_maximalIdeal
      hnS hz0unit hσzpow (hσ z0)
  exact congrArg Subtype.val hfix

end IsDedekindDomain.HeightOneSpectrum
