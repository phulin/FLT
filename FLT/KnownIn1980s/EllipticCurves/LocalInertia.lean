/-
Copyright (c) 2026 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup
public import FLT.KnownIn1980s.EllipticCurves.MaybeMathlib
public import FLT.Mathlib.LinearAlgebra.Dimension.IsQuadraticExtension
public import FLT.Mathlib.RingTheory.Norm.Quotient
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

open NumberField IsLocalRing

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

/-- If inertia fixes one `n`-th root `r` of the Tate parameter `q`, it fixes every unit
whose class in `Ωˣ / q^ℤ` is killed by `n`.  Indeed, such a unit is a root of unity times an
integral power of `r`, and both factors are fixed. -/
theorem localInertia_fixed_unit_of_mk_pow_eq_one
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    [NeZero (n : IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v)
    (q r u : (AlgebraicClosure (v.adicCompletion K))ˣ)
    (hr : r ^ n = q)
    (hfixr : Units.map σ.toAlgHom.toRingHom.toMonoidHom r = r)
    (hu : (u : (AlgebraicClosure (v.adicCompletion K))ˣ ⧸ Subgroup.zpowers q) ^ n = 1) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom u = u := by
  obtain ⟨ζ, z, hζ, huz⟩ :=
    QuotientGroup.exists_pow_eq_one_mul_zpow_of_mk_pow_eq_one hr hu
  have hζfield : (ζ : AlgebraicClosure (v.adicCompletion K)) ^ n = 1 := by
    exact congrArg Units.val hζ
  have hfixζfield : σ (ζ : AlgebraicClosure (v.adicCompletion K)) = ζ :=
    localInertia_fixed_of_pow_eq_one v n σ hσ ζ hζfield
  have hfixζ : Units.map σ.toAlgHom.toRingHom.toMonoidHom ζ = ζ := by
    apply Units.ext
    exact hfixζfield
  rw [huz, map_mul, map_zpow, hfixζ, hfixr]

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

/-- A Kummer generator is fixed by inertia when the exponent of its uniformizer factor is
divisible by `n`.

Writing `q = π ^ (n * t) * u`, choose an `n`-th root `z` of the unit `u`.  The preceding
unit-root theorem fixes `z`, while `π ^ t` already belongs to the base field.  Their product is
therefore an inertia-fixed `n`-th root of `q`. -/
theorem exists_localInertia_fixed_pow_eq_of_eq_pow_mul_unit
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    [NeZero (n : IsLocalRing.ResidueField (v.adicCompletionIntegers K))]
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v)
    (q π : v.adicCompletionIntegers K) (m t : ℕ)
    (u : (v.adicCompletionIntegers K)ˣ)
    (hq : q = π ^ m * (u : v.adicCompletionIntegers K)) (hm : m = n * t) :
    ∃ r : AlgebraicClosure (v.adicCompletion K),
      r ^ n = algebraMap (v.adicCompletionIntegers K)
        (AlgebraicClosure (v.adicCompletion K)) q ∧ σ r = r := by
  let k := v.adicCompletion K
  let R := v.adicCompletionIntegers K
  let Ω := AlgebraicClosure k
  have hn0 : n ≠ 0 := by
    intro hn
    apply NeZero.ne (n : IsLocalRing.ResidueField R)
    simp [hn]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap R Ω (u : R)) (Nat.pos_of_ne_zero hn0)
  have hσz : σ z = z :=
    localInertia_fixed_of_pow_eq_algebraMap_unit v n σ hσ u z hz
  let r : Ω := algebraMap R Ω (π ^ t) * z
  refine ⟨r, ?_, ?_⟩
  · rw [show r = algebraMap R Ω (π ^ t) * z from rfl, mul_pow, hz, ← map_pow,
      ← map_mul, hq, hm]
    congr 2
    exact (pow_mul π t n).symm.trans <|
      congrArg (fun e : ℕ ↦ π ^ e) (Nat.mul_comm t n)
  · rw [show r = algebraMap R Ω (π ^ t) * z from rfl, map_mul, hσz]
    change σ (algebraMap R Ω (π ^ t)) * z = _
    rw [IsScalarTower.algebraMap_apply R k Ω, σ.commutes]

/-- Local inertia fixes an integral generator of an unramified quadratic extension.

The generator satisfies `X² - tX + n`, and its discriminant `t² - 4n` is a unit because its
residue is nonzero.  If inertia moved the generator, the generator and its conjugate would be
distinct roots with the same residue.  Their squared difference would then be the discriminant,
putting a unit in the maximal ideal of the integral closure, a contradiction. -/
theorem localInertia_fixed_of_unramified_quadratic_generator
    (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion K) L]
    [Algebra (v.adicCompletionIntegers K) L]
    [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
    (ι : L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K))
    (θ : L) (t n : v.adicCompletionIntegers K)
    (hθint : _root_.IsIntegral (v.adicCompletionIntegers K) θ)
    (htr : Algebra.trace (v.adicCompletion K) L θ =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) t)
    (hnr : Algebra.norm (v.adicCompletion K) θ =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) n)
    (hD : residue (v.adicCompletionIntegers K) (t ^ 2 - 4 * n) ≠ 0)
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v) :
    σ (ι θ) = ι θ := by
  let k := v.adicCompletion K
  let R := v.adicCompletionIntegers K
  let Ω := AlgebraicClosure k
  let S := IntegralClosure R Ω
  let z : Ω := ι θ
  have hzint : _root_.IsIntegral R z := by
    exact hθint.map (ι.restrictScalars R)
  let z0 : S := ⟨z, hzint⟩
  have hθpoly := sq_sub_trace_mul_self_add_norm
    (Algebra.IsQuadraticExtension.finrank_eq_two k L) θ
  rw [htr, hnr] at hθpoly
  have hzpoly : z ^ 2 - algebraMap R Ω t * z + algebraMap R Ω n = 0 := by
    have hzpoly' := congrArg ι hθpoly
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hzpoly'
    rw [ι.commutes (algebraMap R k t), ι.commutes (algebraMap R k n)] at hzpoly'
    simpa only [z, IsScalarTower.algebraMap_apply R k Ω] using hzpoly'
  have hσzpoly :
      (σ z) ^ 2 - algebraMap R Ω t * σ z + algebraMap R Ω n = 0 := by
    have hroot := congrArg σ hzpoly
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hroot
    have hfixcoeff (r : R) : σ (algebraMap R Ω r) = algebraMap R Ω r := by
      rw [IsScalarTower.algebraMap_apply R k Ω, σ.commutes]
    simpa only [hfixcoeff] using hroot
  by_contra hne
  have hsum : σ z + z = algebraMap R Ω t := by
    have hprod : (σ z - z) * (σ z + z - algebraMap R Ω t) = 0 := by
      linear_combination hσzpoly - hzpoly
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne))
  have hsqΩ : (σ z - z) ^ 2 = algebraMap R Ω (t ^ 2 - 4 * n) := by
    have hmul : σ z * z = algebraMap R Ω n := by
      linear_combination (σ z) * hsum - hσzpoly
    simp only [map_sub, map_pow, map_mul, map_ofNat]
    calc
      (σ z - z) ^ 2 = (σ z + z) ^ 2 - 4 * (σ z * z) := by ring
      _ = (algebraMap R Ω t) ^ 2 - 4 * (σ z * z) := by rw [hsum]
      _ = (algebraMap R Ω t) ^ 2 - 4 * algebraMap R Ω n := by rw [hmul]
  have hmem : (σ • z0) - z0 ∈ maximalIdeal S := hσ z0
  have hsqS : ((σ • z0) - z0) ^ 2 = algebraMap R S (t ^ 2 - 4 * n) := by
    apply Subtype.ext
    exact hsqΩ
  have hpowmem : ((σ • z0) - z0) ^ 2 ∈ maximalIdeal S :=
    (maximalIdeal S).pow_mem_of_mem hmem 2 (by norm_num)
  have hunitR : IsUnit (t ^ 2 - 4 * n) :=
    (residue_ne_zero_iff_isUnit _).mp hD
  have hunitS : IsUnit (algebraMap R S (t ^ 2 - 4 * n)) :=
    hunitR.map (algebraMap R S)
  exact (notMem_maximalIdeal.mpr hunitS) (hsqS ▸ hpowmem)

/-- Every element of an unramified quadratic extension is fixed by local inertia.  Once the
integral generator is fixed, this follows by writing each element in the basis `1, θ`; the
non-base-field hypothesis guarantees that `1, θ` is a basis of the quadratic extension. -/
theorem localInertia_fixed_on_unramified_quadratic_extension
    (v : HeightOneSpectrum (𝓞 K))
    (L : Type*) [Field L] [Algebra (v.adicCompletion K) L]
    [Algebra.IsQuadraticExtension (v.adicCompletion K) L]
    [Algebra (v.adicCompletionIntegers K) L]
    [IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) L]
    (ι : L →ₐ[v.adicCompletion K] AlgebraicClosure (v.adicCompletion K))
    (θ : L) (t n : v.adicCompletionIntegers K)
    (hθint : _root_.IsIntegral (v.adicCompletionIntegers K) θ)
    (hθ : θ ∉ Set.range (algebraMap (v.adicCompletion K) L))
    (htr : Algebra.trace (v.adicCompletion K) L θ =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) t)
    (hnr : Algebra.norm (v.adicCompletion K) θ =
      algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) n)
    (hD : residue (v.adicCompletionIntegers K) (t ^ 2 - 4 * n) ≠ 0)
    (σ : Γ(v.adicCompletion K)) (hσ : σ ∈ localInertiaGroup v) :
    ∀ x : L, σ (ι x) = ι x := by
  have hfixθ := localInertia_fixed_of_unramified_quadratic_generator
    v L ι θ t n hθint htr hnr hD σ hσ
  intro x
  by_cases hx : x ∈ Set.range (algebraMap (v.adicCompletion K) L)
  · obtain ⟨a, rfl⟩ := hx
    rw [ι.commutes, σ.commutes]
  · obtain ⟨a, b, _ha, hx⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
        (v.adicCompletion K) L hθ hx
    rw [hx]
    simp only [map_add, map_mul, ι.commutes, σ.commutes, hfixθ]

end IsDedekindDomain.HeightOneSpectrum
