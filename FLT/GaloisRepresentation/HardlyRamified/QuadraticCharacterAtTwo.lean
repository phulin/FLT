/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.GaloisRepresentation.QuadraticCharacter
public import FLT.KnownIn1980s.EllipticCurves.LocalInertia
public import Mathlib.NumberTheory.Padics.Complex

/-!
# Unramified quadratic characters at two

We connect the explicit unramified quadratic extensions used for multiplicative reduction to
the concrete inertia subgroup in the hardly-ramified condition.
-/

@[expose] public section

open IsLocalRing
open scoped NNReal
open ValuativeRel

namespace GaloisRepresentation

noncomputable section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 "K" => ℚ_[2]
local notation3 "Ω" => AlgebraicClosure K
local notation3 "R" => ℤ_[2]

/-- Elements integral in `ℚ₂` remain in the valuation ring of its algebraic closure. -/
lemma norm_algebraMap_integer_to_padicAlgCl_le_one (x : R) :
    ‖algebraMap K Ω (x : K)‖ ≤ 1 := by
  rw [PadicAlgCl.norm_extends]
  exact_mod_cast x.2

/-- The canonical inclusion of the integers of `ℚ₂` into `Z2bar`. -/
def integerToZ2bar : R →+* Z2bar where
  toFun x := ⟨algebraMap K Ω (x : K), by
    rw [Valuation.mem_valuationSubring_iff]
    change ‖algebraMap K Ω (x : K)‖₊ ≤ 1
    exact_mod_cast norm_algebraMap_integer_to_padicAlgCl_le_one x⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

@[simp]
theorem integerToZ2bar_coe (x : R) :
    ((integerToZ2bar x : Z2bar) : Ω) = algebraMap K Ω (x : K) :=
  rfl

/-- In a nonarchimedean normed field, a root of a monic quadratic whose remaining
coefficients have norm at most one also has norm at most one. -/
theorem norm_le_one_of_sq_sub_mul_add_eq_zero
    {F : Type*} [NormedField F] [IsUltrametricDist F] {a b z : F}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hz : z ^ 2 - a * z + b = 0) :
    ‖z‖ ≤ 1 := by
  by_contra hzle
  have hzgt : 1 < ‖z‖ := lt_of_not_ge hzle
  have heq : z ^ 2 = a * z - b := by linear_combination hz
  have hsub : ‖a * z - b‖ ≤ max ‖a * z‖ ‖b‖ := by
    simpa only [sub_eq_add_neg, norm_neg] using
      (IsUltrametricDist.norm_add_le_max (a * z) (-b))
  have haz : ‖a * z‖ ≤ ‖z‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg z) ha
  have hbz : ‖b‖ ≤ ‖z‖ := hb.trans hzgt.le
  have hsq : ‖z‖ ^ 2 ≤ ‖z‖ := by
    calc
      ‖z‖ ^ 2 = ‖z ^ 2‖ := (norm_pow z 2).symm
      _ = ‖a * z - b‖ := congrArg norm heq
      _ ≤ max ‖a * z‖ ‖b‖ := hsub
      _ ≤ ‖z‖ := max_le haz hbz
  nlinarith [norm_nonneg z]

/-- Inertia at `2` fixes an integral generator of an explicitly unramified quadratic
extension of `ℚ₂`. -/
theorem inertia_fixed_of_unramified_quadratic_generator
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra R L] [IsScalarTower R K L]
    (ι : L →ₐ[K] Ω) (θ : L) (t n : R)
    (htr : Algebra.trace K L θ = algebraMap R K t)
    (hnr : Algebra.norm K θ = algebraMap R K n)
    (hD : residue R (t ^ 2 - 4 * n) ≠ 0)
    (σ : Γ K)
    (hσ : σ ∈ AddSubgroup.inertia
      ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ K)) :
    σ (ι θ) = ι θ := by
  let z : Ω := ι θ
  have hθpoly := sq_sub_trace_mul_self_add_norm
    (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
  rw [htr, hnr] at hθpoly
  have hzpoly : z ^ 2 - algebraMap K Ω (algebraMap R K t) * z +
      algebraMap K Ω (algebraMap R K n) = 0 := by
    have hzpoly' := congrArg ι hθpoly
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hzpoly'
    rw [ι.commutes (algebraMap R K t), ι.commutes (algebraMap R K n)] at hzpoly'
    exact hzpoly'
  have hzle : ‖z‖ ≤ 1 :=
    norm_le_one_of_sq_sub_mul_add_eq_zero
      (norm_algebraMap_integer_to_padicAlgCl_le_one t)
      (norm_algebraMap_integer_to_padicAlgCl_le_one n) hzpoly
  let z0 : Z2bar := ⟨z, by
    rw [Valuation.mem_valuationSubring_iff]
    change ‖z‖₊ ≤ 1
    exact_mod_cast hzle⟩
  have hσzpoly :
      (σ z) ^ 2 - algebraMap K Ω (algebraMap R K t) * σ z +
        algebraMap K Ω (algebraMap R K n) = 0 := by
    have hroot := congrArg σ hzpoly
    simp only [map_add, map_sub, map_mul, map_pow, map_zero] at hroot
    simpa only [σ.commutes] using hroot
  by_contra hne
  have hsum : σ z + z = algebraMap K Ω (algebraMap R K t) := by
    have hprod : (σ z - z) *
        (σ z + z - algebraMap K Ω (algebraMap R K t)) = 0 := by
      linear_combination hσzpoly - hzpoly
    exact sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hne))
  have hsqΩ : (σ z - z) ^ 2 =
      algebraMap K Ω (algebraMap R K (t ^ 2 - 4 * n)) := by
    have hmul : σ z * z = algebraMap K Ω (algebraMap R K n) := by
      linear_combination (σ z) * hsum - hσzpoly
    calc
      (σ z - z) ^ 2 = (σ z + z) ^ 2 - 4 * (σ z * z) := by ring
      _ = (algebraMap K Ω (algebraMap R K t)) ^ 2 - 4 * (σ z * z) := by rw [hsum]
      _ = (algebraMap K Ω (algebraMap R K t)) ^ 2 -
          4 * algebraMap K Ω (algebraMap R K n) := by rw [hmul]
      _ = algebraMap K Ω (algebraMap R K (t ^ 2 - 4 * n)) := by
        symm
        change ((algebraMap K Ω).comp (algebraMap R K)) (t ^ 2 - 4 * n) = _
        rw [map_sub, map_pow, map_mul, map_ofNat]
        rfl
  have hmem : (σ • z0) - z0 ∈ maximalIdeal Z2bar := hσ z0
  have hsqS : ((σ • z0) - z0) ^ 2 = integerToZ2bar (t ^ 2 - 4 * n) := by
    apply Subtype.ext
    exact hsqΩ
  have hpowmem : ((σ • z0) - z0) ^ 2 ∈ maximalIdeal Z2bar :=
    (maximalIdeal Z2bar).pow_mem_of_mem hmem 2 (by norm_num)
  have hunitR : IsUnit (t ^ 2 - 4 * n) :=
    (residue_ne_zero_iff_isUnit _).mp hD
  have hunitS : IsUnit (integerToZ2bar (t ^ 2 - 4 * n)) :=
    hunitR.map integerToZ2bar
  exact (notMem_maximalIdeal.mpr hunitS) (hsqS ▸ hpowmem)

/-- Every element of an explicitly unramified quadratic extension of `ℚ₂` is fixed by
inertia. -/
theorem inertia_fixed_on_unramified_quadratic_extension
    (L : Type*) [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    [Algebra R L] [IsScalarTower R K L]
    (ι : L →ₐ[K] Ω) (θ : L) (t n : R)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htr : Algebra.trace K L θ = algebraMap R K t)
    (hnr : Algebra.norm K θ = algebraMap R K n)
    (hD : residue R (t ^ 2 - 4 * n) ≠ 0)
    (σ : Γ K)
    (hσ : σ ∈ AddSubgroup.inertia
      ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ K)) :
    ∀ x : L, σ (ι x) = ι x := by
  have hfixθ := inertia_fixed_of_unramified_quadratic_generator
    L ι θ t n htr hnr hD σ hσ
  intro x
  by_cases hx : x ∈ Set.range (algebraMap K L)
  · obtain ⟨a, rfl⟩ := hx
    rw [ι.commutes, σ.commutes]
  · obtain ⟨a, b, _ha, hx⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
        K L hθ hx
    rw [hx]
    simp only [map_add, map_mul, ι.commutes, σ.commutes, hfixθ]

/-- The rank-one quadratic representation associated to an explicitly unramified quadratic
extension of `ℚ₂` is trivial on inertia. -/
theorem quadraticCharacterGaloisRep_eq_one_on_inertia
    (N : ℕ) (L : Type*) [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
    [Algebra R L] [IsScalarTower R K L]
    [Algebra L Ω] [IsScalarTower K L Ω]
    (θ : L) (t n : R)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htr : Algebra.trace K L θ = algebraMap R K t)
    (hnr : Algebra.norm K θ = algebraMap R K n)
    (hD : residue R (t ^ 2 - 4 * n) ≠ 0) :
    (∀ σ : Γ K, σ ∈ AddSubgroup.inertia
        ((maximalIdeal Z2bar).toAddSubgroup : AddSubgroup Z2bar) (Γ K) →
      quadraticCharacterGaloisRep K L N σ = 1) := by
  intro σ hσ
  have hfix : ∀ x : L, σ (algebraMap L Ω x) = algebraMap L Ω x := by
    exact inertia_fixed_on_unramified_quadratic_extension L
      (IsScalarTower.toAlgHom K L Ω) θ t n hθ htr hnr hD σ hσ
  have hχ : quadraticCharacter K L Ω σ = 1 :=
    (quadraticCharacter_eq_one_iff K L Ω σ).2 hfix
  change quadraticCharacterGaloisRep K L N σ = 1
  apply LinearMap.ext
  intro x
  simp [quadraticCharacterGaloisRep_apply, hχ]

end

end GaloisRepresentation
