/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve

/-!
# The component quotient on Tate-curve torsion

For an element `q` of infinite order in a commutative group `G`, an `N`-torsion class in
`G / q^ℤ` has a well-defined exponent modulo `N`: if `u` represents the class and
`u ^ N = q ^ z`, its exponent is `z mod N`.  This file constructs that exponent as a
`ZMod N`-linear map.  Applied to Tate uniformization, it is the quotient
`E[N] → Z/NZ` in the standard exact sequence `0 → μ_N → E[N] → Z/NZ → 0`.
-/

@[expose] public section

open scoped Multiplicative

namespace QuotientGroup

variable {G : Type*} [CommGroup G]

/-- A representative `u` of a torsion class has exponent `z` when `u ^ N = q ^ z`. -/
def IsTorsionExponent (q : G) (N : ℕ)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ))
    (z : ℤ) : Prop :=
  ∃ u : G, Additive.ofMul (u : G ⧸ Subgroup.zpowers q) = x.1 ∧ u ^ N = q ^ z

/-- Every torsion class has an exponent. -/
lemma exists_isTorsionExponent (q : G) (N : ℕ)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :
    ∃ z : ℤ, IsTorsionExponent q N x z := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x.1)
  have hpow : (u : G ⧸ Subgroup.zpowers q) ^ N = 1 := by
    have hx : N • x.1 = 0 := congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
    have hx' := congrArg Additive.toMul hx
    simpa [hu] using hx'
  have humem : u ^ N ∈ Subgroup.zpowers q := by
    rw [← QuotientGroup.eq_one_iff]
    simpa only [QuotientGroup.mk_pow] using hpow
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp humem
  exact ⟨z, u, by simpa [hu], hz.symm⟩

/-- Exponents of the same torsion class are congruent modulo `N`, provided `q` has infinite
order. -/
lemma isTorsionExponent_modEq (q : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ))
    {z w : ℤ} (hz : IsTorsionExponent q N x z)
    (hw : IsTorsionExponent q N x w) : z ≡ w [ZMOD N] := by
  obtain ⟨u, hux, huz⟩ := hz
  obtain ⟨v, hvx, hvw⟩ := hw
  have huvquot : (u : G ⧸ Subgroup.zpowers q) = v := by
    exact congrArg Additive.toMul (hux.trans hvx.symm)
  have huv : u / v ∈ Subgroup.zpowers q := QuotientGroup.eq_iff_div_mem.mp huvquot
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp huv
  have hukv : u = q ^ k * v := by
    calc
      u = (u / v) * v := (div_mul_cancel u v).symm
      _ = q ^ k * v := by rw [hk]
  have hzw : q ^ z = q ^ (k * (N : ℤ) + w) := by
    calc
      q ^ z = u ^ N := huz.symm
      _ = (q ^ k * v) ^ N := congrArg (fun a : G ↦ a ^ N) hukv
      _ = (q ^ k) ^ N * v ^ N := mul_pow _ _ _
      _ = q ^ (k * (N : ℤ)) * q ^ w := by rw [← zpow_natCast, ← zpow_mul, hvw]
      _ = q ^ (k * (N : ℤ) + w) := (zpow_add _ _ _).symm
  have hzint : z = k * (N : ℤ) + w := hq hzw
  rw [hzint]
  convert Int.modEq_add_fac_self (a := w) (t := k) (n := N) using 1 <;> ring

/-- The exponent modulo `N` of a torsion class in `G / q^ℤ`. -/
noncomputable def torsionExponent (q : G) (N : ℕ)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) : ZMod N :=
  ((Classical.choose (exists_isTorsionExponent q N x) : ℤ) : ZMod N)

lemma torsionExponent_eq (q : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ))
    {z : ℤ} (hz : IsTorsionExponent q N x z) :
    torsionExponent q N x = (z : ZMod N) := by
  let w := Classical.choose (exists_isTorsionExponent q N x)
  have hw := Classical.choose_spec (exists_isTorsionExponent q N x)
  rw [torsionExponent]
  apply (ZMod.intCast_eq_intCast_iff _ _ N).mpr
  exact isTorsionExponent_modEq q N hq x hw hz

/-- Exponents add under multiplication of representatives. -/
lemma isTorsionExponent_add (q : G) (N : ℕ)
    {x y : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)}
    {z w : ℤ} (hz : IsTorsionExponent q N x z)
    (hw : IsTorsionExponent q N y w) :
    IsTorsionExponent q N (x + y) (z + w) := by
  obtain ⟨u, hux, huz⟩ := hz
  obtain ⟨v, hvy, hvw⟩ := hw
  refine ⟨u * v, ?_, ?_⟩
  · change Additive.ofMul
      ((u : G ⧸ Subgroup.zpowers q) * (v : G ⧸ Subgroup.zpowers q)) = (x + y).1
    rw [ofMul_mul, hux, hvy]
    rfl
  · rw [mul_pow, huz, hvw, ← zpow_add]

/-- The Tate exponent is an additive homomorphism. -/
noncomputable def torsionExponentAddHom (q : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z) :
    AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) →+ ZMod N where
  toFun := torsionExponent q N
  map_zero' := by
    simpa using torsionExponent_eq q N hq
      (0 : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ))
      (z := 0) ⟨1, rfl, by simp⟩
  map_add' x y := by
    let z := Classical.choose (exists_isTorsionExponent q N x)
    let w := Classical.choose (exists_isTorsionExponent q N y)
    have hz := Classical.choose_spec (exists_isTorsionExponent q N x)
    have hw := Classical.choose_spec (exists_isTorsionExponent q N y)
    calc
      torsionExponent q N (x + y) = ((z + w : ℤ) : ZMod N) :=
        torsionExponent_eq q N hq (x + y) (isTorsionExponent_add q N hz hw)
      _ = (z : ZMod N) + (w : ZMod N) := Int.cast_add z w
      _ = torsionExponent q N x + torsionExponent q N y := by
        rw [torsionExponent_eq q N hq x hz, torsionExponent_eq q N hq y hw]

/-- The Tate exponent as a `ZMod N`-linear map. -/
noncomputable def torsionExponentLinearMap (q : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) →ₗ[ZMod N] ZMod N := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  exact (torsionExponentAddHom q N hq).toZModLinearMap N

/-- The torsion class represented by an `N`-th root of `q`. -/
def torsionClassOfRoot (q r : G) (N : ℕ) (hr : r ^ N = q) :
    AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) := by
  refine ⟨Additive.ofMul (r : G ⧸ Subgroup.zpowers q), ?_⟩
  rw [AddSubgroup.torsionBy.nsmul_iff]
  change Additive.ofMul ((r : G ⧸ Subgroup.zpowers q) ^ N) = 0
  rw [← QuotientGroup.mk_pow, hr]
  change (q : G ⧸ Subgroup.zpowers q) = 1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_zpowers q

/-- An `N`-th root of `q` has Tate exponent one. -/
lemma torsionExponent_torsionClassOfRoot (q r : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z) (hr : r ^ N = q) :
    torsionExponent q N (torsionClassOfRoot q r N hr) = 1 := by
  simpa using torsionExponent_eq q N hq (torsionClassOfRoot q r N hr)
    (z := 1) ⟨r, rfl, by simpa using hr⟩

/-- If `q` has an `N`-th root, the Tate exponent map is onto. -/
lemma torsionExponentLinearMap_surjective (q r : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z) (hr : r ^ N = q) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Function.Surjective (torsionExponentLinearMap q N hq) := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  intro a
  refine ⟨a • torsionClassOfRoot q r N hr, ?_⟩
  rw [map_smul, show torsionExponentLinearMap q N hq
      (torsionClassOfRoot q r N hr) = 1 from
    torsionExponent_torsionClassOfRoot q r N hq hr, smul_eq_mul, mul_one]

end QuotientGroup
