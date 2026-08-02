/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.KnownIn1980s.EllipticCurves.TateCurve
public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.SplitMultiplicativeReduction

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

/-- An additive equivalence restricts to a `ZMod N`-linear equivalence on `N`-torsion. -/
noncomputable def AddEquiv.torsionByLinearEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (N : ℕ) :
    letI : Module (ZMod N) (AddSubgroup.torsionBy A (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod N) (AddSubgroup.torsionBy B (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy A (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy B (N : ℤ) := by
  letI : Module (ZMod N) (AddSubgroup.torsionBy A (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N) (AddSubgroup.torsionBy B (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let eN : AddSubgroup.torsionBy A (N : ℤ) ≃+
      AddSubgroup.torsionBy B (N : ℤ) := {
    toFun x := ⟨e x.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
      have hx : N • x.1 = 0 := congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
      rw [hx, map_zero]⟩
    invFun x := ⟨e.symm x.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
      have hx : N • x.1 = 0 := congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
      rw [hx, map_zero]⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x.1)
    right_inv x := Subtype.ext (e.apply_symm_apply x.1)
    map_add' x y := Subtype.ext (map_add e x.1 y.1) }
  exact LinearEquiv.ofBijective (eN.toAddMonoidHom.toZModLinearMap N) eN.bijective

@[simp]
lemma AddEquiv.torsionByLinearEquiv_coe
    {A B : Type*} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (N : ℕ)
    (x : AddSubgroup.torsionBy A (N : ℤ)) :
    (e.torsionByLinearEquiv N x).1 = e x.1 :=
  rfl

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

/-! ### Functoriality under automorphisms fixing the Tate parameter -/

/-- A group endomorphism fixing `q` descends to the quotient by `q^ℤ`. -/
def mapFixingGenerator (q : G) (f : G →* G) (hf : f q = q) :
    G ⧸ Subgroup.zpowers q →* G ⧸ Subgroup.zpowers q :=
  QuotientGroup.map (Subgroup.zpowers q) (Subgroup.zpowers q) f <| by
    intro u hu
    obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    change f (q ^ z) ∈ Subgroup.zpowers q
    rw [map_zpow, hf]
    exact zpow_mem (Subgroup.mem_zpowers q) z

@[simp]
lemma mapFixingGenerator_mk (q : G) (f : G →* G) (hf : f q = q) (u : G) :
    mapFixingGenerator q f hf (u : G ⧸ Subgroup.zpowers q) =
      (f u : G ⧸ Subgroup.zpowers q) :=
  rfl

/-- The induced endomorphism on the `N`-torsion of the quotient by `q^ℤ`. -/
def torsionMapFixingGenerator (q : G) (N : ℕ) (f : G →* G) (hf : f q = q) :
    AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) →+
      AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) := by
  let F : Additive (G ⧸ Subgroup.zpowers q) →+ Additive (G ⧸ Subgroup.zpowers q) :=
    (mapFixingGenerator q f hf).toAdditive
  exact (F.domRestrict (AddSubgroup.torsionBy
      (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ))).codRestrict
    (AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) <| by
      intro x
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul,
        AddSubgroup.torsionBy.nsmul, map_zero]

@[simp]
lemma torsionMapFixingGenerator_coe (q : G) (N : ℕ) (f : G →* G)
    (hf : f q = q)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :
    (torsionMapFixingGenerator q N f hf x).1 =
      Additive.ofMul (mapFixingGenerator q f hf (Additive.toMul x.1)) :=
  rfl

/-- Automorphisms fixing `q` preserve the Tate exponent. -/
lemma torsionExponent_torsionMapFixingGenerator (q : G) (N : ℕ)
    (hq : Function.Injective fun z : ℤ ↦ q ^ z)
    (f : G →* G) (hf : f q = q)
    (x : AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ)) :
    torsionExponent q N (torsionMapFixingGenerator q N f hf x) =
      torsionExponent q N x := by
  let z := Classical.choose (exists_isTorsionExponent q N x)
  have hz := Classical.choose_spec (exists_isTorsionExponent q N x)
  obtain ⟨u, hux, hupow⟩ := hz
  have hzmap : IsTorsionExponent q N (torsionMapFixingGenerator q N f hf x) z := by
    refine ⟨f u, ?_, ?_⟩
    · rw [torsionMapFixingGenerator_coe]
      apply congrArg Additive.ofMul
      have huxmul : (u : G ⧸ Subgroup.zpowers q) = Additive.toMul x.1 :=
        congrArg Additive.toMul hux
      rw [← huxmul, mapFixingGenerator_mk]
    · rw [← map_pow, hupow, map_zpow, hf]
  rw [torsionExponent_eq q N hq _ hzmap,
    torsionExponent_eq q N hq _ ⟨u, hux, hupow⟩]

end QuotientGroup

namespace WeierstrassCurve

open ValuativeRel
open scoped WeierstrassCurve.Affine

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
variable (E : WeierstrassCurve k) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[k]]
variable (Ω : Type*) [Field Ω] [Algebra k Ω] [IsSepClosed Ω]
  [Algebra.IsSeparable k Ω] [DecidableEq k] [DecidableEq Ω]

/-- The image of the Tate parameter in a separable closure has infinite order. -/
lemma qUnitSepClosure_zpow_injective :
    Function.Injective fun z : ℤ ↦ E.qUnitSepClosure Ω ^ z := by
  intro z w hzw
  let f : kˣ →* Ωˣ := Units.map (algebraMap k Ω).toMonoidHom
  have hf : Function.Injective f := Units.map_injective (algebraMap k Ω).injective
  have hbase : E.qUnit ^ z = E.qUnit ^ w := by
    apply hf
    simpa only [f, WeierstrassCurve.qUnitSepClosure, map_zpow] using hzw
  have hval := congrArg (fun u : kˣ ↦ valuation k (u : k)) hbase
  simp only [Units.val_zpow_eq_zpow_val, map_zpow₀] at hval
  have hq0 : 0 < valuation k (E.qUnit : k) :=
    (valuation k).pos_iff.mpr E.qUnit.ne_zero
  have hq1 : valuation k (E.qUnit : k) ≠ 1 :=
    ne_of_lt (by simpa [WeierstrassCurve.qUnit] using E.valuation_q_lt_one)
  exact (zpow_right_injective₀ hq0 hq1) hval

/-- Tate uniformization restricted to `N`-torsion, upgraded to a `ZMod N`-linear
equivalence. -/
noncomputable def tateTorsionLinearEquiv (N : ℕ) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy
          (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  let e : AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ) ≃+
      AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) := {
    toFun x := ⟨E.tateEquivSepClosure Ω x.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
      have hx : N • x.1 = 0 := congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
      rw [hx, map_zero]⟩
    invFun x := ⟨(E.tateEquivSepClosure Ω).symm x.1, by
      rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul]
      have hx : N • x.1 = 0 := congrArg Subtype.val (AddSubgroup.torsionBy.nsmul x)
      rw [hx, map_zero]⟩
    left_inv x := Subtype.ext ((E.tateEquivSepClosure Ω).symm_apply_apply x.1)
    right_inv x := Subtype.ext ((E.tateEquivSepClosure Ω).apply_symm_apply x.1)
    map_add' x y := Subtype.ext (map_add (E.tateEquivSepClosure Ω) x.1 y.1) }
  exact LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap N) e.bijective

@[simp]
lemma tateTorsionLinearEquiv_coe (N : ℕ)
    (x : AddSubgroup.torsionBy
      (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :
    (E.tateTorsionLinearEquiv Ω N x).1 = E.tateEquivSepClosure Ω x.1 :=
  rfl

/-- The component quotient `E[N] → Z/NZ` supplied by Tate uniformization. -/
noncomputable def tateComponentLinearMap (N : ℕ) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ) →ₗ[ZMod N] ZMod N := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  exact (QuotientGroup.torsionExponentLinearMap (E.qUnitSepClosure Ω) N
      (E.qUnitSepClosure_zpow_injective Ω)).comp
    (E.tateTorsionLinearEquiv Ω N).symm.toLinearMap

/-- The component quotient of Tate-curve torsion is surjective. -/
lemma tateComponentLinearMap_surjective (N : ℕ) [NeZero (N : Ω)] :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Function.Surjective (E.tateComponentLinearMap Ω N) := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  obtain ⟨r, hr⟩ := IsSepClosed.exists_pow_nat_eq
    (algebraMap k Ω E.q) N
  have hN : 0 < N := Nat.pos_of_ne_zero fun hN ↦ by
    apply NeZero.ne (N : Ω)
    rw [hN, Nat.cast_zero]
  have hr0 : r ≠ 0 := by
    intro hrzero
    rw [hrzero, zero_pow hN.ne'] at hr
    exact E.q_ne_zero ((algebraMap k Ω).injective (by simpa using hr.symm))
  let ru : Ωˣ := Units.mk0 r hr0
  have hru : ru ^ N = E.qUnitSepClosure Ω := by
    apply Units.ext
    change r ^ N = algebraMap k Ω E.q
    exact hr
  exact (QuotientGroup.torsionExponentLinearMap_surjective
      (E.qUnitSepClosure Ω) ru N (E.qUnitSepClosure_zpow_injective Ω) hru).comp
    (E.tateTorsionLinearEquiv Ω N).symm.surjective

/-- A base-field automorphism of the separable closure fixes the Tate parameter. -/
lemma unitsMap_qUnitSepClosure (σ : Ω ≃ₐ[k] Ω) :
    Units.map σ.toAlgHom.toRingHom.toMonoidHom (E.qUnitSepClosure Ω) =
      E.qUnitSepClosure Ω := by
  apply Units.ext
  change σ (algebraMap k Ω E.q) = algebraMap k Ω E.q
  exact σ.commutes E.q

/-- Pulling the Galois action through Tate uniformization gives the quotient action induced by
the automorphism of the multiplicative group. -/
lemma tateTorsionLinearEquiv_symm_nTorsionMap (N : ℕ) (σ : Ω ≃ₐ[k] Ω)
    (T : AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :
    (E.tateTorsionLinearEquiv Ω N).symm (E.nTorsionMap N σ.toAlgHom T) =
      QuotientGroup.torsionMapFixingGenerator (E.qUnitSepClosure Ω) N
        (Units.map σ.toAlgHom.toRingHom.toMonoidHom)
        (E.unitsMap_qUnitSepClosure Ω σ)
        ((E.tateTorsionLinearEquiv Ω N).symm T) := by
  let e := E.tateTorsionLinearEquiv Ω N
  let x := e.symm T
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul x.1)
  apply e.injective
  apply Subtype.ext
  rw [e.apply_symm_apply]
  rw [E.nTorsionMap_coe, E.tateTorsionLinearEquiv_coe]
  have hT : T.1 = E.tatePoint Ω u := by
    calc
      T.1 = (e x).1 := congrArg Subtype.val (e.apply_symm_apply T).symm
      _ = E.tateEquivSepClosure Ω x.1 := E.tateTorsionLinearEquiv_coe Ω N x
      _ = E.tatePoint Ω u := by
        rw [WeierstrassCurve.tatePoint]
        congr 2
        simpa using (congrArg Additive.ofMul hu).symm
  rw [hT]
  change WeierstrassCurve.Affine.Point.map (W' := E) σ.toAlgHom
      (E.tatePoint Ω u) = E.tateEquivSepClosure Ω
        (QuotientGroup.torsionMapFixingGenerator (E.qUnitSepClosure Ω) N
          (Units.map σ.toAlgHom.toRingHom.toMonoidHom)
          (E.unitsMap_qUnitSepClosure Ω σ) x).1
  rw [E.tatePoint_galois Ω σ u]
  rw [show (QuotientGroup.torsionMapFixingGenerator (E.qUnitSepClosure Ω) N
      (Units.map σ.toAlgHom.toRingHom.toMonoidHom)
      (E.unitsMap_qUnitSepClosure Ω σ) x).1 =
        Additive.ofMul
          (Units.map σ.toAlgHom.toRingHom.toMonoidHom u :
            Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω)) from by
      rw [QuotientGroup.torsionMapFixingGenerator_coe]
      change Additive.ofMul
          (QuotientGroup.mapFixingGenerator (E.qUnitSepClosure Ω)
            (Units.map σ.toAlgHom.toRingHom.toMonoidHom)
            (E.unitsMap_qUnitSepClosure Ω σ) (Additive.toMul x.1)) = _
      rw [← hu, QuotientGroup.mapFixingGenerator_mk]]
  rfl

/-- The Tate component quotient is Galois invariant in the split-multiplicative case. -/
lemma tateComponentLinearMap_nTorsionMap (N : ℕ) (σ : Ω ≃ₐ[k] Ω)
    (T : AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :
    E.tateComponentLinearMap Ω N (E.nTorsionMap N σ.toAlgHom T) =
      E.tateComponentLinearMap Ω N T := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy
        (Additive (Ωˣ ⧸ Subgroup.zpowers (E.qUnitSepClosure Ω))) (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  change QuotientGroup.torsionExponent (E.qUnitSepClosure Ω) N
      ((E.tateTorsionLinearEquiv Ω N).symm (E.nTorsionMap N σ.toAlgHom T)) =
    QuotientGroup.torsionExponent (E.qUnitSepClosure Ω) N
      ((E.tateTorsionLinearEquiv Ω N).symm T)
  rw [E.tateTorsionLinearEquiv_symm_nTorsionMap Ω N σ T]
  exact QuotientGroup.torsionExponent_torsionMapFixingGenerator
    (E.qUnitSepClosure Ω) N (E.qUnitSepClosure_zpow_injective Ω)
    (Units.map σ.toAlgHom.toRingHom.toMonoidHom)
    (E.unitsMap_qUnitSepClosure Ω σ) _

/-! ### The nonsplit multiplicative case -/

section QuadraticTwist

variable {L : Type*} [Field L] [Algebra k L]
  [Algebra.IsQuadraticExtension k L] [Algebra.IsSeparable k L]
  [Algebra L Ω] [IsScalarTower k L Ω]
variable (E₀ : WeierstrassCurve k) [E₀.IsElliptic]
variable (C : WeierstrassCurve.VariableChange k)
variable [((C • E₀.quadraticTwist L)).HasSplitMultiplicativeReduction 𝒪[k]]

/-- The split minimal model of a quadratic twist is isomorphic over the separable closure to
the original curve. -/
noncomputable def quadraticTwistTatePointEquiv :
    (((C • E₀.quadraticTwist L))⁄Ω).Point ≃+ (E₀⁄Ω).Point :=
  (WeierstrassCurve.Affine.Point.variableChangePointEquiv
      (E₀.quadraticTwist L) C Ω).trans
    (E₀.quadraticTwistPointEquiv L Ω)

/-- The point equivalence from the split quadratic twist, restricted to `N`-torsion. -/
noncomputable def quadraticTwistTateTorsionLinearEquiv (N : ℕ) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (((C • E₀.quadraticTwist L))⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (((C • E₀.quadraticTwist L))⁄Ω).Point (N : ℤ) ≃ₗ[ZMod N]
      AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ) :=
  (quadraticTwistTatePointEquiv Ω E₀ C).torsionByLinearEquiv N

/-- The Tate component quotient on a multiplicative curve, obtained from a split quadratic
twist. -/
noncomputable def quadraticTwistTateComponentLinearMap (N : ℕ) :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ) →ₗ[ZMod N] ZMod N := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (((C • E₀.quadraticTwist L))⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  exact ((C • E₀.quadraticTwist L).tateComponentLinearMap Ω N).comp
    (quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N).symm.toLinearMap

/-- The component quotient obtained from the split quadratic twist is surjective. -/
lemma quadraticTwistTateComponentLinearMap_surjective (N : ℕ) [NeZero (N : Ω)] :
    letI : Module (ZMod N)
        (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
      AddSubgroup.torsionBy.zmodModule
    Function.Surjective
      (quadraticTwistTateComponentLinearMap (L := L) Ω E₀ C N) := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (((C • E₀.quadraticTwist L))⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  exact ((C • E₀.quadraticTwist L).tateComponentLinearMap_surjective Ω N).comp
    (quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N).symm.surjective

/-- Under the torsion equivalence from the split quadratic twist, Galois acts with the
quadratic sign. -/
lemma quadraticTwistTateTorsionLinearEquiv_symm_nTorsionMap
    (N : ℕ) (σ : Ω ≃ₐ[k] Ω)
    (T : AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :
    (quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N).symm
        (E₀.nTorsionMap N σ.toAlgHom T) =
      (quadraticCharacter k L Ω σ : ℤ) •
        (C • E₀.quadraticTwist L).nTorsionMap N σ.toAlgHom
          ((quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N).symm T) := by
  let e := quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N
  let P := e.symm T
  apply e.injective
  apply Subtype.ext
  rw [e.apply_symm_apply]
  rw [E₀.nTorsionMap_coe]
  change WeierstrassCurve.Affine.Point.map (W' := E₀) σ.toAlgHom T.1 =
    (quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N
      ((quadraticCharacter k L Ω σ : ℤ) •
        (C • E₀.quadraticTwist L).nTorsionMap N σ.toAlgHom P)).1
  rw [quadraticTwistTateTorsionLinearEquiv,
    AddEquiv.torsionByLinearEquiv_coe]
  change WeierstrassCurve.Affine.Point.map (W' := E₀) σ.toAlgHom T.1 =
    quadraticTwistTatePointEquiv (L := L) Ω E₀ C
      ((quadraticCharacter k L Ω σ : ℤ) •
        ((C • E₀.quadraticTwist L).nTorsionMap N σ.toAlgHom P).1)
  rw [map_zsmul, (C • E₀.quadraticTwist L).nTorsionMap_coe]
  have hP : (quadraticTwistTatePointEquiv (L := L) Ω E₀ C) P.1 = T.1 := by
    exact congrArg Subtype.val (e.apply_symm_apply T)
  have hmap : quadraticTwistTatePointEquiv (L := L) Ω E₀ C
      (WeierstrassCurve.Affine.Point.map (W' := C • E₀.quadraticTwist L)
        σ.toAlgHom P.1) =
      (quadraticCharacter k L Ω σ : ℤ) •
        WeierstrassCurve.Affine.Point.map (W' := E₀) σ.toAlgHom T.1 := by
    change E₀.quadraticTwistPointEquiv L Ω
        (WeierstrassCurve.Affine.Point.variableChangePointEquiv
          (E₀.quadraticTwist L) C Ω
          (WeierstrassCurve.Affine.Point.map σ.toAlgHom P.1)) = _
    rw [WeierstrassCurve.Affine.Point.variableChangePointEquiv_map]
    rw [E₀.quadraticTwistPointEquiv_galois L Ω σ]
    rw [← hP]
    rfl
  change WeierstrassCurve.Affine.Point.map (W' := E₀) σ.toAlgHom T.1 =
    (quadraticCharacter k L Ω σ : ℤ) •
      quadraticTwistTatePointEquiv (L := L) Ω E₀ C
        (WeierstrassCurve.Affine.Point.map (W' := C • E₀.quadraticTwist L)
          σ.toAlgHom P.1)
  rw [hmap]
  rcases Int.units_eq_one_or (quadraticCharacter k L Ω σ) with hχ | hχ
  · simp [hχ]
  · simp [hχ]

/-- The Tate component quotient of a multiplicative curve transforms under Galois by the
quadratic character of any quadratic extension over which the curve becomes split
multiplicative. -/
lemma quadraticTwistTateComponentLinearMap_nTorsionMap
    (N : ℕ) (σ : Ω ≃ₐ[k] Ω)
    (T : AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :
    quadraticTwistTateComponentLinearMap (L := L) Ω E₀ C N
        (E₀.nTorsionMap N σ.toAlgHom T) =
      (quadraticCharacter k L Ω σ : ℤ) •
        quadraticTwistTateComponentLinearMap (L := L) Ω E₀ C N T := by
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (((C • E₀.quadraticTwist L))⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  letI : Module (ZMod N)
      (AddSubgroup.torsionBy (E₀⁄Ω).Point (N : ℤ)) :=
    AddSubgroup.torsionBy.zmodModule
  change (C • E₀.quadraticTwist L).tateComponentLinearMap Ω N
      ((quadraticTwistTateTorsionLinearEquiv (L := L) Ω E₀ C N).symm
        (E₀.nTorsionMap N σ.toAlgHom T)) = _
  rw [quadraticTwistTateTorsionLinearEquiv_symm_nTorsionMap]
  rw [map_zsmul]
  rw [(C • E₀.quadraticTwist L).tateComponentLinearMap_nTorsionMap]
  rfl

end QuadraticTwist

end WeierstrassCurve
