/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummerPoints
public import FLT.KnownIn1980s.EllipticCurves.TateCurveTorsion

/-!
# Tate--Kummer points and quotient torsion

If `q = a ^ N * u`, a Kummer point `(i, x)` with `x ^ N = u ^ i`+maps to the `N`-torsion class represented by `a ^ i * x` in `Sˣ / q^ℤ`.
This file proves that the carry correction in the finite-flat Hopf algebra is exactly
what makes this assignment multiplicative, and constructs its inverse.
-/

@[expose] public section

open scoped Multiplicative TensorProduct

universe u v

namespace QuotientGroup

variable {G : Type*} [CommGroup G]

/-- A class represented by an element whose `N`-th power is the `i`-th power of the
quotient generator is `N`-torsion. -/
def torsionClassOfExponent (q r : G) (N i : ℕ) (hr : r ^ N = q ^ i) :
    AddSubgroup.torsionBy (Additive (G ⧸ Subgroup.zpowers q)) (N : ℤ) := by
  refine ⟨Additive.ofMul (r : G ⧸ Subgroup.zpowers q), ?_⟩
  rw [AddSubgroup.torsionBy.nsmul_iff]
  change Additive.ofMul ((r : G ⧸ Subgroup.zpowers q) ^ N) = 0
  rw [← QuotientGroup.mk_pow, hr]
  change (q ^ i : G ⧸ Subgroup.zpowers q) = 1
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact (Subgroup.zpowers q).pow_mem (Subgroup.mem_zpowers q) i

/-- The evident representative witnesses the exponent of `torsionClassOfExponent`. -/
lemma isTorsionExponent_torsionClassOfExponent
    (q r : G) (N i : ℕ) (hr : r ^ N = q ^ i) :
    IsTorsionExponent q N (torsionClassOfExponent q r N i hr) (i : ℤ) :=
  ⟨r, rfl, by simpa only [zpow_natCast] using hr⟩

end QuotientGroup

namespace TateKummer

section QuotientTorsion

variable (R : Type u) [CommRing R]
variable (S : Type v) [Field S] [Algebra R S]

/-- Two standard representatives in `Fin N` are equal if their natural-number casts in
`ZMod N` agree. -/
lemma fin_eq_of_natCast_zmod_eq
    (N : ℕ) [NeZero N] (i j : Fin N)
    (h : (i.1 : ZMod N) = (j.1 : ZMod N)) : i = j := by
  apply Fin.ext
  have hmod := (ZMod.natCast_eq_natCast_iff' i.1 j.1 N).mp h
  simpa [Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] using hmod

/-- The representative `a^i x` attached to a Kummer point `(i, x)`. -/
noncomputable def kummerRepresentative
    (N : ℕ) (u : Rˣ) (a : Sˣ) (x : KummerUnitPoint R S N u) : Sˣ :=
  a ^ x.1.1 * x.2.1

/-- The representative attached to `(i, x)` has `N`-th power
`(a^N u)^i`. -/
lemma kummerRepresentative_pow
    (N : ℕ) (u : Rˣ) (a : Sˣ) (x : KummerUnitPoint R S N u) :
    kummerRepresentative R S N u a x ^ N =
      (a ^ N * Units.map (algebraMap R S) u) ^ x.1.1 := by
  rcases x with ⟨i, x⟩
  change (a ^ i.1 * x.1) ^ N =
    (a ^ N * Units.map (algebraMap R S) u) ^ i.1
  rw [mul_pow, mul_pow, x.2, ← pow_mul, ← pow_mul,
    Nat.mul_comm i.1 N]
  simp only [map_pow]

/-- The quotient-torsion point represented by `a^i x`. -/
noncomputable def kummerPointToTorsion
    (N : ℕ) (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (x : KummerUnitPoint R S N u) :
    AddSubgroup.torsionBy (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) :=
  QuotientGroup.torsionClassOfExponent q (kummerRepresentative R S N u a x)
    N x.1.1 (by rw [kummerRepresentative_pow, hq])

/-- The component index is an exponent of the associated quotient-torsion point. -/
lemma kummerPointToTorsion_isTorsionExponent
    (N : ℕ) (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (x : KummerUnitPoint R S N u) :
    QuotientGroup.IsTorsionExponent q N
      (kummerPointToTorsion R S N u q a hq x) (x.1.1 : ℤ) :=
  QuotientGroup.isTorsionExponent_torsionClassOfExponent q
    (kummerRepresentative R S N u a x) N x.1.1
      (by rw [kummerRepresentative_pow, hq])

/-- Multiplying Kummer representatives differs from the representative of the
carry-corrected product by the corresponding power of `q`. -/
lemma kummerRepresentative_mul
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (x y : KummerUnitPoint R S N u) :
    kummerRepresentative R S N u a x * kummerRepresentative R S N u a y =
      q ^ addCarry N x.1 y.1 *
        kummerRepresentative R S N u a
          (kummerUnitPointMul R S N u x y) := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  let uS : Sˣ := Units.map (algebraMap R S) u
  have hindex := addIndex_val_add_mul_addCarry N i j
  change (a ^ i.1 * x.1) * (a ^ j.1 * y.1) =
    q ^ addCarry N i j *
      (a ^ (addIndex N i j).1 *
        (x.1 * y.1 * (uS⁻¹) ^ addCarry N i j))
  rw [← hq, mul_pow]
  calc
    (a ^ i.1 * x.1) * (a ^ j.1 * y.1) =
        a ^ (i.1 + j.1) * (x.1 * y.1) := by
      rw [pow_add]
      ac_rfl
    _ = a ^ ((addIndex N i j).1 + N * addCarry N i j) *
          (x.1 * y.1) := by
      rw [hindex]
    _ = (a ^ N) ^ addCarry N i j * uS ^ addCarry N i j *
          (a ^ (addIndex N i j).1 *
            (x.1 * y.1 * (uS⁻¹) ^ addCarry N i j)) := by
      have hcancel : uS ^ addCarry N i j *
          (uS⁻¹) ^ addCarry N i j = 1 := by
        rw [← mul_pow]
        simp
      calc
        a ^ ((addIndex N i j).1 + N * addCarry N i j) *
            (x.1 * y.1) =
          a ^ (addIndex N i j).1 * (a ^ N) ^ addCarry N i j *
            (x.1 * y.1) := by
          rw [pow_add, pow_mul]
        _ = a ^ (addIndex N i j).1 * (a ^ N) ^ addCarry N i j *
            (x.1 * y.1) *
              (uS ^ addCarry N i j * (uS⁻¹) ^ addCarry N i j) := by
          rw [hcancel, mul_one]
        _ = _ := by ac_rfl

/-- The Kummer-to-quotient assignment sends carry-corrected multiplication to addition
of torsion classes. -/
lemma kummerPointToTorsion_mul
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (x y : KummerUnitPoint R S N u) :
    kummerPointToTorsion R S N u q a hq
        (kummerUnitPointMul R S N u x y) =
      kummerPointToTorsion R S N u q a hq x +
        kummerPointToTorsion R S N u q a hq y := by
  apply Subtype.ext
  change Additive.ofMul
      ((kummerRepresentative R S N u a
        (kummerUnitPointMul R S N u x y) : Sˣ ⧸ Subgroup.zpowers q)) =
    Additive.ofMul
      ((kummerRepresentative R S N u a x : Sˣ ⧸ Subgroup.zpowers q) *
        (kummerRepresentative R S N u a y : Sˣ ⧸ Subgroup.zpowers q))
  apply congrArg Additive.ofMul
  have hrep := congrArg
    (fun z : Sˣ ↦ (z : Sˣ ⧸ Subgroup.zpowers q))
    (kummerRepresentative_mul R S N u q a hq x y)
  change (kummerRepresentative R S N u a x : Sˣ ⧸ Subgroup.zpowers q) *
      kummerRepresentative R S N u a y =
    (q ^ addCarry N x.1 y.1 : Sˣ ⧸ Subgroup.zpowers q) *
      kummerRepresentative R S N u a
        (kummerUnitPointMul R S N u x y) at hrep
  have hqpow : (q ^ addCarry N x.1 y.1 : Sˣ ⧸ Subgroup.zpowers q) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact (Subgroup.zpowers q).pow_mem (Subgroup.mem_zpowers q) _
  rw [hqpow] at hrep
  exact (one_mul _).symm.trans hrep.symm

/-- Distinct Kummer points give distinct quotient-torsion classes when the Tate
parameter has infinite order. -/
lemma kummerPointToTorsion_injective
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    Function.Injective (kummerPointToTorsion R S N u q a hq) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ hxy
  have hiExp := QuotientGroup.torsionExponent_eq q N hqinj
    (kummerPointToTorsion R S N u q a hq ⟨i, x⟩)
    (kummerPointToTorsion_isTorsionExponent R S N u q a hq ⟨i, x⟩)
  have hjExp := QuotientGroup.torsionExponent_eq q N hqinj
    (kummerPointToTorsion R S N u q a hq ⟨j, y⟩)
    (kummerPointToTorsion_isTorsionExponent R S N u q a hq ⟨j, y⟩)
  have hiExp' : QuotientGroup.torsionExponent q N
      (kummerPointToTorsion R S N u q a hq ⟨i, x⟩) =
        (i.1 : ZMod N) := by
    simpa using hiExp
  have hjExp' : QuotientGroup.torsionExponent q N
      (kummerPointToTorsion R S N u q a hq ⟨j, y⟩) =
        (j.1 : ZMod N) := by
    simpa using hjExp
  have hijCast : (i.1 : ZMod N) = (j.1 : ZMod N) := by
    calc
      (i.1 : ZMod N) = QuotientGroup.torsionExponent q N
          (kummerPointToTorsion R S N u q a hq ⟨i, x⟩) := hiExp'.symm
      _ = QuotientGroup.torsionExponent q N
          (kummerPointToTorsion R S N u q a hq ⟨j, y⟩) := congrArg _ hxy
      _ = (j.1 : ZMod N) := hjExp'
  have hij : i = j := fin_eq_of_natCast_zmod_eq N i j hijCast
  subst j
  have hquot :
      (kummerRepresentative R S N u a ⟨i, x⟩ :
          Sˣ ⧸ Subgroup.zpowers q) =
        kummerRepresentative R S N u a ⟨i, y⟩ := by
    exact congrArg (fun t ↦ Additive.toMul t.1) hxy
  have hmem : kummerRepresentative R S N u a ⟨i, x⟩ /
      kummerRepresentative R S N u a ⟨i, y⟩ ∈ Subgroup.zpowers q :=
    QuotientGroup.eq_iff_div_mem.mp hquot
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz' : q ^ z = (a ^ i.1 * x.1) / (a ^ i.1 * y.1) := by
    exact hz
  have hzxy : x.1 / y.1 = q ^ z := by
    calc
      x.1 / y.1 = (a ^ i.1 * x.1) / (a ^ i.1 * y.1) :=
        (mul_div_mul_left_eq_div x.1 y.1 (a ^ i.1)).symm
      _ = q ^ z := hz'.symm
  have hxyPow : (x.1 / y.1) ^ N = 1 := by
    rw [div_pow, x.2, y.2]
    change (Units.map (algebraMap R S) (u ^ i.1) : Sˣ) /
      Units.map (algebraMap R S) (u ^ i.1) = 1
    simp
  have hqPow : q ^ (z * (N : ℤ)) = q ^ (0 : ℤ) := by
    calc
      q ^ (z * (N : ℤ)) = (q ^ z) ^ N := by
        rw [zpow_mul, zpow_natCast]
      _ = (x.1 / y.1) ^ N := congrArg (fun w : Sˣ ↦ w ^ N) hzxy.symm
      _ = 1 := hxyPow
      _ = q ^ (0 : ℤ) := (zpow_zero q).symm
  have hzMul : z * (N : ℤ) = 0 := hqinj hqPow
  have hNInt : (N : ℤ) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have hz0 : z = 0 := (mul_eq_zero.mp hzMul).resolve_right hNInt
  have hxyUnit : x.1 = y.1 := by
    apply (div_eq_one.mp)
    simpa [hz0] using hzxy
  have hxyRoot : x = y := Subtype.ext hxyUnit
  subst y
  rfl

/-- Every quotient-torsion class has a normalized Kummer representative. -/
lemma kummerPointToTorsion_surjective
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q) :
    Function.Surjective (kummerPointToTorsion R S N u q a hq) := by
  intro t
  obtain ⟨z, b, hbt, hbpow⟩ :=
    QuotientGroup.exists_isTorsionExponent q N t
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNint : 0 < (N : ℤ) := by exact_mod_cast hNnat
  let r : ℤ := z % (N : ℤ)
  let k : ℤ := z / (N : ℤ)
  have hr0 : 0 ≤ r := by
    exact Int.emod_nonneg z (ne_of_gt hNint)
  have hrN : r < (N : ℤ) := by
    exact Int.emod_lt_of_pos z hNint
  have hrNatN : r.toNat < N := by
    have hrCast : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hr0
    have h : (r.toNat : ℤ) < (N : ℤ) := by simpa only [hrCast] using hrN
    exact_mod_cast h
  let i : Fin N := ⟨r.toNat, hrNatN⟩
  have hiCast : (i.1 : ℤ) = r := by
    exact Int.toNat_of_nonneg hr0
  have hzsplit : r + (N : ℤ) * k = z := by
    exact Int.emod_add_mul_ediv z (N : ℤ)
  let b₀ : Sˣ := b * q ^ (-k)
  have hb₀pow : b₀ ^ N = q ^ i.1 := by
    calc
      b₀ ^ N = b ^ N * (q ^ (-k)) ^ N := by
        change (b * q ^ (-k)) ^ N = _
        rw [mul_pow]
      _ = q ^ z * q ^ ((-k) * (N : ℤ)) := by
        rw [hbpow, ← zpow_natCast, ← zpow_mul]
      _ = q ^ (z + (-k) * (N : ℤ)) := (zpow_add q _ _).symm
      _ = q ^ r := by
        have hexp : z + (-k) * (N : ℤ) = r := by
          rw [← hzsplit]
          ring
        rw [hexp]
      _ = q ^ (i.1 : ℤ) := by rw [hiCast]
      _ = q ^ i.1 := zpow_natCast q i.1
  let uS : Sˣ := Units.map (algebraMap R S) u
  let x₀ : Sˣ := b₀ / a ^ i.1
  have hx₀pow : x₀ ^ N = uS ^ i.1 := by
    calc
      x₀ ^ N = b₀ ^ N / (a ^ i.1) ^ N := by
        change (b₀ / a ^ i.1) ^ N = _
        rw [div_pow]
      _ = q ^ i.1 / (a ^ i.1) ^ N := by rw [hb₀pow]
      _ = (a ^ N * uS) ^ i.1 / (a ^ i.1) ^ N := by rw [hq]
      _ = (a ^ N) ^ i.1 * uS ^ i.1 / (a ^ i.1) ^ N := by
        rw [mul_pow]
      _ = uS ^ i.1 := by
        have ha : (a ^ i.1) ^ N = (a ^ N) ^ i.1 := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm i.1 N]
        rw [ha, mul_div_cancel_left]
  let x : KummerUnitRoot R S N i u :=
    ⟨x₀, by simpa [uS, map_pow] using hx₀pow⟩
  let p : KummerUnitPoint R S N u := ⟨i, x⟩
  refine ⟨p, ?_⟩
  apply Subtype.ext
  change Additive.ofMul
      ((kummerRepresentative R S N u a p : Sˣ ⧸ Subgroup.zpowers q)) = t.1
  have hrep : kummerRepresentative R S N u a p = b₀ := by
    change a ^ i.1 * (b₀ / a ^ i.1) = b₀
    exact mul_div_cancel (a ^ i.1) b₀
  have hb₀quot : (b₀ : Sˣ ⧸ Subgroup.zpowers q) = b := by
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (b * q ^ (-k)) / b ∈ Subgroup.zpowers q
    rw [mul_div_cancel_left]
    exact zpow_mem (Subgroup.mem_zpowers q) (-k)
  calc
    Additive.ofMul
        ((kummerRepresentative R S N u a p : Sˣ ⧸ Subgroup.zpowers q)) =
      Additive.ofMul (b₀ : Sˣ ⧸ Subgroup.zpowers q) :=
        congrArg (fun w : Sˣ ↦ Additive.ofMul
          (w : Sˣ ⧸ Subgroup.zpowers q)) hrep
    _ = Additive.ofMul (b : Sˣ ⧸ Subgroup.zpowers q) :=
      congrArg Additive.ofMul hb₀quot
    _ = t.1 := hbt

/-- The Kummer description is bijective when the quotient generator has infinite order. -/
lemma kummerPointToTorsion_bijective
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    Function.Bijective (kummerPointToTorsion R S N u q a hq) :=
  ⟨kummerPointToTorsion_injective R S N u q a hq hqinj,
    kummerPointToTorsion_surjective R S N u q a hq⟩

/-- Applying a base-algebra automorphism to a Kummer point applies it to the associated
representative, provided the chosen factor `a` is fixed. -/
lemma kummerRepresentative_map
    (N : ℕ) (u : Rˣ) (a : Sˣ) (σ : S ≃ₐ[R] S)
    (ha : Units.map σ.toRingEquiv.toMonoidHom a = a)
    (x : KummerUnitPoint R S N u) :
    kummerRepresentative R S N u a
        (kummerUnitPointMap R S N u σ x) =
      Units.map σ.toRingEquiv.toMonoidHom
        (kummerRepresentative R S N u a x) := by
  rcases x with ⟨i, x⟩
  change a ^ i.1 * Units.map σ.toRingEquiv.toMonoidHom x.1 =
    Units.map σ.toRingEquiv.toMonoidHom (a ^ i.1 * x.1)
  have hapow : Units.map σ.toRingEquiv.toMonoidHom (a ^ i.1) = a ^ i.1 := by
    calc
      _ = (Units.map σ.toRingEquiv.toMonoidHom a) ^ i.1 := map_pow _ _ i.1
      _ = _ := congrArg (fun w : Sˣ ↦ w ^ i.1) ha
  calc
    a ^ i.1 * Units.map σ.toRingEquiv.toMonoidHom x.1 =
        Units.map σ.toRingEquiv.toMonoidHom (a ^ i.1) *
          Units.map σ.toRingEquiv.toMonoidHom x.1 :=
      congrArg (fun w : Sˣ ↦ w * Units.map σ.toRingEquiv.toMonoidHom x.1) hapow.symm
    _ = _ := (map_mul (Units.map σ.toRingEquiv.toMonoidHom) (a ^ i.1) x.1).symm

/-- The Kummer-to-torsion bijection intertwines automorphisms with the induced action on
the quotient by `q^ℤ`. -/
lemma kummerPointToTorsion_map
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (σ : S ≃ₐ[R] S)
    (hqσ : Units.map σ.toRingEquiv.toMonoidHom q = q)
    (haσ : Units.map σ.toRingEquiv.toMonoidHom a = a)
    (x : KummerUnitPoint R S N u) :
    kummerPointToTorsion R S N u q a hq
        (kummerUnitPointMap R S N u σ x) =
      QuotientGroup.torsionMapFixingGenerator q N
        (Units.map σ.toRingEquiv.toMonoidHom) hqσ
        (kummerPointToTorsion R S N u q a hq x) := by
  apply Subtype.ext
  rw [QuotientGroup.torsionMapFixingGenerator_coe]
  change Additive.ofMul
      ((kummerRepresentative R S N u a
          (kummerUnitPointMap R S N u σ x) :
        Sˣ ⧸ Subgroup.zpowers q)) =
    Additive.ofMul
      (QuotientGroup.mapFixingGenerator q
        (Units.map σ.toRingEquiv.toMonoidHom) hqσ
        (kummerRepresentative R S N u a x :
          Sˣ ⧸ Subgroup.zpowers q))
  rw [QuotientGroup.mapFixingGenerator_mk]
  exact congrArg (fun w : Sˣ ↦ Additive.ofMul
    (w : Sˣ ⧸ Subgroup.zpowers q))
      (kummerRepresentative_map R S N u a σ haσ x)

end QuotientTorsion

section GenericFiber

variable (R : Type u) [CommRing R]
variable (K : Type u) [CommRing K] [Algebra R K]
variable (S : Type v) [Field S]
  [Algebra R S] [Algebra K S] [IsScalarTower R K S]

/-- A geometric point of the generic fiber, interpreted as quotient torsion. -/
noncomputable def genericFiberPointToTorsion
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (φ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    AddSubgroup.torsionBy (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) :=
  kummerPointToTorsion R S N u q a hq
    (genericFiberAlgHomUnitEquiv R K S N u φ)

/-- Convolution of generic-fiber points becomes addition of quotient-torsion classes. -/
lemma genericFiberPointToTorsion_convMul
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (φ ψ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    genericFiberPointToTorsion R K S N u q a hq
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      genericFiberPointToTorsion R K S N u q a hq φ +
        genericFiberPointToTorsion R K S N u q a hq ψ := by
  rw [genericFiberPointToTorsion,
    genericFiberAlgHomUnitEquiv_convMul,
    kummerPointToTorsion_mul]
  rfl

/-- The quotient-torsion interpretation of generic-fiber points is Galois equivariant. -/
lemma genericFiberPointToTorsion_comp
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (σ : S ≃ₐ[K] S)
    (hqσ : Units.map σ.toRingEquiv.toMonoidHom q = q)
    (haσ : Units.map σ.toRingEquiv.toMonoidHom a = a)
    (φ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    genericFiberPointToTorsion R K S N u q a hq (σ.toAlgHom.comp φ) =
      QuotientGroup.torsionMapFixingGenerator q N
        (Units.map σ.toRingEquiv.toMonoidHom) hqσ
        (genericFiberPointToTorsion R K S N u q a hq φ) := by
  rw [genericFiberPointToTorsion,
    genericFiberAlgHomUnitEquiv_comp]
  exact kummerPointToTorsion_map R S N u q a hq
    (σ.restrictScalars R) hqσ haσ
      (genericFiberAlgHomUnitEquiv R K S N u φ)

/-- The quotient-torsion interpretation as an additive homomorphism on convolution
points. -/
noncomputable def genericFiberToTorsionAddHom
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q) :
    Additive (WithConv
      (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)) →+
        AddSubgroup.torsionBy
          (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) where
  toFun φ := genericFiberPointToTorsion R K S N u q a hq φ.toMul.ofConv
  map_zero' := by
    let φ₁ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S :=
      (1 : WithConv
        (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)).ofConv
    have h := genericFiberPointToTorsion_convMul R K S N u q a hq
      φ₁ φ₁
    have hmul : (WithConv.toConv φ₁ * WithConv.toConv φ₁).ofConv = φ₁ := by
      change (1 * 1 : WithConv
        (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)).ofConv =
          (1 : WithConv
            (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)).ofConv
      exact congrArg WithConv.ofConv (one_mul (1 : WithConv
        (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)))
    rw [hmul] at h
    change genericFiberPointToTorsion R K S N u q a hq φ₁ = 0
    exact add_left_cancel (a :=
      genericFiberPointToTorsion R K S N u q a hq φ₁) (by
        calc
          genericFiberPointToTorsion R K S N u q a hq φ₁ +
              genericFiberPointToTorsion R K S N u q a hq φ₁ =
            genericFiberPointToTorsion R K S N u q a hq φ₁ := h.symm
          _ = genericFiberPointToTorsion R K S N u q a hq φ₁ + 0 :=
            (add_zero _).symm)
  map_add' φ ψ :=
    genericFiberPointToTorsion_convMul R K S N u q a hq
      φ.toMul.ofConv ψ.toMul.ofConv

/-- The additive map from generic-fiber points to quotient torsion is bijective. -/
lemma genericFiberToTorsionAddHom_bijective
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    Function.Bijective (genericFiberToTorsionAddHom R K S N u q a hq) := by
  let e := genericFiberAlgHomUnitEquiv R K S N u
  have hK := kummerPointToTorsion_bijective R S N u q a hq hqinj
  constructor
  · intro x y hxy
    have hpoint : e x.toMul.ofConv = e y.toMul.ofConv := hK.1 hxy
    have halg : x.toMul.ofConv = y.toMul.ofConv := e.injective hpoint
    simpa using congrArg Additive.ofMul (congrArg WithConv.toConv halg)
  · intro t
    obtain ⟨p, hp⟩ := hK.2 t
    obtain ⟨φ, hφ⟩ := e.surjective p
    refine ⟨Additive.ofMul (WithConv.toConv φ), ?_⟩
    change kummerPointToTorsion R S N u q a hq (e φ) = t
    rw [hφ, hp]

/-- Geometric points of the Tate--Kummer generic fiber are additively equivalent to the
`N`-torsion of `Sˣ/q^ℤ`. -/
noncomputable def genericFiberTorsionAddEquiv
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    Additive (WithConv
      (K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy
          (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) :=
  AddEquiv.ofBijective (genericFiberToTorsionAddHom R K S N u q a hq)
    (genericFiberToTorsionAddHom_bijective R K S N u q a hq hqinj)

/-- Galois equivariance of the additive equivalence between generic-fiber points and
quotient torsion. -/
lemma genericFiberTorsionAddEquiv_comp
    (N : ℕ) [NeZero N] (u : Rˣ) (q a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z)
    (σ : S ≃ₐ[K] S)
    (hqσ : Units.map σ.toRingEquiv.toMonoidHom q = q)
    (haσ : Units.map σ.toRingEquiv.toMonoidHom a = a)
    (φ : K ⊗[R] CoordinateAlgebra (R := R) N u →ₐ[K] S) :
    genericFiberTorsionAddEquiv R K S N u q a hq hqinj
        (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) =
      QuotientGroup.torsionMapFixingGenerator q N
        (Units.map σ.toRingEquiv.toMonoidHom) hqσ
        (genericFiberTorsionAddEquiv R K S N u q a hq hqinj
          (Additive.ofMul (WithConv.toConv φ))) := by
  change genericFiberPointToTorsion R K S N u q a hq
      (σ.toAlgHom.comp φ) =
    QuotientGroup.torsionMapFixingGenerator q N
      (Units.map σ.toRingEquiv.toMonoidHom) hqσ
      (genericFiberPointToTorsion R K S N u q a hq φ)
  exact genericFiberPointToTorsion_comp R K S N u q a hq σ hqσ haσ φ

end GenericFiber

end TateKummer
