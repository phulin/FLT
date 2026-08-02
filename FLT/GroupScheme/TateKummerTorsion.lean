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

end QuotientTorsion

end TateKummer
