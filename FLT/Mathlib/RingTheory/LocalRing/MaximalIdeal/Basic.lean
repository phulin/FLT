/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Basic

Material destined for Mathlib.
-/

@[expose] public section

theorem IsLocalRing.maximalIdeal_le {R : Type*} [CommSemiring R] [IsLocalRing R] {J : Ideal R}
    (hJ : J ≠ ⊤) (h : IsLocalRing.maximalIdeal R ≤ J) :
    J.IsMaximal :=
  (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hJ h ▸ IsLocalRing.maximalIdeal.isMaximal R

/-- A root of unity whose order is a unit cannot specialize to `1` without already being
`1`.  Equivalently, the prime-to-residue-character roots of unity inject into the residue
field of a local ring. -/
theorem IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {x : R} {n : ℕ}
    (hn : IsUnit (n : R)) (hpow : x ^ n = 1)
    (hx : x - 1 ∈ IsLocalRing.maximalIdeal R) : x = 1 := by
  let s : R := ∑ i ∈ Finset.range n, x ^ i
  have hresx : IsLocalRing.residue R x = 1 := by
    rw [← sub_eq_zero, ← map_one (IsLocalRing.residue R), ← map_sub,
      IsLocalRing.residue_eq_zero_iff]
    exact hx
  have hress : IsLocalRing.residue R s = IsLocalRing.residue R (n : R) := by
    simp [s, hresx]
  have hresn : IsLocalRing.residue R (n : R) ≠ 0 :=
    (hn.map (IsLocalRing.residue R)).ne_zero
  have hsunit : IsUnit s := IsLocalRing.notMem_maximalIdeal.mp fun hs ↦ by
    have hs0 := (IsLocalRing.residue_eq_zero_iff s).2 hs
    rw [hress] at hs0
    exact hresn hs0
  have hmul : (x - 1) * s = 0 := by
    change (x - 1) * (∑ i ∈ Finset.range n, x ^ i) = 0
    rw [mul_geom_sum, hpow, sub_self]
  have hx0 : x - 1 = 0 := by
    apply hsunit.mul_right_cancel
    simpa using hmul
  exact sub_eq_zero.mp hx0

/-- Two unit-valued `n`-th roots which have the same reduction are equal when `n` is a unit.

This is the form of Hensel uniqueness needed for tame Kummer extensions: divide the two roots,
then use injectivity of prime-to-residue-characteristic roots of unity under reduction. -/
theorem IsLocalRing.eq_of_pow_eq_pow_of_isUnit_of_sub_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {x y : R} {n : ℕ}
    (hn : IsUnit (n : R)) (hy : IsUnit y) (hpow : x ^ n = y ^ n)
    (hxy : x - y ∈ IsLocalRing.maximalIdeal R) : x = y := by
  let u : Rˣ := hy.unit
  have hu : (u : R) = y := hy.unit_spec
  let z : R := x * (↑(u⁻¹) : R)
  have hzpow : z ^ n = 1 := by
    rw [show z = x * (↑(u⁻¹) : R) from rfl, mul_pow, hpow, ← hu,
      ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    rw [← Units.val_mul]
    simp
  have hzmem : z - 1 ∈ IsLocalRing.maximalIdeal R := by
    have hz : z - 1 = (x - y) * (↑(u⁻¹) : R) := by
      simp [z, sub_mul, ← hu]
    rw [hz]
    exact (IsLocalRing.maximalIdeal R).mul_mem_right _ hxy
  have hzone : z = 1 :=
    IsLocalRing.eq_one_of_pow_eq_one_of_sub_one_mem_maximalIdeal hn hzpow hzmem
  calc
    x = (x * (↑(u⁻¹) : R)) * (u : R) := by simp
    _ = z * (u : R) := rfl
    _ = 1 * (u : R) := by rw [hzone]
    _ = y := by simpa using hu
