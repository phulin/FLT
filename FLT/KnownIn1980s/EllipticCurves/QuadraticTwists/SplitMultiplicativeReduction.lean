/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Claude
-/
module

public import FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists
public import FLT.Mathlib.Algebra.Algebra.Equiv
public import FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
public import FLT.Mathlib.RingTheory.Norm.Quotient
public import Mathlib.RingTheory.Henselian

import FLT.Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Localization.NormTrace

/-!
# Multiplicative reduction becomes split after a quadratic twist

Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of integers
of a nonarchimedean local field), and let `E` be an elliptic curve over `K` with multiplicative
reduction. This file proves that if the reduction is *nonsplit*, then the quadratic twist of `E`
(`FLT.KnownIn1980s.EllipticCurves.QuadraticTwists.QuadraticTwists`) by the unramified quadratic
extension of `K` (`FLT.Mathlib.RingTheory.Unramified.LocalRing`) has
*split* multiplicative reduction: the reduction of the twist is the same nodal cubic with the
Galois action on the two tangent directions at the node twisted into triviality.

## Main definitions and statements

* `WeierstrassCurve.exists_quadraticTwist_hasSplitMultiplicativeReduction` : over the fraction
  field of a discrete valuation ring, an elliptic curve with nonsplit multiplicative reduction
  has a quadratic twist with split multiplicative reduction.

The generic ingredients — the node polynomial `WeierstrassCurve.nodePoly` with its splitting
criteria, and the invariance of split multiplicative reduction under isomorphism of minimal
models (`WeierstrassCurve.HasSplitMultiplicativeReduction.of_isMinimal_smul`) — are in
`FLT.Mathlib.AlgebraicGeometry.EllipticCurve.Reduction` and
`FLT.Mathlib.Algebra.QuadraticDiscriminant`.

## TODO

* Behaviour of reduction types under twisting in general: over the fraction field of a DVR, an
  unramified quadratic twist preserves good and multiplicative reduction (exchanging split and
  nonsplit), while a ramified quadratic twist of a curve with good or multiplicative reduction
  has additive reduction (at least in residue characteristic ≠ 2).
* Compatibility with the Tate curve (`FLT.KnownIn1980s.EllipticCurves.TateCurve`): for `E` with
  nonsplit multiplicative reduction over a nonarchimedean local field, the Galois representation
  of `E` is the unramified quadratic twist of the Tate-curve representation of its split twist.
  This is the main FLT-facing application of this file together with
  `exists_quadraticTwist_hasSplitMultiplicativeReduction`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VII.§1 and VII.§5
* [J.-P. Serre, *Propriétés galoisiennes des points d'ordre fini des courbes elliptiques*],
  §5.3 (for the interaction of twists with reduction types)
-/

@[expose] public section

open Polynomial IsLocalRing in
/-- In residue characteristic `2`, a quadratic with unit leading and linear coefficients has an
actual root if it splits after reduction.  A reduced root is simple because the linear coefficient
is a unit, so Hensel's lemma lifts it. -/
lemma exists_root_quadratic_of_splits_residue_of_two_eq_zero
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (A B q : R)
    (hA : IsUnit A) (hB : IsUnit B) (h2 : residue R (2 : R) = 0)
    (hs : ((C A * X ^ 2 + C B * X + C q).map (residue R)).Splits) :
    ∃ x : R, A * x ^ 2 + B * x + q = 0 := by
  let Au : Rˣ := hA.unit
  have hAu : (Au : R) = A := hA.unit_spec
  let g : R[X] := C A * X ^ 2 + C B * X + C q
  let f : R[X] := X ^ 2 + C ((↑(Au⁻¹) : R) * B) * X + C ((↑(Au⁻¹) : R) * q)
  have hf : f.Monic := by
    dsimp only [f]
    rw [show X ^ 2 + C ((↑(Au⁻¹) : R) * B) * X + C ((↑(Au⁻¹) : R) * q) =
      X ^ 2 + (C ((↑(Au⁻¹) : R) * B) * X + C ((↑(Au⁻¹) : R) * q)) by ring]
    apply monic_X_pow_add
    compute_degree!
  have hAres : residue R A ≠ 0 := (residue_ne_zero_iff_isUnit A).mpr hA
  have hgnat : (g.map (residue R)).natDegree = 2 := by
    have hglead : g.leadingCoeff = A := by
      dsimp only [g]
      exact leadingCoeff_quadratic hA.ne_zero
    rw [natDegree_map_of_leadingCoeff_ne_zero (residue R) (by rwa [hglead])]
    dsimp only [g]
    exact natDegree_quadratic hA.ne_zero
  have hg0 : g.map (residue R) ≠ 0 := by
    intro h
    rw [h, natDegree_zero] at hgnat
    norm_num at hgnat
  obtain ⟨z, hz⟩ := hs.exists_eval_eq_zero (by
    rw [degree_eq_natDegree hg0, hgnat]
    norm_num)
  obtain ⟨z₀, hz₀⟩ := residue_surjective z
  have hfroot : f.eval z₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    have hz' : (g.map (residue R)).eval z = 0 := hz
    simp only [g, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X, eval_add, eval_mul, eval_pow, eval_C, eval_X] at hz'
    simp only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C, map_add, map_mul, map_pow,
      hz₀]
    rw [← hAu] at hz'
    have hAuRes0 : residue R (Au : R) ≠ 0 :=
      (residue_ne_zero_iff_isUnit (Au : R)).mpr Au.isUnit
    have hAuResInv : residue R (Au : R) * residue R (↑(Au⁻¹) : R) = 1 := by
      simpa only [map_mul, map_one] using congrArg (residue R) Au.mul_inv
    have hBResCancel : residue R (Au : R) *
        (residue R (↑(Au⁻¹) : R) * residue R B * z) = residue R B * z := by
      rw [show residue R (↑(Au⁻¹) : R) * residue R B * z =
          residue R (↑(Au⁻¹) : R) * (residue R B * z) by ring,
        ← mul_assoc (residue R (Au : R)) (residue R (↑(Au⁻¹) : R)),
        hAuResInv, one_mul]
    apply mul_left_cancel₀ hAuRes0
    rw [mul_zero, mul_add, mul_add]
    calc
      residue R (Au : R) * z ^ 2
            + residue R (Au : R) * (residue R (↑(Au⁻¹) : R) * residue R B * z)
            + residue R (Au : R) * (residue R (↑(Au⁻¹) : R) * residue R q)
          = residue R (Au : R) * z ^ 2 + residue R B * z + residue R q := by
              rw [hBResCancel,
                ← mul_assoc (residue R (Au : R)) (residue R (↑(Au⁻¹) : R)),
                hAuResInv, one_mul]
      _ = 0 := hz'
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval z₀)) := by
    apply IsUnit.map
    rw [← residue_ne_zero_iff_isUnit]
    have hBres : residue R B ≠ 0 := (residue_ne_zero_iff_isUnit B).mpr hB
    have h2' : (2 : ResidueField R) = 0 := by simpa only [map_ofNat] using h2
    have hdeval : f.derivative.eval z₀ = 2 * z₀ + (↑(Au⁻¹) : R) * B := by
      dsimp only [f]
      simp only [derivative_add, derivative_pow, derivative_X, derivative_mul, derivative_C,
        Nat.cast_ofNat, C_0, zero_mul, add_zero, eval_add, eval_mul, eval_C, eval_X,
        Nat.reduceSub, pow_one, eval_zero, zero_add, eval_ofNat, eval_one, mul_one]
    rw [hdeval, map_add, map_mul, map_ofNat, h2', zero_mul, zero_add, map_mul]
    exact mul_ne_zero
      ((residue_ne_zero_iff_isUnit (↑(Au⁻¹) : R)).mpr (Au⁻¹).isUnit) hBres
  obtain ⟨x, hx, -⟩ := HenselianRing.is_henselian f hf z₀ hfroot hderiv
  have hfx : f.eval x = 0 := by rwa [IsRoot.def] at hx
  have hrel : A * x ^ 2 + B * x + q = 0 := by
    simp only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C] at hfx
    have hcancel : (Au : R) * (↑(Au⁻¹) : R) = 1 := by
      exact Au.mul_inv
    have hBcancel : (Au : R) * ((↑(Au⁻¹) : R) * B * x) = B * x := by
      rw [show (↑(Au⁻¹) : R) * B * x = (↑(Au⁻¹) : R) * (B * x) by ring,
        ← mul_assoc (Au : R) (↑(Au⁻¹) : R), hcancel, one_mul]
    have hqcancel : (Au : R) * ((↑(Au⁻¹) : R) * q) = q := by
      rw [← mul_assoc (Au : R) (↑(Au⁻¹) : R), hcancel, one_mul]
    rw [← hAu]
    calc
      (Au : R) * x ^ 2 + B * x + q
          = (Au : R) * (x ^ 2 + (↑(Au⁻¹) : R) * B * x
              + (↑(Au⁻¹) : R) * q) := by rw [mul_add, mul_add, hBcancel, hqcancel]
      _ = 0 := by rw [hfx, mul_zero]
  exact ⟨x, hrel⟩

open Polynomial IsLocalRing in
/-- In residue characteristic `2`, a quadratic with unit leading and linear coefficients has
square discriminant if it splits after reduction.  Lift a root `x` and use
`B² - 4Aq = (2Ax + B)²`. -/
lemma isSquare_discrim_of_splits_residue_of_two_eq_zero
    {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] (A B q : R)
    (hA : IsUnit A) (hB : IsUnit B) (h2 : residue R (2 : R) = 0)
    (hs : ((C A * X ^ 2 + C B * X + C q).map (residue R)).Splits) :
    IsSquare (B ^ 2 - 4 * A * q) := by
  obtain ⟨x, hrel⟩ := exists_root_quadratic_of_splits_residue_of_two_eq_zero
    A B q hA hB h2 hs
  refine ⟨2 * A * x + B, ?_⟩
  have hq : q = -(A * x ^ 2 + B * x) := by linear_combination hrel
  rw [hq]
  ring

namespace WeierstrassCurve

universe u

variable {K : Type u} [Field K] (E : WeierstrassCurve K)

/-! ### Multiplicative reduction becomes split after a quadratic twist -/

section Reduction

-- Let `R` be a discrete valuation ring with fraction field `K` (for example the ring of
-- integers of a nonarchimedean local field). The instances are introduced in stages, as needed.
variable (R : Type u) [CommRing R] [Algebra R K]

open Polynomial IsLocalRing in
/-- A unit of a Henselian local ring whose residue is a square is itself a square, provided the
residue characteristic is not `2`.  This is the elementary `X² - x` case of Hensel's lemma. -/
lemma isSquare_of_isSquare_residue [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] {x : R}
    (h2 : residue R (2 : R) ≠ 0) (hx : residue R x ≠ 0)
    (hs : IsSquare (residue R x)) : IsSquare x := by
  obtain ⟨z, hz⟩ := hs
  obtain ⟨a₀, ha₀⟩ := residue_surjective z
  let f : R[X] := X ^ 2 - C x
  have hf : f.Monic := monic_X_pow_sub_C x (by omega)
  have hroot : f.eval a₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp only [f, eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, ha₀]
    rw [hz, pow_two, sub_self]
  have ha₀0 : residue R a₀ ≠ 0 := by
    rw [ha₀]
    intro hz0
    apply hx
    rw [hz, hz0, zero_mul]
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval a₀)) := by
    rw [residue_ne_zero_iff_isUnit] at h2 ha₀0
    have hu : IsUnit (f.derivative.eval a₀) := by
      simpa only [f, derivative_sub, derivative_pow, derivative_X, derivative_C, Nat.cast_ofNat,
        C_0, sub_zero, eval_mul, eval_C, eval_X, Nat.reduceSub, pow_one, eval_one,
        mul_one] using h2.mul ha₀0
    exact hu.map (Ideal.Quotient.mk (maximalIdeal R))
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf a₀ hroot hderiv
  refine ⟨a, ?_⟩
  rw [IsRoot.def] at ha
  simp only [f, eval_sub, eval_pow, eval_X, eval_C] at ha
  simpa only [pow_two] using (sub_eq_zero.mp ha).symm

open Polynomial IsLocalRing in
/-- If an integral generator of a quadratic extension has nonzero reduced trace in residue
characteristic `2`, then its reduced characteristic polynomial is irreducible.  In
Artin--Schreier form this says that `n̄ / t̄²` is not of the form `z² + z`.

Indeed, a solution of the reduced Artin--Schreier equation gives a simple root of
`X² - tX + n` modulo the maximal ideal. Hensel's lemma lifts it to a root in the fraction field;
the rank-two Cayley--Hamilton identity then forces the given generator to lie in the base field. -/
lemma not_exists_artinSchreier_residue_of_quadratic_generator [IsLocalRing R]
    [HenselianRing R (maximalIdeal R)] {L : Type*} [Field L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L] {θ : L} (hθ : θ ∉ Set.range (algebraMap K L))
    (t n : R) (htr : Algebra.trace K L θ = algebraMap R K t)
    (hnr : Algebra.norm K θ = algebraMap R K n)
    (h2 : (2 : ResidueField R) = 0) (ht : residue R t ≠ 0) :
    ¬ ∃ z : ResidueField R, residue R t ^ 2 * (z ^ 2 + z) = residue R n := by
  rintro ⟨z, hz⟩
  obtain ⟨a₀, ha₀⟩ := residue_surjective (residue R t * z)
  let f : R[X] := X ^ 2 - C t * X + C n
  have hf : f.Monic := by
    dsimp [f]
    rw [show X ^ 2 - C t * X + C n = X ^ 2 + (-C t * X + C n) by ring]
    exact monic_X_pow_add (by compute_degree!)
  have hroot : f.eval a₀ ∈ maximalIdeal R := by
    rw [← residue_eq_zero_iff]
    simp only [f, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C, map_add,
      map_sub, map_mul, map_pow, ha₀]
    linear_combination hz + (residue R n - residue R t ^ 2 * z) * h2
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval a₀)) := by
    have hderivEval : f.derivative.eval a₀ = 2 * a₀ - t := by
      simp [f]
      ring
    have hderivRes : residue R (f.derivative.eval a₀) ≠ 0 := by
      rw [hderivEval, map_sub, map_mul, map_ofNat, h2, zero_mul, zero_sub]
      exact neg_ne_zero.mpr ht
    exact ((residue_ne_zero_iff_isUnit _).mp hderivRes).map
      (Ideal.Quotient.mk (maximalIdeal R))
  obtain ⟨a, ha, -⟩ := HenselianRing.is_henselian f hf a₀ hroot hderiv
  rw [IsRoot.def] at ha
  simp only [f, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at ha
  have haK := congrArg (algebraMap R K) ha
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at haK
  have hθpoly := sq_sub_trace_mul_self_add_norm
    (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
  rw [htr, hnr] at hθpoly
  have haL := congrArg (algebraMap K L) haK
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at haL
  have hfac :
      (θ - algebraMap K L (algebraMap R K a)) *
        (θ - algebraMap K L (algebraMap R K t - algebraMap R K a)) = 0 := by
    simp only [map_sub]
    linear_combination hθpoly - haL
  rcases mul_eq_zero.mp hfac with haθ | haθ
  · exact hθ ⟨algebraMap R K a, (sub_eq_zero.mp haθ).symm⟩
  · exact hθ ⟨algebraMap R K t - algebraMap R K a, (sub_eq_zero.mp haθ).symm⟩

/-- The field-level Artin--Schreier class attached to a generator of a separable quadratic
extension in characteristic `2` is nontrivial.  If
`tr(θ)² (z² + z) = N(θ)`, then `tr(θ) z` is a root of the characteristic polynomial of
`θ`.  Factoring the rank-two Cayley--Hamilton identity therefore puts `θ` in the base field. -/
lemma not_exists_artinSchreier_of_quadratic_generator
    {L : Type*} [Field L] [Algebra K L] [Algebra.IsQuadraticExtension K L]
    {θ : L} (hθ : θ ∉ Set.range (algebraMap K L)) (h2 : (2 : K) = 0) :
    ¬ ∃ z : K, Algebra.trace K L θ ^ 2 * (z ^ 2 + z) = Algebra.norm K θ := by
  rintro ⟨z, hz⟩
  let t : K := Algebra.trace K L θ
  let n : K := Algebra.norm K θ
  have ha : (t * z) ^ 2 - t * (t * z) + n = 0 := by
    dsimp only [t, n]
    linear_combination -hz + Algebra.trace K L θ ^ 2 * z ^ 2 * h2
  have hθpoly := sq_sub_trace_mul_self_add_norm
    (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
  have haL := congrArg (algebraMap K L) ha
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at haL
  have hfac :
      (θ - algebraMap K L (t * z)) *
        (θ - algebraMap K L (t - t * z)) = 0 := by
    simp only [map_sub, map_mul]
    dsimp only [t, n] at haL ⊢
    linear_combination hθpoly - haL
  rcases mul_eq_zero.mp hfac with haθ | haθ
  · exact hθ ⟨t * z, (sub_eq_zero.mp haθ).symm⟩
  · exact hθ ⟨t - t * z, (sub_eq_zero.mp haθ).symm⟩

open Polynomial in
/-- **Twisting flips the square class (residue characteristic ≠ 2).** Combining the split criterion
`nodePoly_map_splits_iff_isSquare` with the coefficient scaling of the quadratic twist
(`c₄_quadraticTwistOf`, `c₆_quadraticTwistOf`), the node polynomial of `W.quadraticTwistOf t n`
splits over a field `k` of characteristic `≠ 2` exactly when `D · (-c₄ c₆)` is a square there, where
`D = t² - 4n`. Thus twisting multiplies the square class governing splitting by `D`: it converts a
nonsplit reduction into a split one precisely when `D` and `-c₄ c₆` lie in the same square class. -/
lemma nodePoly_quadraticTwistOf_map_splits_iff {A : Type*} [CommRing A] {k : Type*} [Field k]
    [NeZero (2 : k)] (φ : A →+* k) (W : WeierstrassCurve A) (t n : A) (hc₄ : φ W.c₄ ≠ 0)
    (hD : φ (t ^ 2 - 4 * n) ≠ 0) :
    ((W.quadraticTwistOf t n).nodePoly.map φ).Splits
      ↔ IsSquare (φ ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆))) := by
  have key : ∀ s y : k, s ≠ 0 → (IsSquare (s ^ 2 * y) ↔ IsSquare y) := fun s y hs ↦
    ⟨fun ⟨w, hw⟩ ↦ ⟨w / s, by field_simp; linear_combination hw⟩,
      fun ⟨w, hw⟩ ↦ ⟨s * w, by rw [hw]; ring⟩⟩
  have hc₄' : φ (W.quadraticTwistOf t n).c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, map_mul, map_pow]; exact mul_ne_zero (pow_ne_zero 2 hD) hc₄
  rw [nodePoly_map_splits_iff_isSquare φ (W.quadraticTwistOf t n) hc₄',
    show -((W.quadraticTwistOf t n).c₄ * (W.quadraticTwistOf t n).c₆)
        = ((t ^ 2 - 4 * n) ^ 2) ^ 2 * ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆)) from by
      rw [c₄_quadraticTwistOf, c₆_quadraticTwistOf]; ring,
    map_mul, map_pow,
    key _ _ (show φ ((t ^ 2 - 4 * n) ^ 2) ≠ 0 by rw [map_pow]; exact pow_ne_zero 2 hD)]

/-- **A nonsquare unit twist flips a split node to a nonsplit node (residue characteristic
`≠ 2`).**  If the node polynomial of `W` splits and the discriminant `D = t² - 4n` of the
quadratic twisting datum is nonzero and nonsquare after applying `φ`, then the node polynomial
of `W.quadraticTwistOf t n` does not split.

This is the converse-facing form of `nodePoly_quadraticTwistOf_map_splits_iff`: splitting of
the original node says `-(c₄c₆)` is a square, while splitting after twisting would say that
`D · -(c₄c₆)` is a square.  Since the former square is nonzero, division would make `D` a
square, contradicting the twisting hypothesis. -/
lemma not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_isSquare
    {A : Type*} [CommRing A] {k : Type*} [Field k] [NeZero (2 : k)]
    (φ : A →+* k) (W : WeierstrassCurve A) (t n : A)
    (hc₄ : φ W.c₄ ≠ 0) (hc₆ : φ W.c₆ ≠ 0)
    (hD : φ (t ^ 2 - 4 * n) ≠ 0)
    (hsplit : (W.nodePoly.map φ).Splits)
    (hDnsq : ¬ IsSquare (φ (t ^ 2 - 4 * n))) :
    ¬ ((W.quadraticTwistOf t n).nodePoly.map φ).Splits := by
  intro htwist
  have hs : IsSquare (φ (-(W.c₄ * W.c₆))) :=
    (nodePoly_map_splits_iff_isSquare φ W hc₄).mp hsplit
  have hDs : IsSquare (φ ((t ^ 2 - 4 * n) * -(W.c₄ * W.c₆))) :=
    (nodePoly_quadraticTwistOf_map_splits_iff φ W t n hc₄ hD).mp htwist
  obtain ⟨s, hs⟩ := hs
  obtain ⟨z, hz⟩ := hDs
  have hs0 : s ≠ 0 := by
    intro hs0
    have : φ (-(W.c₄ * W.c₆)) = 0 := by rw [hs, hs0, zero_mul]
    apply mul_ne_zero hc₄ hc₆
    simpa only [map_neg, map_mul, neg_eq_zero] using this
  apply hDnsq
  refine ⟨z / s, ?_⟩
  rw [div_mul_div_comm]
  apply (eq_div_iff (mul_ne_zero hs0 hs0)).mpr
  rw [← hs, ← hz, map_mul]

/-- **An irreducible Artin--Schreier twist flips a split node to a nonsplit node (residue
characteristic `2`).**  If `φ(t) ≠ 0`, the reduced quadratic twisting polynomial is
`X² + φ(t)X + φ(n)`.  Its irreducibility is expressed by saying that
`φ(n) / φ(t)²` is not in the image of `z ↦ z² + z`.  If both the original and twisted node
polynomials split, their Artin--Schreier splitting equations differ by exactly this class,
giving a root of the twisting polynomial and a contradiction. -/
lemma not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_exists_artinSchreier
    {A : Type*} [CommRing A] {k : Type*} [Field k]
    (h2 : (2 : k) = 0) (φ : A →+* k) (W : WeierstrassCurve A) (t n : A)
    (hc₄ : φ W.c₄ ≠ 0) (hc₆ : φ W.c₆ ≠ 0) (ht : φ t ≠ 0)
    (hsplit : (W.nodePoly.map φ).Splits)
    (hAS : ¬ ∃ z : k, φ t ^ 2 * (z ^ 2 + z) = φ n) :
    ¬ ((W.quadraticTwistOf t n).nodePoly.map φ).Splits := by
  intro htwist
  have h4 : (4 : k) = 0 := by linear_combination (2 : k) * h2
  have hDmap : φ (t ^ 2 - 4 * n) = φ t ^ 2 := by
    simp only [map_sub, map_pow, map_mul, map_ofNat, h4, zero_mul, sub_zero]
  have hc₄twist : φ (W.quadraticTwistOf t n).c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, map_mul, map_pow, hDmap]
    exact mul_ne_zero (pow_ne_zero 2 (pow_ne_zero 2 ht)) hc₄
  have hc₆twist : φ (W.quadraticTwistOf t n).c₆ ≠ 0 := by
    rw [c₆_quadraticTwistOf, map_mul, map_pow, hDmap]
    exact mul_ne_zero (pow_ne_zero 3 (pow_ne_zero 2 ht)) hc₆
  obtain ⟨z₀, hz₀⟩ :=
    (nodePoly_map_splits_iff_of_two_eq_zero h2 φ W hc₄ hc₆).mp hsplit
  obtain ⟨z₁, hz₁⟩ := (nodePoly_map_splits_iff_of_two_eq_zero h2 φ
    (W.quadraticTwistOf t n) hc₄twist hc₆twist).mp htwist
  rw [show (W.quadraticTwistOf t n).a₁ = t * W.a₁ from rfl,
    kappa_quadraticTwistOf, c₄_quadraticTwistOf] at hz₁
  simp only [map_mul, map_pow, map_sub, map_neg, map_ofNat, h4, zero_mul, sub_zero] at hz₁
  have hA : φ (W.a₁ * W.c₄) ≠ 0 := by
    have hdisc := map_splitPolynomial_discrim φ W
    intro hA
    refine neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆) ?_
    rw [← map_mul, ← map_neg]
    linear_combination -hdisc + φ (W.a₁ * W.c₄) * hA
      + φ W.c₄ * φ (54 * W.b₆ - 3 * W.b₂ * W.b₄ + W.a₂ * W.c₄) * h4
  have hASsub : (z₁ + z₀) ^ 2 + (z₁ + z₀) =
      (z₁ ^ 2 + z₁) - (z₀ ^ 2 + z₀) := by
    linear_combination (z₁ * z₀ + z₀ ^ 2 + z₀) * h2
  simp only [map_mul] at hz₀ hA
  apply hAS
  refine ⟨z₁ + z₀, ?_⟩
  rw [hASsub]
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 8 ht) (pow_ne_zero 2 hA))
  linear_combination hz₁ - φ t ^ 10 * hz₀

/-- The `R`-model twist base-changes to the twist over `K`: for `E` integral over `R`, twisting its
integral model by `t, n : R` and base-changing to `K` equals twisting `E` by the images
`(algebraMap R K t, algebraMap R K n)`. Together with the coefficient laws this is the bridge from
the `K`-twist `E.quadraticTwist L` to a genuine `R`-model whose reduction can be computed. -/
theorem baseChange_integralModel_quadraticTwistOf [IsIntegral R E] (t n : R) :
    ((E.integralModel R).quadraticTwistOf t n)⁄K
      = E.quadraticTwistOf (algebraMap R K t) (algebraMap R K n) := by
  change ((E.integralModel R).quadraticTwistOf t n).map (algebraMap R K) = _
  rw [quadraticTwistOf_map, show (E.integralModel R).map (algebraMap R K) = E
    from baseChange_integralModel_eq R E]

variable [IsFractionRing R K]

variable [IsDomain R]

/-- The base change of the twisted integral model has nonzero discriminant: its `Δ` is
`(t'² - 4n')⁶ · Δ` (`Δ_quadraticTwistOf`), and both factors are nonzero. -/
theorem Δ_baseChange_quadraticTwistOf_ne_zero [E.IsElliptic] [IsIntegral R E] (t' n' : R)
    (hD : t' ^ 2 - 4 * n' ≠ 0) :
    ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ ≠ 0 := by
  have hΔint : (E.integralModel R).Δ ≠ 0 := fun h0 ↦
    E.isUnit_Δ.ne_zero (by rw [← integralModel_Δ_eq R E, h0, map_zero])
  rw [show ((((E.integralModel R).quadraticTwistOf t' n'))⁄K).Δ
    = algebraMap R K ((E.integralModel R).quadraticTwistOf t' n').Δ from map_Δ _ _,
    Δ_quadraticTwistOf, Ne, map_eq_zero_iff _ (IsFractionRing.injective R K), mul_eq_zero]
  exact not_or.mpr ⟨pow_ne_zero 6 hD, hΔint⟩

-- From here on, `R` is a discrete valuation ring.
variable [IsDiscreteValuationRing R]

open IsLocalRing in
/-- In residue characteristic `2`, multiplicative reduction forces the `a₁` coefficient of the
integral model to be a unit.  The reduced node-polynomial discriminant identity becomes
`(a₁c₄)² = -c₄c₆`, and `c₄,c₆` are both nonzero. -/
lemma isUnit_integralModel_a₁_of_two_residue_eq_zero [E.HasMultiplicativeReduction R]
    (h2 : (2 : ResidueField R) = 0) : IsUnit (E.integralModel R).a₁ := by
  let I := E.integralModel R
  have hc₄ : residue R I.c₄ ≠ 0 := by
    dsimp only [I]
    exact residue_integralModel_c₄_ne_zero E R
  have hc₆ : residue R I.c₆ ≠ 0 := by
    dsimp only [I]
    exact residue_integralModel_c₆_ne_zero E R
  have h4 : (4 : ResidueField R) = 0 := by
    rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, zero_mul]
  apply (residue_ne_zero_iff_isUnit I.a₁).mp
  intro ha₁
  have hdisc := map_splitPolynomial_discrim (residue R) I
  have hzero : -(residue R I.c₄ * residue R I.c₆) = 0 := by
    simpa only [map_mul, ha₁, zero_mul, zero_pow (by norm_num : 2 ≠ 0), map_ofNat,
      h4, map_neg, mul_zero, sub_zero] using hdisc.symm
  exact (neg_ne_zero.mpr (mul_ne_zero hc₄ hc₆)) hzero

open Polynomial IsLocalRing in
/-- For split multiplicative reduction in residue characteristic `2`, the discriminant
`-c₄c₆` of the node polynomial is already a square in the discrete valuation ring.  This is
stronger than merely being a square after reduction: a tangent direction lifts by Hensel's lemma. -/
lemma isSquare_neg_c₄_mul_c₆_integralModel_of_two_residue_eq_zero
    [HenselianRing R (maximalIdeal R)] [E.HasSplitMultiplicativeReduction R]
    (h2 : (2 : ResidueField R) = 0) :
    IsSquare (-((E.integralModel R).c₄ * (E.integralModel R).c₆)) := by
  let I := E.integralModel R
  let κ := 54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄
  have hc₄ : IsUnit I.c₄ := by
    apply (residue_ne_zero_iff_isUnit I.c₄).mp
    dsimp only [I]
    exact residue_integralModel_c₄_ne_zero E R
  have ha₁ : IsUnit I.a₁ := by
    dsimp only [I]
    exact isUnit_integralModel_a₁_of_two_residue_eq_zero E R h2
  have hs : ((C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X + C (-κ)).map (residue R)).Splits := by
    simpa only [I, κ, C_neg, sub_eq_add_neg, ResidueField.algebraMap_eq] using
      (HasSplitMultiplicativeReduction.splitMultiplicativeReduction (R := R) (W := E))
  have hsq := isSquare_discrim_of_splits_residue_of_two_eq_zero
    I.c₄ (I.a₁ * I.c₄) (-κ) hc₄ (ha₁.mul hc₄) (by
      simpa only [map_ofNat] using h2) hs
  convert hsq using 1
  dsimp only [κ]
  rw [show (I.a₁ * I.c₄) ^ 2 - 4 * I.c₄ *
      (-(54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄)) =
      (I.a₁ * I.c₄) ^ 2 + 4 * I.c₄ *
        (54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄) by ring]
  exact I.splitPolynomial_discrim.symm

open Polynomial IsLocalRing in
/-- In residue characteristic `2`, `c₄` of a multiplicative integral model is a square.  Write
`c₄ = b₂² - 24b₄`; the polynomial `Y² + b₂Y + 6b₄` has the simple reduced root `0`
because `b₂ ≡ a₁²` is a unit.  If `y` is its Hensel lift, then `(b₂ + 2y)² = c₄`. -/
lemma isSquare_c₄_integralModel_of_two_residue_eq_zero
    [HenselianRing R (maximalIdeal R)] [E.HasMultiplicativeReduction R]
    (h2 : (2 : ResidueField R) = 0) : IsSquare (E.integralModel R).c₄ := by
  let I := E.integralModel R
  have ha₁ : IsUnit I.a₁ := by
    dsimp only [I]
    exact isUnit_integralModel_a₁_of_two_residue_eq_zero E R h2
  have h4 : (4 : ResidueField R) = 0 := by
    rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, zero_mul]
  have hb₂ : IsUnit I.b₂ := by
    apply (residue_ne_zero_iff_isUnit I.b₂).mp
    simp only [b₂, map_add, map_pow, map_mul, map_ofNat, h4, zero_mul, add_zero]
    exact pow_ne_zero 2 ((residue_ne_zero_iff_isUnit I.a₁).mpr ha₁)
  let f : R[X] := X ^ 2 + C I.b₂ * X + C (6 * I.b₄)
  have hf : f.Monic := by
    dsimp only [f]
    rw [show X ^ 2 + C I.b₂ * X + C (6 * I.b₄) =
      X ^ 2 + (C I.b₂ * X + C (6 * I.b₄)) by ring]
    exact monic_X_pow_add (by compute_degree!)
  have h6 : (6 : ResidueField R) = 0 := by
    rw [show (6 : ResidueField R) = 2 * 3 by norm_num, h2, zero_mul]
  have hroot : f.eval 0 ∈ maximalIdeal R := by
    have heval : f.eval 0 = 6 * I.b₄ := by
      simp only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C,
        zero_pow (by norm_num : 2 ≠ 0), mul_zero, zero_add]
    rw [heval]
    rw [← residue_eq_zero_iff]
    rw [map_mul, map_ofNat, h6, zero_mul]
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal R) (f.derivative.eval 0)) := by
    apply IsUnit.map
    simpa only [f, derivative_add, derivative_pow, derivative_X, derivative_mul, derivative_C,
      Nat.cast_ofNat, C_0, zero_mul, add_zero, eval_add, eval_mul, eval_C, eval_X,
      Nat.reduceSub, pow_one, eval_zero, mul_zero, zero_add, eval_one, mul_one] using hb₂
  obtain ⟨y, hy, -⟩ := HenselianRing.is_henselian f hf 0 hroot hderiv
  have hfy : y ^ 2 + I.b₂ * y + 6 * I.b₄ = 0 := by
    rw [IsRoot.def] at hy
    simpa only [f, eval_add, eval_mul, eval_pow, eval_X, eval_C] using hy
  refine ⟨I.b₂ + 2 * y, ?_⟩
  change I.b₂ ^ 2 - 24 * I.b₄ = (I.b₂ + 2 * y) * (I.b₂ + 2 * y)
  linear_combination -4 * hfy

open IsLocalRing in
/-- **Split-multiplicative square criterion, dyadic case.**  If the residue characteristic is
`2`, split multiplicative reduction still implies that `-c₆` is a square in the fraction field.
The lifted node discriminant is `-c₄c₆`, while `c₄` itself is a nonzero square. -/
theorem isSquare_neg_c₆_of_hasSplitMultiplicativeReduction_of_two_residue_eq_zero
    [HenselianRing R (maximalIdeal R)] [E.HasSplitMultiplicativeReduction R]
    (h2 : (2 : ResidueField R) = 0) : IsSquare (-E.c₆) := by
  obtain ⟨z, hz⟩ :=
    isSquare_neg_c₄_mul_c₆_integralModel_of_two_residue_eq_zero E R h2
  obtain ⟨s, hs⟩ := isSquare_c₄_integralModel_of_two_residue_eq_zero E R h2
  have hc₄unit : IsUnit (E.integralModel R).c₄ :=
    (residue_ne_zero_iff_isUnit (E.integralModel R).c₄).mp
      (residue_integralModel_c₄_ne_zero E R)
  have hc₄ : (E.integralModel R).c₄ ≠ 0 := hc₄unit.ne_zero
  have hs0 : s ≠ 0 := by
    intro h
    apply hc₄
    rw [hs, h, zero_mul]
  refine ⟨algebraMap R K z / algebraMap R K s, ?_⟩
  have hzK := congrArg (algebraMap R K) hz
  have hsK := congrArg (algebraMap R K) hs
  simp only [map_neg, map_mul] at hzK
  simp only [map_mul] at hsK
  rw [integralModel_c₆_eq R E, integralModel_c₄_eq R E] at hzK
  rw [integralModel_c₄_eq R E] at hsK
  have hsK0 : algebraMap R K s ≠ 0 := by
    intro h
    apply hs0
    apply IsFractionRing.injective R K
    simpa only [map_zero] using h
  field_simp
  rw [pow_two, ← hsK]
  simpa only [mul_comm, pow_two] using hzK

open Polynomial IsLocalRing in
/-- In residue characteristic `2`, the node polynomial of a split-multiplicative curve already
splits over the fraction field, not merely after reduction.  Its reduced tangent direction is a
simple root and hence Hensel-lifts. -/
theorem nodePoly_splits_of_hasSplitMultiplicativeReduction_of_two_residue_eq_zero
    [HenselianRing R (maximalIdeal R)] [E.HasSplitMultiplicativeReduction R]
    (h2 : (2 : ResidueField R) = 0) : E.nodePoly.Splits := by
  let I := E.integralModel R
  let κ := 54 * I.b₆ - 3 * I.b₂ * I.b₄ + I.a₂ * I.c₄
  have hc₄ : IsUnit I.c₄ := by
    apply (residue_ne_zero_iff_isUnit I.c₄).mp
    dsimp only [I]
    exact residue_integralModel_c₄_ne_zero E R
  have ha₁ : IsUnit I.a₁ := by
    dsimp only [I]
    exact isUnit_integralModel_a₁_of_two_residue_eq_zero E R h2
  have hs : ((C I.c₄ * X ^ 2 + C (I.a₁ * I.c₄) * X + C (-κ)).map (residue R)).Splits := by
    simpa only [I, κ, C_neg, sub_eq_add_neg, ResidueField.algebraMap_eq] using
      (HasSplitMultiplicativeReduction.splitMultiplicativeReduction (R := R) (W := E))
  obtain ⟨x, hx⟩ := exists_root_quadratic_of_splits_residue_of_two_eq_zero
    I.c₄ (I.a₁ * I.c₄) (-κ) hc₄ (ha₁.mul hc₄)
      (by simpa only [map_ofNat] using h2) hs
  have hrootI : I.nodePoly.eval x = 0 := by
    simpa only [nodePoly, κ, eval_add, eval_sub, eval_neg, eval_mul, eval_pow, eval_C, eval_X,
      sub_eq_add_neg] using hx
  have hroot : E.nodePoly.eval (algebraMap R K x) = 0 := by
    have hmap := map_nodePoly (algebraMap R K) I
    have hmodel : I.map (algebraMap R K) = E := by
      dsimp only [I]
      exact baseChange_integralModel_eq R E
    rw [hmodel] at hmap
    rw [hmap, eval_map, eval₂_at_apply, hrootI, map_zero]
  apply Splits.of_natDegree_eq_two (x := algebraMap R K x)
  · rw [nodePoly, sub_eq_add_neg, ← C_neg]
    apply natDegree_quadratic
    rw [← integralModel_c₄_eq R E]
    intro hzero
    apply hc₄.ne_zero
    apply IsFractionRing.injective R K
    simpa only [map_zero] using hzero
  · exact hroot

open IsLocalRing IsDedekindDomain.HeightOneSpectrum in
/-- **The twist by a unit discriminant keeps multiplicative reduction.** If `E` has multiplicative
reduction and `D = t² - 4n` is a unit of `R` (residue `≠ 0`), then the base change of the `R`-model
twist `(E.integralModel R).quadraticTwistOf t n` again has multiplicative reduction: its
`c₄ = D² · c₄` is a unit (so the model is minimal and the reduction multiplicative) and its
`Δ = D⁶ · Δ` still has positive valuation. -/
theorem hasMultiplicativeReduction_baseChange_quadraticTwistOf [E.HasMultiplicativeReduction R]
    (t n : R) (hD : residue R (t ^ 2 - 4 * n) ≠ 0) :
    (((E.integralModel R).quadraticTwistOf t n)⁄K).HasMultiplicativeReduction R := by
  set W := (E.integralModel R).quadraticTwistOf t n with hW
  have hWint : IsIntegral R (W⁄K) := ⟨⟨W, rfl⟩⟩
  -- `residue W.c₄ = residue D² · residue (E.integralModel R).c₄ ≠ 0`, `residue W.Δ = 0`.
  have hc₄res : residue R W.c₄ ≠ 0 := by
    rw [hW, c₄_quadraticTwistOf, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hD) (residue_integralModel_c₄_ne_zero E R)
  have hΔres : residue R W.Δ = 0 := by
    rw [hW, Δ_quadraticTwistOf, map_mul, map_pow, residue_integralModel_Δ_eq_zero E R, mul_zero]
  -- Convert to the valuation conditions on the base change `W⁄K`.
  have hc₄val : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).c₄ = 1 := by
    rw [show (W⁄K).c₄ = algebraMap R K W.c₄ from map_c₄ W (algebraMap R K)]
    exact (IsDiscreteValuationRing.maximalIdeal R).valuation_eq_one_iff_notMem.mpr
      fun hmem ↦ hc₄res ((residue_eq_zero_iff W.c₄).mpr hmem)
  have hΔval : valuation K (IsDiscreteValuationRing.maximalIdeal R) (W⁄K).Δ < 1 := by
    rw [show (W⁄K).Δ = algebraMap R K W.Δ from map_Δ W (algebraMap R K)]
    exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem W.Δ).mpr
      ((residue_eq_zero_iff W.Δ).mp hΔres)
  have : IsMinimal R (W⁄K) := isMinimal_of_valuation_c₄_eq_one R (W⁄K) hc₄val
  exact { badReduction := hΔval, multiplicativeReduction := hc₄val }

open IsLocalRing in
/-- If the residue of an integral element `θ` of `S` does not come from the residue field of `R`,
then `θ` does not come from `K` either: an element of `K` integral over the integrally closed `R`
lies in `R`, and residues are compatible. -/
theorem notMem_range_algebraMap_of_residue_notMem {S : Type u} [CommRing S] [IsLocalRing S]
    [Algebra R S] [Algebra.IsIntegral R S] [IsLocalHom (algebraMap R S)] {L : Type u} [Field L]
    [Algebra K L] [Algebra R L] [Algebra S L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsFractionRing S L] {θ : S}
    (hθ : residue S θ ∉ Set.range (algebraMap (ResidueField R) (ResidueField S))) :
    algebraMap S L θ ∉ Set.range (algebraMap K L) := by
  rintro ⟨a, ha⟩
  have haint : _root_.IsIntegral R a := by
    have h1 : _root_.IsIntegral R (algebraMap S L θ) :=
      _root_.IsIntegral.map (IsScalarTower.toAlgHom R S L) (Algebra.IsIntegral.isIntegral θ)
    rw [← ha] at h1
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom R K L)
      (FaithfulSMul.algebraMap_injective K L)).mp h1
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp haint
  refine hθ ⟨residue R r, ?_⟩
  rw [show algebraMap (ResidueField R) (ResidueField S) (residue R r)
    = residue S (algebraMap R S r) by simp only [← ResidueField.algebraMap_residue]]
  congr 1
  apply IsFractionRing.injective S L
  rw [← ha, ← hr, ← IsScalarTower.algebraMap_apply R S L, ← IsScalarTower.algebraMap_apply R K L]

open IsLocalRing in
/-- If the root of the reduced node polynomial `P̄` (assumed irreducible) satisfies a monic
quadratic relation `X² - t·X + n` over the residue field, then comparing with the defining
relation of `P̄` (`aeval_root_nodePoly_map`) and using the linear independence of `1` and the root
(`AdjoinRoot.eq_zero_of_mul_root_add_eq_zero`) yields the relations `φc₄·t + φ(a₁c₄) = 0` and
`φc₄·n + φκ = 0` (φ = residue, `κ = 54b₆ - 3b₂b₄ + a₂c₄`). -/
theorem nodePoly_map_root_relations [E.HasMultiplicativeReduction R]
    (hirr : Irreducible ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))))
    {t n : ResidueField R}
    (hρ : AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R))) ^ 2
        - algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) t
          * AdjoinRoot.root ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))
        + algebraMap (ResidueField R)
            (AdjoinRoot ((E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)))) n
        = 0) :
    residue R (E.integralModel R).c₄ * t
        + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0
      ∧ residue R (E.integralModel R).c₄ * n
        + residue R (54 * (E.integralModel R).b₆
          - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
          + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0 := by
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hρ2 : algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) (E.integralModel R).c₄) * (AdjoinRoot.root P) ^ 2
        + algebraMap (ResidueField R) (AdjoinRoot P)
          (algebraMap R (ResidueField R) ((E.integralModel R).a₁ * (E.integralModel R).c₄))
          * (AdjoinRoot.root P)
        - algebraMap (ResidueField R) (AdjoinRoot P) (algebraMap R (ResidueField R)
          (54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
            + (E.integralModel R).a₂ * (E.integralModel R).c₄)) = 0 :=
    aeval_root_nodePoly_map (algebraMap R (ResidueField R)) (E.integralModel R)
  obtain ⟨hA, hB⟩ := AdjoinRoot.eq_zero_of_mul_root_add_eq_zero hPdeg2.ge
    (a := residue R (E.integralModel R).c₄ * t
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄))
    (b := -(residue R (E.integralModel R).c₄ * n
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄))) (by
    simp only [IsLocalRing.ResidueField.algebraMap_eq, map_add, map_mul, map_neg] at hρ2 ⊢
    linear_combination hρ2
      - algebraMap (ResidueField R) (AdjoinRoot P) (residue R (E.integralModel R).c₄) * hρ)
  rw [neg_eq_zero] at hB
  exact ⟨hA, hB⟩

open IsLocalRing in
/-- The key identity `φc₄ · φ(t'² - 4n') = -φc₆` of the twisting datum `(t', n')`: if its residues
satisfy the trace and norm relations cut out by the node polynomial
(`κ = 54 b₆ - 3 b₂ b₄ + a₂ c₄`), then the discriminant identity `splitPolynomial_discrim` turns
them into this identity. -/
theorem residue_c₄_mul_residue_eq_neg_c₆ [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    residue R (E.integralModel R).c₄ * residue R (t' ^ 2 - 4 * n')
      = -residue R (E.integralModel R).c₆ := by
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hRid : ((E.integralModel R).a₁ * c₄') ^ 2 + 4 * c₄' * κ'
      = -(c₄' * (E.integralModel R).c₆) := by
    rw [hκ', hc₄']
    exact splitPolynomial_discrim (E.integralModel R)
  have hdisc := congrArg (residue R) hRid
  simp only [map_add, map_mul, map_pow, map_neg, map_ofNat] at hdisc
  apply mul_left_cancel₀ (residue_integralModel_c₄_ne_zero E R)
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination hdisc
    + (residue R c₄' * residue R t' - residue R (E.integralModel R).a₁ * residue R c₄') * hA
    - 4 * residue R c₄' * hB

open IsLocalRing in
/-- The residue characteristic `2` case of `nodePoly_quadraticTwistOf_map_splits_of_residue`:
the Artin–Schreier split condition (`nodePoly_map_splits_iff_of_two_eq_zero`) holds with `z = 0`,
because `φ κ_W = 0`. Indeed `κ_W = D³κ - D²·n·a₁²·c₄` (`kappa_quadraticTwistOf`), and
`φκ = -φc₄·φn` (`hB`), `φa₁ = -φt'` (`hA`), `φD = φt'²` (as `4 = 0`), so
`φκ_W = -φD²·φc₄·φn·(φD + φa₁²) = -φD²·φc₄·φn·(2·φt'²) = 0`. -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero
    [E.HasMultiplicativeReduction R] (t' n' : R) (h2 : (2 : ResidueField R) = 0)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  -- `D = t'²-4n'` has nonzero residue (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  set c₄' := (E.integralModel R).c₄ with hc₄'
  set κ' := 54 * (E.integralModel R).b₆ - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
    + (E.integralModel R).a₂ * c₄' with hκ'
  simp only [map_mul] at hA
  have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
  have hc₄map : algebraMap R (ResidueField R) (E.integralModel R).c₄ ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hc₄0
  set D := t' ^ 2 - 4 * n' with hDdef
  have h4 : (4 : ResidueField R) = 0 := by
    rw [show (4 : ResidueField R) = 2 * 2 by norm_num, h2, mul_zero]
  have hDmap : algebraMap R (ResidueField R) D ≠ 0 := by
    rw [ResidueField.algebraMap_eq]; exact hDne
  have hDt : residue R D = residue R t' ^ 2 := by
    rw [hDdef, map_sub, map_mul, map_pow, map_ofNat, h4, zero_mul, sub_zero]
  have hWc₄ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₄ ≠ 0 := by
    rw [c₄_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 2 hDmap) hc₄map
  have hWc₆ : algebraMap R (ResidueField R)
      ((E.integralModel R).quadraticTwistOf t' n').c₆ ≠ 0 := by
    rw [c₆_quadraticTwistOf, ← hDdef, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero 3 hDmap)
      (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
  have hta : residue R (E.integralModel R).a₁ = -residue R t' := by
    rcases mul_eq_zero.mp (show residue R c₄'
        * (residue R t' + residue R (E.integralModel R).a₁) = 0 by linear_combination hA)
      with hz | hz
    · exact absurd hz hc₄0
    · linear_combination hz
  have hκW_eq : 54 * ((E.integralModel R).quadraticTwistOf t' n').b₆
      - 3 * ((E.integralModel R).quadraticTwistOf t' n').b₂
          * ((E.integralModel R).quadraticTwistOf t' n').b₄
      + ((E.integralModel R).quadraticTwistOf t' n').a₂
          * ((E.integralModel R).quadraticTwistOf t' n').c₄
      = D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄' := by
    rw [hDdef, hκ', hc₄']
    exact kappa_quadraticTwistOf (E.integralModel R) t' n'
  have hWc₄eq : ((E.integralModel R).quadraticTwistOf t' n').c₄ = D ^ 2 * c₄' := by
    rw [c₄_quadraticTwistOf, ← hDdef, hc₄']
  have hκW0 : algebraMap R (ResidueField R)
      (D ^ 3 * κ' - D ^ 2 * n' * (E.integralModel R).a₁ ^ 2 * c₄') = 0 := by
    simp only [map_sub, map_mul, map_pow, ResidueField.algebraMap_eq, hDt, hta]
    linear_combination (residue R t') ^ 6 * hB
      - (residue R t') ^ 6 * residue R n' * residue R c₄' * h2
  rw [nodePoly_map_splits_iff_of_two_eq_zero h2 (algebraMap R (ResidueField R))
    ((E.integralModel R).quadraticTwistOf t' n') hWc₄ hWc₆]
  refine ⟨0, ?_⟩
  rw [hκW_eq, hWc₄eq, show (0 : ResidueField R) ^ 2 + 0 = 0 from by ring, mul_zero, hκW0,
    neg_zero, mul_zero]

open IsLocalRing in
/-- If the residues of `(t', n')` satisfy the trace and norm relations cut out by the node
polynomial, then the node polynomial of the quadratic twist of the integral model by `(t', n')`
splits over the residue field: the key identity `φc₄ · φ(t'² - 4n') = -φc₆`
(`residue_c₄_mul_residue_eq_neg_c₆`) reduces this to a square-class computation for residue
characteristic `≠ 2`, and to an Artin–Schreier computation for residue characteristic `2`
(`nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero`). -/
theorem nodePoly_quadraticTwistOf_map_splits_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    Polynomial.Splits (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
      (algebraMap R (ResidueField R))) := by
  rcases ne_or_eq (2 : ResidueField R) 0 with h2 | h2
  · -- Residue characteristic `≠ 2`: split ↔ `IsSquare (φ((t'²-4n')·-(c₄c₆)))`, which `hkey` shows
    -- equals `IsSquare (φc₆²)`.
    have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
    have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
      residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
    have hc₄0 : residue R (E.integralModel R).c₄ ≠ 0 := residue_integralModel_c₄_ne_zero E R
    have : NeZero (2 : ResidueField R) := ⟨h2⟩
    rw [nodePoly_quadraticTwistOf_map_splits_iff (algebraMap R (ResidueField R))
      (E.integralModel R) t' n' (by rw [ResidueField.algebraMap_eq]; exact hc₄0)
      (by rw [ResidueField.algebraMap_eq]; exact hDne)]
    refine ⟨residue R (E.integralModel R).c₆, ?_⟩
    apply mul_left_cancel₀ hc₄0
    rw [ResidueField.algebraMap_eq]
    simp only [map_mul, map_neg]
    linear_combination
      (-(residue R (E.integralModel R).c₄ * residue R (E.integralModel R).c₆)) * hkey
  · exact nodePoly_quadraticTwistOf_map_splits_of_residue_of_two_eq_zero E R t' n' h2 hA hB

open IsLocalRing in
/-- Packaging `nodePoly_quadraticTwistOf_map_splits_of_residue`: if the base change of the twisted
integral model has multiplicative reduction and the residues of `(t', n')` satisfy the trace and
norm relations, then the reduction is *split* multiplicative. -/
theorem hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue
    [E.HasMultiplicativeReduction R] (t' n' : R)
    [hW : (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasMultiplicativeReduction R]
    (hA : residue R (E.integralModel R).c₄ * residue R t'
      + residue R ((E.integralModel R).a₁ * (E.integralModel R).c₄) = 0)
    (hB : residue R (E.integralModel R).c₄ * residue R n'
      + residue R (54 * (E.integralModel R).b₆
        - 3 * (E.integralModel R).b₂ * (E.integralModel R).b₄
        + (E.integralModel R).a₂ * (E.integralModel R).c₄) = 0) :
    (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
  refine { hW with splitMultiplicativeReduction := ?_ }
  rw [show (((E.integralModel R).quadraticTwistOf t' n')⁄K).integralModel R
    = (E.integralModel R).quadraticTwistOf t' n' from integralModel_baseChange R _]
  exact nodePoly_quadraticTwistOf_map_splits_of_residue E R t' n' hA hB

open IsLocalRing in
/-- **A nonsquare unit twist of a split multiplicative curve is nonsplit (residue
characteristic `≠ 2`).**  This packages
`not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_isSquare` in terms of the reduction
predicates.  The twisted integral model is assumed to retain multiplicative reduction; this is
automatic from `hasMultiplicativeReduction_baseChange_quadraticTwistOf` when the discriminant
has nonzero residue.

The remaining local-field input needed to apply this to an abstract unramified quadratic
extension is a normalized integral generator whose reduced discriminant is a nonsquare. -/
theorem not_hasSplitMultiplicativeReduction_baseChange_quadraticTwistOf_of_not_isSquare
    [E.HasSplitMultiplicativeReduction R] (t' n' : R)
    (hD : residue R (t' ^ 2 - 4 * n') ≠ 0)
    (hDnsq : ¬ IsSquare (residue R (t' ^ 2 - 4 * n'))) :
    ¬ (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
  letI hW := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hD
  intro hWsplit
  have h2 : (2 : ResidueField R) ≠ 0 := by
    intro h2
    apply hDnsq
    rw [show residue R (t' ^ 2 - 4 * n') = (residue R t') ^ 2 from by
      simp only [map_sub, map_pow, map_mul, map_ofNat, show (4 : ResidueField R) = 2 * 2 by
        norm_num, h2, zero_mul, sub_zero]]
    exact ⟨residue R t', by simp only [pow_two]⟩
  letI : NeZero (2 : ResidueField R) := ⟨h2⟩
  have htwist : Polynomial.Splits
      (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
        (algebraMap R (ResidueField R))) := by
    rw [← integralModel_baseChange (K := K) R
      ((E.integralModel R).quadraticTwistOf t' n')]
    exact hWsplit.splitMultiplicativeReduction
  exact not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_isSquare
    (algebraMap R (ResidueField R)) (E.integralModel R) t' n'
    (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R)
    (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
    (by rw [ResidueField.algebraMap_eq]; exact hD)
    ‹E.HasSplitMultiplicativeReduction R›.splitMultiplicativeReduction
    (by simpa only [ResidueField.algebraMap_eq] using hDnsq) htwist

open IsLocalRing in
/-- **An irreducible Artin--Schreier unit twist of a split multiplicative curve is nonsplit
(residue characteristic `2`).**  This is the reduction-predicate packaging of
`not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_exists_artinSchreier`.

The hypotheses say that the reduced twisting polynomial `X² + t'X + n'` is separable
(`t' ≠ 0`) and has no root in the residue field.  Its discriminant is consequently a unit, so
the explicit twisted integral model still has multiplicative reduction, but its node polynomial
does not split. -/
theorem
    not_hasSplitMultiplicativeReduction_baseChange_quadraticTwistOf_of_not_exists_artinSchreier
    [E.HasSplitMultiplicativeReduction R] (t' n' : R)
    (h2 : (2 : ResidueField R) = 0) (ht : residue R t' ≠ 0)
    (hAS : ¬ ∃ z : ResidueField R,
      residue R t' ^ 2 * (z ^ 2 + z) = residue R n') :
    ¬ (((E.integralModel R).quadraticTwistOf t' n')⁄K).HasSplitMultiplicativeReduction R := by
  have hD : residue R (t' ^ 2 - 4 * n') ≠ 0 := by
    rw [show residue R (t' ^ 2 - 4 * n') = residue R t' ^ 2 from by
      simp only [map_sub, map_pow, map_mul, map_ofNat, show (4 : ResidueField R) = 2 * 2 by
        norm_num, h2, zero_mul, sub_zero]]
    exact pow_ne_zero 2 ht
  letI hW := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hD
  intro hWsplit
  have htwist : Polynomial.Splits
      (((E.integralModel R).quadraticTwistOf t' n').nodePoly.map
        (algebraMap R (ResidueField R))) := by
    rw [← integralModel_baseChange (K := K) R
      ((E.integralModel R).quadraticTwistOf t' n')]
    exact hWsplit.splitMultiplicativeReduction
  exact not_nodePoly_quadraticTwistOf_map_splits_of_splits_of_not_exists_artinSchreier
    h2 (algebraMap R (ResidueField R)) (E.integralModel R) t' n'
    (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₄_ne_zero E R)
    (by rw [ResidueField.algebraMap_eq]; exact residue_integralModel_c₆_ne_zero E R)
    (by simpa only [ResidueField.algebraMap_eq] using ht)
    ‹E.HasSplitMultiplicativeReduction R›.splitMultiplicativeReduction
    (by simpa only [ResidueField.algebraMap_eq] using hAS) htwist

variable [E.IsElliptic]

open IsLocalRing in
/-- If `E` has multiplicative reduction which is not split, then `E` has a quadratic twist with
split multiplicative reduction — namely the twist by the unramified quadratic extension of `K`:
the reduction of the twist is the same nodal cubic with the Galois action on the two tangent
directions at the node twisted into triviality.

Mathlib's reduction-type predicates apply to a specific Weierstrass equation and require it to
be minimal, while our chosen model `E.quadraticTwist L` of the twist need not be; so the
conclusion is phrased via the minimal model `(E.quadraticTwist L).minimal R`. (Being split
multiplicative is intrinsic, so any other minimal model would do.)

The nonsplitness hypothesis `h` cannot be dropped: if `E` already has split multiplicative
reduction then *no* quadratic twist of `E` has split multiplicative reduction, since the
unramified quadratic twist has nonsplit multiplicative reduction and ramified quadratic twists
have additive reduction. -/
theorem exists_quadraticTwist_hasSplitMultiplicativeReduction [E.HasMultiplicativeReduction R]
    (h : ¬E.HasSplitMultiplicativeReduction R) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra.IsQuadraticExtension K L)
      (_ : Algebra.IsSeparable K L),
      ((E.quadraticTwist L).minimal R).HasSplitMultiplicativeReduction R := by
  -- The node polynomial reduced to the residue field `k`; nonsplitness makes it irreducible
  -- (`irreducible_nodePoly_map`), and multiplicative reduction makes it separable
  -- (`separable_nodePoly_map`). Its root field `k' = k[X]/(P)` is therefore a separable
  -- quadratic extension of `k`.
  set P := (E.integralModel R).nodePoly.map (algebraMap R (ResidueField R)) with hP
  have hirr : Irreducible P := irreducible_nodePoly_map E R h
  have : Fact (Irreducible P) := ⟨hirr⟩
  have hPdeg2 : P.natDegree = 2 := natDegree_nodePoly_map E R
  have hk'rank : Module.finrank (ResidueField R) (AdjoinRoot P) = 2 :=
    AdjoinRoot.finrank_eq_natDegree.trans hPdeg2
  have : FiniteDimensional (ResidueField R) (AdjoinRoot P) := .of_finrank_eq_succ hk'rank
  have : Algebra.IsSeparable (ResidueField R) (AdjoinRoot P) :=
    AdjoinRoot.isSeparable_of_separable (separable_nodePoly_map E R)
  -- Lift `k'` to the unramified quadratic extension `L/K` (`LiftSeparableExtension`).
  obtain ⟨L, _, _, _, _, _, _, S, _, _, _, _, _, _, _, _, _, hLrank, ⟨resIso⟩⟩ :=
    exists_unramified_extension_of_residueField (R := R) (K := K) (AdjoinRoot P)
  have : Algebra.IsQuadraticExtension K L := ⟨hLrank.trans hk'rank⟩
  refine ⟨L, ‹Field L›, ‹Algebra K L›, ‹Algebra.IsQuadraticExtension K L›,
    ‹Algebra.IsSeparable K L›, ?_⟩
  -- `S = 𝒪_L` is the integral closure of `R` in `L` (now that `Frac S = L` is proved), so `L` is
  -- the base-change localization of `S`, and `R`-trace/norm are compatible with `K`-trace/norm.
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have : IsIntegralClosure S R L := IsIntegralClosure.of_isIntegrallyClosed S R L
  have : IsLocalization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) L :=
    IsIntegralClosure.isLocalization_of_isSeparable R K L S
  have : Module.IsTorsionFree R L := Module.IsTorsionFree.trans_faithfulSMul R K L
  have : Module.Free R S := IsIntegralClosure.module_free R K L S
  have hSrank : Module.finrank R S = 2 :=
    (IsIntegralClosure.rank R K L S).trans (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨θ', hθ'res⟩ := IsLocalRing.residue_surjective (resIso.symm (AdjoinRoot.root P))
  -- Via `resIso`, `root P` satisfies the Cayley–Hamilton relation `X² - φ(t')·X + φ(n')` of `θ'`
  -- (`sq_sub_trace_mul_self_add_norm_residue`); comparing with the defining relation of `P` gives
  -- the residue relations `φc₄·φt' = -φ(a₁c₄)` and `φc₄·φn' = -φκ` (`nodePoly_map_root_relations`).
  have hρ1 := sq_sub_trace_mul_self_add_norm_residue R hSrank resIso θ'
  rw [hθ'res, resIso.apply_symm_apply] at hρ1
  obtain ⟨hA, hB⟩ := nodePoly_map_root_relations E R hirr hρ1
  set t' := Algebra.trace R S θ'
  set n' := Algebra.norm R θ'
  -- `root P ∉ k` (its minimal polynomial has degree 2), so `θ'̄ = resIso⁻¹(root P) ∉ k` and, since
  -- `R` is integrally closed, `algebraMap S L θ' ∉ K` — the twist by `θ'` is nontrivial.
  have hθ' : algebraMap S L θ' ∉ Set.range (algebraMap K L) :=
    notMem_range_algebraMap_of_residue_notMem R (by
      rw [hθ'res]
      exact fun hmem ↦ AdjoinRoot.root_notMem_range_algebraMap hPdeg2.ge
        (resIso.symm.apply_mem_range_algebraMap_iff.mp hmem))
  -- Trace/norm land in `K`, giving the connection to the `R`-model `W = quadraticTwistOf t' n'`.
  have htr : Algebra.trace K L (algebraMap S L θ') = algebraMap R K t' :=
    Algebra.trace_localization R (nonZeroDivisors R) θ'
  have hnr : Algebra.norm K (algebraMap S L θ') = algebraMap R K n' :=
    Algebra.norm_localization R (nonZeroDivisors R) θ'
  obtain ⟨C, hC⟩ := E.exists_smul_quadraticTwist_eq_quadraticTwistBy L hθ'
  rw [quadraticTwistBy, htr, hnr, ← baseChange_integralModel_quadraticTwistOf E R t' n'] at hC
  -- `D = t'²-4n'` is a unit (`residue_c₄_mul_residue_eq_neg_c₆`: `φc₄·φD = -φc₆ ≠ 0`), so `W⁄K`
  -- has multiplicative reduction; the relations `hA`, `hB` make it split
  -- (`nodePoly_quadraticTwistOf_map_splits_of_residue`).
  have hkey := residue_c₄_mul_residue_eq_neg_c₆ E R t' n' hA hB
  have hDne : residue R (t' ^ 2 - 4 * n') ≠ 0 := fun h0 ↦
    residue_integralModel_c₆_ne_zero E R (neg_eq_zero.mp (by rw [← hkey, h0, mul_zero]))
  have hWmult := hasMultiplicativeReduction_baseChange_quadraticTwistOf E R t' n' hDne
  have hWsplit := hasSplitMultiplicativeReduction_quadraticTwistOf_of_residue E R t' n' hA hB
  -- `hWsplit : (W⁄K).HasSplitMultiplicativeReduction R` with `W⁄K` minimal and
  -- `hC : C • E.quadraticTwist L = W⁄K`. Split multiplicativity transfers to the chosen minimal
  -- model `(E.quadraticTwist L).minimal R`, which is another minimal model of
  -- `E.quadraticTwist L` (`of_isMinimal_smul`).
  have : IsMinimal R (((E.integralModel R).quadraticTwistOf t' n')⁄K) := hWmult.toIsMinimal
  have hD : (((E.quadraticTwist L).exists_isMinimal R).choose * C⁻¹)
      • (((E.integralModel R).quadraticTwistOf t' n')⁄K) = (E.quadraticTwist L).minimal R := by
    rw [mul_smul, ← hC, inv_smul_smul]; rfl
  have : (((E.integralModel R).quadraticTwistOf t' n')⁄K).IsElliptic :=
    ⟨(Δ_baseChange_quadraticTwistOf_ne_zero E R t' n' fun h0 ↦
      hDne (by rw [h0, map_zero])).isUnit⟩
  exact HasSplitMultiplicativeReduction.of_isMinimal_smul R _ hD hWsplit

end Reduction

end WeierstrassCurve

end
