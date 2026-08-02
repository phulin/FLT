/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummerTorsion

/-!
# Finite-flat Tate--Kummer models for split multiplicative torsion

Suppose the Tate parameter of a split-multiplicative elliptic curve factors over a
discrete valuation ring as `q = a ^ N * u`, with `u` a unit.  The Tate--Kummer Hopf
algebra attached to `u` is then a finite flat model of the curve's `N`-torsion.

This file separates the proof into three pieces: the factor `a` gives a nonzero unit in
the separable closure, that unit supplies the required factorization of the Tate
parameter and is Galois fixed, and the abstract Tate--Kummer point equivalence then
supplies the finite-flat prolongation.
-/

@[expose] public section

open ValuativeRel
open scoped TensorProduct WeierstrassCurve.Affine

universe u v

namespace WeierstrassCurve

section SplitMultiplicative

variable (R : Type u) [CommRing R] [IsDomain R]
variable (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (S : Type v) [Field S] [Algebra R S] [Algebra K S]
  [IsScalarTower R K S] [IsSepClosed S] [Algebra.IsSeparable K S]
  [DecidableEq K] [DecidableEq S]
variable (E : WeierstrassCurve K) [E.IsElliptic]
  [E.HasSplitMultiplicativeReduction 𝒪[K]]

/-- In a factorization of the nonzero Tate parameter as `q₀ = a ^ N * u`, the
nonunit factor `a` is nonzero. -/
lemma tateKummer_factor_ne_zero
    (N : ℕ) [NeZero N] (q₀ a : R) (u : Rˣ)
    (hq₀ : algebraMap R K q₀ = E.q)
    (hfac : q₀ = a ^ N * (u : R)) : a ≠ 0 := by
  have hq₀ne : q₀ ≠ 0 := by
    intro hq₀zero
    apply E.q_ne_zero
    rw [← hq₀, hq₀zero, map_zero]
  intro hazero
  apply hq₀ne
  rw [hfac, hazero, zero_pow (NeZero.ne N), zero_mul]

/-- The image in the separable closure of the nonunit factor in the Tate-parameter
factorization, regarded as a unit of the field. -/
noncomputable def tateKummerRootUnit
    (a : R) (haS : algebraMap R S a ≠ 0) : Sˣ :=
  Units.mk0 (algebraMap R S a) haS

@[simp]
lemma coe_tateKummerRootUnit
    (a : R) (haS : algebraMap R S a ≠ 0) :
    (tateKummerRootUnit (R := R) (S := S) a haS : S) =
      algebraMap R S a :=
  rfl

/-- The unit coming from an integral factor is fixed by every automorphism over the
generic-fiber field. -/
lemma unitsMap_tateKummerRootUnit
    (a : R) (haS : algebraMap R S a ≠ 0) (σ : S ≃ₐ[K] S) :
    Units.map σ.toRingEquiv.toMonoidHom
        (tateKummerRootUnit (R := R) (S := S) a haS) =
      tateKummerRootUnit (R := R) (S := S) a haS := by
  apply Units.ext
  change σ (algebraMap R S a) = algebraMap R S a
  rw [IsScalarTower.algebraMap_apply R K S]
  exact σ.commutes (algebraMap R K a)

/-- An integral factorization `q₀ = a ^ N * u` becomes the unit factorization of the
Tate parameter required by the abstract Tate--Kummer model. -/
lemma tateKummerRootUnit_pow_mul
    (N : ℕ) [NeZero N] (q₀ a : R) (u : Rˣ)
    (hq₀ : algebraMap R K q₀ = E.q)
    (hfac : q₀ = a ^ N * (u : R))
    (haS : algebraMap R S a ≠ 0) :
    tateKummerRootUnit (R := R) (S := S) a haS ^ N *
        Units.map (algebraMap R S) u = E.qUnitSepClosure S := by
  apply Units.ext
  change (algebraMap R S a) ^ N * algebraMap R S (u : R) =
    algebraMap K S E.q
  calc
    (algebraMap R S a) ^ N * algebraMap R S (u : R) =
        algebraMap R S (a ^ N * (u : R)) := by
          simp only [map_pow, map_mul]
    _ = algebraMap R S q₀ := congrArg (algebraMap R S) hfac.symm
    _ = algebraMap K S (algebraMap R K q₀) :=
      IsScalarTower.algebraMap_apply R K S q₀
    _ = algebraMap K S E.q := congrArg (algebraMap K S) hq₀

/-- A split-multiplicative curve whose Tate parameter is an `N`-th power times an
integral unit has a finite flat Tate--Kummer model for its `N`-torsion. -/
theorem torsion_flat_of_split_multiplicative_factorization
    (N : ℕ) [NeZero N] [NeZero (N : K)]
    (q₀ a : R) (u : Rˣ)
    (hq₀ : algebraMap R K q₀ = E.q)
    (hfac : q₀ = a ^ N * (u : R)) :
    ∃ (H : Type u) (_ : CommRing H) (_ : HopfAlgebra R H)
      (_ : Module.Finite R H) (_ : Module.Flat R H)
      (_ : Algebra.Etale K (K ⊗[R] H))
      (f : Additive (WithConv (K ⊗[R] H →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy (E⁄S).Point (N : ℤ)),
      ∀ (σ : S ≃ₐ[K] S) (φ : K ⊗[R] H →ₐ[K] S),
        (f (Additive.ofMul (WithConv.toConv (σ.toAlgHom.comp φ))) :
            (E⁄S).Point) =
          Affine.Point.map σ.toAlgHom
            (f (Additive.ofMul (WithConv.toConv φ))) := by
  let ha : a ≠ 0 := E.tateKummer_factor_ne_zero (R := R) (K := K)
    N q₀ a u hq₀ hfac
  let haS : algebraMap R S a ≠ 0 := by
    intro hzero
    apply ha
    apply IsFractionRing.injective R K
    apply (algebraMap K S).injective
    rw [← IsScalarTower.algebraMap_apply R K S]
    simpa only [map_zero] using hzero
  let aS : Sˣ := tateKummerRootUnit (R := R) (S := S) a haS
  let hqS : aS ^ N * Units.map (algebraMap R S) u = E.qUnitSepClosure S :=
    E.tateKummerRootUnit_pow_mul (R := R) (K := K) (S := S)
      N q₀ a u hq₀ hfac haS
  let H := TateKummer.CoordinateAlgebra (R := R) N u
  let f := E.tateKummerTorsionAddEquiv R K S N u aS hqS
  refine ⟨H, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, f, ?_⟩
  intro σ φ
  have h := E.tateKummerTorsionAddEquiv_comp R K S N u aS hqS
    (fun τ ↦ unitsMap_tateKummerRootUnit (R := R) (K := K) (S := S)
      a haS τ) σ φ
  exact congrArg Subtype.val h

end SplitMultiplicative

end WeierstrassCurve
