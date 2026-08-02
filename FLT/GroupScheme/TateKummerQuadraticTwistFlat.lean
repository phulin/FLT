/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummerQuadraticTwistTorsion
public import Mathlib.RingTheory.Etale.Descent

/-!
# Finite-flat quadratic twists of Tate--Kummer models

This file packages the geometric properties of the quadratic descent constructed in
`TateKummerQuadraticTwist`.  The first step is generic-fiber etaleness: after the
faithfully flat quadratic field extension, the descended algebra is the ordinary
Tate--Kummer generic fiber, so etaleness descends.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace TateKummer.QuadraticTwist

variable (R : Type u) [CommRing R]
variable (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L]

set_option backward.isDefEq.respectTransparency false

/-- The generic fiber of the descended quadratic-twist coordinate algebra is etale.

The quadratic splitting field is faithfully flat over the generic-fiber field.  Over
that field the explicit descent equivalence identifies the algebra with the split
Tate--Kummer generic fiber, whose etaleness was proved componentwise. -/
theorem genericFiberEtale
    [NeZero (N : K)]
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n)) :
    Algebra.Etale K (K ⊗[R] fixedSubalgebra R N u₀ t n) := by
  letI : NeZero (N : L) := ⟨by
    intro h
    apply NeZero.ne (N : K)
    apply (algebraMap K L).injective
    simpa using h⟩
  letI : CommRing (K ⊗[R] fixedSubalgebra R N u₀ t n) := by
    infer_instance
  letI : Algebra K (K ⊗[R] fixedSubalgebra R N u₀ t n) :=
    Algebra.TensorProduct.leftAlgebra
  letI : CommRing
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) := by
    infer_instance
  letI : Algebra L
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) :=
    Algebra.TensorProduct.leftAlgebra
  let e := genericFiberFieldExtendedCoverEquiv R N u₀ t n K L θ
    htrace hnorm h2 hdisc
  letI : Algebra.Etale L
      (L ⊗[R] TateKummer.CoordinateAlgebra (R := R) N u₀) :=
    TateKummer.coordinateGenericFiberEtale L N u₀
  letI : Algebra.Etale L
      (L ⊗[K] (K ⊗[R] fixedSubalgebra R N u₀ t n)) :=
    Algebra.Etale.of_equiv e.symm
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat L

end TateKummer.QuadraticTwist

namespace WeierstrassCurve

open ValuativeRel
open scoped WeierstrassCurve.Affine

universe v

section CurveTorsion

variable (R : Type u) [CommRing R] [IsDomain R]
variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]
variable (S : Type v) [Field S]
  [Algebra R S] [Algebra K S] [Algebra L S]
  [IsScalarTower R K S] [IsScalarTower R L S] [IsScalarTower K L S]
  [IsSepClosed S] [Algebra.IsSeparable K S]
  [DecidableEq K] [DecidableEq S]
variable [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- Geometric points of the descended Tate--Kummer model, identified with torsion on
the split quadratic twist through Tate uniformization. -/
noncomputable def quadraticTateKummerTorsionAddEquiv
    (W : WeierstrassCurve K) [W.IsElliptic]
    [W.HasSplitMultiplicativeReduction 𝒪[K]]
    (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u₀ = W.qUnitSepClosure S) :
    letI := TateKummer.QuadraticTwist.coordinateBialgebra
      R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] TateKummer.QuadraticTwist.fixedSubalgebra R N u₀ t n →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy (W⁄S).Point (N : ℤ) := by
  letI := TateKummer.QuadraticTwist.coordinateBialgebra
    R N u₀ t n h2 hdisc
  let e := W.tateTorsionLinearEquiv S N
  let eAdd : AddSubgroup.torsionBy
        (Additive (Sˣ ⧸ Subgroup.zpowers (W.qUnitSepClosure S))) (N : ℤ) ≃+
      AddSubgroup.torsionBy (W⁄S).Point (N : ℤ) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add }
  exact (TateKummer.QuadraticTwist.genericFiberTorsionAddEquiv
    R N u₀ t n K L S θ htrace hnorm h2 hdisc
      (W.qUnitSepClosure S) a hq
      (W.qUnitSepClosure_zpow_injective S)).trans eAdd

variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (C : WeierstrassCurve.VariableChange K)
variable [((C • E.quadraticTwist L)).HasSplitMultiplicativeReduction 𝒪[K]]

/-- The descended model's geometric points, identified with torsion on the original
nonsplit-multiplicative curve.  This composes Tate uniformization on the split quadratic
twist with the quadratic-twist point equivalence. -/
noncomputable def quadraticTwistTateKummerTorsionAddEquiv
    (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (a : Sˣ)
    (hq : a ^ N * Units.map (algebraMap R S) u₀ =
      (C • E.quadraticTwist L).qUnitSepClosure S) :
    letI := TateKummer.QuadraticTwist.coordinateBialgebra
      R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] TateKummer.QuadraticTwist.fixedSubalgebra R N u₀ t n →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy (E⁄S).Point (N : ℤ) := by
  letI := TateKummer.QuadraticTwist.coordinateBialgebra
    R N u₀ t n h2 hdisc
  let e := quadraticTwistTateTorsionLinearEquiv (L := L) S E C N
  let eAdd : AddSubgroup.torsionBy
        (((C • E.quadraticTwist L))⁄S).Point (N : ℤ) ≃+
      AddSubgroup.torsionBy (E⁄S).Point (N : ℤ) :=
    { toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add }
  exact (quadraticTateKummerTorsionAddEquiv R K L S
    (C • E.quadraticTwist L) N u₀ t n θ htrace hnorm h2 hdisc a hq).trans eAdd

end CurveTorsion

end WeierstrassCurve
