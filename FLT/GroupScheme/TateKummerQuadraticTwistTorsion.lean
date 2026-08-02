/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GroupScheme.TateKummerQuadraticTwist
public import FLT.GroupScheme.TateKummerTorsion

/-!
# Torsion points of quadratic Tate--Kummer models

This file composes quadratic descent of the Tate--Kummer coordinate algebra with the
explicit quotient-torsion classification.  The descended generic-fiber points form the
expected torsion group because the quadratic-cover comparison preserves convolution.
-/

@[expose] public section

open scoped Multiplicative TensorProduct

universe u v

namespace TateKummer.QuadraticTwist

section GenericFiber

variable (R : Type u) [CommRing R]
variable (N : ℕ) [NeZero N] (u₀ : Rˣ) (t n : R)
variable (K L : Type u) [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra.IsQuadraticExtension K L]
variable (S : Type v) [Field S]
  [Algebra R S] [Algebra K S] [Algebra L S]
  [IsScalarTower R K S] [IsScalarTower R L S]

/-- A geometric point of the quadratic-twist generic fiber, interpreted as torsion in
the Tate quotient. -/
noncomputable def genericFiberPointToTorsion
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q a : Sˣ) (hq : a ^ N * Units.map (algebraMap R S) u₀ = q)
    (φ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    AddSubgroup.torsionBy
      (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) :=
  TateKummer.kummerPointToTorsion R S N u₀ q a hq
    (genericFiberAlgHomUnitEquiv R N u₀ t n K L S θ
      htrace hnorm h2 hdisc φ)

/-- Convolution of descended generic-fiber points becomes addition of quotient-torsion
classes. -/
lemma genericFiberPointToTorsion_convMul
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q a : Sˣ) (hq : a ^ N * Units.map (algebraMap R S) u₀ = q)
    (φ ψ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S) :
    letI := coordinateBialgebra R N u₀ t n h2 hdisc
    genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
        h2 hdisc q a hq
        (WithConv.toConv φ * WithConv.toConv ψ).ofConv =
      genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
          h2 hdisc q a hq φ +
        genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
          h2 hdisc q a hq ψ := by
  letI := coordinateBialgebra R N u₀ t n h2 hdisc
  rw [genericFiberPointToTorsion,
    genericFiberAlgHomUnitEquiv_convMul,
    TateKummer.kummerPointToTorsion_mul]
  rfl

/-- The quotient-torsion interpretation of descended generic-fiber points as an additive
homomorphism. -/
noncomputable def genericFiberToTorsionAddHom
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q a : Sˣ) (hq : a ^ N * Units.map (algebraMap R S) u₀ = q) :
    letI := coordinateBialgebra R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)) →+
        AddSubgroup.torsionBy
          (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) := by
  letI := coordinateBialgebra R N u₀ t n h2 hdisc
  exact
    { toFun := fun φ ↦ genericFiberPointToTorsion R N u₀ t n K L S θ
        htrace hnorm h2 hdisc q a hq φ.toMul.ofConv
      map_zero' := by
        let φ₁ : K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S :=
          (1 : WithConv
            (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)).ofConv
        have h := genericFiberPointToTorsion_convMul R N u₀ t n K L S θ
          htrace hnorm h2 hdisc q a hq φ₁ φ₁
        have hmul :
            (WithConv.toConv φ₁ * WithConv.toConv φ₁).ofConv = φ₁ := by
          change (1 * 1 : WithConv
            (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)).ofConv =
              (1 : WithConv
                (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)).ofConv
          exact congrArg WithConv.ofConv (one_mul (1 : WithConv
            (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)))
        rw [hmul] at h
        change genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
          h2 hdisc q a hq φ₁ = 0
        exact add_left_cancel (a := genericFiberPointToTorsion R N u₀ t n
          K L S θ htrace hnorm h2 hdisc q a hq φ₁) (by
            calc
              genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
                    h2 hdisc q a hq φ₁ +
                  genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
                    h2 hdisc q a hq φ₁ =
                genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
                  h2 hdisc q a hq φ₁ := h.symm
              _ = genericFiberPointToTorsion R N u₀ t n K L S θ htrace hnorm
                    h2 hdisc q a hq φ₁ + 0 := (add_zero _).symm)
      map_add' := fun φ ψ ↦
        genericFiberPointToTorsion_convMul R N u₀ t n K L S θ
          htrace hnorm h2 hdisc q a hq φ.toMul.ofConv ψ.toMul.ofConv }

/-- The additive quotient-torsion map is bijective. -/
lemma genericFiberToTorsionAddHom_bijective
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q a : Sˣ) (hq : a ^ N * Units.map (algebraMap R S) u₀ = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    letI := coordinateBialgebra R N u₀ t n h2 hdisc
    Function.Bijective (genericFiberToTorsionAddHom R N u₀ t n K L S θ
      htrace hnorm h2 hdisc q a hq) := by
  letI := coordinateBialgebra R N u₀ t n h2 hdisc
  let e := genericFiberAlgHomUnitEquiv R N u₀ t n K L S θ
    htrace hnorm h2 hdisc
  have hK := TateKummer.kummerPointToTorsion_bijective
    R S N u₀ q a hq hqinj
  constructor
  · intro x y hxy
    have hpoint : e x.toMul.ofConv = e y.toMul.ofConv := hK.1 hxy
    have halg : x.toMul.ofConv = y.toMul.ofConv := e.injective hpoint
    simpa using congrArg Additive.ofMul (congrArg WithConv.toConv halg)
  · intro z
    obtain ⟨p, hp⟩ := hK.2 z
    obtain ⟨φ, hφ⟩ := e.surjective p
    refine ⟨Additive.ofMul (WithConv.toConv φ), ?_⟩
    change TateKummer.kummerPointToTorsion R S N u₀ q a hq (e φ) = z
    rw [hφ, hp]

/-- Geometric points of the quadratic Tate--Kummer generic fiber are additively equivalent
to the `N`-torsion of `Sˣ/q^ℤ`. -/
noncomputable def genericFiberTorsionAddEquiv
    (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n)
    (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (QuadraticDescent.discriminant R t n))
    (q a : Sˣ) (hq : a ^ N * Units.map (algebraMap R S) u₀ = q)
    (hqinj : Function.Injective fun z : ℤ ↦ q ^ z) :
    letI := coordinateBialgebra R N u₀ t n h2 hdisc
    Additive (WithConv
      (K ⊗[R] fixedSubalgebra R N u₀ t n →ₐ[K] S)) ≃+
        AddSubgroup.torsionBy
          (Additive (Sˣ ⧸ Subgroup.zpowers q)) (N : ℤ) := by
  letI := coordinateBialgebra R N u₀ t n h2 hdisc
  exact AddEquiv.ofBijective
    (genericFiberToTorsionAddHom R N u₀ t n K L S θ
      htrace hnorm h2 hdisc q a hq)
    (genericFiberToTorsionAddHom_bijective R N u₀ t n K L S θ
      htrace hnorm h2 hdisc q a hq hqinj)

end GenericFiber

end TateKummer.QuadraticTwist
