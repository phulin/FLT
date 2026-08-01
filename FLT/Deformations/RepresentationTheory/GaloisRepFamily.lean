/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import Mathlib.NumberTheory.Padics.Complex
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.RingTheory.PicardGroup

/-!
# Compatible families of Galois representations

We define `GaloisRepFamily K E d`: a collection of `d`-dimensional
`E_λ`-adic Galois representations indexed by the finite places `λ` of a
number field `E`, together with the notion of compatibility.
-/

@[expose] public section

/-

## Compatible families

-/

-- Note that `λ` is a reserved symbol in Lean, as Lean is a functional programming language,
-- so instead of lambda-adic representations we're doing `φ`-adic ones.

set_option linter.unusedVariables false in
/-- `GaloisRepFamily K E d` is an (unrelated) collection of d-dimensional
  p-adic Galois representations of the absolute Galois group of the field K,
  parametrised by field maps from the number field `E` into the algebraic
  closure of ℚ_p as p runs through the primes.
-/
@[nolint unusedArguments]
def GaloisRepFamily (K : Type*) [Field K]
    (E : Type*) [Field E] [NumberField E] (d : ℕ) : Type _ :=
    ∀ {p : ℕ} (_ : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p]),
    GaloisRep K (AlgebraicClosure ℚ_[p]) (Fin d → (AlgebraicClosure ℚ_[p]))

open IsDedekindDomain NumberField Polynomial

local notation "Frob" => Field.AbsoluteGaloisGroup.adicArithFrob

/-- A family `ρ_λ` of `E_λ`-adic Galois representations `GaloisRepFamily K E d` of the
absolute Galois group of a number field `K` is *compatible* if there is a finite set `S` of
finite places of `K` and, for each finite place `v` of `K` not in `S`, a monic
degree `d` polynomial `P_v` with coefficients in `E`, such that if
`v` and `λ` do not lie above the same rational prime then `ρ_λ` is unramified at `v`
and `P_v` is the characteristic polynomial of `ρ_λ(Frob_v)`, where `Frob_v` denotes
an arithmetic Frobenius element.

This is the weakest possible concept of a compatible family but it will
suffice for our needs.
-/
def GaloisRepFamily.isCompatible {K : Type*} [Field K] [NumberField K]
    {E : Type*} [Field E] [NumberField E] {d : ℕ} (ρ : GaloisRepFamily K E d) : Prop :=
    ∃ (S : Finset (HeightOneSpectrum (𝓞 K))) (Pv : HeightOneSpectrum (𝓞 K) → E[X]),
    ∀ {p : ℕ} (hfp : Fact (p.Prime)) (φ : E →+* AlgebraicClosure ℚ_[p])
      (v : HeightOneSpectrum (𝓞 K)),
    v ∉ S → (p : 𝓞 K) ∉ v.asIdeal →
      (ρ hfp φ).IsUnramifiedAt v ∧ ((ρ hfp φ).toLocal v (Frob v)).charpoly = (Pv v).map φ

/-- Two members of a compatible family have characteristic polynomials obtained from one common
polynomial away from a finite exceptional set and their residue characteristics. -/
theorem GaloisRepFamily.isCompatible.common_charpoly
    {K : Type*} [Field K] [NumberField K]
    {E : Type*} [Field E] [NumberField E] {d : ℕ}
    {ρ : GaloisRepFamily K E d} (hρ : ρ.isCompatible) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ {p q : ℕ} (hp : Fact p.Prime) (hq : Fact q.Prime)
        (φp : E →+* AlgebraicClosure ℚ_[p]) (φq : E →+* AlgebraicClosure ℚ_[q])
        (v : HeightOneSpectrum (𝓞 K)),
        v ∉ S → (p : 𝓞 K) ∉ v.asIdeal → (q : 𝓞 K) ∉ v.asIdeal →
          ∃ P : E[X],
            (ρ hp φp).IsUnramifiedAt v ∧
            ((ρ hp φp).toLocal v (Frob v)).charpoly = P.map φp ∧
            (ρ hq φq).IsUnramifiedAt v ∧
            ((ρ hq φq).toLocal v (Frob v)).charpoly = P.map φq := by
  obtain ⟨S, Pv, hPv⟩ := hρ
  refine ⟨S, ?_⟩
  intro p q hp hq φp φq v hvS hpv hqv
  have hpdata := hPv hp φp v hvS hpv
  have hqdata := hPv hq φq v hvS hqv
  exact ⟨Pv v, hpdata.1, hpdata.2, hqdata.1, hqdata.2⟩

/-- In dimension two, compatibility gives a common algebraic Frobenius trace away from a finite
exceptional set and the two residue characteristics. -/
theorem GaloisRepFamily.isCompatible.common_trace
    {K : Type*} [Field K] [NumberField K]
    {E : Type*} [Field E] [NumberField E]
    {ρ : GaloisRepFamily K E 2} (hρ : ρ.isCompatible) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)),
      ∀ {p q : ℕ} (hp : Fact p.Prime) (hq : Fact q.Prime)
        (φp : E →+* AlgebraicClosure ℚ_[p]) (φq : E →+* AlgebraicClosure ℚ_[q])
        (v : HeightOneSpectrum (𝓞 K)),
        v ∉ S → (p : 𝓞 K) ∉ v.asIdeal → (q : 𝓞 K) ∉ v.asIdeal →
          ∃ a : E,
            (ρ hp φp).IsUnramifiedAt v ∧
            LinearMap.trace _ _ ((ρ hp φp).toLocal v (Frob v)) = φp a ∧
            (ρ hq φq).IsUnramifiedAt v ∧
            LinearMap.trace _ _ ((ρ hq φq).toLocal v (Frob v)) = φq a := by
  obtain ⟨S, hS⟩ := hρ.common_charpoly
  refine ⟨S, ?_⟩
  intro p q hp hq φp φq v hvS hpv hqv
  obtain ⟨P, hpU, hpP, hqU, hqP⟩ := hS hp hq φp φq v hvS hpv hqv
  refine ⟨-P.coeff 1, hpU, ?_, hqU, ?_⟩
  · let b := Pi.basisFun (AlgebraicClosure ℚ_[p]) (Fin 2)
    rw [LinearMap.trace_eq_matrix_trace _ b, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hpP]
    norm_num
  · let b := Pi.basisFun (AlgebraicClosure ℚ_[q]) (Fin 2)
    rw [LinearMap.trace_eq_matrix_trace _ b, Matrix.trace_eq_neg_charpoly_coeff,
      LinearMap.charpoly_toMatrix, hqP]
    norm_num
