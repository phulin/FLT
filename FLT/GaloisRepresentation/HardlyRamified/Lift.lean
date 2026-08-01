/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThree
public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Lifting hardly ramified residual representations

If `ρ̄ : Gal(ℚ̄/ℚ) → GL₂(k)` is an irreducible hardly ramified mod-`ℓ`
representation, we construct (as part of the inputs to FLT) a hardly
ramified `ℓ`-adic lift to characteristic zero.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

universe u v

variable {k : Type u} [Finite k] [Field k]
    [TopologicalSpace k] [DiscreteTopology k]
    {p : ℕ} (hpodd : Odd p) [Fact p.Prime]
    [Algebra ℤ_[p] k]
    [IsLocalHom (algebraMap ℤ_[p] k)]
    (V : Type v) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2)

open TensorProduct

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K
local notation3 K:max "ᵃˡᵍ" => AlgebraicClosure K

/-- A complex conjugation in the absolute Galois group of `ℚ`: it is an involution and its
`p`-adic cyclotomic character is `-1`.  The construction extends ordinary complex conjugation
from the algebraic numbers inside `ℂ` to the chosen algebraic closure of `ℚ`. -/
theorem exists_odd_involution :
    ∃ c : Γ ℚ, c * c = 1 ∧
      ((cyclotomicCharacter (ℚ ᵃˡᵍ) p c.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = -1 := by
  sorry

/-- An irreducible hardly ramified residual representation is absolutely irreducible.  The
cyclotomic determinant makes complex conjugation an odd involution, and hence gives a
one-dimensional fixed space. -/
theorem isAbsolutelyIrreducible_of_isIrreducible
    [CharP k p] (hp : 3 < p) (ρ : FramedGaloisRep ℚ k (Fin 2))
    (hρirred : ρ.IsIrreducible) (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    Representation.IsAbsolutelyIrreducible.{u} ρ.toRepresentation := by
  obtain ⟨c, hc_sq, hc_cyclo⟩ := exists_odd_involution (p := p)
  letI : Fact (2 < p) := ⟨by omega⟩
  have hneg : (-1 : k) ≠ 1 := CharP.neg_one_ne_one k p
  have hc_rep_sq : (ρ.toRepresentation c).comp (ρ.toRepresentation c) = LinearMap.id := by
    change ρ c * ρ c = 1
    rw [← map_mul, hc_sq, map_one]
  have hc_det : LinearMap.det (ρ.toRepresentation c) = -1 := by
    change ρ.det c = -1
    rw [hρ.det c, hc_cyclo, map_neg, map_one]
  have hc_fixed :
      Module.finrank k (Module.End.eigenspace (ρ.toRepresentation c) 1) = 1 :=
    Representation.finrank_eigenspace_one_of_sq_eq_one_of_det_eq_neg_one
      (by simp) (ρ.toRepresentation c) hneg hc_rep_sq hc_det
  exact Representation.IsAbsolutelyIrreducible.of_finrank_eigenspace_eq_one
    ρ.toRepresentation hρirred hc_fixed

/--
The arithmetic core of the lifting theorem in residue characteristic greater than three,
after choosing a basis of the residual representation.  Keeping this input framed isolates
the deformation-theoretic construction from both the exceptional characteristic-three case
and the basis-independence argument below.
-/
theorem lifts_framed_of_three_lt_of_charP_of_isAbsolutelyIrreducible [CharP k p] (hp : 3 < p)
    (ρ : FramedGaloisRep ℚ k (Fin 2))
    [Representation.IsAbsolutelyIrreducible.{u} ρ.toRepresentation]
    (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := sorry

/-- Absolute irreducibility needed by the deformation-theoretic lifting theorem follows from
irreducibility and the cyclotomic determinant. -/
theorem lifts_framed_of_three_lt_of_charP [CharP k p] (hp : 3 < p)
    (ρ : FramedGaloisRep ℚ k (Fin 2)) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  letI : Representation.IsAbsolutelyIrreducible.{u} ρ.toRepresentation :=
    isAbsolutelyIrreducible_of_isIrreducible hpodd hp ρ hρirred hρ
  exact lifts_framed_of_three_lt_of_charP_of_isAbsolutelyIrreducible
    hpodd hp ρ hρirred hρ

/-- The local coefficient-field hypothesis already forces the residue field to have
characteristic `p`; this is the form used by the public lifting theorem. -/
theorem lifts_framed_of_three_lt (hp : 3 < p)
    (ρ : FramedGaloisRep ℚ k (Fin 2)) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  letI : CharP k p := PadicInt.charP_of_algebra_isLocalHom k
  exact lifts_framed_of_three_lt_of_charP hpodd hp ρ hρirred hρ

/-- The framed lifting theorem.  The characteristic-three case is vacuous by the mod-three
classification, so all arithmetic lifting work may be carried out under `3 < p`. -/
theorem lifts_framed (ρ : FramedGaloisRep ℚ k (Fin 2)) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  by_cases hp3 : p = 3
  · subst p
    exact (mod_three_not_isIrreducible (Fin 2 → k) (by simp) hρ hρirred).elim
  · apply lifts_framed_of_three_lt hpodd
      (by
        have hpge : 3 ≤ p := (Fact.out : p.Prime).odd_iff.mp hpodd
        omega) ρ hρirred hρ

/--
An irreducible mod p hardly ramified representation lifts to a p-adic one.
-/
theorem lifts (ρ : GaloisRep ℚ k V) (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd hV ρ) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R)
      (_ : TopologicalSpace R) (_ : IsTopologicalRing R)
      (_ : Algebra ℤ_[p] R) (_ : IsLocalHom (algebraMap ℤ_[p] R))
      (_ : Module.Finite ℤ_[p] R) (_ : Module.Free ℤ_[p] R)
      (_ : IsModuleTopology ℤ_[p] R)
      (_ : Algebra R k) (_ : IsScalarTower ℤ_[p] R k) (_ : ContinuousSMul R k)
      (W : Type v) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] V),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  have hfin : Module.finrank k V = 2 := Module.finrank_eq_of_rank_eq hV
  let b : Module.Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V hfin
  let e : V ≃ₗ[k] (Fin 2 → k) :=
    b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite k k (Fin 2)
  let τ : FramedGaloisRep ℚ k (Fin 2) := ρ.conj e
  have hτrank : Module.rank k (Fin 2 → k) = 2 := by simp
  have hτirred : τ.IsIrreducible :=
    (GaloisRep.isIrreducible_conj_iff ρ e).mp hρirred
  have hτ : IsHardlyRamified hpodd hτrank τ :=
    IsHardlyRamified.conj hpodd hV hτrank ρ hρ e
  obtain ⟨R, hRcomm, hRdomain, hRlocal, hRtop, hRtopRing, hRpAlg, hRlocalHom,
      hRfinite, hRfree, hRmoduleTopology, hRkAlg, hRkTower, hRkContinuous,
      W, hWadd, hWmodule, hWfinite, hWfree, hWrank, σ, r, hσ, hr⟩ :=
    lifts_framed hpodd τ hτirred hτ
  letI : CommRing R := hRcomm
  letI : IsDomain R := hRdomain
  letI : IsLocalRing R := hRlocal
  letI : TopologicalSpace R := hRtop
  letI : IsTopologicalRing R := hRtopRing
  letI : Algebra ℤ_[p] R := hRpAlg
  letI : IsLocalHom (algebraMap ℤ_[p] R) := hRlocalHom
  letI : Module.Finite ℤ_[p] R := hRfinite
  letI : Module.Free ℤ_[p] R := hRfree
  letI : IsModuleTopology ℤ_[p] R := hRmoduleTopology
  letI : Algebra R k := hRkAlg
  letI : IsScalarTower ℤ_[p] R k := hRkTower
  letI : ContinuousSMul R k := hRkContinuous
  letI : AddCommGroup W := hWadd
  letI : Module R W := hWmodule
  letI : Module.Finite R W := hWfinite
  letI : Module.Free R W := hWfree
  refine ⟨R, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, W, inferInstance, inferInstance, inferInstance, inferInstance,
    hWrank, σ, r.trans e.symm, hσ, ?_⟩
  calc
    (σ.baseChange k).conj (r.trans e.symm) =
        ((σ.baseChange k).conj r).conj e.symm := (GaloisRep.conj_trans _ _ _).symm
    _ = τ.conj e.symm := congrArg (GaloisRep.conj · e.symm) hr
    _ = ρ := (GaloisRep.conjEquiv e).left_inv ρ

end GaloisRepresentation.IsHardlyRamified
