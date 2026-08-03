/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ModThree
public import FLT.Deformations.CoefficientRing
public import FLT.Deformations.HardlyRamified
public import FLT.Deformations.RepresentationTheory.Irreducible
public import FLT.Mathlib.NumberTheory.Padics.PadicIntegers

import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import FLT.Deformations.CharacteristicZeroPoint
import FLT.Mathlib.RingTheory.Flat.TorsionFree
import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology

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

/-- A realization of complex conjugation on the chosen algebraic closure of `ℚ`.  The
embedding into `ℂ` is noncanonical, but conjugation preserves its algebraic image and hence
restricts back to an automorphism of `AlgebraicClosure ℚ`. -/
theorem exists_complexEmbedding_conjugation :
    ∃ (ι : (ℚ ᵃˡᵍ) →ₐ[ℚ] ℂ) (c : Γ ℚ), c * c = 1 ∧
      ∀ x : ℚ ᵃˡᵍ, ι (c x) = (starRingEnd ℂ) (ι x) := by
  letI : Algebra.IsAlgebraic ℚ (ℚ ᵃˡᵍ) := AlgebraicClosure.isAlgebraic ℚ
  let ι : (ℚ ᵃˡᵍ) →ₐ[ℚ] ℂ := IsAlgClosed.lift
  letI := ι.toRingHom.toAlgebra
  letI : Normal ℚ (ℚ ᵃˡᵍ) := normal_iff.2 fun x ↦
    ⟨((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic x).isIntegral, IsAlgClosed.splits _⟩
  let φ : (ℚ ᵃˡᵍ) →ₐ[ℚ] ℂ :=
    (Complex.conjAe.restrictScalars ℚ).toAlgHom.comp ι
  let c₀ : (ℚ ᵃˡᵍ) ≃ₐ[ℚ] (ℚ ᵃˡᵍ) := φ.restrictNormal' (ℚ ᵃˡᵍ)
  let c : Γ ℚ := c₀
  have hc (x : ℚ ᵃˡᵍ) : ι (c x) = (starRingEnd ℂ) (ι x) := by
    change algebraMap (ℚ ᵃˡᵍ) ℂ (c₀ x) = φ x
    exact AlgHom.restrictNormal_commutes φ (ℚ ᵃˡᵍ) x
  have hc_sq : c * c = 1 := by
    apply AlgEquiv.ext
    intro x
    apply ι.injective
    change ι (c (c x)) = ι x
    rw [hc, hc]
    exact star_star (ι x)
  exact ⟨ι, c, hc_sq, hc⟩

private lemma pow_pred_eq_inv_of_pow_eq_one {G : Type*} [Group G] {a : G} {n : ℕ}
    (hn : 0 < n) (ha : a ^ n = 1) : a ^ (n - 1) = a⁻¹ := by
  apply mul_left_cancel
  calc
    a * a ^ (n - 1) = a ^ n := by
      rw [← pow_succ', Nat.sub_add_cancel hn]
    _ = 1 := ha
    _ = a * a⁻¹ := (mul_inv_cancel a).symm

/-- A complex conjugation in the absolute Galois group of `ℚ`: it is an involution and its
`p`-adic cyclotomic character is `-1`.  The construction extends ordinary complex conjugation
from the algebraic numbers inside `ℂ` to the chosen algebraic closure of `ℚ`. -/
theorem exists_odd_involution :
    ∃ c : Γ ℚ, c * c = 1 ∧
      ((cyclotomicCharacter (ℚ ᵃˡᵍ) p c.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = -1 := by
  obtain ⟨ι, c, hc_sq, hc⟩ := exists_complexEmbedding_conjugation
  refine ⟨c, hc_sq, ?_⟩
  refine PadicInt.ext_of_toZModPow.mp fun n ↦ ?_
  rw [cyclotomicCharacter.toZModPow, map_neg, map_one]
  apply Eq.symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  have hval : ((-1 : ZMod (p ^ n))).val = p ^ n - 1 := by
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpn.ne'
    rw [hm, ZMod.val_neg_one]
    omega
  let ζ : ℂˣ := Units.map ι.toRingHom t
  have hζ : ζ ∈ rootsOfUnity (p ^ n) ℂ := by
    change ζ ^ (p ^ n) = 1
    dsimp only [ζ]
    rw [← map_pow, (mem_rootsOfUnity (p ^ n) t).mp ht, map_one]
  have hconj := Complex.conj_rootsOfUnity hζ
  have hpred := congrArg Units.val
    (pow_pred_eq_inv_of_pow_eq_one hpn ((mem_rootsOfUnity (p ^ n) ζ).mp hζ))
  apply ι.injective
  change ι (c (t : ℚ ᵃˡᵍ)) = ι ((t : ℚ ᵃˡᵍ) ^ ((-1 : ZMod (p ^ n)).val))
  rw [hc, hval, map_pow]
  exact hconj.trans hpred.symm

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

/-- The output of the finiteness and Böckle-presentation argument needed before the final
DVR commutative-algebra step.  Finiteness is the conclusion of Khare--Wintenberger,
Proposition 3.8, obtained by potential modularity and the totally-real `R = T` theorems.
The regular action of a uniformizer is the consequence of their balanced presentation
(Proposition 3.4) used in the proof of Theorem 3.7. -/
def HasBockleFinitenessData
    (R D : Type u) [CommRing R] [CommRing D] [Algebra R D] : Prop :=
  ∃ π : R, Irreducible π ∧ Module.Finite R D ∧ IsSMulRegular D π

/-- The remaining modern arithmetic input for hardly ramified lifts, stated at the exact point
where the potential-modularity finiteness argument and Böckle's balanced-presentation argument
meet the formal DVR algebra.  Flatness and the topology are derived below rather than included
in this input. -/
theorem exists_hardlyRamifiedBockleFinitenessData (hp : 3 < p)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [IsLocalHom (algebraMap ℤ_[p] R)]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (rhoRes : (Deformation.repnFunctor (Fin 2) (Γ ℚ) R).obj .residueField)
    [Representation.IsAbsolutelyIrreducible.{u}
      (Deformation.toRepresentation rhoRes)]
    (hrhoRes : rhoRes ∈
      (Deformation.hardlyRamifiedFunctor R p hpodd).obj .residueField) :
    let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoRes
    HasBockleFinitenessData R D := by
  sorry

/-- Finiteness plus the regular action of a uniformizer imply flatness over the coefficient DVR.
The key formal point is that every nonzero scalar is a unit times a power of the uniformizer,
so uniformizer-regularity gives torsion-freeness and hence flatness. -/
theorem hardlyRamifiedUniversalRing_finiteFlat_arithmetic (hp : 3 < p)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [IsLocalHom (algebraMap ℤ_[p] R)]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (rhoRes : (Deformation.repnFunctor (Fin 2) (Γ ℚ) R).obj .residueField)
    [Representation.IsAbsolutelyIrreducible.{u}
      (Deformation.toRepresentation rhoRes)]
    (hrhoRes : rhoRes ∈
      (Deformation.hardlyRamifiedFunctor R p hpodd).obj .residueField) :
    let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoRes
    Module.Finite R D ∧ Module.Flat R D := by
  let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoRes
  obtain ⟨π, hπ, hfinite, hregular⟩ :=
    exists_hardlyRamifiedBockleFinitenessData hpodd hp R rhoRes hrhoRes
  change Module.Finite R D ∧ Module.Flat R D
  exact ⟨hfinite, Module.Flat.of_isSMulRegular_irreducible hπ hregular⟩

/-- Finite-flatness supplies all the data formerly bundled into the modern input.  In
particular, the topology of the universal pro-Artinian ring is forced to be its finite-module
topology, so that clause is a formal consequence rather than part of Taylor--Wiles. -/
theorem hardlyRamifiedUniversalRing_finiteFlat (hp : 3 < p)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [IsLocalHom (algebraMap ℤ_[p] R)]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    [IsNoetherianRing R] [Finite (IsLocalRing.ResidueField R)]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (rhoRes : (Deformation.repnFunctor (Fin 2) (Γ ℚ) R).obj .residueField)
    [Representation.IsAbsolutelyIrreducible.{u}
      (Deformation.toRepresentation rhoRes)]
    (hrhoRes : rhoRes ∈
      (Deformation.hardlyRamifiedFunctor R p hpodd).obj .residueField) :
    let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoRes
    Module.Finite R D ∧ Module.Flat R D ∧ IsModuleTopology R D := by
  let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoRes
  have hD := hardlyRamifiedUniversalRing_finiteFlat_arithmetic
    hpodd hp R rhoRes hrhoRes
  change Module.Finite R D ∧ Module.Flat R D at hD
  letI : Module.Finite R D := hD.1
  exact ⟨hD.1, hD.2,
    Deformation.isModuleTopology_of_isProartinian_of_finiteFree_base ℤ_[p] R D⟩

/--
The formal passage from the universal hardly ramified deformation ring to the finite-flat
deformation data used by the characteristic-zero extraction.  All arithmetic content is
isolated in `hardlyRamifiedUniversalRing_finiteFlat`; this theorem constructs the universal
representation, its residue map, and the required basis change.

The passage from this finite flat ring to a characteristic-zero domain and an actual lift is
commutative algebra and is proved in `exists_minimalLift_over_coefficientRing` below.
-/
theorem exists_finiteFlat_minimalDeformation [CharP k p] (hp : 3 < p)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [IsLocalHom (algebraMap ℤ_[p] R)]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    [Algebra R k] [IsLocalHom (algebraMap R k)] [IsScalarTower ℤ_[p] R k]
    [ContinuousSMul R k]
    (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (hresidueEquiv : ∀ r, residueEquiv (IsLocalRing.residue R r) = algebraMap R k r)
    (ρ : FramedGaloisRep ℚ k (Fin 2))
    [Representation.IsAbsolutelyIrreducible.{u} ρ.toRepresentation]
    (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (D : Type u) (_ : CommRing D) (_ : IsLocalRing D)
      (_ : Algebra R D) (_ : Algebra ℤ_[p] D) (_ : IsScalarTower ℤ_[p] R D)
      (_ : IsLocalHom (algebraMap R D))
      (_ : Module.Finite R D) (_ : Module.Flat R D)
      (_ : TopologicalSpace D) (_ : IsTopologicalRing D) (_ : IsModuleTopology R D)
      (_ : Algebra D k) (_ : IsLocalHom (algebraMap D k))
      (_ : IsScalarTower R D k) (_ : IsScalarTower ℤ_[p] D k)
      (_ : ContinuousSMul D k) (_ : Function.Surjective (algebraMap D k))
      (τ : FramedGaloisRep ℚ D (Fin 2))
      (r : k ⊗[D] (Fin 2 → D) ≃ₗ[k] (Fin 2 → k)),
      IsHardlyRamified hpodd (by simp) τ ∧
        (GaloisRep.baseChange k (τ : GaloisRep ℚ D (Fin 2 → D))).conj r = ρ := by
  letI : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ_[p] R
  letI : Finite (IsLocalRing.ResidueField R) :=
    Finite.of_equiv k residueEquiv.symm.toEquiv
  letI : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    Deformation.isAdicComplete_of_finiteFree_moduleTopology ℤ_[p] R
  let kappaR : Deformation.ProartinianCat R := .residueField
  let residueRingEquiv : (kappaR : Type u) ≃+* k :=
    Deformation.ProartinianCat.residueFieldRingEquiv R residueEquiv
  letI : Finite kappaR :=
    Finite.of_equiv k residueRingEquiv.symm.toEquiv
  letI : Algebra ℤ_[p] kappaR := Algebra.compHom kappaR (algebraMap ℤ_[p] R)
  letI : IsLocalHom (algebraMap ℤ_[p] kappaR) := by
    change IsLocalHom ((algebraMap R kappaR).comp (algebraMap ℤ_[p] R))
    infer_instance
  letI : CharP kappaR p := PadicInt.charP_of_algebra_isLocalHom kappaR
  let rhoRes := Deformation.residualRepresentation R residueEquiv ρ
  have hrhoResIrred : (Deformation.toRepresentation rhoRes).IsIrreducible :=
    Deformation.residualRepresentation_isIrreducible R residueEquiv ρ hρirred
  have hrhoResMem : rhoRes ∈
      (Deformation.hardlyRamifiedFunctor R p hpodd).obj .residueField :=
    Deformation.residualRepresentation_mem_hardlyRamifiedFunctor
      hpodd R residueEquiv hresidueEquiv ρ hρ
  have hrhoResHard : IsHardlyRamified hpodd (by simp)
      (Deformation.toFramedGaloisRep rhoRes) := by
    exact hrhoResMem
  letI : Representation.IsAbsolutelyIrreducible.{u}
      (Deformation.toRepresentation rhoRes) :=
    isAbsolutelyIrreducible_of_isIrreducible hpodd hp
      (Deformation.toFramedGaloisRep rhoRes) hrhoResIrred hrhoResHard
  let D := Deformation.hardlyRamifiedUniversalRing R p hpodd rhoRes hrhoResMem
  have hDfiniteFlat :=
    hardlyRamifiedUniversalRing_finiteFlat hpodd hp R rhoRes hrhoResMem
  change Module.Finite R D ∧ Module.Flat R D ∧ IsModuleTopology R D at hDfiniteFlat
  letI : Module.Finite R D := hDfiniteFlat.1
  letI : Module.Flat R D := hDfiniteFlat.2.1
  letI : IsModuleTopology R D := hDfiniteFlat.2.2
  letI : Algebra ℤ_[p] D := Algebra.compHom D (algebraMap ℤ_[p] R)
  letI : IsScalarTower ℤ_[p] R D :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let fDk : D →+* k := residueRingEquiv.toRingHom.comp
    (Deformation.ProartinianCat.toResidueField D).hom.toRingHom
  have hfDkSurjective : Function.Surjective fDk :=
    residueRingEquiv.surjective.comp
      (Deformation.ProartinianCat.toResidueField_surjective D)
  letI : Algebra D k := fDk.toAlgebra
  letI : IsLocalHom (algebraMap D k) :=
    IsLocalHom.of_surjective fDk hfDkSurjective
  letI : IsScalarTower R D k := IsScalarTower.of_algebraMap_eq fun x ↦ by
    calc
      algebraMap R k x = residueRingEquiv (IsLocalRing.residue R x) :=
        (hresidueEquiv x).symm
      _ = residueRingEquiv
          ((Deformation.ProartinianCat.toResidueField D).hom (algebraMap R D x)) := by
        congr 1
        exact ((Deformation.ProartinianCat.toResidueField D).hom.commutes x).symm
  letI : IsScalarTower ℤ_[p] D k := IsScalarTower.of_algebraMap_eq fun x ↦ by
    calc
      algebraMap ℤ_[p] k x = algebraMap R k (algebraMap ℤ_[p] R x) :=
        IsScalarTower.algebraMap_apply ℤ_[p] R k x
      _ = algebraMap D k (algebraMap R D (algebraMap ℤ_[p] R x)) :=
        IsScalarTower.algebraMap_apply R D k _
      _ = algebraMap D k (algebraMap ℤ_[p] D x) := rfl
  have hresidueRingEquivContinuous : Continuous residueRingEquiv :=
    continuous_of_discreteTopology
  have hfDk : Continuous fDk :=
    hresidueRingEquivContinuous.comp
      (Deformation.ProartinianCat.toResidueField D).hom.cont
  letI : ContinuousSMul D k :=
    continuousSMul_of_algebraMap D k hfDk
  let tau : FramedGaloisRep ℚ D (Fin 2) :=
    Deformation.hardlyRamifiedUniversalGaloisRep R p hpodd rhoRes hrhoResMem
  have htau : IsHardlyRamified hpodd (by simp) tau := by
    exact (Deformation.hardlyRamifiedUniversalRepresentation_conditions
      R p hpodd rhoRes hrhoResMem).2
  have hreduce := Deformation.hardlyRamifiedUniversalRepresentation_reduces
    R p hpodd rhoRes hrhoResMem
  have hreduceFramed :
      tau.baseChange
          (Deformation.ProartinianCat.toResidueField D).hom.toRingHom
          (Deformation.ProartinianCat.toResidueField D).hom.cont =
        Deformation.toFramedGaloisRep rhoRes := by
    have h := congrArg (fun x ↦ Deformation.toFramedGaloisRep x) hreduce
    rw [Deformation.toFramedGaloisRep_map] at h
    exact h
  have hback :=
    Deformation.toFramedGaloisRep_residualRepresentation_baseChange
      R residueEquiv ρ
  have htauReduceFramed : tau.baseChange fDk hfDk = ρ := by
    calc
      tau.baseChange fDk hfDk =
          (tau.baseChange
              (Deformation.ProartinianCat.toResidueField D).hom.toRingHom
              (Deformation.ProartinianCat.toResidueField D).hom.cont).baseChange
            residueRingEquiv.toRingHom continuous_of_discreteTopology := by
              rw [FramedGaloisRep.baseChange_baseChange]
      _ = (Deformation.toFramedGaloisRep rhoRes).baseChange
            residueRingEquiv.toRingHom continuous_of_discreteTopology := by
              rw [hreduceFramed]
      _ = ρ := hback
  let r : k ⊗[D] (Fin 2 → D) ≃ₗ[k] (Fin 2 → k) :=
    ((Pi.basisFun D (Fin 2)).baseChange k).repr ≪≫ₗ
      Finsupp.linearEquivFunOnFinite k k (Fin 2)
  have htauReduce :
      (GaloisRep.baseChange k (tau : GaloisRep ℚ D (Fin 2 → D))).conj r = ρ := by
    simpa only [FramedGaloisRep.baseChange_def, GaloisRep.frame, r] using
      htauReduceFramed
  exact ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hfDkSurjective,
    tau, r, htau, htauReduce⟩

/--
The arithmetic input to the hardly-ramified lifting theorem, after fixing an unramified
coefficient DVR `R` with residue field `k`.  The lift is allowed to have coefficients in a
finite free local `R`-algebra `S` with the same residue field.  This extension is essential:
the rationality of a minimal lift cannot in general be controlled, so the lift need not be
defined over `R` itself.

This is the level-two, weight-two specialization of Khare--Wintenberger, *On Serre's conjecture
for 2-dimensional mod p representations of Gal(Qbar/Q)*, Theorem 3.3.  Their Theorem 3.7 proves
that the relevant minimal deformation ring is finite flat over the Witt-vector coefficient
ring; a minimal prime outside `p` and normalization then produce the finite coefficient
extension and the characteristic-zero point.  The reductions from the hardly-ramified
hypotheses to their S-type, cyclotomic-restriction, and Serre-weight hypotheses belong to this
arithmetic input as well.

The coefficient-ring construction, the exceptional characteristic-three case, and the removal
of a chosen residual basis are all handled separately below.
-/
theorem exists_minimalLift_over_coefficientRing [CharP k p] (hp : 3 < p)
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [TopologicalSpace R] [IsTopologicalRing R]
    [Algebra ℤ_[p] R] [IsLocalHom (algebraMap ℤ_[p] R)]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [IsModuleTopology ℤ_[p] R]
    [Algebra R k] [IsLocalHom (algebraMap R k)] [IsScalarTower ℤ_[p] R k]
    [ContinuousSMul R k]
    (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (hresidueEquiv : ∀ r, residueEquiv (IsLocalRing.residue R r) = algebraMap R k r)
    (ρ : FramedGaloisRep ℚ k (Fin 2))
    [Representation.IsAbsolutelyIrreducible.{u} ρ.toRepresentation]
    (hρirred : ρ.IsIrreducible)
    (hρ : IsHardlyRamified hpodd (by simp) ρ) :
    ∃ (S : Type u) (_ : CommRing S) (_ : IsDomain S) (_ : IsLocalRing S)
      (_ : TopologicalSpace S) (_ : IsTopologicalRing S)
      (_ : Algebra ℤ_[p] S) (_ : Algebra R S) (_ : IsScalarTower ℤ_[p] R S)
      (_ : IsLocalHom (algebraMap R S))
      (_ : Module.Finite R S) (_ : Module.Free R S) (_ : IsModuleTopology R S)
      (_ : Algebra S k) (_ : IsLocalHom (algebraMap S k))
      (_ : IsScalarTower R S k) (_ : IsScalarTower ℤ_[p] S k) (_ : ContinuousSMul S k)
      (W : Type u) (_ : AddCommGroup W) (_ : Module S W) (_ : Module.Finite S W)
      (_ : Module.Free S W) (hW : Module.rank S W = 2)
      (σ : GaloisRep ℚ S W) (r : k ⊗[S] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  obtain ⟨D, hDcomm, hDlocal, hRDAlg, hZpDAlg, hZpRDTower, hRDlocalHom,
      hRDfinite, hRDflat, hDtop, hDtopRing, hRDmoduleTopology, hDkAlg,
      hDklocalHom, hRDkTower, hZpDkTower, hDkContinuous, hDksurj, τ, rD,
      hτ, hτred⟩ :=
    exists_finiteFlat_minimalDeformation hpodd hp R residueEquiv hresidueEquiv
      ρ hρirred hρ
  letI : CommRing D := hDcomm
  letI : IsLocalRing D := hDlocal
  letI : Algebra R D := hRDAlg
  letI : Algebra ℤ_[p] D := hZpDAlg
  letI : IsScalarTower ℤ_[p] R D := hZpRDTower
  letI : IsLocalHom (algebraMap R D) := hRDlocalHom
  letI : Module.Finite R D := hRDfinite
  letI : Module.Flat R D := hRDflat
  letI : Module.Free R D := Module.free_of_flat_of_isLocalRing
  letI : TopologicalSpace D := hDtop
  letI : IsTopologicalRing D := hDtopRing
  letI : IsModuleTopology R D := hRDmoduleTopology
  letI : Algebra D k := hDkAlg
  letI : IsLocalHom (algebraMap D k) := hDklocalHom
  letI : IsScalarTower R D k := hRDkTower
  letI : IsScalarTower ℤ_[p] D k := hZpDkTower
  letI : ContinuousSMul D k := hDkContinuous
  obtain ⟨P, hPmin, hRinj, hRSfinite, hRSfree⟩ :=
    Deformation.exists_finiteFree_characteristicZero_minimalPrime_of_dvr R D
  letI : P.IsPrime := hPmin.1.1
  let S := D ⧸ P
  letI : CommRing S := inferInstance
  letI : IsDomain S := inferInstance
  letI : IsLocalRing S := inferInstance
  letI : Algebra D S := inferInstance
  letI : Algebra R S := inferInstance
  letI : Algebra ℤ_[p] S := inferInstance
  letI : IsScalarTower R D S := inferInstance
  letI : IsScalarTower ℤ_[p] R S := inferInstance
  letI : IsScalarTower ℤ_[p] D S := inferInstance
  letI : IsLocalHom (algebraMap D S) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  letI : IsLocalHom (algebraMap R S) := by
    rw [IsScalarTower.algebraMap_eq R D S]
    infer_instance
  letI : Module.Finite R S := hRSfinite
  letI : Module.Free R S := hRSfree
  letI : TopologicalSpace S := moduleTopology R S
  letI : IsModuleTopology R S := ⟨rfl⟩
  letI : IsTopologicalRing S := IsModuleTopology.isTopologicalRing R S
  letI : IsModuleTopology D S := (IsModuleTopology.trans R D S).mp inferInstance
  letI : IsResidueAlgebra D S := inferInstance
  letI : Module.Finite ℤ_[p] D := Module.Finite.trans R D
  letI : Module.Free ℤ_[p] D :=
    Module.Free.trans (R := ℤ_[p]) (S := R) (M := D)
  letI : IsModuleTopology ℤ_[p] D :=
    (IsModuleTopology.trans ℤ_[p] R D).mpr inferInstance
  letI : IsProartinian D :=
    Deformation.isProartinian_of_finiteFree_moduleTopology ℤ_[p] D
  letI : Module.Finite ℤ_[p] S := Module.Finite.trans R S
  letI : Module.Free ℤ_[p] S :=
    Module.Free.trans (R := ℤ_[p]) (S := R) (M := S)
  letI : IsModuleTopology ℤ_[p] S :=
    (IsModuleTopology.trans ℤ_[p] R S).mpr inferInstance
  letI : IsProartinian S :=
    Deformation.isProartinian_of_finiteFree_moduleTopology ℤ_[p] S
  have hPker : P ≤ RingHom.ker (algebraMap D k) := by
    rw [IsLocalRing.ker_eq_maximalIdeal (algebraMap D k) hDksurj]
    exact IsLocalRing.le_maximalIdeal_of_isPrime P
  let fSk : S →+* k := Ideal.Quotient.lift P (algebraMap D k) hPker
  letI : Algebra S k := fSk.toAlgebra
  have hSksurj : Function.Surjective (algebraMap S k) := by
    intro x
    obtain ⟨d, rfl⟩ := hDksurj x
    exact ⟨Ideal.Quotient.mk P d, rfl⟩
  letI : IsLocalHom (algebraMap S k) :=
    IsLocalHom.of_surjective _ hSksurj
  letI : IsScalarTower D S k := IsScalarTower.of_algebraMap_eq fun d ↦ by
    rfl
  letI : IsScalarTower R S k := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R k r = algebraMap D k (algebraMap R D r)
    exact IsScalarTower.algebraMap_apply R D k r
  letI : IsScalarTower ℤ_[p] S k := IsScalarTower.of_algebraMap_eq fun z ↦ by
    change algebraMap ℤ_[p] k z = algebraMap D k (algebraMap ℤ_[p] D z)
    exact IsScalarTower.algebraMap_apply ℤ_[p] D k z
  have hSkcont : Continuous (algebraMap S k) :=
    IsModuleTopology.continuous_of_ringHom (R := R) (A := S) (B := k)
      (algebraMap S k) (by
        rw [show (algebraMap S k).comp (algebraMap R S) = algebraMap R k by
          ext r
          exact (IsScalarTower.algebraMap_apply R S k r).symm]
        exact continuous_algebraMap R k)
  letI : ContinuousSMul S k :=
    continuousSMul_of_algebraMap S k hSkcont
  let W := S ⊗[D] (Fin 2 → D)
  letI : AddCommGroup W := inferInstance
  letI : Module S W := inferInstance
  letI : Module.Finite S W := inferInstance
  letI : Module.Free S W := inferInstance
  have hW : Module.rank S W = 2 := rank_two_baseChange (by simp)
  let σ : GaloisRep ℚ S W :=
    GaloisRep.baseChange S (τ : GaloisRep ℚ D (Fin 2 → D))
  have hσ : IsHardlyRamified hpodd hW σ :=
    IsHardlyRamified.baseChange hpodd (by simp) hW τ hτ
  let e : k ⊗[S] W ≃ₗ[k] k ⊗[D] (Fin 2 → D) :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange D S k k (Fin 2 → D)
  let r : k ⊗[S] W ≃ₗ[k] (Fin 2 → k) := e.trans rD
  have hσred : (σ.baseChange k).conj r = ρ := by
    dsimp [σ]
    rw [GaloisRep.baseChange_baseChange, GaloisRep.conj_trans]
    have heq : e.symm.trans (e.trans rD) = rD := by
      ext
      simp [e]
    rw [heq]
    exact hτred
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    W, inferInstance, inferInstance, inferInstance, inferInstance, hW, σ, r, hσ, hσred⟩

/--
The arithmetic core of the lifting theorem in residue characteristic greater than three,
after choosing a basis of the residual representation.  First construct the unramified
coefficient DVR `R`, then apply `exists_minimalLift_over_coefficientRing` to obtain its finite
free local coefficient extension `S`.  Finiteness, freeness, and the module topology descend
along the tower `ℤ_[p] → R → S`.
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
      (W : Type u) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
      (_ : Module.Free R W) (hW : Module.rank R W = 2)
      (σ : GaloisRep ℚ R W) (r : k ⊗[R] W ≃ₗ[k] (Fin 2 → k)),
    IsHardlyRamified hpodd hW σ ∧ (σ.baseChange k).conj r = ρ := by
  obtain ⟨R, hRcomm, hRdomain, hRdvr, hRtop, hRtopRing, hRpAlg, hRlocalHom,
      hRfinite, hRfree, hRmoduleTopology, hRkAlg, hRkTower, hRkContinuous,
      hRkLocalHom, residueEquiv, hresidueEquiv⟩ :=
    Deformation.exists_unramified_coefficientRing (k := k) (p := p)
  letI : CommRing R := hRcomm
  letI : IsDomain R := hRdomain
  letI : IsDiscreteValuationRing R := hRdvr
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
  letI : IsLocalHom (algebraMap R k) := hRkLocalHom
  obtain ⟨S, hScomm, hSdomain, hSlocal, hStop, hStopRing, hZpSAlg, hRSAlg,
      hZpRSTower, hRSlocalHom, hRSfinite, hRSfree, hRSmoduleTopology, hSkAlg,
      hSklocalHom, hRSkTower, hZpSkTower, hSkContinuous, W, hWadd, hWmodule,
      hWfinite, hWfree, hWrank, σ, r, hσ⟩ :=
    exists_minimalLift_over_coefficientRing hpodd hp R residueEquiv hresidueEquiv ρ hρirred hρ
  letI : CommRing S := hScomm
  letI : IsDomain S := hSdomain
  letI : IsLocalRing S := hSlocal
  letI : TopologicalSpace S := hStop
  letI : IsTopologicalRing S := hStopRing
  letI : Algebra ℤ_[p] S := hZpSAlg
  letI : Algebra R S := hRSAlg
  letI : IsScalarTower ℤ_[p] R S := hZpRSTower
  letI : IsLocalHom (algebraMap R S) := hRSlocalHom
  letI : Module.Finite R S := hRSfinite
  letI : Module.Free R S := hRSfree
  letI : IsModuleTopology R S := hRSmoduleTopology
  letI : Algebra S k := hSkAlg
  letI : IsLocalHom (algebraMap S k) := hSklocalHom
  letI : IsScalarTower R S k := hRSkTower
  letI : IsScalarTower ℤ_[p] S k := hZpSkTower
  letI : ContinuousSMul S k := hSkContinuous
  letI : Module.Finite ℤ_[p] S := Module.Finite.trans R S
  letI : Module.Free ℤ_[p] S := Module.Free.trans (R := ℤ_[p]) (S := R) (M := S)
  letI : IsModuleTopology ℤ_[p] S :=
    (IsModuleTopology.trans ℤ_[p] R S).mpr inferInstance
  exact ⟨S, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, W, hWadd, hWmodule, hWfinite, hWfree, hWrank, σ, r, hσ⟩

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
      (W : Type u) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
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
      (W : Type u) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
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
      (W : Type u) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
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
      (W : Type u) (_ : AddCommGroup W) (_ : Module R W) (_ : Module.Finite R W)
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
