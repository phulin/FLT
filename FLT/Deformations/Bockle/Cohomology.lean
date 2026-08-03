/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle
public import FLT.Deformations.Bockle.PowerSeries
public import FLT.Deformations.RepresentationTheory.Adjoint
public import FLT.Deformations.RepresentationTheory.Carayol
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Cohomological inputs for Böckle presentations

This file isolates the cohomology groups which control a fixed-determinant rank-two
deformation problem.  The first input is the elementary vanishing of
`H⁰(G, ad⁰(ρ))`: an invariant endomorphism is scalar by absolute irreducibility, and a
scalar trace-zero endomorphism is zero when the characteristic is not two.
-/

@[expose] public section

universe u v

namespace Representation

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- An invariant trace-zero endomorphism of an absolutely irreducible rank-two
representation commutes with the representation. -/
theorem commute_of_mem_traceZeroAdjoint_invariants
    (rho : Representation k G (Fin 2 → k))
    (f : (traceZeroAdjoint rho).invariants) (g : G) :
    Commute (rho g) (f.1.1 : Module.End k (Fin 2 → k)) := by
  have hconj :
      rho g * (f.1.1 : Module.End k (Fin 2 → k)) * rho g⁻¹ = f.1.1 := by
    exact congrArg Subtype.val (f.2 g)
  rw [Commute]
  calc
    rho g * (f.1.1 : Module.End k (Fin 2 → k)) =
        (rho g * f.1.1 * rho g⁻¹) * rho g := by
          rw [mul_assoc, ← map_mul]
          simp
    _ = f.1.1 * rho g := by rw [hconj]

/-- Every invariant vector in `ad⁰(ρ)` is zero for an absolutely irreducible rank-two
representation in characteristic different from two. -/
theorem eq_zero_of_mem_traceZeroAdjoint_invariants
    [NeZero (2 : k)] (rho : Representation k G (Fin 2 → k))
    [rho.IsAbsolutelyIrreducible.{u}]
    (f : (traceZeroAdjoint rho).invariants) : f = 0 := by
  let T : Module.End k (Fin 2 → k) := f.1.1
  have hcomm : ∀ g : G, Commute (rho g) T :=
    fun g ↦ commute_of_mem_traceZeroAdjoint_invariants rho f g
  obtain ⟨μ, hμ⟩ :=
    Slop.OddRep.exists_smul_eq_of_isAbsolutelyIrreducible rho T hcomm
  have htrace : LinearMap.trace k (Fin 2 → k) T = 0 :=
    LinearMap.mem_ker.mp f.1.2
  have hμtwo : μ * (2 : k) = 0 := by
    rw [hμ, map_smul, LinearMap.trace_one, Module.finrank_pi] at htrace
    simpa using htrace
  have hμzero : μ = 0 := (mul_eq_zero.mp hμtwo).resolve_right (NeZero.ne (2 : k))
  have hT : T = 0 := by simpa [hμzero] using hμ
  apply Subtype.ext
  apply Subtype.ext
  exact hT

/-- The invariant subspace of the trace-zero adjoint is trivial.  This is the algebraic
form of the `H⁰` vanishing used in the global Euler-characteristic calculation. -/
theorem subsingleton_traceZeroAdjoint_invariants
    [NeZero (2 : k)] (rho : Representation k G (Fin 2 → k))
    [rho.IsAbsolutelyIrreducible.{u}] :
    Subsingleton (traceZeroAdjoint rho).invariants := by
  constructor
  intro f f'
  rw [eq_zero_of_mem_traceZeroAdjoint_invariants rho f,
    eq_zero_of_mem_traceZeroAdjoint_invariants rho f']

variable [TopologicalSpace k] [DiscreteTopology k]

/-- The invariant subspace is still trivial after bundling `ad⁰(ρ)` as a discrete
topological representation. -/
theorem subsingleton_traceZeroAdjointTopRep_invariants
    [NeZero (2 : k)] (rho : Representation k G (Fin 2 → k))
    [rho.IsAbsolutelyIrreducible.{u}] :
    Subsingleton (traceZeroAdjointTopRep rho).ρ.invariants := by
  constructor
  intro f f'
  let fAlg : (traceZeroAdjoint rho).invariants := ⟨f.1, f.2⟩
  let fAlg' : (traceZeroAdjoint rho).invariants := ⟨f'.1, f'.2⟩
  have hf := eq_zero_of_mem_traceZeroAdjoint_invariants rho fAlg
  have hf' := eq_zero_of_mem_traceZeroAdjoint_invariants rho fAlg'
  apply Subtype.ext
  exact (congrArg Subtype.val hf).trans (congrArg Subtype.val hf').symm

end Representation

namespace Representation

variable {k G : Type u} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- Zeroth continuous cohomology of `ad⁰(ρ)` vanishes. -/
theorem subsingleton_continuousCohomology_zero_traceZeroAdjoint
    [NeZero (2 : k)] (rho : Representation k G (Fin 2 → k))
    [rho.IsAbsolutelyIrreducible.{u}] :
    Subsingleton (continuousCohomology 0 (traceZeroAdjointTopRep rho)) := by
  let e := ContinuousCohomology.zeroIso (traceZeroAdjointTopRep rho)
  letI : Subsingleton (traceZeroAdjointTopRep rho).ρ.invariants :=
    subsingleton_traceZeroAdjointTopRep_invariants rho
  constructor
  intro x y
  have hxy : e.hom x = e.hom y := Subsingleton.elim _ _
  calc
    x = e.inv (e.hom x) := by simp
    _ = e.inv (e.hom y) := congrArg e.inv hxy
    _ = y := by simp

end Representation

namespace Deformation

variable {k G : Type u} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The continuous cohomology of the trace-zero adjoint representation. -/
noncomputable abbrev BockleAdjointCohomology
    (n : ℕ) (rho : Representation k G (Fin 2 → k)) : TopModuleCat k :=
  continuousCohomology n (Representation.traceZeroAdjointTopRep rho)

/-- The tangent space controlling a fixed-determinant rank-two deformation problem. -/
noncomputable abbrev BockleTangentSpace
    (rho : Representation k G (Fin 2 → k)) : TopModuleCat k :=
  BockleAdjointCohomology 1 rho

/-- The obstruction space controlling a fixed-determinant rank-two deformation problem. -/
noncomputable abbrev BockleObstructionSpace
    (rho : Representation k G (Fin 2 → k)) : TopModuleCat k :=
  BockleAdjointCohomology 2 rho

end Deformation

namespace Deformation

variable {R D k G : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing D] [Algebra R D]
  [Field k] [TopologicalSpace k] [DiscreteTopology k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The field isomorphism used to regard adjoint cohomology as a vector space over the
residue field of the chosen power-series ring. -/
noncomputable def BockleObstructionScalarEquiv
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k) :
    BocklePowerSeriesResidueField R numVariables ≃+* k :=
  (bocklePowerSeriesResidueEquiv R numVariables).trans residueEquiv

/-- The obstruction group, with a type synonym recording its transported scalar field.
This avoids carrying an ad hoc abstract obstruction space in applications. -/
noncomputable def BockleObstructionModel
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k)) : Type u :=
  BockleObstructionSpace rho

noncomputable instance BockleObstructionModel.addCommGroup
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k)) :
    AddCommGroup (BockleObstructionModel R numVariables residueEquiv rho) :=
  inferInstanceAs (AddCommGroup (BockleObstructionSpace rho))

/-- The original residue-field action on the obstruction model. -/
noncomputable instance BockleObstructionModel.moduleOriginal
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k)) :
    Module k (BockleObstructionModel R numVariables residueEquiv rho) :=
  inferInstanceAs (Module k (BockleObstructionSpace rho))

noncomputable instance BockleObstructionModel.moduleFiniteOriginal
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k))
    [Module.Finite k (BockleObstructionSpace rho)] :
    Module.Finite k (BockleObstructionModel R numVariables residueEquiv rho) :=
  inferInstanceAs (Module.Finite k (BockleObstructionSpace rho))

noncomputable instance BockleObstructionModel.module
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k)) :
    Module (BocklePowerSeriesResidueField R numVariables)
      (BockleObstructionModel R numVariables residueEquiv rho) :=
  Module.compHom _ (BockleObstructionScalarEquiv R numVariables residueEquiv).toRingHom

/-- Finite-dimensionality is preserved when the obstruction group's scalar field is
transported across the residue-field equivalence. -/
noncomputable instance BockleObstructionModel.moduleFinite
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k))
    [Module.Finite k (BockleObstructionSpace rho)] :
    Module.Finite (BocklePowerSeriesResidueField R numVariables)
      (BockleObstructionModel R numVariables residueEquiv rho) := by
  let e := BockleObstructionScalarEquiv R numVariables residueEquiv
  let W := BockleObstructionModel R numVariables residueEquiv rho
  let b := Module.Free.chooseBasis k W
  letI : Finite (Module.Free.ChooseBasisIndex k W) :=
    Module.Finite.finite_basis b
  let b' : Module.Basis (Module.Free.ChooseBasisIndex k W)
      (BocklePowerSeriesResidueField R numVariables) W :=
    b.mapCoeffs e.symm fun c x ↦ by
      change e (e.symm c) • x = c • x
      rw [e.apply_symm_apply]
  exact Module.Finite.of_basis b'

/-- Transporting the obstruction group across the residue-field equivalence does not change
its dimension. -/
theorem BockleObstructionModel.finrank_eq
    (R : Type u) [CommRing R] [IsLocalRing R]
    (numVariables : ℕ) (residueEquiv : IsLocalRing.ResidueField R ≃+* k)
    (rho : Representation k G (Fin 2 → k))
    [Module.Finite k (BockleObstructionSpace rho)] :
    Module.finrank (BocklePowerSeriesResidueField R numVariables)
        (BockleObstructionModel R numVariables residueEquiv rho) =
      Module.finrank k (BockleObstructionSpace rho) := by
  let e := BockleObstructionScalarEquiv R numVariables residueEquiv
  let W := BockleObstructionModel R numVariables residueEquiv rho
  let b := Module.Free.chooseBasis k W
  letI : Finite (Module.Free.ChooseBasisIndex k W) :=
    Module.Finite.finite_basis b
  let b' : Module.Basis (Module.Free.ChooseBasisIndex k W)
      (BocklePowerSeriesResidueField R numVariables) W :=
    b.mapCoeffs e.symm fun c x ↦ by
      change e (e.symm c) • x = c • x
      rw [e.apply_symm_apply]
  change Module.finrank (BocklePowerSeriesResidueField R numVariables) W =
    Module.finrank k W
  rw [Module.finrank_eq_card_basis b', Module.finrank_eq_card_basis b]

/-- The precise tangent--obstruction data needed to turn cohomological deformation theory
into a balanced power-series presentation.  Keeping the power-series map, obstruction map,
the two dimension identifications, and the Euler-characteristic inequality as separate fields
makes each arithmetic ingredient independently replaceable by a theorem. -/
structure BockleCohomologicalPresentationInput
    (rho : Representation k G (Fin 2 → k)) where
  /-- The number of parameters chosen from the tangent space. -/
  numVariables : ℕ
  /-- The map from the resulting power-series ring to the universal deformation ring. -/
  powerSeriesMap : MvPowerSeries (Fin numVariables) R →ₐ[R] D
  /-- Tangent parameters topologically generate the universal ring. -/
  powerSeriesMap_surjective : Function.Surjective powerSeriesMap
  /-- A scalar-compatible realization of the obstruction group. -/
  obstructionSpace : Type u
  [obstructionAddCommGroup : AddCommGroup obstructionSpace]
  [obstructionModule :
    Module (BocklePowerSeriesResidueField R numVariables) obstructionSpace]
  [obstructionFinite :
    Module.Finite (BocklePowerSeriesResidueField R numVariables) obstructionSpace]
  /-- Böckle's map from minimal relations to deformation obstructions. -/
  obstructionMap :
    Ideal.RelationSpace (RingHom.ker powerSeriesMap.toRingHom) →ₗ[
      BocklePowerSeriesResidueField R numVariables] obstructionSpace
  /-- A relation with zero obstruction was not minimal. -/
  obstructionMap_injective : Function.Injective obstructionMap
  /-- The chosen variables form a basis of the tangent space. -/
  tangent_finrank_eq : Module.finrank k (BockleTangentSpace rho) = numVariables
  /-- The scalar-compatible obstruction model has the dimension of `H²(G, ad⁰(ρ))`. -/
  obstruction_finrank_eq :
    Module.finrank (BocklePowerSeriesResidueField R numVariables) obstructionSpace =
      Module.finrank k (BockleObstructionSpace rho)
  /-- The global/local Euler-characteristic calculation gives the balanced inequality. -/
  obstruction_finrank_le_tangent_finrank :
    Module.finrank k (BockleObstructionSpace rho) ≤
      Module.finrank k (BockleTangentSpace rho)

attribute [instance]
  BockleCohomologicalPresentationInput.obstructionAddCommGroup
  BockleCohomologicalPresentationInput.obstructionModule
  BockleCohomologicalPresentationInput.obstructionFinite

/-- The cohomological dimension identities reduce Böckle's numerical condition to the
Euler-characteristic inequality. -/
theorem BockleCohomologicalPresentationInput.obstruction_finrank_le_numVariables
    {rho : Representation k G (Fin 2 → k)}
    (P : BockleCohomologicalPresentationInput (R := R) (D := D) rho) :
    Module.finrank (BocklePowerSeriesResidueField R P.numVariables) P.obstructionSpace ≤
      P.numVariables := by
  rw [P.obstruction_finrank_eq, ← P.tangent_finrank_eq]
  exact P.obstruction_finrank_le_tangent_finrank

/-- Böckle's commutative-algebra theorem consumes the decomposed cohomological data and
produces the balanced presentation. -/
theorem BockleCohomologicalPresentationInput.exists_bocklePresentation
    {rho : Representation k G (Fin 2 → k)}
    (P : BockleCohomologicalPresentationInput (R := R) (D := D) rho) :
    Nonempty (BocklePresentation R D) := by
  exact exists_bocklePresentation_of_surjective_of_obstructionMap
    P.numVariables P.powerSeriesMap P.powerSeriesMap_surjective
      P.obstructionMap P.obstructionMap_injective
      P.obstruction_finrank_le_numVariables

end Deformation
