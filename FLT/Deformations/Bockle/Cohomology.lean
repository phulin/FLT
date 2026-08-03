/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.Adjoint
public import FLT.Deformations.RepresentationTheory.Carayol
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
