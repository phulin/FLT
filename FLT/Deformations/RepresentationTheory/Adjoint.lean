/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Subrepresentation

/-!
# Adjoint representations

This file defines the adjoint action on endomorphisms and its trace-zero subrepresentation.
For a fixed-determinant deformation problem, this is the coefficient representation customarily
denoted `ad⁰(ρ̄)` in the tangent and obstruction groups.
-/

@[expose] public section

universe u v w

namespace Representation

variable {k : Type u} {G : Type v} {V : Type w}
  [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- The adjoint representation of `ρ`, acting on endomorphisms by conjugation. -/
abbrev adjoint (ρ : Representation k G V) : Representation k G (Module.End k V) :=
  ρ.linHom ρ

/-- The trace-zero endomorphisms form a subrepresentation of the adjoint representation. -/
noncomputable def traceZeroAdjointSubrepresentation (ρ : Representation k G V) :
    Subrepresentation ρ.adjoint where
  toSubmodule := LinearMap.ker (LinearMap.trace k V)
  apply_mem_toSubmodule g f hf := by
    rw [LinearMap.mem_ker] at hf ⊢
    change LinearMap.trace k V (ρ g * f * ρ g⁻¹) = 0
    rw [LinearMap.trace_mul_cycle]
    simpa [← map_mul, hf]

/-- The trace-zero adjoint representation `ad⁰(ρ)`. -/
noncomputable def traceZeroAdjoint (ρ : Representation k G V) :
    Representation k G (traceZeroAdjointSubrepresentation ρ).toSubmodule :=
  (traceZeroAdjointSubrepresentation ρ).toRepresentation

@[simp]
lemma traceZeroAdjoint_apply_val (ρ : Representation k G V) (g : G)
    (f : (traceZeroAdjointSubrepresentation ρ).toSubmodule) :
    (traceZeroAdjoint ρ g f : Module.End k V) = ρ g ∘ₗ (f : Module.End k V) ∘ₗ ρ g⁻¹ :=
  rfl

/-- For a rank-two representation over a field, the trace-zero adjoint representation has
dimension three. -/
theorem finrank_traceZeroAdjoint_fin_two
    {k : Type u} {G : Type v} [Field k] [Group G]
    (ρ : Representation k G (Fin 2 → k)) :
    Module.finrank k (traceZeroAdjointSubrepresentation ρ).toSubmodule = 3 := by
  have htrace : Function.Surjective (LinearMap.trace k (Fin 2 → k)) := by
    intro x
    obtain ⟨A, hA⟩ := Matrix.trace_surjective (n := Fin 2) x
    exact ⟨A.toLin', by simpa using hA⟩
  have hrank :=
    (LinearMap.trace k (Fin 2 → k)).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr htrace, finrank_top, Module.finrank_self,
    Module.finrank_linearMap, Module.finrank_pi] at hrank
  change Module.finrank k (LinearMap.ker (LinearMap.trace k (Fin 2 → k))) = 3
  norm_num at hrank ⊢
  omega

/-- Over a discrete coefficient ring, `ad⁰(ρ)` is naturally a topological representation
with the discrete topology.  This is the object used by continuous group cohomology for residual
representations. -/
noncomputable def traceZeroAdjointTopRep
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V) : TopRep k G := by
  let A := (traceZeroAdjointSubrepresentation ρ).toSubmodule
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : ContinuousSMul k A := ⟨continuous_of_discreteTopology⟩
  exact TopRep.of (Representation.toContRepresentationOfDiscrete (traceZeroAdjoint ρ))

/-- The carrier chosen by `traceZeroAdjointTopRep` is the trace-zero submodule.  This named
equality prevents downstream proofs from depending on reducibility of the `TopRep` constructor. -/
abbrev traceZeroAdjointTopRep_V
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V) :
    (traceZeroAdjointTopRep ρ).V = (traceZeroAdjointSubrepresentation ρ).toSubmodule := by
  unfold traceZeroAdjointTopRep
  rfl

/-- Forget the topological packaging of the trace-zero adjoint carrier. -/
noncomputable def traceZeroAdjointTopRepLinearEquiv
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V) :
    traceZeroAdjointTopRep ρ ≃ₗ[k] (traceZeroAdjointSubrepresentation ρ).toSubmodule :=
  match traceZeroAdjointTopRep_V ρ with
  | rfl => LinearEquiv.refl k _

/-- A topologically packaged trace-zero adjoint vector, viewed as an endomorphism. -/
noncomputable def traceZeroAdjointTopRepToEnd
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V) :
    traceZeroAdjointTopRep ρ →ₗ[k] Module.End k V :=
  (traceZeroAdjointSubrepresentation ρ).toSubmodule.subtype.comp
    (traceZeroAdjointTopRepLinearEquiv ρ).toLinearMap

@[simp]
lemma traceZeroAdjointTopRepToEnd_apply
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V)
    (x : traceZeroAdjointTopRep ρ) :
    traceZeroAdjointTopRepToEnd ρ x = (traceZeroAdjointTopRepLinearEquiv ρ x : Module.End k V) :=
  rfl

/-- The carrier equivalence intertwines the packaged and algebraic adjoint actions. -/
lemma traceZeroAdjointTopRepLinearEquiv_action
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V)
    (g : G) (x : traceZeroAdjointTopRep ρ) :
    traceZeroAdjointTopRepLinearEquiv ρ ((traceZeroAdjointTopRep ρ).ρ g x) =
      traceZeroAdjoint ρ g (traceZeroAdjointTopRepLinearEquiv ρ x) := by
  unfold traceZeroAdjointTopRepLinearEquiv traceZeroAdjointTopRep_V
  unfold traceZeroAdjointTopRep
  rfl

/-- In endomorphism coordinates, the packaged adjoint action is conjugation. -/
lemma traceZeroAdjointTopRepToEnd_action
    [TopologicalSpace k] [DiscreteTopology k] (ρ : Representation k G V)
    (g : G) (x : traceZeroAdjointTopRep ρ) :
    traceZeroAdjointTopRepToEnd ρ ((traceZeroAdjointTopRep ρ).ρ g x) =
      ρ g * traceZeroAdjointTopRepToEnd ρ x * ρ g⁻¹ := by
  rw [traceZeroAdjointTopRepToEnd_apply, traceZeroAdjointTopRepLinearEquiv_action,
    traceZeroAdjoint_apply_val]
  rfl

end Representation
