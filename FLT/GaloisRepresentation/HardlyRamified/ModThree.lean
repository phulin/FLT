/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.Assumptions.KnownIn1980s
public import FLT.GaloisRepresentation.HardlyRamified.Defs
public import FLT.Deformations.RepresentationTheory.TraceReducibility

/-!
# Mod-3 hardly ramified representations

A mod-3 hardly ramified representation is shown to be an extension of
the trivial character by the mod-3 cyclotomic character.
-/

@[expose] public section

namespace GaloisRepresentation.IsHardlyRamified

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

/-- Arithmetic core of the mod-3 classification: Fontaine's ramification bound and the global
classification of the resulting finite extension produce a nonzero Galois-fixed covector.

The passage from this statement to a quotient by the trivial character is elementary linear
algebra and is kept out of this input theorem. -/
theorem mod_three_exists_nonzero_invariant_covector
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ π : V →ₗ[k] k, π ≠ 0 ∧ ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  knownin1980s

/-- A mod 3 hardly ramified representation is an extension of trivial by cyclo -/
-- Probably `Field k` can be replaced with `(3 : k) = 0`
theorem mod_three {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k] --
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∃ (π : V →ₗ[k] k) (_ : Function.Surjective π),
    ∀ g : Γ ℚ, ∀ v : V, π (ρ g v) = π v := by
  obtain ⟨π, hπ, hπρ⟩ := mod_three_exists_nonzero_invariant_covector V hV hρ
  exact ⟨π, π.surjective hπ, hπρ⟩

/-- In particular, a hardly ramified mod-3 representation is reducible. -/
theorem mod_three_not_isIrreducible {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ¬ ρ.IsIrreducible := by
  obtain ⟨π, hπ, hπρ⟩ := mod_three V hV hρ
  exact ρ.not_isIrreducible_of_surjective_invariant_quotient hV π hπ hπρ

/-- The mod-3 classification also gives the character identity `trace = 1 + det`. -/
theorem mod_three_trace_eq_one_add_det
    {k : Type u} [Finite k] [Field k] [Algebra ℤ_[3] k]
    [TopologicalSpace k] [DiscreteTopology k]
    (V : Type*) [AddCommGroup V] [Module k V] [Module.Finite k V] [Module.Free k V]
    (hV : Module.rank k V = 2) {ρ : GaloisRep ℚ k V}
    (hρ : IsHardlyRamified (show Odd 3 by decide) hV ρ) :
    ∀ g : Γ ℚ, LinearMap.trace k V (ρ g) = 1 + LinearMap.det (ρ g) := by
  obtain ⟨π, hπ, hπρ⟩ := mod_three V hV hρ
  exact ρ.trace_eq_one_add_det_of_surjective_invariant_quotient hV π hπ hπρ

end GaloisRepresentation.IsHardlyRamified
