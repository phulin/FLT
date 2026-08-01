/-
Copyright (c) 2024 Javier López-Contreras. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Javier López-Contreras, Kevin Buzzard
-/
module

public import Mathlib.RepresentationTheory.Irreducible
public import FLT.Mathlib.RepresentationTheory.Basic
public import FLT.Slop.RepresentationTheory.OddAbsIrredSlop

/-!
# Absolutely irreducible representations

The class `Representation.IsAbsolutelyIrreducible ρ`, expressing that the
base change of `ρ` to the algebraic closure of the base field remains
irreducible.
-/

@[expose] public section

universe u

namespace Representation

variable {G : Type*} [Group G]

variable {k : Type*} [Field k]

variable {W : Type*} [AddCommGroup W] [Module k W]

/-- `IsAbsolutelyIrreducible ρ` states that a given Representation `ρ` over a field `k`
is absolutely irreducible, meaning that all the possible base change extensions are irreducible. -/
class IsAbsolutelyIrreducible (ρ : Representation k G W) : Prop where
  absolutelyIrreducible :
    ∀ k' : Type u, ∀ _ : Field k', ∀ _ : Algebra k k', IsIrreducible (k' ⊗ᵣ' ρ)

/-- An irreducible finite-dimensional representation is absolutely irreducible if one group
element has a one-dimensional fixed space. -/
theorem IsAbsolutelyIrreducible.of_finrank_eigenspace_eq_one
    (ρ : Representation k G W) [FiniteDimensional k W] (hρ : ρ.IsIrreducible)
    {g : G} (hg : Module.finrank k (Module.End.eigenspace (ρ g) 1) = 1) :
    ρ.IsAbsolutelyIrreducible where
  absolutelyIrreducible k' _ _ := by
    change (Slop.OddRep.baseChange k' ρ).IsIrreducible
    exact Slop.OddRep.isIrreducible_baseChange_of_finrank_eigenspace_eq_one ρ k' hρ hg

end Representation
