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

/-- A two-dimensional involution with determinant `-1` has a one-dimensional fixed space
when the field does not have characteristic two. -/
theorem finrank_eigenspace_one_of_sq_eq_one_of_det_eq_neg_one
    [FiniteDimensional k W] (hW : Module.finrank k W = 2)
    (f : Module.End k W) (hneg : (-1 : k) ≠ 1)
    (hsq : f.comp f = LinearMap.id) (hdet : LinearMap.det f = -1) :
    Module.finrank k (Module.End.eigenspace f 1) = 1 := by
  have hf_one : f ≠ LinearMap.id := by
    intro hf
    rw [hf, LinearMap.det_id] at hdet
    exact hneg hdet.symm
  have hf_neg_one : f ≠ -LinearMap.id := by
    intro hf
    have hfdet : LinearMap.det f = 1 := by
      rw [hf, show -LinearMap.id = (-1 : k) • LinearMap.id by ext; simp,
        LinearMap.det_smul, hW, LinearMap.det_id]
      ring
    rw [hdet] at hfdet
    exact hneg hfdet
  have hf_add_ne : f + (LinearMap.id : Module.End k W) ≠ 0 := by
    intro h
    apply hf_neg_one
    apply LinearMap.ext
    intro x
    have hx := LinearMap.congr_fun h x
    simpa using eq_neg_of_add_eq_zero_left hx
  obtain ⟨v, hv⟩ : ∃ v : W, (f + (LinearMap.id : Module.End k W)) v ≠ 0 := by
    by_contra h
    push Not at h
    apply hf_add_ne
    ext x
    exact h x
  let w : W := (f + (LinearMap.id : Module.End k W)) v
  have hw : w ≠ 0 := hv
  have hfw : f w = w := by
    have hsqv := LinearMap.congr_fun hsq v
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at hsqv
    change f (f v + v) = f v + v
    rw [map_add, hsqv]
    exact add_comm _ _
  have hw_mem : w ∈ Module.End.eigenspace f 1 := by
    rw [Module.End.mem_eigenspace_iff]
    simpa using hfw
  have hpos : 0 < Module.finrank k (Module.End.eigenspace f 1) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨w, hw_mem⟩, by simpa using hw⟩
  have hproper : Module.End.eigenspace f 1 ≠ ⊤ := by
    intro htop
    apply hf_one
    ext x
    have hx : x ∈ Module.End.eigenspace f 1 := by rw [htop]; trivial
    simpa using (Module.End.mem_eigenspace_iff.mp hx)
  have hlt : Module.finrank k (Module.End.eigenspace f 1) < 2 := by
    rw [← hW]
    exact Submodule.finrank_lt hproper
  omega

end Representation
