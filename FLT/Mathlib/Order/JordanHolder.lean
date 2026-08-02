/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.Order.JordanHolder

/-!
# Additional Jordan--Hölder lattice lemmas

Local lattice mechanics used to reorder adjacent factors of a composition series.
-/

@[expose] public section

/-- Suppose `u ⋖ v ⋖ w` are two adjacent covers in a modular lattice.  If `v'` is a
relative complement to `v` in the interval `[u, w]`, then `u ⋖ v' ⋖ w` is the series
with the two factors interchanged.  In the Schoof argument, the Ext-vanishing theorem supplies
exactly this relative complement. -/
theorem covBy_swap_of_inf_eq_sup_eq
    {X : Type*} [Lattice X] [IsModularLattice X] {u v v' w : X}
    (huv : u ⋖ v) (hvw : v ⋖ w) (hinf : v ⊓ v' = u) (hsup : v ⊔ v' = w) :
    u ⋖ v' ∧ v' ⋖ w := by
  have hv'w₀ : v' ⋖ v ⊔ v' := by
    apply CovBy.sup_of_inf_left
    rwa [hinf]
  have hv'w : v' ⋖ w := by simpa only [hsup] using hv'w₀
  have hvw₀ : v ⋖ v ⊔ v' := by simpa only [hsup] using hvw
  have huv'₀ : v ⊓ v' ⋖ v' :=
    inf_covBy_of_covBy_sup_of_covBy_sup_right hvw₀ hv'w₀
  have huv' : u ⋖ v' := by
    rwa [hinf] at huv'₀
  exact ⟨huv', hv'w⟩
