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

/-- Sort the factors of a composition series into a lower block satisfying `P` and an
upper block satisfying `Q`.

This is the abstract devissage used in Schoof's finite-flat argument.  The hypotheses say
that `P` and `Q` contain identity intervals and are closed under concatenation, every simple
interval has one of the two types, and a final `P`-factor can be moved below an arbitrary
`Q`-block.  The proof removes the last factor and inserts it on the appropriate side of the
cut. -/
theorem CompositionSeries.exists_cut_of_covBy_or
    {X : Type*} [Lattice X] [IsModularLattice X]
    (P Q : X → X → Prop)
    (hP_refl : ∀ x, P x x) (hQ_refl : ∀ x, Q x x)
    (hP_trans : ∀ {x y z}, P x y → P y z → P x z)
    (hQ_trans : ∀ {x y z}, Q x y → Q y z → Q x z)
    (hfactor : ∀ {x y}, x ⋖ y → P x y ∨ Q x y)
    (hswap : ∀ {x y z}, Q x y → y ⋖ z → P y z →
      ∃ y', P x y' ∧ Q y' z)
    (s : CompositionSeries X) :
    ∃ y, P s.head y ∧ Q y s.last := by
  induction hlen : s.length using Nat.strong_induction_on generalizing s with
  | h n ih =>
      by_cases hn : n = 0
      · have hs : s.head = s.last := by
          have hslen : s.length = 0 := hlen.trans hn
          simpa [RelSeries.head, RelSeries.last, hslen]
        exact ⟨s.head, hP_refl _, hs ▸ hQ_refl _⟩
      · have hpos : 0 < s.length := by omega
        have herase : s.eraseLast.length < n := by
          simp only [RelSeries.eraseLast_length, hlen]
          omega
        obtain ⟨y, hPy, hQy⟩ :=
          ih s.eraseLast.length herase s.eraseLast rfl
        have hhead : s.eraseLast.head = s.head := by
          rw [RelSeries.head_eraseLast]
        rw [hhead] at hPy
        have hlast := CompositionSeries.isMaximal_eraseLast_last hpos
        rcases hfactor hlast with hPtop | hQtop
        · obtain ⟨y', hPyy', hQy'⟩ := hswap hQy hlast hPtop
          exact ⟨y', hP_trans hPy hPyy', hQy'⟩
        · exact ⟨y, hPy, hQ_trans hQy hQtop⟩
