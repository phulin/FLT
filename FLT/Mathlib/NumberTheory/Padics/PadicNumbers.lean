/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# Complements on rational p-adic valuations

This file supplies the discrete-valuation-ring instance for the valuation subring of the standard
`p`-adic valuation on `ℚ`. The valuation is surjective onto `ℤᵐ⁰`, so its value group is the full
cyclic group of units of `ℤᵐ⁰` and is nontrivial.
-/

@[expose] public section

open MonoidWithZeroHom
open scoped WithZero

namespace Rat

instance {p : ℕ} [Fact p.Prime] :
    IsDiscreteValuationRing (padicValuation p).valuationSubring := by
  let v := padicValuation p
  have hvg : valueGroup (.ofClass v) = ⊤ := by
    ext x
    simp only [Subgroup.mem_top, iff_true]
    rw [mem_valueGroup_iff_of_comm]
    obtain ⟨y, hy⟩ := surjective_padicValuation p x
    exact ⟨1, by simp, y, by simpa [v] using hy.symm⟩
  let _ : IsCyclic (valueGroup (.ofClass v)) := hvg.symm ▸ inferInstance
  have hvnontriv : v.IsNontrivial := by
    refine ⟨p, ?_, ?_⟩
    · simp [v]
    · simp [v]
  let _ : v.IsNontrivial := hvnontriv
  let _ : Nontrivial (valueGroup (.ofClass v)) := inferInstance
  exact Valuation.valuationSubring_isDiscreteValuationRing v

end Rat
