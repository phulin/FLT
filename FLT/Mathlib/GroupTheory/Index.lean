/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Kevin Buzzard
-/
module

public meta import Mathlib.Tactic.ToDual
public import Mathlib.GroupTheory.Index

import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.ScopedNS
import Mathlib.Tactic.SetLike

/-!
# TODO

* Rename `relindex` to `relIndex`
* Rename `FiniteIndex.finiteIndex` to `FiniteIndex.index_ne_zero`
-/

@[expose] public section

open Function
open scoped Pointwise

-- This is cool notation. Should mathlib have it? And what should the `relindex` version be?
/-- Notation `[G : H]` for the (additive) index of a subgroup `H ≤ G`. -/
scoped[GroupTheory] notation "[" G ":" H "]" => @AddSubgroup.index G _ H

theorem Subgroup.index_op {G : Type*} [Group G] (H : Subgroup G) :
    H.op.index = H.index := by
  trans (H.comap (MulEquiv.inv' G).symm.toMonoidHom).index
  · congr 1
    ext; simp
  · exact Subgroup.index_comap_of_surjective _ (MulEquiv.inv' G).symm.surjective

instance {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    H.op.FiniteIndex := ⟨by rw [Subgroup.index_op]; exact Subgroup.FiniteIndex.index_ne_zero⟩

/-- If the restriction of a group homomorphism to a finite-index subgroup has finite image,
then the original homomorphism has finite image. -/
theorem MonoidHom.finite_range_of_finiteIndex_restrict
    {G K : Type*} [Group G] [Group K] (ρ : G →* K) (H : Subgroup G)
    [H.FiniteIndex] (hfinite : Finite (ρ.comp H.subtype).range) : Finite ρ.range := by
  letI : Finite (ρ.comp H.subtype).range := hfinite
  haveI hrest : (ρ.comp H.subtype).ker.FiniteIndex := inferInstance
  have hker : (ρ.comp H.subtype).ker = ρ.ker.subgroupOf H := by
    ext x
    rfl
  haveI hsub : (ρ.ker.subgroupOf H).FiniteIndex := hker ▸ hrest
  have hrel : ρ.ker.IsFiniteRelIndex H :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex).mpr hsub
  let L := ρ.ker ⊓ H
  have hLrel : L.relIndex H ≠ 0 := by
    change (ρ.ker ⊓ H).relIndex H ≠ 0
    rw [Subgroup.inf_relIndex_right]
    exact Subgroup.relIndex_ne_zero
  haveI hL : L.FiniteIndex := by
    constructor
    rw [← Subgroup.relIndex_mul_index (show L ≤ H from inf_le_right)]
    exact mul_ne_zero hLrel Subgroup.FiniteIndex.index_ne_zero
  haveI : ρ.ker.FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := L) (K := ρ.ker) inf_le_left
  rw [← (QuotientGroup.quotientKerEquivRange ρ).finite_iff]
  infer_instance
