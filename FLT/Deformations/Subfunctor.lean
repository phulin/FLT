/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-!
# Subfunctors

Basic constructions for subfunctors of functors valued in `Type`, including
the subfunctor cut out by a subset of the value at a terminal object.
-/

@[expose] public section

universe w v u

open Opposite CategoryTheory

namespace CategoryTheory
namespace Subfunctor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- The subfunctor defined by pulling back a subset of the terminal component. -/
def ofIsTerminal {X : C} (hX : Limits.IsTerminal X) (s : Set (F.obj X)) :
    Subfunctor F where
  obj U := F.map (hX.from U) ⁻¹' s
  map {U V} i := by
    simp only [← Set.preimage_comp, ← hX.comp_from i, F.map_comp]
    rfl

variable {F : C ⥤ Type w} {F' : C ⥤ Type w}

/-- The pointwise image of a subfunctor under a natural transformation. -/
def imageUnder (G : Subfunctor F) (η : F ⟶ F') : Subfunctor F' where
  obj U := η.app U '' G.obj U
  map {U V} i := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨F.map i x, G.map i hx, ?_⟩
    exact η.naturality_apply i x

lemma mem_imageUnder_iff (G : Subfunctor F) (η : F ⟶ F') {U : C} {y : F'.obj U} :
    y ∈ (G.imageUnder η).obj U ↔
      ∃ x, x ∈ G.obj U ∧ η.app U x = y :=
  Iff.rfl

end Subfunctor
end CategoryTheory
