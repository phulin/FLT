/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Jonas Bayer
-/
module

public import FLT.GlobalLanglandsConjectures.GLnDefs

/-!
# Proof of a case of the global Langlands conjectures.

Class Field Theory was one of the highlights of 19th century mathematics, linking
analysis to arithmetic of extensions of number fields with abelian Galois groups.
In the 1960s the main results had been re-interpreted as the GL(1) case of the global
Langlands conjectures. The general global Langlands conjectures are for GL(n) for any natural
number n, and work over any number field or global function field. Much is known in the function
field case (Lafforgue got a Fields Medal for his work on the topic), but the general number
field case remains largely open even today. For example we have very few results if the
base number field is not totally real or CM. For simplicity, let us stick to GL(n)/Q.

In 1993 Wiles announced his proof of the modularity of semistable elliptic curves over the
rationals. The result gave us a way of constructing automorphic forms from Galois representations;
refinements of the work by Taylor and others over the next decade led to a profound understanding
of the "holomorphic" or "odd" part of global Langlands functoriality for GL(2) over the rationals.
Wiles' work used class field theory (in the form of global Tate duality) crucially in a
central proof that a deformation ring R was isomorphic to a Hecke algebra T.

The fact that Wiles needed the theory for GL(1) to make progress in the GL(2) case,
is surely evidence that at the end of the day the proof for GL(n) is going to be by induction on n.
We will thus attempt to prove the global Langlands conjectures for GL(0).

## Structure of the proof

We will deduce the global Langlands conjectures for GL(0) from a far stronger theorem,
called the *classification theorem for automorphic representations for GL(0) over Q*.
This theorem gives a *canonical isomorphism* between the space of automorphic representations
and the complex numbers. Except in Lean we're not allowed to say "canonical" so instead
our "theorem" is a *definition* of a bijection.

## TODO

State them first.

-/

@[expose] public section

open scoped Manifold

namespace AutomorphicForm

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- A `GLₙ`-weight `ρ` is trivial if it is the one-dimensional trivial representation. -/
def GLn.Weight.IsTrivial {n : ℕ} (ρ : Weight n) : Prop :=
  ρ.w.d = 1 ∧ ∀ g, ρ.w.rho g = 1

open GLn

namespace GL0

variable (ρ : Weight 0)

set_option backward.isDefEq.respectTransparency.types false in
/-- Make an automorphic form for GL₀/ℚ from a complex number -/
def ofComplex (c : ℂ) : AutomorphicFormForGLnOverQ 0 ρ := {
    toFun := fun _ => c,
    is_smooth := {
      continuous := by continuity
      loc_cst := by
        intro _
        rw [IsLocallyConstant]
        intro s
        by_cases hc : c ∈ s
        · simp [hc]
        · simp [hc]
      smooth := by simp [contMDiff_const]
    }
    is_periodic := by simp
    is_slowly_increasing x := ⟨‖c‖, 0, by simp⟩
    -- is_finite_cod := by
    --   intros x
    --   sorry
    has_finite_level := by
      let U : Subgroup (GL (Fin 0) (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)) := {
        carrier := {1},
        one_mem' := by simp,
        mul_mem' := by simp
        inv_mem' := by simp
      }
      apply Exists.intro U
      exact {
          is_open := by
            change IsOpen ({1} : Set (GL (Fin 0)
              (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))
            convert (isOpen_univ : IsOpen (Set.univ : Set (GL (Fin 0)
              (IsDedekindDomain.FiniteAdeleRing ℤ ℚ)))) using 1
            ext g
            simp only [Set.mem_singleton_iff, Set.mem_univ, iff_true]
            exact Subsingleton.eq_one g
          is_compact := by aesop
          finite_level := by simp
      }
  }

-- the weakest form of the classification theorem
/-- The classification of automorphic forms for `GL₀/ℚ`: they are in bijection with `ℂ`. -/
noncomputable def classification : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ := {
  toFun := fun f ↦ f 1
  invFun := fun c ↦ ofComplex ρ c
  left_inv := by
    rw [Function.LeftInverse]
    simp only [ofComplex]
    intro x
    have h: x.toFun = fun _ => x.toFun 1 := by
      exact funext fun g ↦ congrArg x.toFun <| Subsingleton.eq_one g
    ext m
    rw [h]
  right_inv := by
    rw [Function.RightInverse, Function.LeftInverse]
    simp [ofComplex]
}

end GL0

namespace GLn

-- Let's write down an inverse
-- For general n, it will only work for ρ the trivial representation, but we didn't
-- define the trivial representation yet.
-- Some of the other fields will work for all n.
set_option backward.isDefEq.respectTransparency false in
/-- Make an automorphic form for `GLₙ/ℚ` of trivial weight `ρ` from a complex number `z`,
returning the constant function with value `z`. -/
def ofComplex (z : ℂ) {n : ℕ} (ρ : Weight n) (hρ : ρ.IsTrivial) :
    AutomorphicFormForGLnOverQ n ρ where
      toFun _ := z
      is_smooth := {
        continuous := by continuity
        loc_cst := by
          intro _
          rw [IsLocallyConstant]
          intro s
          by_cases hz : z ∈ s
          · simp [hz]
          · simp [hz]
        smooth := fun _ ↦ contMDiff_const
      }
      is_periodic := by simp
      is_slowly_increasing _ := ⟨‖z‖, 0, by simp⟩
      -- is_finite_cod := sorry -- needs a better name
      has_finite_level := sorry -- needs a better name

-- no idea why it's not computable
/-- The classification of automorphic forms for `GL₀/ℚ` of weight `ρ`: they are in
bijection with `ℂ`. -/
noncomputable def classification (ρ : Weight 0) : AutomorphicFormForGLnOverQ 0 ρ ≃ ℂ where
  toFun := GL0.classification ρ
  invFun := (GL0.classification ρ).symm
  left_inv := (GL0.classification ρ).left_inv
  right_inv := (GL0.classification ρ).right_inv

-- Can this be beefed up to an isomorphism of complex
-- vector spaces?

end GLn

end AutomorphicForm
