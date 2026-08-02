/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.EllipticCurve.Torsion
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!

# The Weil pairing

Let `E` be an elliptic curve over a separably closed field `k` and let `n` be a natural
number which is nonzero in `k`. This file states the existence of the Weil pairing, a
bilinear pairing on the `n`-torsion of `E(k)` with values in the `n`-th roots of unity
of `k`.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation for the group of `k`-points

/-! ### From additive pairings to `ZMod`-bilinear forms -/

universe u v w

/-- An additive pairing on a `ZMod n`-module, followed by an additive coordinate map
to `ZMod n`, is automatically a `ZMod n`-bilinear form. -/
noncomputable def AddMonoidHom.toZModBilinForm {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (ZMod n) M]
    {A : Type v} [AddCommGroup A]
    (b : M →+ M →+ A) (e : A →+ ZMod n) :
    LinearMap.BilinForm (ZMod n) M := by
  let outer : M →+ (M →ₗ[ZMod n] ZMod n) :=
    { toFun := fun x ↦ (e.comp (b x)).toZModLinearMap n
      map_zero' := by
        ext y
        simp
      map_add' := by
        intro x y
        ext z
        simp }
  exact outer.toZModLinearMap n

@[simp]
theorem AddMonoidHom.toZModBilinForm_apply {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (ZMod n) M]
    {A : Type v} [AddCommGroup A]
    (b : M →+ M →+ A) (e : A →+ ZMod n) (x y : M) :
    b.toZModBilinForm e x y = e (b x y) := rfl

/-- Alternation is preserved when an additive pairing is written in `ZMod` coordinates. -/
theorem AddMonoidHom.toZModBilinForm_isAlt {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (ZMod n) M]
    {A : Type v} [AddCommGroup A]
    (b : M →+ M →+ A) (e : A →+ ZMod n) (h : ∀ x, b x x = 0) :
    (b.toZModBilinForm e).IsAlt := by
  intro x
  simp [h]

/-- A perfect additive pairing remains nondegenerate after an injective change of
coordinates on its target. -/
theorem AddMonoidHom.toZModBilinForm_nondegenerate {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (ZMod n) M]
    {A : Type v} [AddCommGroup A]
    (b : M →+ M →+ A) (e : A →+ ZMod n) (he : Function.Injective e)
    (hl : ∀ x, (∀ y, b x y = 0) → x = 0)
    (hr : ∀ y, (∀ x, b x y = 0) → y = 0) :
    (b.toZModBilinForm e).Nondegenerate := by
  constructor
  · intro x hx
    apply hl x
    intro y
    apply he
    simpa using hx y
  · intro y hy
    apply hr y
    intro x
    apply he
    simpa using hy x

/-- Equivariance of an additive pairing and scalar equivariance of its target
coordinates combine to give the usual similitude identity. -/
theorem AddMonoidHom.toZModBilinForm_similitude {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (ZMod n) M]
    {A : Type v} [AddCommGroup A] {G : Type w}
    (b : M →+ M →+ A) (e : A →+ ZMod n)
    (actM : G → M → M) (actA : G → A → A) (c : G → ZMod n)
    (hb : ∀ g x y, b (actM g x) (actM g y) = actA g (b x y))
    (he : ∀ g z, e (actA g z) = c g * e z) :
    ∀ g x y,
      b.toZModBilinForm e (actM g x) (actM g y) = c g * b.toZModBilinForm e x y := by
  intro g x y
  simp only [AddMonoidHom.toZModBilinForm_apply, hb, he]

-- let k be a separably closed field (`DecidableEq` is needed for the group law on `(E⁄k).Point`)
variable (k : Type*) [Field k] [IsSepClosed k] [DecidableEq k]

-- Let E/k be an elliptic curve
variable (E : WeierstrassCurve k) [E.IsElliptic]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : k)]

/-- The Weil pairing on the `n`-torsion of an elliptic curve `E` over a separably closed
field `k`, a bilinear pairing with values in the `n`-th roots of unity of `k`. -/
def WeierstrassCurve.weilPairing :
    AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
    AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) →+
    Additive (rootsOfUnity n k) :=
  sorry

/-- The Weil pairing written as a `ZMod n`-valued bilinear form after choosing additive
coordinates on the group of `n`-th roots of unity. -/
noncomputable def WeierstrassCurve.weilPairingForm
    (e : Additive (rootsOfUnity n k) ≃+ ZMod n) :
    LinearMap.BilinForm (ZMod n) (E.nTorsion n) :=
  AddMonoidHom.toZModBilinForm
    (show E.nTorsion n →+ E.nTorsion n →+ Additive (rootsOfUnity n k) from
      E.weilPairing k n)
    e.toAddMonoidHom

@[simp]
theorem WeierstrassCurve.weilPairingForm_apply
    (e : Additive (rootsOfUnity n k) ≃+ ZMod n)
    (P Q : E.nTorsion n) :
    WeierstrassCurve.weilPairingForm (E := E) k n e P Q = e (E.weilPairing k n P Q) := by
  rfl
