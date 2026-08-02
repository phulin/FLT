/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.EllipticCurve.Torsion
public import FLT.GaloisRepresentation.Cyclotomic
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

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

/-! ### The Weil pairing over a separably closed extension -/

/-- The data and the three structural properties of the Weil pairing on `E(L)[n]`.

The base field `K` is retained separately from the separably closed field `L`.  This is
essential for the equivariance field: an automorphism of `L/K` fixes the coefficients of
`E`, hence acts on the points of the base-changed curve `E / L`. -/
structure WeierstrassCurve.WeilPairingData
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : WeierstrassCurve K) [E.IsElliptic]
    [IsSepClosed L] [DecidableEq K] [DecidableEq L]
    (n : ℕ) [NeZero (n : L)] where
  pairing :
    (E⁄L).nTorsion n →+
    (E⁄L).nTorsion n →+
    Additive (rootsOfUnity n L)
  alternating : ∀ P, pairing P P = 0
  left_nondegenerate : ∀ P, (∀ Q, pairing P Q = 0) → P = 0
  right_nondegenerate : ∀ Q, (∀ P, pairing P Q = 0) → Q = 0
  equivariant : ∀ (σ : L ≃ₐ[K] L) P Q,
    pairing (E.nTorsionMap (K := L) (L := L) n σ.toAlgHom P)
        (E.nTorsionMap (K := L) (L := L) n σ.toAlgHom Q) =
      Additive.ofMul
        (σ.toRingEquiv.toMulEquiv.restrictRootsOfUnity n (Additive.toMul (pairing P Q)))

/-- The Weil pairing, including alternation, perfection, and Galois equivariance.

The eventual construction is by the usual divisor/function definition.  Keeping all
properties in one package prevents later arithmetic arguments from silently choosing
incompatible pairings over different presentations of the same extension. -/
noncomputable def WeierstrassCurve.weilPairingData
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (E : WeierstrassCurve K) [E.IsElliptic]
    [IsSepClosed L] [DecidableEq K] [DecidableEq L]
    (n : ℕ) [NeZero (n : L)] : WeierstrassCurve.WeilPairingData (L := L) E n :=
  sorry

/-- The Weil pairing on the `n`-torsion of `E` over a separably closed extension `L`. -/
noncomputable def WeierstrassCurve.weilPairing
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (L : Type v) [Field L] [Algebra K L] [IsSepClosed L]
    [DecidableEq K] [DecidableEq L] (n : ℕ) [NeZero (n : L)] :
    (E⁄L).nTorsion n →+ (E⁄L).nTorsion n →+ Additive (rootsOfUnity n L) :=
  (E.weilPairingData n : WeierstrassCurve.WeilPairingData (L := L) E n).pairing

/-- An arbitrary additive coordinate system on the `n`-th roots of unity in a separably
closed field. -/
noncomputable def rootsOfUnity.addEquivZMod
    (L : Type v) [Field L] (n : ℕ) [NeZero (n : L)] [IsSepClosed L] :
    Additive (rootsOfUnity n L) ≃+ ZMod n := by
  letI : NeZero n := .of_neZero_natCast L
  letI : IsAddCyclic (Additive (rootsOfUnity n L)) :=
    isAddCyclic_additive_iff.mpr inferInstance
  apply addEquivOfAddCyclicCardEq
  change Nat.card (rootsOfUnity n L) = Nat.card (ZMod n)
  rw [HasEnoughRootsOfUnity.natCard_rootsOfUnity L n, Nat.card_zmod]

/-- The Weil pairing written as a `ZMod n`-valued bilinear form after choosing additive
coordinates on the group of `n`-th roots of unity. -/
noncomputable def WeierstrassCurve.weilPairingForm
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (L : Type v) [Field L] [Algebra K L] [IsSepClosed L]
    [DecidableEq K] [DecidableEq L] (n : ℕ) [NeZero (n : L)]
    (e : Additive (rootsOfUnity n L) ≃+ ZMod n) :
    LinearMap.BilinForm (ZMod n) ((E⁄L).nTorsion n) :=
  (E.weilPairing L n).toZModBilinForm e.toAddMonoidHom

@[simp]
theorem WeierstrassCurve.weilPairingForm_apply
    {K : Type u} [Field K] (E : WeierstrassCurve K) [E.IsElliptic]
    (L : Type v) [Field L] [Algebra K L] [IsSepClosed L]
    [DecidableEq K] [DecidableEq L] (n : ℕ) [NeZero (n : L)]
    (e : Additive (rootsOfUnity n L) ≃+ ZMod n)
    (P Q : (E⁄L).nTorsion n) :
    E.weilPairingForm L n e P Q = e (E.weilPairing L n P Q) := by
  rfl

namespace WeierstrassCurve.WeilPairingData

/-- The canonical `ZMod n`-valued form attached to a Weil-pairing package. -/
noncomputable def form
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {E : WeierstrassCurve K} [E.IsElliptic]
    [IsSepClosed L] [DecidableEq K] [DecidableEq L]
    {n : ℕ} [NeZero (n : L)]
    (D : WeierstrassCurve.WeilPairingData (L := L) E n) :
    LinearMap.BilinForm (ZMod n) ((E⁄L).nTorsion n) :=
  D.pairing.toZModBilinForm (rootsOfUnity.addEquivZMod L n).toAddMonoidHom

/-- Alternation of the Weil pairing in additive root-of-unity coordinates. -/
theorem form_isAlt
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {E : WeierstrassCurve K} [E.IsElliptic]
    [IsSepClosed L] [DecidableEq K] [DecidableEq L]
    {n : ℕ} [NeZero (n : L)]
    (D : WeierstrassCurve.WeilPairingData (L := L) E n) : D.form.IsAlt :=
  D.pairing.toZModBilinForm_isAlt _ D.alternating

/-- Perfection of the Weil pairing in additive root-of-unity coordinates. -/
theorem form_nondegenerate
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    {E : WeierstrassCurve K} [E.IsElliptic]
    [IsSepClosed L] [DecidableEq K] [DecidableEq L]
    {n : ℕ} [NeZero (n : L)]
    (D : WeierstrassCurve.WeilPairingData (L := L) E n) : D.form.Nondegenerate :=
  D.pairing.toZModBilinForm_nondegenerate _
    (rootsOfUnity.addEquivZMod L n).injective
    D.left_nondegenerate D.right_nondegenerate

/-- Galois equivariance of the Weil pairing becomes the cyclotomic similitude identity
after choosing additive coordinates on the roots of unity. -/
theorem form_galois_similitude
    {K : Type u} [Field K] [CharZero K]
    {E : WeierstrassCurve K} [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
    {p : ℕ} [Fact p.Prime] [NeZero (p : K)]
    (D : WeierstrassCurve.WeilPairingData
      (L := AlgebraicClosure K) E p)
    (g : Field.absoluteGaloisGroup K)
    (P Q : (E⁄(AlgebraicClosure K)).nTorsion p) :
    D.form (E.galoisRep p (Fact.out : p.Prime).pos g P)
        (E.galoisRep p (Fact.out : p.Prime).pos g Q) =
      PadicInt.toZMod ((cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val) *
        D.form P Q := by
  let e := rootsOfUnity.addEquivZMod (AlgebraicClosure K) p
  change e (D.pairing (E.nTorsionMap p g.toAlgHom P)
    (E.nTorsionMap p g.toAlgHom Q)) = _
  rw [D.equivariant]
  exact rootsOfUnity.addEquiv_restrictRootsOfUnity_cyclotomic e g.toRingEquiv
    (D.pairing P Q)

/-- The determinant of the Galois action on prime torsion is the mod-`p` cyclotomic
character.  This is the Weil-pairing argument of Silverman, III.8.3. -/
theorem galoisRep_det_eq_cyclotomic
    {K : Type u} [Field K] [CharZero K]
    {E : WeierstrassCurve K} [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
    {p : ℕ} [Fact p.Prime] [NeZero (p : K)]
    (D : WeierstrassCurve.WeilPairingData
      (L := AlgebraicClosure K) E p) :
    ∀ g, (E.galoisRep p (Fact.out : p.Prime).pos).det g =
      PadicInt.toZMod ((cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val) := by
  letI : (E⁄(AlgebraicClosure K)).IsElliptic :=
    inferInstanceAs (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
  have hRank : Module.rank (ZMod p) ((E⁄(AlgebraicClosure K)).nTorsion p) = 2 := by
    apply (E⁄(AlgebraicClosure K)).n_torsion_rank (Fact.out : p.Prime)
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  exact GaloisRep.det_eq_of_nondegenerate_alternating_pairing
    (E.galoisRep p (Fact.out : p.Prime).pos) hRank D.form D.form_isAlt
    D.form_nondegenerate
    (fun g ↦ PadicInt.toZMod
      ((cyclotomicCharacter (AlgebraicClosure K) p g.toRingEquiv).val))
    D.form_galois_similitude

end WeierstrassCurve.WeilPairingData
