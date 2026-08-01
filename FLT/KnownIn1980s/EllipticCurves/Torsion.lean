/-
Copyright (c) 2026 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import FLT.EllipticCurve.Torsion

/-!

# Torsion of an elliptic curve over a separably closed field

Let `E` be an elliptic curve over a separably closed field `k` and let `n` be a natural
number which is nonzero in `k`. Then the `n`-torsion subgroup of `E(k)` is free of rank 2
over `ℤ/nℤ`.

-/

@[expose] public section

open scoped WeierstrassCurve.Affine -- `(E⁄k).Point` notation

-- let k be a separably closed field (`DecidableEq` is needed for the group law on `(E⁄k).Point`)
variable (k : Type*) [Field k] [IsSepClosed k] [DecidableEq k]

-- Let E/k be an elliptic curve
variable (E : WeierstrassCurve k) [E.IsElliptic]

-- Let n be a natural which is nonzero in k
variable (n : ℕ) [NeZero (n : k)]

-- then the n-torsion of E(k) is free rank 2 over ℤ/nℤ
theorem WeierstrassCurve.torsion_rank_two :
    Nonempty (AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) ≃+ (ZMod n) × (ZMod n)) :=
  by
    haveI : (E.baseChange k).IsElliptic := by
      change (E.map (algebraMap k k)).IsElliptic
      infer_instance
    let e₀ :
        Submodule.torsionBy ℤ (E⁄k).toAffine.Point (n : ℤ) ≃+
          AddSubgroup.torsionBy (E⁄k).Point (n : ℤ) := {
      toFun P := ⟨P, P.2⟩
      invFun P := ⟨P, P.2⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl }
    obtain ⟨e⟩ := (E.baseChange k).n_torsion_dimension (NeZero.ne (n : k))
    exact ⟨e₀.symm.trans e⟩
