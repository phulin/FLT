/-
Copyright (c) 2024 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Topology.Instances.ZMod
public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!

See
https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/n-torsion.20or.20multiplication.20by.20n.20as.20an.20additive.20group.20hom/near/429096078

The main theorems in this file are part of the PhD thesis work of David Angdinata, one of KB's
PhD students. It would be great if anyone who is interested in working on these results
could talk to David first. Note that he has already made substantial progress.

-/

@[expose] public section

universe u

variable {k : Type u} [Field k] (E : WeierstrassCurve k) [E.IsElliptic] [DecidableEq k]

open WeierstrassCurve WeierstrassCurve.Affine

/-- The `n`-torsion subgroup of an elliptic curve `E` over `k`: the kernel of multiplication
by `n` on the group of `k`-points of `E`. -/
abbrev WeierstrassCurve.nTorsion (n : ℕ) : Type u :=
  Submodule.torsionBy ℤ E.toAffine.Point n

--variable (n : ℕ) in
--#synth AddCommGroup (E.nTorsion n)

-- not sure if this instance will cause more trouble than it's worth
noncomputable instance (n : ℕ) : Module (ZMod n) (E.nTorsion n) :=
  AddCommGroup.zmodModule <| by
  intro ⟨P, hP⟩
  simpa using hP

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
theorem WeierstrassCurve.n_torsion_finite {n : ℕ} (hn : 0 < n) : Finite (E.nTorsion n) := sorry

-- This theorem needs e.g. a theory of division polynomials. It's ongoing work of David Angdinata.
-- Please do not work on it without talking to KB and David first.
-- This theorem was well-known in the early part of the 20th century.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

/-- A group killed by a prime `p` and having cardinality `p ^ r` is the standard
`r`-dimensional vector space over `ZMod p`. -/
theorem group_theory_lemma_of_prime {A : Type*} [AddCommGroup A] {p r : ℕ}
    (hp : p.Prime)
    (hcard : Nat.card (Submodule.torsionBy ℤ A p) = p ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A p) ≃+ (Fin r → ZMod p)) := by
  letI : Fact p.Prime := ⟨hp⟩
  letI moduleInst : Module (ZMod p) (Submodule.torsionBy ℤ A p) :=
    AddCommGroup.zmodModule <| by
      intro ⟨x, hx⟩
      simpa using hx
  letI finiteInst : Finite (Submodule.torsionBy ℤ A p) :=
    Nat.finite_of_card_ne_zero <| by rw [hcard]; exact pow_ne_zero _ hp.ne_zero
  letI finiteModule : Module.Finite (ZMod p) (Submodule.torsionBy ℤ A p) :=
    Module.Finite.of_finite
  have hfinrank : Module.finrank (ZMod p) (Submodule.torsionBy ℤ A p) = r := by
    have hpow := @Module.natCard_eq_pow_finrank
      (ZMod p) (Submodule.torsionBy ℤ A p) inferInstance inferInstance moduleInst finiteModule
    rw [Nat.card_zmod, hcard] at hpow
    exact Nat.pow_right_injective hp.two_le hpow.symm
  let freeModule : Module.Free (ZMod p) (Submodule.torsionBy ℤ A p) :=
    Module.Free.of_divisionRing (ZMod p) (Submodule.torsionBy ℤ A p)
  let b := @Module.finBasisOfFinrankEq (ZMod p) (Submodule.torsionBy ℤ A p)
    inferInstance inferInstance moduleInst freeModule inferInstance finiteModule r hfinrank
  exact ⟨b.equivFun.toAddEquiv⟩

/-- Multiplication by `d` sends `(d * e)`-torsion to `e`-torsion. This is the
map occurring in the elementary exact sequences used to classify finite torsion groups. -/
noncomputable def torsionNsmulHom {A : Type*} [AddCommGroup A] (d e : ℕ) :
    Submodule.torsionBy ℤ A (d * e) →+
      Submodule.torsionBy ℤ A e where
  toFun x := ⟨(d : ℤ) • (x : A), by
    rw [Submodule.mem_torsionBy_iff, smul_smul]
    simpa [mul_comm] using x.prop⟩
  map_zero' := by simp
  map_add' x y := by simp [smul_add]

/-- The kernel of multiplication by `d` from `(d * e)`-torsion to `e`-torsion
is canonically the `d`-torsion. -/
noncomputable def torsionNsmulHomKerEquiv {A : Type*} [AddCommGroup A] (d e : ℕ) :
    Submodule.torsionBy ℤ A d ≃+
      (torsionNsmulHom (A := A) d e).ker where
  toFun x := ⟨⟨x, by
    rw [Submodule.mem_torsionBy_iff]
    rw [← Nat.cast_mul, Nat.cast_smul_eq_nsmul]
    have hx : d • (x : A) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact x.prop
    calc
      (d * e) • (x : A) = e • (d • (x : A)) := mul_nsmul (x : A) d e
      _ = 0 := by rw [hx, nsmul_zero]⟩, by
        ext
        exact x.prop⟩
  invFun x := ⟨x, congrArg (fun z : Submodule.torsionBy ℤ A e ↦ (z : A)) x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- If the `d`-, `e`-, and `(d * e)`-torsion groups have the cardinalities of
rank-`r` free modules, multiplication by `d` maps the `(d * e)`-torsion onto
the `e`-torsion. -/
lemma torsionNsmulHom_surjective_of_card {A : Type*} [AddCommGroup A] {d e r : ℕ}
    (hd : 0 < d) (he : 0 < e)
    (hcard_d : Nat.card (Submodule.torsionBy ℤ A d) = d ^ r)
    (hcard_e : Nat.card (Submodule.torsionBy ℤ A e) = e ^ r)
    (hcard_de : Nat.card (Submodule.torsionBy ℤ A (d * e)) = (d * e) ^ r) :
    Function.Surjective (torsionNsmulHom (A := A) d e) := by
  let f := torsionNsmulHom (A := A) d e
  have hde : 0 < d * e := Nat.mul_pos hd he
  letI : Finite (Submodule.torsionBy ℤ A (d * e)) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcard_de]
      exact pow_ne_zero _ hde.ne'
  letI : Finite (Submodule.torsionBy ℤ A e) :=
    Nat.finite_of_card_ne_zero <| by
      rw [hcard_e]
      exact pow_ne_zero _ he.ne'
  have hker : Nat.card f.ker = d ^ r := by
    rw [← Nat.card_congr (torsionNsmulHomKerEquiv d e).toEquiv]
    exact hcard_d
  have hrange : Nat.card f.range = e ^ r := by
    have hprod := f.ker.card_mul_index
    have hcard_domain : Nat.card (Submodule.torsionBy ℤ A ((d : ℤ) * (e : ℤ))) =
        (d * e) ^ r := by
      simpa only [Nat.cast_mul] using hcard_de
    rw [AddSubgroup.index_ker f, hker, hcard_domain, mul_pow] at hprod
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hd r) hprod
  rw [← f.range_eq_top, ← AddSubgroup.card_eq_iff_eq_top]
  rw [hrange]
  exact hcard_e.symm

/-- Torsion in a finite product of additive groups is computed coordinatewise. -/
noncomputable def torsionByPiAddEquiv {ι : Type*} [Fintype ι]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)] (d : ℕ) :
    Submodule.torsionBy ℤ (∀ i, B i) d ≃+
      (∀ i, Submodule.torsionBy ℤ (B i) d) where
  toFun x i := ⟨x.1 i, congrFun x.prop i⟩
  invFun x := ⟨fun i ↦ x i, funext fun i ↦ (x i).prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The `d`-torsion in the cyclic group `ZMod m` has cardinality `gcd m d`. -/
lemma natCard_torsionBy_zmod (m d : ℕ) (hm : m ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (ZMod m) d) = m.gcd d := by
  letI : NeZero m := ⟨hm⟩
  let f : ZMod m →+ ZMod m := nsmulAddMonoidHom d
  let e : Submodule.torsionBy ℤ (ZMod m) d ≃+ f.ker := {
    toFun x := ⟨x, by
      change d • (x : ZMod m) = 0
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact x.prop⟩
    invFun x := ⟨x, by
      rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
      exact x.prop⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl }
  rw [Nat.card_congr e.toEquiv]
  simpa only [f, Nat.card_zmod] using
    IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod m) d

/-- The `d`-torsion cardinality of a finite product of cyclic groups is the
product of the corresponding gcds. -/
lemma natCard_torsionBy_pi_zmod {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (hm : ∀ i, m i ≠ 0) (d : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (m i)) d) = ∏ i, (m i).gcd d := by
  rw [Nat.card_congr (torsionByPiAddEquiv (fun i ↦ ZMod (m i)) d).toEquiv, Nat.card_pi]
  congr 1
  funext i
  exact natCard_torsionBy_zmod (m i) d (hm i)

/-- An additive equivalence restricts to an equivalence on `d`-torsion. -/
noncomputable def AddEquiv.torsionBy {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (d : ℕ) :
    Submodule.torsionBy ℤ A d ≃+ Submodule.torsionBy ℤ B d where
  toFun x := ⟨e x, by
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    have hx : d • (x : A) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact x.prop
    simpa only [map_nsmul, map_zero] using congrArg e hx⟩
  invFun x := ⟨e.symm x, by
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    have hx : d • (x : B) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact x.prop
    simpa only [map_nsmul, map_zero] using congrArg e.symm hx⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_add' _ _ := Subtype.ext (map_add e _ _)

/-- If `d ∣ n`, taking `d`-torsion inside `A[n]` recovers `A[d]`. -/
noncomputable def torsionByTorsionAddEquiv {A : Type*} [AddCommGroup A]
    {d n : ℕ} (hdn : d ∣ n) :
    Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d ≃+
      Submodule.torsionBy ℤ A d where
  toFun x := ⟨x.1.1, congrArg (fun z : Submodule.torsionBy ℤ A n ↦ (z : A)) x.prop⟩
  invFun x := ⟨⟨x, by
    rcases hdn with ⟨c, rfl⟩
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    have hx : d • (x : A) = 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℤ]
      exact x.prop
    calc
      (d * c) • (x : A) = c • (d • (x : A)) := mul_nsmul (x : A) d c
      _ = 0 := by rw [hx, nsmul_zero]⟩, by
        apply Subtype.ext
        exact x.prop⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Zero exponents contribute only trivial `ZMod 1` factors to a product of
cyclic prime-power groups, so they can be discarded. -/
noncomputable def piZModPowNeZeroAddEquiv {ι : Type*} [Fintype ι]
    (p e : ι → ℕ) :
    (∀ i, ZMod (p i ^ e i)) ≃+
      (∀ i : {i // e i ≠ 0}, ZMod (p i ^ e i)) where
  toFun x i := x i
  invFun x i := if hi : e i = 0 then 0 else x ⟨i, hi⟩
  left_inv x := by
    ext i
    change (if hi : e i = 0 then 0 else x i) = x i
    split_ifs with hi
    · exact (ZMod.subsingleton_iff.2 <| by rw [hi, pow_zero]).elim _ _
    · rfl
  right_inv x := by
    ext i
    change (if hi : e i = 0 then 0 else x ⟨i, hi⟩) = x i
    rw [dif_neg i.prop]
  map_add' x y := by
    ext i
    rfl

/-- Every cyclic factor of a product equivalent to `A[n]` has modulus dividing
`n`, since every element of `A[n]` is killed by `n`. -/
lemma cyclic_factor_dvd_of_torsion_equiv {A : Type*} [AddCommGroup A]
    {n : ℕ} {ι : Type*} [Fintype ι] (m : ι → ℕ)
    (E : Submodule.torsionBy ℤ A n ≃+ (∀ i, ZMod (m i))) (i : ι) :
    m i ∣ n := by
  let x : Submodule.torsionBy ℤ A n := E.symm (fun _ ↦ 1)
  have hx : n • x = 0 := by
    apply Subtype.ext
    rw [← Nat.cast_smul_eq_nsmul ℤ]
    exact x.prop
  have hy := congrArg (fun y ↦ y i) (congrArg E hx)
  have : (n : ZMod (m i)) = 0 := by
    simpa [x] using hy
  exact (ZMod.natCast_eq_zero_iff n (m i)).mp this

/-- Structure-theorem data for `A[n]`, together with the numerical constraints
on its cyclic prime-power factors supplied by all the smaller torsion cardinalities. -/
theorem group_theory_structure_data {A : Type*} [AddCommGroup A] {n : ℕ}
    (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ) (_ : ∀ i, (p i).Prime) (e : ι → ℕ)
      (_he : ∀ i, e i ≠ 0)
      (_E : Submodule.torsionBy ℤ A n ≃+ (∀ i, ZMod (p i ^ e i))),
      ∀ d : ℕ, d ∣ n → ∏ i, (p i ^ e i).gcd d = d ^ r := by
  letI : Finite (Submodule.torsionBy ℤ A n) :=
    Nat.finite_of_card_ne_zero <| by
      rw [h n dvd_rfl]
      exact pow_ne_zero _ hn.ne'
  obtain ⟨ι, hι, p, hp, e, ⟨E₀⟩⟩ :=
    AddCommGroup.equiv_directSum_zmod_of_finite (Submodule.torsionBy ℤ A n)
  let ι' := {i : ι // e i ≠ 0}
  let p' : ι' → ℕ := fun i ↦ p i
  let e' : ι' → ℕ := fun i ↦ e i
  let E : Submodule.torsionBy ℤ A n ≃+ (∀ i : ι', ZMod (p' i ^ e' i)) :=
    (E₀.trans (DirectSum.addEquivProd fun i ↦ ZMod (p i ^ e i))).trans
      (piZModPowNeZeroAddEquiv p e)
  refine ⟨ι', inferInstance, p', fun i ↦ hp i, e', fun i ↦ i.prop, E, ?_⟩
  intro d hd
  have hm : ∀ i, p' i ^ e' i ≠ 0 := fun i ↦ pow_ne_zero _ (hp i).ne_zero
  calc
    ∏ i, (p' i ^ e' i).gcd d =
        Nat.card (Submodule.torsionBy ℤ (∀ i, ZMod (p' i ^ e' i)) d) :=
      (natCard_torsionBy_pi_zmod (fun i ↦ p' i ^ e' i) hm d).symm
    _ = Nat.card (Submodule.torsionBy ℤ (Submodule.torsionBy ℤ A n) d) :=
      (Nat.card_congr (E.torsionBy d).toEquiv).symm
    _ = Nat.card (Submodule.torsionBy ℤ A d) :=
      Nat.card_congr (torsionByTorsionAddEquiv hd).toEquiv
    _ = d ^ r := h d hd

-- This theorem was well-known in the early part of the 20th century.
theorem group_theory_lemma {A : Type*} [AddCommGroup A] {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : ∀ d : ℕ, d ∣ n → Nat.card (Submodule.torsionBy ℤ A d) = d ^ r) :
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := sorry

-- I only need this if n is prime but there's no harm thinking about it in general I guess.
-- It follows from the previous theorem using pure group theory (possibly including the
-- structure theorem for finite abelian groups)
theorem WeierstrassCurve.n_torsion_dimension [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nonempty (E.nTorsion n ≃+ (ZMod n) × (ZMod n)) := by
  obtain ⟨φ⟩ : Nonempty (E.nTorsion n ≃+ (Fin 2 → (ZMod n))) := by
    apply group_theory_lemma (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn)
    intro d hd
    apply E.n_torsion_card
    contrapose! hn
    rcases hd with ⟨c, rfl⟩
    simp [hn]
  exact ⟨φ.trans (RingEquiv.piFinTwo _).toAddEquiv⟩

/-- If `n` is nonzero in a separably closed field, the `n`-torsion has rank two over
`ZMod n`. -/
theorem WeierstrassCurve.n_torsion_rank [IsSepClosed k] {n : ℕ} (hnp : n.Prime)
    (hn : (n : k) ≠ 0) :
    Module.rank (ZMod n) (E.nTorsion n) = 2 := by
  letI : Fact n.Prime := ⟨hnp⟩
  obtain ⟨e⟩ := group_theory_lemma_of_prime hnp (E.n_torsion_card hn)
  let e' : E.nTorsion n ≃ₗ[ZMod n] (Fin 2 → ZMod n) :=
    LinearEquiv.ofBijective (e.toAddMonoidHom.toZModLinearMap n) e.bijective
  let e'' : E.nTorsion n ≃ₗ[ZMod n] ULift.{u} (Fin 2 → ZMod n) :=
    e'.trans ULift.moduleEquiv.symm
  rw [e''.rank_eq, rank_ulift, rank_fun']
  norm_num

/-- Positive torsion is finite as a module over `ZMod n`. -/
theorem WeierstrassCurve.n_torsion_module_finite {n : ℕ} (hn : 0 < n) :
    Module.Finite (ZMod n) (E.nTorsion n) := by
  letI : Finite (E.nTorsion n) := E.n_torsion_finite hn
  exact Module.Finite.of_finite

noncomputable instance (n : ℕ) [NeZero n] : Module.Finite (ZMod n) (E.nTorsion n) :=
  E.n_torsion_module_finite (Nat.pos_of_ne_zero (NeZero.ne n))

-- This should be a straightforward but perhaps long unravelling of the definition
/-- The map on points for an elliptic curve over `k` induced by a morphism of `k`-algebras
is a group homomorphism. -/
noncomputable def WeierstrassCurve.Points.map {K L : Type u} [Field K] [Field L] [Algebra k K]
    [Algebra k L] [DecidableEq K] [DecidableEq L]
    (f : K →ₐ[k] L) : (E⁄K).Point →+ (E⁄L).Point := WeierstrassCurve.Affine.Point.map f

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_id (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    WeierstrassCurve.Points.map E (AlgHom.id k K) = AddMonoidHom.id _ := by
      ext
      exact WeierstrassCurve.Affine.Point.map_id _

omit [E.IsElliptic] [DecidableEq k] in
lemma WeierstrassCurve.Points.map_comp (K L M : Type u) [Field K] [Field L] [Field M]
    [DecidableEq K] [DecidableEq L] [DecidableEq M] [Algebra k K] [Algebra k L] [Algebra k M]
    (f : K →ₐ[k] L) (g : L →ₐ[k] M) :
    (WeierstrassCurve.Affine.Point.map g).comp (WeierstrassCurve.Affine.Point.map f) =
    WeierstrassCurve.Affine.Point.map (W' := E) (g.comp f) := by
  ext P
  exact WeierstrassCurve.Affine.Point.map_map _ _ _

omit [E.IsElliptic] [DecidableEq k] in
/-- For the Krull topology, the set of automorphisms sending one elliptic-curve point to
another is open. -/
lemma WeierstrassCurve.Points.isOpen_setOf_map_eq
    (K : Type u) [Field K] [Algebra k K] [Algebra.IsIntegral k K]
    [DecidableEq K] (P Q : (E⁄K).Point) :
    IsOpen {g : K ≃ₐ[k] K | WeierstrassCurve.Points.map E (g : K →ₐ[k] K) P = Q} := by
  letI : ContinuousSMulDiscrete (K ≃ₐ[k] K) K :=
    continuousSMulDiscrete_iff_isOpen_stabilizer.mpr fun x ↦
      stabilizer_isOpen_of_isIntegral x
  cases P with
  | zero =>
      cases Q with
      | zero =>
          convert (isOpen_univ : IsOpen (Set.univ : Set (K ≃ₐ[k] K))) using 1
          ext g
          simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
          rfl
      | some x' y' hQ =>
          convert (isOpen_empty : IsOpen (∅ : Set (K ≃ₐ[k] K))) using 1
          ext g
          rw [Set.mem_empty_iff_false, iff_false]
          intro h
          change WeierstrassCurve.Affine.Point.zero =
            WeierstrassCurve.Affine.Point.some x' y' hQ at h
          cases h
  | some x y hP =>
      cases Q with
      | zero =>
          convert (isOpen_empty : IsOpen (∅ : Set (K ≃ₐ[k] K))) using 1
          ext g
          rw [Set.mem_empty_iff_false, iff_false]
          intro h
          change WeierstrassCurve.Affine.Point.some (g x) (g y) _ =
            WeierstrassCurve.Affine.Point.zero at h
          cases h
      | some x' y' hQ =>
          convert (ContinuousSMulDiscrete.isOpen_smul_eq (K ≃ₐ[k] K) x x').inter
            (ContinuousSMulDiscrete.isOpen_smul_eq (K ≃ₐ[k] K) y y') using 1
          ext g
          simp only [WeierstrassCurve.Points.map, WeierstrassCurve.Affine.Point.map_some,
            Set.mem_ofPred_eq, Set.mem_inter_iff, WeierstrassCurve.Affine.Point.some.injEq,
            AlgEquiv.smul_def]
          rfl

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentationSmul
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    SMul (K ≃ₐ[k] K) (E⁄K).Point := ⟨
  fun g P ↦ WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K) P⟩

/-- The Galois action on the points of an elliptic curve. -/
noncomputable instance WeierstrassCurve.galoisRepresentation
    (K : Type u) [Field K] [DecidableEq K] [Algebra k K] :
    DistribMulAction (K ≃ₐ[k] K) (E⁄K).Point where
      one_smul P := WeierstrassCurve.Affine.Point.map_id P
      mul_smul g h P := (WeierstrassCurve.Affine.Point.map_map
        (f := (h : K →ₐ[k] K)) (g := (g : K →ₐ[k] K)) P).symm
      smul_zero g := WeierstrassCurve.Affine.Point.map_zero (g : K →ₐ[k] K)
      smul_add g P Q := map_add (WeierstrassCurve.Affine.Point.map (g : K →ₐ[k] K)) P Q

/-- A classical decidable instance on `AlgebraicClosure ℚ`, given that there is
no hope of a constructive one with the current definition of algebraic closure. -/
noncomputable instance : DecidableEq (AlgebraicClosure ℚ) := Classical.typeDecidableEq _

/-- The continuous Galois representation associated to an elliptic curve over a field. -/
noncomputable def WeierstrassCurve.galoisRep {K : Type u} [Field K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) (hn : 0 < n) :
    GaloisRep K (ZMod n) ((E.map (algebraMap K (AlgebraicClosure K))).nTorsion n) := by
  let T := (E⁄(AlgebraicClosure K)).nTorsion n
  change GaloisRep K (ZMod n) T
  let act (g : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) : T →+ T :=
    let g' : AlgebraicClosure K →ₐ[K] AlgebraicClosure K := g
    {
      toFun := fun P ↦ ⟨WeierstrassCurve.Points.map E g' P.1, by
        rw [Submodule.mem_torsionBy_iff]
        rw [← map_zsmul]
        have hP : (n : ℤ) • P.1 = 0 :=
          (Submodule.mem_torsionBy_iff (R := ℤ) (a := (n : ℤ)) P.1).mp P.2
        rw [hP, map_zero]⟩
      map_zero' := Subtype.ext (map_zero (WeierstrassCurve.Points.map E g'))
      map_add' := fun P Q ↦
        Subtype.ext (map_add (WeierstrassCurve.Points.map E g') P.1 Q.1)
    }
  let ρ : Field.absoluteGaloisGroup K →* Module.End (ZMod n) T := {
    toFun := fun g ↦ (act g).toZModLinearMap n
    map_one' := by
      ext P
      change WeierstrassCurve.Points.map E (AlgHom.id K (AlgebraicClosure K)) P.1 = P.1
      exact DFunLike.congr_fun
        (WeierstrassCurve.Points.map_id E (AlgebraicClosure K)) P.1
    map_mul' := fun g h ↦ by
      ext P
      change WeierstrassCurve.Points.map E ((g * h : Field.absoluteGaloisGroup K) :
        AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P.1 =
        WeierstrassCurve.Points.map E (g : AlgebraicClosure K →ₐ[K] AlgebraicClosure K)
          (WeierstrassCurve.Points.map E
            (h : AlgebraicClosure K →ₐ[K] AlgebraicClosure K) P.1)
      exact DFunLike.congr_fun
        (WeierstrassCurve.Points.map_comp E (AlgebraicClosure K) (AlgebraicClosure K)
          (AlgebraicClosure K) (h : _ →ₐ[K] _) (g : _ →ₐ[K] _)).symm P.1
  }
  letI : TopologicalSpace (Module.End (ZMod n) T) :=
    moduleTopology (ZMod n) (Module.End (ZMod n) T)
  refine ContinuousMonoidHom.mk ρ ?_
  haveI : DiscreteTopology (Module.End (ZMod n) T) := by
    constructor
    apply le_antisymm
    · letI : TopologicalSpace (Module.End (ZMod n) T) := ⊥
      letI : DiscreteTopology (Module.End (ZMod n) T) := discreteTopology_bot _
      letI : ContinuousAdd (Module.End (ZMod n) T) :=
        ⟨continuous_of_discreteTopology⟩
      letI : ContinuousSMul (ZMod n) (Module.End (ZMod n) T) :=
        ⟨continuous_of_discreteTopology⟩
      exact moduleTopology_le (ZMod n) (Module.End (ZMod n) T)
    · exact bot_le
  rw [continuous_discrete_rng]
  intro f
  letI : (E⁄(AlgebraicClosure K)).IsElliptic := by
    change (E.map (algebraMap K (AlgebraicClosure K))).IsElliptic
    infer_instance
  haveI : Finite T := (E⁄(AlgebraicClosure K)).n_torsion_finite hn
  suffices IsOpen (⋂ P : T, {g | ρ g P = f P}) by
    convert this using 1
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    exact LinearMap.ext_iff
  apply isOpen_iInter_of_finite
  intro P
  convert WeierstrassCurve.Points.isOpen_setOf_map_eq E (AlgebraicClosure K)
    P.1 (f P).1 using 1
  ext g
  simp only [Set.mem_ofPred_eq]
  change (act g P = f P) ↔ _
  rw [Subtype.ext_iff]
  rfl
