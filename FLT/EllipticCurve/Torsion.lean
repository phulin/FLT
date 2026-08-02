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
-- This theorem was well-known in the early part of the 20th century.
theorem WeierstrassCurve.n_torsion_card [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Nat.card (E.nTorsion n) = n^2 := sorry

/-- If `n` is nonzero in a separably closed field, the `n`-torsion is finite.  This is an
immediate consequence of its cardinality; spelling it out avoids a separate, stronger
finiteness input in positive characteristic. -/
theorem WeierstrassCurve.n_torsion_finite [IsSepClosed k] {n : ℕ} (hn : (n : k) ≠ 0) :
    Finite (E.nTorsion n) := by
  apply Nat.finite_of_card_ne_zero
  rw [E.n_torsion_card hn]
  apply pow_ne_zero
  intro hn0
  subst n
  exact hn (by simp)

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

/-- The gcd of a positive power of one prime with another prime detects
whether the two primes agree. -/
lemma gcd_prime_pow_prime {p q e : ℕ} (hp : p.Prime) (hq : q.Prime)
    (he : e ≠ 0) :
    (p ^ e).gcd q = if p = q then q else 1 := by
  split_ifs with hpq
  · subst q
    exact Nat.gcd_eq_right (dvd_pow_self p he)
  · exact Nat.Coprime.gcd_eq_one
      (by simpa using Nat.coprime_pow_primes e 1 hp hq hpq)

/-- The gcd of two prime powers is the first power when their primes agree
and its exponent is smaller, and is one otherwise. -/
lemma gcd_prime_pow_prime_pow {p q e f : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hle : p = q → e ≤ f) :
    (p ^ e).gcd (q ^ f) = if p = q then p ^ e else 1 := by
  split_ifs with hpq
  · exact Nat.gcd_eq_left (by simpa [hpq] using Nat.pow_dvd_pow q (hle hpq))
  · exact Nat.Coprime.gcd_eq_one (Nat.coprime_pow_primes e f hp hq hpq)

/-- If the product of the `q`-torsion cardinalities of prime-power cyclic
factors is `q ^ r`, exactly `r` factors are `q`-primary. -/
lemma card_prime_fiber_of_gcd_product {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    {q r : ℕ} (hq : q.Prime) (hprod : ∏ i, (p i ^ e i).gcd q = q ^ r) :
    Fintype.card {i // p i = q} = r := by
  classical
  have hc : Fintype.card {i // p i = q} =
      (Finset.univ.filter fun i ↦ p i = q).card :=
    Fintype.card_ofFinset (p := {i | p i = q}) _ (by intro x; simp)
  have heval : (∏ i, (p i ^ e i).gcd q) =
      q ^ Fintype.card {i // p i = q} := by
    simp_rw [gcd_prime_pow_prime (hp _) hq (he _)]
    calc
      (∏ i, if p i = q then q else 1) =
          ∏ i ∈ Finset.univ.filter (fun i ↦ p i = q), q := by
        rw [Finset.prod_filter]
      _ = q ^ (Finset.univ.filter fun i ↦ p i = q).card := Finset.prod_const _
      _ = q ^ Fintype.card {i // p i = q} := congrArg (q ^ ·) hc.symm
  exact Nat.pow_right_injective hq.two_le (heval.symm.trans hprod)

/-- Once each prime-power cyclic factor divides `n`, the torsion cardinalities
force its exponent to be the full exponent of that prime in `n`. -/
lemma prime_power_exponent_eq_factorization {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    {n r : ℕ} (hn : 0 < n) (hdiv : ∀ i, p i ^ e i ∣ n)
    (hgcd : ∀ d, d ∣ n → ∏ i, (p i ^ e i).gcd d = d ^ r) (i : ι) :
    e i = n.factorization (p i) := by
  classical
  let q := p i
  have hq : q.Prime := hp i
  have hqdiv : q ∣ n := (dvd_pow_self q (he i)).trans (hdiv i)
  have hcard : Fintype.card {j // p j = q} = r :=
    card_prime_fiber_of_gcd_product p hp e he hq (hgcd q hqdiv)
  let S := Finset.univ.filter fun j ↦ p j = q
  have hcardS : S.card = r := by
    have hc : Fintype.card {j // p j = q} = S.card :=
      Fintype.card_ofFinset (p := {j | p j = q}) S (by intro x; simp [S])
    exact hc.symm.trans hcard
  have hle : ∀ j, p j = q → e j ≤ n.factorization q := by
    intro j hj
    apply (hq.pow_dvd_iff_le_factorization hn.ne').mp
    simpa [hj] using hdiv j
  have hlevel : q ^ n.factorization q ∣ n :=
    (hq.pow_dvd_iff_le_factorization hn.ne').mpr le_rfl
  have heval : (∏ j, (p j ^ e j).gcd (q ^ n.factorization q)) =
      q ^ ∑ j ∈ S, e j := by
    simp_rw [gcd_prime_pow_prime_pow (hp _) hq (hle _)]
    calc
      (∏ j, if p j = q then p j ^ e j else 1) = ∏ j ∈ S, p j ^ e j := by
        exact (Finset.prod_filter (s := Finset.univ) (fun j ↦ p j = q)
          (fun j ↦ p j ^ e j)).symm
      _ = ∏ j ∈ S, q ^ e j := by
        apply Finset.prod_congr rfl
        intro j hj
        rw [Finset.mem_filter] at hj
        rw [hj.2]
      _ = q ^ ∑ j ∈ S, e j := Finset.prod_pow_eq_pow_sum _ _ _
  have hpow : q ^ (∑ j ∈ S, e j) = q ^ (n.factorization q * r) := by
    calc
      q ^ (∑ j ∈ S, e j) = ∏ j, (p j ^ e j).gcd (q ^ n.factorization q) :=
        heval.symm
      _ = (q ^ n.factorization q) ^ r := hgcd _ hlevel
      _ = q ^ (n.factorization q * r) := (pow_mul q _ _).symm
  have hsum : ∑ j ∈ S, e j = n.factorization q * r :=
    Nat.pow_right_injective hq.two_le hpow
  apply Nat.le_antisymm (hle i rfl)
  by_contra hnot
  have hiS : i ∈ S := by simp [S, q]
  have hlt : ∑ j ∈ S, e j < ∑ _j ∈ S, n.factorization q :=
    Finset.sum_lt_sum
      (fun j hj ↦ hle j (by simpa [S] using (Finset.mem_filter.mp hj).2))
      ⟨i, hiS, Nat.lt_of_not_ge hnot⟩
  have hconst : ∑ _j ∈ S, n.factorization q = r * n.factorization q := by
    simp [hcardS]
  rw [hsum, hconst, Nat.mul_comm] at hlt
  exact Nat.lt_irrefl _ hlt

/-- The prime-power factors can be indexed by a prime factor of `n` and one
of `r` copies, compatibly with their underlying prime. -/
lemma prime_power_index_equiv {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, (p i).Prime) (e : ι → ℕ) (he : ∀ i, e i ≠ 0)
    {n r : ℕ} (hn : 0 < n) (hdiv : ∀ i, p i ^ e i ∣ n)
    (hgcd : ∀ d, d ∣ n → ∏ i, (p i ^ e i).gcd d = d ^ r) :
    ∃ idx : ι ≃ (n.primeFactors × Fin r), ∀ i, (idx i).1.val = p i := by
  classical
  let f : ι → n.primeFactors := fun i ↦
    ⟨p i, Nat.mem_primeFactors.mpr
      ⟨hp i, (dvd_pow_self (p i) (he i)).trans (hdiv i), hn.ne'⟩⟩
  let efiber (q : n.primeFactors) : {i // f i = q} ≃ {i // p i = q.val} :=
    { toFun := fun i ↦ ⟨i, congrArg Subtype.val i.prop⟩
      invFun := fun i ↦ ⟨i, Subtype.ext i.prop⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcardFiber (q : n.primeFactors) : Fintype.card {i // f i = q} = r := by
    rw [Fintype.card_congr (efiber q)]
    exact card_prime_fiber_of_gcd_product p hp e he
      (Nat.prime_of_mem_primeFactors q.prop)
      (hgcd q (Nat.dvd_of_mem_primeFactors q.prop))
  let fiberFin (q : n.primeFactors) : {i // f i = q} ≃ Fin r :=
    Fintype.equivOfCardEq (by simpa using hcardFiber q)
  let idx : ι ≃ (n.primeFactors × Fin r) :=
    (Equiv.sigmaFiberEquiv f).symm.trans <|
      (Equiv.sigmaCongrRight fiberFin).trans (Equiv.sigmaEquivProd _ _)
  exact ⟨idx, fun _ ↦ rfl⟩

/-- Reorder a product indexed by `α × β`, with component type depending only
on `α`, as `β` copies of the product over `α`. -/
noncomputable def piPrimeCopiesAddEquiv {α β : Type*} (B : α → Type*)
    [∀ a, AddCommGroup (B a)] :
    (∀ x : α × β, B x.1) ≃+ (∀ _b : β, ∀ a : α, B a) where
  toFun x b a := x (a, b)
  invFun x ab := x ab.2 ab.1
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

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
    Nonempty ((Submodule.torsionBy ℤ A n) ≃+ (Fin r → (ZMod n))) := by
  classical
  obtain ⟨ι, hι, p, hp, e, he, E, hgcd⟩ := group_theory_structure_data hn r h
  letI : Fintype ι := hι
  have hdiv : ∀ i, p i ^ e i ∣ n :=
    cyclic_factor_dvd_of_torsion_equiv (fun i ↦ p i ^ e i) E
  have hexp : ∀ i, e i = n.factorization (p i) :=
    prime_power_exponent_eq_factorization p hp e he hn hdiv hgcd
  obtain ⟨idx, hidx⟩ := prime_power_index_equiv p hp e he hn hdiv hgcd
  let B : n.primeFactors × Fin r → Type := fun x ↦
    ZMod (x.1.val ^ n.factorization x.1.val)
  let efactors : (∀ i, ZMod (p i ^ e i)) ≃+ (∀ i, B (idx i)) :=
    AddEquiv.piCongrRight fun i ↦ (ZMod.ringEquivCongr <| by
      calc
        p i ^ e i = p i ^ n.factorization (p i) := congrArg (p i ^ ·) (hexp i)
        _ = (idx i).1.val ^ n.factorization (idx i).1.val := by rw [hidx i]).toAddEquiv
  let eindex : (∀ i, B (idx i)) ≃+ (∀ x, B x) :=
    (RingEquiv.piCongrLeft B idx).toAddEquiv
  let ecopies : (∀ x, B x) ≃+
      (∀ _j : Fin r, ∀ q : n.primeFactors,
        ZMod (q.val ^ n.factorization q.val)) :=
    piPrimeCopiesAddEquiv fun q : n.primeFactors ↦
      ZMod (q.val ^ n.factorization q.val)
  let ecrt : (∀ _j : Fin r, ∀ q : n.primeFactors,
      ZMod (q.val ^ n.factorization q.val)) ≃+ (Fin r → ZMod n) :=
    AddEquiv.piCongrRight fun _ ↦ (ZMod.equivPi n hn.ne').symm.toAddEquiv
  exact ⟨(((E.trans efactors).trans eindex).trans ecopies).trans ecrt⟩

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

/-- Prime-to-characteristic torsion over a separably closed field is finite as a module over
`ZMod n`. -/
theorem WeierstrassCurve.n_torsion_module_finite [IsSepClosed k] {n : ℕ}
    (hn : (n : k) ≠ 0) :
    Module.Finite (ZMod n) (E.nTorsion n) := by
  letI : Finite (E.nTorsion n) := E.n_torsion_finite hn
  exact Module.Finite.of_finite

noncomputable instance (n : ℕ) [IsSepClosed k] [NeZero (n : k)] :
    Module.Finite (ZMod n) (E.nTorsion n) :=
  E.n_torsion_module_finite (NeZero.ne (n : k))

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
    [DecidableEq K] [DecidableEq (AlgebraicClosure K)] (n : ℕ) [NeZero (n : K)] (hn : 0 < n) :
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
  have hnAC : (n : AlgebraicClosure K) ≠ 0 := by
    intro h
    apply NeZero.ne (n : K)
    apply (algebraMap K (AlgebraicClosure K)).injective
    simpa only [map_natCast, map_zero] using h
  haveI : Finite T := (E⁄(AlgebraicClosure K)).n_torsion_finite hnAC
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
