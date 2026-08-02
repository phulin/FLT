/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import FLT.Mathlib.LinearAlgebra.Dimension.IsQuadraticExtension
public import FLT.Mathlib.RingTheory.Norm.Quotient

/-!
# Quadratic descent algebras

This file packages the quadratic algebra `R[X]/(X² - tX + n)` together with its
canonical conjugation.  It is the coefficient algebra used to descend a finite-flat
group scheme along an unramified quadratic twist.
-/

@[expose] public section

open Polynomial IsLocalRing
open scoped TensorProduct

universe u v

namespace QuadraticDescent

variable (R : Type u) [CommRing R]

/-- The monic quadratic polynomial with trace `t` and norm `n`. -/
noncomputable def polynomial (t n : R) : R[X] :=
  X ^ 2 + (-C t * X + C n)

/-- The quadratic `R`-algebra with trace parameter `t` and norm parameter `n`. -/
abbrev Algebra (t n : R) :=
  AdjoinRoot (polynomial R t n)

lemma polynomial_monic (t n : R) : (polynomial R t n).Monic := by
  rw [show polynomial R t n = X ^ 2 + (-C t * X + C n) from rfl]
  exact monic_X_pow_add (by compute_degree!)

/-- The discriminant of `X² - tX + n`. -/
noncomputable def discriminant (t n : R) : R :=
  t ^ 2 - 4 * n

/-- The derivative of the quadratic polynomial. -/
lemma derivative_polynomial (t n : R) :
    (polynomial R t n).derivative = C 2 * X - C t := by
  unfold polynomial
  simp only [derivative_add, derivative_mul, derivative_neg, derivative_pow,
    derivative_X, derivative_C, Nat.cast_ofNat, add_zero, Nat.reduceSub, pow_one]
  ring

/-- Bézout identity expressing the discriminant through the polynomial and its derivative. -/
lemma derivative_bezout (t n : R) :
    (polynomial R t n).derivative * (polynomial R t n).derivative +
        polynomial R t n * C (-4 : R) = C (discriminant R t n) := by
  rw [derivative_polynomial]
  unfold polynomial discriminant
  simp only [map_sub, map_pow, map_mul, map_ofNat, map_neg]
  ring

/-- A nonzero residue-class discriminant is a unit in a local ring. -/
lemma discriminant_isUnit_of_residue_ne_zero [IsLocalRing R] (t n : R)
    (h : residue R (discriminant R t n) ≠ 0) : IsUnit (discriminant R t n) :=
  (residue_ne_zero_iff_isUnit _).mp h

/-- Evaluation of the quadratic polynomial, stated independently of its quotient algebra. -/
lemma eval₂_polynomial {S : Type*} [CommRing S] (f : R →+* S) (x : S) (t n : R) :
    (polynomial R t n).eval₂ f x = x ^ 2 + (-f t * x + f n) := by
  unfold polynomial
  rw [eval₂_add, eval₂_X_pow, eval₂_add, eval₂_mul, eval₂_neg,
    eval₂_C, eval₂_X, eval₂_C]

/-- The quadratic algebra is finite free over its coefficient ring. -/
noncomputable instance instModuleFree (t n : R) : Module.Free R (Algebra R t n) :=
  (polynomial_monic R t n).free_adjoinRoot

noncomputable instance instModuleFinite (t n : R) : Module.Finite R (Algebra R t n) :=
  (polynomial_monic R t n).finite_adjoinRoot

lemma natDegree_polynomial [Nontrivial R] (t n : R) :
    (polynomial R t n).natDegree = 2 := by
  unfold polynomial
  compute_degree!

noncomputable instance instNontrivial [IsDomain R] (t n : R) :
    Nontrivial (Algebra R t n) := by
  apply AdjoinRoot.nontrivial
  rw [degree_eq_natDegree (polynomial_monic R t n).ne_zero, natDegree_polynomial]
  norm_num

/-- Over a domain the quadratic algebra is a faithfully flat cover. -/
noncomputable instance instFaithfullyFlat [IsDomain R] (t n : R) :
    Module.FaithfullyFlat R (Algebra R t n) :=
  inferInstance

/-! ## Scalar extension and quadratic fields -/

section BaseChange

variable (K : Type u) [CommRing K] [_root_.Algebra R K]

/-- Adjoining a root of the trace--norm polynomial commutes with scalar extension. -/
noncomputable def algebraBaseChangeEquiv (t n : R) :
    K ⊗[R] Algebra R t n ≃ₐ[K]
      Algebra K (algebraMap R K t) (algebraMap R K n) := by
  let pR := polynomial R t n
  let pT := pR.map
    (Algebra.TensorProduct.includeRight : R →ₐ[R] K ⊗[R] R).toRingHom
  let pK := polynomial K (algebraMap R K t) (algebraMap R K n)
  let e₁ : K ⊗[R] AdjoinRoot pR ≃ₐ[K] AdjoinRoot pT :=
    AdjoinRoot.tensorAlgEquiv pR pT rfl
  let e₂ : AdjoinRoot pT ≃ₐ[K] AdjoinRoot pK :=
    AdjoinRoot.mapAlgEquiv (Algebra.TensorProduct.rid R K K) pT pK
      (Associated.of_eq (by
        simp [pT, pK, pR, polynomial, Algebra.smul_def]))
  exact e₁.trans e₂

end BaseChange

section QuadraticField

variable (K L : Type u) [Field K] [Field L] [_root_.Algebra K L]
  [Algebra.IsQuadraticExtension K L]

/-- Evaluation at a quadratic generator with prescribed trace and norm. -/
noncomputable def fieldAlgHom (t n : K) (θ : L)
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    Algebra K t n →ₐ[K] L :=
  AdjoinRoot.liftAlgHom (polynomial K t n) (Algebra.ofId K L) θ (by
    rw [eval₂_polynomial]
    change θ ^ 2 + (-(algebraMap K L t) * θ + algebraMap K L n) = 0
    have hθ := sq_sub_trace_mul_self_add_norm
      (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
    rw [htrace, hnorm] at hθ
    linear_combination hθ)

@[simp]
lemma fieldAlgHom_root (t n : K) (θ : L)
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    fieldAlgHom K L t n θ htrace hnorm
        (AdjoinRoot.root (polynomial K t n)) = θ := by
  apply AdjoinRoot.liftAlgHom_root

/-- A non-base quadratic generator makes the evaluation map surjective. -/
lemma fieldAlgHom_surjective (t n : K) (θ : L)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    Function.Surjective (fieldAlgHom K L t n θ htrace hnorm) := by
  intro z
  by_cases hz : z ∈ Set.range (algebraMap K L)
  · obtain ⟨c, rfl⟩ := hz
    refine ⟨algebraMap K (Algebra K t n) c, ?_⟩
    exact (fieldAlgHom K L t n θ htrace hnorm).commutes c
  · obtain ⟨a, b, _ha, hz⟩ :=
      Algebra.IsQuadraticExtension.exists_eq_algebraMap_add_algebraMap_mul
        K L hθ hz
    refine ⟨algebraMap K (Algebra K t n) b +
      algebraMap K (Algebra K t n) a * AdjoinRoot.root (polynomial K t n), ?_⟩
    rw [map_add, map_mul, (fieldAlgHom K L t n θ htrace hnorm).commutes,
      (fieldAlgHom K L t n θ htrace hnorm).commutes, fieldAlgHom_root]
    exact hz.symm

/-- Evaluation at a non-base generator is bijective because both sides have dimension two. -/
lemma fieldAlgHom_bijective (t n : K) (θ : L)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    Function.Bijective (fieldAlgHom K L t n θ htrace hnorm) := by
  have hsurj := fieldAlgHom_surjective K L t n θ hθ htrace hnorm
  have hdim : Module.finrank K (Algebra K t n) = Module.finrank K L := by
    calc
      Module.finrank K (Algebra K t n) = (polynomial K t n).natDegree :=
        (AdjoinRoot.powerBasis (polynomial_monic K t n).ne_zero).finrank
      _ = 2 := natDegree_polynomial K t n
      _ = Module.finrank K L :=
        (Algebra.IsQuadraticExtension.finrank_eq_two K L).symm
  have hinj :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim
      (f := (fieldAlgHom K L t n θ htrace hnorm).toLinearMap)).mpr hsurj
  exact ⟨hinj, hsurj⟩

/-- The trace--norm presentation of a quadratic extension by a non-base generator. -/
noncomputable def fieldAlgEquiv (t n : K) (θ : L)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    Algebra K t n ≃ₐ[K] L :=
  AlgEquiv.ofBijective (fieldAlgHom K L t n θ htrace hnorm)
    (fieldAlgHom_bijective K L t n θ hθ htrace hnorm)

@[simp]
lemma fieldAlgEquiv_root (t n : K) (θ : L)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = t)
    (hnorm : Algebra.norm K θ = n) :
    fieldAlgEquiv K L t n θ hθ htrace hnorm
        (AdjoinRoot.root (polynomial K t n)) = θ := by
  exact fieldAlgHom_root K L t n θ htrace hnorm

section GenericFiber

variable (R : Type u) [CommRing R] [_root_.Algebra R K]
  [_root_.Algebra R L] [IsScalarTower R K L]

/-- The generic fiber of the integral trace--norm algebra is the prescribed quadratic
field extension. -/
noncomputable def genericFiberFieldEquiv (t n : R) (θ : L)
    (hθ : θ ∉ Set.range (algebraMap K L))
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n) :
    K ⊗[R] Algebra R t n ≃ₐ[K] L :=
  (algebraBaseChangeEquiv R K t n).trans
    (fieldAlgEquiv K L (algebraMap R K t) (algebraMap R K n)
      θ hθ htrace hnorm)

/-- Evaluation of the integral trace--norm algebra in its quadratic generic fiber. -/
noncomputable def integralFieldAlgHom (t n : R) (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n) :
    Algebra R t n →ₐ[R] L :=
  AdjoinRoot.liftAlgHom (polynomial R t n) (Algebra.ofId R L) θ (by
    rw [eval₂_polynomial]
    change θ ^ 2 + (-(algebraMap R L t) * θ + algebraMap R L n) = 0
    have hθ := sq_sub_trace_mul_self_add_norm
      (Algebra.IsQuadraticExtension.finrank_eq_two K L) θ
    rw [htrace, hnorm] at hθ
    rw [IsScalarTower.algebraMap_apply R K L,
      IsScalarTower.algebraMap_apply R K L]
    linear_combination hθ)

@[simp]
lemma integralFieldAlgHom_root (t n : R) (θ : L)
    (htrace : Algebra.trace K L θ = algebraMap R K t)
    (hnorm : Algebra.norm K θ = algebraMap R K n) :
    integralFieldAlgHom K L R t n θ htrace hnorm
      (AdjoinRoot.root (polynomial R t n)) = θ := by
  apply AdjoinRoot.liftAlgHom_root

end GenericFiber

end QuadraticField

/-- The standard étale presentation attached to the quadratic polynomial.  Localizing away
from its discriminant is encoded by the constant polynomial `C discriminant`. -/
noncomputable def standardEtalePair (t n : R) : StandardEtalePair R where
  f := polynomial R t n
  monic_f := polynomial_monic R t n
  g := C (discriminant R t n)
  cond := ⟨(polynomial R t n).derivative, C (-4 : R), 1, by
    rw [pow_one]
    exact derivative_bezout R t n⟩

@[simp]
lemma standardEtalePair_f (t n : R) :
    (standardEtalePair R t n).f = polynomial R t n :=
  rfl

@[simp]
lemma standardEtalePair_g (t n : R) :
    (standardEtalePair R t n).g = C (discriminant R t n) :=
  rfl

/-- If the discriminant is a unit, the adjoined root defines a point of the standard étale
presentation. -/
lemma standardEtalePair_hasMap_root (t n : R) (hdisc : IsUnit (discriminant R t n)) :
    (standardEtalePair R t n).HasMap (AdjoinRoot.root (polynomial R t n)) := by
  constructor
  · change aeval (AdjoinRoot.root (polynomial R t n)) (polynomial R t n) = 0
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  · change IsUnit (aeval (AdjoinRoot.root (polynomial R t n))
      (C (discriminant R t n)))
    simpa only [aeval_C] using hdisc.map (algebraMap R (Algebra R t n))

/-- When the discriminant is a unit, the standard étale presentation is exactly the
quadratic adjoin-root algebra. -/
noncomputable def standardEtaleEquiv (t n : R) (hdisc : IsUnit (discriminant R t n)) :
    (standardEtalePair R t n).Ring ≃ₐ[R] Algebra R t n := by
  let P := standardEtalePair R t n
  let x : Algebra R t n := AdjoinRoot.root (polynomial R t n)
  have hx : P.HasMap x := standardEtalePair_hasMap_root R t n hdisc
  let f : P.Ring →ₐ[R] Algebra R t n := P.lift x hx
  let g : Algebra R t n →ₐ[R] P.Ring :=
    AdjoinRoot.liftAlgHom (polynomial R t n) (Algebra.ofId R P.Ring) P.X (by
      simpa only [← standardEtalePair_f R t n, aeval_def,
        Algebra.toRingHom_ofId] using P.hasMap_X.1)
  have hfX : f P.X = x := by
    dsimp only [f]
    exact P.lift_X x hx
  have hgroot : g (AdjoinRoot.root (polynomial R t n)) = P.X := by
    dsimp only [g]
    apply AdjoinRoot.liftAlgHom_root
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, hgroot, hfX]
    rfl
  · apply P.hom_ext
    rw [AlgHom.comp_apply, hfX, hgroot]
    rfl

/-- A quadratic adjoin-root algebra with unit discriminant is étale. -/
theorem etale_of_discriminant_isUnit (t n : R) (hdisc : IsUnit (discriminant R t n)) :
    _root_.Algebra.Etale R (Algebra R t n) := by
  let _ : _root_.Algebra.Etale R (standardEtalePair R t n).Ring := inferInstance
  exact _root_.Algebra.Etale.of_equiv (standardEtaleEquiv R t n hdisc)

/-- The distinguished generator satisfies its quadratic equation. -/
lemma root_sq_sub_trace_mul_add_norm (t n : R) :
    (AdjoinRoot.root (polynomial R t n)) ^ 2 +
        (-AdjoinRoot.of (polynomial R t n) t * AdjoinRoot.root (polynomial R t n) +
          AdjoinRoot.of (polynomial R t n) n) = 0 := by
  have h := AdjoinRoot.eval₂_root (polynomial R t n)
  rw [eval₂_polynomial] at h
  exact h

/-- The adjoin-root presentation identified with mathlib's explicit rank-two quadratic algebra. -/
noncomputable def quadraticAlgebraEquiv (t n : R) :
    QuadraticAlgebra R (-n) t ≃ₐ[R] Algebra R t n := by
  let x : Algebra R t n := AdjoinRoot.root (polynomial R t n)
  have hx : x * x = (-n) • (1 : Algebra R t n) + t • x := by
    have hr := root_sq_sub_trace_mul_add_norm R t n
    dsimp only [x]
    simp only [Algebra.smul_def, map_neg, mul_one,
      AdjoinRoot.algebraMap_eq]
    change
      AdjoinRoot.root (polynomial R t n) * AdjoinRoot.root (polynomial R t n) =
        -AdjoinRoot.of (polynomial R t n) n +
          AdjoinRoot.of (polynomial R t n) t *
            AdjoinRoot.root (polynomial R t n)
    linear_combination hr
  let f : QuadraticAlgebra R (-n) t →ₐ[R] Algebra R t n :=
    QuadraticAlgebra.lift ⟨x, hx⟩
  let g : Algebra R t n →ₐ[R] QuadraticAlgebra R (-n) t :=
    AdjoinRoot.liftAlgHom (polynomial R t n)
      (Algebra.ofId R (QuadraticAlgebra R (-n) t)) QuadraticAlgebra.omega (by
        rw [eval₂_polynomial]
        ext <;> simp [pow_two, QuadraticAlgebra.omega_mul_omega_eq_add,
          QuadraticAlgebra.re_one, QuadraticAlgebra.im_one])
  have hfomega :
      f (QuadraticAlgebra.omega : QuadraticAlgebra R (-n) t) = x := by
    simp [f]
  have hgroot :
      g (AdjoinRoot.root (polynomial R t n)) =
        (QuadraticAlgebra.omega : QuadraticAlgebra R (-n) t) := by
    dsimp only [g]
    apply AdjoinRoot.liftAlgHom_root
  refine AlgEquiv.ofAlgHom f g ?_ ?_
  · apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, hgroot, hfomega]
    rfl
  · apply QuadraticAlgebra.algHom_ext
    rw [AlgHom.comp_apply, hfomega, hgroot]
    rfl

@[simp]
lemma quadraticAlgebraEquiv_omega (t n : R) :
    quadraticAlgebraEquiv R t n (QuadraticAlgebra.omega : QuadraticAlgebra R (-n) t) =
      AdjoinRoot.root (polynomial R t n) := by
  simp [quadraticAlgebraEquiv]

@[simp]
lemma quadraticAlgebraEquiv_symm_root (t n : R) :
    (quadraticAlgebraEquiv R t n).symm (AdjoinRoot.root (polynomial R t n)) =
      (QuadraticAlgebra.omega : QuadraticAlgebra R (-n) t) := by
  simp [quadraticAlgebraEquiv]

/-- The scalar coefficient in the basis `1, root`. -/
noncomputable def reCoeff (t n : R) : Algebra R t n →ₗ[R] R :=
  (QuadraticAlgebra.reₗ (-n) t).comp
    (quadraticAlgebraEquiv R t n).symm.toLinearMap

/-- The root coefficient in the basis `1, root`. -/
noncomputable def imCoeff (t n : R) : Algebra R t n →ₗ[R] R :=
  (QuadraticAlgebra.imₗ (-n) t).comp
    (quadraticAlgebraEquiv R t n).symm.toLinearMap

/-- The scalar coefficient is a left inverse to the structural map into the quadratic
algebra. -/
@[simp]
lemma reCoeff_algebraMap (t n r : R) :
    reCoeff R t n (algebraMap R (Algebra R t n) r) = r := by
  simp [reCoeff, quadraticAlgebraEquiv]

@[simp]
lemma reCoeff_one (t n : R) : reCoeff R t n (1 : Algebra R t n) = 1 := by
  simpa only [map_one] using reCoeff_algebraMap R t n (1 : R)

/-- Every element has its explicit scalar-plus-root decomposition. -/
lemma eq_algebraMap_reCoeff_add_smul_root (t n : R) (z : Algebra R t n) :
    z = algebraMap R (Algebra R t n) (reCoeff R t n z) +
      imCoeff R t n z • AdjoinRoot.root (polynomial R t n) := by
  let q := (quadraticAlgebraEquiv R t n).symm z
  have hq : q =
      algebraMap R (QuadraticAlgebra R (-n) t) q.re +
        q.im • (QuadraticAlgebra.omega : QuadraticAlgebra R (-n) t) :=
    QuadraticAlgebra.mk_eq_add_smul_omega q.re q.im
  have h := congrArg (quadraticAlgebraEquiv R t n) hq
  simpa only [q, reCoeff, imCoeff, LinearMap.comp_apply,
    AlgEquiv.toLinearMap_apply, AlgEquiv.coe_toLinearEquiv,
    AlgEquiv.apply_symm_apply, QuadraticAlgebra.reₗ_apply,
    QuadraticAlgebra.imₗ_apply, map_add, map_smul,
    AlgEquiv.commutes, quadraticAlgebraEquiv_omega] using h

/-- The conjugate of the distinguished quadratic generator. -/
noncomputable def conjugateRoot (t n : R) : Algebra R t n :=
  AdjoinRoot.of (polynomial R t n) t - AdjoinRoot.root (polynomial R t n)

/-- The conjugate generator satisfies the same quadratic equation. -/
lemma conjugateRoot_isRoot (t n : R) :
    (polynomial R t n).eval₂ (AdjoinRoot.of (polynomial R t n))
      (conjugateRoot R t n) = 0 := by
  have hr := root_sq_sub_trace_mul_add_norm R t n
  rw [eval₂_polynomial]
  unfold conjugateRoot
  linear_combination hr

/-- Quadratic conjugation as an algebra endomorphism. -/
noncomputable def conjugationAlgHom (t n : R) :
    Algebra R t n →ₐ[R] Algebra R t n :=
  AdjoinRoot.liftAlgHom (polynomial R t n)
    (AdjoinRoot.ofAlgHom R (polynomial R t n))
    (conjugateRoot R t n) (conjugateRoot_isRoot R t n)

@[simp]
lemma conjugationAlgHom_root (t n : R) :
    conjugationAlgHom R t n (AdjoinRoot.root (polynomial R t n)) =
      conjugateRoot R t n := by
  unfold conjugationAlgHom
  apply AdjoinRoot.liftAlgHom_root

/-- Applying quadratic conjugation twice is the identity. -/
lemma conjugationAlgHom_involutive (t n : R) :
    Function.Involutive (conjugationAlgHom R t n) := by
  have hcomp : (conjugationAlgHom R t n).comp (conjugationAlgHom R t n) =
      AlgHom.id R (Algebra R t n) := by
    apply AdjoinRoot.algHom_ext
    rw [AlgHom.comp_apply, conjugationAlgHom_root, conjugateRoot,
      map_sub]
    rw [← AdjoinRoot.algebraMap_eq,
      (conjugationAlgHom R t n).commutes,
      conjugationAlgHom_root]
    rw [conjugateRoot]
    simp only [AdjoinRoot.algebraMap_eq, AlgHom.id_apply]
    abel
  intro x
  exact DFunLike.congr_fun hcomp x

/-- Quadratic conjugation as an involutive algebra automorphism. -/
noncomputable def conjugationAlgEquiv (t n : R) :
    Algebra R t n ≃ₐ[R] Algebra R t n :=
  AlgEquiv.ofAlgHom (conjugationAlgHom R t n) (conjugationAlgHom R t n)
    (by
      apply DFunLike.ext
      exact conjugationAlgHom_involutive R t n)
    (by
      apply DFunLike.ext
      exact conjugationAlgHom_involutive R t n)

@[simp]
lemma conjugationAlgEquiv_apply (t n : R) (x : Algebra R t n) :
    conjugationAlgEquiv R t n x = conjugationAlgHom R t n x :=
  rfl

@[simp]
lemma conjugationAlgEquiv_symm (t n : R) :
    (conjugationAlgEquiv R t n).symm = conjugationAlgEquiv R t n := by
  rfl

@[simp]
lemma conjugationAlgEquiv_apply_apply (t n : R) (z : Algebra R t n) :
    conjugationAlgEquiv R t n (conjugationAlgEquiv R t n z) = z :=
  conjugationAlgHom_involutive R t n z

/-- The explicit quadratic-algebra identification intertwines its standard star operation with
quadratic conjugation on the adjoin-root presentation. -/
lemma conjugationAlgEquiv_quadraticAlgebraEquiv (t n : R)
    (q : QuadraticAlgebra R (-n) t) :
    conjugationAlgEquiv R t n (quadraticAlgebraEquiv R t n q) =
      quadraticAlgebraEquiv R t n (star q) := by
  rcases q with ⟨a, b⟩
  change
    conjugationAlgEquiv R t n
        (quadraticAlgebraEquiv R t n (⟨a, b⟩ : QuadraticAlgebra R (-n) t)) =
      quadraticAlgebraEquiv R t n
        (⟨a + t * b, -b⟩ : QuadraticAlgebra R (-n) t)
  rw [QuadraticAlgebra.mk_eq_add_smul_omega a b,
    QuadraticAlgebra.mk_eq_add_smul_omega (a + t * b) (-b)]
  simp only [map_add, map_smul, AlgEquiv.commutes,
    quadraticAlgebraEquiv_omega, conjugationAlgEquiv_apply,
    conjugationAlgHom_root, conjugateRoot]
  rw [← AdjoinRoot.algebraMap_eq]
  simp only [Algebra.smul_def, map_mul, map_neg]
  ring

/-- Quadratic conjugation negates the root coordinate. -/
lemma imCoeff_conjugationAlgEquiv (t n : R) (z : Algebra R t n) :
    imCoeff R t n (conjugationAlgEquiv R t n z) = -imCoeff R t n z := by
  let q := (quadraticAlgebraEquiv R t n).symm z
  have h := conjugationAlgEquiv_quadraticAlgebraEquiv R t n q
  have h' := congrArg (quadraticAlgebraEquiv R t n).symm h
  have him := congrArg QuadraticAlgebra.im h'
  simpa only [q, imCoeff, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply,
    AlgEquiv.coe_toLinearEquiv, AlgEquiv.symm_apply_apply,
    AlgEquiv.apply_symm_apply, QuadraticAlgebra.imₗ_apply,
    QuadraticAlgebra.im_star] using him

/-- If `2` is invertible, the only elements fixed by quadratic conjugation are scalars. -/
lemma eq_algebraMap_of_conjugationAlgEquiv_eq (t n : R)
    (h2 : IsUnit (2 : R)) (z : Algebra R t n)
    (hz : conjugationAlgEquiv R t n z = z) :
    z = algebraMap R (Algebra R t n) (reCoeff R t n z) := by
  have himneg : -imCoeff R t n z = imCoeff R t n z := by
    calc
      -imCoeff R t n z =
          imCoeff R t n (conjugationAlgEquiv R t n z) :=
        (imCoeff_conjugationAlgEquiv R t n z).symm
      _ = imCoeff R t n z := congrArg (imCoeff R t n) hz
  have himtwo : (2 : R) * imCoeff R t n z = 0 := by
    linear_combination -himneg
  have hhalf : (↑(h2.unit⁻¹) : R) * 2 = 1 := by
    calc
      (↑(h2.unit⁻¹) : R) * 2 =
          (↑(h2.unit⁻¹) : R) * (h2.unit : R) :=
        congrArg (fun x : R ↦ (↑(h2.unit⁻¹) : R) * x) h2.unit_spec.symm
      _ = 1 := h2.unit.inv_mul
  have him : imCoeff R t n z = 0 := by
    calc
      imCoeff R t n z =
          ((↑(h2.unit⁻¹) : R) * 2) * imCoeff R t n z := by rw [hhalf, one_mul]
      _ = (↑(h2.unit⁻¹) : R) * ((2 : R) * imCoeff R t n z) := by ring
      _ = 0 := by rw [himtwo, mul_zero]
  calc
    z = algebraMap R (Algebra R t n) (reCoeff R t n z) +
        imCoeff R t n z • AdjoinRoot.root (polynomial R t n) :=
      eq_algebraMap_reCoeff_add_smul_root R t n z
    _ = algebraMap R (Algebra R t n) (reCoeff R t n z) := by
      rw [him, zero_smul, add_zero]

/-- The trace-zero generator of the quadratic algebra. -/
noncomputable def antiInvariant (t n : R) : Algebra R t n :=
  2 * AdjoinRoot.root (polynomial R t n) -
    AdjoinRoot.of (polynomial R t n) t

/-- Quadratic conjugation negates the trace-zero generator. -/
@[simp]
lemma conjugationAlgEquiv_antiInvariant (t n : R) :
    conjugationAlgEquiv R t n (antiInvariant R t n) =
      -antiInvariant R t n := by
  simp only [antiInvariant, map_sub, map_mul, map_ofNat,
    conjugationAlgEquiv_apply, conjugationAlgHom_root, conjugateRoot]
  rw [← AdjoinRoot.algebraMap_eq,
    (conjugationAlgHom R t n).commutes]
  ring

/-- The square of the trace-zero generator is the quadratic discriminant. -/
lemma antiInvariant_sq (t n : R) :
    antiInvariant R t n ^ 2 =
      algebraMap R (Algebra R t n) (discriminant R t n) := by
  have hr := root_sq_sub_trace_mul_add_norm R t n
  unfold antiInvariant discriminant
  rw [map_sub, map_pow, map_mul, map_ofNat]
  change
    (2 * AdjoinRoot.root (polynomial R t n) -
        AdjoinRoot.of (polynomial R t n) t) ^ 2 =
      (AdjoinRoot.of (polynomial R t n) t) ^ 2 -
        4 * AdjoinRoot.of (polynomial R t n) n
  linear_combination 4 * hr

/-- Unit discriminant makes the trace-zero generator invertible. -/
lemma antiInvariant_isUnit (t n : R)
    (hdisc : IsUnit (discriminant R t n)) :
    IsUnit (antiInvariant R t n) := by
  rw [← isUnit_pow_iff (n := 2) (by norm_num), antiInvariant_sq]
  exact hdisc.map (algebraMap R (Algebra R t n))

/-- An explicit inverse to the trace-zero generator. -/
noncomputable def antiInvariantInv (t n : R)
    (hdisc : IsUnit (discriminant R t n)) : Algebra R t n :=
  algebraMap R (Algebra R t n) (↑(hdisc.unit⁻¹) : R) * antiInvariant R t n

lemma antiInvariantInv_mul (t n : R)
    (hdisc : IsUnit (discriminant R t n)) :
    antiInvariantInv R t n hdisc * antiInvariant R t n = 1 := by
  rw [antiInvariantInv, mul_assoc, ← pow_two, antiInvariant_sq, ← map_mul]
  rw [← map_one (algebraMap R (Algebra R t n))]
  apply congrArg (algebraMap R (Algebra R t n))
  calc
    (↑(hdisc.unit⁻¹) : R) * discriminant R t n =
        (↑(hdisc.unit⁻¹) : R) * (hdisc.unit : R) :=
      congrArg (fun x : R ↦ (↑(hdisc.unit⁻¹) : R) * x) hdisc.unit_spec.symm
    _ = 1 := hdisc.unit.inv_mul

lemma antiInvariant_mul_inv (t n : R)
    (hdisc : IsUnit (discriminant R t n)) :
    antiInvariant R t n * antiInvariantInv R t n hdisc = 1 := by
  rw [mul_comm]
  exact antiInvariantInv_mul R t n hdisc

/-- The explicit inverse is also anti-invariant. -/
@[simp]
lemma conjugationAlgEquiv_antiInvariantInv (t n : R)
    (hdisc : IsUnit (discriminant R t n)) :
    conjugationAlgEquiv R t n (antiInvariantInv R t n hdisc) =
      -antiInvariantInv R t n hdisc := by
  simp only [antiInvariantInv, map_mul, AlgEquiv.commutes,
    conjugationAlgEquiv_antiInvariant, mul_neg]

/-- The invariant half of an element of the quadratic cover. -/
noncomputable def evenPart (t n : R) (h2 : IsUnit (2 : R))
    (z : Algebra R t n) : Algebra R t n :=
  (↑(h2.unit⁻¹) : R) • (conjugationAlgEquiv R t n z + z)

/-- The invariant coefficient of the anti-invariant half of a quadratic-cover element. -/
noncomputable def oddPart (t n : R) (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (discriminant R t n))
    (z : Algebra R t n) : Algebra R t n :=
  (↑(h2.unit⁻¹) : R) •
    (antiInvariantInv R t n hdisc * (z - conjugationAlgEquiv R t n z))

lemma conjugationAlgEquiv_evenPart (t n : R) (h2 : IsUnit (2 : R))
    (z : Algebra R t n) :
    conjugationAlgEquiv R t n (evenPart R t n h2 z) = evenPart R t n h2 z := by
  simp only [evenPart, map_smul, map_add, conjugationAlgEquiv_apply_apply]
  rw [add_comm]

lemma conjugationAlgEquiv_oddPart (t n : R) (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (discriminant R t n)) (z : Algebra R t n) :
    conjugationAlgEquiv R t n (oddPart R t n h2 hdisc z) =
      oddPart R t n h2 hdisc z := by
  simp only [oddPart, map_smul, map_mul, map_sub,
    conjugationAlgEquiv_antiInvariantInv, conjugationAlgEquiv_apply_apply]
  apply congrArg ((↑(h2.unit⁻¹) : R) • ·)
  ring

/-- The invariant half is a scalar from the base ring. -/
lemma evenPart_eq_algebraMap (t n : R) (h2 : IsUnit (2 : R))
    (z : Algebra R t n) :
    evenPart R t n h2 z =
      algebraMap R (Algebra R t n) (reCoeff R t n (evenPart R t n h2 z)) :=
  eq_algebraMap_of_conjugationAlgEquiv_eq R t n h2 _
    (conjugationAlgEquiv_evenPart R t n h2 z)

/-- The anti-invariant coefficient is a scalar from the base ring. -/
lemma oddPart_eq_algebraMap (t n : R) (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (discriminant R t n)) (z : Algebra R t n) :
    oddPart R t n h2 hdisc z =
      algebraMap R (Algebra R t n) (reCoeff R t n (oddPart R t n h2 hdisc z)) :=
  eq_algebraMap_of_conjugationAlgEquiv_eq R t n h2 _
    (conjugationAlgEquiv_oddPart R t n h2 hdisc z)

/-- Scalar and anti-invariant halves reconstruct every quadratic-cover element. -/
lemma evenPart_add_antiInvariant_mul_oddPart (t n : R) (h2 : IsUnit (2 : R))
    (hdisc : IsUnit (discriminant R t n)) (z : Algebra R t n) :
    evenPart R t n h2 z +
      antiInvariant R t n * oddPart R t n h2 hdisc z = z := by
  have hhalf : (↑(h2.unit⁻¹) : R) * 2 = 1 := by
    calc
      (↑(h2.unit⁻¹) : R) * 2 =
          (↑(h2.unit⁻¹) : R) * (h2.unit : R) :=
        congrArg (fun x : R ↦ (↑(h2.unit⁻¹) : R) * x) h2.unit_spec.symm
      _ = 1 := h2.unit.inv_mul
  rw [evenPart, oddPart, mul_smul_comm, ← mul_assoc,
    antiInvariant_mul_inv, one_mul]
  calc
    (↑(h2.unit⁻¹) : R) • (conjugationAlgEquiv R t n z + z) +
          (↑(h2.unit⁻¹) : R) • (z - conjugationAlgEquiv R t n z) =
        (↑(h2.unit⁻¹) : R) •
          ((conjugationAlgEquiv R t n z + z) +
            (z - conjugationAlgEquiv R t n z)) :=
      (smul_add (↑(h2.unit⁻¹) : R)
        (conjugationAlgEquiv R t n z + z)
        (z - conjugationAlgEquiv R t n z)).symm
    _ = (↑(h2.unit⁻¹) : R) • ((2 : R) • z) := by
      congr 1
      rw [two_smul]
      abel
    _ = z := by rw [smul_smul, hhalf, one_smul]

/-! ## Coefficients after tensoring with a module -/

section TensorCoefficients

variable (G : Type v) [AddCommMonoid G] [Module R G]

/-- Extract the scalar-basis coefficient after tensoring the quadratic algebra with a
module. -/
noncomputable def tensorReCoeff (t n : R) : Algebra R t n ⊗[R] G →ₗ[R] G :=
  (TensorProduct.lid R G).toLinearMap.comp ((reCoeff R t n).rTensor G)

/-- Extract the root-basis coefficient after tensoring the quadratic algebra with a
module. -/
noncomputable def tensorImCoeff (t n : R) : Algebra R t n ⊗[R] G →ₗ[R] G :=
  (TensorProduct.lid R G).toLinearMap.comp ((imCoeff R t n).rTensor G)

@[simp]
lemma tensorReCoeff_tmul (t n : R) (a : Algebra R t n) (g : G) :
    tensorReCoeff R G t n (a ⊗ₜ[R] g) = reCoeff R t n a • g := by
  simp [tensorReCoeff]

@[simp]
lemma tensorImCoeff_tmul (t n : R) (a : Algebra R t n) (g : G) :
    tensorImCoeff R G t n (a ⊗ₜ[R] g) = imCoeff R t n a • g := by
  simp [tensorImCoeff]

/-- The basis decomposition `A = R · 1 ⊕ R · root` persists after tensoring with any
module. -/
lemma eq_one_tmul_tensorReCoeff_add_root_tmul_tensorImCoeff
    (t n : R) (z : Algebra R t n ⊗[R] G) :
    z = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n z +
      AdjoinRoot.root (polynomial R t n) ⊗ₜ[R] tensorImCoeff R G t n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a g =>
      calc
        a ⊗ₜ[R] g =
            (algebraMap R (Algebra R t n) (reCoeff R t n a) +
              imCoeff R t n a • AdjoinRoot.root (polynomial R t n)) ⊗ₜ[R] g :=
          congrArg (fun b : Algebra R t n => b ⊗ₜ[R] g)
            (eq_algebraMap_reCoeff_add_smul_root R t n a)
        _ = algebraMap R (Algebra R t n) (reCoeff R t n a) ⊗ₜ[R] g +
            (imCoeff R t n a • AdjoinRoot.root (polynomial R t n)) ⊗ₜ[R] g := by
          rw [TensorProduct.add_tmul]
        _ = (reCoeff R t n a • (1 : Algebra R t n)) ⊗ₜ[R] g +
            (imCoeff R t n a • AdjoinRoot.root (polynomial R t n)) ⊗ₜ[R] g := by
          rw [show reCoeff R t n a • (1 : Algebra R t n) =
              algebraMap R (Algebra R t n) (reCoeff R t n a) by
            rw [Algebra.smul_def, mul_one]]
        _ = (1 : Algebra R t n) ⊗ₜ[R] (reCoeff R t n a • g) +
            AdjoinRoot.root (polynomial R t n) ⊗ₜ[R] (imCoeff R t n a • g) := by
          rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul]
        _ = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n (a ⊗ₜ[R] g) +
            AdjoinRoot.root (polynomial R t n) ⊗ₜ[R]
              tensorImCoeff R G t n (a ⊗ₜ[R] g) := by
          rw [tensorReCoeff_tmul, tensorImCoeff_tmul]
  | add x y hx hy =>
      calc
        x + y =
            ((1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n x +
              AdjoinRoot.root (polynomial R t n) ⊗ₜ[R] tensorImCoeff R G t n x) +
            ((1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n y +
              AdjoinRoot.root (polynomial R t n) ⊗ₜ[R] tensorImCoeff R G t n y) :=
          congrArg₂ (· + ·) hx hy
        _ = (1 : Algebra R t n) ⊗ₜ[R]
              (tensorReCoeff R G t n x + tensorReCoeff R G t n y) +
            AdjoinRoot.root (polynomial R t n) ⊗ₜ[R]
              (tensorImCoeff R G t n x + tensorImCoeff R G t n y) := by
          rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
          abel
        _ = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n (x + y) +
            AdjoinRoot.root (polynomial R t n) ⊗ₜ[R]
              tensorImCoeff R G t n (x + y) := by rw [map_add, map_add]

/-- Conjugation on the quadratic factor, tensor the identity on an arbitrary module. -/
noncomputable def conjugationTensorLinear (t n : R) :
    Algebra R t n ⊗[R] G →ₗ[R] Algebra R t n ⊗[R] G :=
  (conjugationAlgEquiv R t n).toLinearMap.rTensor G

@[simp]
lemma conjugationTensorLinear_tmul (t n : R) (a : Algebra R t n) (g : G) :
    conjugationTensorLinear R G t n (a ⊗ₜ[R] g) =
      conjugationAlgEquiv R t n a ⊗ₜ[R] g := by
  rfl

/-- Conjugating the quadratic factor negates the root coefficient. -/
lemma tensorImCoeff_conjugationTensorLinear (t n : R)
    (z : Algebra R t n ⊗[R] G) :
    tensorImCoeff R G t n (conjugationTensorLinear R G t n z) =
      (-1 : R) • tensorImCoeff R G t n z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a g =>
      simp only [conjugationTensorLinear_tmul, tensorImCoeff_tmul,
        imCoeff_conjugationAlgEquiv]
      rw [smul_smul]
      congr 1
      ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

/-- When `2` is invertible, conjugation-fixed elements after arbitrary scalar extension are
exactly the tensors with scalar quadratic coefficient. -/
lemma eq_one_tmul_tensorReCoeff_of_conjugationTensorLinear_eq
    (t n : R) (h2 : IsUnit (2 : R))
    (z : Algebra R t n ⊗[R] G)
    (hz : conjugationTensorLinear R G t n z = z) :
    z = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n z := by
  have himneg :
      (-1 : R) • tensorImCoeff R G t n z = tensorImCoeff R G t n z := by
    rw [← tensorImCoeff_conjugationTensorLinear R G t n z, hz]
  have himtwo : (2 : R) • tensorImCoeff R G t n z = 0 := by
    calc
      (2 : R) • tensorImCoeff R G t n z =
          tensorImCoeff R G t n z + tensorImCoeff R G t n z := by rw [two_smul]
      _ = (-1 : R) • tensorImCoeff R G t n z + tensorImCoeff R G t n z :=
        congrArg (fun x => x + tensorImCoeff R G t n z) himneg.symm
      _ = (-1 : R) • tensorImCoeff R G t n z +
          (1 : R) • tensorImCoeff R G t n z := by rw [one_smul]
      _ = ((-1 : R) + 1) • tensorImCoeff R G t n z :=
        (add_smul (-1 : R) 1 (tensorImCoeff R G t n z)).symm
      _ = 0 := by simp
  have hhalf : (↑(h2.unit⁻¹) : R) * 2 = 1 := by
    calc
      (↑(h2.unit⁻¹) : R) * 2 =
          (↑(h2.unit⁻¹) : R) * (h2.unit : R) :=
        congrArg (fun x : R => (↑(h2.unit⁻¹) : R) * x) h2.unit_spec.symm
      _ = 1 := h2.unit.inv_mul
  have him : tensorImCoeff R G t n z = 0 := by
    calc
      tensorImCoeff R G t n z =
          (((↑(h2.unit⁻¹) : R) * 2) : R) • tensorImCoeff R G t n z := by
        rw [hhalf, one_smul]
      _ = (↑(h2.unit⁻¹) : R) • ((2 : R) • tensorImCoeff R G t n z) := by
        rw [smul_smul]
      _ = 0 := by rw [himtwo, smul_zero]
  calc
    z = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n z +
        AdjoinRoot.root (polynomial R t n) ⊗ₜ[R] tensorImCoeff R G t n z :=
      eq_one_tmul_tensorReCoeff_add_root_tmul_tensorImCoeff R G t n z
    _ = (1 : Algebra R t n) ⊗ₜ[R] tensorReCoeff R G t n z := by
      rw [him, TensorProduct.tmul_zero, add_zero]

end TensorCoefficients

end QuadraticDescent
