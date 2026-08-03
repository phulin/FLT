/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep
public import FLT.Mathlib.GroupTheory.Index
public import FLT.Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.FieldTheory.IsAlgClosed.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Finite images of framed Galois representations

This file contains the elementary group-theoretic and coefficient-change steps in the
finite-image argument for universal deformation rings.  In particular, it separates the
arithmetic assertion that a representation has finite image after restriction to a
finite-index subgroup from the formal deduction that its original image is finite.
-/

@[expose] public section

open scoped Pointwise

open Polynomial

/-- A finite set of integral algebra generators over a finite ring generates a finite ring. -/
theorem Algebra.finite_of_finite_generators_of_isIntegral
    {k C : Type*} [CommRing k] [CommRing C] [Algebra k C] [Finite k]
    (s : Set C) (hfinite : s.Finite) (hgen : Algebra.adjoin k s = ⊤)
    (hint : ∀ x ∈ s, IsIntegral k x) : Finite C := by
  letI : Module.Finite k (Algebra.adjoin k s) :=
    Algebra.finite_adjoin_of_finite_of_isIntegral hfinite hint
  haveI : Module.Finite k (⊤ : Subalgebra k C) := hgen ▸ inferInstance
  haveI : Module.Finite k C :=
    Module.Finite.equiv
      (Subalgebra.topEquiv : (⊤ : Subalgebra k C) ≃ₐ[k] C).toLinearEquiv
  exact Module.finite_of_finite k

/-- Integrality can be checked after quotienting a Noetherian algebra by all of its prime
ideals.  For each minimal prime choose a monic equation for the image of `x`.  The product of
these finitely many equations evaluates into the nilradical, and a power of that product gives
a monic equation already over the original algebra. -/
theorem Algebra.isIntegral_of_isIntegral_primeQuotients
    {k A : Type*} [CommRing k] [CommRing A] [Algebra k A] [IsNoetherianRing A]
    (x : A)
    (h : ∀ (P : Ideal A) [P.IsPrime],
      IsIntegral k (Ideal.Quotient.mk P x)) :
    IsIntegral k x := by
  classical
  let MinPrime := {P : Ideal A // P ∈ minimalPrimes A}
  letI : Finite MinPrime :=
    (minimalPrimes.finite_of_isNoetherianRing (R := A)).to_subtype
  letI : Fintype MinPrime := Fintype.ofFinite MinPrime
  have hpoly (P : MinPrime) :
      ∃ f : k[X], f.Monic ∧ Polynomial.eval₂ (algebraMap k A) x f ∈ P.1 := by
    letI : P.1.IsPrime := P.2.isPrime
    obtain ⟨f, hfmonic, hfroot⟩ := h P.1
    refine ⟨f, hfmonic, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    change Ideal.Quotient.mk P.1 (Polynomial.eval₂ (algebraMap k A) x f) = 0
    rw [Polynomial.hom_eval₂]
    exact hfroot
  choose f hfmonic hfeval using hpoly
  let q : k[X] := ∏ P : MinPrime, f P
  have hqmonic : q.Monic := by
    exact Polynomial.monic_prod_of_monic Finset.univ f fun P _ ↦ hfmonic P
  have hqeval_mem (P : MinPrime) :
      Polynomial.eval₂ (algebraMap k A) x q ∈ P.1 := by
    apply P.1.mem_of_dvd _ (hfeval P)
    exact _root_.map_dvd (Polynomial.eval₂RingHom (algebraMap k A) x)
      (Finset.dvd_prod_of_mem f (Finset.mem_univ P))
  have hnil : Polynomial.eval₂ (algebraMap k A) x q ∈ nilradical A := by
    change Polynomial.eval₂ (algebraMap k A) x q ∈ (⊥ : Ideal A).radical
    rw [← Ideal.sInf_minimalPrimes]
    rw [Ideal.mem_sInf]
    intro P hP
    exact hqeval_mem ⟨P, hP⟩
  obtain ⟨N, hN⟩ := (mem_nilradical.mp hnil)
  refine ⟨q ^ N, hqmonic.pow N, ?_⟩
  rw [Polynomial.eval₂_pow, hN]

/-- The trace of a finite-order matrix over a domain is integral over any coefficient ring.
After passing injectively to the algebraic closure of the fraction field, spectral mapping shows
that every characteristic root has finite order.  The trace is therefore a sum of integral roots
of unity. -/
theorem Matrix.trace_isIntegral_of_pow_eq_one
    {k : Type*} [CommRing k]
    {A : Type*} [CommRing A] [IsDomain A] [Algebra k A]
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (M : Matrix n n A) {m : ℕ} (hm : 0 < m) (hM : M ^ m = 1) :
    IsIntegral k M.trace := by
  let C := AlgebraicClosure (FractionRing A)
  let f : A →+* C := algebraMap A C
  let MC : Matrix n n C := M.map f
  have hMC : MC ^ m = 1 := by
    change (M.map f) ^ m = 1
    rw [← Matrix.map_pow, hM, Matrix.map_one f f.map_zero f.map_one]
  have hroot : ∀ z ∈ MC.charpoly.roots, IsIntegral k z := by
    intro z hz
    have hzspec : z ∈ spectrum C MC :=
      Matrix.mem_spectrum_of_isRoot_charpoly (Polynomial.mem_roots'.mp hz).2
    have hzpow : z ^ m ∈ spectrum C (MC ^ m) := spectrum.pow_mem_pow MC m hzspec
    have hspectrum_one : spectrum C (1 : Matrix n n C) = {1} := by
      simpa only [Algebra.algebraMap_eq_smul_one, one_smul] using
        (spectrum.scalar_eq (A := Matrix n n C) (1 : C))
    rw [hMC, hspectrum_one] at hzpow
    have hzone : z ^ m = 1 := by simpa using hzpow
    apply IsIntegral.of_pow hm
    rw [hzone]
    exact isIntegral_one
  have htraceC : IsIntegral k MC.trace := by
    rw [Matrix.trace_eq_sum_roots_charpoly]
    exact IsIntegral.multiset_sum hroot
  have hinj : Function.Injective (algebraMap A C) := by
    exact (algebraMap (FractionRing A) C).injective.comp
      (IsFractionRing.injective A (FractionRing A))
  apply IsIntegral.tower_bot (B := C) hinj
  rw [AddMonoidHom.map_trace]
  exact htraceC

namespace FramedGaloisRep

universe uK uA un uk

variable {K : Type uK} [Field K]
variable {A : Type uA} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
variable {n : Type un} [Fintype n] [DecidableEq n]

/-- Reduce a framed representation entrywise modulo an ideal of its coefficient ring. -/
noncomputable def quotient (rho : FramedGaloisRep K A n) (I : Ideal A) :
    FramedGaloisRep K (A ⧸ I) n :=
  rho.baseChange (Ideal.Quotient.mk I) continuous_quot_mk

/-- A framed representation has finite image if its associated homomorphism to `GL` does. -/
def HasFiniteImage (rho : FramedGaloisRep K A n) : Prop :=
  Finite rho.GL.toMonoidHom.range

/-- The exact elementary output needed from a potential-modularity restriction argument:
there is a finite-index subgroup on which the representation has finite image. -/
structure FiniteImageAfterRestriction (rho : FramedGaloisRep K A n) where
  /-- The subgroup to which the representation is restricted. -/
  subgroup : Subgroup (Field.absoluteGaloisGroup K)
  /-- The restriction subgroup has finite index. -/
  finiteIndex : subgroup.FiniteIndex
  /-- The restricted representation has finite image. -/
  restrictedFinite : Finite (rho.GL.toMonoidHom.comp subgroup.subtype).range

/-- Finite image after restriction to a finite-index subgroup implies finite image globally. -/
theorem FiniteImageAfterRestriction.finite
    {rho : FramedGaloisRep K A n} (h : rho.FiniteImageAfterRestriction) :
    rho.HasFiniteImage := by
  letI := h.finiteIndex
  exact rho.GL.toMonoidHom.finite_range_of_finiteIndex_restrict
    h.subgroup h.restrictedFinite

/-- Finite image is preserved by an arbitrary continuous change of coefficients. -/
theorem HasFiniteImage.baseChange
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (rho : FramedGaloisRep K A n) (h : rho.HasFiniteImage)
    (f : A →+* B) (hf : Continuous f) : (rho.baseChange f hf).HasFiniteImage := by
  letI : Finite rho.GL.toMonoidHom.range := h
  let g : GL n A →* GL n B := Units.map f.mapMatrix.toMonoidHom
  have heq : (rho.baseChange f hf).GL.toMonoidHom =
      g.comp rho.GL.toMonoidHom := by
    ext sigma i j
    simp [g]
  rw [HasFiniteImage, heq]
  exact rho.GL.toMonoidHom.finite_range_comp_right g

/-- The set of traces occurring in a framed representation. -/
def traceSet (rho : FramedGaloisRep K A n) : Set A :=
  Set.range fun g => Matrix.trace (rho.GL g : Matrix n n A)

/-- A representation with finite image has only finitely many traces. -/
theorem traceSet_finite_of_hasFiniteImage
    (rho : FramedGaloisRep K A n) (h : rho.HasFiniteImage) : rho.traceSet.Finite := by
  letI : Finite rho.GL.toMonoidHom.range := h
  let f : rho.GL.toMonoidHom.range → A := fun x => Matrix.trace (x.1 : Matrix n n A)
  refine (Set.finite_range f).subset ?_
  rintro x ⟨g, rfl⟩
  exact ⟨⟨rho.GL g, ⟨g, rfl⟩⟩, rfl⟩

/-- Every trace of a finite-image representation over a domain is integral over any coefficient
ring acting on the representation ring. -/
theorem isIntegral_trace_of_hasFiniteImage
    {k : Type uk} [CommRing k] [Algebra k A] [IsDomain A] [Nonempty n]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage) :
    ∀ x ∈ rho.traceSet, IsIntegral k x := by
  letI : Finite rho.GL.toMonoidHom.range := hfinite
  rintro _ ⟨g, rfl⟩
  let y : rho.GL.toMonoidHom.range := ⟨rho.GL g, ⟨g, rfl⟩⟩
  have hyfinite : IsOfFinOrder y := isOfFinOrder_of_finite y
  have hGL : (rho.GL g) ^ orderOf y = 1 := by
    exact congrArg Subtype.val (pow_orderOf_eq_one y)
  have hmatrix : ((rho.GL g : GL n A) : Matrix n n A) ^ orderOf y = 1 := by
    exact congrArg Units.val hGL
  exact Matrix.trace_isIntegral_of_pow_eq_one _ hyfinite.orderOf_pos hmatrix

/-- Entrywise coefficient change sends the old trace set onto the new trace set. -/
theorem traceSet_baseChange
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (rho : FramedGaloisRep K A n) (f : A →+* B) (hf : Continuous f) :
    (rho.baseChange f hf).traceSet = f '' rho.traceSet := by
  have htrace (g : Field.absoluteGaloisGroup K) :
      Matrix.trace ((rho.baseChange f hf).GL g : Matrix n n B) =
        f (Matrix.trace (rho.GL g : Matrix n n A)) := by
    rw [AddMonoidHom.map_trace]
    congr 1
    ext i j
    exact FramedGaloisRep.baseChange_GL rho f hf
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨Matrix.trace (rho.GL g : Matrix n n A), ⟨g, rfl⟩, (htrace g).symm⟩
  · rintro ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, htrace g⟩

/-- In every prime quotient, traces of a finite-image representation remain integral over the
coefficient ring.  This is the roots-of-unity step in the Carayol finite-image argument. -/
theorem primeQuotient_isIntegral_trace_of_hasFiniteImage
    {k : Type uk} [CommRing k] [Algebra k A] [Nonempty n]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage)
    (P : Ideal A) [P.IsPrime] :
    ∀ x ∈ Ideal.Quotient.mk P '' rho.traceSet, IsIntegral k x := by
  letI : Finite rho.GL.toMonoidHom.range := hfinite
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  let y : rho.GL.toMonoidHom.range := ⟨rho.GL g, ⟨g, rfl⟩⟩
  have hyfinite : IsOfFinOrder y := isOfFinOrder_of_finite y
  have hGL : (rho.GL g) ^ orderOf y = 1 := by
    exact congrArg Subtype.val (pow_orderOf_eq_one y)
  have hmatrix : ((rho.GL g : GL n A) : Matrix n n A) ^ orderOf y = 1 := by
    exact congrArg Units.val hGL
  change IsIntegral k (Ideal.Quotient.mk P
    (Matrix.trace ((rho.GL g : GL n A) : Matrix n n A)))
  rw [AddMonoidHom.map_trace]
  apply Matrix.trace_isIntegral_of_pow_eq_one _ hyfinite.orderOf_pos
  rw [← Matrix.map_pow, hmatrix]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- Over a Noetherian coefficient algebra, every trace of a finite-image representation is
integral over the scalar ring.  The domain argument applies in each prime quotient, and
`Algebra.isIntegral_of_isIntegral_primeQuotients` lifts the resulting equations through the
nilradical. -/
theorem isIntegral_trace_of_hasFiniteImage_of_isNoetherianRing
    {k : Type uk} [CommRing k] [Algebra k A] [IsNoetherianRing A] [Nonempty n]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage) :
    ∀ x ∈ rho.traceSet, IsIntegral k x := by
  intro x hx
  apply Algebra.isIntegral_of_isIntegral_primeQuotients x
  intro P _
  exact rho.primeQuotient_isIntegral_trace_of_hasFiniteImage hfinite P
    (Ideal.Quotient.mk P x) ⟨x, hx, rfl⟩

/-- The coefficient algebra is generated by the traces of a framed representation.  Carayol's
theorem gives the topological variant below for an absolutely irreducible universal
deformation; this stronger algebraic form is useful when it is available. -/
def IsTraceGenerated
    {k : Type uk} [CommRing k] [Algebra k A] (rho : FramedGaloisRep K A n) : Prop :=
  Algebra.adjoin k rho.traceSet = ⊤

/-- If the traces generate a coefficient algebra over a smaller scalar ring, they also
generate it after extending the scalar ring. -/
theorem IsTraceGenerated.extendScalars
    {k k' : Type*} [CommRing k] [CommRing k'] [Algebra k k']
    [Algebra k A] [Algebra k' A] [IsScalarTower k k' A]
    (rho : FramedGaloisRep K A n) (h : rho.IsTraceGenerated (k := k)) :
    rho.IsTraceGenerated (k := k') := by
  rw [IsTraceGenerated] at h ⊢
  apply top_unique
  intro x _
  have hx : x ∈ Algebra.adjoin k rho.traceSet := by
    rw [h]
    exact Set.mem_univ x
  refine Algebra.adjoin_induction
    (p := fun x _ ↦ x ∈ Algebra.adjoin k' rho.traceSet)
    (fun x hx ↦ Algebra.subset_adjoin hx) (fun r ↦ ?_)
    (fun _ _ _ _ hx hy ↦ add_mem hx hy)
    (fun _ _ _ _ hx hy ↦ mul_mem hx hy) hx
  · rw [IsScalarTower.algebraMap_apply k k' A]
    exact (Algebra.adjoin k' rho.traceSet).algebraMap_mem (algebraMap k k' r)

/-- Trace generation descends along a surjective continuous change of coefficients. -/
theorem IsTraceGenerated.baseChange
    {k : Type uk} [CommRing k] [Algebra k A]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra k B]
    (rho : FramedGaloisRep K A n) (h : rho.IsTraceGenerated (k := k))
    (f : A →ₐ[k] B) (hf : Continuous f) (hsurj : Function.Surjective f) :
    (rho.baseChange f.toRingHom hf).IsTraceGenerated (k := k) := by
  rw [IsTraceGenerated, traceSet_baseChange]
  change Algebra.adjoin k (f '' rho.traceSet) = ⊤
  rw [← AlgHom.map_adjoin f rho.traceSet]
  rw [h, Algebra.map_top]
  exact f.range_eq_top.mpr hsurj

/-- The coefficient algebra is topologically generated by the traces of a representation.
This is the precise form supplied by the Serre--Carayol descent theorem for a universal
unframed deformation over a complete local coefficient ring. -/
def IsTopologicallyTraceGenerated
    {k : Type uk} [CommRing k] [Algebra k A] (rho : FramedGaloisRep K A n) : Prop :=
  Dense (Algebra.adjoin k rho.traceSet : Set A)

/-- Algebraic trace generation implies topological trace generation. -/
theorem IsTraceGenerated.isTopologicallyTraceGenerated
    {k : Type uk} [CommRing k] [Algebra k A]
    (rho : FramedGaloisRep K A n) (h : rho.IsTraceGenerated (k := k)) :
    rho.IsTopologicallyTraceGenerated (k := k) := by
  rw [IsTopologicallyTraceGenerated, h]
  exact dense_univ

/-- Topological trace generation persists after extending the scalar ring. -/
theorem IsTopologicallyTraceGenerated.extendScalars
    {k k' : Type*} [CommRing k] [CommRing k'] [Algebra k k']
    [Algebra k A] [Algebra k' A] [IsScalarTower k k' A]
    (rho : FramedGaloisRep K A n) (h : rho.IsTopologicallyTraceGenerated (k := k)) :
    rho.IsTopologicallyTraceGenerated (k := k') := by
  rw [IsTopologicallyTraceGenerated] at h ⊢
  apply h.mono
  intro x hx
  refine Algebra.adjoin_induction
    (p := fun x _ ↦ x ∈ Algebra.adjoin k' rho.traceSet)
    (fun y hy ↦ Algebra.subset_adjoin hy) (fun r ↦ ?_)
    (fun _ _ _ _ hx hy ↦ add_mem hx hy)
    (fun _ _ _ _ hx hy ↦ mul_mem hx hy) hx
  rw [IsScalarTower.algebraMap_apply k k' A]
  exact (Algebra.adjoin k' rho.traceSet).algebraMap_mem (algebraMap k k' r)

/-- Topological trace generation descends along a surjective continuous change of
coefficients. -/
theorem IsTopologicallyTraceGenerated.baseChange
    {k : Type uk} [CommRing k] [Algebra k A]
    {B : Type*} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [Algebra k B]
    (rho : FramedGaloisRep K A n) (h : rho.IsTopologicallyTraceGenerated (k := k))
    (f : A →ₐ[k] B) (hf : Continuous f) (hsurj : Function.Surjective f) :
    (rho.baseChange f.toRingHom hf).IsTopologicallyTraceGenerated (k := k) := by
  rw [IsTopologicallyTraceGenerated, traceSet_baseChange]
  change Dense (Algebra.adjoin k (f '' rho.traceSet) : Set B)
  rw [← AlgHom.map_adjoin f rho.traceSet]
  change Dense (f '' (Algebra.adjoin k rho.traceSet : Set A))
  exact hsurj.denseRange.dense_image hf h

/-- The commutative-algebra core of the finite-image criterion: finitely many integral traces
which generate the coefficient algebra make that algebra finite over a finite base ring. -/
theorem finite_of_hasFiniteImage_of_isTraceGenerated_of_isIntegral_trace
    {k : Type uk} [CommRing k] [Finite k] [Algebra k A]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage)
    (hgen : rho.IsTraceGenerated (k := k))
    (hint : ∀ x ∈ rho.traceSet, IsIntegral k x) : Finite A :=
  Algebra.finite_of_finite_generators_of_isIntegral rho.traceSet
    (rho.traceSet_finite_of_hasFiniteImage hfinite) hgen hint

/-- A finite-image representation over a Hausdorff Noetherian coefficient algebra that is
topologically generated by its traces has finite coefficient ring.  No algebraic-generation
shortcut is used: the finite set of integral traces generates a finite, hence closed,
subalgebra; density then says that subalgebra is the whole ring. -/
theorem finite_of_hasFiniteImage_of_isTopologicallyTraceGenerated
    {k : Type uk} [CommRing k] [Finite k] [Algebra k A]
    [IsNoetherianRing A] [T1Space A] [Nonempty n]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage)
    (hgen : rho.IsTopologicallyTraceGenerated (k := k)) : Finite A := by
  let S := Algebra.adjoin k rho.traceSet
  letI : Module.Finite k S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral
      (rho.traceSet_finite_of_hasFiniteImage hfinite)
      (rho.isIntegral_trace_of_hasFiniteImage_of_isNoetherianRing hfinite)
  letI : Finite S := Module.finite_of_finite k
  have hSfinite : (S : Set A).Finite := by
    refine (Set.finite_range fun y : S ↦ (y : A)).subset ?_
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  have hSclosed : IsClosed (S : Set A) := hSfinite.isClosed
  have hStop : S = ⊤ := by
    apply SetLike.coe_injective
    change (S : Set A) = Set.univ
    rw [← hSclosed.closure_eq]
    exact hgen.closure_eq
  exact finite_of_hasFiniteImage_of_isTraceGenerated_of_isIntegral_trace rho hfinite hStop
    (rho.isIntegral_trace_of_hasFiniteImage_of_isNoetherianRing hfinite)

/-- The prime-quotient form of Carayol's finite-image criterion.  Trace generation is the
Carayol input.  For every prime quotient it remains only to prove that the images of the traces
are integral over the finite base ring; in the deformation-ring application they are sums of
roots of unity because the representation has finite image. -/
theorem finite_of_hasFiniteImage_of_isTraceGenerated_of_primeQuotient_integral_trace
    {k : Type uk} [CommRing k] [Finite k] [Algebra k A]
    [IsLocalRing A] [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField A)]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage)
    (hgen : rho.IsTraceGenerated (k := k))
    (hint : ∀ (P : Ideal A) [P.IsPrime],
      ∀ x ∈ Ideal.Quotient.mk P '' rho.traceSet, IsIntegral k x) : Finite A := by
  apply IsLocalRing.finite_of_finite_prime_quotients A
  intro P _
  apply Algebra.finite_of_finite_generators_of_isIntegral (k := k) (C := A ⧸ P)
    (Ideal.Quotient.mk P '' rho.traceSet)
  · exact (rho.traceSet_finite_of_hasFiniteImage hfinite).image _
  · change Algebra.adjoin k ((Ideal.Quotient.mkₐ k P) '' rho.traceSet) = ⊤
    rw [← AlgHom.map_adjoin (Ideal.Quotient.mkₐ k P) rho.traceSet]
    rw [hgen, Algebra.map_top]
    exact (Ideal.Quotient.mkₐ k P).range_eq_top.mpr Ideal.Quotient.mk_surjective
  · exact hint P

/-- Carayol's finite-image criterion with the roots-of-unity integrality argument discharged:
a finite-image representation whose traces generate a Noetherian local coefficient algebra over
a finite ring forces that coefficient algebra to be finite. -/
theorem finite_of_hasFiniteImage_of_isTraceGenerated
    {k : Type uk} [CommRing k] [Finite k] [Algebra k A] [Nonempty n]
    [IsLocalRing A] [IsNoetherianRing A] [Finite (IsLocalRing.ResidueField A)]
    (rho : FramedGaloisRep K A n) (hfinite : rho.HasFiniteImage)
    (hgen : rho.IsTraceGenerated (k := k)) : Finite A := by
  exact finite_of_hasFiniteImage_of_isTraceGenerated_of_primeQuotient_integral_trace
    rho hfinite hgen fun P _ =>
      rho.primeQuotient_isIntegral_trace_of_hasFiniteImage hfinite P

end FramedGaloisRep
