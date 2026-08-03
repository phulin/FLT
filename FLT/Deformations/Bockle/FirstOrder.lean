/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Bockle.Cohomology
public import FLT.Deformations.DualNumber
public import FLT.Deformations.LiftFunctor
public import FLT.Mathlib.LinearAlgebra.Matrix.DualNumber

/-!
# First-order deformations and adjoint cocycles

For an adjoint cocycle `c`, the familiar formula

`rhoₑ(g) = (1 + ε c(g)) rho(g)`

defines a representation over the dual numbers.  This file separates the calculation into an
endomorphism-valued square-zero extension and its matrix realization.  Trace zero, and hence the
fixed-determinant calculation, is handled separately below.
-/

@[expose] public section

universe u

open scoped DualNumber

namespace Deformation

section General

variable {k G V : Type u} [CommRing k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The value `(rho(g), c(g) * rho(g))` in the square-zero extension of the endomorphism ring.
It represents `(1 + ε c(g)) rho(g)`. -/
def firstOrderEndValue (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) : DualNumber (Module.End k V) :=
  (rho g, c g * rho g)

@[simp]
lemma firstOrderEndValue_fst (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) :
    (firstOrderEndValue rho c g).fst = rho g := rfl

@[simp]
lemma firstOrderEndValue_snd (rho : Representation k G V)
    (c : G → Module.End k V) (g : G) :
    (firstOrderEndValue rho c g).snd = c g * rho g := rfl

/-- The crossed-homomorphism identity is exactly the multiplicativity calculation for a
first-order lift. -/
lemma firstOrderEndValue_map_mul (rho : Representation k G V)
    (c : G → Module.End k V)
    (hc : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g)
    (g h : G) :
    firstOrderEndValue rho c (g * h) =
      firstOrderEndValue rho c g * firstOrderEndValue rho c h := by
  apply TrivSqZeroExt.ext
  · change rho (g * h) = rho g * rho h
    rw [map_mul]
  · change c (g * h) * rho (g * h) =
      rho g * (c h * rho h) + (c g * rho g) * rho h
    rw [hc, map_mul]
    simp only [add_mul, mul_assoc]
    rw [← mul_assoc (rho g⁻¹) (rho g) (rho h), ← map_mul]
    simp

/-- An adjoint cocycle produces a monoid homomorphism into the square-zero extension of the
endomorphism ring. -/
def firstOrderEndMonoidHom (rho : Representation k G V)
    (c : G → Module.End k V) (hc_one : c 1 = 0)
    (hc_mul : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g) :
    G →* DualNumber (Module.End k V) where
  toFun := firstOrderEndValue rho c
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp [firstOrderEndValue, hc_one]
  map_mul' := firstOrderEndValue_map_mul rho c hc_mul

@[simp]
lemma firstOrderEndMonoidHom_apply (rho : Representation k G V)
    (c : G → Module.End k V) (hc_one : c 1 = 0)
    (hc_mul : ∀ g h, c (g * h) = rho g * c h * rho g⁻¹ + c g) (g : G) :
    firstOrderEndMonoidHom rho c hc_one hc_mul g = firstOrderEndValue rho c g := rfl

/-- A named constructor for dual numbers of endomorphisms, avoiding reducibility-sensitive
elaboration of product notation in multiplicative expressions. -/
def endDualNumber (x y : Module.End k V) : DualNumber (Module.End k V) :=
  (x, y)

@[simp]
lemma endDualNumber_fst (x y : Module.End k V) : (endDualNumber x y).fst = x := rfl

@[simp]
lemma endDualNumber_snd (x y : Module.End k V) : (endDualNumber x y).snd = y := rfl

/-- The strict first-order change of basis `1 - ε a`.  Its inverse is `1 + ε a`. -/
def firstOrderConjugatingUnit (a : Module.End k V) : Units (DualNumber (Module.End k V)) where
  val := endDualNumber 1 (-a)
  inv := endDualNumber 1 a
  val_inv := by
    apply TrivSqZeroExt.ext
    · change 1 * 1 = 1
      simp
    · change 1 * a + (-a) * 1 = 0
      simp
  inv_val := by
    apply TrivSqZeroExt.ext
    · change 1 * 1 = 1
      simp
    · change 1 * (-a) + a * 1 = 0
      simp

@[simp]
lemma firstOrderConjugatingUnit_val (a : Module.End k V) :
    (firstOrderConjugatingUnit a : DualNumber (Module.End k V)) = endDualNumber 1 (-a) :=
  rfl

@[simp]
lemma firstOrderConjugatingUnit_inv_val (a : Module.End k V) :
    (↑((firstOrderConjugatingUnit a)⁻¹) : DualNumber (Module.End k V)) = endDualNumber 1 a :=
  rfl

/-- An inner adjoint cocycle changes the constant first-order lift by strict conjugation. -/
lemma firstOrderEndValue_eq_conj_of_inner (rho : Representation k G V)
    (a : Module.End k V) (g : G) :
    firstOrderEndValue rho (fun h ↦ rho h * a * rho h⁻¹ - a) g =
      (firstOrderConjugatingUnit a : DualNumber (Module.End k V)) *
        firstOrderEndValue rho 0 g *
          (↑((firstOrderConjugatingUnit a)⁻¹) : DualNumber (Module.End k V)) := by
  have hexplicit :
      firstOrderEndValue rho (fun h ↦ rho h * a * rho h⁻¹ - a) g =
        endDualNumber 1 (-a) * firstOrderEndValue rho 0 g * endDualNumber 1 a := by
    apply TrivSqZeroExt.ext
    · change rho g = (1 * rho g) * 1
      simp
    · change (rho g * a * rho g⁻¹ - a) * rho g =
        (1 * rho g) * a + (1 * 0 + (-a) * rho g) * 1
      rw [sub_mul, mul_assoc (rho g * a), ← map_mul]
      simp [sub_eq_add_neg]
  simpa only [firstOrderConjugatingUnit_val, firstOrderConjugatingUnit_inv_val] using hexplicit

/-- Adding an inner cocycle to any first-order deformation is strict conjugation by
`1 - ε a`. -/
lemma firstOrderEndValue_add_inner_eq_conj (rho : Representation k G V)
    (c : G → Module.End k V) (a : Module.End k V) (g : G) :
    firstOrderEndValue rho
        (fun h ↦ c h + (rho h * a * rho h⁻¹ - a)) g =
      (firstOrderConjugatingUnit a : DualNumber (Module.End k V)) *
        firstOrderEndValue rho c g *
          (↑((firstOrderConjugatingUnit a)⁻¹) : DualNumber (Module.End k V)) := by
  have hexplicit :
      firstOrderEndValue rho
          (fun h ↦ c h + (rho h * a * rho h⁻¹ - a)) g =
        endDualNumber 1 (-a) * firstOrderEndValue rho c g * endDualNumber 1 a := by
    apply TrivSqZeroExt.ext
    · change rho g = (1 * rho g) * 1
      simp
    · change (c g + (rho g * a * rho g⁻¹ - a)) * rho g =
        (1 * rho g) * a + (1 * (c g * rho g) + (-a) * rho g) * 1
      rw [add_mul, sub_mul, mul_assoc (rho g * a), ← map_mul]
      simp [sub_eq_add_neg]
      abel
  simpa only [firstOrderConjugatingUnit_val, firstOrderConjugatingUnit_inv_val] using hexplicit

end General

section RankTwo

variable {k G : Type u} [Field k] [Group G]
  [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G]

/-- The endomorphism-valued first-order representation attached to a trace-zero adjoint
cocycle. -/
noncomputable def bockleFirstOrderEndMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    G →* DualNumber (Module.End k (Fin 2 → k)) := by
  let c : G → Module.End k (Fin 2 → k) := fun g ↦
    Representation.traceZeroAdjointTopRepToEnd rho (σ g)
  refine firstOrderEndMonoidHom rho c ?_ ?_
  · change Representation.traceZeroAdjointTopRepToEnd rho (σ 1) = 0
    rw [ContinuousCohomology.Cocycles₁.map_one
      (Representation.traceZeroAdjointTopRep rho) σ, map_zero]
  · intro g h
    have hσ := congrArg (Representation.traceZeroAdjointTopRepToEnd rho)
      (BockleAdjointCocycles₁.map_mul rho σ g h)
    rw [map_add, Representation.traceZeroAdjointTopRepToEnd_action] at hσ
    exact hσ

@[simp]
lemma bockleFirstOrderEndMonoidHom_fst
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderEndMonoidHom rho σ g).fst = rho g := rfl

@[simp]
lemma bockleFirstOrderEndMonoidHom_snd
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderEndMonoidHom rho σ g).snd =
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) * rho g := rfl

@[simp]
lemma bockleFirstOrderEndMonoidHom_apply
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    bockleFirstOrderEndMonoidHom rho σ g =
      firstOrderEndValue rho
        (fun h ↦ Representation.traceZeroAdjointTopRepToEnd rho (σ h)) g :=
  rfl

/-- In endomorphism coordinates, a homogeneous degree-one boundary is the inner cocycle
`rho(g) a rho(g)⁻¹ - a`. -/
lemma bockleBoundary_toEnd
    (rho : Representation k G (Fin 2 → k))
    (a : (TopRep.homogeneousCochains
      (Representation.traceZeroAdjointTopRep rho)).X 0) (g : G) :
    Representation.traceZeroAdjointTopRepToEnd rho
        ((ContinuousCohomology.bdryKer
          (Representation.traceZeroAdjointTopRep rho) 1 a : BockleAdjointCocycles₁ rho) g) =
      rho g * Representation.traceZeroAdjointTopRepToEnd rho (a.1 1) * rho g⁻¹ -
        Representation.traceZeroAdjointTopRepToEnd rho (a.1 1) := by
  rw [ContinuousCohomology.bdryKer_one_apply_eq_action_sub, map_sub,
    Representation.traceZeroAdjointTopRepToEnd_action]

/-- A cocycle representing zero in `H¹` gives a strict conjugate of the constant
first-order lift. -/
theorem bockleFirstOrderEndMonoidHom_eq_conj_of_isCoboundary
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hσ : ContinuousCohomology.IsCoboundary₁
      (Representation.traceZeroAdjointTopRep rho) σ) :
    ∃ a : Module.End k (Fin 2 → k), ∀ g,
      bockleFirstOrderEndMonoidHom rho σ g =
        (firstOrderConjugatingUnit a : DualNumber (Module.End k (Fin 2 → k))) *
          firstOrderEndValue rho 0 g *
            (↑((firstOrderConjugatingUnit a)⁻¹) :
              DualNumber (Module.End k (Fin 2 → k))) := by
  obtain ⟨a, rfl⟩ := hσ
  let A := Representation.traceZeroAdjointTopRepToEnd rho (a.1 1)
  refine ⟨A, fun g ↦ ?_⟩
  rw [bockleFirstOrderEndMonoidHom_apply]
  calc
    firstOrderEndValue rho
        (fun h ↦ Representation.traceZeroAdjointTopRepToEnd rho
          ((ContinuousCohomology.bdryKer
            (Representation.traceZeroAdjointTopRep rho) 1 a : BockleAdjointCocycles₁ rho) h)) g =
        firstOrderEndValue rho (fun h ↦ rho h * A * rho h⁻¹ - A) g := by
      apply TrivSqZeroExt.ext
      · rfl
      · simpa only [firstOrderEndValue_snd, A] using
          congrArg (fun z : Module.End k (Fin 2 → k) ↦ z * rho g)
          (bockleBoundary_toEnd rho a g)
    _ = _ := firstOrderEndValue_eq_conj_of_inner rho A g

/-- The first-order deformation depends, up to strict conjugacy, only on the represented
continuous `H¹` class. -/
theorem bockleFirstOrderEndMonoidHom_eq_conj_of_tangentπ_eq
    (rho : Representation k G (Fin 2 → k)) (σ τ : BockleAdjointCocycles₁ rho)
    (hστ : bockleTangentπ rho σ = bockleTangentπ rho τ) :
    ∃ a : Module.End k (Fin 2 → k), ∀ g,
      bockleFirstOrderEndMonoidHom rho σ g =
        (firstOrderConjugatingUnit a : DualNumber (Module.End k (Fin 2 → k))) *
          bockleFirstOrderEndMonoidHom rho τ g *
            (↑((firstOrderConjugatingUnit a)⁻¹) :
              DualNumber (Module.End k (Fin 2 → k))) := by
  let X := Representation.traceZeroAdjointTopRep rho
  let δ : ContinuousCohomology.Cocycles₁ X := σ - τ
  have hzero : ContinuousCohomology.H1π X δ = 0 := by
    dsimp only [δ, X]
    rw [map_sub, hστ, sub_self]
  obtain ⟨b, hb⟩ :=
    ContinuousCohomology.isCoboundary₁_of_H1π_eq_zero X δ hzero
  dsimp only [δ, X] at hb
  let a := Representation.traceZeroAdjointTopRepToEnd rho (b.1 1)
  refine ⟨a, fun g ↦ ?_⟩
  have hdiff :
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) -
          Representation.traceZeroAdjointTopRepToEnd rho (τ g) =
        rho g * a * rho g⁻¹ - a := by
    calc
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) -
          Representation.traceZeroAdjointTopRepToEnd rho (τ g) =
          Representation.traceZeroAdjointTopRepToEnd rho ((σ - τ) g) := by
            change Representation.traceZeroAdjointTopRepToEnd rho (σ g) -
              Representation.traceZeroAdjointTopRepToEnd rho (τ g) =
                Representation.traceZeroAdjointTopRepToEnd rho (σ g - τ g)
            rw [map_sub]
      _ = Representation.traceZeroAdjointTopRepToEnd rho
          ((ContinuousCohomology.bdryKer
            (Representation.traceZeroAdjointTopRep rho) 1 b : BockleAdjointCocycles₁ rho) g) := by
            rw [hb]
      _ = rho g * a * rho g⁻¹ - a := by
            simpa only [a] using bockleBoundary_toEnd rho b g
  have hsum :
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) =
        Representation.traceZeroAdjointTopRepToEnd rho (τ g) +
          (rho g * a * rho g⁻¹ - a) := by
    rw [← hdiff]
    abel
  rw [bockleFirstOrderEndMonoidHom_apply]
  calc
    firstOrderEndValue rho
        (fun h ↦ Representation.traceZeroAdjointTopRepToEnd rho (σ h)) g =
        firstOrderEndValue rho
          (fun h ↦ Representation.traceZeroAdjointTopRepToEnd rho (τ h) +
            (rho h * a * rho h⁻¹ - a)) g := by
      apply TrivSqZeroExt.ext
      · rfl
      · simpa only [firstOrderEndValue_snd] using
          congrArg (fun z : Module.End k (Fin 2 → k) ↦ z * rho g) hsum
    _ = (firstOrderConjugatingUnit a : DualNumber (Module.End k (Fin 2 → k))) *
          firstOrderEndValue rho
            (fun h ↦ Representation.traceZeroAdjointTopRepToEnd rho (τ h)) g *
          (↑((firstOrderConjugatingUnit a)⁻¹) :
            DualNumber (Module.End k (Fin 2 → k))) :=
      firstOrderEndValue_add_inner_eq_conj rho _ a g
    _ = _ := by rw [← bockleFirstOrderEndMonoidHom_apply]

/-- The trace-zero adjoint cocycle written in the standard rank-two basis. -/
noncomputable def bockleAdjointMatrix
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    Matrix (Fin 2) (Fin 2) k :=
  LinearMap.toMatrixAlgEquiv'
    (Representation.traceZeroAdjointTopRepToEnd rho (σ g))

lemma bockleAdjointMatrix_trace
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleAdjointMatrix rho σ g).trace = 0 := by
  have htrace := Representation.trace_traceZeroAdjointTopRepToEnd rho (σ g)
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin 2))] at htrace
  exact htrace

/-- Apply the standard endomorphism-to-matrix equivalence coefficientwise to a dual number. -/
noncomputable def endDualNumberToMatrixMonoidHom :
    DualNumber (Module.End k (Fin 2 → k)) →*
      Matrix (Fin 2) (Fin 2) (DualNumber k) where
  toFun z := fun i j ↦
    (LinearMap.toMatrixAlgEquiv' z.fst i j, LinearMap.toMatrixAlgEquiv' z.snd i j)
  map_one' := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mk, TrivSqZeroExt.fst_one, map_one]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · simp only [TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_one, map_zero]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  map_mul' x y := by
    apply Matrix.ext
    intro i j
    apply TrivSqZeroExt.ext
    · change LinearMap.toMatrixAlgEquiv' ((x * y).fst) i j =
        ∑ l, LinearMap.toMatrixAlgEquiv' x.fst i l *
          LinearMap.toMatrixAlgEquiv' y.fst l j
      rw [TrivSqZeroExt.fst_mul, map_mul]
      rfl
    · change LinearMap.toMatrixAlgEquiv' ((x * y).snd) i j =
        ∑ l, (LinearMap.toMatrixAlgEquiv' x.fst i l *
          LinearMap.toMatrixAlgEquiv' y.snd l j +
          LinearMap.toMatrixAlgEquiv' x.snd i l *
            LinearMap.toMatrixAlgEquiv' y.fst l j)
      rw [DualNumber.snd_mul, map_add, map_mul, map_mul]
      simp only [Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib]

omit [TopologicalSpace k] [DiscreteTopology k] in
@[simp]
lemma endDualNumberToMatrixMonoidHom_apply (z : DualNumber (Module.End k (Fin 2 → k))) :
    endDualNumberToMatrixMonoidHom z =
      Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' z.fst)
        (LinearMap.toMatrixAlgEquiv' z.snd) := by
  apply Matrix.ext
  intro i j
  rfl

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- Coefficientwise matrix realization of dual-number endomorphisms is faithful. -/
theorem endDualNumberToMatrixMonoidHom_injective :
    Function.Injective (endDualNumberToMatrixMonoidHom (k := k)) := by
  intro x y hxy
  have hparts := congrArg
    (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)) hxy
  rw [endDualNumberToMatrixMonoidHom_apply,
    endDualNumberToMatrixMonoidHom_apply,
    Matrix.dualNumberEquiv'_dualNumberOfParts,
    Matrix.dualNumberEquiv'_dualNumberOfParts] at hparts
  apply TrivSqZeroExt.ext
  · apply (LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin 2)).injective
    exact congrArg TrivSqZeroExt.fst hparts
  · apply (LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin 2)).injective
    exact congrArg TrivSqZeroExt.snd hparts
/-- The matrix-valued strict change of basis induced by `1 - ε a`. -/
noncomputable def firstOrderConjugatingMatrixUnit (a : Module.End k (Fin 2 → k)) :
    Units (Matrix (Fin 2) (Fin 2) (DualNumber k)) :=
  Units.map endDualNumberToMatrixMonoidHom (firstOrderConjugatingUnit a)

omit [TopologicalSpace k] [DiscreteTopology k] in
@[simp]
lemma firstOrderConjugatingMatrixUnit_val (a : Module.End k (Fin 2 → k)) :
    (firstOrderConjugatingMatrixUnit a : Matrix (Fin 2) (Fin 2) (DualNumber k)) =
      Matrix.dualNumberOfParts 1 (-LinearMap.toMatrixAlgEquiv' a) := by
  rw [firstOrderConjugatingMatrixUnit, Units.coe_map, firstOrderConjugatingUnit_val,
    endDualNumberToMatrixMonoidHom_apply]
  simp

omit [TopologicalSpace k] [DiscreteTopology k] in
@[simp]
lemma firstOrderConjugatingMatrixUnit_inv_val (a : Module.End k (Fin 2 → k)) :
    (↑((firstOrderConjugatingMatrixUnit a)⁻¹) :
      Matrix (Fin 2) (Fin 2) (DualNumber k)) =
      Matrix.dualNumberOfParts 1 (LinearMap.toMatrixAlgEquiv' a) := by
  rw [firstOrderConjugatingMatrixUnit, Units.coe_map_inv,
    firstOrderConjugatingUnit_inv_val, endDualNumberToMatrixMonoidHom_apply]
  simp

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- The first-order conjugating matrix reduces to the identity after killing the dual-number
direction, so it is a strict change of basis. -/
lemma firstOrderConjugatingMatrixUnit_map_fst (a : Module.End k (Fin 2 → k)) :
    (firstOrderConjugatingMatrixUnit a : Matrix (Fin 2) (Fin 2) (DualNumber k)).map
      (TrivSqZeroExt.fstHom k k k).toRingHom = 1 := by
  rw [firstOrderConjugatingMatrixUnit_val]
  apply Matrix.ext
  intro i j
  change (if i = j then 1 else 0) = if i = j then 1 else 0
  rfl

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- Every strict change of basis over the dual numbers is uniquely of first-order form
up to its infinitesimal matrix. -/
theorem exists_firstOrderConjugatingMatrixUnit_eq_of_map_fst_eq_one
    (P : Units (Matrix (Fin 2) (Fin 2) (DualNumber k)))
    (hP : (P : Matrix (Fin 2) (Fin 2) (DualNumber k)).map
      (TrivSqZeroExt.fstHom k k k).toRingHom = 1) :
    ∃ a : Module.End k (Fin 2 → k), P = firstOrderConjugatingMatrixUnit a := by
  let A : Matrix (Fin 2) (Fin 2) k :=
    (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)
      (P : Matrix (Fin 2) (Fin 2) (DualNumber k))).snd
  have hPval :
      (P : Matrix (Fin 2) (Fin 2) (DualNumber k)) =
        Matrix.dualNumberOfParts 1 A := by
    apply (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)).injective
    rw [Matrix.dualNumberEquiv'_dualNumberOfParts]
    apply TrivSqZeroExt.ext
    · exact hP
    · rfl
  let a : Module.End k (Fin 2 → k) :=
    -(LinearMap.toMatrixAlgEquiv' (R := k) (n := Fin 2)).symm A
  refine ⟨a, Units.ext ?_⟩
  rw [firstOrderConjugatingMatrixUnit_val, hPval]
  congr 1
  simp [a]
omit [TopologicalSpace k] [DiscreteTopology k] in
/-- Remove the scalar trace from a rank-two endomorphism. -/
noncomputable def rankTwoTraceZeroPart (a : Module.End k (Fin 2 → k)) :
    Module.End k (Fin 2 → k) :=
  a - ((2 : k)⁻¹ * LinearMap.trace k (Fin 2 → k) a) • 1

omit [TopologicalSpace k] [DiscreteTopology k] in
/-- The rank-two trace-zero part has trace zero in characteristic different from two. -/
theorem trace_rankTwoTraceZeroPart [NeZero (2 : k)]
    (a : Module.End k (Fin 2 → k)) :
    LinearMap.trace k (Fin 2 → k) (rankTwoTraceZeroPart a) = 0 := by
  rw [rankTwoTraceZeroPart, map_sub, map_smul, LinearMap.trace_one,
    Module.finrank_pi]
  simp only [Fintype.card_fin, Nat.cast_ofNat]
  rw [smul_eq_mul]
  field_simp
  simp
omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Removing a scalar endomorphism does not change its inner adjoint cocycle. -/
theorem rankTwoTraceZeroPart_inner (rho : Representation k G (Fin 2 → k))
    (a : Module.End k (Fin 2 → k)) (g : G) :
    rho g * rankTwoTraceZeroPart a * rho g⁻¹ - rankTwoTraceZeroPart a =
      rho g * a * rho g⁻¹ - a := by
  simp only [rankTwoTraceZeroPart, mul_sub, sub_mul, mul_smul_comm,
    smul_mul_assoc, mul_one]
  rw [mul_assoc, ← map_mul]
  simp

/-- Matrix realization of the first-order representation over `k[ε]`. -/
noncomputable def bockleFirstOrderMatrixMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    G →* Matrix (Fin 2) (Fin 2) (DualNumber k) :=
  endDualNumberToMatrixMonoidHom.comp (bockleFirstOrderEndMonoidHom rho σ)

/-- The matrix-valued first-order representation lands in `GL₂(k[ε])`.  No determinant
calculation is needed for invertibility here: a monoid homomorphism out of a group carries every
element to a unit. -/
noncomputable def bockleFirstOrderGLMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    G →* GL (Fin 2) (DualNumber k) :=
  (bockleFirstOrderMatrixMonoidHom rho σ).toHomUnits

@[simp]
lemma bockleFirstOrderGLMonoidHom_val
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderGLMonoidHom rho σ g : Matrix (Fin 2) (Fin 2) (DualNumber k)) =
      bockleFirstOrderMatrixMonoidHom rho σ g :=
  rfl

/-- A coboundary changes the constant matrix lift by a strict first-order conjugation. -/
theorem bockleFirstOrderMatrixMonoidHom_eq_conj_of_isCoboundary
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hσ : ContinuousCohomology.IsCoboundary₁
      (Representation.traceZeroAdjointTopRep rho) σ) :
    ∃ P : Units (Matrix (Fin 2) (Fin 2) (DualNumber k)), ∀ g,
      bockleFirstOrderMatrixMonoidHom rho σ g =
        (P : Matrix (Fin 2) (Fin 2) (DualNumber k)) *
          Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g)) 0 *
            (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (DualNumber k)) := by
  obtain ⟨a, ha⟩ := bockleFirstOrderEndMonoidHom_eq_conj_of_isCoboundary rho σ hσ
  refine ⟨firstOrderConjugatingMatrixUnit a, fun g ↦ ?_⟩
  have hmap := congrArg endDualNumberToMatrixMonoidHom (ha g)
  simpa only [bockleFirstOrderMatrixMonoidHom, MonoidHom.comp_apply, map_mul,
    endDualNumberToMatrixMonoidHom_apply, firstOrderEndValue_fst,
    firstOrderEndValue_snd, Pi.zero_apply, zero_mul, map_zero,
    firstOrderConjugatingUnit_val, firstOrderConjugatingUnit_inv_val,
    endDualNumber_fst, endDualNumber_snd, map_one, map_neg,
    firstOrderConjugatingMatrixUnit_val, firstOrderConjugatingMatrixUnit_inv_val] using hmap

/-- Matrix-valued first-order deformations attached to equal tangent classes are strictly
conjugate. -/
theorem bockleFirstOrderMatrixMonoidHom_eq_conj_of_tangentπ_eq
    (rho : Representation k G (Fin 2 → k)) (σ τ : BockleAdjointCocycles₁ rho)
    (hστ : bockleTangentπ rho σ = bockleTangentπ rho τ) :
    ∃ P : Units (Matrix (Fin 2) (Fin 2) (DualNumber k)), ∀ g,
      bockleFirstOrderMatrixMonoidHom rho σ g =
        (P : Matrix (Fin 2) (Fin 2) (DualNumber k)) *
          bockleFirstOrderMatrixMonoidHom rho τ g *
            (↑(P⁻¹) : Matrix (Fin 2) (Fin 2) (DualNumber k)) := by
  obtain ⟨a, ha⟩ := bockleFirstOrderEndMonoidHom_eq_conj_of_tangentπ_eq rho σ τ hστ
  refine ⟨firstOrderConjugatingMatrixUnit a, fun g ↦ ?_⟩
  have hmap := congrArg endDualNumberToMatrixMonoidHom (ha g)
  simpa only [bockleFirstOrderMatrixMonoidHom, MonoidHom.comp_apply, map_mul,
    endDualNumberToMatrixMonoidHom_apply, firstOrderConjugatingUnit_val,
    firstOrderConjugatingUnit_inv_val, endDualNumber_fst, endDualNumber_snd,
    map_one, map_neg, firstOrderConjugatingMatrixUnit_val,
    firstOrderConjugatingMatrixUnit_inv_val] using hmap

/-- Conversely, a strict first-order conjugacy is exactly equality of adjoint tangent
classes in characteristic different from two. -/
theorem bockleTangentπ_eq_of_firstOrderMatrixMonoidHom_eq_conj
    [NeZero (2 : k)] (rho : Representation k G (Fin 2 → k))
    (σ τ : BockleAdjointCocycles₁ rho) (a : Module.End k (Fin 2 → k))
    (hconj : ∀ g,
      bockleFirstOrderMatrixMonoidHom rho σ g =
        (firstOrderConjugatingMatrixUnit a :
          Matrix (Fin 2) (Fin 2) (DualNumber k)) *
          bockleFirstOrderMatrixMonoidHom rho τ g *
            (↑((firstOrderConjugatingMatrixUnit a)⁻¹) :
              Matrix (Fin 2) (Fin 2) (DualNumber k))) :
    bockleTangentπ rho σ = bockleTangentπ rho τ := by
  have hend (g : G) :
      bockleFirstOrderEndMonoidHom rho σ g =
        (firstOrderConjugatingUnit a :
          DualNumber (Module.End k (Fin 2 → k))) *
          bockleFirstOrderEndMonoidHom rho τ g *
            (↑((firstOrderConjugatingUnit a)⁻¹) :
              DualNumber (Module.End k (Fin 2 → k))) := by
    apply endDualNumberToMatrixMonoidHom_injective
    simpa only [bockleFirstOrderMatrixMonoidHom, MonoidHom.comp_apply,
      firstOrderConjugatingMatrixUnit, Units.coe_map, Units.coe_map_inv,
      map_mul] using hconj g
  have hinner (g : G) :
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) -
          Representation.traceZeroAdjointTopRepToEnd rho (τ g) =
        rho g * a * rho g⁻¹ - a := by
    have hsnd := congrArg TrivSqZeroExt.snd (hend g)
    simp only [bockleFirstOrderEndMonoidHom_apply,
      firstOrderConjugatingUnit_val, firstOrderConjugatingUnit_inv_val,
      TrivSqZeroExt.snd_mul, endDualNumber_fst, endDualNumber_snd,
      firstOrderEndValue_fst, firstOrderEndValue_snd] at hsnd
    calc
      Representation.traceZeroAdjointTopRepToEnd rho (σ g) -
          Representation.traceZeroAdjointTopRepToEnd rho (τ g) =
        (Representation.traceZeroAdjointTopRepToEnd rho (σ g) * rho g) * rho g⁻¹ -
          (Representation.traceZeroAdjointTopRepToEnd rho (τ g) * rho g) * rho g⁻¹ := by
            simp only [mul_assoc, ← map_mul]
            simp
      _ = rho g * a * rho g⁻¹ - a := by
        rw [hsnd]
        simp only [add_mul, mul_assoc, ← map_mul]
        have hrho : rho g * rho g⁻¹ = 1 := by
          rw [← map_mul]
          simp
        simp
        rw [add_mul, neg_mul]
        simp only [mul_assoc]
        rw [hrho]
        simp
        abel
  let a0 : Module.End k (Fin 2 → k) := rankTwoTraceZeroPart a
  let x0 :
      (Representation.traceZeroAdjointSubrepresentation rho).toSubmodule :=
    ⟨a0, trace_rankTwoTraceZeroPart a⟩
  let x : Representation.traceZeroAdjointTopRep rho :=
    (Representation.traceZeroAdjointTopRepLinearEquiv rho).symm x0
  have hx :
      Representation.traceZeroAdjointTopRepToEnd rho x = a0 := by
    rw [Representation.traceZeroAdjointTopRepToEnd_apply]
    dsimp only [x]
    rw [LinearEquiv.apply_symm_apply]
  let δ : BockleAdjointCocycles₁ rho := σ - τ
  have hδ (g : G) :
      δ g = (Representation.traceZeroAdjointTopRep rho).ρ g x - x := by
    apply (Representation.traceZeroAdjointTopRepLinearEquiv rho).injective
    apply Subtype.ext
    change Representation.traceZeroAdjointTopRepToEnd rho (σ g - τ g) =
      Representation.traceZeroAdjointTopRepToEnd rho
        ((Representation.traceZeroAdjointTopRep rho).ρ g x - x)
    rw [map_sub, map_sub, Representation.traceZeroAdjointTopRepToEnd_action,
      hx, rankTwoTraceZeroPart_inner]
    exact hinner g
  have hδcob : ContinuousCohomology.IsCoboundary₁
      (Representation.traceZeroAdjointTopRep rho) δ :=
    ContinuousCohomology.isCoboundary₁_of_eq_action_sub
      (Representation.traceZeroAdjointTopRep rho) δ x hδ
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact (ContinuousCohomology.H1π_eq_zero_iff
    (Representation.traceZeroAdjointTopRep rho) δ).2 hδcob
@[simp]
lemma bockleFirstOrderMatrixMonoidHom_dualNumberEquiv
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    Matrix.dualNumberEquiv' (R := k) (n := Fin 2)
        (bockleFirstOrderMatrixMonoidHom rho σ g) =
      ((LinearMap.toMatrixAlgEquiv' (rho g),
        LinearMap.toMatrixAlgEquiv'
          (Representation.traceZeroAdjointTopRepToEnd rho (σ g) * rho g)) :
        DualNumber (Matrix (Fin 2) (Fin 2) k)) := by
  apply TrivSqZeroExt.ext <;> rfl

/-- Constant and infinitesimal matrix coefficients of the first-order representation. -/
lemma bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    bockleFirstOrderMatrixMonoidHom rho σ g =
      Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g))
        (bockleAdjointMatrix rho σ g * LinearMap.toMatrixAlgEquiv' (rho g)) := by
  apply (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)).injective
  rw [bockleFirstOrderMatrixMonoidHom_dualNumberEquiv,
    Matrix.dualNumberEquiv'_dualNumberOfParts]
  apply TrivSqZeroExt.ext
  · rfl
  · simp [bockleAdjointMatrix]

/-- Killing the dual-number direction recovers the original representation. -/
lemma bockleFirstOrderMatrixMonoidHom_map_fst
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderMatrixMonoidHom rho σ g).map
        (TrivSqZeroExt.fstHom k k k).toRingHom =
      LinearMap.toMatrixAlgEquiv' (rho g) := by
  rw [bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts]
  ext i j
  rfl

/-- The matrix coefficients of the trace-zero adjoint cocycle vary continuously. -/
lemma continuous_bockleAdjointMatrix
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) :
    Continuous (fun g ↦ bockleAdjointMatrix rho σ g) := by
  letI : DiscreteTopology (Representation.traceZeroAdjointTopRep rho) := ⟨rfl⟩
  have hσ : Continuous (fun g ↦ σ g) :=
    (ContinuousCohomology.Cocycles₁.toInhomogeneous
      (Representation.traceZeroAdjointTopRep rho) σ).continuous
  have htoMatrix : Continuous (fun x : Representation.traceZeroAdjointTopRep rho ↦
      LinearMap.toMatrixAlgEquiv'
        (Representation.traceZeroAdjointTopRepToEnd rho x)) :=
    continuous_of_discreteTopology
  exact htoMatrix.comp hσ

/-- Continuity of the residual matrix representation promotes the first-order formula to a
continuous matrix-valued representation. -/
lemma continuous_bockleFirstOrderMatrixMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    Continuous (bockleFirstOrderMatrixMonoidHom rho σ) := by
  apply continuous_matrix
  intro i j
  have hinf : Continuous (fun g ↦
      (bockleAdjointMatrix rho σ g * LinearMap.toMatrixAlgEquiv' (rho g)) i j) :=
    ((continuous_bockleAdjointMatrix rho σ).matrix_mul hrho).matrix_elem i j
  have hconst : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g) i j) :=
    hrho.matrix_elem i j
  simp only [bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts,
    Matrix.dualNumberOfParts_apply]
  change Continuous (fun g ↦
    ((LinearMap.toMatrixAlgEquiv' (rho g) i j,
      (bockleAdjointMatrix rho σ g * LinearMap.toMatrixAlgEquiv' (rho g)) i j) : k × k))
  exact hconst.prodMk hinf

/-- The continuous matrix-valued first-order representation. -/
noncomputable def bockleFirstOrderMatrixContinuousMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k) :=
  ⟨bockleFirstOrderMatrixMonoidHom rho σ,
    continuous_bockleFirstOrderMatrixMonoidHom rho σ hrho⟩

@[simp]
lemma bockleFirstOrderMatrixContinuousMonoidHom_apply
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) (g : G) :
    bockleFirstOrderMatrixContinuousMonoidHom rho σ hrho g =
      bockleFirstOrderMatrixMonoidHom rho σ g :=
  rfl

/-- A continuous `GL₂(k[ε])` representation attached to an adjoint cocycle. -/
noncomputable def bockleFirstOrderGLContinuousMonoidHom
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    G →ₜ* GL (Fin 2) (DualNumber k) :=
  (bockleFirstOrderMatrixContinuousMonoidHom rho σ hrho).toHomUnits

@[simp]
lemma bockleFirstOrderGLContinuousMonoidHom_val
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) (g : G) :
    (bockleFirstOrderGLContinuousMonoidHom rho σ hrho g :
        Matrix (Fin 2) (Fin 2) (DualNumber k)) =
      bockleFirstOrderMatrixMonoidHom rho σ g :=
  rfl

/-- The first-order representation factors as `(1 + ε c(g)) · rho(g)`. -/
lemma bockleFirstOrderMatrixMonoidHom_factor
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    bockleFirstOrderMatrixMonoidHom rho σ g =
      Matrix.dualNumberOfParts 1 (bockleAdjointMatrix rho σ g) *
        Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g)) 0 := by
  rw [bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts,
    Matrix.dualNumberOfParts_mul]
  simp

/-- A trace-zero adjoint cocycle preserves the determinant to first order. -/
theorem bockleFirstOrderMatrixMonoidHom_det
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho) (g : G) :
    (bockleFirstOrderMatrixMonoidHom rho σ g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)) := by
  rw [bockleFirstOrderMatrixMonoidHom_factor, Matrix.det_mul,
    Matrix.det_dualNumberOfParts_one _ (bockleAdjointMatrix_trace rho σ g),
    Matrix.det_dualNumberOfParts_zero, one_mul]
  congr 1
  simp [LinearMap.toMatrixAlgEquiv', LinearMap.det_toMatrix']

/-- The continuous `GL₂` lift has the prescribed (constant) determinant. -/
lemma bockleFirstOrderGLContinuousMonoidHom_det
    (rho : Representation k G (Fin 2 → k)) (σ : BockleAdjointCocycles₁ rho)
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) (g : G) :
    (bockleFirstOrderGLContinuousMonoidHom rho σ hrho g :
        Matrix (Fin 2) (Fin 2) (DualNumber k)).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)) := by
  rw [bockleFirstOrderGLContinuousMonoidHom_val]
  exact bockleFirstOrderMatrixMonoidHom_det rho σ g

/-- The continuous first-order deformation corresponding to a chosen tangent-basis vector. -/
noncomputable def bockleTangentBasisFirstOrderGL
    (rho : Representation k G (Fin 2 → k))
    [Module.Finite k (BockleTangentSpace rho)]
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g)))
    (i : Fin (BockleTangentParameterCount rho)) :
    G →ₜ* GL (Fin 2) (DualNumber k) :=
  bockleFirstOrderGLContinuousMonoidHom rho
    (bockleTangentCocycleRepresentative rho i) hrho

@[simp]
lemma bockleTangentBasisFirstOrderGL_val
    (rho : Representation k G (Fin 2 → k))
    [Module.Finite k (BockleTangentSpace rho)]
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g)))
    (i : Fin (BockleTangentParameterCount rho)) (g : G) :
    (bockleTangentBasisFirstOrderGL rho hrho i g :
        Matrix (Fin 2) (Fin 2) (DualNumber k)) =
      bockleFirstOrderMatrixMonoidHom rho
        (bockleTangentCocycleRepresentative rho i) g :=
  rfl

omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Extract the adjoint matrix from a dual-number matrix lift by removing the residual
factor on the right. -/
noncomputable def firstOrderAdjointMatrixOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k)) (g : G) :
    Matrix (Fin 2) (Fin 2) k :=
  (Matrix.dualNumberEquiv' (tau g)).snd *
    LinearMap.toMatrixAlgEquiv' (rho g⁻¹)

omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A lift with residual part `rho` is reconstructed from its extracted adjoint matrix. -/
lemma matrixLift_eq_dualNumberOfParts
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g)) (g : G) :
    tau g = Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g))
      (firstOrderAdjointMatrixOfLift rho tau g *
        LinearMap.toMatrixAlgEquiv' (rho g)) := by
  apply (Matrix.dualNumberEquiv' (R := k) (n := Fin 2)).injective
  rw [Matrix.dualNumberEquiv'_dualNumberOfParts]
  apply TrivSqZeroExt.ext
  · exact hred g
  · simp [firstOrderAdjointMatrixOfLift, mul_assoc, ← map_mul]

omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Multiplicativity of a dual-number lift is exactly the crossed-homomorphism identity
for its extracted adjoint matrices. -/
lemma firstOrderAdjointMatrixOfLift_map_mul
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g)) (g h : G) :
    firstOrderAdjointMatrixOfLift rho tau (g * h) =
      LinearMap.toMatrixAlgEquiv' (rho g) *
          firstOrderAdjointMatrixOfLift rho tau h *
            LinearMap.toMatrixAlgEquiv' (rho g⁻¹) +
        firstOrderAdjointMatrixOfLift rho tau g := by
  have htau :
      Matrix.dualNumberEquiv' (tau (g * h)) =
        Matrix.dualNumberEquiv' (tau g) * Matrix.dualNumberEquiv' (tau h) := by
    rw [tau.map_mul, map_mul]
  have hsnd := congrArg TrivSqZeroExt.snd htau
  rw [DualNumber.snd_mul, hred g, hred h] at hsnd
  have hhinv :
      LinearMap.toMatrixAlgEquiv' (rho h) *
          LinearMap.toMatrixAlgEquiv' (rho h⁻¹) = 1 := by
    rw [← map_mul, ← map_mul]
    simp
  simp only [firstOrderAdjointMatrixOfLift]
  rw [hsnd]
  simp [map_mul, add_mul, mul_assoc]
  rw [← mul_assoc (LinearMap.toMatrixAlgEquiv' (rho h)), hhinv, one_mul]

omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The reconstructed lift factors as `(1 + ε C(g)) rho(g)`. -/
lemma matrixLift_firstOrder_factor
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g)) (g : G) :
    tau g =
      Matrix.dualNumberOfParts 1 (firstOrderAdjointMatrixOfLift rho tau g) *
        Matrix.dualNumberOfParts (LinearMap.toMatrixAlgEquiv' (rho g)) 0 := by
  rw [Matrix.dualNumberOfParts_mul]
  simpa using matrixLift_eq_dualNumberOfParts rho tau hred g

omit [TopologicalSpace k] [DiscreteTopology k]
  [TopologicalSpace G] [IsTopologicalGroup G] in
/-- A fixed-determinant dual-number lift has trace-zero extracted adjoint matrices. -/
lemma firstOrderAdjointMatrixOfLift_trace
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g))) (g : G) :
    (firstOrderAdjointMatrixOfLift rho tau g).trace = 0 := by
  have hfactor := matrixLift_firstOrder_factor rho tau hred g
  have hdetMatrix :
      (LinearMap.toMatrixAlgEquiv' (rho g)).det = LinearMap.det (rho g) := by
    simp [LinearMap.toMatrixAlgEquiv', LinearMap.det_toMatrix']
  have hdet' :
      (Matrix.dualNumberOfParts 1
          (firstOrderAdjointMatrixOfLift rho tau g)).det *
          algebraMap k (DualNumber k) (LinearMap.det (rho g)) =
        algebraMap k (DualNumber k) (LinearMap.det (rho g)) := by
    calc
      _ = (Matrix.dualNumberOfParts 1
              (firstOrderAdjointMatrixOfLift rho tau g)).det *
            (Matrix.dualNumberOfParts
              (LinearMap.toMatrixAlgEquiv' (rho g)) 0).det := by
          rw [Matrix.det_dualNumberOfParts_zero, hdetMatrix]
      _ = (tau g).det := by rw [← Matrix.det_mul, ← hfactor]
      _ = _ := hdet g
  have hsnd := congrArg TrivSqZeroExt.snd hdet'
  have hmul :
      (firstOrderAdjointMatrixOfLift rho tau g).trace *
          LinearMap.det (rho g) = 0 := by
    rw [TrivSqZeroExt.snd_mul, Matrix.fst_det_dualNumberOfParts_one,
      Matrix.snd_det_dualNumberOfParts_one] at hsnd
    change 1 * 0 + (firstOrderAdjointMatrixOfLift rho tau g).trace *
      LinearMap.det (rho g) = 0 at hsnd
    simpa only [one_mul, zero_add] using hsnd
  have hdet_ne : LinearMap.det (rho g) ≠ 0 := by
    intro hzero
    have hinv : rho g * rho g⁻¹ = 1 := by
      rw [← map_mul]
      simp
    have := congrArg LinearMap.det hinv
    simp [map_mul, hzero] at this
  exact (mul_eq_zero.mp hmul).resolve_right hdet_ne
/-- Package the extracted trace-zero matrix as a vector in the residual adjoint
representation. -/
noncomputable def firstOrderAdjointTopRepOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g))) (g : G) :
    Representation.traceZeroAdjointTopRep rho :=
  (Representation.traceZeroAdjointTopRepLinearEquiv rho).symm
    ⟨(firstOrderAdjointMatrixOfLift rho tau g).toLin', by
      change LinearMap.trace k (Fin 2 → k)
        (firstOrderAdjointMatrixOfLift rho tau g).toLin' = 0
      rw [Matrix.trace_toLin'_eq]
      exact firstOrderAdjointMatrixOfLift_trace rho tau hred hdet g⟩

@[simp]
lemma firstOrderAdjointTopRepOfLift_toEnd
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g))) (g : G) :
    Representation.traceZeroAdjointTopRepToEnd rho
        (firstOrderAdjointTopRepOfLift rho tau hred hdet g) =
      (firstOrderAdjointMatrixOfLift rho tau g).toLin' := by
  rw [Representation.traceZeroAdjointTopRepToEnd_apply]
  unfold firstOrderAdjointTopRepOfLift
  rw [LinearEquiv.apply_symm_apply]

/-- The packaged extracted adjoint vectors satisfy the crossed-homomorphism identity. -/
lemma firstOrderAdjointTopRepOfLift_map_mul
    (rho : Representation k G (Fin 2 → k))
    (tau : G →* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g))) (g h : G) :
    firstOrderAdjointTopRepOfLift rho tau hred hdet (g * h) =
      (Representation.traceZeroAdjointTopRep rho).ρ g
          (firstOrderAdjointTopRepOfLift rho tau hred hdet h) +
        firstOrderAdjointTopRepOfLift rho tau hred hdet g := by
  apply Representation.traceZeroAdjointTopRepToEnd_injective rho
  rw [map_add, Representation.traceZeroAdjointTopRepToEnd_action,
    firstOrderAdjointTopRepOfLift_toEnd, firstOrderAdjointTopRepOfLift_toEnd,
    firstOrderAdjointTopRepOfLift_toEnd]
  have hmatrix := firstOrderAdjointMatrixOfLift_map_mul rho tau hred g h
  have hlin := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) k ↦ A.toLin') hmatrix
  have hR (x : G) :
      Matrix.toLin' (LinearMap.toMatrixAlgEquiv' (rho x)) = rho x :=
    Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' (rho x)
  simpa only [map_add, Matrix.toLin'_mul, Module.End.mul_eq_comp,
    hR] using hlin

/-- The adjoint matrix extracted from a continuous dual-number lift varies continuously. -/
lemma continuous_firstOrderAdjointMatrixOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    Continuous (fun g ↦
      firstOrderAdjointMatrixOfLift rho tau.toMonoidHom g) := by
  have hsnd : Continuous (fun g ↦ (Matrix.dualNumberEquiv' (tau g)).snd) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun g ↦ (tau g i j).snd)
    exact continuous_snd.comp (tau.continuous.matrix_elem i j)
  have hrhoInv :
      Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g⁻¹)) :=
    hrho.comp continuous_inv
  exact hsnd.matrix_mul hrhoInv

/-- The extracted trace-zero adjoint vector of a continuous lift varies continuously. -/
lemma continuous_firstOrderAdjointTopRepOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)))
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    Continuous (fun g ↦
      firstOrderAdjointTopRepOfLift rho tau.toMonoidHom hred hdet g) := by
  let X := Representation.traceZeroAdjointTopRep rho
  letI : DiscreteTopology X := ⟨rfl⟩
  let C : G → Matrix (Fin 2) (Fin 2) k := fun g ↦
    firstOrderAdjointMatrixOfLift rho tau.toMonoidHom g
  let c : G → X := fun g ↦
    firstOrderAdjointTopRepOfLift rho tau.toMonoidHom hred hdet g
  change Continuous c
  have hC : Continuous C := continuous_firstOrderAdjointMatrixOfLift rho tau hrho
  rw [continuous_discrete_rng]
  intro y
  let S : Set (Matrix (Fin 2) (Fin 2) k) :=
    {A | ∃ h : G, C h = A ∧ c h = y}
  have hpre : c ⁻¹' {y} = C ⁻¹' S := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    change c g = y ↔ ∃ h : G, C h = C g ∧ c h = y
    constructor
    · intro hg
      exact ⟨g, rfl, hg⟩
    · rintro ⟨h, hmatrix, hhy⟩
      have hc : c h = c g := by
        apply Representation.traceZeroAdjointTopRepToEnd_injective rho
        dsimp only [c]
        rw [firstOrderAdjointTopRepOfLift_toEnd,
          firstOrderAdjointTopRepOfLift_toEnd]
        exact congrArg (fun A : Matrix (Fin 2) (Fin 2) k ↦ A.toLin') hmatrix
      exact hc.symm.trans hhy
  rw [hpre]
  exact (isOpen_discrete S).preimage hC

/-- The continuous inhomogeneous adjoint map extracted from a fixed-determinant lift. -/
noncomputable def firstOrderAdjointContinuousMapOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)))
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    C(G, Representation.traceZeroAdjointTopRep rho) :=
  ⟨fun g ↦ firstOrderAdjointTopRepOfLift rho tau.toMonoidHom hred hdet g,
    continuous_firstOrderAdjointTopRepOfLift rho tau hred hdet hrho⟩

/-- Every continuous fixed-determinant first-order lift determines a continuous
trace-zero adjoint cocycle. -/
noncomputable def firstOrderAdjointCocycleOfLift
    (rho : Representation k G (Fin 2 → k))
    (tau : G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)))
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) :
    BockleAdjointCocycles₁ rho :=
  ContinuousCohomology.Cocycles₁.ofInhomogeneous
    (Representation.traceZeroAdjointTopRep rho)
    (firstOrderAdjointContinuousMapOfLift rho tau hred hdet hrho)
    (Representation.continuous_traceZeroAdjointTopRep_action_fin_two rho hrho)
    (firstOrderAdjointTopRepOfLift_map_mul rho tau.toMonoidHom hred hdet)

@[simp]
lemma firstOrderAdjointCocycleOfLift_apply
    (rho : Representation k G (Fin 2 → k))
    (tau : G →ₜ* Matrix (Fin 2) (Fin 2) (DualNumber k))
    (hred : ∀ g, (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : ∀ g, (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)))
    (hrho : Continuous (fun g ↦ LinearMap.toMatrixAlgEquiv' (rho g))) (g : G) :
    firstOrderAdjointCocycleOfLift rho tau hred hdet hrho g =
      firstOrderAdjointTopRepOfLift rho tau.toMonoidHom hred hdet g := by
  exact ContinuousCohomology.Cocycles₁.ofInhomogeneous_apply
    (Representation.traceZeroAdjointTopRep rho)
    (firstOrderAdjointContinuousMapOfLift rho tau hred hdet hrho)
    (Representation.continuous_traceZeroAdjointTopRep_action_fin_two rho hrho)
    (firstOrderAdjointTopRepOfLift_map_mul rho tau.toMonoidHom hred hdet) g

/-- Rebuilding the first-order representation from the cocycle extracted from a
fixed-determinant lift recovers that lift pointwise. -/
lemma bockleFirstOrderMatrixMonoidHom_firstOrderAdjointCocycleOfLift
    (rho : Representation k G (Fin 2 -> k))
    (tau : ContinuousMonoidHom G (Matrix (Fin 2) (Fin 2) (DualNumber k)))
    (hred : (g : G) -> (Matrix.dualNumberEquiv' (tau g)).fst =
      LinearMap.toMatrixAlgEquiv' (rho g))
    (hdet : (g : G) -> (tau g).det =
      algebraMap k (DualNumber k) (LinearMap.det (rho g)))
    (hrho : Continuous (fun g => LinearMap.toMatrixAlgEquiv' (rho g))) (g : G) :
    bockleFirstOrderMatrixMonoidHom rho
        (firstOrderAdjointCocycleOfLift rho tau hred hdet hrho) g = tau g := by
  rw [bockleFirstOrderMatrixMonoidHom_eq_dualNumberOfParts,
    bockleAdjointMatrix, firstOrderAdjointCocycleOfLift_apply,
    firstOrderAdjointTopRepOfLift_toEnd]
  rw [show LinearMap.toMatrixAlgEquiv'
      (Matrix.toLin' (firstOrderAdjointMatrixOfLift rho tau.toMonoidHom g)) =
        firstOrderAdjointMatrixOfLift rho tau.toMonoidHom g by
      exact LinearMap.toMatrix'_toLin' _]
  exact (matrixLift_eq_dualNumberOfParts rho tau.toMonoidHom hred g).symm

end RankTwo

section RepresentationFunctor

variable {R G : Type u} [CommRing R] [IsLocalRing R]
  [Finite (IsLocalRing.ResidueField R)]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Converting a `repnFunctor` value to endomorphisms and back to matrices is the identity. -/
lemma matrix_toRepresentation_apply
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField) (g : G) :
    LinearMap.toMatrixAlgEquiv' ((toRepresentation rhoRes) g) =
      (DFunLike.coe
        (F := G →ₜ* GL (Fin 2) (ProartinianCat.residueFieldType R)) rhoRes g :
          Matrix (Fin 2) (Fin 2) (ProartinianCat.residueFieldType R)) := by
  change LinearMap.toMatrixAlgEquiv'
      (Matrix.GeneralLinearGroup.toLin
        (DFunLike.coe
          (F := G →ₜ* GL (Fin 2) (ProartinianCat.residueFieldType R)) rhoRes g) :
        (Fin 2 → ProartinianCat.residueFieldType R) →ₗ[
          ProartinianCat.residueFieldType R]
        (Fin 2 → ProartinianCat.residueFieldType R)) = _
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

/-- A residual point of `repnFunctor` is continuous when its underlying endomorphisms are
written in the standard matrix basis. -/
lemma continuous_matrix_toRepresentation
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField) :
    Continuous (fun g ↦
      LinearMap.toMatrixAlgEquiv' ((toRepresentation rhoRes) g)) := by
  have hval : Continuous (fun g ↦
      (DFunLike.coe
        (F := G →ₜ* GL (Fin 2) (ProartinianCat.residueFieldType R)) rhoRes g :
          Matrix (Fin 2) (Fin 2) (ProartinianCat.residueFieldType R))) :=
    Units.continuous_val.comp rhoRes.continuous
  convert hval using 1
  funext g
  exact matrix_toRepresentation_apply rhoRes g

/-- The underlying continuous matrix representation of a repnFunctor point over the
dual numbers. -/
noncomputable def repnFunctorMatrixContinuousMonoidHom
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R)) :
    ContinuousMonoidHom G
      (Matrix (Fin 2) (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R))) :=
  { toMonoidHom := (Units.coeHom _).comp tau.toMonoidHom
    continuous_toFun := Units.continuous_val.comp tau.continuous }

@[simp]
lemma repnFunctorMatrixContinuousMonoidHom_apply
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R)) (g : G) :
    repnFunctorMatrixContinuousMonoidHom tau g =
      (DFunLike.coe
        (F := ContinuousMonoidHom G (GL (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R)))) tau g :
        Matrix (Fin 2) (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R))) :=
  rfl

/-- Matrix determinant of the continuous coercion agrees with the determinant of the
associated linear representation. -/
lemma repnFunctorMatrixContinuousMonoidHom_det
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R)) (g : G) :
    (repnFunctorMatrixContinuousMonoidHom tau g).det =
      LinearMap.det ((toRepresentation tau) g) := by
  change (DFunLike.coe
      (F := ContinuousMonoidHom G (GL (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R)))) tau g :
      Matrix (Fin 2) (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R))).det =
    LinearMap.det ((Matrix.GeneralLinearGroup.toLin
      (DFunLike.coe
        (F := ContinuousMonoidHom G (GL (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R)))) tau g)).1)
  let f : Module.End (DualNumber (ProartinianCat.residueFieldType R))
      (Fin 2 -> DualNumber (ProartinianCat.residueFieldType R)) :=
    (Matrix.GeneralLinearGroup.toLin
      (DFunLike.coe
        (F := ContinuousMonoidHom G (GL (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R)))) tau g)).1
  change (DFunLike.coe
      (F := ContinuousMonoidHom G (GL (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R)))) tau g :
      Matrix (Fin 2) (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R))).det = LinearMap.det f
  have hmatrix : LinearMap.toMatrixAlgEquiv' f =
      (DFunLike.coe
        (F := ContinuousMonoidHom G (GL (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R)))) tau g :
        Matrix (Fin 2) (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R))) := by
    dsimp only [f]
    exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _
  calc
    _ = (LinearMap.toMatrixAlgEquiv' f).det := congrArg Matrix.det hmatrix.symm
    _ = _ := LinearMap.det_toMatrix' f

/-- Exact reduction of a dual-number repnFunctor point is the residual equation used by
the adjoint-cocycle extractor. -/
lemma repnFunctorMatrixContinuousMonoidHom_fst_of_reduces
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R))
    (hred : (repnFunctor (Fin 2) G R).map
      (ProartinianCat.dualNumberToResidueField R) tau = rhoRes) (g : G) :
    (Matrix.dualNumberEquiv'
      (repnFunctorMatrixContinuousMonoidHom tau g)).fst =
        LinearMap.toMatrixAlgEquiv' ((toRepresentation rhoRes) g) := by
  rw [matrix_toRepresentation_apply]
  have hg := congrArg
    (fun x : ContinuousMonoidHom G
      (GL (Fin 2) (ProartinianCat.residueFieldType R)) => x g) hred
  have hval := congrArg Units.val hg
  change ((DFunLike.coe
      (F := ContinuousMonoidHom G (GL (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R)))) tau g :
      Matrix (Fin 2) (Fin 2)
        (DualNumber (ProartinianCat.residueFieldType R))).map
          (TrivSqZeroExt.fstHom R
            (ProartinianCat.residueFieldType R)
            (ProartinianCat.residueFieldType R)).toRingHom =
      (DFunLike.coe
        (F := ContinuousMonoidHom G
          (GL (Fin 2) (ProartinianCat.residueFieldType R))) rhoRes g :
        Matrix (Fin 2) (Fin 2) (ProartinianCat.residueFieldType R))) at hval
  exact hval

/-- Extract the continuous trace-zero adjoint cocycle from a fixed-determinant
dual-number point of repnFunctor. -/
noncomputable def firstOrderAdjointCocycleOfRepnFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R))
    (hred : (repnFunctor (Fin 2) G R).map
      (ProartinianCat.dualNumberToResidueField R) tau = rhoRes)
    (hdet : (g : G) -> (repnFunctorMatrixContinuousMonoidHom tau g).det =
      algebraMap (ProartinianCat.residueFieldType R)
        (DualNumber (ProartinianCat.residueFieldType R))
        (LinearMap.det ((toRepresentation rhoRes) g))) :=
  firstOrderAdjointCocycleOfLift (toRepresentation rhoRes)
    (repnFunctorMatrixContinuousMonoidHom tau)
    (repnFunctorMatrixContinuousMonoidHom_fst_of_reduces rhoRes tau hred)
    hdet (continuous_matrix_toRepresentation rhoRes)

/-- An adjoint cocycle at a residual `repnFunctor` point, realized as a representation over
the pro-Artinian dual-number object. -/
noncomputable def bockleFirstOrderRepnFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R) :=
  bockleFirstOrderGLContinuousMonoidHom (toRepresentation rhoRes) σ
    (continuous_matrix_toRepresentation rhoRes)

@[simp]
lemma bockleFirstOrderRepnFunctor_val
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) (g : G) :
    (DFunLike.coe
        (F := G →ₜ* GL (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R)))
        (bockleFirstOrderRepnFunctor rhoRes σ) g :
        Matrix (Fin 2) (Fin 2)
          (DualNumber (ProartinianCat.residueFieldType R))) =
      bockleFirstOrderMatrixMonoidHom (toRepresentation rhoRes) σ g :=
  rfl

/-- Rebuilding from the cocycle extracted from a fixed-determinant repnFunctor lift
recovers the original continuous representation exactly. -/
theorem bockleFirstOrderRepnFunctor_firstOrderAdjointCocycleOfRepnFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (tau : (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R))
    (hred : (repnFunctor (Fin 2) G R).map
      (ProartinianCat.dualNumberToResidueField R) tau = rhoRes)
    (hdet : (g : G) -> (repnFunctorMatrixContinuousMonoidHom tau g).det =
      algebraMap (ProartinianCat.residueFieldType R)
        (DualNumber (ProartinianCat.residueFieldType R))
        (LinearMap.det ((toRepresentation rhoRes) g))) :
    bockleFirstOrderRepnFunctor rhoRes
      (firstOrderAdjointCocycleOfRepnFunctor rhoRes tau hred hdet) = tau := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  change bockleFirstOrderMatrixMonoidHom (toRepresentation rhoRes)
      (firstOrderAdjointCocycleOfRepnFunctor rhoRes tau hred hdet) g =
    repnFunctorMatrixContinuousMonoidHom tau g
  simpa only [firstOrderAdjointCocycleOfRepnFunctor] using
    bockleFirstOrderMatrixMonoidHom_firstOrderAdjointCocycleOfLift
      (toRepresentation rhoRes) (repnFunctorMatrixContinuousMonoidHom tau)
      (repnFunctorMatrixContinuousMonoidHom_fst_of_reduces rhoRes tau hred)
      hdet (continuous_matrix_toRepresentation rhoRes) g

/-- The dual-number representation reduces to the residual `repnFunctor` point. -/
theorem bockleFirstOrderRepnFunctor_reduces
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (repnFunctor (Fin 2) G R).map
        (ProartinianCat.dualNumberToResidueField R)
        (bockleFirstOrderRepnFunctor rhoRes σ) = rhoRes := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Units.ext
  apply Matrix.ext
  intro i j
  change (TrivSqZeroExt.fstHom R
      (ProartinianCat.residueFieldType R)
      (ProartinianCat.residueFieldType R))
      (bockleFirstOrderMatrixMonoidHom (toRepresentation rhoRes) σ g i j) =
      (DFunLike.coe
        (F := G →ₜ* GL (Fin 2) (ProartinianCat.residueFieldType R)) rhoRes g :
          Matrix (Fin 2) (Fin 2) (ProartinianCat.residueFieldType R)) i j
  have hred := bockleFirstOrderMatrixMonoidHom_map_fst
    (toRepresentation rhoRes) σ g
  have hrho := matrix_toRepresentation_apply rhoRes g
  exact congrFun (congrFun (hred.trans hrho) i) j

/-- The first-order representation is an honest lift of the fixed residual point. -/
theorem bockleFirstOrderRepnFunctor_mem_liftFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    bockleFirstOrderRepnFunctor rhoRes σ ∈
      (liftFunctor (Fin 2) G R rhoRes).obj (ProartinianCat.dualNumber R) := by
  change (repnFunctor (Fin 2) G R).map
      (ProartinianCat.isTerminalResidueField.from (ProartinianCat.dualNumber R))
      (bockleFirstOrderRepnFunctor rhoRes σ) = rhoRes
  rw [Subsingleton.elim
    (ProartinianCat.isTerminalResidueField.from (ProartinianCat.dualNumber R))
    (ProartinianCat.dualNumberToResidueField R)]
  exact bockleFirstOrderRepnFunctor_reduces rhoRes σ

set_option backward.isDefEq.respectTransparency false in
/-- Equality of first-order strict-equivalence classes forces equality of the corresponding
adjoint tangent classes in characteristic different from two. -/
theorem bockleTangentπ_eq_of_firstOrderRepnFunctor_toRepnQuot_eq
    [NeZero (2 : ProartinianCat.residueFieldType R)]
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ τ : BockleAdjointCocycles₁ (toRepresentation rhoRes))
    (h : (toRepnQuot (Fin 2) G R).app (ProartinianCat.dualNumber R)
          (bockleFirstOrderRepnFunctor rhoRes σ) =
        (toRepnQuot (Fin 2) G R).app (ProartinianCat.dualNumber R)
          (bockleFirstOrderRepnFunctor rhoRes τ)) :
    bockleTangentπ (toRepresentation rhoRes) σ =
      bockleTangentπ (toRepresentation rhoRes) τ := by
  obtain ⟨P, hP⟩ := Quotient.exact h
  let P0 : GL (Fin 2)
      (DualNumber (ProartinianCat.residueFieldType R)) := P.1.ofConjAct
  have hPker : Matrix.GeneralLinearGroup.map (n := Fin 2)
      (ProartinianCat.toResidueField (ProartinianCat.dualNumber R)).hom.toRingHom P0 = 1 :=
    MonoidHom.mem_ker.mp P.2
  rw [← ProartinianCat.dualNumberToResidueField_eq_toResidueField] at hPker
  have hPval := congrArg Units.val hPker
  change (P0 : Matrix (Fin 2) (Fin 2)
      (DualNumber (ProartinianCat.residueFieldType R))).map
        (TrivSqZeroExt.fstHom R
          (ProartinianCat.residueFieldType R)
          (ProartinianCat.residueFieldType R)).toRingHom = 1 at hPval
  obtain ⟨a, hPa⟩ :=
    exists_firstOrderConjugatingMatrixUnit_eq_of_map_fst_eq_one P0 hPval
  apply bockleTangentπ_eq_of_firstOrderMatrixMonoidHom_eq_conj
    (toRepresentation rhoRes) σ τ a
  intro g
  have hg := congrArg Units.val (DFunLike.congr_fun hP g)
  change (P0 : Matrix (Fin 2) (Fin 2)
      (DualNumber (ProartinianCat.residueFieldType R))) *
        bockleFirstOrderMatrixMonoidHom (toRepresentation rhoRes) τ g *
          (↑(P0⁻¹) : Matrix (Fin 2) (Fin 2)
            (DualNumber (ProartinianCat.residueFieldType R))) =
      bockleFirstOrderMatrixMonoidHom (toRepresentation rhoRes) σ g at hg
  rw [hPa] at hg
  exact hg.symm
/-- The strict-equivalence class of the first-order representation, regarded as an
unrestricted deformation over the dual numbers. -/
noncomputable def bockleFirstOrderDeformationClass
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (deformationFunctor (Fin 2) G R rhoRes).toFunctor.obj
      (ProartinianCat.dualNumber R) :=
  deformationClassOfLift (n := Fin 2) (G := G) (𝓞 := R) rhoRes
    (bockleFirstOrderRepnFunctor rhoRes σ)
    (bockleFirstOrderRepnFunctor_mem_liftFunctor rhoRes σ)

@[simp]
lemma bockleFirstOrderDeformationClass_val
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ : BockleAdjointCocycles₁ (toRepresentation rhoRes)) :
    (bockleFirstOrderDeformationClass rhoRes σ).1 =
      (toRepnQuot (Fin 2) G R).app (ProartinianCat.dualNumber R)
        (bockleFirstOrderRepnFunctor rhoRes σ) :=
  rfl

/-- Equality of the packaged first-order deformation classes detects equality in the adjoint
tangent space. -/
theorem bockleTangentπ_eq_of_firstOrderDeformationClass_eq
    [NeZero (2 : ProartinianCat.residueFieldType R)]
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    (σ τ : BockleAdjointCocycles₁ (toRepresentation rhoRes))
    (h : bockleFirstOrderDeformationClass rhoRes σ =
      bockleFirstOrderDeformationClass rhoRes τ) :
    bockleTangentπ (toRepresentation rhoRes) σ =
      bockleTangentπ (toRepresentation rhoRes) τ := by
  apply bockleTangentπ_eq_of_firstOrderRepnFunctor_toRepnQuot_eq
  exact congrArg Subtype.val h


/-- The chosen tangent basis gives a family of points of the residual lifting functor over
the dual numbers. -/
noncomputable def bockleTangentBasisRepnFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    (repnFunctor (Fin 2) G R).obj (ProartinianCat.dualNumber R) :=
  bockleFirstOrderRepnFunctor rhoRes
    (bockleTangentCocycleRepresentative (toRepresentation rhoRes) i)

/-- The selected tangent basis, realized as strict-equivalence classes of deformations
over the dual numbers. -/
noncomputable def bockleTangentBasisDeformationClass
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    (deformationFunctor (Fin 2) G R rhoRes).toFunctor.obj
      (ProartinianCat.dualNumber R) :=
  bockleFirstOrderDeformationClass rhoRes
    (bockleTangentCocycleRepresentative (toRepresentation rhoRes) i)

lemma bockleTangentBasisRepnFunctor_mem_liftFunctor
    (rhoRes : (repnFunctor (Fin 2) G R).obj .residueField)
    [Module.Finite (ProartinianCat.residueFieldType R)
      (BockleTangentSpace (toRepresentation rhoRes))]
    (i : Fin (BockleTangentParameterCount (toRepresentation rhoRes))) :
    bockleTangentBasisRepnFunctor rhoRes i ∈
      (liftFunctor (Fin 2) G R rhoRes).obj (ProartinianCat.dualNumber R) :=
  bockleFirstOrderRepnFunctor_mem_liftFunctor rhoRes _

end RepresentationFunctor

end Deformation
