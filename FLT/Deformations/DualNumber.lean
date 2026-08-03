/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.Categories
public import Mathlib.RingTheory.DualNumber
public import Mathlib.RingTheory.Artinian.Module

/-!
# Dual numbers as a pro-Artinian coefficient algebra

The tangent space of a deformation problem is tested on the dual numbers over the residue
field.  This file supplies their coefficientwise topology, proves that they have the same
residue field as the coefficient ring, and packages them as an object of `ProartinianCat`.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open scoped DualNumber

namespace Deformation

universe u

/-- The coefficientwise product topology on the dual numbers. -/
instance dualNumberTopology (k : Type u) [TopologicalSpace k] :
    TopologicalSpace (DualNumber k) :=
  inferInstanceAs (TopologicalSpace (k × k))

/-- Dual numbers over a discrete ring are discrete in the coefficientwise topology. -/
instance dualNumberDiscreteTopology (k : Type u) [TopologicalSpace k] [DiscreteTopology k] :
    DiscreteTopology (DualNumber k) := by
  change DiscreteTopology (k × k)
  infer_instance

/-- The residue field of `k[ε]` is `k`. -/
instance dualNumberIsResidueAlgebra (k : Type u) [Field k] :
    IsResidueAlgebra k (DualNumber k) where
  isSurjective' := by
    intro x
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
    refine ⟨z.fst, ?_⟩
    change IsLocalRing.residue (DualNumber k)
        (algebraMap k (DualNumber k) z.fst) =
      IsLocalRing.residue (DualNumber k) z
    apply Ideal.Quotient.eq.mpr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      TrivSqZeroExt.isUnit_iff_isUnit_fst]
    simp [TrivSqZeroExt.algebraMap_eq_inl']

namespace ProartinianCat

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The underlying type of the canonical residue-field object. -/
abbrev residueFieldType : Type u :=
  (residueField : ProartinianCat R)

/-- The dual numbers over the residue field, regarded as a local pro-Artinian `R`-algebra. -/
noncomputable def dualNumber [Finite (ResidueField R)] : ProartinianCat R where
  carrier := DualNumber (residueFieldType R)
  topologicalSpace := dualNumberTopology (residueFieldType R)
  isLocalProartinianAlgebra := by
    let k := residueFieldType R
    letI : Finite k := inferInstanceAs (Finite (ResidueField R))
    letI : Finite (DualNumber k) := inferInstanceAs (Finite (k × k))
    letI : IsArtinianRing (DualNumber k) := isArtinian_of_finite
    have hcomp : (algebraMap k (DualNumber k)).comp (algebraMap R k) =
        algebraMap R (DualNumber k) := by
      rfl
    letI : IsLocalHom (algebraMap R (DualNumber k)) := hcomp ▸
      inferInstanceAs (IsLocalHom
        ((algebraMap k (DualNumber k)).comp (algebraMap R k)))
    letI : IsResidueAlgebra R (DualNumber k) := ⟨by
      intro x
      obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective x
      obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective z.fst
      refine ⟨r, ?_⟩
      change IsLocalRing.residue (DualNumber k)
          (algebraMap R (DualNumber k) r) =
        IsLocalRing.residue (DualNumber k) z
      apply Ideal.Quotient.eq.mpr
      have hRk : algebraMap R k r = z.fst := by
        change IsLocalRing.residue R r = z.fst
        exact hr
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        TrivSqZeroExt.isUnit_iff_isUnit_fst]
      simp [TrivSqZeroExt.algebraMap_eq_inl', hRk]⟩
    exact ⟨⟩

/-- The projection `k[ε] → k` as a morphism of pro-Artinian `R`-algebras. -/
noncomputable def dualNumberToResidueField [Finite (ResidueField R)] :
    dualNumber R ⟶ residueField where
  hom := by
    letI : DiscreteTopology (dualNumber R) := by
      change DiscreteTopology (DualNumber (residueFieldType R))
      infer_instance
    exact ⟨TrivSqZeroExt.fstHom R (residueFieldType R)
      (residueFieldType R), continuous_of_discreteTopology⟩

@[simp]
lemma dualNumberToResidueField_apply [Finite (ResidueField R)]
    (z : dualNumber R) :
    (dualNumberToResidueField R).hom z =
      TrivSqZeroExt.fst (R := residueFieldType R) z :=
  rfl

/-- The explicit first-coefficient projection is the canonical map to the residue field. -/
lemma dualNumberToResidueField_eq_toResidueField [Finite (ResidueField R)] :
    dualNumberToResidueField R = toResidueField (dualNumber R) :=
  Subsingleton.elim _ _

end ProartinianCat

end Deformation
