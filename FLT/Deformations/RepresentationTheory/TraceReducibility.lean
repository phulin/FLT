/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.GaloisRep

/-!
# Trace criteria for reducibility in dimension two

This file develops the elementary linear-algebra part of the argument that a two-dimensional
representation satisfying `trace(g) = 1 + det(g)` is reducible.  The two lemmas below handle the
normal forms which arise from a nonidentity element having `1` as an eigenvalue.
-/

@[expose] public section

local notation3 "Γ" K:max => Field.absoluteGaloisGroup K

universe u

namespace GaloisRep

variable {K k : Type*} [Field K] [Field k] [TopologicalSpace k] [IsTopologicalRing k]

private abbrev e₀ : Fin 2 → k := Pi.single 0 1
private abbrev e₁ : Fin 2 → k := Pi.single 1 1

/-- If a framed two-dimensional representation satisfies `trace = 1 + det` and contains a
nonidentity unipotent in standard upper-triangular form, then the first coordinate line is
invariant and the representation is reducible. -/
theorem not_isIrreducible_of_unipotent_normal_form
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det)
    (g : Γ K) (a : k) (ha : a ≠ 0)
    (hg : (ρ.GL g).1 = !![1, a; 0, 1]) :
    ¬ ρ.IsIrreducible := by
  let M : Γ K → Matrix (Fin 2) (Fin 2) k := fun h ↦ (ρ.GL h).1
  have hMmul (x y : Γ K) : M (x * y) = M x * M y := by
    change LinearMap.toMatrix' (ρ (x * y)) =
      LinearMap.toMatrix' (ρ x) * LinearMap.toMatrix' (ρ y)
    rw [map_mul]
    exact LinearMap.toMatrixAlgEquiv'_mul _ _
  have h10 (h : Γ K) : M h 1 0 = 0 := by
    have hprod := hchar (g * h)
    have hh := hchar h
    rw [show (ρ.GL (g * h)).1 = M g * M h by simpa [M] using hMmul g h,
      show M g = !![1, a; 0, 1] by simpa [M] using hg,
      Matrix.trace_fin_two, Matrix.det_fin_two] at hprod
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two] at hh
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hprod
    have haz : a * M h 1 0 = 0 := by
      linear_combination hprod - hh
    exact (mul_eq_zero.mp haz).resolve_left ha
  apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
    (show Module.rank k (Fin 2 → k) = 2 by simp) e₀
  · simp [e₀]
  · intro h
    refine Submodule.mem_span_singleton.mpr ⟨M h 0 0, ?_⟩
    funext i
    fin_cases i
    · simp [M, e₀, FramedGaloisRep.GL_apply]
    · simpa [M, e₀, FramedGaloisRep.GL_apply] using (h10 h).symm

/-- If a framed two-dimensional representation satisfies `trace = 1 + det` and contains an
element in standard diagonal form with distinct eigenvalues `1` and `d`, then one of the two
coordinate lines is invariant and the representation is reducible. -/
theorem not_isIrreducible_of_diagonal_normal_form
    (ρ : FramedGaloisRep K k (Fin 2))
    (hchar : ∀ g : Γ K, (ρ.GL g).1.trace = 1 + (ρ.GL g).1.det)
    (g : Γ K) (d : k) (hd : d ≠ 1)
    (hg : (ρ.GL g).1 = !![1, 0; 0, d]) :
    ¬ ρ.IsIrreducible := by
  let M : Γ K → Matrix (Fin 2) (Fin 2) k := fun h ↦ (ρ.GL h).1
  have hMmul (x y : Γ K) : M (x * y) = M x * M y := by
    change LinearMap.toMatrix' (ρ (x * y)) =
      LinearMap.toMatrix' (ρ x) * LinearMap.toMatrix' (ρ y)
    rw [map_mul]
    exact LinearMap.toMatrixAlgEquiv'_mul _ _
  have h00 (h : Γ K) : M h 0 0 = 1 := by
    have hprod := hchar (g * h)
    have hh := hchar h
    rw [show (ρ.GL (g * h)).1 = M g * M h by simpa [M] using hMmul g h,
      show M g = !![1, 0; 0, d] by simpa [M] using hg,
      Matrix.trace_fin_two, Matrix.det_fin_two] at hprod
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two] at hh
    simp [Matrix.mul_apply, Fin.sum_univ_two] at hprod
    have hx : (1 - d) * (M h 0 0 - 1) = 0 := by
      linear_combination hprod - d * hh
    exact sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (sub_ne_zero.mpr hd.symm))
  have hoffdiag (h : Γ K) : M h 0 1 * M h 1 0 = 0 := by
    have hh := hchar h
    rw [show (ρ.GL h).1 = M h by rfl, Matrix.trace_fin_two, Matrix.det_fin_two,
      h00 h] at hh
    linear_combination hh
  by_cases hu : ∀ h : Γ K, M h 1 0 = 0
  · apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
      (show Module.rank k (Fin 2 → k) = 2 by simp) e₀
    · simp [e₀]
    · intro h
      refine Submodule.mem_span_singleton.mpr ⟨M h 0 0, ?_⟩
      funext i
      fin_cases i
      · simp [M, e₀, FramedGaloisRep.GL_apply]
      · simpa [M, e₀, FramedGaloisRep.GL_apply] using (hu h).symm
  · push_neg at hu
    obtain ⟨h₀, hh₀⟩ := hu
    have hh₀01 : M h₀ 0 1 = 0 :=
      (mul_eq_zero.mp (hoffdiag h₀)).resolve_right hh₀
    have h01 (h : Γ K) : M h 0 1 = 0 := by
      by_contra hh
      have hh10 : M h 1 0 = 0 :=
        (mul_eq_zero.mp (hoffdiag h)).resolve_left hh
      have hprod := hoffdiag (h₀ * h)
      rw [hMmul] at hprod
      simp only [Matrix.mul_apply, Fin.sum_univ_two, hh₀01, hh10, h00, mul_zero,
        zero_mul, add_zero, zero_add, one_mul] at hprod
      exact hh₀ (by simpa using (mul_eq_zero.mp hprod).resolve_left hh)
    apply GaloisRep.not_isIrreducible_of_invariant_line (K := K)
      (show Module.rank k (Fin 2 → k) = 2 by simp) e₁
    · simp [e₁]
    · intro h
      refine Submodule.mem_span_singleton.mpr ⟨M h 1 1, ?_⟩
      funext i
      fin_cases i
      · simpa [M, e₁, FramedGaloisRep.GL_apply] using (h01 h).symm
      · simp [M, e₁, FramedGaloisRep.GL_apply]

end GaloisRep
