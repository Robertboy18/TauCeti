/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.Root.Basis
public import TauCeti.Algebra.Lie.SpecialLinear.GraphAutomorphism
public import Mathlib.Data.Nat.Dist

/-!
# Signed root coordinates of the pinned type-A graph automorphism

The native graph map reverses the simple-coroot coordinates and reverses and swaps the
root indices. A root of height `h` acquires the sign `(-1) ^ (h - 1)`.
-/

public section

namespace TauCeti

open LieAlgebra.SpecialLinear

attribute [local instance 100] LieRing.ofAssociativeRing

variable (r : ℕ) (A : Type*) [CommRing A]

private theorem rootSign_rev (i j : Fin (r + 1)) :
    specialLinearRootSign r A j.rev i.rev = specialLinearRootSign r A i j := by
  have h : j.rev.val - i.rev.val = i.val - j.val := by
    simp only [Fin.val_rev]
    omega
  simp only [specialLinearRootSign_eq, Fin.rev_lt_rev, h]

private theorem graphSign_eq (i j : Fin (r + 1)) (hij : i ≠ j) :
    (-1 : A) ^ (i.val + j.val + 1) = (-1 : A) ^ (Nat.dist i.val j.val - 1) := by
  rw [neg_one_pow_eq_pow_mod_two (i.val + j.val + 1),
    neg_one_pow_eq_pow_mod_two (Nat.dist i.val j.val - 1)]
  congr 1
  have hne : i.val ≠ j.val := fun h ↦ hij (Fin.ext h)
  unfold Nat.dist
  omega

/-- Signed root vectors transform by reversed indices and the interval-height sign. -/
theorem typeASpecialLinearGraphAutomorphism_signedRoot
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    typeASpecialLinearGraphAutomorphism r A (specialLinearSignedRoot r A i j hij) =
      (-1 : A) ^ (Nat.dist i.val j.val - 1) •
        specialLinearSignedRoot r A j.rev i.rev (Fin.rev_injective.ne hij.symm) := by
  apply Subtype.ext
  rw [coe_typeASpecialLinearGraphAutomorphism, specialLinearSignedRoot_val,
    typeAGraphLieEquiv_single, SetLike.val_smul, specialLinearSignedRoot_val,
    Matrix.smul_single, smul_eq_mul, rootSign_rev, graphSign_eq r A i j hij]

/-- On the coroot part of the full basis, the graph map reverses the Dynkin node. -/
theorem typeASpecialLinearGraphAutomorphism_rootBasis_inl (i : Fin r) :
    typeASpecialLinearGraphAutomorphism r A (specialLinearRootBasis r A (.inl i)) =
      specialLinearRootBasis r A (.inl i.rev) := by
  simp only [specialLinearRootBasis_inl, specialLinearCorootBasis_apply,
    typeASpecialLinearGraphAutomorphism_coroot]

/-- The graph map reverses the simple-coroot coordinates of every trace-zero matrix. -/
theorem specialLinearRootEquiv_graph_inl (X : sl (Fin (r + 1)) A) (i : Fin r) :
    specialLinearRootEquiv r A (typeASpecialLinearGraphAutomorphism r A X) (.inl i.rev) =
      specialLinearRootEquiv r A X (.inl i) := by
  let f : sl (Fin (r + 1)) A →ₗ[A] A :=
    (LinearMap.proj (.inl i.rev)).comp ((specialLinearRootEquiv r A).toLinearMap.comp
      (typeASpecialLinearGraphAutomorphism r A).toLinearMap)
  let g : sl (Fin (r + 1)) A →ₗ[A] A :=
    (LinearMap.proj (.inl i)).comp (specialLinearRootEquiv r A).toLinearMap
  have h : f = g := by
    apply (specialLinearRootBasis r A).ext
    intro q
    -- Evaluate the coordinate projections and their linear-map compositions.
    change specialLinearRootEquiv r A
      (typeASpecialLinearGraphAutomorphism r A (specialLinearRootBasis r A q)) (.inl i.rev) =
        specialLinearRootEquiv r A (specialLinearRootBasis r A q) (.inl i)
    cases q with
    | inl j =>
      simp only [typeASpecialLinearGraphAutomorphism_rootBasis_inl,
        ← specialLinearRootBasis_repr, Module.Basis.repr_self, Finsupp.single_apply,
        Sum.inl.injEq, Fin.rev_inj]
    | inr p =>
      have hroot : typeASpecialLinearGraphAutomorphism r A
          (specialLinearRootBasis r A (.inr p)) =
          (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) •
            specialLinearRootBasis r A
              (.inr ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩) := by
        simp only [specialLinearRootBasis_inr, typeASpecialLinearGraphAutomorphism_signedRoot]
      rw [hroot, map_smul]
      simp only [Pi.smul_apply, ← specialLinearRootBasis_repr, Module.Basis.repr_self,
        Finsupp.single_apply, Sum.inr_ne_inl, ite_false, smul_zero]
  exact DFunLike.congr_fun h X

/-- The graph map permutes the signed root coordinates with the interval-height sign. -/
theorem specialLinearRootEquiv_graph_inr (X : sl (Fin (r + 1)) A)
    (p : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2}) :
    specialLinearRootEquiv r A (typeASpecialLinearGraphAutomorphism r A X)
        (.inr ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩) =
      (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) *
        specialLinearRootEquiv r A X (.inr p) := by
  let p' : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} :=
    ⟨(p.val.2.rev, p.val.1.rev), Fin.rev_injective.ne p.property.symm⟩
  let f : sl (Fin (r + 1)) A →ₗ[A] A :=
    (LinearMap.proj (.inr p')).comp ((specialLinearRootEquiv r A).toLinearMap.comp
      (typeASpecialLinearGraphAutomorphism r A).toLinearMap)
  let g : sl (Fin (r + 1)) A →ₗ[A] A :=
    (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) •
      (LinearMap.proj (.inr p)).comp (specialLinearRootEquiv r A).toLinearMap
  have h : f = g := by
    apply (specialLinearRootBasis r A).ext
    intro q
    -- Evaluate the coordinate projections, scalar action and linear-map compositions.
    change specialLinearRootEquiv r A
      (typeASpecialLinearGraphAutomorphism r A (specialLinearRootBasis r A q)) (.inr p') =
        (-1 : A) ^ (Nat.dist p.val.1.val p.val.2.val - 1) *
          specialLinearRootEquiv r A (specialLinearRootBasis r A q) (.inr p)
    cases q with
    | inl j =>
      simp only [typeASpecialLinearGraphAutomorphism_rootBasis_inl,
        ← specialLinearRootBasis_repr, Module.Basis.repr_self, Finsupp.single_apply,
        Sum.inl_ne_inr, ite_false, mul_zero]
    | inr q =>
      let q' : {p : Fin (r + 1) × Fin (r + 1) // p.1 ≠ p.2} :=
        ⟨(q.val.2.rev, q.val.1.rev), Fin.rev_injective.ne q.property.symm⟩
      have hroot : typeASpecialLinearGraphAutomorphism r A
          (specialLinearRootBasis r A (.inr q)) =
          (-1 : A) ^ (Nat.dist q.val.1.val q.val.2.val - 1) •
            specialLinearRootBasis r A (.inr q') := by
        simp only [q', specialLinearRootBasis_inr,
          typeASpecialLinearGraphAutomorphism_signedRoot]
      have heq : q' = p' ↔ q = p := by
        constructor
        · intro he
          apply Subtype.ext
          exact Prod.ext (Fin.rev_injective (congrArg (fun x ↦ x.val.2) he))
            (Fin.rev_injective (congrArg (fun x ↦ x.val.1) he))
        · rintro rfl
          rfl
      rw [hroot, map_smul]
      simp only [Pi.smul_apply, smul_eq_mul, ← specialLinearRootBasis_repr,
        Module.Basis.repr_self, Finsupp.single_apply, Sum.inr.injEq, heq]
      by_cases hqp : q = p
      · subst q
        simp
      · simp [hqp]
  exact DFunLike.congr_fun h X

end TauCeti
