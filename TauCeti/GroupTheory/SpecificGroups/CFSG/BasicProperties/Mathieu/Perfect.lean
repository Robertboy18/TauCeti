/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.GroupTheory.IsPerfect
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Mathieu
import Mathlib.Tactic.Abel

/-!
# Perfectness of three Mathieu presentations

The exact transcribed presentations of `M₁₁`, `M₁₂`, and `M₂₂` are perfect. Every
homomorphism to a commutative group kills both generators: the exponent-sum rows of the
defining relators span `ℤ²`. Applying this to the abelianization map proves perfectness.

These are basic properties for milestone P1 of
`TauCetiRoadmap/CFSGBasicProperties/README.md`. They do not establish finiteness, orders,
or simplicity of the presented groups.
-/

public section

namespace TauCeti.Sporadic.Mathieu

private theorem map_transcribed_eq_one {P : GroupPresentation} {G : Type*} [Group G]
    (f : P.Group →* G) :
    ∀ t ∈ P.transcribed, f (PresentedGroup.mk P.relatorSet t.toFreeGroup) = 1 := by
  intro t ht
  rw [PresentedGroup.one_of_mem ((P.mem_relatorSet_iff _).mpr ⟨t, ht, rfl⟩), map_one]

/-- Every homomorphism from the transcribed `M₁₁` presentation to a commutative group is trivial. -/
theorem m11_hom_eq_one {G : Type*} [CommGroup G] (f : m11Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m11Presentation_transcribed] at h
  simp only [List.forall_mem_cons,
    Relator.toFreeGroup_mul, Relator.toFreeGroup_inv, Relator.toFreeGroup_gen,
    Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  change b + 3 • (-a) + b + -a + 3 • b = 0 at h₁'
  change b + a + -b + -a + -b + -a + b + a + -b + a = 0 at h₂'
  have hr₁ : (-4 : ℤ) • a + 5 • b = 0 := by
    calc
      _ = b + 3 • (-a) + b + -a + 3 • b := by abel
      _ = 0 := h₁'
  have hr₂ : a - b = 0 := by
    calc
      _ = b + a + -b + -a + -b + -a + b + a + -b + a := by abel
      _ = 0 := h₂'
  have ha : a = 0 := by
    calc
      a = ((-4 : ℤ) • a + 5 • b) + 5 • (a - b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  have hb : b = 0 := by
    calc
      b = ((-4 : ℤ) • a + 5 • b) + 4 • (a - b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m11Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₁₁` presentation equals its commutator subgroup. -/
theorem m11_isPerfect : Group.IsPerfect m11Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m11_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₁₂` presentation to a commutative group is trivial. -/
theorem m12_hom_eq_one {G : Type*} [CommGroup G] (f : m12Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m12Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, h₃, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  have h₃' := congrArg Additive.ofMul h₃
  change 3 • (-b + a) = 0 at h₁'
  change 5 • a + 6 • b = 0 at h₂'
  change a + 2 • b + a + -b + 2 • a + b + 2 • a + 2 • b = 0 at h₃'
  have hr₁ : (3 : ℤ) • a - 3 • b = 0 := by
    calc
      _ = 3 • (-b + a) := by abel
      _ = 0 := h₁'
  have hr₃ : (6 : ℤ) • a + 4 • b = 0 := by
    calc
      _ = a + 2 • b + a + -b + 2 • a + b + 2 • a + 2 • b := by abel
      _ = 0 := h₃'
  -- Integer combinations (6, 11, -12) and (-5, -9, 10) recover the two generators.
  have ha : a = 0 := by
    calc
      a = 6 • ((3 : ℤ) • a - 3 • b) + 11 • (5 • a + 6 • b) -
          12 • ((6 : ℤ) • a + 4 • b) := by abel
      _ = 0 := by rw [hr₁, h₂', hr₃]; simp
  have hb : b = 0 := by
    calc
      b = -5 • ((3 : ℤ) • a - 3 • b) - 9 • (5 • a + 6 • b) +
          10 • ((6 : ℤ) • a + 4 • b) := by abel
      _ = 0 := by rw [hr₁, h₂', hr₃]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m12Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₁₂` presentation equals its commutator subgroup. -/
theorem m12_isPerfect : Group.IsPerfect m12Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m12_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

/-- Every homomorphism from the transcribed `M₂₂` presentation to a commutative group is trivial. -/
theorem m22_hom_eq_one {G : Type*} [CommGroup G] (f : m22Presentation.Group →* G) :
    f = 1 := by
  let a : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨0, by simp [GroupPresentation.generatorCount]⟩))
  let b : Additive G := Additive.ofMul
    (f (PresentedGroup.of ⟨1, by simp [GroupPresentation.generatorCount]⟩))
  have h := map_transcribed_eq_one f
  rw [m22Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨h₁, h₂, _⟩ := h
  have h₁' := congrArg Additive.ofMul h₁
  have h₂' := congrArg Additive.ofMul h₂
  change 4 • a + b + -a + b + -a + b = 0 at h₁'
  change 2 • a + b + -a + -b + a + 2 • b + -a + -b = 0 at h₂'
  have hr₁ : (2 : ℤ) • a + 3 • b = 0 := by
    calc
      _ = 4 • a + b + -a + b + -a + b := by abel
      _ = 0 := h₁'
  have hr₂ : a + b = 0 := by
    calc
      _ = 2 • a + b + -a + -b + a + 2 • b + -a + -b := by abel
      _ = 0 := h₂'
  -- The first two relators suffice; the relation b¹¹ = 1 is not needed here.
  have ha : a = 0 := by
    calc
      a = -((2 : ℤ) • a + 3 • b) + 3 • (a + b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  have hb : b = 0 := by
    calc
      b = ((2 : ℤ) • a + 3 • b) - 2 • (a + b) := by abel
      _ = 0 := by rw [hr₁, hr₂]; simp
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m22Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have : i = ⟨0, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact ha
  · have : i = ⟨1, by simp [GroupPresentation.generatorCount]⟩ := Fin.ext hi
    subst i
    exact hb

/-- The exact transcribed `M₂₂` presentation equals its commutator subgroup. -/
theorem m22_isPerfect : Group.IsPerfect m22Presentation.Group := by
  constructor
  rw [← Abelianization.ker_of, m22_hom_eq_one Abelianization.of]
  exact MonoidHom.ker_one

end TauCeti.Sporadic.Mathieu
