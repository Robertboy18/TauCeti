/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Simple
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11Recognition

/-!
# Simplicity of the M11 presentation

The faithful permutation representation gives a transitive action of degree 11.
The first presentation generator has order dividing 11 and normally generates the
whole group, as follows directly from the second defining relator. Since the group
has order 7,920, the criterion for actions of prime degree proves simplicity.

The finiteness and faithfulness inputs are proved from the original presentation
in the imported certificate modules. This establishes the M11 simplicity target
in the proposed CFSG basic-properties roadmap.
-/

public section

namespace TauCeti.Sporadic.Mathieu

private def genA : Fin m11Presentation.generatorCount :=
  ⟨0, by simp [GroupPresentation.generatorCount]⟩

private def genB : Fin m11Presentation.generatorCount :=
  ⟨1, by simp [GroupPresentation.generatorCount]⟩

private def a : m11Presentation.Group := PresentedGroup.of genA

private theorem hom_eq_one_of_a {G : Type*} [Group G] (f : m11Presentation.Group →* G)
    (ha : f a = 1) : f = 1 := by
  have h : ∀ t ∈ m11Presentation.transcribed,
      f (PresentedGroup.mk m11Presentation.relatorSet t.toFreeGroup) = 1 := by
    intro t ht
    rw [PresentedGroup.one_of_mem
      ((m11Presentation.mem_relatorSet_iff _).mpr ⟨t, ht, rfl⟩), map_one]
  rw [m11Presentation_transcribed] at h
  simp only [List.forall_mem_cons, Relator.toFreeGroup_mul, Relator.toFreeGroup_inv,
    Relator.toFreeGroup_gen, Relator.toFreeGroup_pow, map_mul, map_inv, map_pow] at h
  obtain ⟨_, hb, _⟩ := h
  change f (PresentedGroup.of genA) = 1 at ha
  change f (PresentedGroup.of genB) * f (PresentedGroup.of genA) *
    (f (PresentedGroup.of genB))⁻¹ * (f (PresentedGroup.of genA))⁻¹ *
    (f (PresentedGroup.of genB))⁻¹ * (f (PresentedGroup.of genA))⁻¹ *
    f (PresentedGroup.of genB) * f (PresentedGroup.of genA) *
    (f (PresentedGroup.of genB))⁻¹ * f (PresentedGroup.of genA) = 1 at hb
  simp only [ha, inv_one, mul_one, mul_inv_cancel, one_mul, inv_mul_cancel] at hb
  have hb' : f (PresentedGroup.of genB) = 1 := inv_eq_one.mp hb
  apply PresentedGroup.ext
  intro i
  have hi : i.val = 0 ∨ i.val = 1 := by
    have := i.isLt
    simp only [GroupPresentation.generatorCount, m11Presentation_generatorNames,
      List.length_cons, List.length_nil] at this
    omega
  rcases hi with hi | hi
  · have heq : i = genA := Fin.ext hi
    subst i
    exact ha
  · have heq : i = genB := Fin.ext hi
    subst i
    exact hb'

private theorem normalClosure_a : Subgroup.normalClosure ({a} : Set m11Presentation.Group) = ⊤ := by
  let N := Subgroup.normalClosure ({a} : Set m11Presentation.Group)
  have h : QuotientGroup.mk' N a = 1 :=
    (QuotientGroup.eq_one_iff a).mpr (Subgroup.subset_normalClosure (Set.mem_singleton a))
  have hf := hom_eq_one_of_a (QuotientGroup.mk' N) h
  have hk := MonoidHom.ker_eq_top_iff.mpr hf
  simpa only [QuotientGroup.ker_mk'] using hk

private theorem a_pow_eleven : a ^ 11 = 1 := by
  apply m11PermutationHom_injective
  rw [map_pow, map_one]
  change (m11PermutationHom (PresentedGroup.of genA)) ^ 11 = 1
  rw [m11PermutationHom_of]
  unfold m11GeneratorImages genA
  decide +kernel

private noncomputable instance : MulAction m11Presentation.Group (Fin 11) :=
  MulAction.compHom _ m11PermutationHom

private instance : FaithfulSMul m11Presentation.Group (Fin 11) where
  eq_of_smul_eq_smul h := m11PermutationHom_injective (Equiv.ext h)

private theorem a_orbit :
    ∀ x : Fin 11, ∃ i : Fin 11, (m11GeneratorImages genA ^ i.val) 0 = x := by
  unfold m11GeneratorImages genA
  decide +kernel

private instance : MulAction.IsPretransitive m11Presentation.Group (Fin 11) := by
  apply (MulAction.isPretransitive_iff_base (0 : Fin 11)).mpr
  intro x
  obtain ⟨i, hi⟩ := a_orbit x
  refine ⟨a ^ i.val, ?_⟩
  change m11PermutationHom (a ^ i.val) 0 = x
  rw [map_pow]
  change (m11PermutationHom (PresentedGroup.of genA) ^ i.val) 0 = x
  rwa [m11PermutationHom_of]

/-- The exact two-generator M11 presentation defines a simple group. -/
theorem m11_isSimple : IsSimpleGroup m11Presentation.Group := by
  have := m11_nontrivial
  apply isSimpleGroup_of_prime_degree_action (X := Fin 11)
    (by simpa only [Nat.card_fin] using (show Nat.Prime 11 by decide +kernel))
    (by rw [card_m11Presentation]; norm_num)
    a (by simpa using a_pow_eleven) normalClosure_a

end TauCeti.Sporadic.Mathieu
