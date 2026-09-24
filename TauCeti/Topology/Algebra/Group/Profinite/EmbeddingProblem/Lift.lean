/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Topology.Compactness.InverseSystem

public import TauCeti.Topology.Algebra.Group.Profinite.EmbeddingProblem.Compatible
public import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# Continuous lifts from compatible finite-level solutions

A compatible family of `LevelSolution`s determines a continuous lift into the profinite
group `A`, with precisely the supplied quotient maps. This assembly requires no finite
generation or finite embedding-problem solvability assumption.

Topological finite generation and `HasPGroupSolutions` supply such a family when `A` is
pro-`p`, giving a continuous lift under those explicit hypotheses.
-/

public section

namespace TauCeti

universe u v w

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {A : Type v} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [CompactSpace A] [TotallyDisconnectedSpace A]
variable {B : Type w} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] [T2Space B]

/-- Assemble a compatible family of finite-level solutions into a continuous lift, retaining
its prescribed value in every open-normal quotient. -/
theorem exists_continuous_lift_of_compatible_levelSolutions
    (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B)
    (β : ∀ U, LevelSolution α hα f U)
    (hβ : ∀ ⦃V U : OpenNormalSubgroup A⦄ (hVU : V ≤ U),
      levelSolutionMap α hα f hVU (β V) = β U) :
    ∃ φ : G →ₜ* A, α.comp φ = f ∧ ∀ U : OpenNormalSubgroup A,
      (QuotientGroup.mk' U.toSubgroup).comp φ.toMonoidHom = (β U).1.toMonoidHom := by
  have hmaps : ∀ ⦃V U : OpenNormalSubgroup A⦄ (hVU : V ≤ U),
      (QuotientGroup.mapOfLE hVU).comp (β V).1.toMonoidHom = (β U).1.toMonoidHom := by
    intro V U hVU
    ext g
    simpa only [levelSolutionMap_apply, MonoidHom.comp_apply,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using
        congrArg (fun s : LevelSolution α hα f U ↦ s.1 g) (hβ hVU)
  obtain ⟨φ, hφ, _⟩ := existsUnique_monoidHom_mk'_comp_eq
    (fun U ↦ (β U).1.toMonoidHom) hmaps
  have hcont : Continuous φ := continuous_iff_forall_continuous_mk.mpr fun U ↦ by
    change Continuous ((QuotientGroup.mk' U.toSubgroup).comp φ)
    rw [hφ U]
    exact (β U).1.continuous
  refine ⟨⟨φ, hcont⟩, ?_, hφ⟩
  ext g
  change α (φ g) = f g
  obtain ⟨a, ha⟩ := hα (f g)
  -- The level equations put the discrepancy in every open-normal thickening of the closed kernel.
  have hker : IsClosed (α.toMonoidHom.ker : Set A) :=
    isClosed_singleton.preimage α.continuous
  have hmem : (φ g)⁻¹ * a ∈ α.toMonoidHom.ker := by
    rw [α.toMonoidHom.ker.eq_iInf_sup_openNormalSubgroup hker]
    refine Subgroup.mem_iInf.mpr fun U ↦ ?_
    have hquot : ((φ g : A) : A ⧸ U.toSubgroup) = (β U).1 g := by
      simpa only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using
        DFunLike.congr_fun (hφ U) g
    have hlevel := (β U).2 g
    rw [← hquot, levelMap_mk, ← ha] at hlevel
    have himage : (φ g)⁻¹ * a ∈
        (U.toSubgroup.map α.toMonoidHom).comap α.toMonoidHom := by
      simpa only [Subgroup.mem_comap, map_mul, map_inv, levelImage_toSubgroup,
        ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using QuotientGroup.eq.mp hlevel
    simpa only [Subgroup.comap_map_eq, sup_comm] using himage
  have heq : (α (φ g))⁻¹ * α a = 1 := by
    simpa only [MonoidHom.mem_ker, map_mul, map_inv,
      ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using hmem
  exact (inv_mul_eq_one.mp heq).trans ha

/-- A topologically finitely generated group with solutions to all finite `p`-kernel
embedding problems lifts continuously through every surjection from a profinite pro-`p` group. -/
theorem HasPGroupSolutions.exists_continuous_lift [IsTopologicalGroup G] {p : ℕ}
    (hG : HasPGroupSolutions p G) (hfg : IsTopologicallyFinitelyGenerated G)
    (hA : IsProP p A) (α : A →ₜ* B) (hα : Function.Surjective α) (f : G →ₜ* B) :
    ∃ φ : G →ₜ* A, α.comp φ = f := by
  have : ∀ U, Nonempty (LevelSolution α hα f U) :=
    fun U ↦ nonempty_levelSolution hG hA α hα f U
  have : ∀ U, Finite (LevelSolution α hα f U) :=
    fun U ↦ hfg.finite_levelSolution α hα f U
  obtain ⟨β, hβ⟩ := exists_forall_map_eq_of_codirected_of_finite
    (fun _ _ hVU ↦ levelSolutionMap α hα f hVU)
  obtain ⟨φ, hφ, _⟩ := exists_continuous_lift_of_compatible_levelSolutions α hα f β hβ
  exact ⟨φ, hφ⟩

end TauCeti
