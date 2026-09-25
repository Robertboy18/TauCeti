/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Extension
public import TauCeti.Topology.Algebra.GroupAction.TypeTags
public import TauCeti.Topology.Algebra.GroupExtension.FactorSet

/-!
# Continuous `1`-cocycles on a free pro-`p` group

Let `F = freeProP p X` be the free pro-`p` group on a type `X`, and let `M` be a profinite abelian
pro-`p` group with a continuous action of `F`. A continuous `1`-cocycle `c : F → M`, that is a
continuous crossed homomorphism `c (g * h) = g • c h + c g`, is the same thing as a continuous
homomorphic section `g ↦ ⟨c g, g⟩` of the semidirect product `M ⋊ F → F`. The semidirect product is
the extension attached to the trivial factor set, it is profinite and pro-`p`, and such an
extension of `F` has a continuous homomorphic section with any prescribed values on the generators
(`GroupExtension.exists_splitting_continuous_freeProP_forall_apply_of_eq`). Since a cocycle is
determined by its values on a topological generating set, this identifies the continuous
`1`-cocycles of `F` with the functions on the generators:

`Z¹(F, M) ≃+ (X → M)`, by evaluation at the generators (`TauCeti.freeProP.Z1Equiv`).

No finiteness of `X` is needed, and `M` need not be discrete: any profinite abelian pro-`p`
coefficient module with a continuous action is allowed, exactly as for the vanishing of `H²` in
`TauCeti.Topology.Algebra.Group.Profinite.Free.Cohomology`. The coefficient module is written
additively; the pro-`p` hypothesis is on `Multiplicative M`.

## Main results

* `TauCeti.freeProP.eq_of_mem_Z1_of_forall_of`: continuous `1`-cocycles on `F` agreeing on the
  generators are equal.
* `TauCeti.freeProP.exists_mem_Z1_forall_apply_of_eq`: every function on the generators extends to
  a continuous `1`-cocycle on `F`.
* `TauCeti.freeProP.Z1Equiv`: evaluation at the generators is an additive equivalence
  `Z¹(F, M) ≃+ (X → M)`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.4 and §4.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. III, §9.
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} {X : Type u}

namespace freeProP

variable {M : Type u} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction (freeProP p X) M] [ContinuousSMul (freeProP p X) M]

section Uniqueness

variable [T1Space M]

omit [ContinuousSMul (freeProP p X) M] in
/-- Two continuous `1`-cocycles on a free pro-`p` group that agree on the generators are equal. -/
theorem eq_of_mem_Z1_of_forall_of {c₁ c₂ : freeProP p X → M} (h₁ : c₁ ∈ Z1 (freeProP p X) M)
    (h₂ : c₂ ∈ Z1 (freeProP p X) M) (h : ∀ x : X, c₁ (of x) = c₂ (of x)) : c₁ = c₂ :=
  eq_of_mem_Z1_of_eqOn_of_topologicalClosure_closure_eq_top h₁ h₂
    (topologicalClosure_closure_range_of_eq_top p X) (by rintro _ ⟨x, rfl⟩; exact h x)

end Uniqueness

section Existence

variable [CompactSpace M] [TotallyDisconnectedSpace M]

/-- **Continuous `1`-cocycles on a free pro-`p` group take prescribed values on the generators.**
For `F = freeProP p X` and `M` a profinite abelian pro-`p` group with a continuous action of `F`,
every function `X → M` is the restriction to the generators of a continuous `1`-cocycle `F → M`.
The cocycle is read off a continuous homomorphic section `F → M ⋊ F` of the semidirect product,
which the universal property of `F` supplies with the prescribed values. -/
theorem exists_mem_Z1_forall_apply_of_eq (hM : IsProP p (Multiplicative M)) (v : X → M) :
    ∃ c ∈ Z1 (freeProP p X) M, ∀ x : X, c (of x) = v x := by
  -- The semidirect product `M ⋊ F` is the extension attached to the trivial factor set. It is
  -- profinite, and it has a continuous homomorphic section with the prescribed values on the
  -- generators because `M` and `F` are pro-`p`.
  have _ : IsTopologicalGroup (FactorSet.trivial (freeProP p X) (Multiplicative M)).Extension :=
    FactorSet.Extension.isTopologicalGroup FactorSet.continuous_trivial
  obtain ⟨s, hs, hsv⟩ :=
    GroupExtension.exists_splitting_continuous_freeProP_forall_apply_of_eq
      (FactorSet.trivial (freeProP p X) (Multiplicative M)).groupExtension
      (by rw [FactorSet.groupExtension_inl]; exact FactorSet.continuous_inl _)
      (by rw [FactorSet.groupExtension_rightHom]; exact FactorSet.continuous_rightHom _) hM
      (fun x ↦ ⟨Multiplicative.ofAdd (v x), of x⟩) fun x ↦ by
        rw [FactorSet.groupExtension_rightHom, FactorSet.rightHom_apply]
  have hright : ∀ g, (s g).right = g := fun g ↦ by
    have h := s.rightHom_splitting g
    rwa [FactorSet.groupExtension_rightHom, FactorSet.rightHom_apply] at h
  refine ⟨fun g ↦ Multiplicative.toAdd (s g).left, mem_Z1_iff.2 ⟨?_, fun g h ↦ ?_⟩, fun x ↦ ?_⟩
  · exact continuous_toAdd.comp (FactorSet.Extension.continuous_left.comp hs)
  · -- The cocycle identity is the `M`-component of `s (g * h) = s g * s h`.
    simp only [map_mul, FactorSet.Extension.mul_left, hright, FactorSet.trivial_apply, mul_one,
      toAdd_mul, Multiplicative.toAdd_smul]
    exact add_comm _ _
  · exact congrArg (fun z ↦ Multiplicative.toAdd z.left) (hsv x)

variable (hM : IsProP p (Multiplicative M))

/-- **Evaluation at the generators identifies the continuous `1`-cocycles of a free pro-`p` group
with the functions on the generators**, `Z¹(F, M) ≃+ (X → M)`. -/
noncomputable def Z1Equiv : Z1 (freeProP p X) M ≃+ (X → M) where
  toFun c x := (c : freeProP p X → M) (of x)
  invFun v := ⟨(exists_mem_Z1_forall_apply_of_eq hM v).choose,
    (exists_mem_Z1_forall_apply_of_eq hM v).choose_spec.1⟩
  left_inv c := Subtype.ext (eq_of_mem_Z1_of_forall_of
    (exists_mem_Z1_forall_apply_of_eq hM _).choose_spec.1 c.2
    (exists_mem_Z1_forall_apply_of_eq hM _).choose_spec.2)
  right_inv v := funext (exists_mem_Z1_forall_apply_of_eq hM v).choose_spec.2
  map_add' _ _ := rfl

@[simp]
theorem Z1Equiv_apply (c : Z1 (freeProP p X) M) (x : X) :
    Z1Equiv hM c x = (c : freeProP p X → M) (of x) :=
  (rfl)

@[simp]
theorem Z1Equiv_symm_apply_of (v : X → M) (x : X) :
    ((Z1Equiv hM).symm v : freeProP p X → M) (of x) = v x :=
  (exists_mem_Z1_forall_apply_of_eq hM v).choose_spec.2 x

end Existence

end freeProP

end TauCeti
