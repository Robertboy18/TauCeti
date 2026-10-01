/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiveLemma
public import TauCeti.Algebra.Module.ZMod.Extend
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact

/-!
# Tate's duality maps along a short exact sequence

Let `G` be a topological group, let `N` be a discrete `G`-module, and for a finite discrete
`G`-module `M` write `M' = InternalHom G M N` for its dual and
`αᵢ : Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, N))`, `i = 0, 1, 2`, for Tate's duality maps
(`TauCeti.ContCohomology.dualityMap0`, `dualityMap1`, `dualityMap2`). This file compares the
duality maps of the three terms of a short exact sequence `0 → A → B → C → 0` of finite discrete
`G`-modules killed by a prime `p`.

The long exact cohomology sequence of `S` and the `Hom(-, H²(G, N))`-dual of the long exact
sequence of the dual sequence `0 → C' → B' → A' → 0` form a ladder

```text
H⁰(A) → H⁰(B) → H⁰(C) → H¹(A) → H¹(B) → H¹(C) → H²(A) → H²(B) → H²(C)
  ↓α₀     ↓α₀     ↓α₀     ↓α₁     ↓α₁     ↓α₁     ↓α₂     ↓α₂     ↓α₂
H²(A')ᵛ → H²(B')ᵛ → H²(C')ᵛ → H¹(A')ᵛ → H¹(B')ᵛ → H¹(C')ᵛ → H⁰(A')ᵛ → H⁰(B')ᵛ → H⁰(C')ᵛ
```

whose squares commute, up to the Leibniz sign in the square at `δ⁰`, by the naturality of the
duality maps in the module (`dualityMap0_explicitCoeff0`, `dualityMap1_explicitCoeff1`,
`dualityMap2_explicitCoeff2`) and their compatibility with the connecting maps
(`DiscreteShortExact.dualityMap1_explicitDelta0`, `DiscreteShortExact.dualityMap2_explicitDelta1`).
The bottom row is exact because `Hom(-, T)` is exact on groups killed by `p`
(`Function.Exact.compHom'`). The four lemmas then give the dévissage steps of Tate's duality
argument (Serre's exposé, §9.1): from `α₀` surjective, `α₁` bijective and `α₂` injective on `A`
and on `C`, the same follows on `B`
(`DiscreteShortExact.dualityMap0_surjective`, `DiscreteShortExact.dualityMap1_injective`,
`DiscreteShortExact.dualityMap1_surjective`, `DiscreteShortExact.dualityMap2_injective`), and the
injectivity of `α₀` on `C` follows from that of `α₁` on `A` when `H⁰(G, B) → H⁰(G, C)` vanishes
(`DiscreteShortExact.dualityMap0_injective_of_explicitCoeff0_eq_zero`). Bijectivity of each
duality map transports along an isomorphism of modules
(`dualityMap0_bijective_of_bijective`, `dualityMap1_bijective_of_bijective`,
`dualityMap2_bijective_of_bijective`), which is how a base case stated for `ZMod p` applies to
every trivial module of order `p`.

## Main results

* `TauCeti.ContCohomology.dualityMap0_explicitCoeff0`, `dualityMap1_explicitCoeff1`,
  `dualityMap2_explicitCoeff2`: naturality of the duality maps in the module.
* `TauCeti.ContCohomology.DiscreteShortExact.dualityMap1_explicitDelta0`,
  `DiscreteShortExact.dualityMap2_explicitDelta1`: the duality maps against the connecting maps of
  a short exact sequence and of its dual.
* `TauCeti.ContCohomology.DiscreteShortExact.dualityMap0_surjective`,
  `DiscreteShortExact.dualityMap1_injective`, `DiscreteShortExact.dualityMap1_surjective`,
  `DiscreteShortExact.dualityMap2_injective`: the four lemmas along a short exact sequence.
* `TauCeti.ContCohomology.DiscreteShortExact.dualityMap0_injective_of_explicitCoeff0_eq_zero`:
  injectivity of `α₀` from a sequence whose map on invariants vanishes.
* `TauCeti.ContCohomology.dualityMap0_bijective_of_bijective`,
  `dualityMap1_bijective_of_bijective`, `dualityMap2_bijective_of_bijective`: transport of
  bijectivity along an isomorphism of modules.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uM' uN uA uB uC

section NaturalityInModule

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M'] [Finite M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (f : M →+[G] M')

/-- **Naturality of `α₀` in the module**: `α₀ (f_* x) b = α₀ x (f^* b)`. -/
theorem dualityMap0_explicitCoeff0 (x : H0 G M) (b : H2 G (InternalHom G M' N)) :
    dualityMap0 G M' N (explicitCoeff0 G M f x) b =
      dualityMap0 G M N x (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
        continuous_of_discreteTopology b) := by
  rw [dualityMap0_eq_explicitDualityPairing20, dualityMap0_eq_explicitDualityPairing20,
    explicitDualityPairing20_explicitCoeff0]

/-- **Naturality of `α₁` in the module**: `α₁ (f_* x) b = α₁ x (f^* b)`. -/
theorem dualityMap1_explicitCoeff1 (x : H1 G M) (b : H1 G (InternalHom G M' N)) :
    dualityMap1 G M' N (explicitCoeff1 G M f continuous_of_discreteTopology x) b =
      dualityMap1 G M N x (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
        continuous_of_discreteTopology b) := by
  rw [dualityMap1_eq_neg_explicitDualityPairing11, dualityMap1_eq_neg_explicitDualityPairing11,
    explicitDualityPairing11_explicitCoeff1]

omit [Finite M] [Finite M'] in
/-- **Naturality of `α₂` in the module**: `α₂ (f_* x) b = α₂ x (f^* b)`. -/
theorem dualityMap2_explicitCoeff2 (x : H2 G M) (b : H0 G (InternalHom G M' N)) :
    dualityMap2 G M' N (explicitCoeff2 G M f continuous_of_discreteTopology x) b =
      dualityMap2 G M N x (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f) b) := by
  rw [dualityMap2_eq_explicitDualityPairing02, dualityMap2_eq_explicitDualityPairing02,
    explicitDualityPairing02_explicitCoeff2]

end NaturalityInModule

section ConnectingMaps

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
  {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
  (S : DiscreteShortExact G A B C)
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime] (hB : ∀ b : B, p • b = 0)

/-- `α₁ (δ⁰ x) b = - α₀ x (δ¹ b)` for the connecting maps of `S` and of its dual sequence. -/
theorem DiscreteShortExact.dualityMap1_explicitDelta0 (x : H0 G C)
    (b : H1 G (InternalHom G A N)) :
    dualityMap1 G A N (S.explicitDelta0 x) b =
      -dualityMap0 G C N x ((S.dual N hB).explicitDelta1 b) := by
  rw [dualityMap1_eq_neg_explicitDualityPairing11, dualityMap0_eq_explicitDualityPairing20,
    explicitDualityPairing20_explicitDelta1_dual_eq_explicitDualityPairing11_explicitDelta0]

omit [Finite A] in
/-- `α₂ (δ¹ x) b = α₁ x (δ⁰ b)` for the connecting maps of `S` and of its dual sequence. -/
theorem DiscreteShortExact.dualityMap2_explicitDelta1 (x : H1 G C)
    (b : H0 G (InternalHom G A N)) :
    dualityMap2 G A N (S.explicitDelta1 x) b =
      dualityMap1 G C N x ((S.dual N hB).explicitDelta0 b) := by
  rw [dualityMap2_eq_explicitDualityPairing02, dualityMap1_eq_neg_explicitDualityPairing11,
    explicitDualityPairing11_explicitDelta0_dual_eq_neg_explicitDualityPairing02_explicitDelta1,
    neg_neg]

end ConnectingMaps

section FourLemma

/-! ### The four lemmas

The sign in the square at `δ⁰` is absorbed by negating the vertical map at the end of the
four-term ladder that contains it, which changes neither injectivity nor surjectivity. -/

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
  {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
  (S : DiscreteShortExact G A B C)
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime] (hB : ∀ b : B, p • b = 0)

include S hB

/-- **The first four lemma for `α₁`.** If `α₀(C)` is surjective and `α₁(A)`, `α₁(C)` are injective,
then `α₁(B)` is injective. -/
theorem DiscreteShortExact.dualityMap1_injective (h₀C : Function.Surjective (dualityMap0 G C N))
    (h₁A : Function.Injective (dualityMap1 G A N)) (h₁C : Function.Injective (dualityMap1 G C N)) :
    Function.Injective (dualityMap1 G B N) := by
  refine AddMonoidHom.injective_of_surjective_of_injective_of_injective S.explicitDelta0
    (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology)
    (S.dual N hB).explicitDelta1.compHom'
    (explicitCoeff1 G (InternalHom G B N) (S.dual N hB).projDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (explicitCoeff1 G (InternalHom G C N) (S.dual N hB).inclDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (-dualityMap0 G C N) (dualityMap1 G A N) (dualityMap1 G B N) (dualityMap1 G C N) ?_ ?_ ?_
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H1A.symm)
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H1B.symm)
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H1C.symm).compHom'
      (nsmul_H2_eq_zero (InternalHom.nsmul_eq_zero_of_domain (S.nsmul_eq_zero_right hB))))
    (fun y => by
      obtain ⟨x, hx⟩ := h₀C (-y)
      exact ⟨x, by rw [AddMonoidHom.neg_apply, hx]; exact neg_neg y⟩) h₁A h₁C
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, AddMonoidHom.compHom'_apply_apply]
    rw [S.dualityMap1_explicitDelta0 hB]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap1_explicitCoeff1, DiscreteShortExact.dual_projDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap1_explicitCoeff1, DiscreteShortExact.dual_inclDistribMulActionHom]

/-- **The second four lemma for `α₁`.** If `α₁(A)`, `α₁(C)` are surjective and `α₂(A)` is injective,
then `α₁(B)` is surjective. -/
theorem DiscreteShortExact.dualityMap1_surjective (h₁A : Function.Surjective (dualityMap1 G A N))
    (h₁C : Function.Surjective (dualityMap1 G C N)) (h₂A : Function.Injective (dualityMap2 G A N)) :
    Function.Surjective (dualityMap1 G B N) := by
  refine AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (explicitCoeff1 G A S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff1 G B S.projDistribMulActionHom continuous_of_discreteTopology) S.explicitDelta1
    (explicitCoeff1 G (InternalHom G B N) (S.dual N hB).projDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (explicitCoeff1 G (InternalHom G C N) (S.dual N hB).inclDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (S.dual N hB).explicitDelta0.compHom'
    (dualityMap1 G A N) (dualityMap1 G B N) (dualityMap1 G C N) (dualityMap2 G A N) ?_ ?_ ?_
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H1C.symm)
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H1B.symm).compHom'
      (nsmul_H1_eq_zero (InternalHom.nsmul_eq_zero_of_domain (S.nsmul_eq_zero_left hB))))
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H1A.symm).compHom'
      (nsmul_H1_eq_zero (InternalHom.nsmul_eq_zero_of_domain hB))) h₁A h₁C h₂A
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap1_explicitCoeff1, DiscreteShortExact.dual_projDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap1_explicitCoeff1, DiscreteShortExact.dual_inclDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [S.dualityMap2_explicitDelta1 hB]

/-- **The four lemma for `α₀`.** If `α₀(A)`, `α₀(C)` are surjective and `α₁(A)` is injective, then
`α₀(B)` is surjective. -/
theorem DiscreteShortExact.dualityMap0_surjective (h₀A : Function.Surjective (dualityMap0 G A N))
    (h₀C : Function.Surjective (dualityMap0 G C N)) (h₁A : Function.Injective (dualityMap1 G A N)) :
    Function.Surjective (dualityMap0 G B N) := by
  refine AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    (explicitCoeff0 G A S.inclDistribMulActionHom) (explicitCoeff0 G B S.projDistribMulActionHom)
    S.explicitDelta0
    (explicitCoeff2 G (InternalHom G B N) (S.dual N hB).projDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (explicitCoeff2 G (InternalHom G C N) (S.dual N hB).inclDistribMulActionHom
      continuous_of_discreteTopology).compHom'
    (S.dual N hB).explicitDelta1.compHom'
    (dualityMap0 G A N) (dualityMap0 G B N) (dualityMap0 G C N) (-dualityMap1 G A N) ?_ ?_ ?_
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H0C.symm)
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H2B.symm).compHom'
      (nsmul_H2_eq_zero (InternalHom.nsmul_eq_zero_of_domain (S.nsmul_eq_zero_left hB))))
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H2A.symm).compHom'
      (nsmul_H2_eq_zero (InternalHom.nsmul_eq_zero_of_domain hB))) h₀A h₀C
    (fun a a' h => h₁A (neg_inj.1 h))
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap0_explicitCoeff0, DiscreteShortExact.dual_projDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap0_explicitCoeff0, DiscreteShortExact.dual_inclDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.neg_apply, AddMonoidHom.compHom'_apply_apply]
    rw [S.dualityMap1_explicitDelta0 hB, neg_neg]

omit [Finite A] in
/-- **The four lemma for `α₂`.** If `α₁(C)` is surjective and `α₂(A)`, `α₂(C)` are injective, then
`α₂(B)` is injective. -/
theorem DiscreteShortExact.dualityMap2_injective (h₁C : Function.Surjective (dualityMap1 G C N))
    (h₂A : Function.Injective (dualityMap2 G A N)) (h₂C : Function.Injective (dualityMap2 G C N)) :
    Function.Injective (dualityMap2 G B N) := by
  refine AddMonoidHom.injective_of_surjective_of_injective_of_injective S.explicitDelta1
    (explicitCoeff2 G A S.inclDistribMulActionHom continuous_of_discreteTopology)
    (explicitCoeff2 G B S.projDistribMulActionHom continuous_of_discreteTopology)
    (S.dual N hB).explicitDelta0.compHom'
    (explicitCoeff0 G (InternalHom G B N) (S.dual N hB).projDistribMulActionHom).compHom'
    (explicitCoeff0 G (InternalHom G C N) (S.dual N hB).inclDistribMulActionHom).compHom'
    (dualityMap1 G C N) (dualityMap2 G A N) (dualityMap2 G B N) (dualityMap2 G C N) ?_ ?_ ?_
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H2A.symm)
    (AddMonoidHom.exact_iff.2 S.explicitLongExact_H2B.symm)
    ((AddMonoidHom.exact_iff.2 (S.dual N hB).explicitLongExact_H0C.symm).compHom'
      (nsmul_H1_eq_zero (InternalHom.nsmul_eq_zero_of_domain (S.nsmul_eq_zero_right hB))))
    h₁C h₂A h₂C
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [S.dualityMap2_explicitDelta1 hB]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap2_explicitCoeff2, DiscreteShortExact.dual_projDistribMulActionHom]
  · refine AddMonoidHom.ext fun x => AddMonoidHom.ext fun b => ?_
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.compHom'_apply_apply]
    rw [dualityMap2_explicitCoeff2, DiscreteShortExact.dual_inclDistribMulActionHom]

/-- **Injectivity of `α₀` from a co-effacing sequence.** If `H⁰(G, B) → H⁰(G, C)` is zero and
`α₁(A)` is injective, then `α₀(C)` is injective: a class of `H⁰(G, C)` killed by `α₀` has a
connecting image killed by `α₁`, hence zero, and `δ⁰` is injective on `H⁰(G, C)`. -/
theorem DiscreteShortExact.dualityMap0_injective_of_explicitCoeff0_eq_zero
    (h : explicitCoeff0 G B S.projDistribMulActionHom = 0)
    (h₁A : Function.Injective (dualityMap1 G A N)) : Function.Injective (dualityMap0 G C N) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hδ : S.explicitDelta0 x = 0 := by
    refine h₁A (AddMonoidHom.ext fun b => ?_)
    rw [S.dualityMap1_explicitDelta0 hB, hx]
    simp
  have hmem : x ∈ S.explicitDelta0.ker := hδ
  rw [← S.explicitLongExact_H0C] at hmem
  obtain ⟨y, rfl⟩ := hmem
  rw [h, AddMonoidHom.zero_apply]

end FourLemma

section Transport

/-! ### Transport along an isomorphism of modules

A bijective equivariant homomorphism `f : M →+[G] M'` induces bijections on cohomology and, through
its dual `f^*`, on the targets of the duality maps; the naturality squares then carry bijectivity
of each duality map from `M'` to `M`. -/

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime] (hM' : ∀ x : M', p • x = 0) {f : M →+[G] M'} (hf : Function.Bijective f)

/-- Precomposition with a bijective homomorphism is bijective on homomorphisms: it is the inverse
of Mathlib's `AddEquiv.addMonoidHomCongrLeft` along the equivalence the bijection defines. -/
private theorem compHom'_bijective {X X' T : Type*} [AddCommGroup X] [AddCommGroup X']
    [AddCommGroup T] {u : X →+ X'} (hu : Function.Bijective u) :
    Function.Bijective (u.compHom' : (X' →+ T) →+ X →+ T) := by
  have h : ⇑(u.compHom' : (X' →+ T) →+ X →+ T) =
      ⇑((AddEquiv.ofBijective u hu).symm.addMonoidHomCongrLeft (N := T)) := funext fun φ =>
    AddMonoidHom.ext fun x => by
      rw [AddEquiv.addMonoidHomCongrLeft_apply, AddEquiv.symm_symm]
      rfl
  rw [h]
  exact AddEquiv.bijective _

include hM' hf

/-- **Bijectivity of `α₀` transports along an isomorphism of modules killed by `p`.** -/
theorem dualityMap0_bijective_of_bijective [Finite M] [Finite M']
    (h : Function.Bijective (dualityMap0 G M' N)) : Function.Bijective (dualityMap0 G M N) := by
  have hu : Function.Bijective (explicitCoeff0 G M f) := explicitCoeff0_bijective G M hf
  have hw : Function.Bijective (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff2_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hM' hf)
  have hsq : ⇑(explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology).compHom' ∘ ⇑(dualityMap0 G M N) =
      ⇑(dualityMap0 G M' N) ∘ ⇑(explicitCoeff0 G M f) := funext fun x =>
    AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap0_explicitCoeff0 f x b).symm
  refine (Function.Bijective.of_comp_iff' (compHom'_bijective (T := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

/-- **Bijectivity of `α₁` transports along an isomorphism of modules killed by `p`.** -/
theorem dualityMap1_bijective_of_bijective [Finite M] [Finite M']
    (h : Function.Bijective (dualityMap1 G M' N)) : Function.Bijective (dualityMap1 G M N) := by
  have hu : Function.Bijective (explicitCoeff1 G M f continuous_of_discreteTopology) :=
    explicitCoeff1_bijective G M hf
  have hw : Function.Bijective (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology) :=
    explicitCoeff1_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hM' hf)
  have hsq : ⇑(explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
      continuous_of_discreteTopology).compHom' ∘ ⇑(dualityMap1 G M N) =
      ⇑(dualityMap1 G M' N) ∘ ⇑(explicitCoeff1 G M f continuous_of_discreteTopology) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap1_explicitCoeff1 f x b).symm
  refine (Function.Bijective.of_comp_iff' (compHom'_bijective (T := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

/-- **Bijectivity of `α₂` transports along an isomorphism of modules killed by `p`.** -/
theorem dualityMap2_bijective_of_bijective (h : Function.Bijective (dualityMap2 G M' N)) :
    Function.Bijective (dualityMap2 G M N) := by
  have hu : Function.Bijective (explicitCoeff2 G M f continuous_of_discreteTopology) :=
    explicitCoeff2_bijective G M hf
  have hw : Function.Bijective (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f)) :=
    explicitCoeff0_bijective G (InternalHom G M' N) (InternalHom.precomp_bijective (N := N) hM' hf)
  have hsq : ⇑(explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f)).compHom' ∘
      ⇑(dualityMap2 G M N) =
      ⇑(dualityMap2 G M' N) ∘ ⇑(explicitCoeff2 G M f continuous_of_discreteTopology) :=
    funext fun x => AddMonoidHom.ext fun b => by
      simp only [Function.comp_apply, AddMonoidHom.compHom'_apply_apply]
      exact (dualityMap2_explicitCoeff2 f x b).symm
  refine (Function.Bijective.of_comp_iff' (compHom'_bijective (T := H2 G N) hw) _).1 ?_
  rw [hsq]
  exact h.comp hu

end Transport

end TauCeti.ContCohomology
