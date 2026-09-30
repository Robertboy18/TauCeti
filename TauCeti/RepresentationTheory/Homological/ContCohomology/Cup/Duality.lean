/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.ConnectingMap
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Product
public import TauCeti.Topology.Algebra.GroupAction.InternalHom

import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Evaluation cups for finite discrete modules

For a finite discrete `G`-module `M` and a discrete module `N`, evaluation is an equivariant
biadditive pairing from `InternalHom G M N` and `M` to `N`. The three low-degree cup shapes of
total degree two give pairings from `Hⁱ(G, InternalHom G M N)` and `H²⁻ⁱ(G, M)` to `H²(G, N)`.
These are the underlying cohomological pairings used in duality statements.

The cochain formulas below fix the order of the two inputs: the internal hom is always the first
factor, so in degree `(1,1)` the evaluation is `a(g) (g • b(h))`.

The three pairings are compatible with the maps of coefficients in two ways, which together say
that they form a morphism of `δ`-functors (Serre, exposé 252, §9.1, following Tate). First, they are
**natural in the module**: a `G`-map `f : M →+[G] M'` and its dual `InternalHom.precomp G f` are
adjoint, `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩` in every shape. Second, they are **compatible with the connecting
maps** of a short exact sequence `0 → A → B → C → 0` of modules killed by a prime and of its dual
sequence `0 → C' → B' → A' → 0`: the connecting map of the dual sequence, paired against a class of
the original one, is the connecting map of the original sequence paired against the dual class, with
the Leibniz sign `(-1)^(p+1)` of the degree `p` of the dual class. These are the identities that let
the duality maps `Hⁱ(G, M) → Hom(H²⁻ⁱ(G, M'), H²(G, N))` be compared along the long exact sequences
of `M` and of `M'`, one short exact sequence at a time.

## Main statements

* `TauCeti.ContCohomology.explicitDualityPairing02`, `explicitDualityPairing11` and
  `explicitDualityPairing20`, with their cochain formulas `explicitDualityPairing02_mk`,
  `explicitDualityPairing11_mk` and `explicitDualityPairing20_mk`.
* `TauCeti.ContCohomology.explicitDualityPairing02_explicitCoeff2`,
  `explicitDualityPairing11_explicitCoeff1` and `explicitDualityPairing20_explicitCoeff0`:
  **naturality in the module**, `⟨φ, f_* b⟩ = ⟨f^* φ, b⟩`, one identity per shape.
* `TauCeti.ContCohomology.explicitDualityPairing11_explicitDelta0_dual` and
  `explicitDualityPairing20_explicitDelta1_dual`: **compatibility with the connecting maps** of a
  short exact sequence and of its dual sequence, `⟨δ x, y⟩ = (-1)^(p+1) ⟨x, δ y⟩`, in the two shapes
  of total degree two.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.1: Tate's duality argument, in which the evaluation pairings are
  compared along the long exact sequences of a finite module and of its dual.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.4.2), (1.4.3)
  and (1.4.5): naturality of the cup product in the coefficients and its compatibility with the
  connecting homomorphisms.
* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., I §0, the cup-product properties
  (0.1.1)-(0.1.6).
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uM' uN uA uB uC

section ZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H⁰(G, InternalHom G M N) × H²(G, M)`. -/
noncomputable def explicitDualityPairing02 :
    H0 G (InternalHom G M N) →+ H2 G M →+ H2 G N :=
  explicitCup02 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- On cocycles, the `(0,2)` evaluation cup evaluates the invariant homomorphism pointwise. -/
@[simp]
theorem explicitDualityPairing02_mk (a : H0 G (InternalHom G M N)) (b : Z2 G M) :
    explicitDualityPairing02 G M N a (b : H2 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G (a : InternalHom G M N) ((b : G × G → M) q),
        cup02_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing02] using
    explicitCup02_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end ZeroTwo

section OneOneAndTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- Evaluation on `H¹(G, InternalHom G M N) × H¹(G, M)`. -/
noncomputable def explicitDualityPairing11 :
    H1 G (InternalHom G M N) →+ H1 G M →+ H2 G N :=
  explicitCup11 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- Evaluation on `H²(G, InternalHom G M N) × H⁰(G, M)`. -/
noncomputable def explicitDualityPairing20 :
    H2 G (InternalHom G M N) →+ H0 G M →+ H2 G N :=
  explicitCup20 G (InternalHom G M N) M N (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G))

/-- On cocycles, the `(1,1)` evaluation cup applies the first cocycle to the translate of the
second. -/
@[simp]
theorem explicitDualityPairing11_mk (a : Z1 G (InternalHom G M N)) (b : Z1 G M) :
    explicitDualityPairing11 G M N (a : H1 G (InternalHom G M N)) (b : H1 G M) =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G → InternalHom G M N) q.1)
          (q.1 • (b : G → M) q.2),
        cup11_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b.2⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing11] using
    explicitCup11_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- On cocycles, the `(2,0)` evaluation cup evaluates at an invariant element of `M`. -/
@[simp]
theorem explicitDualityPairing20_mk (a : Z2 G (InternalHom G M N)) (b : H0 G M) :
    explicitDualityPairing20 G M N (a : H2 G (InternalHom G M N)) b =
      ((⟨fun q : G × G => InternalHom.evalPairing G ((a : G × G → InternalHom G M N) q)
          ((q.1 * q.2) • (b : M)),
        cup20_mem_Z2 G (InternalHom G M N) M N (InternalHom.evalPairing G)
          continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a.2 b⟩ :
        Z2 G N) : H2 G N) := by
  simpa only [explicitDualityPairing20] using
    explicitCup20_mk G (InternalHom G M N) M N (InternalHom.evalPairing G)
      continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end OneOneAndTwoZero

/-! ### Naturality in the module

For a `G`-map `f : M →+[G] M'` the dual map is precomposition,
`f^* = InternalHom.precomp G f : InternalHom G M' N →+[G] InternalHom G M N`, and the two evaluation
pairings are intertwined by `(f^* φ) m = φ (f m)`. On cohomology this is the adjunction
`⟨φ, f_* b⟩ = ⟨f^* φ, b⟩`, one identity per shape. Each follows from the naturality of the cup
product in the pairing, applied twice: once from the mixed pairing `(φ, m) ↦ φ (f m)` of
`InternalHom G M' N` with `M` to the evaluation pairing of `M'`, along `(id, f)`, and once from the
mixed pairing to the evaluation pairing of `M`, along `(f^*, id)`. -/

section NaturalityInModule

-- The identities below are deliberately not `simp` lemmas: neither side is a normal form, as each
-- moves the coefficient map from one factor of the pairing to the other.

variable {G : Type uG} [Group G] {M : Type uM} [AddCommGroup M] [DistribMulAction G M]
  {M' : Type uM'} [AddCommGroup M'] [DistribMulAction G M']
  {N : Type uN} [AddCommGroup N] [DistribMulAction G N] (f : M →+[G] M')

/-- The mixed pairing `(φ, m) ↦ φ (f m)` of `InternalHom G M' N` with `M`, through which the
evaluation pairings of `M` and of `M'` are compared. -/
private def evalPairingComp : InternalHom G M' N →+ M →+ N :=
  (InternalHom.evalPairing G).comp (InternalHom.precomp G f (N := N)).toAddMonoidHom

private theorem evalPairingComp_apply (φ : InternalHom G M' N) (m : M) :
    evalPairingComp f φ m = InternalHom.evalPairing G φ (f m) :=
  InternalHom.evalPairing_precomp f φ m

private theorem evalPairingComp_equivariant (g : G) (φ : InternalHom G M' N) (m : M) :
    evalPairingComp f (g • φ) (g • m) = g • evalPairingComp f φ m := by
  rw [evalPairingComp_apply, evalPairingComp_apply, map_smul f,
    InternalHom.evalPairing_equivariant]

variable [TopologicalSpace G] [ContinuousMul G] [TopologicalSpace M] [DiscreteTopology M]
  [ContinuousSMul G M] [TopologicalSpace M'] [DiscreteTopology M'] [ContinuousSMul G M']
  [TopologicalSpace N] [DiscreteTopology N] [ContinuousSMul G N]

/-- **Naturality of the `(0,2)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`,
an invariant `φ` of `InternalHom G M' N` and a class `b ∈ H²(G, M)`, pairing `φ` with `f_* b`
is pairing the precomposed invariant `f^* φ` with `b`. -/
theorem explicitDualityPairing02_explicitCoeff2 (φ : H0 G (InternalHom G M' N)) (b : H2 G M) :
    explicitDualityPairing02 G M' N φ (explicitCoeff2 G M f continuous_of_discreteTopology b) =
      explicitDualityPairing02 G M N
        (explicitCoeff0 G (InternalHom G M' N) (InternalHom.precomp G f) φ) b := by
  have h₁ := explicitCoeff2_explicitCup02 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_of_discreteTopology continuous_id
    (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup02 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_id continuous_id
    (fun _ _ => rfl) φ b
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing02
  exact h₁.symm.trans h₂

end NaturalityInModule

section NaturalityInModuleFinite

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  {M' : Type uM'} [AddCommGroup M'] [TopologicalSpace M'] [DiscreteTopology M']
    [DistribMulAction G M'] [ContinuousSMul G M'] [Finite M']
  {N : Type uN} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (f : M →+[G] M')

/-- **Naturality of the `(1,1)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`
and classes `φ ∈ H¹(G, InternalHom G M' N)` and `b ∈ H¹(G, M)`, pairing `φ` with `f_* b` is
pairing the precomposed class `f^* φ` with `b`. -/
theorem explicitDualityPairing11_explicitCoeff1 (φ : H1 G (InternalHom G M' N)) (b : H1 G M) :
    explicitDualityPairing11 G M' N φ (explicitCoeff1 G M f continuous_of_discreteTopology b) =
      explicitDualityPairing11 G M N
        (explicitCoeff1 G (InternalHom G M' N) (InternalHom.precomp G f)
          continuous_of_discreteTopology φ) b := by
  have h₁ := explicitCoeff2_explicitCup11 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_id continuous_of_discreteTopology continuous_id
    (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup11 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id continuous_id (fun _ _ => rfl) φ b
  simp only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing11
  exact h₁.symm.trans h₂

/-- **Naturality of the `(2,0)` evaluation pairing in the module.** For a `G`-map `f : M →+[G] M'`,
a class `φ ∈ H²(G, InternalHom G M' N)` and an invariant `b` of `M`, pairing `φ` with `f b` is
pairing the precomposed class `f^* φ` with `b`. -/
theorem explicitDualityPairing20_explicitCoeff0 (φ : H2 G (InternalHom G M' N)) (b : H0 G M) :
    explicitDualityPairing20 G M' N φ (explicitCoeff0 G M f b) =
      explicitDualityPairing20 G M N
        (explicitCoeff2 G (InternalHom G M' N) (InternalHom.precomp G f)
          continuous_of_discreteTopology φ) b := by
  have h₁ := explicitCoeff2_explicitCup20 G (InternalHom G M' N) M N (InternalHom G M' N) M' N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DistribMulActionHom.id G) f
    (DistribMulActionHom.id G) continuous_id continuous_id (evalPairingComp_apply f) φ b
  have h₂ := explicitCoeff2_explicitCup20 G (InternalHom G M' N) M N (InternalHom G M N) M N
    (evalPairingComp f) continuous_of_discreteTopology (evalPairingComp_equivariant f)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (InternalHom.precomp G f)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id (fun _ _ => rfl) φ b
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  unfold explicitDualityPairing20
  exact h₁.symm.trans h₂

end NaturalityInModuleFinite

/-! ### Compatibility with the connecting maps of a short exact sequence and of its dual

Let `0 → A → B → C → 0` be a short exact sequence of finite discrete `G`-modules killed by a prime
`p`, and let `0 → C' → B' → A' → 0` be its dual sequence `DiscreteShortExact.dual`, where
`X' = InternalHom G X N`. The sub-object `C'` of the dual sequence pairs with the quotient `C` of
the original one, and the quotient `A'` pairs with the sub-object `A`, so the two sequences are a
compatibly paired pair in the sense of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/ConnectingMap.lean`, and the
adjointness identities there specialize to the evaluation pairings. -/

section ConnectingMaps

-- As in `Cup/ConnectingMap.lean`, these are not `simp` lemmas: the left-hand sides do not
-- determine the original sequence.

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction G A] [ContinuousSMul G A] [Finite A]
  {B : Type uB} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction G B] [ContinuousSMul G B] [Finite B]
  {C : Type uC} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction G C] [ContinuousSMul G C] [Finite C]
  (S : DiscreteShortExact G A B C)
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  {p : ℕ} [Fact p.Prime] (hB : ∀ b : B, p • b = 0)

omit [Finite A] in
/-- **The connecting maps `δ⁰` of the dual sequence and `δ¹` of the original sequence are
anti-adjoint under the evaluation pairings.** For an invariant `x` of `A' = InternalHom G A N` and
a class `y ∈ H¹(G, C)`, the `(1,1)` pairing of `δ⁰ x ∈ H¹(G, C')` with `y` is the negative of the
`(0,2)` pairing of `x` with `δ¹ y ∈ H²(G, A)`. -/
theorem explicitDualityPairing11_explicitDelta0_dual
    (x : H0 G (InternalHom G A N)) (y : H1 G C) :
    explicitDualityPairing11 G C N ((S.dual N hB).explicitDelta0 x) y =
      -explicitDualityPairing02 G A N x (S.explicitDelta1 y) :=
  explicitCup11_explicitDelta0_eq_neg_explicitCup02_explicitDelta1 (S.dual N hB) S
    (InternalHom.evalPairing G) (InternalHom.evalPairing G) (InternalHom.evalPairing G)
    (S.evalPairing_dual_incl N hB) (fun ψ a => (S.evalPairing_dual_proj N hB ψ a).symm)
    (InternalHom.evalPairing_equivariant (G := G)) x y

/-- **The connecting maps `δ¹` of the dual sequence and `δ⁰` of the original sequence are adjoint
under the evaluation pairings.** For a class `x ∈ H¹(G, A')`, `A' = InternalHom G A N`, and an
invariant `y` of `C`, the `(2,0)` pairing of `δ¹ x ∈ H²(G, C')` with `y` is the `(1,1)` pairing of
`x` with `δ⁰ y ∈ H¹(G, A)`; the Leibniz sign is `1` because `x` has degree one. -/
theorem explicitDualityPairing20_explicitDelta1_dual
    (x : H1 G (InternalHom G A N)) (y : H0 G C) :
    explicitDualityPairing20 G C N ((S.dual N hB).explicitDelta1 x) y =
      explicitDualityPairing11 G A N x (S.explicitDelta0 y) :=
  explicitCup20_explicitDelta1_eq_explicitCup11_explicitDelta0 (S.dual N hB) S
    (InternalHom.evalPairing G) (InternalHom.evalPairing G) (InternalHom.evalPairing G)
    (S.evalPairing_dual_incl N hB) (fun ψ a => (S.evalPairing_dual_proj N hB ψ a).symm)
    (InternalHom.evalPairing_equivariant (G := G)) x y

end ConnectingMaps

end TauCeti.ContCohomology
