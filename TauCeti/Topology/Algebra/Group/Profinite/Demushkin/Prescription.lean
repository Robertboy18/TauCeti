/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.ExplicitFunctoriality
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Cocycle
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.ZModTwist

/-!
# The prescription property of a character

Let `G` be a topological group and `χ : G →ₜ* ℤ_pˣ` a continuous character, with twisted
coefficient modules `I(χ)/pⁱ = TauCeti.ZModTwist χ i`, on which `G` acts by `g • x = χ(g) x`. The
equivariant reductions `I(χ)/pⁱ → I(χ)/pʲ` for `j ≤ i` induce maps on continuous cohomology.

A character has the **prescription property** when every reduction
`H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` is surjective: every continuous crossed homomorphism to
`I(χ)/p` lifts, modulo principal ones, to a continuous crossed homomorphism to `I(χ)/pⁱ`. This is
Labute's condition on the orientation of a Demushkin group: such a group has exactly one continuous
character with the prescription property, its canonical character (Labute, Thm 4). Here the
property is defined, against the explicit model of continuous cohomology, and proved for every
continuous character of a free pro-`p` group: on `F = freeProP p X` a continuous `1`-cocycle is
determined by its values on the generators and takes any prescribed values there, so lifting a
cocycle is lifting its values on the generators. `I(χ)/p` is `ZModTwist χ 1`, the module at
`i = 1`, with carrier `ZMod (p ^ 1)`.

## Main definitions

* `TauCeti.HasPrescriptionProperty`: surjectivity of every `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`.

## Main results

* `TauCeti.freeProP.hasPrescriptionProperty`: every continuous character of a free pro-`p` group
  has the prescription property.

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2
  and Theorem 4.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

universe u

open ContCohomology

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]

/-- **The prescription property** of a continuous character `χ : G →ₜ* ℤ_pˣ` (Labute's condition
on the orientation of a Demushkin group): every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)`, for
`i ≥ 1`, is surjective. In cocycle terms, every continuous crossed homomorphism `G → I(χ)/p` is,
modulo principal ones, the reduction of a continuous crossed homomorphism `G → I(χ)/pⁱ`. -/
def HasPrescriptionProperty (χ : G →ₜ* ℤ_[p]ˣ) : Prop :=
  ∀ (i : ℕ) (hi : 1 ≤ i),
    Function.Surjective
      (explicitCoeff1 G (ZModTwist χ i) (ZModTwist.reduce χ hi) continuous_of_discreteTopology)

/-- **Every continuous character of a free pro-`p` group has the prescription property.** A
continuous `1`-cocycle `F → I(χ)/p` is determined by its values on the generators, each of which
lifts to `I(χ)/pⁱ`, and a continuous `1`-cocycle `F → I(χ)/pⁱ` with those lifted values exists;
its reduction agrees with the given cocycle on the generators, hence everywhere. -/
theorem freeProP.hasPrescriptionProperty {X : Type u} (χ : freeProP p X →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ := by
  intro i hi y
  induction y using QuotientAddGroup.induction_on with
  | H c =>
    -- Lift the values of `c` on the generators from `I(χ)/p` to `I(χ)/pⁱ`.
    choose v hv using fun x : X ↦
      ZModTwist.reduce_surjective χ hi ((c : freeProP p X → ZModTwist χ 1) (freeProP.of x))
    obtain ⟨c', hc', hc'v⟩ :=
      freeProP.exists_mem_Z1_forall_apply_of_eq (ZModTwist.isProP_multiplicative χ i) v
    refine ⟨((⟨c', hc'⟩ : Z1 (freeProP p X) (ZModTwist χ i)) : H1 _ _), ?_⟩
    rw [explicitCoeff1_mk]
    congr 1
    -- The reduction of `c'` and `c` are continuous cocycles agreeing on the generators.
    refine Subtype.ext (freeProP.eq_of_mem_Z1_of_forall_of (Subtype.property _) c.2 fun x ↦ ?_)
    -- `cocyclesMap1_apply` is applied as a term rather than by `rw` or `simp`: the continuity
    -- hypothesis of `explicitCoeff1` is stated for the bundled `reduce χ hi`, while `cocyclesMap1`
    -- receives it for the underlying additive homomorphism, and the two coercions only agree at
    -- default transparency (as in `explicitCoeff1_eq_explicitMap1`).
    exact (cocyclesMap1_apply _ _ _ _ (ContinuousMonoidHom.id _)
      (ZModTwist.reduce χ hi : ZModTwist χ i →+ ZModTwist χ 1) _ _ ⟨c', hc'⟩ (freeProP.of x)).trans
      (by simp [hc'v, hv])

end TauCeti
