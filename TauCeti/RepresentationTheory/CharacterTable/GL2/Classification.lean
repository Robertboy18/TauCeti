/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.GL2Linear`, `TauCeti.GL2SteinbergTwist`, their values and their irreducibility.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Boundary
-- `TauCeti.GL2PrincipalSeries`: irreducibility and the parametrisation by unordered pairs.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.Parameters
-- The values of the principal series at the four normal forms.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.PrincipalSeries.CharacterValues
-- `TauCeti.GL2CuspidalVirtualCharacter`, its values and its irreducibility.
public import TauCeti.RepresentationTheory.CharacterTable.GL2.Cuspidal.Irreducible
-- Non-public: `TauCeti.card_conjClasses_GL2` counts the conjugacy classes of `GL₂(𝔽_q)`.
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.ConjugacyClasses
-- Non-public: `FDRep.nonempty_iso_of_character_eq` recovers an isomorphism from a character
-- identity.
import TauCeti.RepresentationTheory.CharacterTable.Determined
-- Non-public: the character group of a finite commutative group is a `Fintype` of the same
-- cardinality, by Mathlib's duality for finite abelian groups.
import TauCeti.GroupTheory.FiniteAbelian.CharacterOrthogonality
-- Non-public: `ℂ`, being algebraically closed, has enough roots of unity of every order.
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- Non-public: at most `n - 1` characters of a finite cyclic group are fixed by the `n`-th power
-- map.
import TauCeti.GroupTheory.SpecificGroups.Cyclic.Dual

/-!
# The irreducible characters of `GL₂(𝔽_q)`

Let `F` be a finite field with `q` elements and `E/F` a degree-`2` extension. This file proves
that the four families of irreducible characters of `GL₂(F)` constructed in the surrounding files
exhaust the irreducible characters of `GL₂(F)`:

* the `q - 1` **linear** characters `α ∘ det` (`TauCeti.GL2Linear`), of degree `1`;
* the `q - 1` **Steinberg twists** `(α ∘ det) ⊗ St` (`TauCeti.GL2SteinbergTwist`), of degree `q`;
* the **principal series** `Ind_B^{GL₂}(α ⊗ β)` with `α ≠ β` (`TauCeti.GL2PrincipalSeries`), of
  degree `q + 1`, parametrised by the unordered pairs `{α, β}`;
* the **cuspidal** characters attached to the characters `θ` of `Eˣ` with `θ^q ≠ θ`
  (`TauCeti.GL2CuspidalVirtualCharacter`), of degree `q - 1`, parametrised by the orbits
  `{θ, θ^q}`.

The proof is a count. The four families are pairwise disjoint, since their members differ in
degree or in their value at the unipotent Jordan block `!![1, 1; 0, 1]`, and the within-family
identifications (`TauCeti.GL2Linear_character_injective`,
`TauCeti.GL2SteinbergTwist_character_injective`, `TauCeti.nonempty_iso_GL2PrincipalSeries_iff`
and `TauCeti.GL2CuspidalVirtualCharacter_eq_iff`) bound the four families from below by
`q - 1`, `q - 1`, `½ (q - 1) (q - 2)` and `½ q (q - 1)`, whose sum is `q² - 1`. That is the
number of conjugacy classes of `GL₂(F)` (`TauCeti.card_conjClasses_GL2`), hence the number of
irreducible characters (`TauCeti.card_irreducibleCharacters`), so nothing is missing.

The cuspidal count uses that at most `q - 1` characters of `Eˣ` are fixed by `θ ↦ θ^q`
(`IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le`, as `Eˣ` is cyclic), and that the character
group of `Eˣ` has order `q² - 1`, by Mathlib's duality for finite abelian groups.

## Main results

* `TauCeti.character_GL2Linear_mem_irreducibleCharacters`,
  `TauCeti.character_GL2SteinbergTwist_mem_irreducibleCharacters` and
  `TauCeti.character_GL2PrincipalSeries_mem_irreducibleCharacters`: the three induced families are
  irreducible characters (the cuspidal one is
  `TauCeti.GL2CuspidalVirtualCharacter_mem_irreducibleCharacters`).
* `TauCeti.character_GL2Linear_ne_character_GL2SteinbergTwist` and its five companions: the four
  families are pairwise disjoint.
* `TauCeti.irreducibleCharacters_GL2_eq_union`: **the irreducible characters of `GL₂(F)` are
  exactly the linear, Steinberg-twist, principal-series and cuspidal characters.**

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, GTM 129, §5.2.
* I. Piatetski-Shapiro, *Complex Representations of `GL(2, K)` for Finite Fields `K`*,
  Contemporary Mathematics 16, AMS (1983), §§4–5.
-/

public section

open CategoryTheory Matrix

namespace TauCeti

universe u

/-! ### The four families are irreducible characters -/

section Membership

/-- **The linear characters `α ∘ det` are irreducible characters of `GL₂(F)`.** -/
theorem character_GL2Linear_mem_irreducibleCharacters (F : Type u) [Field F] [Finite F]
    (α : Fˣ →* ℂˣ) :
    (GL2Linear F α).character ∈ irreducibleCharacters ℂ (GL (Fin 2) F) := by
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Representation.IsIrreducible (GL2Linear F α).ρ :=
    Representation.isIrreducible_of_finrank_eq_one _ (finrank_GL2Linear α)
  exact character_mem_irreducibleCharacters (GL2Linear F α).ρ

variable (F : Type) [Field F] [Fintype F]

/-- **The Steinberg twists are irreducible characters of `GL₂(F)`.** The universe restriction on
`F` is inherited from `TauCeti.simple_GL2SteinbergTwist`. -/
theorem character_GL2SteinbergTwist_mem_irreducibleCharacters (α : Fˣ →* ℂˣ) :
    (GL2SteinbergTwist F α).character ∈ irreducibleCharacters ℂ (GL (Fin 2) F) := by
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have := simple_GL2SteinbergTwist F α
  exact FDRep.character_mem_irreducibleCharacters (GL2SteinbergTwist F α)

/-- **The principal series with `α ≠ β` are irreducible characters of `GL₂(F)`.** The universe
restriction on `F` is inherited from `TauCeti.simple_GL2PrincipalSeries_iff`. -/
theorem character_GL2PrincipalSeries_mem_irreducibleCharacters {α β : Fˣ →* ℂˣ} (hαβ : α ≠ β) :
    (GL2PrincipalSeries F α β).character ∈ irreducibleCharacters ℂ (GL (Fin 2) F) := by
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have := (simple_GL2PrincipalSeries_iff F α β).mpr hαβ
  exact FDRep.character_mem_irreducibleCharacters (GL2PrincipalSeries F α β)

end Membership

/-! ### The four families are pairwise disjoint

Two of the six comparisons are made at the unipotent Jordan block `!![1, 1; 0, 1]`, where the
linear characters take the value `1`, the Steinberg twists `0` and the cuspidal characters `-1`;
the other four are made at the identity, where the degrees `1`, `q`, `q + 1` and `q - 1` differ. -/

section Distinct

variable {F : Type u} [Field F] [Fintype F]

/-- A linear character is not a Steinberg twist: at the Jordan block they take the values `1`
and `0`. -/
theorem character_GL2Linear_ne_character_GL2SteinbergTwist (α β : Fˣ →* ℂˣ) :
    (GL2Linear F α).character ≠ (GL2SteinbergTwist F β).character := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2Linear_jordanGL, character_GL2SteinbergTwist_jordanGL β 1 one_ne_zero] at this
  simp at this

/-- A linear character is not a principal-series character: their degrees are `1` and `q + 1`. -/
theorem character_GL2Linear_ne_character_GL2PrincipalSeries (α β γ : Fˣ →* ℂˣ) :
    (GL2Linear F α).character ≠ (GL2PrincipalSeries F β γ).character := by
  intro h
  have h1 := congrFun h 1
  rw [FDRep.char_one, finrank_GL2Linear, character_one_GL2PrincipalSeries] at h1
  have := Fintype.card_pos (α := F)
  norm_cast at h1
  omega

/-- A Steinberg twist is not a principal-series character: their degrees are `q` and `q + 1`. -/
theorem character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries (α β γ : Fˣ →* ℂˣ) :
    (GL2SteinbergTwist F α).character ≠ (GL2PrincipalSeries F β γ).character := by
  intro h
  have := congrFun h 1
  rw [FDRep.char_one, finrank_GL2SteinbergTwist, character_one_GL2PrincipalSeries] at this
  norm_cast at this
  omega

variable {E : Type*} [Field E] [Algebra F E] (hE : Module.finrank F E = 2)

/-- A linear character is not a cuspidal character: at the Jordan block they take the values `1`
and `-1`. -/
theorem character_GL2Linear_ne_GL2CuspidalVirtualCharacter (α : Fˣ →* ℂˣ) (θ : Eˣ →* ℂˣ)
    {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (GL2Linear F α).character ≠ (GL2CuspidalVirtualCharacter F E hE θ ψ).1 := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2Linear_jordanGL,
    GL2CuspidalVirtualCharacter_apply_jordanGL hE θ hψ 1 one_ne_zero] at this
  norm_num at this

/-- A Steinberg twist is not a cuspidal character: at the Jordan block they take the values `0`
and `-1`. -/
theorem character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter (α : Fˣ →* ℂˣ)
    (θ : Eˣ →* ℂˣ) {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    (GL2SteinbergTwist F α).character ≠ (GL2CuspidalVirtualCharacter F E hE θ ψ).1 := by
  intro h
  have := congrFun h (jordanGL (1 : Fˣ) (1 : F))
  rw [character_GL2SteinbergTwist_jordanGL α 1 one_ne_zero,
    GL2CuspidalVirtualCharacter_apply_jordanGL hE θ hψ 1 one_ne_zero] at this
  norm_num at this

/-- A principal-series character is not a cuspidal character: their degrees are `q + 1` and
`q - 1`. -/
theorem character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter (α β : Fˣ →* ℂˣ)
    (θ : Eˣ →* ℂˣ) (ψ : AddChar F ℂ) :
    (GL2PrincipalSeries F α β).character ≠ (GL2CuspidalVirtualCharacter F E hE θ ψ).1 := by
  intro h
  have := congrFun h 1
  rw [character_one_GL2PrincipalSeries, GL2CuspidalVirtualCharacter_apply_one] at this
  have h2 : (2 : ℂ) = 0 := by linear_combination this
  norm_num at h2

end Distinct

/-! ### The classification -/

section Classification

variable (F : Type) [Field F] [Fintype F] (E : Type*) [Field E] [Algebra F E]
  (hE : Module.finrank F E = 2)

open Classical in
/-- Two principal-series parameters giving the same character agree up to the swap, so each
fibre of `(α, β) ↦ χ(Ind_B(α ⊗ β))` over the off-diagonal pairs has at most two elements. -/
private theorem card_filter_character_GL2PrincipalSeries_le [Fintype (Fˣ →* ℂˣ)]
    {f : GL (Fin 2) F → ℂ}
    (hf : f ∈ (Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag.image
      fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) :
    ((Finset.univ : Finset (Fˣ →* ℂˣ)).offDiag.filter
      fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) =>
        (GL2PrincipalSeries F p.1 p.2).character = f).card ≤ 2 := by
  classical
  obtain ⟨⟨α, β⟩, -, rfl⟩ := Finset.mem_image.mp hf
  refine (Finset.card_le_card ?_).trans (Finset.card_le_two (a := (α, β)) (b := (β, α)))
  intro p hp
  obtain ⟨-, hp⟩ := Finset.mem_filter.mp hp
  obtain ⟨e⟩ := FDRep.nonempty_iso_of_character_eq _ _ hp
  rcases (nonempty_iso_GL2PrincipalSeries_iff F).mp ⟨e⟩ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Finset.mem_insert.mpr (Or.inl (Prod.ext h1 h2))
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (Prod.ext h1 h2)))

open Classical in
/-- Two cuspidal parameters giving the same character lie in one orbit `{θ, θ^q}`, so each fibre
of `θ ↦ χ_θ` has at most two elements. -/
private theorem card_filter_GL2CuspidalVirtualCharacter_le {ψ : AddChar F ℂ} (hψ : ψ ≠ 1)
    (s : Finset (Eˣ →* ℂˣ))
    {f : GL (Fin 2) F → ℂ}
    (hf : f ∈ s.image fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E hE θ ψ).1) :
    (s.filter fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E hE θ ψ).1 = f).card ≤ 2 := by
  obtain ⟨θ₀, -, rfl⟩ := Finset.mem_image.mp hf
  refine (Finset.card_le_card ?_).trans
    (Finset.card_le_two (a := θ₀) (b := θ₀.comp (powMonoidHom (Fintype.card F))))
  intro θ hθ
  obtain ⟨-, hθ⟩ := Finset.mem_filter.mp hθ
  rcases (GL2CuspidalVirtualCharacter_eq_iff hE θ₀ θ hψ hψ).mp (Subtype.ext hθ).symm with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))

/-- **The irreducible characters of `GL₂(𝔽_q)`.** For a finite field `F` with `q` elements, a
degree-`2` extension `E/F` and a nontrivial additive character `ψ` of `F`, the irreducible
characters of `GL₂(F)` are exactly the linear characters `α ∘ det`, the Steinberg twists
`(α ∘ det) ⊗ St`, the principal series `Ind_B^{GL₂}(α ⊗ β)` with `α ≠ β`, and the cuspidal
characters attached to the characters `θ` of `Eˣ` with `θ^q ≠ θ`.

The four families are pairwise disjoint, and together they have at least `q² - 1` members, the
number of conjugacy classes of `GL₂(F)`; so they exhaust the irreducible characters. -/
theorem irreducibleCharacters_GL2_eq_union {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    irreducibleCharacters ℂ (GL (Fin 2) F) =
      Set.range (fun α : Fˣ →* ℂˣ => (GL2Linear F α).character) ∪
        Set.range (fun α : Fˣ →* ℂˣ => (GL2SteinbergTwist F α).character) ∪
        (fun p : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) => (GL2PrincipalSeries F p.1 p.2).character) ''
          {p | p.1 ≠ p.2} ∪
        (fun θ : Eˣ →* ℂˣ => (GL2CuspidalVirtualCharacter F E hE θ ψ).1) ''
          {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ} := by
  classical
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ (n := 1) hE
  have : Finite E := Module.finite_of_finite F
  let : Invertible (Nat.card (GL (Fin 2) F) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- the four families as finsets of functions on `GL₂(F)`
  set fL : (Fˣ →* ℂˣ) → (GL (Fin 2) F → ℂ) := fun α => (GL2Linear F α).character
  set fS : (Fˣ →* ℂˣ) → (GL (Fin 2) F → ℂ) := fun α => (GL2SteinbergTwist F α).character
  set fP : (Fˣ →* ℂˣ) × (Fˣ →* ℂˣ) → (GL (Fin 2) F → ℂ) :=
    fun p => (GL2PrincipalSeries F p.1 p.2).character
  set fC : (Eˣ →* ℂˣ) → (GL (Fin 2) F → ℂ) :=
    fun θ => (GL2CuspidalVirtualCharacter F E hE θ ψ).1
  set A : Finset (GL (Fin 2) F → ℂ) := Finset.univ.image fL with hA
  set B : Finset (GL (Fin 2) F → ℂ) := Finset.univ.image fS with hB
  set P : Finset (GL (Fin 2) F → ℂ) := Finset.univ.offDiag.image fP with hP
  set sC : Finset (Eˣ →* ℂˣ) :=
    Finset.univ.filter fun θ : Eˣ →* ℂˣ => ¬ θ.comp (powMonoidHom (Fintype.card F)) = θ with hsC
  set C : Finset (GL (Fin 2) F → ℂ) := sC.image fC with hC
  -- the right-hand side is the union of the four finsets
  have hT : (↑(A ∪ B ∪ P ∪ C) : Set (GL (Fin 2) F → ℂ)) =
      Set.range fL ∪ Set.range fS ∪ fP '' {p | p.1 ≠ p.2} ∪
        fC '' {θ | θ.comp (powMonoidHom (Fintype.card F)) ≠ θ} := by
    ext f
    simp [hA, hB, hP, hC, hsC, or_assoc]
  rw [← hT]
  symm
  refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
  · -- every member of the four families is an irreducible character
    intro f hf
    rw [Finset.mem_coe, Finset.mem_union, Finset.mem_union, Finset.mem_union] at hf
    rcases hf with ((hf | hf) | hf) | hf
    · obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hf
      exact character_GL2Linear_mem_irreducibleCharacters F α
    · obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hf
      exact character_GL2SteinbergTwist_mem_irreducibleCharacters F α
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hf
      exact character_GL2PrincipalSeries_mem_irreducibleCharacters F (Finset.mem_offDiag.mp hp).2.2
    · obtain ⟨θ, hθ, rfl⟩ := Finset.mem_image.mp hf
      exact GL2CuspidalVirtualCharacter_mem_irreducibleCharacters hE (Finset.mem_filter.mp hθ).2 hψ
  · -- the four families together have at least `q² - 1` members
    rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, card_irreducibleCharacters,
      card_conjClasses_GL2, Nat.card_eq_fintype_card]
    -- the character groups
    have hcardF : Fintype.card (Fˣ →* ℂˣ) = Fintype.card F - 1 := by
      have : NeZero (Monoid.exponent Fˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
      rw [← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity,
        Nat.card_units, Nat.card_eq_fintype_card]
    have hcardE : Fintype.card (Eˣ →* ℂˣ) = Fintype.card F ^ 2 - 1 := by
      have : NeZero (Monoid.exponent Eˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
      rw [← Nat.card_eq_fintype_card, CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity,
        Nat.card_congr (GL2NonSplitTorus.unitsEquiv hE).toEquiv, GL2NonSplitTorus.natCard_eq,
        Nat.card_eq_fintype_card]
    -- the four families are pairwise disjoint
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro f hfA hfB
      obtain ⟨α, -, rfl⟩ := Finset.mem_image.mp hfA
      obtain ⟨β, -, hβ⟩ := Finset.mem_image.mp hfB
      exact character_GL2Linear_ne_character_GL2SteinbergTwist α β hβ.symm
    have hABP : Disjoint (A ∪ B) P := by
      rw [Finset.disjoint_left]
      intro f hfAB hfP
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hfP
      rcases Finset.mem_union.mp hfAB with hfA | hfB
      · obtain ⟨α, -, hα⟩ := Finset.mem_image.mp hfA
        exact character_GL2Linear_ne_character_GL2PrincipalSeries α p.1 p.2 hα
      · obtain ⟨α, -, hα⟩ := Finset.mem_image.mp hfB
        exact character_GL2SteinbergTwist_ne_character_GL2PrincipalSeries α p.1 p.2 hα
    have hABPC : Disjoint (A ∪ B ∪ P) C := by
      rw [Finset.disjoint_left]
      intro f hfABP hfC
      obtain ⟨θ, -, rfl⟩ := Finset.mem_image.mp hfC
      rcases Finset.mem_union.mp hfABP with hfAB | hfP
      · rcases Finset.mem_union.mp hfAB with hfA | hfB
        · obtain ⟨α, -, hα⟩ := Finset.mem_image.mp hfA
          exact character_GL2Linear_ne_GL2CuspidalVirtualCharacter hE α θ hψ hα
        · obtain ⟨α, -, hα⟩ := Finset.mem_image.mp hfB
          exact character_GL2SteinbergTwist_ne_GL2CuspidalVirtualCharacter hE α θ hψ hα
      · obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hfP
        exact character_GL2PrincipalSeries_ne_GL2CuspidalVirtualCharacter hE p.1 p.2 θ ψ hp
    rw [Finset.card_union_of_disjoint hABPC, Finset.card_union_of_disjoint hABP,
      Finset.card_union_of_disjoint hAB]
    -- the sizes of the four families
    have hcardA : A.card = Fintype.card F - 1 := by
      rw [hA, Finset.card_image_of_injective _ GL2Linear_character_injective, Finset.card_univ,
        hcardF]
    have hcardB : B.card = Fintype.card F - 1 := by
      rw [hB, Finset.card_image_of_injective _ GL2SteinbergTwist_character_injective,
        Finset.card_univ, hcardF]
    have hcardP : (Fintype.card F - 1) * (Fintype.card F - 1) - (Fintype.card F - 1) ≤
        2 * P.card := by
      rw [← hcardF, ← Finset.card_univ, ← Finset.offDiag_card]
      exact Finset.card_le_mul_card_image _ 2 fun f hf =>
        card_filter_character_GL2PrincipalSeries_le F hf
    have hcardC : sC.card ≤ 2 * C.card :=
      Finset.card_le_mul_card_image _ 2 fun f hf =>
        card_filter_GL2CuspidalVirtualCharacter_le F E hE hψ sC hf
    have hsC' : (Finset.univ.filter fun θ : Eˣ →* ℂˣ =>
        θ.comp (powMonoidHom (Fintype.card F)) = θ).card + sC.card = Fintype.card F ^ 2 - 1 := by
      rw [hsC, Finset.card_filter_add_card_filter_not, Finset.card_univ, hcardE]
    have hfix : (Finset.univ.filter fun θ : Eˣ →* ℂˣ =>
        θ.comp (powMonoidHom (Fintype.card F)) = θ).card ≤ Fintype.card F - 1 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact IsCyclic.natCard_monoidHom_comp_powMonoidHom_eq_le Eˣ ℂ Fintype.one_lt_card
    -- the arithmetic: `2 (q - 1) + ½ (q - 1) (q - 2) + ½ q (q - 1) = q² - 1`
    obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 2 :=
      ⟨Fintype.card F - 2, by have := Fintype.one_lt_card (α := F); omega⟩
    rw [hm] at hcardA hcardB hcardP hsC' hfix ⊢
    have h1 : m + 2 - 1 = m + 1 := by omega
    rw [h1] at hcardA hcardB hcardP hfix
    have h2 : (m + 1) * (m + 1) - (m + 1) = (m + 1) * m := by
      rw [Nat.mul_succ, Nat.add_sub_cancel]
    have h3 : (m + 2) ^ 2 - 1 = m * m + 4 * m + 3 := by
      rw [show (m + 2) ^ 2 = m * m + 4 * m + 3 + 1 by ring, Nat.add_sub_cancel]
    rw [h2] at hcardP
    rw [h3] at hsC' ⊢
    nlinarith

end Classification

end TauCeti
