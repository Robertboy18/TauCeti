/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Quotient

/-!
# Transitivity of the Herbrand functions and the upper numbering of a quotient

Let `M/K` be a finite Galois extension of nonarchimedean local fields with group `G`, and let
`L` be an intermediate field Galois over `K`, so that `H = Gal(M/L)` is normal in `G` and
restriction to `L` identifies `Gal(L/K)` with `G / H`. Herbrand's theorem
`(G/H)_{φ_{M/L}(u)} = G_u H / H` has a **counting form**, `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`,
because `H_u = H ∩ G_u`. Both `φ_{M/K}` and `φ_{L/K} ∘ φ_{M/L}` are affine on each interval
`[m, m + 1]`, and the counting form says that their slopes `#G_{m+1} / #G_0` and
`(#H_{m+1} / #H_0) · (#(G/H)_{φ_{M/L}(m+1)} / #(G/H)_0)` agree; since both functions are the
identity on `[-1, 0]`, this gives the **transitivity of the Herbrand functions**

`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`   and   `ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`,

together with its integral form `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`. Reading Herbrand's theorem
at `u = ψ_{M/K}(v) = ψ_{M/L}(ψ_{L/K}(v))` then shows that the upper numbering, unlike the lower
one, is **compatible with quotients**: the image of `G^v` under restriction to `L` is the upper
ramification group of `L/K` at the same index, `(G/H)^v = G^v H / H`.

## Main results

* `TauCeti.LocalFieldsRamification.natCard_lowerRamificationGroupReal_herbrand_mul`:
  Herbrand's theorem in counting form, `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_of_herbrand_lt_of_le_herbrand`:
  the filtration of `L/K` is constant on `(φ_{M/L}(a), φ_{M/L}(b)]` when that of `M/K` is
  constant on `(a, b]`.
* `TauCeti.LocalFieldsRamification.herbrand_tower`: `φ_{M/K}(u) = φ_{L/K}(φ_{M/L}(u))`.
* `TauCeti.LocalFieldsRamification.inverseHerbrand_tower`:
  `ψ_{M/K}(v) = ψ_{M/L}(ψ_{L/K}(v))`.
* `TauCeti.LocalFieldsRamification.psiNat_tower`: `ψℕ_{M/K}(n) = ψℕ_{M/L}(ψℕ_{L/K}(n))`.
* `TauCeti.LocalFieldsRamification.map_restrictNormalHom_upperRamificationGroup`:
  `(G/H)^v = G^v H / H`, the compatibility of the upper numbering with quotients.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §3, Propositions 14 and 15.
-/

public section
noncomputable section

namespace TauCeti.LocalFieldsRamification

variable (K L M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field M] [ValuativeRel M] [TopologicalSpace M]
  [IsNonarchimedeanLocalField M]
  [Algebra K L] [ValuativeExtension K L] [Module.Finite K L]
  [Algebra L M] [ValuativeExtension L M] [Module.Finite L M] [IsGalois L M]
  [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
  [IsScalarTower K L M]

/-! ### Herbrand's theorem in counting form -/

/-- **Herbrand's theorem in counting form.** For `G = Gal(M/K)`, `H = Gal(M/L)` and
`G/H = Gal(L/K)`, the orders satisfy `#(G/H)_{φ_{M/L}(u)} · #H_u = #G_u`: the lower ramification
group of the quotient at `φ_{M/L}(u)` is the image of `G_u` under restriction to `L`, and the
kernel of restriction on `G_u` is `H ∩ G_u = H_u`. -/
theorem natCard_lowerRamificationGroupReal_herbrand_mul [Normal K L] [Normal K M]
    (u : RamificationIndexDomain) :
    Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) *
        Nat.card (lowerRamificationGroupReal L M u) =
      Nat.card (lowerRamificationGroupReal K M u) := by
  rw [← map_restrictNormalHom_lowerRamificationGroupReal (K := K) (L := L) (M := M) u,
    ← Subgroup.relIndex_ker,
    ← Subgroup.card_map_of_injective (K := lowerRamificationGroupReal L M u)
      (AlgEquiv.restrictScalarsHom_injective K),
    map_restrictScalarsHom_lowerRamificationGroupReal K M L u,
    AlgEquiv.range_restrictScalarsHom_eq_ker_restrictNormalHom K L M,
    ← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype, Subgroup.relIndex, mul_comm,
    Subgroup.card_mul_index]

/-- Through Herbrand's theorem, the lower filtration of `L/K` is constant on the interval
`(φ_{M/L}(a), φ_{M/L}(b)]` as soon as that of `M/K` is constant on `(a, b]`. -/
theorem lowerRamificationGroupReal_eq_of_herbrand_lt_of_le_herbrand [Normal K L] [Normal K M]
    {a b : RamificationIndexDomain}
    (h : ∀ t : ℝ, (a : ℝ) < t → t ≤ b →
      lowerRamificationGroupReal K M t = lowerRamificationGroupReal K M b)
    {t : ℝ} (ht₁ : (herbrand L M a : ℝ) < t) (ht₂ : t ≤ herbrand L M b) :
    lowerRamificationGroupReal K L t = lowerRamificationGroupReal K L (herbrand L M b) := by
  set s : RamificationIndexDomain := ⟨t, Set.mem_Ici.2 ((herbrand L M a).2.trans ht₁.le)⟩
  -- `t = φ_{M/L}(ψ_{M/L}(t))` with `a < ψ_{M/L}(t) ≤ b`.
  have hs₁ : a < inverseHerbrand L M s := by
    rw [← inverseHerbrand_herbrand L M a]
    exact inverseHerbrand_strictMono L M (Subtype.coe_lt_coe.1 ht₁)
  have hs₂ : inverseHerbrand L M s ≤ b := by
    rw [← inverseHerbrand_herbrand L M b]
    exact (inverseHerbrand_strictMono L M).monotone (Subtype.coe_le_coe.1 ht₂)
  have ht : t = herbrand L M (inverseHerbrand L M s) := by rw [herbrand_inverseHerbrand]
  rw [ht, ← map_restrictNormalHom_lowerRamificationGroupReal,
    ← map_restrictNormalHom_lowerRamificationGroupReal, h _ hs₁ hs₂]

/-! ### Transitivity of the Herbrand functions -/

variable [IsGalois K L] [IsGalois K M]

/-- The transitivity `φ_{M/K}(u) = φ_{L/K}(φ_{M/L}(u))` propagates from the left endpoint `m` of
an interval `[m, m + 1]`, `m : ℕ`, to every point `u` of that interval: both sides are affine
there, and Herbrand's theorem in counting form identifies their slopes. -/
private theorem herbrand_tower_of_mem_Icc_of_eq (m : ℕ) {u : RamificationIndexDomain}
    (h₁ : (m : ℝ) ≤ u) (h₂ : (u : ℝ) ≤ m + 1)
    (hm : herbrand K M ⟨m, natCast_mem_ramificationIndexDomain m⟩ =
      herbrand K L (herbrand L M ⟨m, natCast_mem_ramificationIndexDomain m⟩)) :
    herbrand K M u = herbrand K L (herbrand L M u) := by
  set a : RamificationIndexDomain := ⟨m, natCast_mem_ramificationIndexDomain m⟩
  have hau : a ≤ u := Subtype.coe_le_coe.1 h₁
  -- The lower filtrations of `M/K` and `M/L` are constant on `(m, u] ⊆ (m, m + 1]`.
  have hGM : ∀ t : ℝ, (a : ℝ) < t → t ≤ u →
      lowerRamificationGroupReal K M t = lowerRamificationGroupReal K M u := fun t ht₁ ht₂ ↦ by
    rw [lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      lowerRamificationGroupReal_eq_of_sub_one_lt_of_le K M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  have hHM : ∀ t : ℝ, (a : ℝ) < t → t ≤ u →
      lowerRamificationGroupReal L M t = lowerRamificationGroupReal L M u := fun t ht₁ ht₂ ↦ by
    rw [lowerRamificationGroupReal_eq_of_sub_one_lt_of_le L M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith),
      lowerRamificationGroupReal_eq_of_sub_one_lt_of_le L M (i := m + 1) (by push_cast; linarith)
        (by push_cast; linarith)]
  -- The three affine formulas and the two counting identities.
  have hMK := coe_herbrand_sub_coe_herbrand_of_forall_eq K M hau hGM
  have hML := coe_herbrand_sub_coe_herbrand_of_forall_eq L M hau hHM
  have hLK := coe_herbrand_sub_coe_herbrand_of_forall_eq K L
    ((herbrand_strictMono L M).monotone hau) fun _ ht₁ ht₂ ↦
      lowerRamificationGroupReal_eq_of_herbrand_lt_of_le_herbrand K L M hGM ht₁ ht₂
  have hcard : (Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) : ℝ) *
      Nat.card (lowerRamificationGroupReal L M u) =
        Nat.card (lowerRamificationGroupReal K M u) := by
    exact_mod_cast natCard_lowerRamificationGroupReal_herbrand_mul K L M u
  have hcard₀ : (Nat.card (lowerRamificationGroup K L 0) : ℝ) *
      Nat.card (lowerRamificationGroup L M 0) = Nat.card (lowerRamificationGroup K M 0) := by
    rw [natCard_lowerRamificationGroup_zero, natCard_lowerRamificationGroup_zero,
      natCard_lowerRamificationGroup_zero, ramificationIndex_tower (K := K) (L := L) M]
    push_cast
    ring
  -- The slopes agree: `#G_u / #G_0 = (#H_u / #H_0) · (#(G/H)_{φ(u)} / #(G/H)_0)`.
  have hslope : (Nat.card (lowerRamificationGroupReal K M u) : ℝ) /
      Nat.card (lowerRamificationGroup K M 0) =
        (Nat.card (lowerRamificationGroupReal L M u) / Nat.card (lowerRamificationGroup L M 0)) *
          (Nat.card (lowerRamificationGroupReal K L (herbrand L M u)) /
            Nat.card (lowerRamificationGroup K L 0)) := by
    rw [div_mul_div_comm, ← hcard, ← hcard₀,
      mul_comm (Nat.card (lowerRamificationGroupReal L M u) : ℝ),
      mul_comm (Nat.card (lowerRamificationGroup L M 0) : ℝ)]
  have hm' : (herbrand K M a : ℝ) = herbrand K L (herbrand L M a) := congrArg Subtype.val hm
  apply Subtype.ext
  rw [hslope] at hMK
  rw [hML] at hLK
  linear_combination hMK - hLK + hm'

/-- `φ_{M/K} = φ_{L/K} ∘ φ_{M/L}` on `[m, m + 1]`, by induction on `m : ℕ`. -/
private theorem herbrand_tower_of_mem_Icc (m : ℕ) :
    ∀ u : RamificationIndexDomain, (m : ℝ) ≤ u → (u : ℝ) ≤ m + 1 →
      herbrand K M u = herbrand K L (herbrand L M u) := by
  induction m with
  | zero =>
    intro u h₁ h₂
    refine herbrand_tower_of_mem_Icc_of_eq K L M 0 h₁ h₂ ?_
    rw [herbrand_of_coe_le_zero L M (by simp), herbrand_of_coe_le_zero K L (by simp),
      herbrand_of_coe_le_zero K M (by simp)]
  | succ m ih =>
    intro u h₁ h₂
    exact herbrand_tower_of_mem_Icc_of_eq K L M (m + 1) h₁ h₂
      (ih _ (by push_cast; linarith) (by push_cast; linarith))

/-- **Transitivity of the Herbrand function** in a tower `M/L/K` of Galois extensions:
`φ_{M/K} = φ_{L/K} ∘ φ_{M/L}`. -/
theorem herbrand_tower (u : RamificationIndexDomain) :
    herbrand K M u = herbrand K L (herbrand L M u) := by
  rcases le_or_gt (u : ℝ) 0 with hu | hu
  · rw [herbrand_of_coe_le_zero L M hu, herbrand_of_coe_le_zero K L hu,
      herbrand_of_coe_le_zero K M hu]
  · exact herbrand_tower_of_mem_Icc K L M ⌊(u : ℝ)⌋₊ u (Nat.floor_le hu.le)
      (Nat.lt_floor_add_one _).le

/-- **Transitivity of the inverse Herbrand function** in a tower `M/L/K` of Galois extensions:
`ψ_{M/K} = ψ_{M/L} ∘ ψ_{L/K}`. Inverting the composite `φ_{L/K} ∘ φ_{M/L}` reverses its order. -/
theorem inverseHerbrand_tower (v : RamificationIndexDomain) :
    inverseHerbrand K M v = inverseHerbrand L M (inverseHerbrand K L v) := by
  apply (herbrand_strictMono K M).injective
  rw [herbrand_inverseHerbrand, herbrand_tower K L M, herbrand_inverseHerbrand,
    herbrand_inverseHerbrand]

/-- **Transitivity of the integral inverse Herbrand function**: `ψℕ_{M/K} = ψℕ_{M/L} ∘ ψℕ_{L/K}`. -/
theorem psiNat_tower (n : ℕ) : psiNat K M n = psiNat L M (psiNat K L n) := by
  have h : (⟨(psiNat K L n : ℝ), natCast_mem_ramificationIndexDomain _⟩ : RamificationIndexDomain) =
      inverseHerbrand K L ⟨n, natCast_mem_ramificationIndexDomain n⟩ :=
    Subtype.ext (coe_psiNat K L n)
  apply Nat.cast_injective (R := ℝ)
  rw [coe_psiNat, coe_psiNat, h, inverseHerbrand_tower K L M]

/-! ### The upper numbering is compatible with quotients -/

/-- **The upper numbering is compatible with quotients.** For `G = Gal(M/K)`, `H = Gal(M/L)`
normal and `G/H = Gal(L/K)`, the image of the upper ramification group `G^v` under restriction to
`L` is the upper ramification group of `L/K` at the same index: `(G/H)^v = G^v H / H`. -/
@[simp]
theorem map_restrictNormalHom_upperRamificationGroup (v : RamificationIndexDomain) :
    (upperRamificationGroup K M v).map (AlgEquiv.restrictNormalHom L) =
      upperRamificationGroup K L v := by
  rw [upperRamificationGroup_def, upperRamificationGroup_def, inverseHerbrand_tower K L M,
    map_restrictNormalHom_lowerRamificationGroupReal, herbrand_inverseHerbrand]

end TauCeti.LocalFieldsRamification
