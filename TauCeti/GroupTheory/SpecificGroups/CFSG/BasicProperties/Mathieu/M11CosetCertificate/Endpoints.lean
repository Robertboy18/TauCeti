/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Bits5
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.Initial

/-!
# Initial and final states of the M11 coset certificate

The initial bit masks agree pointwise with the checker's tree edges.
Every bit corresponding to a table edge is set in the final state.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

theorem interval_extend {P : Fin 990 → Prop} {lo size : ℕ}
    (hbound : lo + size ≤ 990)
    (h : ∀ j : Fin size, P ⟨lo + j.val, by omega⟩)
    (i : Fin 990) (hlo : lo ≤ i.val) (hhi : i.val < lo + size) : P i := by
  have hj : i.val - lo < size := by omega
  have he : lo + (i.val - lo) = i.val := by omega
  simpa only [he] using h ⟨i.val - lo, hj⟩

theorem initial_bits_match : BitsAgree table.treeEdgesFast bits000 := by
  intro t i
  simp only [TauCeti.CosetTable.treeEdgesFast, Fin.getElem_fin, Vector.getElem_ofFn]
  let P (j : Fin 990) : Prop :=
    decide (table.word (table.act t j) = t :: table.word j) = bits000[t].testBit j.val
  by_cases h0 : i.val < 64
  · exact interval_extend (P := P) (lo := 0) (size := 64) (by decide)
      (initial_bits_00 t) i (by omega) (by omega)
  by_cases h1 : i.val < 128
  · exact interval_extend (P := P) (lo := 64) (size := 64) (by decide)
      (initial_bits_01 t) i (by omega) (by omega)
  by_cases h2 : i.val < 192
  · exact interval_extend (P := P) (lo := 128) (size := 64) (by decide)
      (initial_bits_02 t) i (by omega) (by omega)
  by_cases h3 : i.val < 256
  · exact interval_extend (P := P) (lo := 192) (size := 64) (by decide)
      (initial_bits_03 t) i (by omega) (by omega)
  by_cases h4 : i.val < 320
  · exact interval_extend (P := P) (lo := 256) (size := 64) (by decide)
      (initial_bits_04 t) i (by omega) (by omega)
  by_cases h5 : i.val < 384
  · exact interval_extend (P := P) (lo := 320) (size := 64) (by decide)
      (initial_bits_05 t) i (by omega) (by omega)
  by_cases h6 : i.val < 448
  · exact interval_extend (P := P) (lo := 384) (size := 64) (by decide)
      (initial_bits_06 t) i (by omega) (by omega)
  by_cases h7 : i.val < 512
  · exact interval_extend (P := P) (lo := 448) (size := 64) (by decide)
      (initial_bits_07 t) i (by omega) (by omega)
  by_cases h8 : i.val < 576
  · exact interval_extend (P := P) (lo := 512) (size := 64) (by decide)
      (initial_bits_08 t) i (by omega) (by omega)
  by_cases h9 : i.val < 640
  · exact interval_extend (P := P) (lo := 576) (size := 64) (by decide)
      (initial_bits_09 t) i (by omega) (by omega)
  by_cases h10 : i.val < 704
  · exact interval_extend (P := P) (lo := 640) (size := 64) (by decide)
      (initial_bits_10 t) i (by omega) (by omega)
  by_cases h11 : i.val < 768
  · exact interval_extend (P := P) (lo := 704) (size := 64) (by decide)
      (initial_bits_11 t) i (by omega) (by omega)
  by_cases h12 : i.val < 832
  · exact interval_extend (P := P) (lo := 768) (size := 64) (by decide)
      (initial_bits_12 t) i (by omega) (by omega)
  by_cases h13 : i.val < 896
  · exact interval_extend (P := P) (lo := 832) (size := 64) (by decide)
      (initial_bits_13 t) i (by omega) (by omega)
  by_cases h14 : i.val < 960
  · exact interval_extend (P := P) (lo := 896) (size := 64) (by decide)
      (initial_bits_14 t) i (by omega) (by omega)
  exact interval_extend (P := P) (lo := 960) (size := 30) (by decide)
    (initial_bits_15 t) i (by omega) (by omega)

theorem final_bits_value : bits093 = Vector.replicate 4 (2 ^ 990 - 1) := by
  decide +kernel

theorem final_bits_known (t : Fin 4) (i : Fin 990) : bits093[t].testBit i.val = true := by
  rw [final_bits_value]
  rw [Fin.getElem_fin, Vector.getElem_replicate, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true i.isLt

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
