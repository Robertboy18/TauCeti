/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Mathieu.M11CosetCertificate.RelationSoundness.Basic

/-! Exact relations for the concrete words in the M11 coset certificate. -/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness

open Relations

/-- Trimmed scan word 0 holds in the exact presentation group. -/
theorem r0_eq_one : (r0.map letterValue).prod = 1 :=
  scan_reduce_nil _ (by decide +kernel)

/-- Trimmed scan word 1 holds in the exact presentation group. -/
theorem r1_eq_one : (r1.map letterValue).prod = 1 :=
  scan_reduce_nil _ (by decide +kernel)

/-- Trimmed scan word 2 holds in the exact presentation group. -/
theorem r2_eq_one : (r2.map letterValue).prod = 1 :=
  scan_reduce_nil _ (by decide +kernel)

/-- Trimmed scan word 3 holds in the exact presentation group. -/
theorem r3_eq_one : (r3.map letterValue).prod = 1 :=
  scan_reduce_nil _ (by decide +kernel)

/-- Trimmed scan word 4 holds in the exact presentation group. -/
theorem r4_eq_one : (r4.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    0 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 5 holds in the exact presentation group. -/
theorem r5_eq_one : (r5.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    1 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 6 holds in the exact presentation group. -/
theorem r6_eq_one : (r6.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    3 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 7 holds in the exact presentation group. -/
theorem r7_eq_one : (r7.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    4 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 8 holds in the exact presentation group. -/
theorem r8_eq_one : (r8.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    5 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 9 holds in the exact presentation group. -/
theorem r9_eq_one : (r9.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    6 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 10 holds in the exact presentation group. -/
theorem r10_eq_one : (r10.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    7 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 11 holds in the exact presentation group. -/
theorem r11_eq_one : (r11.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 false
    8 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 12 holds in the exact presentation group. -/
theorem r12_eq_one : (r12.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    0 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 13 holds in the exact presentation group. -/
theorem r13_eq_one : (r13.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    1 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 14 holds in the exact presentation group. -/
theorem r14_eq_one : (r14.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    2 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 15 holds in the exact presentation group. -/
theorem r15_eq_one : (r15.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    3 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 16 holds in the exact presentation group. -/
theorem r16_eq_one : (r16.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    4 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 17 holds in the exact presentation group. -/
theorem r17_eq_one : (r17.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    5 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 18 holds in the exact presentation group. -/
theorem r18_eq_one : (r18.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    6 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 19 holds in the exact presentation group. -/
theorem r19_eq_one : (r19.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    7 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 20 holds in the exact presentation group. -/
theorem r20_eq_one : (r20.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word0 true
    8 word0_eq_one (by decide +kernel)

/-- Trimmed scan word 21 holds in the exact presentation group. -/
theorem r21_eq_one : (r21.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    0 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 22 holds in the exact presentation group. -/
theorem r22_eq_one : (r22.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    1 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 23 holds in the exact presentation group. -/
theorem r23_eq_one : (r23.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    2 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 24 holds in the exact presentation group. -/
theorem r24_eq_one : (r24.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    3 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 25 holds in the exact presentation group. -/
theorem r25_eq_one : (r25.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    4 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 26 holds in the exact presentation group. -/
theorem r26_eq_one : (r26.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    5 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 27 holds in the exact presentation group. -/
theorem r27_eq_one : (r27.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    6 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 28 holds in the exact presentation group. -/
theorem r28_eq_one : (r28.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    7 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 29 holds in the exact presentation group. -/
theorem r29_eq_one : (r29.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    8 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 30 holds in the exact presentation group. -/
theorem r30_eq_one : (r30.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 false
    9 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 31 holds in the exact presentation group. -/
theorem r31_eq_one : (r31.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    0 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 32 holds in the exact presentation group. -/
theorem r32_eq_one : (r32.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    1 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 33 holds in the exact presentation group. -/
theorem r33_eq_one : (r33.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    2 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 34 holds in the exact presentation group. -/
theorem r34_eq_one : (r34.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    3 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 35 holds in the exact presentation group. -/
theorem r35_eq_one : (r35.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    4 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 36 holds in the exact presentation group. -/
theorem r36_eq_one : (r36.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    5 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 37 holds in the exact presentation group. -/
theorem r37_eq_one : (r37.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    6 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 38 holds in the exact presentation group. -/
theorem r38_eq_one : (r38.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    7 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 39 holds in the exact presentation group. -/
theorem r39_eq_one : (r39.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    8 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 40 holds in the exact presentation group. -/
theorem r40_eq_one : (r40.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word1 true
    9 word1_eq_one (by decide +kernel)

/-- Trimmed scan word 41 holds in the exact presentation group. -/
theorem r41_eq_one : (r41.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    2 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 42 holds in the exact presentation group. -/
theorem r42_eq_one : (r42.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    4 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 43 holds in the exact presentation group. -/
theorem r43_eq_one : (r43.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    7 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 44 holds in the exact presentation group. -/
theorem r44_eq_one : (r44.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    8 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 45 holds in the exact presentation group. -/
theorem r45_eq_one : (r45.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    11 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 46 holds in the exact presentation group. -/
theorem r46_eq_one : (r46.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 false
    12 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 47 holds in the exact presentation group. -/
theorem r47_eq_one : (r47.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 true
    1 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 48 holds in the exact presentation group. -/
theorem r48_eq_one : (r48.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 true
    4 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 49 holds in the exact presentation group. -/
theorem r49_eq_one : (r49.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 true
    5 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 50 holds in the exact presentation group. -/
theorem r50_eq_one : (r50.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 true
    6 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 51 holds in the exact presentation group. -/
theorem r51_eq_one : (r51.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word2 true
    9 word2_eq_one (by decide +kernel)

/-- Trimmed scan word 52 holds in the exact presentation group. -/
theorem r52_eq_one : (r52.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word3 true
    0 word3_eq_one (by decide +kernel)

/-- Trimmed scan word 53 holds in the exact presentation group. -/
theorem r53_eq_one : (r53.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word3 true
    5 word3_eq_one (by decide +kernel)

/-- Trimmed scan word 54 holds in the exact presentation group. -/
theorem r54_eq_one : (r54.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 false
    0 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 55 holds in the exact presentation group. -/
theorem r55_eq_one : (r55.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 false
    3 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 56 holds in the exact presentation group. -/
theorem r56_eq_one : (r56.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 false
    4 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 57 holds in the exact presentation group. -/
theorem r57_eq_one : (r57.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 false
    7 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 58 holds in the exact presentation group. -/
theorem r58_eq_one : (r58.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 false
    8 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 59 holds in the exact presentation group. -/
theorem r59_eq_one : (r59.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    0 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 60 holds in the exact presentation group. -/
theorem r60_eq_one : (r60.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    5 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 61 holds in the exact presentation group. -/
theorem r61_eq_one : (r61.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    7 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 62 holds in the exact presentation group. -/
theorem r62_eq_one : (r62.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    8 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 63 holds in the exact presentation group. -/
theorem r63_eq_one : (r63.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    9 word4_eq_one (by decide +kernel)

@[expose]
def scanBlock0 : List (List (Fin 4)) :=
  [r0, r1, r2, r3, r4,
    r5, r6, r7, r8, r9,
    r10, r11, r12, r13, r14,
    r15]

theorem scanBlock0_eq_one : ∀ w ∈ scanBlock0, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock0, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r0_eq_one
  · exact r1_eq_one
  · exact r2_eq_one
  · exact r3_eq_one
  · exact r4_eq_one
  · exact r5_eq_one
  · exact r6_eq_one
  · exact r7_eq_one
  · exact r8_eq_one
  · exact r9_eq_one
  · exact r10_eq_one
  · exact r11_eq_one
  · exact r12_eq_one
  · exact r13_eq_one
  · exact r14_eq_one
  · exact r15_eq_one

@[expose]
def scanBlock1 : List (List (Fin 4)) :=
  [r16, r17, r18, r19, r20,
    r21, r22, r23, r24, r25,
    r26, r27, r28, r29, r30,
    r31]

theorem scanBlock1_eq_one : ∀ w ∈ scanBlock1, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock1, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r16_eq_one
  · exact r17_eq_one
  · exact r18_eq_one
  · exact r19_eq_one
  · exact r20_eq_one
  · exact r21_eq_one
  · exact r22_eq_one
  · exact r23_eq_one
  · exact r24_eq_one
  · exact r25_eq_one
  · exact r26_eq_one
  · exact r27_eq_one
  · exact r28_eq_one
  · exact r29_eq_one
  · exact r30_eq_one
  · exact r31_eq_one

@[expose]
def scanBlock2 : List (List (Fin 4)) :=
  [r32, r33, r34, r35, r36,
    r37, r38, r39, r40, r41,
    r42, r43, r44, r45, r46,
    r47]

theorem scanBlock2_eq_one : ∀ w ∈ scanBlock2, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock2, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r32_eq_one
  · exact r33_eq_one
  · exact r34_eq_one
  · exact r35_eq_one
  · exact r36_eq_one
  · exact r37_eq_one
  · exact r38_eq_one
  · exact r39_eq_one
  · exact r40_eq_one
  · exact r41_eq_one
  · exact r42_eq_one
  · exact r43_eq_one
  · exact r44_eq_one
  · exact r45_eq_one
  · exact r46_eq_one
  · exact r47_eq_one

@[expose]
def scanBlock3 : List (List (Fin 4)) :=
  [r48, r49, r50, r51, r52,
    r53, r54, r55, r56, r57,
    r58, r59, r60, r61, r62,
    r63]

theorem scanBlock3_eq_one : ∀ w ∈ scanBlock3, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock3, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r48_eq_one
  · exact r49_eq_one
  · exact r50_eq_one
  · exact r51_eq_one
  · exact r52_eq_one
  · exact r53_eq_one
  · exact r54_eq_one
  · exact r55_eq_one
  · exact r56_eq_one
  · exact r57_eq_one
  · exact r58_eq_one
  · exact r59_eq_one
  · exact r60_eq_one
  · exact r61_eq_one
  · exact r62_eq_one
  · exact r63_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
