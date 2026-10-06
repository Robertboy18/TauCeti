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

/-- Trimmed scan word 64 holds in the exact presentation group. -/
theorem r64_eq_one : (r64.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    10 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 65 holds in the exact presentation group. -/
theorem r65_eq_one : (r65.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word4 true
    11 word4_eq_one (by decide +kernel)

/-- Trimmed scan word 66 holds in the exact presentation group. -/
theorem r66_eq_one : (r66.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 false
    0 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 67 holds in the exact presentation group. -/
theorem r67_eq_one : (r67.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 false
    2 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 68 holds in the exact presentation group. -/
theorem r68_eq_one : (r68.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 false
    10 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 69 holds in the exact presentation group. -/
theorem r69_eq_one : (r69.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 true
    3 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 70 holds in the exact presentation group. -/
theorem r70_eq_one : (r70.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 true
    4 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 71 holds in the exact presentation group. -/
theorem r71_eq_one : (r71.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word5 true
    7 word5_eq_one (by decide +kernel)

/-- Trimmed scan word 72 holds in the exact presentation group. -/
theorem r72_eq_one : (r72.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 false
    3 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 73 holds in the exact presentation group. -/
theorem r73_eq_one : (r73.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 false
    11 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 74 holds in the exact presentation group. -/
theorem r74_eq_one : (r74.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 false
    12 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 75 holds in the exact presentation group. -/
theorem r75_eq_one : (r75.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 true
    1 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 76 holds in the exact presentation group. -/
theorem r76_eq_one : (r76.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 true
    3 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 77 holds in the exact presentation group. -/
theorem r77_eq_one : (r77.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word6 true
    5 word6_eq_one (by decide +kernel)

/-- Trimmed scan word 78 holds in the exact presentation group. -/
theorem r78_eq_one : (r78.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word7 false
    8 word7_eq_one (by decide +kernel)

/-- Trimmed scan word 79 holds in the exact presentation group. -/
theorem r79_eq_one : (r79.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word7 true
    3 word7_eq_one (by decide +kernel)

/-- Trimmed scan word 80 holds in the exact presentation group. -/
theorem r80_eq_one : (r80.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word8 false
    1 word8_eq_one (by decide +kernel)

/-- Trimmed scan word 81 holds in the exact presentation group. -/
theorem r81_eq_one : (r81.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word8 false
    12 word8_eq_one (by decide +kernel)

/-- Trimmed scan word 82 holds in the exact presentation group. -/
theorem r82_eq_one : (r82.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word8 true
    1 word8_eq_one (by decide +kernel)

/-- Trimmed scan word 83 holds in the exact presentation group. -/
theorem r83_eq_one : (r83.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word8 true
    12 word8_eq_one (by decide +kernel)

/-- Trimmed scan word 84 holds in the exact presentation group. -/
theorem r84_eq_one : (r84.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word8 true
    13 word8_eq_one (by decide +kernel)

/-- Trimmed scan word 85 holds in the exact presentation group. -/
theorem r85_eq_one : (r85.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word11 true
    13 word11_eq_one (by decide +kernel)

/-- Trimmed scan word 86 holds in the exact presentation group. -/
theorem r86_eq_one : (r86.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    3 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 87 holds in the exact presentation group. -/
theorem r87_eq_one : (r87.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    4 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 88 holds in the exact presentation group. -/
theorem r88_eq_one : (r88.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    9 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 89 holds in the exact presentation group. -/
theorem r89_eq_one : (r89.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    10 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 90 holds in the exact presentation group. -/
theorem r90_eq_one : (r90.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    11 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 91 holds in the exact presentation group. -/
theorem r91_eq_one : (r91.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 false
    12 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 92 holds in the exact presentation group. -/
theorem r92_eq_one : (r92.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 true
    2 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 93 holds in the exact presentation group. -/
theorem r93_eq_one : (r93.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 true
    10 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 94 holds in the exact presentation group. -/
theorem r94_eq_one : (r94.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word12 true
    11 word12_eq_one (by decide +kernel)

/-- Trimmed scan word 95 holds in the exact presentation group. -/
theorem r95_eq_one : (r95.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 false
    0 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 96 holds in the exact presentation group. -/
theorem r96_eq_one : (r96.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 false
    6 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 97 holds in the exact presentation group. -/
theorem r97_eq_one : (r97.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 false
    7 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 98 holds in the exact presentation group. -/
theorem r98_eq_one : (r98.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 false
    13 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 99 holds in the exact presentation group. -/
theorem r99_eq_one : (r99.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 true
    1 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 100 holds in the exact presentation group. -/
theorem r100_eq_one : (r100.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 true
    7 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 101 holds in the exact presentation group. -/
theorem r101_eq_one : (r101.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 true
    11 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 102 holds in the exact presentation group. -/
theorem r102_eq_one : (r102.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word14 true
    14 word14_eq_one (by decide +kernel)

/-- Trimmed scan word 103 holds in the exact presentation group. -/
theorem r103_eq_one : (r103.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 false
    0 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 104 holds in the exact presentation group. -/
theorem r104_eq_one : (r104.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 false
    4 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 105 holds in the exact presentation group. -/
theorem r105_eq_one : (r105.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 false
    5 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 106 holds in the exact presentation group. -/
theorem r106_eq_one : (r106.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 false
    6 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 107 holds in the exact presentation group. -/
theorem r107_eq_one : (r107.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 true
    6 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 108 holds in the exact presentation group. -/
theorem r108_eq_one : (r108.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 true
    9 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 109 holds in the exact presentation group. -/
theorem r109_eq_one : (r109.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 true
    10 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 110 holds in the exact presentation group. -/
theorem r110_eq_one : (r110.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word19 true
    14 word19_eq_one (by decide +kernel)

/-- Trimmed scan word 111 holds in the exact presentation group. -/
theorem r111_eq_one : (r111.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    1 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 112 holds in the exact presentation group. -/
theorem r112_eq_one : (r112.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    2 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 113 holds in the exact presentation group. -/
theorem r113_eq_one : (r113.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    9 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 114 holds in the exact presentation group. -/
theorem r114_eq_one : (r114.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    10 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 115 holds in the exact presentation group. -/
theorem r115_eq_one : (r115.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    11 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 116 holds in the exact presentation group. -/
theorem r116_eq_one : (r116.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 false
    13 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 117 holds in the exact presentation group. -/
theorem r117_eq_one : (r117.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    1 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 118 holds in the exact presentation group. -/
theorem r118_eq_one : (r118.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    3 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 119 holds in the exact presentation group. -/
theorem r119_eq_one : (r119.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    4 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 120 holds in the exact presentation group. -/
theorem r120_eq_one : (r120.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    5 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 121 holds in the exact presentation group. -/
theorem r121_eq_one : (r121.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    9 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 122 holds in the exact presentation group. -/
theorem r122_eq_one : (r122.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word21 true
    12 word21_eq_one (by decide +kernel)

/-- Trimmed scan word 123 holds in the exact presentation group. -/
theorem r123_eq_one : (r123.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word26 false
    7 word26_eq_one (by decide +kernel)

/-- Trimmed scan word 124 holds in the exact presentation group. -/
theorem r124_eq_one : (r124.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word26 true
    0 word26_eq_one (by decide +kernel)

/-- Trimmed scan word 125 holds in the exact presentation group. -/
theorem r125_eq_one : (r125.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word26 true
    5 word26_eq_one (by decide +kernel)

/-- Trimmed scan word 126 holds in the exact presentation group. -/
theorem r126_eq_one : (r126.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word28 false
    9 word28_eq_one (by decide +kernel)

/-- Trimmed scan word 127 holds in the exact presentation group. -/
theorem r127_eq_one : (r127.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word28 false
    11 word28_eq_one (by decide +kernel)

@[expose]
def scanBlock4 : List (List (Fin 4)) :=
  [r64, r65, r66, r67, r68,
    r69, r70, r71, r72, r73,
    r74, r75, r76, r77, r78,
    r79]

theorem scanBlock4_eq_one : ∀ w ∈ scanBlock4, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock4, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r64_eq_one
  · exact r65_eq_one
  · exact r66_eq_one
  · exact r67_eq_one
  · exact r68_eq_one
  · exact r69_eq_one
  · exact r70_eq_one
  · exact r71_eq_one
  · exact r72_eq_one
  · exact r73_eq_one
  · exact r74_eq_one
  · exact r75_eq_one
  · exact r76_eq_one
  · exact r77_eq_one
  · exact r78_eq_one
  · exact r79_eq_one

@[expose]
def scanBlock5 : List (List (Fin 4)) :=
  [r80, r81, r82, r83, r84,
    r85, r86, r87, r88, r89,
    r90, r91, r92, r93, r94,
    r95]

theorem scanBlock5_eq_one : ∀ w ∈ scanBlock5, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock5, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r80_eq_one
  · exact r81_eq_one
  · exact r82_eq_one
  · exact r83_eq_one
  · exact r84_eq_one
  · exact r85_eq_one
  · exact r86_eq_one
  · exact r87_eq_one
  · exact r88_eq_one
  · exact r89_eq_one
  · exact r90_eq_one
  · exact r91_eq_one
  · exact r92_eq_one
  · exact r93_eq_one
  · exact r94_eq_one
  · exact r95_eq_one

@[expose]
def scanBlock6 : List (List (Fin 4)) :=
  [r96, r97, r98, r99, r100,
    r101, r102, r103, r104, r105,
    r106, r107, r108, r109, r110,
    r111]

theorem scanBlock6_eq_one : ∀ w ∈ scanBlock6, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock6, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r96_eq_one
  · exact r97_eq_one
  · exact r98_eq_one
  · exact r99_eq_one
  · exact r100_eq_one
  · exact r101_eq_one
  · exact r102_eq_one
  · exact r103_eq_one
  · exact r104_eq_one
  · exact r105_eq_one
  · exact r106_eq_one
  · exact r107_eq_one
  · exact r108_eq_one
  · exact r109_eq_one
  · exact r110_eq_one
  · exact r111_eq_one

@[expose]
def scanBlock7 : List (List (Fin 4)) :=
  [r112, r113, r114, r115, r116,
    r117, r118, r119, r120, r121,
    r122, r123, r124, r125, r126,
    r127]

theorem scanBlock7_eq_one : ∀ w ∈ scanBlock7, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock7, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r112_eq_one
  · exact r113_eq_one
  · exact r114_eq_one
  · exact r115_eq_one
  · exact r116_eq_one
  · exact r117_eq_one
  · exact r118_eq_one
  · exact r119_eq_one
  · exact r120_eq_one
  · exact r121_eq_one
  · exact r122_eq_one
  · exact r123_eq_one
  · exact r124_eq_one
  · exact r125_eq_one
  · exact r126_eq_one
  · exact r127_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
