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

/-- Trimmed scan word 128 holds in the exact presentation group. -/
theorem r128_eq_one : (r128.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word28 true
    3 word28_eq_one (by decide +kernel)

/-- Trimmed scan word 129 holds in the exact presentation group. -/
theorem r129_eq_one : (r129.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word30 false
    0 word30_eq_one (by decide +kernel)

/-- Trimmed scan word 130 holds in the exact presentation group. -/
theorem r130_eq_one : (r130.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word30 false
    12 word30_eq_one (by decide +kernel)

/-- Trimmed scan word 131 holds in the exact presentation group. -/
theorem r131_eq_one : (r131.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word30 true
    2 word30_eq_one (by decide +kernel)

/-- Trimmed scan word 132 holds in the exact presentation group. -/
theorem r132_eq_one : (r132.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word30 true
    14 word30_eq_one (by decide +kernel)

/-- Trimmed scan word 133 holds in the exact presentation group. -/
theorem r133_eq_one : (r133.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word38 false
    14 word38_eq_one (by decide +kernel)

/-- Trimmed scan word 134 holds in the exact presentation group. -/
theorem r134_eq_one : (r134.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word38 false
    15 word38_eq_one (by decide +kernel)

/-- Trimmed scan word 135 holds in the exact presentation group. -/
theorem r135_eq_one : (r135.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word38 true
    0 word38_eq_one (by decide +kernel)

/-- Trimmed scan word 136 holds in the exact presentation group. -/
theorem r136_eq_one : (r136.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word38 true
    1 word38_eq_one (by decide +kernel)

/-- Trimmed scan word 137 holds in the exact presentation group. -/
theorem r137_eq_one : (r137.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word38 true
    4 word38_eq_one (by decide +kernel)

/-- Trimmed scan word 138 holds in the exact presentation group. -/
theorem r138_eq_one : (r138.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 false
    0 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 139 holds in the exact presentation group. -/
theorem r139_eq_one : (r139.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 false
    1 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 140 holds in the exact presentation group. -/
theorem r140_eq_one : (r140.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 false
    4 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 141 holds in the exact presentation group. -/
theorem r141_eq_one : (r141.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 false
    7 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 142 holds in the exact presentation group. -/
theorem r142_eq_one : (r142.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 false
    11 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 143 holds in the exact presentation group. -/
theorem r143_eq_one : (r143.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 true
    0 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 144 holds in the exact presentation group. -/
theorem r144_eq_one : (r144.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 true
    4 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 145 holds in the exact presentation group. -/
theorem r145_eq_one : (r145.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 true
    7 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 146 holds in the exact presentation group. -/
theorem r146_eq_one : (r146.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 true
    10 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 147 holds in the exact presentation group. -/
theorem r147_eq_one : (r147.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word46 true
    11 word46_eq_one (by decide +kernel)

/-- Trimmed scan word 148 holds in the exact presentation group. -/
theorem r148_eq_one : (r148.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 false
    5 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 149 holds in the exact presentation group. -/
theorem r149_eq_one : (r149.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 false
    11 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 150 holds in the exact presentation group. -/
theorem r150_eq_one : (r150.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 false
    13 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 151 holds in the exact presentation group. -/
theorem r151_eq_one : (r151.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 true
    0 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 152 holds in the exact presentation group. -/
theorem r152_eq_one : (r152.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 true
    2 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 153 holds in the exact presentation group. -/
theorem r153_eq_one : (r153.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word48 true
    8 word48_eq_one (by decide +kernel)

/-- Trimmed scan word 154 holds in the exact presentation group. -/
theorem r154_eq_one : (r154.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word52 false
    12 word52_eq_one (by decide +kernel)

/-- Trimmed scan word 155 holds in the exact presentation group. -/
theorem r155_eq_one : (r155.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word52 true
    4 word52_eq_one (by decide +kernel)

/-- Trimmed scan word 156 holds in the exact presentation group. -/
theorem r156_eq_one : (r156.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word70 false
    3 word70_eq_one (by decide +kernel)

/-- Trimmed scan word 157 holds in the exact presentation group. -/
theorem r157_eq_one : (r157.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word70 false
    7 word70_eq_one (by decide +kernel)

/-- Trimmed scan word 158 holds in the exact presentation group. -/
theorem r158_eq_one : (r158.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word70 true
    8 word70_eq_one (by decide +kernel)

/-- Trimmed scan word 159 holds in the exact presentation group. -/
theorem r159_eq_one : (r159.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word70 true
    12 word70_eq_one (by decide +kernel)

/-- Trimmed scan word 160 holds in the exact presentation group. -/
theorem r160_eq_one : (r160.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word75 false
    5 word75_eq_one (by decide +kernel)

/-- Trimmed scan word 161 holds in the exact presentation group. -/
theorem r161_eq_one : (r161.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word75 true
    10 word75_eq_one (by decide +kernel)

/-- Trimmed scan word 162 holds in the exact presentation group. -/
theorem r162_eq_one : (r162.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    0 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 163 holds in the exact presentation group. -/
theorem r163_eq_one : (r163.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    1 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 164 holds in the exact presentation group. -/
theorem r164_eq_one : (r164.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    2 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 165 holds in the exact presentation group. -/
theorem r165_eq_one : (r165.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    3 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 166 holds in the exact presentation group. -/
theorem r166_eq_one : (r166.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    7 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 167 holds in the exact presentation group. -/
theorem r167_eq_one : (r167.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    9 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 168 holds in the exact presentation group. -/
theorem r168_eq_one : (r168.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    10 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 169 holds in the exact presentation group. -/
theorem r169_eq_one : (r169.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 false
    11 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 170 holds in the exact presentation group. -/
theorem r170_eq_one : (r170.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    0 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 171 holds in the exact presentation group. -/
theorem r171_eq_one : (r171.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    1 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 172 holds in the exact presentation group. -/
theorem r172_eq_one : (r172.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    2 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 173 holds in the exact presentation group. -/
theorem r173_eq_one : (r173.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    4 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 174 holds in the exact presentation group. -/
theorem r174_eq_one : (r174.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    8 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 175 holds in the exact presentation group. -/
theorem r175_eq_one : (r175.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    9 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 176 holds in the exact presentation group. -/
theorem r176_eq_one : (r176.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    10 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 177 holds in the exact presentation group. -/
theorem r177_eq_one : (r177.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word76 true
    11 word76_eq_one (by decide +kernel)

/-- Trimmed scan word 178 holds in the exact presentation group. -/
theorem r178_eq_one : (r178.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word82 false
    6 word82_eq_one (by decide +kernel)

/-- Trimmed scan word 179 holds in the exact presentation group. -/
theorem r179_eq_one : (r179.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word82 false
    10 word82_eq_one (by decide +kernel)

/-- Trimmed scan word 180 holds in the exact presentation group. -/
theorem r180_eq_one : (r180.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word82 true
    3 word82_eq_one (by decide +kernel)

/-- Trimmed scan word 181 holds in the exact presentation group. -/
theorem r181_eq_one : (r181.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word82 true
    9 word82_eq_one (by decide +kernel)

/-- Trimmed scan word 182 holds in the exact presentation group. -/
theorem r182_eq_one : (r182.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word91 false
    6 word91_eq_one (by decide +kernel)

/-- Trimmed scan word 183 holds in the exact presentation group. -/
theorem r183_eq_one : (r183.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word91 false
    13 word91_eq_one (by decide +kernel)

/-- Trimmed scan word 184 holds in the exact presentation group. -/
theorem r184_eq_one : (r184.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word91 true
    2 word91_eq_one (by decide +kernel)

/-- Trimmed scan word 185 holds in the exact presentation group. -/
theorem r185_eq_one : (r185.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word91 true
    9 word91_eq_one (by decide +kernel)

/-- Trimmed scan word 186 holds in the exact presentation group. -/
theorem r186_eq_one : (r186.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 false
    8 word103_eq_one (by decide +kernel)

/-- Trimmed scan word 187 holds in the exact presentation group. -/
theorem r187_eq_one : (r187.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 false
    13 word103_eq_one (by decide +kernel)

/-- Trimmed scan word 188 holds in the exact presentation group. -/
theorem r188_eq_one : (r188.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 false
    15 word103_eq_one (by decide +kernel)

/-- Trimmed scan word 189 holds in the exact presentation group. -/
theorem r189_eq_one : (r189.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 true
    0 word103_eq_one (by decide +kernel)

/-- Trimmed scan word 190 holds in the exact presentation group. -/
theorem r190_eq_one : (r190.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 true
    2 word103_eq_one (by decide +kernel)

/-- Trimmed scan word 191 holds in the exact presentation group. -/
theorem r191_eq_one : (r191.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word103 true
    7 word103_eq_one (by decide +kernel)

@[expose]
def scanBlock8 : List (List (Fin 4)) :=
  [r128, r129, r130, r131, r132,
    r133, r134, r135, r136, r137,
    r138, r139, r140, r141, r142,
    r143]

theorem scanBlock8_eq_one : ∀ w ∈ scanBlock8, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock8, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r128_eq_one
  · exact r129_eq_one
  · exact r130_eq_one
  · exact r131_eq_one
  · exact r132_eq_one
  · exact r133_eq_one
  · exact r134_eq_one
  · exact r135_eq_one
  · exact r136_eq_one
  · exact r137_eq_one
  · exact r138_eq_one
  · exact r139_eq_one
  · exact r140_eq_one
  · exact r141_eq_one
  · exact r142_eq_one
  · exact r143_eq_one

@[expose]
def scanBlock9 : List (List (Fin 4)) :=
  [r144, r145, r146, r147, r148,
    r149, r150, r151, r152, r153,
    r154, r155, r156, r157, r158,
    r159]

theorem scanBlock9_eq_one : ∀ w ∈ scanBlock9, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock9, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r144_eq_one
  · exact r145_eq_one
  · exact r146_eq_one
  · exact r147_eq_one
  · exact r148_eq_one
  · exact r149_eq_one
  · exact r150_eq_one
  · exact r151_eq_one
  · exact r152_eq_one
  · exact r153_eq_one
  · exact r154_eq_one
  · exact r155_eq_one
  · exact r156_eq_one
  · exact r157_eq_one
  · exact r158_eq_one
  · exact r159_eq_one

@[expose]
def scanBlock10 : List (List (Fin 4)) :=
  [r160, r161, r162, r163, r164,
    r165, r166, r167, r168, r169,
    r170, r171, r172, r173, r174,
    r175]

theorem scanBlock10_eq_one : ∀ w ∈ scanBlock10, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock10, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r160_eq_one
  · exact r161_eq_one
  · exact r162_eq_one
  · exact r163_eq_one
  · exact r164_eq_one
  · exact r165_eq_one
  · exact r166_eq_one
  · exact r167_eq_one
  · exact r168_eq_one
  · exact r169_eq_one
  · exact r170_eq_one
  · exact r171_eq_one
  · exact r172_eq_one
  · exact r173_eq_one
  · exact r174_eq_one
  · exact r175_eq_one

@[expose]
def scanBlock11 : List (List (Fin 4)) :=
  [r176, r177, r178, r179, r180,
    r181, r182, r183, r184, r185,
    r186, r187, r188, r189, r190,
    r191]

theorem scanBlock11_eq_one : ∀ w ∈ scanBlock11, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock11, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r176_eq_one
  · exact r177_eq_one
  · exact r178_eq_one
  · exact r179_eq_one
  · exact r180_eq_one
  · exact r181_eq_one
  · exact r182_eq_one
  · exact r183_eq_one
  · exact r184_eq_one
  · exact r185_eq_one
  · exact r186_eq_one
  · exact r187_eq_one
  · exact r188_eq_one
  · exact r189_eq_one
  · exact r190_eq_one
  · exact r191_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
