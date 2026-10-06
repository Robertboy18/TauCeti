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

/-- Trimmed scan word 192 holds in the exact presentation group. -/
theorem r192_eq_one : (r192.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 false
    2 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 193 holds in the exact presentation group. -/
theorem r193_eq_one : (r193.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 false
    4 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 194 holds in the exact presentation group. -/
theorem r194_eq_one : (r194.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 false
    5 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 195 holds in the exact presentation group. -/
theorem r195_eq_one : (r195.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 false
    14 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 196 holds in the exact presentation group. -/
theorem r196_eq_one : (r196.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 true
    0 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 197 holds in the exact presentation group. -/
theorem r197_eq_one : (r197.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 true
    9 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 198 holds in the exact presentation group. -/
theorem r198_eq_one : (r198.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 true
    10 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 199 holds in the exact presentation group. -/
theorem r199_eq_one : (r199.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word112 true
    12 word112_eq_one (by decide +kernel)

/-- Trimmed scan word 200 holds in the exact presentation group. -/
theorem r200_eq_one : (r200.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 false
    4 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 201 holds in the exact presentation group. -/
theorem r201_eq_one : (r201.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 false
    8 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 202 holds in the exact presentation group. -/
theorem r202_eq_one : (r202.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 false
    13 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 203 holds in the exact presentation group. -/
theorem r203_eq_one : (r203.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 false
    14 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 204 holds in the exact presentation group. -/
theorem r204_eq_one : (r204.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 true
    0 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 205 holds in the exact presentation group. -/
theorem r205_eq_one : (r205.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 true
    6 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 206 holds in the exact presentation group. -/
theorem r206_eq_one : (r206.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word119 true
    10 word119_eq_one (by decide +kernel)

/-- Trimmed scan word 207 holds in the exact presentation group. -/
theorem r207_eq_one : (r207.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word121 false
    1 word121_eq_one (by decide +kernel)

/-- Trimmed scan word 208 holds in the exact presentation group. -/
theorem r208_eq_one : (r208.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word121 false
    4 word121_eq_one (by decide +kernel)

/-- Trimmed scan word 209 holds in the exact presentation group. -/
theorem r209_eq_one : (r209.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word121 false
    14 word121_eq_one (by decide +kernel)

/-- Trimmed scan word 210 holds in the exact presentation group. -/
theorem r210_eq_one : (r210.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word121 true
    11 word121_eq_one (by decide +kernel)

/-- Trimmed scan word 211 holds in the exact presentation group. -/
theorem r211_eq_one : (r211.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word121 true
    14 word121_eq_one (by decide +kernel)

/-- Trimmed scan word 212 holds in the exact presentation group. -/
theorem r212_eq_one : (r212.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 false
    2 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 213 holds in the exact presentation group. -/
theorem r213_eq_one : (r213.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 false
    5 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 214 holds in the exact presentation group. -/
theorem r214_eq_one : (r214.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 false
    9 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 215 holds in the exact presentation group. -/
theorem r215_eq_one : (r215.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 false
    12 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 216 holds in the exact presentation group. -/
theorem r216_eq_one : (r216.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 false
    13 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 217 holds in the exact presentation group. -/
theorem r217_eq_one : (r217.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 true
    2 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 218 holds in the exact presentation group. -/
theorem r218_eq_one : (r218.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 true
    5 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 219 holds in the exact presentation group. -/
theorem r219_eq_one : (r219.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word124 true
    9 word124_eq_one (by decide +kernel)

/-- Trimmed scan word 220 holds in the exact presentation group. -/
theorem r220_eq_one : (r220.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    0 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 221 holds in the exact presentation group. -/
theorem r221_eq_one : (r221.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    5 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 222 holds in the exact presentation group. -/
theorem r222_eq_one : (r222.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    8 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 223 holds in the exact presentation group. -/
theorem r223_eq_one : (r223.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    9 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 224 holds in the exact presentation group. -/
theorem r224_eq_one : (r224.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    11 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 225 holds in the exact presentation group. -/
theorem r225_eq_one : (r225.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 false
    12 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 226 holds in the exact presentation group. -/
theorem r226_eq_one : (r226.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    1 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 227 holds in the exact presentation group. -/
theorem r227_eq_one : (r227.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    2 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 228 holds in the exact presentation group. -/
theorem r228_eq_one : (r228.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    4 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 229 holds in the exact presentation group. -/
theorem r229_eq_one : (r229.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    5 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 230 holds in the exact presentation group. -/
theorem r230_eq_one : (r230.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    8 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 231 holds in the exact presentation group. -/
theorem r231_eq_one : (r231.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    11 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 232 holds in the exact presentation group. -/
theorem r232_eq_one : (r232.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word125 true
    13 word125_eq_one (by decide +kernel)

/-- Trimmed scan word 233 holds in the exact presentation group. -/
theorem r233_eq_one : (r233.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    1 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 234 holds in the exact presentation group. -/
theorem r234_eq_one : (r234.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    2 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 235 holds in the exact presentation group. -/
theorem r235_eq_one : (r235.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    3 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 236 holds in the exact presentation group. -/
theorem r236_eq_one : (r236.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    5 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 237 holds in the exact presentation group. -/
theorem r237_eq_one : (r237.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    9 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 238 holds in the exact presentation group. -/
theorem r238_eq_one : (r238.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    12 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 239 holds in the exact presentation group. -/
theorem r239_eq_one : (r239.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 false
    13 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 240 holds in the exact presentation group. -/
theorem r240_eq_one : (r240.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    1 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 241 holds in the exact presentation group. -/
theorem r241_eq_one : (r241.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    3 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 242 holds in the exact presentation group. -/
theorem r242_eq_one : (r242.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    5 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 243 holds in the exact presentation group. -/
theorem r243_eq_one : (r243.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    6 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 244 holds in the exact presentation group. -/
theorem r244_eq_one : (r244.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    8 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 245 holds in the exact presentation group. -/
theorem r245_eq_one : (r245.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    10 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 246 holds in the exact presentation group. -/
theorem r246_eq_one : (r246.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    12 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 247 holds in the exact presentation group. -/
theorem r247_eq_one : (r247.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word129 true
    13 word129_eq_one (by decide +kernel)

/-- Trimmed scan word 248 holds in the exact presentation group. -/
theorem r248_eq_one : (r248.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    0 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 249 holds in the exact presentation group. -/
theorem r249_eq_one : (r249.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    1 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 250 holds in the exact presentation group. -/
theorem r250_eq_one : (r250.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    4 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 251 holds in the exact presentation group. -/
theorem r251_eq_one : (r251.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    9 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 252 holds in the exact presentation group. -/
theorem r252_eq_one : (r252.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    11 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 253 holds in the exact presentation group. -/
theorem r253_eq_one : (r253.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 false
    12 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 254 holds in the exact presentation group. -/
theorem r254_eq_one : (r254.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    1 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 255 holds in the exact presentation group. -/
theorem r255_eq_one : (r255.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    2 word135_eq_one (by decide +kernel)

@[expose]
def scanBlock12 : List (List (Fin 4)) :=
  [r192, r193, r194, r195, r196,
    r197, r198, r199, r200, r201,
    r202, r203, r204, r205, r206,
    r207]

theorem scanBlock12_eq_one : ∀ w ∈ scanBlock12, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock12, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r192_eq_one
  · exact r193_eq_one
  · exact r194_eq_one
  · exact r195_eq_one
  · exact r196_eq_one
  · exact r197_eq_one
  · exact r198_eq_one
  · exact r199_eq_one
  · exact r200_eq_one
  · exact r201_eq_one
  · exact r202_eq_one
  · exact r203_eq_one
  · exact r204_eq_one
  · exact r205_eq_one
  · exact r206_eq_one
  · exact r207_eq_one

@[expose]
def scanBlock13 : List (List (Fin 4)) :=
  [r208, r209, r210, r211, r212,
    r213, r214, r215, r216, r217,
    r218, r219, r220, r221, r222,
    r223]

theorem scanBlock13_eq_one : ∀ w ∈ scanBlock13, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock13, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r208_eq_one
  · exact r209_eq_one
  · exact r210_eq_one
  · exact r211_eq_one
  · exact r212_eq_one
  · exact r213_eq_one
  · exact r214_eq_one
  · exact r215_eq_one
  · exact r216_eq_one
  · exact r217_eq_one
  · exact r218_eq_one
  · exact r219_eq_one
  · exact r220_eq_one
  · exact r221_eq_one
  · exact r222_eq_one
  · exact r223_eq_one

@[expose]
def scanBlock14 : List (List (Fin 4)) :=
  [r224, r225, r226, r227, r228,
    r229, r230, r231, r232, r233,
    r234, r235, r236, r237, r238,
    r239]

theorem scanBlock14_eq_one : ∀ w ∈ scanBlock14, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock14, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r224_eq_one
  · exact r225_eq_one
  · exact r226_eq_one
  · exact r227_eq_one
  · exact r228_eq_one
  · exact r229_eq_one
  · exact r230_eq_one
  · exact r231_eq_one
  · exact r232_eq_one
  · exact r233_eq_one
  · exact r234_eq_one
  · exact r235_eq_one
  · exact r236_eq_one
  · exact r237_eq_one
  · exact r238_eq_one
  · exact r239_eq_one

@[expose]
def scanBlock15 : List (List (Fin 4)) :=
  [r240, r241, r242, r243, r244,
    r245, r246, r247, r248, r249,
    r250, r251, r252, r253, r254,
    r255]

theorem scanBlock15_eq_one : ∀ w ∈ scanBlock15, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock15, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r240_eq_one
  · exact r241_eq_one
  · exact r242_eq_one
  · exact r243_eq_one
  · exact r244_eq_one
  · exact r245_eq_one
  · exact r246_eq_one
  · exact r247_eq_one
  · exact r248_eq_one
  · exact r249_eq_one
  · exact r250_eq_one
  · exact r251_eq_one
  · exact r252_eq_one
  · exact r253_eq_one
  · exact r254_eq_one
  · exact r255_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
