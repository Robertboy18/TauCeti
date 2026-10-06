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

/-- Trimmed scan word 256 holds in the exact presentation group. -/
theorem r256_eq_one : (r256.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    3 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 257 holds in the exact presentation group. -/
theorem r257_eq_one : (r257.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    6 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 258 holds in the exact presentation group. -/
theorem r258_eq_one : (r258.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    10 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 259 holds in the exact presentation group. -/
theorem r259_eq_one : (r259.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    13 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 260 holds in the exact presentation group. -/
theorem r260_eq_one : (r260.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word135 true
    14 word135_eq_one (by decide +kernel)

/-- Trimmed scan word 261 holds in the exact presentation group. -/
theorem r261_eq_one : (r261.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    0 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 262 holds in the exact presentation group. -/
theorem r262_eq_one : (r262.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    3 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 263 holds in the exact presentation group. -/
theorem r263_eq_one : (r263.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    7 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 264 holds in the exact presentation group. -/
theorem r264_eq_one : (r264.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    8 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 265 holds in the exact presentation group. -/
theorem r265_eq_one : (r265.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    9 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 266 holds in the exact presentation group. -/
theorem r266_eq_one : (r266.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    10 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 267 holds in the exact presentation group. -/
theorem r267_eq_one : (r267.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    11 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 268 holds in the exact presentation group. -/
theorem r268_eq_one : (r268.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    13 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 269 holds in the exact presentation group. -/
theorem r269_eq_one : (r269.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 false
    14 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 270 holds in the exact presentation group. -/
theorem r270_eq_one : (r270.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    1 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 271 holds in the exact presentation group. -/
theorem r271_eq_one : (r271.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    2 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 272 holds in the exact presentation group. -/
theorem r272_eq_one : (r272.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    3 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 273 holds in the exact presentation group. -/
theorem r273_eq_one : (r273.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    4 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 274 holds in the exact presentation group. -/
theorem r274_eq_one : (r274.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    5 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 275 holds in the exact presentation group. -/
theorem r275_eq_one : (r275.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    6 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 276 holds in the exact presentation group. -/
theorem r276_eq_one : (r276.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    7 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 277 holds in the exact presentation group. -/
theorem r277_eq_one : (r277.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    9 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 278 holds in the exact presentation group. -/
theorem r278_eq_one : (r278.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    11 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 279 holds in the exact presentation group. -/
theorem r279_eq_one : (r279.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    13 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 280 holds in the exact presentation group. -/
theorem r280_eq_one : (r280.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word146 true
    14 word146_eq_one (by decide +kernel)

/-- Trimmed scan word 281 holds in the exact presentation group. -/
theorem r281_eq_one : (r281.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    0 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 282 holds in the exact presentation group. -/
theorem r282_eq_one : (r282.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    1 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 283 holds in the exact presentation group. -/
theorem r283_eq_one : (r283.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    2 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 284 holds in the exact presentation group. -/
theorem r284_eq_one : (r284.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    4 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 285 holds in the exact presentation group. -/
theorem r285_eq_one : (r285.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    9 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 286 holds in the exact presentation group. -/
theorem r286_eq_one : (r286.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 false
    14 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 287 holds in the exact presentation group. -/
theorem r287_eq_one : (r287.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    1 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 288 holds in the exact presentation group. -/
theorem r288_eq_one : (r288.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    2 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 289 holds in the exact presentation group. -/
theorem r289_eq_one : (r289.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    3 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 290 holds in the exact presentation group. -/
theorem r290_eq_one : (r290.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    4 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 291 holds in the exact presentation group. -/
theorem r291_eq_one : (r291.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    6 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 292 holds in the exact presentation group. -/
theorem r292_eq_one : (r292.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    9 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 293 holds in the exact presentation group. -/
theorem r293_eq_one : (r293.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    10 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 294 holds in the exact presentation group. -/
theorem r294_eq_one : (r294.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    11 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 295 holds in the exact presentation group. -/
theorem r295_eq_one : (r295.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    13 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 296 holds in the exact presentation group. -/
theorem r296_eq_one : (r296.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word149 true
    14 word149_eq_one (by decide +kernel)

/-- Trimmed scan word 297 holds in the exact presentation group. -/
theorem r297_eq_one : (r297.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    1 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 298 holds in the exact presentation group. -/
theorem r298_eq_one : (r298.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    2 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 299 holds in the exact presentation group. -/
theorem r299_eq_one : (r299.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    3 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 300 holds in the exact presentation group. -/
theorem r300_eq_one : (r300.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    6 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 301 holds in the exact presentation group. -/
theorem r301_eq_one : (r301.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    7 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 302 holds in the exact presentation group. -/
theorem r302_eq_one : (r302.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    8 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 303 holds in the exact presentation group. -/
theorem r303_eq_one : (r303.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    10 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 304 holds in the exact presentation group. -/
theorem r304_eq_one : (r304.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    11 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 305 holds in the exact presentation group. -/
theorem r305_eq_one : (r305.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    12 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 306 holds in the exact presentation group. -/
theorem r306_eq_one : (r306.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    13 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 307 holds in the exact presentation group. -/
theorem r307_eq_one : (r307.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 false
    14 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 308 holds in the exact presentation group. -/
theorem r308_eq_one : (r308.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    0 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 309 holds in the exact presentation group. -/
theorem r309_eq_one : (r309.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    1 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 310 holds in the exact presentation group. -/
theorem r310_eq_one : (r310.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    2 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 311 holds in the exact presentation group. -/
theorem r311_eq_one : (r311.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    3 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 312 holds in the exact presentation group. -/
theorem r312_eq_one : (r312.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    6 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 313 holds in the exact presentation group. -/
theorem r313_eq_one : (r313.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    7 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 314 holds in the exact presentation group. -/
theorem r314_eq_one : (r314.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    11 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 315 holds in the exact presentation group. -/
theorem r315_eq_one : (r315.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    12 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 316 holds in the exact presentation group. -/
theorem r316_eq_one : (r316.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word175 true
    13 word175_eq_one (by decide +kernel)

/-- Trimmed scan word 317 holds in the exact presentation group. -/
theorem r317_eq_one : (r317.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    0 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 318 holds in the exact presentation group. -/
theorem r318_eq_one : (r318.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    1 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 319 holds in the exact presentation group. -/
theorem r319_eq_one : (r319.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    2 word178_eq_one (by decide +kernel)

@[expose]
def scanBlock16 : List (List (Fin 4)) :=
  [r256, r257, r258, r259, r260,
    r261, r262, r263, r264, r265,
    r266, r267, r268, r269, r270,
    r271]

theorem scanBlock16_eq_one : ∀ w ∈ scanBlock16, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock16, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r256_eq_one
  · exact r257_eq_one
  · exact r258_eq_one
  · exact r259_eq_one
  · exact r260_eq_one
  · exact r261_eq_one
  · exact r262_eq_one
  · exact r263_eq_one
  · exact r264_eq_one
  · exact r265_eq_one
  · exact r266_eq_one
  · exact r267_eq_one
  · exact r268_eq_one
  · exact r269_eq_one
  · exact r270_eq_one
  · exact r271_eq_one

@[expose]
def scanBlock17 : List (List (Fin 4)) :=
  [r272, r273, r274, r275, r276,
    r277, r278, r279, r280, r281,
    r282, r283, r284, r285, r286,
    r287]

theorem scanBlock17_eq_one : ∀ w ∈ scanBlock17, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock17, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r272_eq_one
  · exact r273_eq_one
  · exact r274_eq_one
  · exact r275_eq_one
  · exact r276_eq_one
  · exact r277_eq_one
  · exact r278_eq_one
  · exact r279_eq_one
  · exact r280_eq_one
  · exact r281_eq_one
  · exact r282_eq_one
  · exact r283_eq_one
  · exact r284_eq_one
  · exact r285_eq_one
  · exact r286_eq_one
  · exact r287_eq_one

@[expose]
def scanBlock18 : List (List (Fin 4)) :=
  [r288, r289, r290, r291, r292,
    r293, r294, r295, r296, r297,
    r298, r299, r300, r301, r302,
    r303]

theorem scanBlock18_eq_one : ∀ w ∈ scanBlock18, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock18, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r288_eq_one
  · exact r289_eq_one
  · exact r290_eq_one
  · exact r291_eq_one
  · exact r292_eq_one
  · exact r293_eq_one
  · exact r294_eq_one
  · exact r295_eq_one
  · exact r296_eq_one
  · exact r297_eq_one
  · exact r298_eq_one
  · exact r299_eq_one
  · exact r300_eq_one
  · exact r301_eq_one
  · exact r302_eq_one
  · exact r303_eq_one

@[expose]
def scanBlock19 : List (List (Fin 4)) :=
  [r304, r305, r306, r307, r308,
    r309, r310, r311, r312, r313,
    r314, r315, r316, r317, r318,
    r319]

theorem scanBlock19_eq_one : ∀ w ∈ scanBlock19, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock19, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r304_eq_one
  · exact r305_eq_one
  · exact r306_eq_one
  · exact r307_eq_one
  · exact r308_eq_one
  · exact r309_eq_one
  · exact r310_eq_one
  · exact r311_eq_one
  · exact r312_eq_one
  · exact r313_eq_one
  · exact r314_eq_one
  · exact r315_eq_one
  · exact r316_eq_one
  · exact r317_eq_one
  · exact r318_eq_one
  · exact r319_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
