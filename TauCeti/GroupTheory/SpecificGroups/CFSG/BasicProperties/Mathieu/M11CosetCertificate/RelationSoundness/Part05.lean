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

/-- Trimmed scan word 320 holds in the exact presentation group. -/
theorem r320_eq_one : (r320.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    3 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 321 holds in the exact presentation group. -/
theorem r321_eq_one : (r321.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    4 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 322 holds in the exact presentation group. -/
theorem r322_eq_one : (r322.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    5 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 323 holds in the exact presentation group. -/
theorem r323_eq_one : (r323.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    6 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 324 holds in the exact presentation group. -/
theorem r324_eq_one : (r324.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    7 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 325 holds in the exact presentation group. -/
theorem r325_eq_one : (r325.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    10 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 326 holds in the exact presentation group. -/
theorem r326_eq_one : (r326.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    11 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 327 holds in the exact presentation group. -/
theorem r327_eq_one : (r327.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    12 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 328 holds in the exact presentation group. -/
theorem r328_eq_one : (r328.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 false
    13 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 329 holds in the exact presentation group. -/
theorem r329_eq_one : (r329.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    0 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 330 holds in the exact presentation group. -/
theorem r330_eq_one : (r330.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    1 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 331 holds in the exact presentation group. -/
theorem r331_eq_one : (r331.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    2 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 332 holds in the exact presentation group. -/
theorem r332_eq_one : (r332.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    3 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 333 holds in the exact presentation group. -/
theorem r333_eq_one : (r333.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    4 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 334 holds in the exact presentation group. -/
theorem r334_eq_one : (r334.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    5 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 335 holds in the exact presentation group. -/
theorem r335_eq_one : (r335.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    6 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 336 holds in the exact presentation group. -/
theorem r336_eq_one : (r336.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    8 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 337 holds in the exact presentation group. -/
theorem r337_eq_one : (r337.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    9 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 338 holds in the exact presentation group. -/
theorem r338_eq_one : (r338.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    10 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 339 holds in the exact presentation group. -/
theorem r339_eq_one : (r339.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    11 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 340 holds in the exact presentation group. -/
theorem r340_eq_one : (r340.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    12 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 341 holds in the exact presentation group. -/
theorem r341_eq_one : (r341.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word178 true
    13 word178_eq_one (by decide +kernel)

/-- Trimmed scan word 342 holds in the exact presentation group. -/
theorem r342_eq_one : (r342.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    0 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 343 holds in the exact presentation group. -/
theorem r343_eq_one : (r343.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    1 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 344 holds in the exact presentation group. -/
theorem r344_eq_one : (r344.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    2 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 345 holds in the exact presentation group. -/
theorem r345_eq_one : (r345.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    3 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 346 holds in the exact presentation group. -/
theorem r346_eq_one : (r346.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    4 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 347 holds in the exact presentation group. -/
theorem r347_eq_one : (r347.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    5 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 348 holds in the exact presentation group. -/
theorem r348_eq_one : (r348.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    6 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 349 holds in the exact presentation group. -/
theorem r349_eq_one : (r349.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    7 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 350 holds in the exact presentation group. -/
theorem r350_eq_one : (r350.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    8 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 351 holds in the exact presentation group. -/
theorem r351_eq_one : (r351.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    10 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 352 holds in the exact presentation group. -/
theorem r352_eq_one : (r352.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    11 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 353 holds in the exact presentation group. -/
theorem r353_eq_one : (r353.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    12 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 354 holds in the exact presentation group. -/
theorem r354_eq_one : (r354.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    13 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 355 holds in the exact presentation group. -/
theorem r355_eq_one : (r355.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 false
    14 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 356 holds in the exact presentation group. -/
theorem r356_eq_one : (r356.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    0 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 357 holds in the exact presentation group. -/
theorem r357_eq_one : (r357.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    3 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 358 holds in the exact presentation group. -/
theorem r358_eq_one : (r358.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    5 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 359 holds in the exact presentation group. -/
theorem r359_eq_one : (r359.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    6 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 360 holds in the exact presentation group. -/
theorem r360_eq_one : (r360.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    7 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 361 holds in the exact presentation group. -/
theorem r361_eq_one : (r361.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    8 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 362 holds in the exact presentation group. -/
theorem r362_eq_one : (r362.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    9 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 363 holds in the exact presentation group. -/
theorem r363_eq_one : (r363.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    10 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 364 holds in the exact presentation group. -/
theorem r364_eq_one : (r364.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    11 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 365 holds in the exact presentation group. -/
theorem r365_eq_one : (r365.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    12 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 366 holds in the exact presentation group. -/
theorem r366_eq_one : (r366.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    13 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 367 holds in the exact presentation group. -/
theorem r367_eq_one : (r367.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    14 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 368 holds in the exact presentation group. -/
theorem r368_eq_one : (r368.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word182 true
    15 word182_eq_one (by decide +kernel)

/-- Trimmed scan word 369 holds in the exact presentation group. -/
theorem r369_eq_one : (r369.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    0 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 370 holds in the exact presentation group. -/
theorem r370_eq_one : (r370.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    1 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 371 holds in the exact presentation group. -/
theorem r371_eq_one : (r371.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    2 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 372 holds in the exact presentation group. -/
theorem r372_eq_one : (r372.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    3 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 373 holds in the exact presentation group. -/
theorem r373_eq_one : (r373.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    4 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 374 holds in the exact presentation group. -/
theorem r374_eq_one : (r374.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    5 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 375 holds in the exact presentation group. -/
theorem r375_eq_one : (r375.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    6 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 376 holds in the exact presentation group. -/
theorem r376_eq_one : (r376.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    7 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 377 holds in the exact presentation group. -/
theorem r377_eq_one : (r377.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    8 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 378 holds in the exact presentation group. -/
theorem r378_eq_one : (r378.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    10 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 379 holds in the exact presentation group. -/
theorem r379_eq_one : (r379.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    12 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 380 holds in the exact presentation group. -/
theorem r380_eq_one : (r380.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    13 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 381 holds in the exact presentation group. -/
theorem r381_eq_one : (r381.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    14 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 382 holds in the exact presentation group. -/
theorem r382_eq_one : (r382.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 false
    15 word184_eq_one (by decide +kernel)

/-- Trimmed scan word 383 holds in the exact presentation group. -/
theorem r383_eq_one : (r383.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word184 true
    0 word184_eq_one (by decide +kernel)

@[expose]
def scanBlock20 : List (List (Fin 4)) :=
  [r320, r321, r322, r323, r324,
    r325, r326, r327, r328, r329,
    r330, r331, r332, r333, r334,
    r335]

theorem scanBlock20_eq_one : ∀ w ∈ scanBlock20, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock20, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r320_eq_one
  · exact r321_eq_one
  · exact r322_eq_one
  · exact r323_eq_one
  · exact r324_eq_one
  · exact r325_eq_one
  · exact r326_eq_one
  · exact r327_eq_one
  · exact r328_eq_one
  · exact r329_eq_one
  · exact r330_eq_one
  · exact r331_eq_one
  · exact r332_eq_one
  · exact r333_eq_one
  · exact r334_eq_one
  · exact r335_eq_one

@[expose]
def scanBlock21 : List (List (Fin 4)) :=
  [r336, r337, r338, r339, r340,
    r341, r342, r343, r344, r345,
    r346, r347, r348, r349, r350,
    r351]

theorem scanBlock21_eq_one : ∀ w ∈ scanBlock21, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock21, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r336_eq_one
  · exact r337_eq_one
  · exact r338_eq_one
  · exact r339_eq_one
  · exact r340_eq_one
  · exact r341_eq_one
  · exact r342_eq_one
  · exact r343_eq_one
  · exact r344_eq_one
  · exact r345_eq_one
  · exact r346_eq_one
  · exact r347_eq_one
  · exact r348_eq_one
  · exact r349_eq_one
  · exact r350_eq_one
  · exact r351_eq_one

@[expose]
def scanBlock22 : List (List (Fin 4)) :=
  [r352, r353, r354, r355, r356,
    r357, r358, r359, r360, r361,
    r362, r363, r364, r365, r366,
    r367]

theorem scanBlock22_eq_one : ∀ w ∈ scanBlock22, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock22, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r352_eq_one
  · exact r353_eq_one
  · exact r354_eq_one
  · exact r355_eq_one
  · exact r356_eq_one
  · exact r357_eq_one
  · exact r358_eq_one
  · exact r359_eq_one
  · exact r360_eq_one
  · exact r361_eq_one
  · exact r362_eq_one
  · exact r363_eq_one
  · exact r364_eq_one
  · exact r365_eq_one
  · exact r366_eq_one
  · exact r367_eq_one

@[expose]
def scanBlock23 : List (List (Fin 4)) :=
  [r368, r369, r370, r371, r372,
    r373, r374, r375, r376, r377,
    r378, r379, r380, r381, r382,
    r383]

theorem scanBlock23_eq_one : ∀ w ∈ scanBlock23, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock23, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r368_eq_one
  · exact r369_eq_one
  · exact r370_eq_one
  · exact r371_eq_one
  · exact r372_eq_one
  · exact r373_eq_one
  · exact r374_eq_one
  · exact r375_eq_one
  · exact r376_eq_one
  · exact r377_eq_one
  · exact r378_eq_one
  · exact r379_eq_one
  · exact r380_eq_one
  · exact r381_eq_one
  · exact r382_eq_one
  · exact r383_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
