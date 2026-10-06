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

/-- Trimmed scan word 512 holds in the exact presentation group. -/
theorem r512_eq_one : (r512.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    12 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 513 holds in the exact presentation group. -/
theorem r513_eq_one : (r513.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    13 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 514 holds in the exact presentation group. -/
theorem r514_eq_one : (r514.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    14 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 515 holds in the exact presentation group. -/
theorem r515_eq_one : (r515.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word227 true
    15 word227_eq_one (by decide +kernel)

/-- Trimmed scan word 516 holds in the exact presentation group. -/
theorem r516_eq_one : (r516.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    0 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 517 holds in the exact presentation group. -/
theorem r517_eq_one : (r517.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    1 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 518 holds in the exact presentation group. -/
theorem r518_eq_one : (r518.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    2 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 519 holds in the exact presentation group. -/
theorem r519_eq_one : (r519.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    3 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 520 holds in the exact presentation group. -/
theorem r520_eq_one : (r520.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    4 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 521 holds in the exact presentation group. -/
theorem r521_eq_one : (r521.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    5 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 522 holds in the exact presentation group. -/
theorem r522_eq_one : (r522.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    6 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 523 holds in the exact presentation group. -/
theorem r523_eq_one : (r523.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    7 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 524 holds in the exact presentation group. -/
theorem r524_eq_one : (r524.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    8 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 525 holds in the exact presentation group. -/
theorem r525_eq_one : (r525.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    9 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 526 holds in the exact presentation group. -/
theorem r526_eq_one : (r526.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    10 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 527 holds in the exact presentation group. -/
theorem r527_eq_one : (r527.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    11 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 528 holds in the exact presentation group. -/
theorem r528_eq_one : (r528.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    12 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 529 holds in the exact presentation group. -/
theorem r529_eq_one : (r529.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    13 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 530 holds in the exact presentation group. -/
theorem r530_eq_one : (r530.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    14 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 531 holds in the exact presentation group. -/
theorem r531_eq_one : (r531.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 false
    15 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 532 holds in the exact presentation group. -/
theorem r532_eq_one : (r532.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    0 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 533 holds in the exact presentation group. -/
theorem r533_eq_one : (r533.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    1 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 534 holds in the exact presentation group. -/
theorem r534_eq_one : (r534.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    2 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 535 holds in the exact presentation group. -/
theorem r535_eq_one : (r535.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    3 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 536 holds in the exact presentation group. -/
theorem r536_eq_one : (r536.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    4 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 537 holds in the exact presentation group. -/
theorem r537_eq_one : (r537.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    5 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 538 holds in the exact presentation group. -/
theorem r538_eq_one : (r538.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    6 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 539 holds in the exact presentation group. -/
theorem r539_eq_one : (r539.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    9 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 540 holds in the exact presentation group. -/
theorem r540_eq_one : (r540.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    12 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 541 holds in the exact presentation group. -/
theorem r541_eq_one : (r541.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word231 true
    13 word231_eq_one (by decide +kernel)

/-- Trimmed scan word 542 holds in the exact presentation group. -/
theorem r542_eq_one : (r542.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word238 false
    15 word238_eq_one (by decide +kernel)

/-- Trimmed scan word 543 holds in the exact presentation group. -/
theorem r543_eq_one : (r543.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word435 false
    8 word435_eq_one (by decide +kernel)

/-- Trimmed scan word 544 holds in the exact presentation group. -/
theorem r544_eq_one : (r544.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word435 false
    10 word435_eq_one (by decide +kernel)

/-- Trimmed scan word 545 holds in the exact presentation group. -/
theorem r545_eq_one : (r545.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word435 true
    4 word435_eq_one (by decide +kernel)

/-- Trimmed scan word 546 holds in the exact presentation group. -/
theorem r546_eq_one : (r546.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word435 true
    6 word435_eq_one (by decide +kernel)

/-- Trimmed scan word 547 holds in the exact presentation group. -/
theorem r547_eq_one : (r547.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 false
    1 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 548 holds in the exact presentation group. -/
theorem r548_eq_one : (r548.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 false
    3 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 549 holds in the exact presentation group. -/
theorem r549_eq_one : (r549.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 false
    5 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 550 holds in the exact presentation group. -/
theorem r550_eq_one : (r550.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 false
    10 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 551 holds in the exact presentation group. -/
theorem r551_eq_one : (r551.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 false
    13 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 552 holds in the exact presentation group. -/
theorem r552_eq_one : (r552.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 true
    0 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 553 holds in the exact presentation group. -/
theorem r553_eq_one : (r553.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 true
    3 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 554 holds in the exact presentation group. -/
theorem r554_eq_one : (r554.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 true
    8 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 555 holds in the exact presentation group. -/
theorem r555_eq_one : (r555.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 true
    10 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 556 holds in the exact presentation group. -/
theorem r556_eq_one : (r556.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word437 true
    12 word437_eq_one (by decide +kernel)

/-- Trimmed scan word 557 holds in the exact presentation group. -/
theorem r557_eq_one : (r557.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word443 false
    10 word443_eq_one (by decide +kernel)

/-- Trimmed scan word 558 holds in the exact presentation group. -/
theorem r558_eq_one : (r558.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word443 true
    5 word443_eq_one (by decide +kernel)

/-- Trimmed scan word 559 holds in the exact presentation group. -/
theorem r559_eq_one : (r559.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word448 false
    12 word448_eq_one (by decide +kernel)

/-- Trimmed scan word 560 holds in the exact presentation group. -/
theorem r560_eq_one : (r560.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word448 true
    2 word448_eq_one (by decide +kernel)

/-- Trimmed scan word 561 holds in the exact presentation group. -/
theorem r561_eq_one : (r561.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word449 false
    10 word449_eq_one (by decide +kernel)

/-- Trimmed scan word 562 holds in the exact presentation group. -/
theorem r562_eq_one : (r562.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word449 true
    5 word449_eq_one (by decide +kernel)

/-- Trimmed scan word 563 holds in the exact presentation group. -/
theorem r563_eq_one : (r563.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word451 false
    9 word451_eq_one (by decide +kernel)

/-- Trimmed scan word 564 holds in the exact presentation group. -/
theorem r564_eq_one : (r564.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word451 true
    5 word451_eq_one (by decide +kernel)

/-- Trimmed scan word 565 holds in the exact presentation group. -/
theorem r565_eq_one : (r565.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word461 false
    4 word461_eq_one (by decide +kernel)

/-- Trimmed scan word 566 holds in the exact presentation group. -/
theorem r566_eq_one : (r566.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word461 true
    11 word461_eq_one (by decide +kernel)

/-- Trimmed scan word 567 holds in the exact presentation group. -/
theorem r567_eq_one : (r567.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word462 false
    9 word462_eq_one (by decide +kernel)

/-- Trimmed scan word 568 holds in the exact presentation group. -/
theorem r568_eq_one : (r568.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word462 false
    10 word462_eq_one (by decide +kernel)

/-- Trimmed scan word 569 holds in the exact presentation group. -/
theorem r569_eq_one : (r569.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word462 true
    3 word462_eq_one (by decide +kernel)

/-- Trimmed scan word 570 holds in the exact presentation group. -/
theorem r570_eq_one : (r570.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word462 true
    4 word462_eq_one (by decide +kernel)

/-- Trimmed scan word 571 holds in the exact presentation group. -/
theorem r571_eq_one : (r571.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word476 false
    8 word476_eq_one (by decide +kernel)

/-- Trimmed scan word 572 holds in the exact presentation group. -/
theorem r572_eq_one : (r572.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word476 false
    14 word476_eq_one (by decide +kernel)

/-- Trimmed scan word 573 holds in the exact presentation group. -/
theorem r573_eq_one : (r573.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word476 true
    0 word476_eq_one (by decide +kernel)

/-- Trimmed scan word 574 holds in the exact presentation group. -/
theorem r574_eq_one : (r574.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word476 true
    6 word476_eq_one (by decide +kernel)

/-- Trimmed scan word 575 holds in the exact presentation group. -/
theorem r575_eq_one : (r575.map letterValue).prod = 1 :=
  scan_variant_eq_one _ word478 false
    5 word478_eq_one (by decide +kernel)

@[expose]
def scanBlock32 : List (List (Fin 4)) :=
  [r512, r513, r514, r515, r516,
    r517, r518, r519, r520, r521,
    r522, r523, r524, r525, r526,
    r527]

theorem scanBlock32_eq_one : ∀ w ∈ scanBlock32, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock32, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r512_eq_one
  · exact r513_eq_one
  · exact r514_eq_one
  · exact r515_eq_one
  · exact r516_eq_one
  · exact r517_eq_one
  · exact r518_eq_one
  · exact r519_eq_one
  · exact r520_eq_one
  · exact r521_eq_one
  · exact r522_eq_one
  · exact r523_eq_one
  · exact r524_eq_one
  · exact r525_eq_one
  · exact r526_eq_one
  · exact r527_eq_one

@[expose]
def scanBlock33 : List (List (Fin 4)) :=
  [r528, r529, r530, r531, r532,
    r533, r534, r535, r536, r537,
    r538, r539, r540, r541, r542,
    r543]

theorem scanBlock33_eq_one : ∀ w ∈ scanBlock33, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock33, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r528_eq_one
  · exact r529_eq_one
  · exact r530_eq_one
  · exact r531_eq_one
  · exact r532_eq_one
  · exact r533_eq_one
  · exact r534_eq_one
  · exact r535_eq_one
  · exact r536_eq_one
  · exact r537_eq_one
  · exact r538_eq_one
  · exact r539_eq_one
  · exact r540_eq_one
  · exact r541_eq_one
  · exact r542_eq_one
  · exact r543_eq_one

@[expose]
def scanBlock34 : List (List (Fin 4)) :=
  [r544, r545, r546, r547, r548,
    r549, r550, r551, r552, r553,
    r554, r555, r556, r557, r558,
    r559]

theorem scanBlock34_eq_one : ∀ w ∈ scanBlock34, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock34, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r544_eq_one
  · exact r545_eq_one
  · exact r546_eq_one
  · exact r547_eq_one
  · exact r548_eq_one
  · exact r549_eq_one
  · exact r550_eq_one
  · exact r551_eq_one
  · exact r552_eq_one
  · exact r553_eq_one
  · exact r554_eq_one
  · exact r555_eq_one
  · exact r556_eq_one
  · exact r557_eq_one
  · exact r558_eq_one
  · exact r559_eq_one

@[expose]
def scanBlock35 : List (List (Fin 4)) :=
  [r560, r561, r562, r563, r564,
    r565, r566, r567, r568, r569,
    r570, r571, r572, r573, r574,
    r575]

theorem scanBlock35_eq_one : ∀ w ∈ scanBlock35, (w.map letterValue).prod = 1 := by
  intro w hw
  simp only [scanBlock35, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl
  · exact r560_eq_one
  · exact r561_eq_one
  · exact r562_eq_one
  · exact r563_eq_one
  · exact r564_eq_one
  · exact r565_eq_one
  · exact r566_eq_one
  · exact r567_eq_one
  · exact r568_eq_one
  · exact r569_eq_one
  · exact r570_eq_one
  · exact r571_eq_one
  · exact r572_eq_one
  · exact r573_eq_one
  · exact r574_eq_one
  · exact r575_eq_one

end TauCeti.Sporadic.Mathieu.M11CosetCertificate.RelationSoundness
