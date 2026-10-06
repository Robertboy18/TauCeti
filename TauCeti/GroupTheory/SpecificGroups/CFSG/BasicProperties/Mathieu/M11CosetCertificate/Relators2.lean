/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Relators2

Literal scan words, indexed in the order used by the certificate.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def r512 : List (Fin 4) := [0, 1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1]

@[expose]
def r513 : List (Fin 4) := [1, 2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 0]

@[expose]
def r514 : List (Fin 4) := [2, 2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 0, 1]

@[expose]
def r515 : List (Fin 4) := [2, 1, 2, 1, 2, 3, 2, 1, 1, 2, 1, 1, 1, 0, 1, 2]

@[expose]
def r516 : List (Fin 4) := [0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1]

@[expose]
def r517 : List (Fin 4) := [0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0]

@[expose]
def r518 : List (Fin 4) := [0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0]

@[expose]
def r519 : List (Fin 4) := [0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0]

@[expose]
def r520 : List (Fin 4) := [3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0]

@[expose]
def r521 : List (Fin 4) := [2, 3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3]

@[expose]
def r522 : List (Fin 4) := [3, 2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2]

@[expose]
def r523 : List (Fin 4) := [2, 2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3]

@[expose]
def r524 : List (Fin 4) := [2, 2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2]

@[expose]
def r525 : List (Fin 4) := [2, 1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2]

@[expose]
def r526 : List (Fin 4) := [1, 1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2]

@[expose]
def r527 : List (Fin 4) := [1, 2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1]

@[expose]
def r528 : List (Fin 4) := [2, 2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1]

@[expose]
def r529 : List (Fin 4) := [2, 1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2]

@[expose]
def r530 : List (Fin 4) := [1, 1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2]

@[expose]
def r531 : List (Fin 4) := [1, 0, 0, 0, 0, 3, 2, 3, 2, 2, 2, 1, 1, 2, 2, 1]

@[expose]
def r532 : List (Fin 4) := [3, 3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2]

@[expose]
def r533 : List (Fin 4) := [3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3]

@[expose]
def r534 : List (Fin 4) := [0, 0, 3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3]

@[expose]
def r535 : List (Fin 4) := [0, 3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0]

@[expose]
def r536 : List (Fin 4) := [3, 3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0]

@[expose]
def r537 : List (Fin 4) := [3, 0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3]

@[expose]
def r538 : List (Fin 4) := [0, 0, 0, 1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 3]

@[expose]
def r539 : List (Fin 4) := [1, 0, 1, 2, 2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 0]

@[expose]
def r540 : List (Fin 4) := [2, 2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 1]

@[expose]
def r541 : List (Fin 4) := [2, 2, 2, 3, 3, 0, 0, 3, 3, 0, 0, 0, 1, 0, 1, 2]

@[expose]
def r542 : List (Fin 4) := [1, 0, 0, 3, 0, 0, 3, 2, 3, 3, 3, 0, 3, 2, 3, 0]

@[expose]
def r543 : List (Fin 4) := [0, 0, 3, 3, 0, 1, 1, 0, 0, 0, 3, 3, 2, 2, 3]

@[expose]
def r544 : List (Fin 4) := [3, 3, 0, 1, 1, 0, 0, 0, 3, 3, 2, 2, 3, 0, 0]

@[expose]
def r545 : List (Fin 4) := [1, 2, 2, 1, 0, 0, 1, 1, 2, 2, 2, 3, 3, 2, 1]

@[expose]
def r546 : List (Fin 4) := [2, 1, 0, 0, 1, 1, 2, 2, 2, 3, 3, 2, 1, 1, 2]

@[expose]
def r547 : List (Fin 4) := [0, 3, 0, 3, 2, 3, 0, 3, 3, 2, 1, 2, 3, 0]

@[expose]
def r548 : List (Fin 4) := [0, 3, 2, 3, 0, 3, 3, 2, 1, 2, 3, 0, 0, 3]

@[expose]
def r549 : List (Fin 4) := [2, 3, 0, 3, 3, 2, 1, 2, 3, 0, 0, 3, 0, 3]

@[expose]
def r550 : List (Fin 4) := [2, 1, 2, 3, 0, 0, 3, 0, 3, 2, 3, 0, 3, 3]

@[expose]
def r551 : List (Fin 4) := [3, 0, 0, 3, 0, 3, 2, 3, 0, 3, 3, 2, 1, 2]

@[expose]
def r552 : List (Fin 4) := [1, 0, 3, 0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 2]

@[expose]
def r553 : List (Fin 4) := [0, 1, 1, 2, 1, 0, 1, 2, 1, 2, 2, 1, 0, 3]

@[expose]
def r554 : List (Fin 4) := [0, 1, 2, 1, 2, 2, 1, 0, 3, 0, 1, 1, 2, 1]

@[expose]
def r555 : List (Fin 4) := [2, 1, 2, 2, 1, 0, 3, 0, 1, 1, 2, 1, 0, 1]

@[expose]
def r556 : List (Fin 4) := [2, 2, 1, 0, 3, 0, 1, 1, 2, 1, 0, 1, 2, 1]

@[expose]
def r557 : List (Fin 4) := [2, 1, 1, 0, 1, 1, 0, 0, 0, 3, 3, 2, 2, 3, 2, 1]

@[expose]
def r558 : List (Fin 4) := [0, 3, 0, 1, 0, 0, 1, 1, 2, 2, 2, 3, 3, 2, 3, 3]

@[expose]
def r559 : List (Fin 4) := [2, 3, 3, 0, 0, 1, 0, 1, 2, 2, 3, 3, 2, 2, 1]

@[expose]
def r560 : List (Fin 4) := [0, 3, 0, 0, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 1]

@[expose]
def r561 : List (Fin 4) := [3, 3, 3, 3, 3, 3, 0, 0, 1, 0, 1, 2, 2, 3, 3, 0]

@[expose]
def r562 : List (Fin 4) := [1, 2, 1, 1, 0, 0, 3, 2, 3, 2, 2, 1, 1, 1, 1, 1]

@[expose]
def r563 : List (Fin 4) := [0, 3, 2, 3, 2, 3, 0, 0, 0, 1, 1, 2, 1, 1, 0]

@[expose]
def r564 : List (Fin 4) := [2, 2, 3, 3, 0, 3, 3, 2, 2, 2, 1, 0, 1, 0, 1]

@[expose]
def r565 : List (Fin 4) := [0, 1, 2, 1, 0, 0, 3, 2, 3, 2, 3, 3, 0, 0, 0, 0]

@[expose]
def r566 : List (Fin 4) := [2, 2, 2, 2, 2, 1, 1, 0, 1, 0, 1, 2, 2, 3, 0, 3]

@[expose]
def r567 : List (Fin 4) := [0, 3, 0, 3, 3, 0, 0, 0, 3, 2, 2, 3, 2, 3]

@[expose]
def r568 : List (Fin 4) := [3, 0, 3, 3, 0, 0, 0, 3, 2, 2, 3, 2, 3, 0]

@[expose]
def r569 : List (Fin 4) := [1, 2, 1, 0, 1, 0, 0, 1, 2, 2, 2, 1, 1, 2]

@[expose]
def r570 : List (Fin 4) := [2, 1, 0, 1, 0, 0, 1, 2, 2, 2, 1, 1, 2, 1]

@[expose]
def r571 : List (Fin 4) := [2, 3, 3, 0, 3, 0, 1, 0, 0, 3, 3, 0, 3, 3, 3]

@[expose]
def r572 : List (Fin 4) := [1, 0, 0, 3, 3, 0, 3, 3, 3, 2, 3, 3, 0, 3, 0]

@[expose]
def r573 : List (Fin 4) := [3, 2, 1, 2, 1, 1, 0, 1, 1, 1, 2, 1, 1, 2, 2]

@[expose]
def r574 : List (Fin 4) := [0, 1, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1]

@[expose]
def r575 : List (Fin 4) := [3, 3, 0, 3, 0, 3, 2, 1, 2, 1, 1, 0, 1, 1, 1, 2]

@[expose]
def r576 : List (Fin 4) := [1, 0, 3, 3, 3, 2, 3, 3, 0, 3, 0, 1, 2, 1, 2, 1]

@[expose]
def r577 : List (Fin 4) := [1, 1, 2, 1, 1, 2, 2, 3, 0, 0, 3, 3, 0, 1]

@[expose]
def r578 : List (Fin 4) := [2, 2, 3, 0, 0, 3, 3, 0, 1, 1, 1, 2, 1, 1]

@[expose]
def r579 : List (Fin 4) := [0, 3, 3, 0, 3, 3, 3, 2, 1, 1, 2, 2, 1, 0]

@[expose]
def r580 : List (Fin 4) := [3, 3, 2, 1, 1, 2, 2, 1, 0, 0, 3, 3, 0, 3]

@[expose]
def r581 : List (Fin 4) := [0, 0, 1, 2, 1, 1, 0, 3, 3, 0, 0, 0, 3, 3, 2, 3]

@[expose]
def r582 : List (Fin 4) := [1, 1, 0, 3, 3, 0, 0, 0, 3, 3, 2, 3, 0, 0, 1, 2]

@[expose]
def r583 : List (Fin 4) := [3, 0, 3, 2, 2, 1, 0, 1, 1, 2, 2, 2, 1, 1, 2, 3]

@[expose]
def r584 : List (Fin 4) := [2, 1, 0, 1, 1, 2, 2, 2, 1, 1, 2, 3, 3, 0, 3, 2]

@[expose]
def r585 : List (Fin 4) := [0, 1, 2, 1, 0, 0, 3, 2, 2, 3, 0, 0, 3, 0]

@[expose]
def r586 : List (Fin 4) := [2, 2, 1, 2, 2, 1, 0, 0, 1, 2, 2, 3, 0, 3]

@[expose]
def r587 : List (Fin 4) := [3, 0, 3, 3, 3, 3, 3, 3, 0, 1, 0, 3, 0, 1, 2, 3]

@[expose]
def r588 : List (Fin 4) := [1, 1, 0, 3, 2, 1, 2, 3, 2, 1, 1, 1, 1, 1, 1, 2]

@[expose]
def r589 : List (Fin 4) := [2, 1, 1, 0, 3, 2, 1, 2, 3, 3, 0, 0, 0, 1, 1]

@[expose]
def r590 : List (Fin 4) := [3, 2, 1, 2, 3, 3, 0, 0, 0, 1, 1, 2, 1, 1, 0]

@[expose]
def r591 : List (Fin 4) := [1, 2, 3, 3, 0, 3, 3, 2, 2, 2, 1, 1, 0, 3, 0]

@[expose]
def r592 : List (Fin 4) := [0, 3, 3, 2, 2, 2, 1, 1, 0, 3, 0, 1, 2, 3, 3]

@[expose]
def r593 : List (Fin 4) := [0, 0, 1, 1, 0, 3, 3, 2, 2, 2, 3, 2, 2, 3, 0]

@[expose]
def r594 : List (Fin 4) := [2, 2, 1, 0, 0, 1, 0, 0, 0, 1, 1, 2, 3, 3, 2]

@[expose]
def r595 : List (Fin 4) := [3, 3, 3, 0, 0, 3, 3, 0, 1, 2, 3, 3, 0, 3, 0, 3]

@[expose]
def r596 : List (Fin 4) := [3, 3, 0, 0, 3, 3, 0, 1, 2, 3, 3, 0, 3, 0, 3, 3]

@[expose]
def r597 : List (Fin 4) := [1, 1, 1, 2, 1, 2, 1, 1, 0, 3, 2, 1, 1, 2, 2, 1]

@[expose]
def r598 : List (Fin 4) := [1, 1, 2, 1, 2, 1, 1, 0, 3, 2, 1, 1, 2, 2, 1, 1]

@[expose]
def r599 : List (Fin 4) := [1, 2, 2, 1, 1, 1, 0, 0, 3, 3, 0, 1, 1, 2, 1]

@[expose]
def r600 : List (Fin 4) := [3, 3, 0, 3, 3, 2, 1, 1, 2, 2, 3, 3, 3, 0, 0]

@[expose]
def r601 : List (Fin 4) := [2, 3, 0, 1, 2, 1, 1, 0, 3, 2, 1, 0, 1, 0, 3]

@[expose]
def r602 : List (Fin 4) := [0, 1, 2, 3, 2, 3, 0, 1, 2, 3, 3, 0, 3, 2, 1]

@[expose]
def r603 : List (Fin 4) := [3, 3, 2, 2, 2, 1, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3]

@[expose]
def r604 : List (Fin 4) := [1, 1, 0, 3, 2, 2, 2, 2, 2, 2, 2, 3, 0, 0, 0, 1]

@[expose]
def r605 : List (Fin 4) := [1, 1, 1, 2, 3, 0, 1, 2, 1, 2, 1, 1, 2, 1, 1, 0]

@[expose]
def r606 : List (Fin 4) := [1, 0, 1, 1, 1, 2, 3, 0, 1, 2, 1, 2, 1, 1, 2, 1]

@[expose]
def r607 : List (Fin 4) := [3, 3, 0, 3, 3, 0, 3, 0, 3, 2, 1, 0, 3, 3, 3, 2]

@[expose]
def r608 : List (Fin 4) := [3, 2, 3, 3, 0, 3, 3, 0, 3, 0, 3, 2, 1, 0, 3, 3]

@[expose]
def r609 : List (Fin 4) := [0, 1, 1, 1, 2, 3, 0, 1, 0, 0, 3, 3, 2, 1, 1]

@[expose]
def r610 : List (Fin 4) := [2, 3, 3, 0, 1, 1, 2, 2, 3, 2, 1, 0, 3, 3, 3]

@[expose]
def r611 : List (Fin 4) := [2, 2, 1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 0, 1]

@[expose]
def r612 : List (Fin 4) := [1, 0, 1, 0, 1, 0, 3, 0, 3, 3, 0, 0, 1, 2, 2]

@[expose]
def r613 : List (Fin 4) := [0, 3, 0, 3, 3, 0, 0, 1, 2, 2, 1, 0, 1, 0, 1]

@[expose]
def r614 : List (Fin 4) := [2, 3, 2, 3, 2, 3, 0, 0, 3, 2, 2, 1, 1, 2, 1]

@[expose]
def r615 : List (Fin 4) := [3, 0, 0, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2]

@[expose]
def r616 : List (Fin 4) := [0, 3, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 2, 3, 0]

@[expose]
def r617 : List (Fin 4) := [3, 3, 2, 1, 1, 0, 1, 1, 0, 1, 0, 3, 0]

@[expose]
def r618 : List (Fin 4) := [1, 2, 1, 2, 3, 2, 3, 3, 2, 3, 3, 0, 1]

@[expose]
def r619 : List (Fin 4) := [1, 1, 0, 0, 3, 0, 3, 3, 0, 0, 3, 3, 2, 3, 3, 2]

@[expose]
def r620 : List (Fin 4) := [3, 0, 1, 1, 0, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3]

@[expose]
def r621 : List (Fin 4) := [3, 0, 0, 1, 1, 2, 2, 1, 1, 0, 0, 3, 3, 0, 1, 0]

@[expose]
def r622 : List (Fin 4) := [1, 2, 3, 2, 1, 1, 2, 2, 3, 3, 0, 0, 3, 3, 2, 2]

@[expose]
def r623 : List (Fin 4) := [0, 3, 0, 0, 3, 0, 1, 0, 0, 3, 3, 2, 1, 1, 0, 3]

@[expose]
def r624 : List (Fin 4) := [2, 1, 2, 3, 3, 0, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1]

@[expose]
def r625 : List (Fin 4) := [0, 0, 1, 1, 2, 3, 3, 3, 3, 3, 3, 0, 0, 0, 1, 0]

@[expose]
def r626 : List (Fin 4) := [3, 0, 0, 0, 1, 0, 0, 0, 1, 1, 2, 3, 3, 3, 3, 3]

@[expose]
def r627 : List (Fin 4) := [2, 2, 3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 0, 3, 3, 2]

@[expose]
def r628 : List (Fin 4) := [0, 3, 2, 1, 0, 1, 0, 0, 3, 2, 3, 0, 0, 0, 0]

@[expose]
def r629 : List (Fin 4) := [0, 0, 3, 2, 3, 0, 0, 0, 0, 0, 3, 2, 1, 0, 1]

@[expose]
def r630 : List (Fin 4) := [2, 3, 2, 3, 0, 1, 2, 2, 2, 2, 2, 1, 0, 1, 2]

@[expose]
def r631 : List (Fin 4) := [2, 2, 2, 2, 2, 1, 0, 1, 2, 2, 3, 2, 3, 0, 1]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
