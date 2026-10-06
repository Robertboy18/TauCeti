/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Words2

Literal defining words and their block representation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def w512 : List (Fin 4) := [3, 3, 0, 1, 2, 2]

@[expose]
def w513 : List (Fin 4) := [0, 0, 1, 1, 2, 2]

@[expose]
def w514 : List (Fin 4) := [3, 0, 1, 1, 2, 2]

@[expose]
def w515 : List (Fin 4) := [1, 2, 1, 1, 2, 2]

@[expose]
def w516 : List (Fin 4) := [2, 2, 1, 1, 2, 2]

@[expose]
def w517 : List (Fin 4) := [0, 1, 2, 1, 2, 2]

@[expose]
def w518 : List (Fin 4) := [1, 1, 2, 1, 2, 2]

@[expose]
def w519 : List (Fin 4) := [2, 1, 2, 1, 2, 2]

@[expose]
def w520 : List (Fin 4) := [1, 2, 2, 1, 2, 2]

@[expose]
def w521 : List (Fin 4) := [0, 3, 2, 1, 2, 2]

@[expose]
def w522 : List (Fin 4) := [3, 3, 2, 1, 2, 2]

@[expose]
def w523 : List (Fin 4) := [0, 1, 2, 2, 2, 2]

@[expose]
def w524 : List (Fin 4) := [3, 2, 2, 2, 2, 2]

@[expose]
def w525 : List (Fin 4) := [0, 3, 2, 2, 2, 2]

@[expose]
def w526 : List (Fin 4) := [3, 3, 2, 2, 2, 2]

@[expose]
def w527 : List (Fin 4) := [3, 2, 3, 2, 2, 2]

@[expose]
def w528 : List (Fin 4) := [0, 1, 2, 3, 2, 2]

@[expose]
def w529 : List (Fin 4) := [2, 1, 2, 3, 2, 2]

@[expose]
def w530 : List (Fin 4) := [2, 3, 2, 3, 2, 2]

@[expose]
def w531 : List (Fin 4) := [3, 3, 2, 3, 2, 2]

@[expose]
def w532 : List (Fin 4) := [3, 0, 3, 3, 2, 2]

@[expose]
def w533 : List (Fin 4) := [2, 2, 3, 3, 2, 2]

@[expose]
def w534 : List (Fin 4) := [3, 2, 3, 3, 2, 2]

@[expose]
def w535 : List (Fin 4) := [0, 3, 3, 3, 2, 2]

@[expose]
def w536 : List (Fin 4) := [2, 3, 3, 3, 2, 2]

@[expose]
def w537 : List (Fin 4) := [0, 1, 0, 0, 3, 2]

@[expose]
def w538 : List (Fin 4) := [1, 1, 0, 0, 3, 2]

@[expose]
def w539 : List (Fin 4) := [3, 3, 0, 0, 3, 2]

@[expose]
def w540 : List (Fin 4) := [1, 1, 1, 0, 3, 2]

@[expose]
def w541 : List (Fin 4) := [2, 1, 1, 0, 3, 2]

@[expose]
def w542 : List (Fin 4) := [1, 2, 1, 0, 3, 2]

@[expose]
def w543 : List (Fin 4) := [0, 0, 3, 0, 3, 2]

@[expose]
def w544 : List (Fin 4) := [1, 0, 3, 0, 3, 2]

@[expose]
def w545 : List (Fin 4) := [1, 2, 3, 0, 3, 2]

@[expose]
def w546 : List (Fin 4) := [2, 2, 3, 0, 3, 2]

@[expose]
def w547 : List (Fin 4) := [3, 2, 3, 0, 3, 2]

@[expose]
def w548 : List (Fin 4) := [0, 3, 3, 0, 3, 2]

@[expose]
def w549 : List (Fin 4) := [0, 1, 2, 2, 3, 2]

@[expose]
def w550 : List (Fin 4) := [2, 1, 2, 2, 3, 2]

@[expose]
def w551 : List (Fin 4) := [1, 2, 2, 2, 3, 2]

@[expose]
def w552 : List (Fin 4) := [2, 2, 2, 2, 3, 2]

@[expose]
def w553 : List (Fin 4) := [0, 3, 2, 2, 3, 2]

@[expose]
def w554 : List (Fin 4) := [2, 3, 2, 2, 3, 2]

@[expose]
def w555 : List (Fin 4) := [3, 3, 2, 2, 3, 2]

@[expose]
def w556 : List (Fin 4) := [2, 3, 3, 2, 3, 2]

@[expose]
def w557 : List (Fin 4) := [3, 3, 3, 2, 3, 2]

@[expose]
def w558 : List (Fin 4) := [1, 1, 0, 3, 3, 2]

@[expose]
def w559 : List (Fin 4) := [0, 3, 0, 3, 3, 2]

@[expose]
def w560 : List (Fin 4) := [3, 3, 0, 3, 3, 2]

@[expose]
def w561 : List (Fin 4) := [1, 2, 2, 3, 3, 2]

@[expose]
def w562 : List (Fin 4) := [3, 2, 2, 3, 3, 2]

@[expose]
def w563 : List (Fin 4) := [0, 3, 2, 3, 3, 2]

@[expose]
def w564 : List (Fin 4) := [0, 1, 0, 0, 0, 0, 0]

@[expose]
def w565 : List (Fin 4) := [1, 1, 0, 0, 0, 0, 0]

@[expose]
def w566 : List (Fin 4) := [0, 0, 1, 0, 0, 0, 0]

@[expose]
def w567 : List (Fin 4) := [1, 0, 1, 0, 0, 0, 0]

@[expose]
def w568 : List (Fin 4) := [3, 0, 1, 0, 0, 0, 0]

@[expose]
def w569 : List (Fin 4) := [0, 1, 1, 0, 0, 0, 0]

@[expose]
def w570 : List (Fin 4) := [2, 1, 1, 0, 0, 0, 0]

@[expose]
def w571 : List (Fin 4) := [2, 2, 1, 0, 0, 0, 0]

@[expose]
def w572 : List (Fin 4) := [3, 2, 1, 0, 0, 0, 0]

@[expose]
def w573 : List (Fin 4) := [0, 3, 3, 0, 0, 0, 0]

@[expose]
def w574 : List (Fin 4) := [2, 3, 3, 0, 0, 0, 0]

@[expose]
def w575 : List (Fin 4) := [3, 3, 3, 0, 0, 0, 0]

@[expose]
def w576 : List (Fin 4) := [0, 1, 0, 1, 0, 0, 0]

@[expose]
def w577 : List (Fin 4) := [2, 1, 0, 1, 0, 0, 0]

@[expose]
def w578 : List (Fin 4) := [0, 0, 1, 1, 0, 0, 0]

@[expose]
def w579 : List (Fin 4) := [1, 0, 1, 1, 0, 0, 0]

@[expose]
def w580 : List (Fin 4) := [3, 0, 1, 1, 0, 0, 0]

@[expose]
def w581 : List (Fin 4) := [1, 1, 1, 1, 0, 0, 0]

@[expose]
def w582 : List (Fin 4) := [1, 2, 1, 1, 0, 0, 0]

@[expose]
def w583 : List (Fin 4) := [2, 2, 1, 1, 0, 0, 0]

@[expose]
def w584 : List (Fin 4) := [1, 2, 2, 1, 0, 0, 0]

@[expose]
def w585 : List (Fin 4) := [2, 2, 2, 1, 0, 0, 0]

@[expose]
def w586 : List (Fin 4) := [3, 2, 2, 1, 0, 0, 0]

@[expose]
def w587 : List (Fin 4) := [0, 3, 2, 1, 0, 0, 0]

@[expose]
def w588 : List (Fin 4) := [2, 2, 2, 3, 0, 0, 0]

@[expose]
def w589 : List (Fin 4) := [0, 3, 2, 3, 0, 0, 0]

@[expose]
def w590 : List (Fin 4) := [2, 3, 2, 3, 0, 0, 0]

@[expose]
def w591 : List (Fin 4) := [0, 0, 3, 3, 0, 0, 0]

@[expose]
def w592 : List (Fin 4) := [3, 0, 3, 3, 0, 0, 0]

@[expose]
def w593 : List (Fin 4) := [0, 3, 3, 3, 0, 0, 0]

@[expose]
def w594 : List (Fin 4) := [2, 3, 3, 3, 0, 0, 0]

@[expose]
def w595 : List (Fin 4) := [0, 0, 0, 0, 1, 0, 0]

@[expose]
def w596 : List (Fin 4) := [3, 0, 0, 0, 1, 0, 0]

@[expose]
def w597 : List (Fin 4) := [1, 1, 0, 0, 1, 0, 0]

@[expose]
def w598 : List (Fin 4) := [2, 1, 0, 0, 1, 0, 0]

@[expose]
def w599 : List (Fin 4) := [3, 3, 0, 0, 1, 0, 0]

@[expose]
def w600 : List (Fin 4) := [0, 0, 1, 0, 1, 0, 0]

@[expose]
def w601 : List (Fin 4) := [2, 2, 1, 0, 1, 0, 0]

@[expose]
def w602 : List (Fin 4) := [3, 2, 1, 0, 1, 0, 0]

@[expose]
def w603 : List (Fin 4) := [0, 0, 3, 0, 1, 0, 0]

@[expose]
def w604 : List (Fin 4) := [3, 0, 3, 0, 1, 0, 0]

@[expose]
def w605 : List (Fin 4) := [2, 2, 3, 0, 1, 0, 0]

@[expose]
def w606 : List (Fin 4) := [0, 3, 3, 0, 1, 0, 0]

@[expose]
def w607 : List (Fin 4) := [2, 3, 3, 0, 1, 0, 0]

@[expose]
def w608 : List (Fin 4) := [0, 0, 0, 1, 1, 0, 0]

@[expose]
def w609 : List (Fin 4) := [1, 0, 0, 1, 1, 0, 0]

@[expose]
def w610 : List (Fin 4) := [3, 0, 0, 1, 1, 0, 0]

@[expose]
def w611 : List (Fin 4) := [2, 1, 0, 1, 1, 0, 0]

@[expose]
def w612 : List (Fin 4) := [0, 0, 1, 1, 1, 0, 0]

@[expose]
def w613 : List (Fin 4) := [0, 1, 1, 1, 1, 0, 0]

@[expose]
def w614 : List (Fin 4) := [1, 1, 1, 1, 1, 0, 0]

@[expose]
def w615 : List (Fin 4) := [0, 1, 2, 1, 1, 0, 0]

@[expose]
def w616 : List (Fin 4) := [1, 2, 2, 1, 1, 0, 0]

@[expose]
def w617 : List (Fin 4) := [2, 2, 2, 1, 1, 0, 0]

@[expose]
def w618 : List (Fin 4) := [3, 2, 2, 1, 1, 0, 0]

@[expose]
def w619 : List (Fin 4) := [0, 3, 2, 1, 1, 0, 0]

@[expose]
def w620 : List (Fin 4) := [1, 1, 2, 2, 1, 0, 0]

@[expose]
def w621 : List (Fin 4) := [2, 2, 2, 2, 1, 0, 0]

@[expose]
def w622 : List (Fin 4) := [3, 3, 2, 2, 1, 0, 0]

@[expose]
def w623 : List (Fin 4) := [2, 1, 2, 2, 3, 0, 0]

@[expose]
def w624 : List (Fin 4) := [1, 2, 2, 2, 3, 0, 0]

@[expose]
def w625 : List (Fin 4) := [3, 2, 2, 2, 3, 0, 0]

@[expose]
def w626 : List (Fin 4) := [2, 3, 2, 2, 3, 0, 0]

@[expose]
def w627 : List (Fin 4) := [3, 3, 2, 2, 3, 0, 0]

@[expose]
def w628 : List (Fin 4) := [3, 0, 3, 2, 3, 0, 0]

@[expose]
def w629 : List (Fin 4) := [1, 2, 3, 2, 3, 0, 0]

@[expose]
def w630 : List (Fin 4) := [3, 2, 3, 2, 3, 0, 0]

@[expose]
def w631 : List (Fin 4) := [0, 3, 3, 2, 3, 0, 0]

@[expose]
def w632 : List (Fin 4) := [3, 0, 0, 3, 3, 0, 0]

@[expose]
def w633 : List (Fin 4) := [1, 1, 0, 3, 3, 0, 0]

@[expose]
def w634 : List (Fin 4) := [2, 1, 0, 3, 3, 0, 0]

@[expose]
def w635 : List (Fin 4) := [2, 1, 2, 3, 3, 0, 0]

@[expose]
def w636 : List (Fin 4) := [2, 2, 2, 3, 3, 0, 0]

@[expose]
def w637 : List (Fin 4) := [0, 0, 0, 0, 0, 1, 0]

@[expose]
def w638 : List (Fin 4) := [1, 0, 0, 0, 0, 1, 0]

@[expose]
def w639 : List (Fin 4) := [0, 0, 1, 0, 0, 1, 0]

@[expose]
def w640 : List (Fin 4) := [3, 0, 1, 0, 0, 1, 0]

@[expose]
def w641 : List (Fin 4) := [2, 1, 1, 0, 0, 1, 0]

@[expose]
def w642 : List (Fin 4) := [1, 2, 1, 0, 0, 1, 0]

@[expose]
def w643 : List (Fin 4) := [3, 2, 1, 0, 0, 1, 0]

@[expose]
def w644 : List (Fin 4) := [1, 2, 3, 0, 0, 1, 0]

@[expose]
def w645 : List (Fin 4) := [2, 2, 3, 0, 0, 1, 0]

@[expose]
def w646 : List (Fin 4) := [0, 3, 3, 0, 0, 1, 0]

@[expose]
def w647 : List (Fin 4) := [3, 3, 3, 0, 0, 1, 0]

@[expose]
def w648 : List (Fin 4) := [0, 1, 0, 1, 0, 1, 0]

@[expose]
def w649 : List (Fin 4) := [2, 1, 0, 1, 0, 1, 0]

@[expose]
def w650 : List (Fin 4) := [3, 0, 1, 1, 0, 1, 0]

@[expose]
def w651 : List (Fin 4) := [0, 1, 1, 1, 0, 1, 0]

@[expose]
def w652 : List (Fin 4) := [1, 2, 1, 1, 0, 1, 0]

@[expose]
def w653 : List (Fin 4) := [3, 2, 1, 1, 0, 1, 0]

@[expose]
def w654 : List (Fin 4) := [1, 2, 2, 1, 0, 1, 0]

@[expose]
def w655 : List (Fin 4) := [3, 2, 2, 1, 0, 1, 0]

@[expose]
def w656 : List (Fin 4) := [3, 3, 2, 1, 0, 1, 0]

@[expose]
def w657 : List (Fin 4) := [0, 0, 0, 3, 0, 1, 0]

@[expose]
def w658 : List (Fin 4) := [0, 3, 0, 3, 0, 1, 0]

@[expose]
def w659 : List (Fin 4) := [2, 3, 0, 3, 0, 1, 0]

@[expose]
def w660 : List (Fin 4) := [1, 0, 0, 0, 1, 1, 0]

@[expose]
def w661 : List (Fin 4) := [0, 1, 0, 0, 1, 1, 0]

@[expose]
def w662 : List (Fin 4) := [2, 1, 0, 0, 1, 1, 0]

@[expose]
def w663 : List (Fin 4) := [2, 3, 0, 0, 1, 1, 0]

@[expose]
def w664 : List (Fin 4) := [3, 3, 0, 0, 1, 1, 0]

@[expose]
def w665 : List (Fin 4) := [0, 0, 1, 0, 1, 1, 0]

@[expose]
def w666 : List (Fin 4) := [1, 1, 1, 0, 1, 1, 0]

@[expose]
def w667 : List (Fin 4) := [1, 2, 1, 0, 1, 1, 0]

@[expose]
def w668 : List (Fin 4) := [2, 2, 1, 0, 1, 1, 0]

@[expose]
def w669 : List (Fin 4) := [3, 2, 1, 0, 1, 1, 0]

@[expose]
def w670 : List (Fin 4) := [0, 0, 3, 0, 1, 1, 0]

@[expose]
def w671 : List (Fin 4) := [1, 0, 3, 0, 1, 1, 0]

@[expose]
def w672 : List (Fin 4) := [3, 0, 3, 0, 1, 1, 0]

@[expose]
def w673 : List (Fin 4) := [1, 2, 3, 0, 1, 1, 0]

@[expose]
def w674 : List (Fin 4) := [2, 2, 3, 0, 1, 1, 0]

@[expose]
def w675 : List (Fin 4) := [3, 2, 3, 0, 1, 1, 0]

@[expose]
def w676 : List (Fin 4) := [0, 3, 3, 0, 1, 1, 0]

@[expose]
def w677 : List (Fin 4) := [3, 3, 3, 0, 1, 1, 0]

@[expose]
def w678 : List (Fin 4) := [3, 0, 1, 1, 1, 1, 0]

@[expose]
def w679 : List (Fin 4) := [0, 1, 1, 1, 1, 1, 0]

@[expose]
def w680 : List (Fin 4) := [2, 2, 2, 1, 1, 1, 0]

@[expose]
def w681 : List (Fin 4) := [3, 2, 2, 1, 1, 1, 0]

@[expose]
def w682 : List (Fin 4) := [0, 3, 2, 1, 1, 1, 0]

@[expose]
def w683 : List (Fin 4) := [3, 3, 2, 1, 1, 1, 0]

@[expose]
def w684 : List (Fin 4) := [3, 0, 1, 2, 1, 1, 0]

@[expose]
def w685 : List (Fin 4) := [2, 1, 1, 2, 1, 1, 0]

@[expose]
def w686 : List (Fin 4) := [1, 1, 0, 1, 2, 1, 0]

@[expose]
def w687 : List (Fin 4) := [0, 3, 0, 1, 2, 1, 0]

@[expose]
def w688 : List (Fin 4) := [0, 1, 1, 1, 2, 1, 0]

@[expose]
def w689 : List (Fin 4) := [2, 1, 1, 1, 2, 1, 0]

@[expose]
def w690 : List (Fin 4) := [1, 2, 1, 1, 2, 1, 0]

@[expose]
def w691 : List (Fin 4) := [1, 0, 1, 2, 2, 1, 0]

@[expose]
def w692 : List (Fin 4) := [0, 1, 1, 2, 2, 1, 0]

@[expose]
def w693 : List (Fin 4) := [1, 2, 1, 2, 2, 1, 0]

@[expose]
def w694 : List (Fin 4) := [3, 2, 1, 2, 2, 1, 0]

@[expose]
def w695 : List (Fin 4) := [1, 2, 2, 2, 2, 1, 0]

@[expose]
def w696 : List (Fin 4) := [3, 2, 2, 2, 2, 1, 0]

@[expose]
def w697 : List (Fin 4) := [2, 3, 2, 2, 2, 1, 0]

@[expose]
def w698 : List (Fin 4) := [0, 0, 3, 2, 2, 1, 0]

@[expose]
def w699 : List (Fin 4) := [1, 2, 3, 2, 2, 1, 0]

@[expose]
def w700 : List (Fin 4) := [3, 2, 3, 2, 2, 1, 0]

@[expose]
def w701 : List (Fin 4) := [2, 3, 3, 2, 2, 1, 0]

@[expose]
def w702 : List (Fin 4) := [3, 3, 3, 2, 2, 1, 0]

@[expose]
def w703 : List (Fin 4) := [0, 0, 0, 3, 2, 1, 0]

@[expose]
def w704 : List (Fin 4) := [3, 0, 0, 3, 2, 1, 0]

@[expose]
def w705 : List (Fin 4) := [1, 1, 0, 3, 2, 1, 0]

@[expose]
def w706 : List (Fin 4) := [2, 1, 0, 3, 2, 1, 0]

@[expose]
def w707 : List (Fin 4) := [0, 3, 0, 3, 2, 1, 0]

@[expose]
def w708 : List (Fin 4) := [2, 3, 0, 3, 2, 1, 0]

@[expose]
def w709 : List (Fin 4) := [1, 2, 2, 3, 2, 1, 0]

@[expose]
def w710 : List (Fin 4) := [0, 0, 3, 3, 2, 1, 0]

@[expose]
def w711 : List (Fin 4) := [2, 2, 3, 3, 2, 1, 0]

@[expose]
def w712 : List (Fin 4) := [3, 2, 3, 3, 2, 1, 0]

@[expose]
def w713 : List (Fin 4) := [0, 0, 0, 0, 0, 3, 0]

@[expose]
def w714 : List (Fin 4) := [0, 0, 1, 0, 0, 3, 0]

@[expose]
def w715 : List (Fin 4) := [1, 0, 1, 0, 0, 3, 0]

@[expose]
def w716 : List (Fin 4) := [1, 1, 1, 0, 0, 3, 0]

@[expose]
def w717 : List (Fin 4) := [2, 2, 1, 0, 0, 3, 0]

@[expose]
def w718 : List (Fin 4) := [1, 0, 3, 0, 0, 3, 0]

@[expose]
def w719 : List (Fin 4) := [0, 3, 3, 0, 0, 3, 0]

@[expose]
def w720 : List (Fin 4) := [2, 3, 3, 0, 0, 3, 0]

@[expose]
def w721 : List (Fin 4) := [0, 1, 0, 1, 0, 3, 0]

@[expose]
def w722 : List (Fin 4) := [1, 0, 1, 1, 0, 3, 0]

@[expose]
def w723 : List (Fin 4) := [3, 0, 1, 1, 0, 3, 0]

@[expose]
def w724 : List (Fin 4) := [1, 2, 1, 1, 0, 3, 0]

@[expose]
def w725 : List (Fin 4) := [2, 2, 2, 1, 0, 3, 0]

@[expose]
def w726 : List (Fin 4) := [3, 2, 2, 1, 0, 3, 0]

@[expose]
def w727 : List (Fin 4) := [0, 0, 1, 1, 2, 3, 0]

@[expose]
def w728 : List (Fin 4) := [2, 1, 1, 1, 2, 3, 0]

@[expose]
def w729 : List (Fin 4) := [0, 1, 2, 2, 2, 3, 0]

@[expose]
def w730 : List (Fin 4) := [2, 1, 2, 2, 2, 3, 0]

@[expose]
def w731 : List (Fin 4) := [1, 2, 2, 2, 2, 3, 0]

@[expose]
def w732 : List (Fin 4) := [3, 2, 2, 2, 2, 3, 0]

@[expose]
def w733 : List (Fin 4) := [0, 3, 2, 2, 2, 3, 0]

@[expose]
def w734 : List (Fin 4) := [2, 3, 0, 3, 2, 3, 0]

@[expose]
def w735 : List (Fin 4) := [1, 1, 2, 3, 2, 3, 0]

@[expose]
def w736 : List (Fin 4) := [2, 1, 2, 3, 2, 3, 0]

@[expose]
def w737 : List (Fin 4) := [2, 2, 2, 3, 2, 3, 0]

@[expose]
def w738 : List (Fin 4) := [3, 0, 3, 3, 2, 3, 0]

@[expose]
def w739 : List (Fin 4) := [1, 2, 3, 3, 2, 3, 0]

@[expose]
def w740 : List (Fin 4) := [2, 2, 3, 3, 2, 3, 0]

@[expose]
def w741 : List (Fin 4) := [0, 3, 3, 3, 2, 3, 0]

@[expose]
def w742 : List (Fin 4) := [2, 3, 3, 3, 2, 3, 0]

@[expose]
def w743 : List (Fin 4) := [1, 1, 0, 0, 3, 3, 0]

@[expose]
def w744 : List (Fin 4) := [0, 3, 0, 0, 3, 3, 0]

@[expose]
def w745 : List (Fin 4) := [2, 1, 1, 0, 3, 3, 0]

@[expose]
def w746 : List (Fin 4) := [3, 0, 3, 0, 3, 3, 0]

@[expose]
def w747 : List (Fin 4) := [1, 2, 3, 0, 3, 3, 0]

@[expose]
def w748 : List (Fin 4) := [0, 3, 3, 0, 3, 3, 0]

@[expose]
def w749 : List (Fin 4) := [2, 3, 3, 0, 3, 3, 0]

@[expose]
def w750 : List (Fin 4) := [1, 1, 1, 2, 3, 3, 0]

@[expose]
def w751 : List (Fin 4) := [2, 1, 1, 2, 3, 3, 0]

@[expose]
def w752 : List (Fin 4) := [0, 1, 2, 2, 3, 3, 0]

@[expose]
def w753 : List (Fin 4) := [1, 1, 2, 2, 3, 3, 0]

@[expose]
def w754 : List (Fin 4) := [2, 2, 2, 2, 3, 3, 0]

@[expose]
def w755 : List (Fin 4) := [3, 2, 2, 2, 3, 3, 0]

@[expose]
def w756 : List (Fin 4) := [2, 2, 3, 2, 3, 3, 0]

@[expose]
def w757 : List (Fin 4) := [3, 2, 3, 2, 3, 3, 0]

@[expose]
def w758 : List (Fin 4) := [0, 3, 3, 2, 3, 3, 0]

@[expose]
def w759 : List (Fin 4) := [3, 3, 3, 2, 3, 3, 0]

@[expose]
def w760 : List (Fin 4) := [0, 1, 2, 3, 3, 3, 0]

@[expose]
def w761 : List (Fin 4) := [1, 0, 0, 0, 0, 0, 1]

@[expose]
def w762 : List (Fin 4) := [1, 1, 0, 0, 0, 0, 1]

@[expose]
def w763 : List (Fin 4) := [2, 3, 0, 0, 0, 0, 1]

@[expose]
def w764 : List (Fin 4) := [3, 3, 0, 0, 0, 0, 1]

@[expose]
def w765 : List (Fin 4) := [0, 1, 1, 0, 0, 0, 1]

@[expose]
def w766 : List (Fin 4) := [1, 1, 1, 0, 0, 0, 1]

@[expose]
def w767 : List (Fin 4) := [2, 1, 1, 0, 0, 0, 1]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
