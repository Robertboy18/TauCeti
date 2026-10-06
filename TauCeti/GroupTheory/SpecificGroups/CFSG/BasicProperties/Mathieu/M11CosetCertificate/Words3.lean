/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coset.TableFast

/-!
# M11 coset certificate: Words3

Literal defining words and their block representation.
-/

public section

namespace TauCeti.Sporadic.Mathieu.M11CosetCertificate

open TauCeti.CosetTable

@[expose]
def w768 : List (Fin 4) := [1, 2, 1, 0, 0, 0, 1]

@[expose]
def w769 : List (Fin 4) := [1, 2, 3, 0, 0, 0, 1]

@[expose]
def w770 : List (Fin 4) := [2, 2, 3, 0, 0, 0, 1]

@[expose]
def w771 : List (Fin 4) := [0, 0, 0, 1, 0, 0, 1]

@[expose]
def w772 : List (Fin 4) := [0, 1, 0, 1, 0, 0, 1]

@[expose]
def w773 : List (Fin 4) := [1, 0, 0, 3, 0, 0, 1]

@[expose]
def w774 : List (Fin 4) := [2, 1, 0, 3, 0, 0, 1]

@[expose]
def w775 : List (Fin 4) := [2, 1, 2, 3, 0, 0, 1]

@[expose]
def w776 : List (Fin 4) := [0, 3, 2, 3, 0, 0, 1]

@[expose]
def w777 : List (Fin 4) := [2, 3, 2, 3, 0, 0, 1]

@[expose]
def w778 : List (Fin 4) := [1, 0, 3, 3, 0, 0, 1]

@[expose]
def w779 : List (Fin 4) := [3, 0, 3, 3, 0, 0, 1]

@[expose]
def w780 : List (Fin 4) := [2, 2, 3, 3, 0, 0, 1]

@[expose]
def w781 : List (Fin 4) := [1, 0, 0, 0, 1, 0, 1]

@[expose]
def w782 : List (Fin 4) := [3, 0, 0, 0, 1, 0, 1]

@[expose]
def w783 : List (Fin 4) := [3, 3, 0, 0, 1, 0, 1]

@[expose]
def w784 : List (Fin 4) := [0, 0, 1, 0, 1, 0, 1]

@[expose]
def w785 : List (Fin 4) := [1, 0, 1, 0, 1, 0, 1]

@[expose]
def w786 : List (Fin 4) := [0, 0, 1, 1, 1, 0, 1]

@[expose]
def w787 : List (Fin 4) := [3, 2, 1, 1, 1, 0, 1]

@[expose]
def w788 : List (Fin 4) := [0, 3, 2, 1, 1, 0, 1]

@[expose]
def w789 : List (Fin 4) := [2, 3, 2, 1, 1, 0, 1]

@[expose]
def w790 : List (Fin 4) := [1, 0, 1, 2, 1, 0, 1]

@[expose]
def w791 : List (Fin 4) := [3, 0, 1, 2, 1, 0, 1]

@[expose]
def w792 : List (Fin 4) := [1, 1, 1, 2, 1, 0, 1]

@[expose]
def w793 : List (Fin 4) := [2, 2, 2, 2, 1, 0, 1]

@[expose]
def w794 : List (Fin 4) := [3, 2, 2, 2, 1, 0, 1]

@[expose]
def w795 : List (Fin 4) := [2, 3, 2, 2, 1, 0, 1]

@[expose]
def w796 : List (Fin 4) := [3, 3, 2, 2, 1, 0, 1]

@[expose]
def w797 : List (Fin 4) := [0, 0, 3, 2, 1, 0, 1]

@[expose]
def w798 : List (Fin 4) := [3, 3, 3, 2, 1, 0, 1]

@[expose]
def w799 : List (Fin 4) := [0, 0, 1, 2, 3, 0, 1]

@[expose]
def w800 : List (Fin 4) := [3, 0, 1, 2, 3, 0, 1]

@[expose]
def w801 : List (Fin 4) := [1, 1, 1, 2, 3, 0, 1]

@[expose]
def w802 : List (Fin 4) := [2, 3, 2, 2, 3, 0, 1]

@[expose]
def w803 : List (Fin 4) := [3, 3, 2, 2, 3, 0, 1]

@[expose]
def w804 : List (Fin 4) := [1, 2, 3, 2, 3, 0, 1]

@[expose]
def w805 : List (Fin 4) := [2, 2, 3, 2, 3, 0, 1]

@[expose]
def w806 : List (Fin 4) := [3, 2, 3, 2, 3, 0, 1]

@[expose]
def w807 : List (Fin 4) := [2, 3, 3, 2, 3, 0, 1]

@[expose]
def w808 : List (Fin 4) := [3, 3, 3, 2, 3, 0, 1]

@[expose]
def w809 : List (Fin 4) := [3, 0, 0, 3, 3, 0, 1]

@[expose]
def w810 : List (Fin 4) := [1, 1, 0, 3, 3, 0, 1]

@[expose]
def w811 : List (Fin 4) := [1, 0, 3, 3, 3, 0, 1]

@[expose]
def w812 : List (Fin 4) := [3, 0, 3, 3, 3, 0, 1]

@[expose]
def w813 : List (Fin 4) := [3, 2, 3, 3, 3, 0, 1]

@[expose]
def w814 : List (Fin 4) := [3, 0, 0, 0, 0, 1, 1]

@[expose]
def w815 : List (Fin 4) := [0, 1, 0, 0, 0, 1, 1]

@[expose]
def w816 : List (Fin 4) := [3, 0, 1, 0, 0, 1, 1]

@[expose]
def w817 : List (Fin 4) := [2, 2, 1, 0, 0, 1, 1]

@[expose]
def w818 : List (Fin 4) := [3, 2, 3, 0, 0, 1, 1]

@[expose]
def w819 : List (Fin 4) := [0, 0, 0, 1, 0, 1, 1]

@[expose]
def w820 : List (Fin 4) := [1, 0, 0, 1, 0, 1, 1]

@[expose]
def w821 : List (Fin 4) := [2, 1, 0, 1, 0, 1, 1]

@[expose]
def w822 : List (Fin 4) := [0, 1, 1, 1, 0, 1, 1]

@[expose]
def w823 : List (Fin 4) := [1, 1, 1, 1, 0, 1, 1]

@[expose]
def w824 : List (Fin 4) := [3, 2, 2, 1, 0, 1, 1]

@[expose]
def w825 : List (Fin 4) := [1, 0, 0, 3, 0, 1, 1]

@[expose]
def w826 : List (Fin 4) := [3, 0, 0, 3, 0, 1, 1]

@[expose]
def w827 : List (Fin 4) := [0, 1, 0, 3, 0, 1, 1]

@[expose]
def w828 : List (Fin 4) := [1, 1, 0, 3, 0, 1, 1]

@[expose]
def w829 : List (Fin 4) := [0, 1, 2, 3, 0, 1, 1]

@[expose]
def w830 : List (Fin 4) := [3, 3, 2, 3, 0, 1, 1]

@[expose]
def w831 : List (Fin 4) := [2, 2, 3, 3, 0, 1, 1]

@[expose]
def w832 : List (Fin 4) := [0, 1, 1, 0, 1, 1, 1]

@[expose]
def w833 : List (Fin 4) := [1, 1, 1, 0, 1, 1, 1]

@[expose]
def w834 : List (Fin 4) := [1, 2, 1, 0, 1, 1, 1]

@[expose]
def w835 : List (Fin 4) := [2, 2, 1, 1, 2, 1, 1]

@[expose]
def w836 : List (Fin 4) := [1, 0, 1, 2, 2, 1, 1]

@[expose]
def w837 : List (Fin 4) := [3, 0, 1, 2, 2, 1, 1]

@[expose]
def w838 : List (Fin 4) := [1, 2, 1, 2, 2, 1, 1]

@[expose]
def w839 : List (Fin 4) := [3, 2, 1, 2, 2, 1, 1]

@[expose]
def w840 : List (Fin 4) := [0, 0, 3, 2, 2, 1, 1]

@[expose]
def w841 : List (Fin 4) := [1, 0, 3, 2, 2, 1, 1]

@[expose]
def w842 : List (Fin 4) := [2, 2, 3, 2, 2, 1, 1]

@[expose]
def w843 : List (Fin 4) := [3, 3, 3, 2, 2, 1, 1]

@[expose]
def w844 : List (Fin 4) := [3, 2, 3, 3, 2, 1, 1]

@[expose]
def w845 : List (Fin 4) := [0, 1, 1, 0, 1, 2, 1]

@[expose]
def w846 : List (Fin 4) := [1, 2, 3, 0, 1, 2, 1]

@[expose]
def w847 : List (Fin 4) := [2, 2, 3, 0, 1, 2, 1]

@[expose]
def w848 : List (Fin 4) := [0, 3, 0, 1, 1, 2, 1]

@[expose]
def w849 : List (Fin 4) := [2, 2, 1, 1, 1, 2, 1]

@[expose]
def w850 : List (Fin 4) := [0, 1, 2, 1, 1, 2, 1]

@[expose]
def w851 : List (Fin 4) := [3, 2, 2, 1, 1, 2, 1]

@[expose]
def w852 : List (Fin 4) := [0, 3, 3, 2, 1, 2, 1]

@[expose]
def w853 : List (Fin 4) := [1, 2, 1, 1, 2, 2, 1]

@[expose]
def w854 : List (Fin 4) := [3, 2, 1, 1, 2, 2, 1]

@[expose]
def w855 : List (Fin 4) := [2, 3, 2, 2, 2, 2, 1]

@[expose]
def w856 : List (Fin 4) := [3, 3, 2, 2, 2, 2, 1]

@[expose]
def w857 : List (Fin 4) := [0, 0, 3, 3, 2, 2, 1]

@[expose]
def w858 : List (Fin 4) := [1, 0, 3, 3, 2, 2, 1]

@[expose]
def w859 : List (Fin 4) := [3, 0, 3, 3, 2, 2, 1]

@[expose]
def w860 : List (Fin 4) := [2, 2, 3, 3, 2, 2, 1]

@[expose]
def w861 : List (Fin 4) := [3, 3, 0, 0, 3, 2, 1]

@[expose]
def w862 : List (Fin 4) := [1, 2, 1, 0, 3, 2, 1]

@[expose]
def w863 : List (Fin 4) := [0, 1, 2, 3, 3, 2, 1]

@[expose]
def w864 : List (Fin 4) := [1, 2, 2, 3, 3, 2, 1]

@[expose]
def w865 : List (Fin 4) := [3, 2, 2, 3, 3, 2, 1]

@[expose]
def w866 : List (Fin 4) := [0, 3, 0, 0, 1, 2, 2]

@[expose]
def w867 : List (Fin 4) := [2, 3, 0, 0, 1, 2, 2]

@[expose]
def w868 : List (Fin 4) := [3, 3, 0, 0, 1, 2, 2]

@[expose]
def w869 : List (Fin 4) := [1, 2, 3, 0, 1, 2, 2]

@[expose]
def w870 : List (Fin 4) := [2, 2, 3, 0, 1, 2, 2]

@[expose]
def w871 : List (Fin 4) := [3, 2, 3, 0, 1, 2, 2]

@[expose]
def w872 : List (Fin 4) := [3, 3, 3, 0, 1, 2, 2]

@[expose]
def w873 : List (Fin 4) := [1, 0, 0, 1, 1, 2, 2]

@[expose]
def w874 : List (Fin 4) := [0, 3, 0, 1, 1, 2, 2]

@[expose]
def w875 : List (Fin 4) := [3, 3, 0, 1, 1, 2, 2]

@[expose]
def w876 : List (Fin 4) := [3, 2, 2, 1, 1, 2, 2]

@[expose]
def w877 : List (Fin 4) := [0, 0, 1, 2, 1, 2, 2]

@[expose]
def w878 : List (Fin 4) := [1, 0, 1, 2, 1, 2, 2]

@[expose]
def w879 : List (Fin 4) := [1, 1, 1, 2, 1, 2, 2]

@[expose]
def w880 : List (Fin 4) := [2, 1, 2, 2, 1, 2, 2]

@[expose]
def w881 : List (Fin 4) := [2, 3, 3, 2, 1, 2, 2]

@[expose]
def w882 : List (Fin 4) := [0, 0, 1, 2, 2, 2, 2]

@[expose]
def w883 : List (Fin 4) := [1, 0, 1, 2, 2, 2, 2]

@[expose]
def w884 : List (Fin 4) := [0, 0, 3, 2, 2, 2, 2]

@[expose]
def w885 : List (Fin 4) := [1, 0, 3, 2, 2, 2, 2]

@[expose]
def w886 : List (Fin 4) := [0, 3, 2, 3, 2, 2, 2]

@[expose]
def w887 : List (Fin 4) := [0, 0, 1, 2, 3, 2, 2]

@[expose]
def w888 : List (Fin 4) := [2, 2, 3, 2, 3, 2, 2]

@[expose]
def w889 : List (Fin 4) := [3, 2, 3, 2, 3, 2, 2]

@[expose]
def w890 : List (Fin 4) := [0, 3, 3, 2, 3, 2, 2]

@[expose]
def w891 : List (Fin 4) := [2, 3, 3, 2, 3, 2, 2]

@[expose]
def w892 : List (Fin 4) := [2, 2, 2, 3, 3, 2, 2]

@[expose]
def w893 : List (Fin 4) := [2, 2, 3, 3, 3, 2, 2]

@[expose]
def w894 : List (Fin 4) := [0, 0, 1, 0, 0, 3, 2]

@[expose]
def w895 : List (Fin 4) := [2, 1, 1, 0, 0, 3, 2]

@[expose]
def w896 : List (Fin 4) := [0, 3, 3, 0, 0, 3, 2]

@[expose]
def w897 : List (Fin 4) := [2, 1, 1, 1, 0, 3, 2]

@[expose]
def w898 : List (Fin 4) := [0, 0, 0, 3, 0, 3, 2]

@[expose]
def w899 : List (Fin 4) := [1, 0, 0, 3, 0, 3, 2]

@[expose]
def w900 : List (Fin 4) := [0, 0, 1, 2, 2, 3, 2]

@[expose]
def w901 : List (Fin 4) := [3, 0, 1, 2, 2, 3, 2]

@[expose]
def w902 : List (Fin 4) := [1, 2, 1, 2, 2, 3, 2]

@[expose]
def w903 : List (Fin 4) := [3, 2, 2, 2, 2, 3, 2]

@[expose]
def w904 : List (Fin 4) := [2, 2, 3, 2, 2, 3, 2]

@[expose]
def w905 : List (Fin 4) := [2, 3, 3, 2, 2, 3, 2]

@[expose]
def w906 : List (Fin 4) := [3, 3, 3, 2, 2, 3, 2]

@[expose]
def w907 : List (Fin 4) := [1, 2, 3, 3, 2, 3, 2]

@[expose]
def w908 : List (Fin 4) := [0, 1, 1, 0, 3, 3, 2]

@[expose]
def w909 : List (Fin 4) := [2, 3, 3, 0, 3, 3, 2]

@[expose]
def w910 : List (Fin 4) := [3, 3, 2, 2, 3, 3, 2]

@[expose]
def w911 : List (Fin 4) := [3, 0, 1, 0, 0, 0, 0, 0]

@[expose]
def w912 : List (Fin 4) := [0, 1, 1, 0, 0, 0, 0, 0]

@[expose]
def w913 : List (Fin 4) := [3, 0, 0, 1, 0, 0, 0, 0]

@[expose]
def w914 : List (Fin 4) := [1, 1, 0, 1, 0, 0, 0, 0]

@[expose]
def w915 : List (Fin 4) := [1, 0, 1, 1, 0, 0, 0, 0]

@[expose]
def w916 : List (Fin 4) := [3, 0, 1, 1, 0, 0, 0, 0]

@[expose]
def w917 : List (Fin 4) := [2, 2, 1, 1, 0, 0, 0, 0]

@[expose]
def w918 : List (Fin 4) := [1, 2, 2, 1, 0, 0, 0, 0]

@[expose]
def w919 : List (Fin 4) := [0, 3, 2, 1, 0, 0, 0, 0]

@[expose]
def w920 : List (Fin 4) := [0, 0, 1, 0, 1, 0, 0, 0]

@[expose]
def w921 : List (Fin 4) := [1, 0, 1, 0, 1, 0, 0, 0]

@[expose]
def w922 : List (Fin 4) := [2, 2, 1, 0, 1, 0, 0, 0]

@[expose]
def w923 : List (Fin 4) := [1, 1, 0, 1, 1, 0, 0, 0]

@[expose]
def w924 : List (Fin 4) := [2, 1, 0, 1, 1, 0, 0, 0]

@[expose]
def w925 : List (Fin 4) := [1, 1, 2, 2, 1, 0, 0, 0]

@[expose]
def w926 : List (Fin 4) := [3, 2, 2, 2, 1, 0, 0, 0]

@[expose]
def w927 : List (Fin 4) := [0, 3, 2, 2, 1, 0, 0, 0]

@[expose]
def w928 : List (Fin 4) := [1, 0, 3, 2, 1, 0, 0, 0]

@[expose]
def w929 : List (Fin 4) := [1, 2, 2, 2, 3, 0, 0, 0]

@[expose]
def w930 : List (Fin 4) := [3, 2, 2, 1, 0, 1, 0, 0]

@[expose]
def w931 : List (Fin 4) := [2, 3, 0, 3, 0, 1, 0, 0]

@[expose]
def w932 : List (Fin 4) := [2, 3, 0, 0, 1, 1, 0, 0]

@[expose]
def w933 : List (Fin 4) := [3, 3, 0, 0, 1, 1, 0, 0]

@[expose]
def w934 : List (Fin 4) := [3, 2, 1, 0, 1, 1, 0, 0]

@[expose]
def w935 : List (Fin 4) := [3, 0, 0, 1, 1, 1, 0, 0]

@[expose]
def w936 : List (Fin 4) := [1, 0, 3, 2, 1, 1, 0, 0]

@[expose]
def w937 : List (Fin 4) := [0, 1, 1, 2, 2, 1, 0, 0]

@[expose]
def w938 : List (Fin 4) := [2, 1, 2, 2, 2, 3, 0, 0]

@[expose]
def w939 : List (Fin 4) := [3, 2, 3, 2, 2, 3, 0, 0]

@[expose]
def w940 : List (Fin 4) := [2, 3, 3, 2, 2, 3, 0, 0]

@[expose]
def w941 : List (Fin 4) := [3, 3, 0, 0, 3, 3, 0, 0]

@[expose]
def w942 : List (Fin 4) := [3, 2, 2, 2, 3, 3, 0, 0]

@[expose]
def w943 : List (Fin 4) := [0, 3, 0, 1, 0, 0, 1, 0]

@[expose]
def w944 : List (Fin 4) := [0, 1, 2, 1, 0, 0, 1, 0]

@[expose]
def w945 : List (Fin 4) := [1, 2, 1, 0, 1, 0, 1, 0]

@[expose]
def w946 : List (Fin 4) := [0, 3, 2, 1, 1, 0, 1, 0]

@[expose]
def w947 : List (Fin 4) := [0, 0, 0, 0, 3, 0, 1, 0]

@[expose]
def w948 : List (Fin 4) := [1, 0, 3, 0, 3, 0, 1, 0]

@[expose]
def w949 : List (Fin 4) := [3, 2, 3, 0, 3, 0, 1, 0]

@[expose]
def w950 : List (Fin 4) := [0, 1, 0, 0, 0, 1, 1, 0]

@[expose]
def w951 : List (Fin 4) := [2, 2, 1, 0, 0, 1, 1, 0]

@[expose]
def w952 : List (Fin 4) := [3, 2, 3, 0, 0, 1, 1, 0]

@[expose]
def w953 : List (Fin 4) := [0, 0, 0, 1, 0, 1, 1, 0]

@[expose]
def w954 : List (Fin 4) := [0, 3, 2, 1, 0, 1, 1, 0]

@[expose]
def w955 : List (Fin 4) := [3, 0, 3, 3, 0, 1, 1, 0]

@[expose]
def w956 : List (Fin 4) := [2, 2, 2, 2, 1, 1, 1, 0]

@[expose]
def w957 : List (Fin 4) := [0, 3, 2, 2, 1, 1, 1, 0]

@[expose]
def w958 : List (Fin 4) := [1, 0, 3, 2, 1, 1, 1, 0]

@[expose]
def w959 : List (Fin 4) := [3, 3, 3, 2, 1, 1, 1, 0]

@[expose]
def w960 : List (Fin 4) := [1, 0, 3, 0, 1, 2, 1, 0]

@[expose]
def w961 : List (Fin 4) := [3, 0, 1, 1, 1, 2, 1, 0]

@[expose]
def w962 : List (Fin 4) := [2, 1, 0, 1, 2, 2, 1, 0]

@[expose]
def w963 : List (Fin 4) := [3, 0, 1, 1, 2, 2, 1, 0]

@[expose]
def w964 : List (Fin 4) := [3, 2, 3, 0, 3, 2, 1, 0]

@[expose]
def w965 : List (Fin 4) := [0, 0, 0, 1, 1, 2, 3, 0]

@[expose]
def w966 : List (Fin 4) := [0, 1, 2, 2, 2, 2, 3, 0]

@[expose]
def w967 : List (Fin 4) := [3, 0, 3, 2, 2, 2, 3, 0]

@[expose]
def w968 : List (Fin 4) := [3, 2, 3, 0, 3, 2, 3, 0]

@[expose]
def w969 : List (Fin 4) := [1, 0, 3, 0, 0, 3, 3, 0]

@[expose]
def w970 : List (Fin 4) := [1, 2, 1, 1, 2, 3, 3, 0]

@[expose]
def w971 : List (Fin 4) := [0, 0, 1, 2, 2, 3, 3, 0]

@[expose]
def w972 : List (Fin 4) := [2, 3, 2, 3, 2, 3, 3, 0]

@[expose]
def w973 : List (Fin 4) := [3, 0, 3, 3, 2, 3, 3, 0]

@[expose]
def w974 : List (Fin 4) := [0, 3, 3, 0, 0, 0, 0, 1]

@[expose]
def w975 : List (Fin 4) := [2, 2, 1, 1, 0, 0, 0, 1]

@[expose]
def w976 : List (Fin 4) := [1, 2, 1, 2, 3, 0, 0, 1]

@[expose]
def w977 : List (Fin 4) := [2, 2, 1, 2, 3, 0, 0, 1]

@[expose]
def w978 : List (Fin 4) := [2, 3, 0, 3, 3, 0, 0, 1]

@[expose]
def w979 : List (Fin 4) := [0, 1, 0, 1, 0, 1, 0, 1]

@[expose]
def w980 : List (Fin 4) := [1, 2, 3, 2, 2, 1, 0, 1]

@[expose]
def w981 : List (Fin 4) := [3, 3, 0, 1, 2, 3, 0, 1]

@[expose]
def w982 : List (Fin 4) := [2, 3, 2, 2, 1, 0, 1, 1]

@[expose]
def w983 : List (Fin 4) := [1, 0, 1, 0, 3, 0, 1, 1]

@[expose]
def w984 : List (Fin 4) := [0, 1, 2, 1, 0, 1, 1, 1]

@[expose]
def w985 : List (Fin 4) := [2, 2, 3, 0, 0, 1, 2, 2]

@[expose]
def w986 : List (Fin 4) := [3, 3, 2, 3, 2, 3, 2, 2]

@[expose]
def w987 : List (Fin 4) := [1, 2, 3, 3, 2, 3, 2, 2]

@[expose]
def w988 : List (Fin 4) := [0, 0, 3, 2, 2, 1, 0, 0, 0]

@[expose]
def w989 : List (Fin 4) := [2, 2, 3, 3, 2, 2, 3, 0, 0]

end TauCeti.Sporadic.Mathieu.M11CosetCertificate
