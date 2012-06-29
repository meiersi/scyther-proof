theory A imports Main begin

locale A =
  fixes L :: "nat list" and
        d :: "nat"
  assumes "d \<in> set L"

definition FOUR :: "nat list"
  where "FOUR = [ 1,2,3,4]"

locale B =
  fixes f :: nat
  assumes a: "F \<in> set FOUR"

sublocale B \<subseteq> A FOUR f
 apply (unfold_locales)
 