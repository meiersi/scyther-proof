theory Infer
imports
  Main
begin


types id = string

text{*
  A general message datatype which is polymorphic over 
  the type of its literals.
*}

datatype 'lit msg = Lit  "'lit"
                  | Tup  "'lit msg" "'lit msg"
                  | Enc  "'lit msg" "'lit msg"
                  | Hash "'lit msg"
                  | K    "'lit msg" "'lit msg"
                  | PK   "'lit msg"
                  | SK   "'lit msg"


text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "Tup x y"

fun inv :: "'lit msg \<Rightarrow> 'lit msg"
where
  "inv (PK m) = SK m"
| "inv (SK m) = PK m"
| "inv m      = m"

coinductive_set
  infer :: "'a msg set \<Rightarrow> 'a msg set"
  for M :: "'a msg set"
where
  Inj [simp,intro]: "m \<in> M                     \<Longrightarrow> m \<in> infer M"
| Fst:  "Tup x y \<in> infer M                      \<Longrightarrow> x \<in> infer M"
| Snd:  "Tup x y \<in> infer M                      \<Longrightarrow> y \<in> infer M"
| Dec:  "\<lbrakk> Enc m k \<in> infer M; inv k \<in> infer M \<rbrakk> \<Longrightarrow> m \<in> infer M"
| Tup:  "\<lbrakk> x \<in> infer M; y \<in> infer M \<rbrakk>           \<Longrightarrow> Tup x y \<in> infer M"
| Hash: "m \<in> infer M                            \<Longrightarrow> Hash m \<in> infer M"
| Enc:  "\<lbrakk> m \<in> infer M; k \<in> infer M \<rbrakk>           \<Longrightarrow> Enc m k \<in> infer M"

thm infer.coinduct
thm infer.cases


inductive inferInj :: "'a msg set \<Rightarrow> 'a msg list \<Rightarrow> 'a msg list set"
  for M  :: "'a msg set"
  and t0 :: "'a msg list"
where
  "\<lbrakk> t \<in> inferInj M t0; m \<notin> set (t0 @ t); m \<in> M \<rbrakk> \<Longrightarrow> t@[m] \<in> inferInj M t0"

inductive inferFst :: "'a msg set \<Rightarrow> 'a list set \<Rightarrow> 'a list set"
  for M  :: "'a msg set"
  and t0 :: "'a msg list"
where
  "\<lbrakk> t \<in> inferFst M t0; m \<notin> set (t0 @ t); \<lbrace>m,y\<rbrace> \<in> set (t0 @ t)