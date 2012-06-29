theory CoinductiveDY
imports Main
begin


datatype msg = Nonce nat
             | Tup msg msg
             | Enc msg msg

coinductive_set infer :: "msg set \<Rightarrow> msg set"
for M :: "msg set"
where
  Inj: "m \<in> M \<Longrightarrow> m \<in> infer M"
| Tup: "\<lbrakk> x \<in> infer M; y \<in> infer M \<rbrakk> \<Longrightarrow> Tup x y \<in> infer M"
| Enc: "\<lbrakk> m \<in> infer M; k \<in> infer M \<rbrakk> \<Longrightarrow> Enc m k \<in> infer M"
| Dec: "\<lbrakk> Enc m k \<in> infer M; k \<in> infer M \<rbrakk> \<Longrightarrow> m \<in> infer M"

lemma infer_empty [simp]: "x \<notin> infer {}"
proof
  show "x \<in> infer {} \<Longrightarrow> False"
    apply(erule infer.cases)
    apply(auto)
  

thm infer.coinduct

  proof(cases rule: infer.coinduct)