theory EquationalTheory
imports Main
begin


section{* Cryptographic Messages *}

types id = string

types tid = nat

datatype msg 
  = Const id
  | Agent id
  | Nonce id tid
  | S "id set"
  | PK msg
  | SK msg  
  | Hash msg
  | Tup  msg msg
  | Enc  msg msg

text{*Concrete syntax: messages appear as {|A,B,NA|}, etc...*}
syntax
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2{|_,/ _|})")

syntax (xsymbols)
  "@MTuple"      :: "['a, args] => 'a * 'b"       ("(2\<lbrace>_,/ _\<rbrace>)")

translations
  "{|x, y, z|}"   == "{|x, {|y, z|}|}"
  "{|x, y|}"      == "Tup x y"


subsection{* Operations *}

fun invkey :: "msg \<Rightarrow> msg"
where
  "invkey (PK m) = SK m"
| "invkey (SK m) = PK m"
| "invkey m      = m"

fun pairParts :: "msg \<Rightarrow> msg set"
where
  "pairParts (Tup x y) = 
      insert (Tup x y) (pairParts x \<union> pairParts y)"
| "pairParts m = {m}"


section{* Protocols *}

types 's proto = "msg \<Rightarrow> (msg option \<times> 's) set"

section{* Explicit Execution Model *}

datatype 's basicevent = 
    Step "msg option \<times> 's"
  | Learns "msg set"

types 's trace = "'s basicevent list"

fun knows :: "'s trace \<Rightarrow> msg set"
where
  "knows [] = {}"
| "knows (Learns M # t) = M \<union> knows t"
| "knows (Step res # t) = knows t"

abbreviation newMsgs :: "'s trace \<Rightarrow> msg \<Rightarrow> msg set"
where "newMsgs t m \<equiv> pairParts m - knows t"

types 's state = "'s trace \<times> 's"

inductive_set 
  reachable :: "'s set \<Rightarrow> 's proto \<Rightarrow> 's state set" 
  for Q\<^isub>0  :: "'s set"
  and  P  :: "'s proto"
where
  init:  
  "q\<^isub>0 \<in> Q\<^isub>0
   \<Longrightarrow> ([Learns IK0],q\<^isub>0) \<in> reachable Q\<^isub>0 P"

| send:  
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
      m \<in> knows t; 
      (Some m', q') \<in> P m
   \<rbrakk> \<Longrightarrow> 
   (t @ [Step (Some m', q'), Learns (newMsgs t m')], q')
    \<in> reachable Q\<^isub>0 P"

| recv:
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
      m \<in> knows t; 
      (None, q') \<in> P m
   \<rbrakk> \<Longrightarrow> 
   (t @ [Step (None, q')], q') \<in> reachable Q\<^isub>0 P"

| hash:  
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
     m \<in> knows t;
     Hash m \<notin> knows t
   \<rbrakk> \<Longrightarrow> 
     (t @ [Learns {Hash m}], q) \<in> reachable Q\<^isub>0 P"

| tuple: 
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
     x \<in> knows t;
     y \<in> knows t;
     Tup x y \<notin> knows t
   \<rbrakk> \<Longrightarrow> 
     (t @ [Learns {Tup x y}], q) \<in> reachable Q\<^isub>0 P"

| encr:  
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
     m \<in> knows t;
     k \<in> knows t;
     Enc m k \<notin> knows t
   \<rbrakk> \<Longrightarrow> 
     (t @ [Learns {Enc m k}], q) \<in> reachable Q\<^isub>0 P"

| decr:  
  "\<lbrakk> (t, q) \<in> reachable Q\<^isub>0 P;
     Enc m k \<in> knows t;
     invkey k \<in> knows t
   \<rbrakk> \<Longrightarrow> 
     (t @ [Learns (newMsgs t m)], q) \<in> reachable Q\<^isub>0 P"

locale reachable_state =  
  fixes Q\<^isub>0 :: "'s set"
  and   P  :: "'s proto"
  and   t  :: "'s trace"
  and   q  :: "'s"
  assumes reachable [simp,intro!]: "(t,q) \<in> reachable Q\<^isub>0 P"
begin
  text{* A local variant of the induction rule of @{term "reachable"}. *}
  lemmas reachable_induct = reachable.induct
    [ OF reachable
    , rule_format
    , consumes 0
    , case_names init send recv hash tuple encr decr
    ]
end
