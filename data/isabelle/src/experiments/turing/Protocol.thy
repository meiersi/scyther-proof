theory Protocol imports Main begin

  
datatype ('msg, 'sig, 's) suspension =
    Fresh          "'msg \<Rightarrow> 's \<Rightarrow> ('s \<times> ('msg, 'sig, 's) suspension)"
  | Receive        "'msg \<Rightarrow> 's \<Rightarrow> ('s \<times> ('msg, 'sig, 's) suspension)"
  | Send    "'msg"         "'s \<Rightarrow> ('s \<times> ('msg, 'sig, 's) suspension)"
  | Signal  "'sig"         "'s \<Rightarrow> ('s \<times> ('msg, 'sig, 's) suspension)"
  | Repl                   "'s \<Rightarrow> ('s \<times> ('msg, 'sig, 's) suspension) list" 
  | Done

types ('msg, 'sig, 's) proto = "'s \<times> ('msg, 'sig, 's) suspension"

types ('g, 's) cond = "('g \<Rightarrow> 's set) \<times> ('g \<Rightarrow> 's set)"

datatype ('msg, 'sig, 's, 'g) suspensionA =
    FreshA          "'msg \<Rightarrow> 's \<Rightarrow> ('s \<times> ('msg, 'sig, 's, 'g) suspensionA)" "'msg \<Rightarrow> ('g, 's) cond"
  | ReceiveA        "'msg \<Rightarrow> 's \<Rightarrow> ('s \<times> ('msg, 'sig, 's, 'g) suspensionA)" "'msg \<Rightarrow> ('g, 's) cond"
  | SendA    "'msg"         "'s \<Rightarrow> ('s \<times> ('msg, 'sig, 's, 'g) suspensionA)"        "('g, 's) cond" "'g \<Rightarrow> 's \<Rightarrow> 'msg set"
  | SignalA  "'sig"         "'s \<Rightarrow> ('s \<times> ('msg, 'sig, 's, 'g) suspensionA)"        "('g, 's) cond" "'g \<Rightarrow> 's \<Rightarrow> 'sig set"
  | ReplA                   "'s \<Rightarrow> (('s \<times> ('msg, 'sig, 's, 'g) suspensionA) \<times> ('g, 's) cond) list"
  | DoneA 


thm suspension.induct
thm suspensionA.induct

definition replicate :: "('s \<Rightarrow> 'sg) \<Rightarrow> (('msg, 'sig, 'si) proto \<Rightarrow> 'sg) \<Rightarrow> ('msg, 'sig, 's) proto \<Rightarrow> ('msg, 'sig, 'sg) proto"
where
  "replicate P = Replicate 






