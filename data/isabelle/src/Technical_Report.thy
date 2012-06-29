(* 
  NOTE: This file takes quite some time to load due
        to the large number of examples included.
*)
theory Technical_Report
imports
(* Preliminaries *)

  "ESPLogic/DistinctList"
  "ESPLogic/HOL_ext"
  "ESPLogic/Hints"


(* Standard Security Protocol Model *)

  "ESPLogic/Protocol"

  "ESPLogic/ExecMessage"
  (* "ESPLogic/Subst"         *)
  (* "ESPLogic/StandardModel" -- not yet adapted to new explicit model *)

(* Security Proof Construction *)

  "ESPLogic/ExplicitModel"
  "ESPLogic/InferenceRules"
  "ESPLogic/WeakTyping"
  "ESPLogic/Capabilities"

  "ESPLogic/Syntax"
  "ESPLogic/Automation"

  "ESPLogic"
  "Tutorial"
(* Case Studies *)

   "compromising_adversaries/All_Examples" 
begin

(* The purpose of this file is to load all stable theories in order
   to generate the technical report detailing the results of the theories.
*)

end


