(*****************************************************************************
 * ESPL --- an embedded security protocol logic
 *          http://people.inf.ethz.ch/meiersi/espl/
 *
 *   Copyright (c) 2009-2011, Simon Meier, ETH Zurich, Switzerland
 *
 * Extension to compromising adversaries:
 *
 *   Copyright (c) 2010-2011, Martin Schaub, ETH Zurich, Switzerland
 *
 * All rights reserved. See file LICENCE for more information.
 ******************************************************************************)
(* 6th Generation: Adapt Syntax to make it more readable, also in ASCII notation 

   Adapted to paper.
*)
theory Syntax
imports
  ExplicitModel
begin

section{* User Level Syntax *}

text{*
  The syntax adaption is currently done in a separate file and AFTER all developments of
  the logic, because it is not fixed yet.
*}


subsubsection{* General Cryptographic Messages *}

notation (xsymbols) ExecMessage.inv  ("[_]\<^isup>-\<^isup>1" [60] 58)


subsubsection{* Specification Messages *}

abbreviation "sC"  where "sC  x \<equiv> PConst x"
abbreviation "sN"  where "sN  x \<equiv> PFresh x"
abbreviation "sMV" where "sMV x \<equiv> PVar (MVar x)"
abbreviation "sAV" where "sAV x \<equiv> PVar (AVar x)"

text{* 
  Note the following abbreviations are kept for 
  backwards compatibility. They are deprecated for 
  new developments.
*}
abbreviation "sLC"   where "sLC  x \<equiv> PConst x"
abbreviation "sLN"   where "sLN  x \<equiv> PFresh x"
abbreviation "sLMV"  where "sLMV x \<equiv> PVar (MVar x)"
abbreviation "sLAV"  where "sLAV x \<equiv> PVar (AVar x)"

abbreviation "sPK"   where "sPK x   \<equiv> PAsymPK  (sAV x)"
abbreviation "sSK"   where "sSK x   \<equiv> PAsymSK  (sAV x)"
abbreviation "sK"    where "sK x y  \<equiv> PSymK    (sAV x) (sAV y)"
abbreviation "sShrK" where "sShrK A \<equiv> PShrK    A"

syntax
  "@PTuple"      :: "['a, args] => 'a * 'b"       ("(2<|_,/ _|>)")

syntax (xsymbols)
  "@PTuple"      :: "['a, args] => 'a * 'b"       ("(2\<langle>_,/ _\<rangle>)")

translations
  "<|x, y, z|>"   == "<|x, <|y, z|> |>"
  "<|x, y|>"      == "CONST PTup x y"


subsubsection{* Execution Messages *}

abbreviation "C"  where "C    \<equiv> EConst"
abbreviation "N"  where "N    \<equiv> ENonce"
abbreviation "MV" where "MV x i \<equiv> (MVar x, i)"
abbreviation "AV" where "AV x i \<equiv> (AVar x, i)"

abbreviation "LC"  where "LC  x \<equiv> Lit (C x)"
abbreviation "LN"  where "LN  x i \<equiv> Lit (N x i)"

abbreviation "LAg"  where "LAg x \<equiv> Lit (EAgent x)"

end
