theory Lowe_modified_BAN_concrete_Andrew_Secure_RPC_cert_auto begin

section{* Lowe modified BAN concrete Andrew Secure RPC *}

text{*
  Modeled after the model in the SPORE library.

  Notable differences:

    1. 'succ(x)' is invertible. Hence, we just model it as a tuple ('succ',x) of
       a global constant 'succ' and the variable x.  This means that we only
       exploit the tagging properties of 'succ', but do not assume any
       information hiding.

    2. Instead of implicit typing, we are using explicit global constants to
       discern messages.
*}

protocol Andrew
{ role A
  { Send_1(A, ~Na)
    Recv_2(?B, {'2', ~Na, ?Kab, ?B}k[A,?B])
    Send_3( {'3', ~Na}?Kab )
    Recv_4( ?Nb )
  }
  
  role B
  { Recv_1(?A, ?Na)
    Send_2(B, {'2', ?Na, ~Kab, B}k[?A,B])
    Recv_3( {'3', ?Na}~Kab )
    Send_4( ~Nb )
  }
}

property (of Andrew) Andrew_msc_typing:
  "A@B :: Known(B_1)
   B@A :: Known(A_2)
   Kab@A :: (Known(A_2) | Kab@B)
   Na@B :: Known(B_1)
   Nb@A :: Known(A_4)"
proof
  case A_2_B
  tautology
next
  case A_2_Kab
  sources( {'2', ~Na#0, ?Kab#0, ?B#0}k[A#0,?B#0] )
  qed (2 trivial)
next
  case B_1_A
  tautology
next
  case B_1_Na
  tautology
qed

text{* 
Note the additional B identity in the second message above. It guarantees that
despite using a bidirectional longterm symmetric key, we have agreement on the
involved roles.
*}

subsection{* Security Properties *}

property (of Andrew) B_sec_Kab:
  for all #0 the premises
    "role( #0 ) = B"
    "uncompromised( B#0, ?A#0 )"
    "knows(~Kab#0)"
  imply "False"
resolve 'Andrew_msc_typing
sources( ~Kab#0 )
  case B_2_Kab
  contradicts secrecy of k[B#0,?A#0]
qed

property (of Andrew) A_sec_Kab:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, ?B#0 )"
    "step(#0, A_2)"
    "knows(?Kab#0)"
  imply "False"
saturate
resolve 'Andrew_msc_typing
sources( {'2', ~Na#0, ?Kab#0, ?B#0}k[A#0,?B#0] )
  case fake
  contradicts secrecy of k[A#0,?B#0]
next
  case (B_2_enc #1)
  contradictory due to 'B_sec_Kab'
qed

property (of Andrew) A_noninjective_agreement:
  for all #1 the premises
    "role( #1 ) = A"
    "uncompromised( A#1, ?B#1 )"
    "step(#1, A_2)"
  imply
    "(? #2.
        role( #2 ) = B &
        A#1 = ?A#2 & ?B#1 = B#2 & ~Na#1 = ?Na#2 & ?Kab#1 = ~Kab#2)"
saturate
resolve 'Andrew_msc_typing
sources( {'2', ~Na#1, ?Kab#1, ?B#1}k[A#1,?B#1] )
  case fake
  contradicts secrecy of k[A#1,?B#1]
next
  case (B_2_enc #2)
  tautology
qed

property (of Andrew) B_noninjective_agreement:
  for all #1 the premises
    "role( #1 ) = B"
    "uncompromised( B#1, ?A#1 )"
    "step(#1, B_3)"
  imply
    "(? #2.
        role( #2 ) = A &
        ?A#1 = A#2 & B#1 = ?B#2 & ?Na#1 = ~Na#2 & ~Kab#1 = ?Kab#2)"
saturate
resolve 'Andrew_msc_typing
sources( {'3', ?Na#1}~Kab#1 )
  case fake
  contradictory due to 'B_sec_Kab'
next
  case (A_3_enc #2)
  sources( {'2', ~Na#2, ~Kab#1, ?B#2}k[A#2,?B#2] )
    case fake
    contradictory due to 'B_sec_Kab'
  next
    case (B_2_enc #3)
    tautology
  qed
qed

end