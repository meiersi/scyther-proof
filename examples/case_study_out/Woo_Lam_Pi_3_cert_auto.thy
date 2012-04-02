theory Woo_Lam_Pi_3_cert_auto begin

section{* Woo and Lam Pi 3 *}

text{*
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We prove non-injective synchronization, which is stronger than the
       authenticatino requirement stated in the description.

    3. We added the identity B to the plaintext of the fourth message, as the
       server must know it for looking up the key k(B,S).

*}

protocol WooLamPi
{
  role A
  {
    Send_1( A )
    Recv_2( ?Nb )
    Send_3( {'3', ?Nb}k(A,S) )
  }
  
  role B
  {
    Recv_1( ?A )
    Send_2( ~Nb )
    Recv_3( ?Ticket )
    Send_4(B, {'4', ?A, ?Ticket}k(B,S))
    Recv_5( {'5', ?A, ~Nb}k(B,S) )
  }
  
  role S
  {
    Recv_4(?B, {'4', ?A, {'3', ?Nb}k(?A,S)}k(?B,S))
    Send_5( {'5', ?A, ?Nb}k(?B,S) )
  }
}

property (of WooLamPi) WooLamPi_msc_typing:
  "A@B :: Known(B_1)
   A@S :: (Known(S_4) | Agent)
   B@S :: Known(S_4)
   Nb@A :: Known(A_2)
   Nb@S :: (Known(S_4) | Nb@B)
   Ticket@B :: Known(B_3)"
proof
  case S_4_A
  sources( {'4', ?A#0, {'3', ?Nb#0}k(?A#0,S#0)}k(?B#0,S#0) )
  qed (2 trivial)
next
  case S_4_B
  tautology
next
  case S_4_Nb
  sources( {'4', ?A#0, {'3', ?Nb#0}k(?A#0,S#0)}k(?B#0,S#0) )
    case fake
    sources( {'3', ?Nb#0}k(?A#0,S#0) )
    qed (2 trivial)
  next
    case (B_4_enc #1)
    sources( {'3', ?Nb#0}k(?A#0,S#0) )
    qed (2 trivial)
  qed
qed

subsection{* Security Properties *}

property (of WooLamPi) B_noninjective_agreement:
  for all #2 the premises
    "role( #2 ) = B"
    "uncompromised( B#2, S#2, ?A#2 )"
    "step(#2, B_5)"
  imply "(? #1. role( #1 ) = A & A#1 = ?A#2 & S#1 = S#2 & ?Nb#1 = ~Nb#2)"
saturate
resolve 'WooLamPi_msc_typing
sources( {'5', ?A#2, ~Nb#2}k(B#2,S#2) )
  case fake
  contradicts secrecy of k(B#2,S#2)
next
  case (S_5_enc #3)
  sources( {'4', ?A#2, {'3', ~Nb#2}k(?A#2,S#2)}k(B#2,S#2) )
    case fake
    contradicts secrecy of k(B#2,S#2)
  next
    case (B_4_enc #4)
    sources( {'3', ~Nb#2}k(?A#2,S#2) )
      case fake
      contradicts secrecy of k(?A#2,S#2)
    next
      case (A_3_enc #5)
      tautology
    qed
  qed
qed

end