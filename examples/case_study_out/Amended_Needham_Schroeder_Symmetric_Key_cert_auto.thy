theory Amended_Needham_Schroeder_Symmetric_Key_cert_auto begin

section{* The Amended Needham Schroeder Symmetric Key Protocol *}

text{*
  Modelled according to the desciprtion in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/nssk_amended.html

  Notable differences:

    1. Instead of assuming a typed model we are using global constants to
       ensure distinctness of messages from different steps.

    2. We use the weaker authentication property of non-injective agreement
       instead of injective agreement because the later cannot yet be proven
       automatically. However, based on the resulting Isabelle file it would be
       easy to also derive injective agreement from the proven non-injective
       variants.

    3. We model the invertible function 'dec(x)' as tupling with a fixed public
       constant 'dec'; i.e., we only exploit 'dec's tagging capabilities.

    TODO: Check that this protocol can also be verified with bidirectional
    shared keys.
*}

protocol AmendedNS
{
  role I
  {
    Send_1( I )
    Recv_2( ?RequestR )
    Send_3(I, R, ~ni, ?RequestR)
    Recv_4(?S, {'2', ~ni, R, ?kIR, ?TicketR}k(I,?S))
    Send_5( ?TicketR )
    Recv_6( {'4', ?nr}?kIR )
    Send_7( {'5', 'dec', ?nr}?kIR )
  }
  
  role R
  {
    Recv_1( ?I )
    Send_2( {'1', ?I, ~nr}k(R,S) )
    Recv_5( {'3', ?kIR, ~nr, ?I}k(R,S) )
    Send_6( {'4', ~nr}?kIR )
    Recv_7( {'5', 'dec', ~nr}?kIR )
  }
  
  role S
  {
    Recv_3(?I, ?R, ?ni, {'1', ?I, ?nr}k(?R,S))
    Send_4(S, {'2', ?ni, ?R, ~kIR, {'3', ~kIR, ?nr, ?I}k(?R,S)}k(?I,S))
  }
}

subsection{* Security Properties *}

property (of AmendedNS) AmendedNS_msc_typing:
  "I@R :: Known(R_1)
   I@S :: Known(S_3)
   R@S :: Known(S_3)
   RequestR@I :: Known(I_2)
   S@I :: Known(I_4)
   TicketR@I
     :: (Known(I_4) |
         {('3', (kIR@S, ((Known(I_4) | nr@R), Agent)))}k(Agent, Agent))
   kIR@I :: (Known(I_4) | kIR@S)
   kIR@R :: (Known(R_5) | kIR@S)
   ni@S :: Known(S_3)
   nr@I :: (Known(I_6) | nr@R)
   nr@S :: (Known(S_3) | nr@R)"
proof
  case I_4_S
  tautology
next
  case I_4_TicketR
  sources( {'2', ~ni#0, R#0, ?kIR#0, ?TicketR#0}k(I#0,?S#0) )
    case (S_4_enc #1)
    sources( {'1', I#0, ?nr#1}k(R#0,S#1) )
    qed (2 trivial)
  qed (1 trivial)
next
  case I_4_kIR
  sources( {'2', ~ni#0, R#0, ?kIR#0, ?TicketR#0}k(I#0,?S#0) )
  qed (2 trivial)
next
  case I_6_nr
  sources( {'4', ?nr#0}?kIR#0 )
  qed (2 trivial)
next
  case R_5_kIR
  sources( {'3', ?kIR#0, ~nr#0, ?I#0}k(R#0,S#0) )
  qed (3 trivial)
next
  case S_3_I
  tautology
next
  case S_3_R
  tautology
next
  case S_3_ni
  tautology
next
  case S_3_nr
  sources( {'1', ?I#0, ?nr#0}k(?R#0,S#0) )
  qed (2 trivial)
qed

property (of AmendedNS) S_kir_sec:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?I#0, ?R#0 )"
    "knows(~kIR#0)"
  imply "False"
resolve 'AmendedNS_msc_typing
sources( ~kIR#0 )
  case (I_5_TicketR_kIR #1 a0 a1 a2 a3)
  sources(
      {'2', ~ni#1, R#1, ?kIR#1, {'3', ~kIR#0, a0, a1}k(a2,a3)}k(I#1,?S#1) )
    case (S_4_enc #2)
    contradicts secrecy of k(R#1,S#0)
  qed (1 trivial)
next
  case S_4_kIR
  contradicts secrecy of k(?I#0,S#0)
next
  case S_4_kIR_1
  contradicts secrecy of k(?I#0,S#0)
qed

property (of AmendedNS) I_kir_sec:
  for all #0 the premises
    "role( #0 ) = I"
    "uncompromised( I#0, R#0, ?S#0 )"
    "step(#0, I_4)"
    "knows(?kIR#0)"
  imply "False"
saturate
resolve 'AmendedNS_msc_typing
sources( {'2', ~ni#0, R#0, ?kIR#0, ?TicketR#0}k(I#0,?S#0) )
  case fake
  contradicts secrecy of k(I#0,?S#0)
next
  case (S_4_enc #1)
  contradictory due to 'S_kir_sec'
qed

property (of AmendedNS) R_kir_sec:
  for all #0 the premises
    "role( #0 ) = R"
    "uncompromised( R#0, S#0, ?I#0 )"
    "step(#0, R_5)"
    "knows(?kIR#0)"
  imply "False"
saturate
resolve 'AmendedNS_msc_typing
sources( {'3', ?kIR#0, ~nr#0, ?I#0}k(R#0,S#0) )
  case fake
  contradicts secrecy of k(R#0,S#0)
next
  case (I_5_TicketR_enc #1 #2 a0 a1 a2 a3)
  sources(
      {'2', ~ni#1, R#1, ?kIR#1, {'3', ~kIR#2, ~nr#0, a1}k(R#0,S#0)}
      k(I#1,?S#1) )
    case (S_4_enc #3)
    contradictory due to 'S_kir_sec'
  qed (1 trivial)
next
  case (S_4_enc_1 #1)
  contradicts secrecy of k(?I#0,S#0)
qed

property (of AmendedNS) I_ni_agree:
  for all #1 the premises
    "role( #1 ) = I"
    "uncompromised( I#1, R#1, ?S#1 )"
    "step(#1, I_6)"
  imply
    "(? #2.
        (? #3.
           role( #2 ) = R &
           role( #3 ) = S &
           I#1 = ?I#2 &
           ?I#2 = ?I#3 &
           R#1 = R#2 &
           R#2 = ?R#3 &
           ?S#1 = S#2 &
           S#2 = S#3 &
           ~ni#1 = ?ni#3 &
           ?nr#1 = ~nr#2 & ~nr#2 = ?nr#3 & ?kIR#1 = ?kIR#2 & ?kIR#2 = ~kIR#3))"
saturate
resolve 'AmendedNS_msc_typing
sources( {'2', ~ni#1, R#1, ?kIR#1, ?TicketR#1}k(I#1,?S#1) )
  case fake
  contradicts secrecy of k(I#1,?S#1)
next
  case (S_4_enc #2)
  sources( {'4', ?nr#1}~kIR#2 )
    case fake
    contradictory due to 'S_kir_sec'
  next
    case (R_6_enc #3)
    sources( {'3', ~kIR#2, ~nr#3, ?I#3}k(R#3,S#3) )
      case fake
      contradictory due to 'S_kir_sec'
    next
      case (I_5_TicketR_enc #4 #5 a0 a1 a2 a3)
      sources(
          {'2', ~ni#4, R#4, ?kIR#4, {'3', ~kIR#2, ~nr#3, a1}k(R#3,S#3)}
          k(I#4,?S#4) )
        case (S_4_enc #5)
        tautology
      qed (1 trivial)
    next
      case (S_4_enc_1 #4)
      tautology
    qed
  qed
qed

property (of AmendedNS) R_ni_agree:
  for all #2 the premises
    "role( #2 ) = R"
    "uncompromised( R#2, S#2, ?I#2 )"
    "step(#2, R_7)"
  imply
    "(? #1.
        (? #3.
           role( #1 ) = I &
           role( #3 ) = S &
           I#1 = ?I#2 &
           ?I#2 = ?I#3 &
           R#1 = R#2 &
           R#2 = ?R#3 &
           ?S#1 = S#2 &
           S#2 = S#3 &
           ~ni#1 = ?ni#3 &
           ?nr#1 = ~nr#2 & ~nr#2 = ?nr#3 & ?kIR#1 = ?kIR#2 & ?kIR#2 = ~kIR#3))"
saturate
resolve 'AmendedNS_msc_typing
sources( {'3', ?kIR#2, ~nr#2, ?I#2}k(R#2,S#2) )
  case fake
  contradicts secrecy of k(R#2,S#2)
next
  case (I_5_TicketR_enc #3 #4 a0 a1 a2 a3)
  sources(
      {'2', ~ni#3, R#3, ?kIR#3, {'3', ~kIR#4, ~nr#2, a1}k(R#2,S#2)}
      k(I#3,?S#3) )
    case (S_4_enc #5)
    sources( {'5', 'dec', ~nr#2}~kIR#4 )
      case fake
      contradictory due to 'S_kir_sec'
    next
      case (I_7_enc #5)
      sources( {'2', ~ni#5, R#5, ~kIR#4, ?TicketR#5}k(I#5,?S#5) )
        case fake
        contradictory due to 'S_kir_sec'
      next
        case (S_4_enc #6)
        tautology
      qed
    qed
  qed (1 trivial)
next
  case (S_4_enc_1 #3)
  contradicts secrecy of k(?I#2,S#2)
qed

end