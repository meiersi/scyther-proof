theory Lowe_modified_Denning_Sacco_shared_key_cert_auto begin

section{* Denning-Sacco Shared Key Protocol *}

text{*
  Modeled after the description in the SPORE library:

    http://www.lsv.ens-cachan.fr/Software/spore/denningSacco.html

  Notable differences:

    1. We do not support reasoning about timestamps yet. Therefore, we use a
       single global constant 'Time' instead of timestamps; i.e., we assume
       that everything happens at the same timepoint.

    2. We are using explicit global constants instead of implicit typing to
       discern the different encryptions.

    3. We model 'dec(x)' as an invertible function using tupling with a fixed
       global constant; i.e., we only exploit its tagging properties.

*}

protocol DenningSacco
{ role A
  { Send_1(A, B)
    Recv_2(?S, {'2', B, ?Kab, 'Time', ?Ticket}k(A,?S))
    Send_3(?S, ?Ticket)
    Recv_4( {'4', ?Nb}?Kab )
    Send_5( {'5', 'dec', ?Nb}?Kab )
  }
  
  role B
  { Recv_3(?S, {'3', ?Kab, ?A, 'Time'}k(B,?S))
    Send_4( {'4', ~Nb}?Kab )
    Recv_5( {'5', 'dec', ~Nb}?Kab )
  }
  
  role S
  { Recv_1(?A, ?B)
    Send_2(S, {'2', ?B, ~Kab, 'Time', {'3', ~Kab, ?A, 'Time'}k(?B,S)}k(?A,S))
  }
}

property (of DenningSacco) DenningSacco_msc_typing:
  "A@B :: (Known(B_3) | Agent)
   A@S :: Known(S_1)
   B@S :: Known(S_1)
   Kab@A :: (Known(A_2) | Kab@S)
   Kab@B :: (Known(B_3) | Kab@S)
   Nb@A :: (Known(A_4) | Nb@B)
   S@A :: Known(A_2)
   S@B :: Known(B_3)
   Ticket@A
     :: (Known(A_2) | {('3', (Kab@S, (Agent, 'Time')))}k(Agent, Agent))"
proof
  case A_2_Kab
  sources( {'2', B#0, ?Kab#0, 'Time', ?Ticket#0}k(A#0,?S#0) )
  qed (2 trivial)
next
  case A_2_S
  tautology
next
  case A_2_Ticket
  sources( {'2', B#0, ?Kab#0, 'Time', ?Ticket#0}k(A#0,?S#0) )
  qed (2 trivial)
next
  case A_4_Nb
  sources( {'4', ?Nb#0}?Kab#0 )
  qed (2 trivial)
next
  case B_3_A
  sources( {'3', ?Kab#0, ?A#0, 'Time'}k(B#0,?S#0) )
  qed (3 trivial)
next
  case B_3_Kab
  sources( {'3', ?Kab#0, ?A#0, 'Time'}k(B#0,?S#0) )
  qed (3 trivial)
next
  case B_3_S
  tautology
next
  case S_1_A
  tautology
next
  case S_1_B
  tautology
qed

subsection{* Security Properties *}

property (of DenningSacco) B_Kab_secrecy:
  for all #0 the premises
    "role( #0 ) = B"
    "uncompromised( B#0, ?A#0, ?S#0 )"
    "step(#0, B_3)"
    "knows(?Kab#0)"
  imply "False"
saturate
resolve 'DenningSacco_msc_typing
sources( {'3', ?Kab#0, ?A#0, 'Time'}k(B#0,?S#0) )
  case fake
  contradicts secrecy of k(B#0,?S#0)
next
  case (A_3_Ticket_enc #1 #2 a0 a1 a2)
  sources(
      {'2', B#1, ?Kab#1, 'Time', {'3', ~Kab#2, a0, 'Time'}k(B#0,a2)}
      k(A#1,?S#1) )
    case (S_2_enc #3)
    sources( ~Kab#2 )
      case (A_3_Ticket_Kab #3 a0 a1 a2)
      sources(
          {'2', B#3, ?Kab#3, 'Time', {'3', ~Kab#2, a0, 'Time'}k(a1,a2)}
          k(A#3,?S#3) )
        case (S_2_enc #4)
        contradicts secrecy of k(B#0,S#2)
      qed (1 trivial)
    next
      case S_2_Kab
      contradicts secrecy of k(A#1,S#2)
    next
      case S_2_Kab_1
      contradicts secrecy of k(A#1,S#2)
    qed
  qed (1 trivial)
next
  case (S_2_enc_1 #1)
  contradicts secrecy of k(?A#0,S#1)
qed

property (of DenningSacco) A_Kab_secrecy:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, B#0, ?S#0 )"
    "step(#0, A_2)"
    "knows(?Kab#0)"
  imply "False"
saturate
resolve 'DenningSacco_msc_typing
sources( {'2', B#0, ?Kab#0, 'Time', ?Ticket#0}k(A#0,?S#0) )
  case fake
  contradicts secrecy of k(A#0,?S#0)
next
  case (S_2_enc #1)
  sources( ~Kab#1 )
    case (A_3_Ticket_Kab #2 a0 a1 a2)
    sources(
        {'2', B#2, ?Kab#2, 'Time', {'3', ~Kab#1, a0, 'Time'}k(a1,a2)}
        k(A#2,?S#2) )
      case (S_2_enc #3)
      contradicts secrecy of k(B#0,S#1)
    qed (1 trivial)
  next
    case S_2_Kab
    contradicts secrecy of k(A#0,S#1)
  next
    case S_2_Kab_1
    contradicts secrecy of k(A#0,S#1)
  qed
qed

text{*
  Note that the following authentication properties only specify the existence
  of partner threads of a certain structure and not the uniqueness. However,
  these partner threads agree on the nonces of each other, which implies that
  we can prove injective authentication. We can do this using Isabelle/HOL
  and exploiting the automatically proven properties below.
*}

property (of DenningSacco) A_noninjective_agree:
  for all #1 the premises
    "role( #1 ) = A"
    "uncompromised( A#1, B#1, ?S#1 )"
    "step(#1, A_4)"
  imply
    "(? #2.
        (? #3.
           role( #2 ) = B &
           role( #3 ) = S &
           A#1 = ?A#2 &
           ?A#2 = ?A#3 &
           B#1 = B#2 &
           B#2 = ?B#3 &
           ?S#1 = ?S#2 &
           ?S#2 = S#3 & ?Kab#1 = ?Kab#2 & ?Kab#2 = ~Kab#3 & ?Nb#1 = ~Nb#2))"
saturate
resolve 'DenningSacco_msc_typing
sources( {'2', B#1, ?Kab#1, 'Time', ?Ticket#1}k(A#1,?S#1) )
  case fake
  contradicts secrecy of k(A#1,?S#1)
next
  case (S_2_enc #2)
  sources( {'4', ?Nb#1}~Kab#2 )
    case fake
    contradictory due to 'A_Kab_secrecy'
  next
    case (B_4_enc #3)
    sources( {'3', ~Kab#2, ?A#3, 'Time'}k(B#3,?S#3) )
      case fake
      contradictory due to 'A_Kab_secrecy'
    next
      case (A_3_Ticket_enc #4 #5 a0 a1 a2)
      sources(
          {'2', B#4, ?Kab#4, 'Time', {'3', ~Kab#2, a0, 'Time'}k(B#3,a2)}
          k(A#4,?S#4) )
        case (S_2_enc #5)
        tautology
      qed (1 trivial)
    next
      case (S_2_enc_1 #4)
      tautology
    qed
  qed
qed

property (of DenningSacco) B_noninjective_agree:
  for all #2 the premises
    "role( #2 ) = B"
    "uncompromised( B#2, ?A#2, ?S#2 )"
    "step(#2, B_5)"
  imply
    "(? #1.
        (? #3.
           role( #1 ) = A &
           role( #3 ) = S &
           A#1 = ?A#2 &
           ?A#2 = ?A#3 &
           B#1 = B#2 &
           B#2 = ?B#3 &
           ?S#1 = ?S#2 &
           ?S#2 = S#3 & ?Kab#1 = ?Kab#2 & ?Kab#2 = ~Kab#3 & ?Nb#1 = ~Nb#2))"
saturate
resolve 'DenningSacco_msc_typing
sources( {'3', ?Kab#2, ?A#2, 'Time'}k(B#2,?S#2) )
  case fake
  contradicts secrecy of k(B#2,?S#2)
next
  case (A_3_Ticket_enc #3 #4 a0 a1 a2)
  sources(
      {'2', B#3, ?Kab#3, 'Time', {'3', ~Kab#4, a0, 'Time'}k(B#2,a2)}
      k(A#3,?S#3) )
    case (S_2_enc #5)
    sources( {'5', 'dec', ~Nb#2}~Kab#4 )
      case fake
      contradictory due to 'B_Kab_secrecy'
    next
      case (A_5_enc #5)
      sources( {'2', B#5, ~Kab#4, 'Time', ?Ticket#5}k(A#5,?S#5) )
        case fake
        contradictory due to 'B_Kab_secrecy'
      next
        case (S_2_enc #6)
        tautology
      qed
    qed
  qed (1 trivial)
next
  case (S_2_enc_1 #3)
  contradicts secrecy of k(?A#2,S#3)
qed

end