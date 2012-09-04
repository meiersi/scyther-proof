theory Paulson_strengthened_Yahalom_cert_auto begin

section{* Yahalom strengthened by Paulson *}

text{*
  Modeled after the model in the SPORE library.

  Notable differences:

    1. Instead of implicit typing, we are using explicit global constants to
       discern messages.

    2. The third message includes the identity of S in plaintext, as it is
       required by role A to lookup the corresponding shared key.

    3. We model longterm shared keys such that k[A,B] = k[B,A]. This extension
       is described in "Provably Repairing the ISO/IEC 9798 Standard for Entity
       Authentication" by Basin, Cremers, and Meier
       (http://people.inf.ethz.ch/cremersc/downloads/download.php?file=papers/BCM2011-iso9798.pdf)

*}

protocol Yahalom
{ role A
  { Send_1(A, ~Na)
    Recv_3(?S, ?Nb, {'3_1', ?B, ?Kab, ~Na}k[A,?S], ?TicketB)
    Send_4(?TicketB, {'4', ?Nb}?Kab)
  }
  
  role B
  { Recv_1(?A, ?Na)
    Send_2(B, ~Nb, {'2', ?A, ?Na}k[B,S])
    Recv_4({'3_2', ?A, B, ?Kab, ~Nb}k[B,S], {'4', ~Nb}?Kab)
  }
  
  role S
  { Recv_2(?B, ?Nb, {'2', ?A, ?Na}k[?B,S])
    Send_3(S, ?Nb, {'3_1', ?B, ~Kab, ?Na}k[?A,S], 
           {'3_2', ?A, ?B, ~Kab, ?Nb}k[?B,S])
  }
}

property (of Yahalom) Yahalom_msc_typing:
  "A@B :: Known(B_1)
   A@S :: (Known(S_2) | Agent)
   B@A :: (Known(A_3) | Agent)
   B@S :: Known(S_2)
   Kab@A :: (Known(A_3) | Kab@S)
   Kab@B :: (Known(B_4) | Kab@S)
   Na@B :: Known(B_1)
   Na@S :: (Known(S_2) | Na@A)
   Nb@A :: Known(A_3)
   Nb@S :: Known(S_2)
   S@A :: Known(A_3)
   TicketB@A :: Known(A_3)"
proof
  case A_3_B
  sources( {'3_1', ?B#0, ?Kab#0, ~Na#0}k[A#0,?S#0] )
  qed (2 trivial)
next
  case A_3_Kab
  sources( {'3_1', ?B#0, ?Kab#0, ~Na#0}k[A#0,?S#0] )
  qed (2 trivial)
next
  case A_3_Nb
  tautology
next
  case A_3_S
  tautology
next
  case A_3_TicketB
  tautology
next
  case B_1_A
  tautology
next
  case B_1_Na
  tautology
next
  case B_4_Kab
  sources( {'3_2', ?A#0, B#0, ?Kab#0, ~Nb#0}k[B#0,S#0] )
  qed (2 trivial)
next
  case S_2_A
  sources( {'2', ?A#0, ?Na#0}k[S#0,?B#0] )
  qed (2 trivial)
next
  case S_2_B
  tautology
next
  case S_2_Na
  sources( {'2', ?A#0, ?Na#0}k[S#0,?B#0] )
  qed (2 trivial)
next
  case S_2_Nb
  tautology
qed

subsection{* Secrecy Properties *}

property (of Yahalom) S_Kab_secret:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?A#0, ?B#0 )"
    "knows(~Kab#0)"
  imply "False"
resolve 'Yahalom_msc_typing
sources( ~Kab#0 )
  case S_3_Kab
  contradicts secrecy of k[S#0,?A#0]
next
  case S_3_Kab_1
  contradicts secrecy of k[S#0,?B#0]
qed

property (of Yahalom) A_Kab_secret:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, ?B#0, ?S#0 )"
    "step(#0, A_3)"
    "knows(?Kab#0)"
  imply "False"
saturate
resolve 'Yahalom_msc_typing
sources( {'3_1', ?B#0, ?Kab#0, ~Na#0}k[A#0,?S#0] )
  case fake
  contradicts secrecy of k[A#0,?S#0]
next
  case (S_3_enc #1)
  split( k[S#1,?A#1] = k[A#0,?S#0] )
    case noswap
    contradictory due to 'S_Kab_secret'
  next
    case swapped
    contradictory due to 'S_Kab_secret'
  qed
qed

property (of Yahalom) B_Kab_secret:
  for all #0 the premises
    "role( #0 ) = B"
    "uncompromised( B#0, S#0, ?A#0 )"
    "step(#0, B_4)"
    "knows(?Kab#0)"
  imply "False"
saturate
resolve 'Yahalom_msc_typing
sources( {'3_2', ?A#0, B#0, ?Kab#0, ~Nb#0}k[B#0,S#0] )
  case fake
  contradicts secrecy of k[B#0,S#0]
next
  case (S_3_enc_1 #1)
  contradictory due to 'S_Kab_secret'
qed

subsection{* Authentication Properties *}

text{* This is what Paulson proves. *}

property (of Yahalom) B_auth:
  for all #2 the premises
    "role( #2 ) = B"
    "uncompromised( B#2, S#2, ?A#2 )"
    "step(#2, B_4)"
  imply "(? #1. role( #1 ) = A & ?B#1 = B#2 & ?Kab#1 = ?Kab#2)"
saturate
resolve 'Yahalom_msc_typing
sources( {'3_2', ?A#2, B#2, ?Kab#2, ~Nb#2}k[B#2,S#2] )
  case fake
  contradicts secrecy of k[B#2,S#2]
next
  case (S_3_enc_1 #3)
  sources( {'4', ~Nb#2}~Kab#3 )
    case fake
    contradictory due to 'S_Kab_secret'
  next
    case (A_4_enc #4)
    sources( {'3_1', ?B#4, ~Kab#3, ~Na#4}k[A#4,?S#4] )
      case fake
      contradictory due to 'S_Kab_secret'
    next
      case (S_3_enc #5)
      tautology
    qed
  qed
qed

subsection{* Stonger Authentication Properties *}

text{*
We can prove stronger authentication properties. However, they hold only under
the additional assumption that agents running the trusted third party do not
participate in the A or B role of the protocol. This is a reasonable assumption.

Without this assumption, the problem is that due to the swapping of identities
on the keys, the authentication properties below can be attacked. Note that the
proofs list exactly the reasoning steps where the axioms are exploited.
*}

axiom (of Yahalom) different_actors_A_S:
  for all #0 #1 the premises
    "role( #0 ) = A"
    "role( #1 ) = S"
    "S#1 = A#0"
  imply "False"

axiom (of Yahalom) different_actors_B_S:
  for all #0 #1 the premises
    "role( #0 ) = B"
    "role( #1 ) = S"
    "S#1 = B#0"
  imply "False"

property (of Yahalom) A_strong_auth:
  for all #1 the premises
    "role( #1 ) = A"
    "uncompromised( A#1, ?B#1, ?S#1 )"
    "step(#1, A_3)"
  imply
    "(? #2.
        (? #3.
           role( #2 ) = B &
           role( #3 ) = S &
           A#1 = ?A#2 &
           ?A#2 = ?A#3 &
           ?B#1 = B#2 &
           B#2 = ?B#3 &
           ?S#1 = S#2 &
           S#2 = S#3 &
           ~Na#1 = ?Na#2 &
           ?Na#2 = ?Na#3 &
           ?Kab#1 = ~Kab#3 &
           St(#1, A_1) < St(#2, B_1) &
           St(#2, B_1) < St(#2, B_2) &
           St(#2, B_2) < St(#3, S_2) &
           St(#3, S_2) < St(#3, S_3) & St(#3, S_3) < St(#1, A_3)))"
saturate
resolve 'Yahalom_msc_typing
sources( {'3_1', ?B#1, ?Kab#1, ~Na#1}k[A#1,?S#1] )
  case fake
  contradicts secrecy of k[A#1,?S#1]
next
  case (S_3_enc #2)
  split( k[S#2,?A#2] = k[A#1,?S#1] )
    case noswap
    contradictory due to 'different_actors_A_S'
  next
    case swapped
    sources( {'2', A#1, ~Na#1}k[S#2,?B#1] )
      case fake
      contradicts secrecy of k[S#2,?B#1]
    next
      case (B_2_enc #3)
      split( k[S#2,?B#1] = k[B#3,S#3] )
        case noswap
        contradictory due to 'different_actors_B_S'
      next
        case swapped
        sources( ~Na#1 )
          case A_1_Na
          tautology
        next
          case (S_3_Na #4)
          sources( {'2', ?A#4, ~Na#1}k[S#4,?B#4] )
          qed (2 trivial)
        qed
      qed
    qed
  qed
qed

property (of Yahalom) B_strong_auth:
  for all #2 the premises
    "role( #2 ) = B"
    "uncompromised( B#2, S#2, ?A#2 )"
    "step(#2, B_4)"
  imply
    "(? #1.
        (? #3.
           role( #1 ) = A &
           role( #3 ) = S &
           A#1 = ?A#2 &
           ?A#2 = ?A#3 &
           ?B#1 = B#2 &
           B#2 = ?B#3 &
           ?S#1 = S#2 &
           S#2 = S#3 &
           ?Nb#1 = ~Nb#2 &
           ~Nb#2 = ?Nb#3 &
           ?Kab#1 = ?Kab#2 &
           ?Kab#2 = ~Kab#3 &
           St(#2, B_1) < St(#2, B_2) &
           St(#2, B_2) < St(#3, S_2) &
           St(#3, S_2) < St(#3, S_3) &
           St(#3, S_3) < St(#1, A_3) &
           St(#1, A_3) < St(#1, A_4) & St(#1, A_4) < St(#2, B_4)))"
saturate
resolve 'Yahalom_msc_typing
sources( {'3_2', ?A#2, B#2, ?Kab#2, ~Nb#2}k[B#2,S#2] )
  case fake
  contradicts secrecy of k[B#2,S#2]
next
  case (S_3_enc_1 #3)
  sources( ~Nb#2 )
    case B_2_Nb
    sources( {'4', ~Nb#2}~Kab#3 )
      case fake
      contradictory due to 'S_Kab_secret'
    next
      case (A_4_enc #4)
      sources( {'3_1', ?B#4, ~Kab#3, ~Na#4}k[A#4,?S#4] )
        case fake
        contradictory due to 'S_Kab_secret'
      next
        case (S_3_enc #5)
        split( k[S#2,?A#2] = k[A#4,?S#4] )
          case noswap
          contradictory due to 'different_actors_A_S'
        next
          case swapped
          tautology
        qed
      qed
    qed
  qed
qed

end