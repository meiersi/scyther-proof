theory Kerberos_V4_cert_auto begin

section{* The Kerberos Protocol, Version 4 *}

text{*
  Modeled after the description given by Bella [1] based on the original
  technical report [2].

  Notable differences:

    1. We do not model the timestamps and the timing properties because our
       model does not support reasoning about them yet. We model them as
       freshly generated nonces that are leaked immediately after generation.

    2. We do not model session key leakage, as our support for key compromise
       properties is not ready yet.

    3. We provide more general authentication and secrecy properties, as we do
       not assume a priory the uncompromisedness of the ticket granting server.
       Furthermore, the authentication propertis are more fine-grained due to
       our more precise execution model.

    4. We use explicit global constants instead of implicit typing to identify
       the different encryptions.

    5. We use the abbreviations: C for Client, A for authenticator, G for
       ticket granting server, S for server.


[1] Bella, Giampaolo and Paulson, Lawrence C., "Kerberos Version 4: Inductive
    Analysis of the Secrecy Goals", in ESORICS, 1998, pp. 361-375.

[2] Miller, S. P. and Neuman, B. C. and Schiller, J. I. and Saltzer, J. H.,
    "Kerberos Authentication and Authorization System", in Project Athena Technical
    Plan, 1987, pp. 1-36.
*}

protocol Kerberos
{
  role A
  {
    Recv_1(?C, ?G, ?Tc1)
    Send_2_leak( ~Ta )
    Send_2(A, 
           {'21', ~AuthKey, ?G, ~Ta, {'22', ?C, ?G, ~AuthKey, ~Ta}k(A,?G)}k(?C,A))
  }
  
  role C
  {
    Send_1_leak( ~Tc1 )
    Send_1(C, G, ~Tc1)
    Recv_2(?A, {'21', ?AuthKey, G, ?Ta, ?AuthTicket}k(C,?A))
    Send_3_leak( ~Tc2 )
    Send_3(?A, ?AuthTicket, {'3', C, ~Tc2}?AuthKey, S)
    Recv_4( {'41', ?ServKey, S, ?Tg, ?ServTicket}?AuthKey )
    Send_5_leak( ~Tc3 )
    Send_5(G, ?ServTicket, {'5', C, ~Tc3}?ServKey)
    Recv_6( {'6', ~Tc3}?ServKey )
  }
  
  role G
  {
    Recv_3(?A, {'22', ?C, G, ?AuthKey, ?Ta}k(?A,G), {'3', ?C, ?Tc2}?AuthKey, 
           ?S)
    Send_4_leak( ~Tg )
    Send_4( {'41', ~ServKey, ?S, ~Tg, {'42', ?C, ?S, ~ServKey, ~Tg}k(G,?S)}
            ?AuthKey
          )
  }
  
  role S
  {
    Recv_5(?G, {'42', ?C, S, ?ServKey, ?Tg}k(?G,S), {'5', ?C, ?Tc3}?ServKey)
    Send_6( {'6', ?Tc3}?ServKey )
  }
}

property (of Kerberos) Kerberos_typing:
  "A@C :: Known(C_2)
   A@G :: Known(G_3)
   AuthKey@C :: (Known(C_2) | AuthKey@A)
   AuthKey@G :: (Known(G_3) | AuthKey@A)
   AuthTicket@C
     :: (Known(C_2) |
         {('22', (Known(C_2), (Agent, (AuthKey@A, Ta@A))))}k(Agent, Agent))
   C@A :: Known(A_1)
   C@G :: (Known(G_3) | Agent)
   C@S :: (Known(S_5) | Agent)
   G@A :: Known(A_1)
   G@S :: Known(S_5)
   S@G :: Known(G_3)
   ServKey@C :: (Known(C_4) | ServKey@G)
   ServKey@S :: (Known(S_5) | ServKey@G)
   ServTicket@C
     :: (Known(C_4) |
         {('42', (Known(C_4), (Agent, (ServKey@G, Tg@G))))}k(Agent, Agent))
   Ta@C :: (Known(C_2) | Ta@A)
   Ta@G :: (Known(G_3) | Ta@A)
   Tc1@A :: Known(A_1)
   Tc2@G :: (Known(G_3) | Tc2@C)
   Tc3@S :: (Known(S_5) | Tc3@C)
   Tg@C :: (Known(C_4) | Tg@G)
   Tg@S :: (Known(S_5) | Tg@G)"
proof
  case A_1_C
  tautology
next
  case A_1_G
  tautology
next
  case A_1_Tc1
  tautology
next
  case C_2_A
  tautology
next
  case C_2_AuthKey
  sources( {'21', ?AuthKey#0, G#0, ?Ta#0, ?AuthTicket#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_2_AuthTicket
  sources( {'21', ?AuthKey#0, G#0, ?Ta#0, ?AuthTicket#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_2_Ta
  sources( {'21', ?AuthKey#0, G#0, ?Ta#0, ?AuthTicket#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_4_ServKey
  sources( {'41', ?ServKey#0, S#0, ?Tg#0, ?ServTicket#0}?AuthKey#0 )
  qed (2 trivial)
next
  case C_4_ServTicket
  sources( {'41', ?ServKey#0, S#0, ?Tg#0, ?ServTicket#0}?AuthKey#0 )
    case (G_4_enc #1)
    sources( {'3', ?C#1, ?Tc2#1}?AuthKey#0 )
    qed (2 trivial)
  qed (1 trivial)
next
  case C_4_Tg
  sources( {'41', ?ServKey#0, S#0, ?Tg#0, ?ServTicket#0}?AuthKey#0 )
  qed (2 trivial)
next
  case G_3_A
  tautology
next
  case G_3_AuthKey
  sources( {'22', ?C#0, G#0, ?AuthKey#0, ?Ta#0}k(?A#0,G#0) )
  qed (3 trivial)
next
  case G_3_C
  sources( {'3', ?C#0, ?Tc2#0}?AuthKey#0 )
  qed (2 trivial)
next
  case G_3_S
  tautology
next
  case G_3_Ta
  sources( {'22', ?C#0, G#0, ?AuthKey#0, ?Ta#0}k(?A#0,G#0) )
  qed (3 trivial)
next
  case G_3_Tc2
  sources( {'3', ?C#0, ?Tc2#0}?AuthKey#0 )
  qed (2 trivial)
next
  case S_5_C
  sources( {'5', ?C#0, ?Tc3#0}?ServKey#0 )
  qed (2 trivial)
next
  case S_5_G
  tautology
next
  case S_5_ServKey
  sources( {'42', ?C#0, S#0, ?ServKey#0, ?Tg#0}k(?G#0,S#0) )
  qed (3 trivial)
next
  case S_5_Tc3
  sources( {'5', ?C#0, ?Tc3#0}?ServKey#0 )
  qed (2 trivial)
next
  case S_5_Tg
  sources( {'42', ?C#0, S#0, ?ServKey#0, ?Tg#0}k(?G#0,S#0) )
  qed (3 trivial)
qed

subsection{* Secrecy Properties *}

property (of Kerberos) A_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, ?C#0, ?G#0 )"
    "knows(~AuthKey#0)"
  imply "False"
resolve 'Kerberos_typing
sources( ~AuthKey#0 )
  case A_2_AuthKey
  contradicts secrecy of k(?C#0,A#0)
next
  case A_2_AuthKey_1
  contradicts secrecy of k(A#0,?G#0)
next
  case (C_3_AuthTicket_AuthKey #1 a0 a1 #3 a2 a3)
  sources(
      {'21', ?AuthKey#1, G#1, ?Ta#1, {'22', a0, a1, ~AuthKey#0, ~Ta#3}k(a2,a3)}
      k(C#1,?A#1) )
    case (A_2_enc #4)
    contradicts secrecy of k(A#0,G#1)
  qed (1 trivial)
qed

property (of Kerberos) C_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( C#0, G#0, ?A#0 )"
    "step(#0, C_2)"
    "knows(?AuthKey#0)"
  imply "False"
saturate
resolve 'Kerberos_typing
sources( {'21', ?AuthKey#0, G#0, ?Ta#0, ?AuthTicket#0}k(C#0,?A#0) )
  case fake
  contradicts secrecy of k(C#0,?A#0)
next
  case (A_2_enc #1)
  contradictory due to 'A_AuthKey_secret'
qed

property (of Kerberos) G_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = G"
    "uncompromised( G#0, ?A#0, ?C#0 )"
    "step(#0, G_3)"
    "knows(?AuthKey#0)"
  imply "False"
saturate
resolve 'Kerberos_typing
sources( {'22', ?C#0, G#0, ?AuthKey#0, ?Ta#0}k(?A#0,G#0) )
  case fake
  contradicts secrecy of k(?A#0,G#0)
next
  case (A_2_enc_1 #1)
  contradicts secrecy of k(?C#0,A#1)
next
  case (C_3_AuthTicket_enc #1 a0 a1 #2 #3 a2 a3)
  sources(
      {'21', ?AuthKey#1, G#1, ?Ta#1, 
       {'22', a0, G#0, ~AuthKey#2, ~Ta#3}k(a2,G#0)}
      k(C#1,?A#1) )
    case (A_2_enc #4)
    contradictory due to 'A_AuthKey_secret'
  qed (1 trivial)
qed

property (of Kerberos) G_ServKey_sec:
  for all #0 the premises
    "role( #0 ) = G"
    "uncompromised( G#0, ?A#0, ?C#0, ?S#0 )"
    "knows(~ServKey#0)"
  imply "False"
resolve 'Kerberos_typing
sources( ~ServKey#0 )
  case (C_5_ServTicket_ServKey #1 a0 a1 #3 a2 a3)
  sources(
      {'41', ?ServKey#1, S#1, ?Tg#1, {'42', a0, a1, ~ServKey#0, ~Tg#3}k(a2,a3)}
      ?AuthKey#1 )
    case (G_4_enc #4)
    contradicts secrecy of k(G#0,S#1)
  qed (1 trivial)
next
  case G_4_ServKey
  sources( {'22', ?C#0, G#0, ?AuthKey#0, ?Ta#0}k(?A#0,G#0) )
    case fake
    contradicts secrecy of k(?A#0,G#0)
  next
    case (A_2_enc_1 #1)
    contradicts secrecy of k(?C#0,A#1)
  next
    case (C_3_AuthTicket_enc #1 a0 a1 #2 #3 a2 a3)
    contradictory due to 'G_AuthKey_secret'
  qed
next
  case G_4_ServKey_1
  contradicts secrecy of k(G#0,?S#0)
qed

property (of Kerberos) C_ServKey_sec:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( C#0, G#0, S#0, ?A#0 )"
    "step(#0, C_4)"
    "knows(?ServKey#0)"
  imply "False"
saturate
resolve 'Kerberos_typing
sources( {'21', ?AuthKey#0, G#0, ?Ta#0, ?AuthTicket#0}k(C#0,?A#0) )
  case fake
  contradicts secrecy of k(C#0,?A#0)
next
  case (A_2_enc #1)
  sources( {'41', ?ServKey#0, S#0, ?Tg#0, ?ServTicket#0}~AuthKey#1 )
    case fake
    contradictory due to 'A_AuthKey_secret'
  next
    case (G_4_enc #2)
    sources( {'22', ?C#2, G#2, ~AuthKey#1, ?Ta#2}k(?A#2,G#2) )
      case fake
      contradictory due to 'A_AuthKey_secret'
    next
      case (A_2_enc_1 #3)
      contradicts secrecy of k(C#0,A#1)
    next
      case (C_3_AuthTicket_enc #3 a0 a1 #4 #5 a2 a3)
      sources(
          {'21', ?AuthKey#3, G#3, ?Ta#3, 
           {'22', a0, G#2, ~AuthKey#1, ~Ta#5}k(a2,G#2)}
          k(C#3,?A#3) )
        case (A_2_enc #6)
        contradictory due to 'G_ServKey_sec'
      qed (1 trivial)
    qed
  qed
qed

subsection{* Authentication Properties *}

property (of Kerberos) C_auth:
  for all #1 the premises
    "role( #1 ) = C"
    "uncompromised( C#1, G#1, S#1, ?A#1 )"
    "step(#1, C_6)"
  imply
    "(? #2.
        (? #3.
           (? #4.
              role( #2 ) = A &
              role( #3 ) = G &
              role( #4 ) = S &
              ?A#1 = A#2 &
              C#1 = ?C#2 &
              G#1 = ?G#2 &
              ?Ta#1 = ~Ta#2 &
              ?AuthKey#1 = ~AuthKey#2 &
              ?A#1 = ?A#3 &
              C#1 = ?C#3 &
              G#1 = G#3 &
              S#1 = ?S#3 &
              ?Tg#1 = ~Tg#3 &
              ?AuthKey#1 = ?AuthKey#3 &
              ?ServKey#1 = ~ServKey#3 &
              C#1 = ?C#4 &
              G#1 = ?G#4 & S#1 = S#4 & ~Tc3#1 = ?Tc3#4 & ?ServKey#1 = ?ServKey#4)))"
saturate
resolve 'Kerberos_typing
sources( {'21', ?AuthKey#1, G#1, ?Ta#1, ?AuthTicket#1}k(C#1,?A#1) )
  case fake
  contradicts secrecy of k(C#1,?A#1)
next
  case (A_2_enc #2)
  sources( {'6', ~Tc3#1}?ServKey#1 )
    case fake
    contradictory due to 'C_ServKey_sec'
  next
    case (S_6_enc #3)
    sources( {'41', ?ServKey#1, S#1, ?Tg#1, ?ServTicket#1}~AuthKey#2 )
      case fake
      contradictory due to 'A_AuthKey_secret'
    next
      case (G_4_enc #4)
      sources( {'22', ?C#4, G#4, ~AuthKey#2, ?Ta#4}k(?A#4,G#4) )
        case fake
        contradictory due to 'A_AuthKey_secret'
      next
        case (A_2_enc_1 #5)
        contradicts secrecy of k(C#1,A#2)
      next
        case (C_3_AuthTicket_enc #5 a0 a1 #6 #7 a2 a3)
        sources( {'42', ?C#3, S#3, ~ServKey#4, ?Tg#3}k(?G#3,S#3) )
          case fake
          contradictory due to 'C_ServKey_sec'
        next
          case (C_5_ServTicket_enc #8 a3 a4 #9 #10 a5 a6)
          sources(
              {'21', ?AuthKey#5, G#5, ?Ta#5, 
               {'22', a0, G#4, ~AuthKey#2, ~Ta#7}k(a2,G#4)}
              k(C#5,?A#5) )
            case (A_2_enc #11)
            sources(
                {'41', ?ServKey#8, S#8, ?Tg#8, 
                 {'42', a3, S#3, ~ServKey#4, ~Tg#10}k(a5,S#3)}
                ?AuthKey#8 )
              case (G_4_enc #11)
              tautology
            qed (1 trivial)
          qed (1 trivial)
        next
          case (G_4_enc_1 #8)
          contradictory due to 'A_AuthKey_secret'
        qed
      qed
    qed
  qed
qed

property (of Kerberos) G_auth:
  for all #3 the premises
    "role( #3 ) = G"
    "uncompromised( G#3, ?A#3, ?C#3 )"
    "step(#3, G_3)"
  imply
    "(? #1.
        (? #2.
           role( #1 ) = C &
           role( #2 ) = A &
           ?A#1 = ?A#3 &
           C#1 = ?C#3 &
           G#1 = G#3 &
           ~Tc2#1 = ?Tc2#3 &
           ?AuthKey#1 = ?AuthKey#3 &
           ?A#1 = A#2 & C#1 = ?C#2 & G#1 = ?G#2 & ?AuthKey#1 = ~AuthKey#2))"
saturate
resolve 'Kerberos_typing
sources( {'22', ?C#3, G#3, ?AuthKey#3, ?Ta#3}k(?A#3,G#3) )
  case fake
  contradicts secrecy of k(?A#3,G#3)
next
  case (A_2_enc_1 #4)
  contradicts secrecy of k(?C#3,A#4)
next
  case (C_3_AuthTicket_enc #4 a0 a1 #5 #6 a2 a3)
  sources( {'3', a0, ?Tc2#3}~AuthKey#5 )
    case fake
    contradictory due to 'G_AuthKey_secret'
  next
    case (C_3_enc #7)
    sources(
        {'21', ?AuthKey#4, G#4, ?Ta#4, 
         {'22', C#7, G#3, ~AuthKey#5, ~Ta#6}k(a2,G#3)}
        k(C#4,?A#4) )
      case (A_2_enc #8)
      sources( {'21', ~AuthKey#5, G#7, ?Ta#7, ?AuthTicket#7}k(C#4,?A#7) )
        case fake
        contradictory due to 'A_AuthKey_secret'
      next
        case (A_2_enc #8)
        tautology
      qed
    qed (1 trivial)
  qed
qed

end