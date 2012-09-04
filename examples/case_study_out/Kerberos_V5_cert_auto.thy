theory Kerberos_V5_cert_auto begin

section{* The Kerberos Protocol, Version 5 *}

text{*
Modeled after SPORE.

Notable differences.

  1. We use explicit global constants instead of implicit typing to identify
     the different encryptions.

  2. We do not model the timestamps and the timing properties because our
     model does not support reasoning about them yet. We use nonces that are
     leaked immediately after generation for timestamps and prove the
     agreement properties over them.

  3. The authentication properties in SPORE are not formulated precisely
     enough. Some directions of agreement are only satisfied under additional
     assumptions. See the notes below (in the original source). We prove now
     the strongest authentication that can be proven without additional
     assumptions. Some more work is required to check whether these are
     sufficient for the real-world applications where Kerberos is used.
  
  4. We identify client and user. Therefore, the user key Ku in the
     description in SPORE is modeled as k(A,C).

Note that we do not model the loss of authentication, server, and session
keys. The Isabelle models could handle that thanks to the work done by Martin
Schaub in his master thesis [1], but scyther-proof does not (yet).

[1] Schaub, Martin. Efficient Interactive Construction of Machine-Checked
    Protocol Security Proofs in the Context of Dynamically Compromising
    Adversaries.  Eidgenoessische Technische Hochschule Zuerich, Departement
    Informatik (2011).  doi:10.3929/ethz-a-006450686.
*}

protocol Kerberos
{ role A
  { Recv_1(?C, ?G, ?L1, ?N1)
    Send_2_leak(~T1start, ~T1expire)
    Send_2(A, ?C, {'2_1', ?C, ?G, ~AuthKey, ~T1start, ~T1expire}k(?G,A), 
           {'2_2', ?G, ~AuthKey, ~T1start, ~T1expire}k(?C,A))
  }
  
  role C
  { Send_1(C, G, ~L1, ~N1)
    Recv_2(?A, C, ?TicketGrantingTicket, 
           {'2_2', G, ?AuthKey, ?T1start, ?T1expire}k(C,?A))
    Send_3_leak( ~T1 )
    Send_3(?A, S, ~L2, ~N2, ?TicketGrantingTicket, {'3', C, ~T1}?AuthKey)
    Recv_4(C, ?ServerTicket, 
           {'4_2', S, ?ServerKey, ?T2start, ?T2expire, ~N2}?AuthKey)
    Send_5_leak( ~T2 )
    Send_5(G, ?ServerTicket, {'5', C, ~T2}?ServerKey)
    Recv_6( {'6', ~T2}?ServerKey )
  }
  
  role G
  { Recv_3(?A, ?S, ?L2, ?N2, 
           {'2_1', ?C, G, ?AuthKey, ?T1start, ?T1expire}k(G,?A), 
           {'3', ?C, ?T1}?AuthKey)
    Send_4_leak(~T2start, ~T2expire)
    Send_4(?C, {'4_1', ?C, ?S, ~ServerKey, ~T2start, ~T2expire}k(G,?S), 
           {'4_2', ?S, ~ServerKey, ~T2start, ~T2expire, ?N2}?AuthKey)
  }
  
  role S
  { Recv_5(?G, {'4_1', ?C, S, ?ServerKey, ?T2start, ?T2expire}k(?G,S), 
           {'5', ?C, ?T2}?ServerKey)
    Send_6( {'6', ?T2}?ServerKey )
  }
}

property (of Kerberos) Kerberos_msc_typing:
  "A@C :: Known(C_2)
   A@G :: Known(G_3)
   AuthKey@C :: (Known(C_2) | AuthKey@A)
   AuthKey@G :: (Known(G_3) | AuthKey@A)
   C@A :: Known(A_1)
   C@G :: (Known(G_3) | Agent)
   C@S :: (Known(S_5) | Agent)
   G@A :: Known(A_1)
   G@S :: Known(S_5)
   L1@A :: Known(A_1)
   L2@G :: Known(G_3)
   N1@A :: Known(A_1)
   N2@G :: Known(G_3)
   S@G :: Known(G_3)
   ServerKey@C :: (Known(C_4) | ServerKey@G)
   ServerKey@S :: (Known(S_5) | ServerKey@G)
   ServerTicket@C :: Known(C_4)
   T1@G :: (Known(G_3) | T1@C)
   T1expire@C :: (Known(C_2) | T1expire@A)
   T1expire@G :: (Known(G_3) | T1expire@A)
   T1start@C :: (Known(C_2) | T1start@A)
   T1start@G :: (Known(G_3) | T1start@A)
   T2@S :: (Known(S_5) | T2@C)
   T2expire@C :: (Known(C_4) | T2expire@G)
   T2expire@S :: (Known(S_5) | T2expire@G)
   T2start@C :: (Known(C_4) | T2start@G)
   T2start@S :: (Known(S_5) | T2start@G)
   TicketGrantingTicket@C :: Known(C_2)"
proof
  case A_1_C
  tautology
next
  case A_1_G
  tautology
next
  case A_1_L1
  tautology
next
  case A_1_N1
  tautology
next
  case C_2_A
  tautology
next
  case C_2_AuthKey
  sources( {'2_2', G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_2_T1expire
  sources( {'2_2', G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_2_T1start
  sources( {'2_2', G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(C#0,?A#0) )
  qed (2 trivial)
next
  case C_2_TicketGrantingTicket
  tautology
next
  case C_4_ServerKey
  sources(
      {'4_2', S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0, ~N2#0}?AuthKey#0 )
  qed (2 trivial)
next
  case C_4_ServerTicket
  tautology
next
  case C_4_T2expire
  sources(
      {'4_2', S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0, ~N2#0}?AuthKey#0 )
  qed (2 trivial)
next
  case C_4_T2start
  sources(
      {'4_2', S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0, ~N2#0}?AuthKey#0 )
  qed (2 trivial)
next
  case G_3_A
  tautology
next
  case G_3_AuthKey
  sources(
      {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
  qed (2 trivial)
next
  case G_3_C
  sources(
      {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
  qed (2 trivial)
next
  case G_3_L2
  tautology
next
  case G_3_N2
  tautology
next
  case G_3_S
  tautology
next
  case G_3_T1
  sources( {'3', ?C#0, ?T1#0}?AuthKey#0 )
  qed (2 trivial)
next
  case G_3_T1expire
  sources(
      {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
  qed (2 trivial)
next
  case G_3_T1start
  sources(
      {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
  qed (2 trivial)
next
  case S_5_C
  sources( {'5', ?C#0, ?T2#0}?ServerKey#0 )
  qed (2 trivial)
next
  case S_5_G
  tautology
next
  case S_5_ServerKey
  sources(
      {'4_1', ?C#0, S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0}k(?G#0,S#0) )
  qed (2 trivial)
next
  case S_5_T2
  sources( {'5', ?C#0, ?T2#0}?ServerKey#0 )
  qed (2 trivial)
next
  case S_5_T2expire
  sources(
      {'4_1', ?C#0, S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0}k(?G#0,S#0) )
  qed (2 trivial)
next
  case S_5_T2start
  sources(
      {'4_1', ?C#0, S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0}k(?G#0,S#0) )
  qed (2 trivial)
qed

subsection{* Secrecy Properties *}

property (of Kerberos) A_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, ?C#0, ?G#0 )"
    "knows(~AuthKey#0)"
  imply "False"
resolve 'Kerberos_msc_typing
sources( ~AuthKey#0 )
  case A_2_AuthKey
  contradicts secrecy of k(?G#0,A#0)
next
  case A_2_AuthKey_1
  contradicts secrecy of k(?C#0,A#0)
qed

property (of Kerberos) C_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( C#0, G#0, ?A#0 )"
    "step(#0, C_2)"
    "knows(?AuthKey#0)"
  imply "False"
saturate
resolve 'Kerberos_msc_typing
sources( {'2_2', G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(C#0,?A#0) )
  case fake
  contradicts secrecy of k(C#0,?A#0)
next
  case (A_2_enc_1 #1)
  contradictory due to 'A_AuthKey_secret'
qed

property (of Kerberos) T_AuthKey_secret:
  for all #0 the premises
    "role( #0 ) = G"
    "uncompromised( G#0, ?A#0, ?C#0 )"
    "step(#0, G_3)"
    "knows(?AuthKey#0)"
  imply "False"
saturate
resolve 'Kerberos_msc_typing
sources(
    {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
  case fake
  contradicts secrecy of k(G#0,?A#0)
next
  case (A_2_enc #1)
  contradictory due to 'A_AuthKey_secret'
qed

property (of Kerberos) G_ServerKey_secret:
  for all #0 the premises
    "role( #0 ) = G"
    "uncompromised( G#0, ?A#0, ?C#0, ?S#0 )"
    "knows(~ServerKey#0)"
  imply "False"
resolve 'Kerberos_msc_typing
sources( ~ServerKey#0 )
  case G_4_ServerKey
  contradicts secrecy of k(G#0,?S#0)
next
  case G_4_ServerKey_1
  sources(
      {'2_1', ?C#0, G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(G#0,?A#0) )
    case fake
    contradicts secrecy of k(G#0,?A#0)
  next
    case (A_2_enc #1)
    contradictory due to 'A_AuthKey_secret'
  qed
qed

property (of Kerberos) C_ServerKey_secret:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( C#0, G#0, S#0, ?A#0 )"
    "step(#0, C_4)"
    "knows(?ServerKey#0)"
  imply "False"
saturate
resolve 'Kerberos_msc_typing
sources( {'2_2', G#0, ?AuthKey#0, ?T1start#0, ?T1expire#0}k(C#0,?A#0) )
  case fake
  contradicts secrecy of k(C#0,?A#0)
next
  case (A_2_enc_1 #1)
  sources(
      {'4_2', S#0, ?ServerKey#0, ?T2start#0, ?T2expire#0, ~N2#0}~AuthKey#1 )
    case fake
    contradictory due to 'A_AuthKey_secret'
  next
    case (G_4_enc_1 #2)
    sources(
        {'2_1', ?C#2, G#2, ~AuthKey#1, ?T1start#2, ?T1expire#2}k(G#2,?A#2) )
      case fake
      contradictory due to 'A_AuthKey_secret'
    next
      case (A_2_enc #3)
      contradictory due to 'G_ServerKey_secret'
    qed
  qed
qed

text{*
Server key secrecy is not given as it cannot check that authenticator is
uncompromised; i.e., the following does not hold

  S_ServerKey_secret: secret(S, 5, ServerKey, {C,A,G,S})

*}

subsection{* Authentication Properties *}

text{*
We first prove the following first send property to speedup the proof search.
*}

property (of Kerberos) C_N2_first_send:
  for all #1 the premises
    "role( #1 ) = C"
    "knows(~N2#1)"
  imply "St(#1, C_3) < Ln(~N2#1)"
resolve 'Kerberos_msc_typing
sources( ~N2#1 )
  case C_3_N2
  tautology
qed

property (of Kerberos) A_auth:
  for all #2 the premises
    "role( #2 ) = A"
    "uncompromised( ~S#2, A#2, ?C#2, ?G#2 )"
    "step(#2, A_2)"
  imply "St(#2, A_1) < St(#2, A_2)"
saturate
tautology

property (of Kerberos) G_auth:
  for all #3 the premises
    "role( #3 ) = G"
    "uncompromised( G#3, ?A#3, ?C#3, ?S#3 )"
    "step(#3, G_3)"
  imply
    "(? #1.
        (? #2.
           role( #1 ) = C &
           role( #2 ) = A &
           ?A#1 = ?A#3 &
           C#1 = ?C#3 &
           G#1 = G#3 &
           ?AuthKey#1 = ?AuthKey#3 &
           ~T1#1 = ?T1#3 &
           ?T1start#1 = ?T1start#3 &
           ?T1expire#1 = ?T1expire#3 &
           ?A#3 = A#2 &
           ?C#3 = ?C#2 &
           G#3 = ?G#2 &
           ?AuthKey#3 = ~AuthKey#2 &
           ?T1start#3 = ~T1start#2 &
           ?T1expire#3 = ~T1expire#2 &
           St(#2, A_2) < St(#1, C_2) &
           St(#1, C_2) < St(#1, C_3) & St(#1, C_3) < St(#3, G_3)))"
saturate
resolve 'Kerberos_msc_typing
sources(
    {'2_1', ?C#3, G#3, ?AuthKey#3, ?T1start#3, ?T1expire#3}k(G#3,?A#3) )
  case fake
  contradicts secrecy of k(G#3,?A#3)
next
  case (A_2_enc #4)
  sources( {'3', ?C#3, ?T1#3}~AuthKey#4 )
    case fake
    contradictory due to 'A_AuthKey_secret'
  next
    case (C_3_enc #5)
    sources( {'2_2', G#5, ~AuthKey#4, ?T1start#5, ?T1expire#5}k(C#5,?A#5) )
      case fake
      contradictory due to 'A_AuthKey_secret'
    next
      case (A_2_enc_1 #6)
      tautology
    qed
  qed
qed

text{* 
Authentication for the server S is also rather weak, as it cannot check whether
the authenticator is compromised or not.
*}

property (of Kerberos) S_auth:
  for all #4 the premises
    "role( #4 ) = S"
    "uncompromised( S#4, ?C#4, ?G#4 )"
    "step(#4, S_5)"
  imply
    "(? #1.
        (? #3.
           (? #4.
              role( #3 ) = G &
              ?C#4 = ?C#3 &
              ?G#4 = G#3 &
              S#4 = ?S#3 &
              ?ServerKey#4 = ~ServerKey#3 &
              ?T2start#4 = ~T2start#3 & ?T2expire#4 = ~T2expire#3)))"
saturate
resolve 'Kerberos_msc_typing
sources(
    {'4_1', ?C#4, S#4, ?ServerKey#4, ?T2start#4, ?T2expire#4}k(?G#4,S#4) )
  case fake
  contradicts secrecy of k(?G#4,S#4)
next
  case (G_4_enc #5)
  tautology
qed

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
              ?AuthKey#1 = ~AuthKey#2 &
              ?T1start#1 = ~T1start#2 &
              ?T1expire#1 = ~T1expire#2 &
              ?A#1 = ?A#3 &
              C#1 = ?C#3 &
              G#1 = G#3 &
              S#1 = ?S#3 &
              ?AuthKey#1 = ?AuthKey#3 &
              ?ServerKey#1 = ~ServerKey#3 &
              ~N2#1 = ?N2#3 &
              ?T2start#1 = ~T2start#3 &
              ?T2expire#1 = ~T2expire#3 &
              C#1 = ?C#4 &
              G#1 = ?G#4 &
              S#1 = S#4 &
              ~T2#1 = ?T2#4 &
              ?T2start#1 = ?T2start#4 &
              ?T2expire#1 = ?T2expire#4 &
              ?ServerKey#1 = ?ServerKey#4 &
              St(#2, A_2) < St(#1, C_2) &
              St(#1, C_2) < St(#1, C_3) &
              St(#1, C_3) < St(#3, G_3) &
              St(#3, G_3) < St(#3, G_4) &
              St(#3, G_4) < St(#1, C_4) &
              St(#1, C_4) < St(#1, C_5) &
              St(#1, C_5) < St(#4, S_5) &
              St(#4, S_5) < St(#4, S_6) & St(#4, S_6) < St(#1, C_6))))"
saturate
resolve 'Kerberos_msc_typing
sources( {'2_2', G#1, ?AuthKey#1, ?T1start#1, ?T1expire#1}k(C#1,?A#1) )
  case fake
  contradicts secrecy of k(C#1,?A#1)
next
  case (A_2_enc_1 #2)
  sources( {'6', ~T2#1}?ServerKey#1 )
    case fake
    contradictory due to 'C_ServerKey_secret'
  next
    case (S_6_enc #3)
    sources(
        {'4_2', S#1, ?ServerKey#1, ?T2start#1, ?T2expire#1, ~N2#1}~AuthKey#2 )
      case fake
      contradictory due to 'A_AuthKey_secret'
    next
      case (G_4_enc_1 #4)
      resolve 'C_N2_first_send' mapping #1 = #1
      sources(
          {'2_1', ?C#4, G#4, ~AuthKey#2, ?T1start#4, ?T1expire#4}k(G#4,?A#4) )
        case fake
        contradictory due to 'A_AuthKey_secret'
      next
        case (A_2_enc #5)
        sources(
            {'4_1', ?C#3, S#3, ~ServerKey#4, ?T2start#3, ?T2expire#3}k(?G#3,S#3) )
          case fake
          contradictory due to 'G_ServerKey_secret'
        next
          case (G_4_enc #5)
          sources( {'5', C#1, ~T2#1}~ServerKey#4 )
            case fake
            contradictory due to 'G_ServerKey_secret'
          next
            case (C_5_enc #5)
            tautology
          qed
        qed
      qed
    qed
  qed
qed

end