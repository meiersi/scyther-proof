theory BAN_modified_CCITT_X509_3_cert_auto begin

section{* BAN modified version of CCITT X.509 (3) *}

text{*
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We prove non-injective synchronization, which is stronger than the
       authentication on Ya and Yb required in the SPORE description.

    3. We equate all timestamps to a single global constant; i.e., we assume
       no checking of timestamps is done.

*}

protocol X509
{ role A
  { Send_1(A, sign{'1_1', 'Time', ~Na, B, ~Xa, {'1_2', ~Ya}pk(B)}pk(A))
    Recv_2(B, sign{'2_1', 'Time', ?Nb, A, ~Na, ?Xb, {'2_2', ?Yb}pk(A)}pk(B))
    Send_3(A, sign{'3', B, ?Nb}pk(A))
  }
  
  role B
  { Recv_1(?A, sign{'1_1', 'Time', ?Na, B, ?Xa, {'1_2', ?Ya}pk(B)}pk(?A))
    Send_2(B, sign{'2_1', 'Time', ~Nb, ?A, ?Na, ~Xb, {'2_2', ~Yb}pk(?A)}pk(B)
          )
    Recv_3(?A, sign{'3', B, ~Nb}pk(?A))
  }
}

property (of X509) X509_msc_typing:
  "A@B :: Known(B_1)
   Na@B :: Known(B_1)
   Nb@A :: Known(A_2)
   Xa@B :: Known(B_1)
   Xb@A :: Known(A_2)
   Ya@B :: (Known(B_1) | Ya@A)
   Yb@A :: (Known(A_2) | Yb@B)"
proof
  case A_2_Nb
  tautology
next
  case A_2_Xb
  tautology
next
  case A_2_Yb
  sources( {'2_2', ?Yb#0}pk(A#0) )
  qed (3 trivial)
next
  case B_1_A
  tautology
next
  case B_1_Na
  tautology
next
  case B_1_Xa
  tautology
next
  case B_1_Ya
  sources( {'1_2', ?Ya#0}pk(B#0) )
  qed (3 trivial)
qed

subsection{* Security Properties *}

property (of X509) A_Ya_secrecy:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, B#0 )"
    "knows(~Ya#0)"
  imply "False"
resolve 'X509_msc_typing
sources( ~Ya#0 )
  case A_1_Ya
  contradicts secrecy of sk(B#0)
next
  case A_1_Ya_1
  contradicts secrecy of sk(B#0)
qed

property (of X509) B_Yb_secrecy:
  for all #0 the premises
    "role( #0 ) = B"
    "uncompromised( B#0, ?A#0 )"
    "knows(~Yb#0)"
  imply "False"
resolve 'X509_msc_typing
sources( ~Yb#0 )
  case B_2_Yb
  contradicts secrecy of sk(?A#0)
next
  case B_2_Yb_1
  contradicts secrecy of sk(?A#0)
qed

property (of X509) B_Ya_secrecy:
  for all #0 the premises
    "role( #0 ) = B"
    "uncompromised( B#0, ?A#0 )"
    "step(#0, B_1)"
    "knows(?Ya#0)"
  imply "False"
saturate
resolve 'X509_msc_typing
sources(
    {'1_1', 'Time', ?Na#0, B#0, ?Xa#0, {'1_2', ?Ya#0}pk(B#0)}sk(?A#0) )
  case fake
  contradicts secrecy of sk(?A#0)
next
  case (A_1_enc_1 #1)
  contradictory due to 'A_Ya_secrecy'
qed

property (of X509) A_Yb_secrecy:
  for all #0 the premises
    "role( #0 ) = A"
    "uncompromised( A#0, B#0 )"
    "step(#0, A_2)"
    "knows(?Yb#0)"
  imply "False"
saturate
resolve 'X509_msc_typing
sources(
    {'2_1', 'Time', ?Nb#0, A#0, ~Na#0, ?Xb#0, {'2_2', ?Yb#0}pk(A#0)}sk(B#0) )
  case fake
  contradicts secrecy of sk(B#0)
next
  case (B_2_enc_1 #1)
  contradictory due to 'B_Yb_secrecy'
qed

property (of X509) A_noninjective_synch:
  for all #1 the premises
    "role( #1 ) = A"
    "uncompromised( A#1, B#1 )"
    "step(#1, A_3)"
  imply
    "(? #2.
        role( #2 ) = B &
        A#1 = ?A#2 &
        B#1 = B#2 &
        ~Na#1 = ?Na#2 &
        ?Nb#1 = ~Nb#2 &
        ~Ya#1 = ?Ya#2 &
        ?Yb#1 = ~Yb#2 &
        St(#1, A_1) < St(#2, B_1) &
        St(#2, B_2) < St(#1, A_2) &
        St(#1, A_1) < St(#1, A_2) &
        St(#1, A_2) < St(#1, A_3) & St(#2, B_1) < St(#2, B_2))"
saturate
resolve 'X509_msc_typing
sources(
    {'2_1', 'Time', ?Nb#1, A#1, ~Na#1, ?Xb#1, {'2_2', ?Yb#1}pk(A#1)}sk(B#1) )
  case fake
  contradicts secrecy of sk(B#1)
next
  case (B_2_enc_1 #2)
  sources(
      {'1_1', 'Time', ~Na#1, B#1, ?Xa#2, {'1_2', ?Ya#2}pk(B#1)}sk(A#1) )
    case fake
    contradicts secrecy of sk(A#1)
  next
    case (A_1_enc_1 #3)
    tautology
  qed
qed

property (of X509) B_noninjective_synch:
  for all #2 the premises
    "role( #2 ) = B"
    "uncompromised( B#2, ?A#2 )"
    "step(#2, B_3)"
  imply
    "(? #1.
        role( #1 ) = A &
        A#1 = ?A#2 &
        B#1 = B#2 &
        ~Na#1 = ?Na#2 &
        ?Nb#1 = ~Nb#2 &
        ~Ya#1 = ?Ya#2 &
        ?Yb#1 = ~Yb#2 &
        St(#1, A_1) < St(#2, B_1) &
        St(#2, B_2) < St(#1, A_2) &
        St(#1, A_3) < St(#2, B_3) &
        St(#1, A_1) < St(#1, A_2) &
        St(#1, A_2) < St(#1, A_3) &
        St(#2, B_1) < St(#2, B_2) & St(#2, B_2) < St(#2, B_3))"
saturate
resolve 'X509_msc_typing
sources(
    {'1_1', 'Time', ?Na#2, B#2, ?Xa#2, {'1_2', ?Ya#2}pk(B#2)}sk(?A#2) )
  case fake
  contradicts secrecy of sk(?A#2)
next
  case (A_1_enc_1 #3)
  sources( {'3', B#2, ~Nb#2}sk(A#3) )
    case fake
    contradicts secrecy of sk(A#3)
  next
    case (A_3_enc #4)
    sources(
        {'2_1', 'Time', ~Nb#2, A#3, ~Na#4, ?Xb#4, {'2_2', ?Yb#4}pk(A#3)}sk(B#2) )
      case fake
      contradicts secrecy of sk(B#2)
    next
      case (B_2_enc_1 #5)
      tautology
    qed
  qed
qed

end