theory Lowe_fixed_Needham_Schroeder_Public_Key_cert_auto begin

section{* Needham-Schroeder-Lowe Public-Key Protocol *}

text{*
  Modelled after SPORE.

  Notable differences:
    1. We use explicit global constants instead of implicit typing to discern
       the different messages.
    
    2. We model a single certificate-authority (CA) server role, which is used
       to answer the certificate requests from both A and B.

    2. We prove non-injective synchronization, which is stronger than the
       entity authentication property stated in SPORE as the requirement on
       this protocol.

*}

protocol NSLPK
{ role I
  { Send_ca1(I, R)
    Recv_ca2(?S, sign{'ca2', ?pkR, R}pk(?S))
    Send_1(I, {'1', ~ni, I}?pkR)
    Recv_2( {'2', ~ni, ?nr, R}pk(I) )
    Send_3( {'3', ?nr}?pkR )
  }
  
  role R
  { Recv_1(?I, {'1', ?ni, ?I}pk(R))
    Send_ca1(R, ?I)
    Recv_ca2(?S, sign{'ca2', ?pkI, ?I}pk(?S))
    Send_2( {'2', ?ni, ~nr, R}?pkI )
    Recv_3( {'3', ~nr}pk(R) )
  }
  
  role S
  { Recv_ca1(?A, ?B)
    Send_ca2(S, sign{'ca2', pk(?B), ?B}pk(S))
  }
}

property (of NSLPK) NSLPK_msc_typing:
  "A@S :: Known(S_ca1)
   B@S :: Known(S_ca1)
   I@R :: Known(R_1)
   S@I :: Known(I_ca2)
   S@R :: Known(R_ca2)
   ni@R :: (Known(R_1) | ni@I)
   nr@I :: (Known(I_2) | nr@R)
   pkI@R :: Known(R_ca2)
   pkR@I :: Known(I_ca2)"
proof
  case I_ca2_S
  tautology
next
  case I_ca2_pkR
  tautology
next
  case I_2_nr
  sources( {'2', ~ni#0, ?nr#0, R#0}pk(I#0) )
  qed (2 trivial)
next
  case R_1_I
  tautology
next
  case R_1_ni
  sources( {'1', ?ni#0, ?I#0}pk(R#0) )
  qed (2 trivial)
next
  case R_ca2_S
  tautology
next
  case R_ca2_pkI
  tautology
next
  case S_ca1_A
  tautology
next
  case S_ca1_B
  tautology
qed

subsection{* Assumptions *}

text{* 
  Initiators as well as responders talk to an uncompromised server. 
*}

axiom (of NSLPK) I_uncompromised_S:
  for all #1 the premises
    "role( #1 ) = I"
  imply "uncompromised(?S#1)"

axiom (of NSLPK) R_uncompromised_S:
  for all #1 the premises
    "role( #1 ) = R"
  imply "uncompromised(?S#1)"

subsection{* Security Properties *}

property (of NSLPK) I_pkR_auth:
  for all #1 the premises
    "role( #1 ) = I"
    "step(#1, I_ca2)"
  imply "?pkR#1 = pk(R#1)"
saturate
resolve 'NSLPK_msc_typing
resolve 'I_uncompromised_S' mapping #1 = #1
sources( {'ca2', ?pkR#1, R#1}sk(?S#1) )
  case fake
  contradicts secrecy of sk(?S#1)
next
  case (S_ca2_enc #2)
  tautology
qed

property (of NSLPK) R_pkI_auth:
  for all #1 the premises
    "role( #1 ) = R"
    "step(#1, R_ca2)"
  imply "?pkI#1 = pk(?I#1)"
saturate
resolve 'NSLPK_msc_typing
resolve 'R_uncompromised_S' mapping #1 = #1
sources( {'ca2', ?pkI#1, ?I#1}sk(?S#1) )
  case fake
  contradicts secrecy of sk(?S#1)
next
  case (S_ca2_enc #2)
  tautology
qed

property (of NSLPK) I_ni_secrecy:
  for all #0 the premises
    "role( #0 ) = I"
    "uncompromised( I#0, R#0 )"
    "knows(~ni#0)"
  imply "False"
resolve 'NSLPK_msc_typing
sources( ~ni#0 )
  case I_1_ni
  resolve 'I_pkR_auth' mapping #1 = #0
  contradicts secrecy of sk(R#0)
next
  case (R_2_ni #1)
  resolve 'R_pkI_auth' mapping #1 = #1
  sources( {'1', ~ni#0, ?I#1}pk(R#1) )
    case (I_1_enc #2)
    contradicts secrecy of sk(I#0)
  qed (1 trivial)
qed

property (of NSLPK) R_nr_secrecy:
  for all #0 the premises
    "role( #0 ) = R"
    "uncompromised( R#0, ?I#0 )"
    "knows(~nr#0)"
  imply "False"
resolve 'NSLPK_msc_typing
sources( ~nr#0 )
  case (I_3_nr #1)
  resolve 'I_pkR_auth' mapping #1 = #1
  sources( {'2', ~ni#1, ~nr#0, R#1}pk(I#1) )
    case (R_2_enc #2)
    contradicts secrecy of sk(R#0)
  qed (1 trivial)
next
  case R_2_nr
  resolve 'R_pkI_auth' mapping #1 = #0
  contradicts secrecy of sk(?I#0)
qed

property (of NSLPK) I_nr_secrecy:
  for all #0 the premises
    "role( #0 ) = I"
    "uncompromised( I#0, R#0 )"
    "step(#0, I_2)"
    "knows(?nr#0)"
  imply "False"
saturate
resolve 'NSLPK_msc_typing
sources( {'2', ~ni#0, ?nr#0, R#0}pk(I#0) )
  case fake
  contradictory due to 'I_ni_secrecy'
next
  case (R_2_enc #1)
  resolve 'R_pkI_auth' mapping #1 = #1
  contradictory due to 'R_nr_secrecy'
qed

property (of NSLPK) R_ni_secrecy:
  for all #0 the premises
    "role( #0 ) = R"
    "uncompromised( R#0, ?I#0 )"
    "step(#0, R_3)"
    "knows(?ni#0)"
  imply "False"
saturate
resolve 'NSLPK_msc_typing
resolve 'R_pkI_auth' mapping #1 = #0
sources( {'3', ~nr#0}pk(R#0) )
  case fake
  contradictory due to 'R_nr_secrecy'
next
  case (I_3_enc #1)
  resolve 'I_pkR_auth' mapping #1 = #1
  sources( {'2', ~ni#1, ~nr#0, R#0}pk(I#1) )
    case fake
    contradictory due to 'R_nr_secrecy'
  next
    case (R_2_enc #2)
    contradictory due to 'I_ni_secrecy'
  qed
qed

property (of NSLPK) I_noninjective_synch:
  for all #1 the premises
    "role( #1 ) = I"
    "uncompromised( I#1, R#1 )"
    "step(#1, I_2)"
  imply
    "(? #2.
        role( #2 ) = R &
        I#1 = ?I#2 &
        R#1 = R#2 &
        ~ni#1 = ?ni#2 &
        ?nr#1 = ~nr#2 &
        St(#1, I_1) < St(#2, R_1) &
        St(#2, R_2) < St(#1, I_2) &
        St(#1, I_1) < St(#1, I_2) & St(#2, R_1) < St(#2, R_2))"
saturate
resolve 'NSLPK_msc_typing
sources( {'2', ~ni#1, ?nr#1, R#1}pk(I#1) )
  case fake
  contradictory due to 'I_ni_secrecy'
next
  case (R_2_enc #2)
  resolve 'R_pkI_auth' mapping #1 = #2
  sources( {'1', ~ni#1, I#1}pk(R#1) )
    case fake
    contradictory due to 'I_ni_secrecy'
  next
    case (I_1_enc #3)
    tautology
  qed
qed

property (of NSLPK) R_noninjective_synch:
  for all #2 the premises
    "role( #2 ) = R"
    "uncompromised( R#2, ?I#2 )"
    "step(#2, R_3)"
  imply
    "(? #1.
        role( #1 ) = I &
        I#1 = ?I#2 &
        R#1 = R#2 &
        ~ni#1 = ?ni#2 &
        ?nr#1 = ~nr#2 &
        St(#1, I_1) < St(#2, R_1) &
        St(#2, R_2) < St(#1, I_2) &
        St(#1, I_3) < St(#2, R_3) &
        St(#1, I_1) < St(#1, I_2) &
        St(#1, I_2) < St(#1, I_3) &
        St(#2, R_1) < St(#2, R_2) & St(#2, R_2) < St(#2, R_3))"
saturate
resolve 'NSLPK_msc_typing
sources( {'1', ?ni#2, ?I#2}pk(R#2) )
  case fake
  contradictory due to 'R_ni_secrecy'
next
  case (I_1_enc #3)
  sources( {'3', ~nr#2}pk(R#2) )
    case fake
    contradictory due to 'R_nr_secrecy'
  next
    case (I_3_enc #4)
    resolve 'I_pkR_auth' mapping #1 = #4
    sources( {'2', ~ni#4, ~nr#2, R#2}pk(I#4) )
      case fake
      contradictory due to 'R_nr_secrecy'
    next
      case (R_2_enc #5)
      tautology
    qed
  qed
qed

end