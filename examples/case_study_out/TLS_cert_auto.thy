theory TLS_cert_auto begin

section{* TLS Handshake *}

text{*
  Modeled after Paulson`s TLS model in Isabelle/src/HOL/Auth/TLS.thy. Notable
  differences are:

    1. We use explicit global constants to differentiate between different
       encryptions instead of implicit typing.

    2. We model session keys directly as hashes of the relevant information.
       Due to our support for composed keys, we do not need any custom
       axiomatization as Paulson does.

    3. We do not model the ClientResume, ServerResume, and Oops steps. They
       are currently outside the scope of our modelling language.

*}

protocol TLS
{ role C
  { Send_1(C, ~nc, ~sid, ~pc)
    Recv_2(?ns, ~sid, ?ps)
    Send_ca1( S )
    Recv_ca2(?CA, sign{'cert', S, ?pkS}pk(?CA))
    Send_3({'31', ~pms}?pkS, sign{'32', h('32', ?ns, S, ~pms)}pk(C), 
           {'33', ~sid, h('PRF', ~pms, ~nc, ?ns), ~nc, ~pc, C, ?ns, ?ps, S}
           h('clientKey', ~nc, ?ns, h('PRF', ~pms, ~nc, ?ns))
          )
    Recv_4( {'4', ~sid, h('PRF', ~pms, ~nc, ?ns), ~nc, ~pc, C, ?ns, ?ps, S}
            h('serverKey', ~nc, ?ns, h('PRF', ~pms, ~nc, ?ns))
          )
  }
  
  role CA
  { Recv_ca1( ?S )
    Send_ca2(CA, sign{'cert', ?S, pk(?S)}pk(CA))
  }
  
  role S
  { Recv_1(?C, ?nc, ?sid, ?pc)
    Send_2(~ns, ?sid, ~ps)
    Recv_3({'31', ?pms}pk(S), sign{'32', h('32', ~ns, S, ?pms)}pk(?C), 
           {'33', ?sid, h('PRF', ?pms, ?nc, ~ns), ?nc, ?pc, ?C, ~ns, ~ps, S}
           h('clientKey', ?nc, ~ns, h('PRF', ?pms, ?nc, ~ns))
          )
    Send_4( {'4', ?sid, h('PRF', ?pms, ?nc, ~ns), ?nc, ?pc, ?C, ~ns, ~ps, S}
            h('serverKey', ?nc, ~ns, h('PRF', ?pms, ?nc, ~ns))
          )
  }
}

property (of TLS) TLS_msc_typing:
  "C@S :: Known(S_1)
   CA@C :: Known(C_ca2)
   S@CA :: Known(CA_ca1)
   nc@S :: Known(S_1)
   ns@C :: Known(C_2)
   pc@S :: Known(S_1)
   pkS@C :: Known(C_ca2)
   pms@S :: (Known(S_3) | pms@C)
   ps@C :: Known(C_2)
   sid@S :: Known(S_1)"
proof
  case C_2_ns
  tautology
next
  case C_2_ps
  tautology
next
  case C_ca2_CA
  tautology
next
  case C_ca2_pkS
  tautology
next
  case S_1_C
  tautology
next
  case S_1_nc
  tautology
next
  case S_1_pc
  tautology
next
  case S_1_sid
  tautology
next
  case S_3_pms
  sources( h('32', ~ns#0, S#0, ?pms#0) )
  qed (3 trivial)
qed

text{* 
We assume that all clients talk to uncompromised certificate authorities. 
*}

axiom (of TLS) uncompromised_CA:
  for all #1 the premises
    "role( #1 ) = C"
  imply "uncompromised(?CA#1)"

subsection{* Secrecy Properties *}

property (of TLS) C_pms_sec:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( S#0 )"
    "knows(~pms#0)"
  imply "False"
resolve 'TLS_msc_typing
resolve 'uncompromised_CA' mapping #1 = #0
sources( ~pms#0 )
  case C_3_pms
  sources( {'cert', S#0, ?pkS#0}sk(?CA#0) )
    case fake
    contradicts secrecy of sk(?CA#0)
  next
    case (CA_ca2_enc #1)
    contradicts secrecy of sk(S#0)
  qed
qed

property (of TLS) C_PRF_sec:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( S#0 )"
    "knows(h('PRF', ~pms#0, ~nc#0, ?ns#0))"
  imply "False"
resolve 'TLS_msc_typing
sources( h('PRF', ~pms#0, ~nc#0, ?ns#0) )
  case fake
  contradictory due to 'C_pms_sec'
next
  case (C_3_hash_2 #1)
  sources( h('clientKey', ~nc#0, ?ns#0, h('PRF', ~pms#0, ~nc#0, ?ns#0)) )
  qed (1 trivial)
next
  case (S_4_hash #1)
  sources( h('serverKey', ~nc#0, ~ns#1, h('PRF', ~pms#0, ~nc#0, ~ns#1)) )
  qed (1 trivial)
qed

property (of TLS) C_clientKey_sec:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( S#0 )"
    "knows(h('clientKey', ~nc#0, ?ns#0, h('PRF', ~pms#0, ~nc#0, ?ns#0)))"
  imply "False"
resolve 'TLS_msc_typing
sources( h('clientKey', ~nc#0, ?ns#0, h('PRF', ~pms#0, ~nc#0, ?ns#0)) )
  case fake
  contradictory due to 'C_PRF_sec'
qed

property (of TLS) C_serverKey_sec:
  for all #0 the premises
    "role( #0 ) = C"
    "uncompromised( S#0 )"
    "knows(h('serverKey', ~nc#0, ?ns#0, h('PRF', ~pms#0, ~nc#0, ?ns#0)))"
  imply "False"
resolve 'TLS_msc_typing
sources( h('serverKey', ~nc#0, ?ns#0, h('PRF', ~pms#0, ~nc#0, ?ns#0)) )
  case fake
  contradictory due to 'C_PRF_sec'
qed

property (of TLS) S_pms_sec:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?C#0 )"
    "step(#0, S_4)"
    "knows(?pms#0)"
  imply "False"
saturate
resolve 'TLS_msc_typing
sources( {'32', h('32', ~ns#0, S#0, ?pms#0)}sk(?C#0) )
  case fake
  contradicts secrecy of sk(?C#0)
next
  case (C_3_enc_1 #1)
  contradictory due to 'C_pms_sec'
qed

property (of TLS) S_PRF_sec:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?C#0 )"
    "step(#0, S_4)"
    "knows(h('PRF', ?pms#0, ?nc#0, ~ns#0))"
  imply "False"
saturate
resolve 'TLS_msc_typing
sources( h('PRF', ?pms#0, ?nc#0, ~ns#0) )
  case fake
  contradictory due to 'S_pms_sec'
next
  case (C_3_hash_2 #1)
  sources( h('32', ~ns#0, S#0, ~pms#1) )
    case fake
    contradictory due to 'S_pms_sec'
  next
    case (C_3_hash #2)
    contradictory due to 'C_PRF_sec'
  next
    case (C_3_hash_1 #2)
    contradictory due to 'C_PRF_sec'
  qed
next
  case (S_4_hash #1)
  sources( h('serverKey', ?nc#0, ~ns#0, h('PRF', ?pms#0, ?nc#0, ~ns#0)) )
  qed (1 trivial)
qed

property (of TLS) S_clientKey_sec:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?C#0 )"
    "step(#0, S_4)"
    "knows(h('clientKey', ?nc#0, ~ns#0, h('PRF', ?pms#0, ?nc#0, ~ns#0)))"
  imply "False"
saturate
resolve 'TLS_msc_typing
sources( h('clientKey', ?nc#0, ~ns#0, h('PRF', ?pms#0, ?nc#0, ~ns#0)) )
  case fake
  contradictory due to 'S_PRF_sec'
qed

property (of TLS) S_serverKey_sec:
  for all #0 the premises
    "role( #0 ) = S"
    "uncompromised( S#0, ?C#0 )"
    "step(#0, S_4)"
    "knows(h('serverKey', ?nc#0, ~ns#0, h('PRF', ?pms#0, ?nc#0, ~ns#0)))"
  imply "False"
saturate
resolve 'TLS_msc_typing
sources( h('serverKey', ?nc#0, ~ns#0, h('PRF', ?pms#0, ?nc#0, ~ns#0)) )
  case fake
  contradictory due to 'S_PRF_sec'
qed

subsection{* Authentication Properties *}

text{*
  First, we prove two first send properties in order to simplify proof search
  for the authentication properties.
*}

property (of TLS) nc_first_send:
  for all #1 the premises
    "role( #1 ) = C"
    "knows(~nc#1)"
  imply "St(#1, C_1) < Ln(~nc#1)"
resolve 'TLS_msc_typing
sources( ~nc#1 )
  case C_1_nc
  tautology
next
  case C_3_nc
  tautology
qed

property (of TLS) ns_first_send:
  for all #1 the premises
    "role( #1 ) = S"
    "knows(~ns#1)"
  imply "St(#1, S_2) < Ln(~ns#1)"
resolve 'TLS_msc_typing
sources( ~ns#1 )
  case S_2_ns
  tautology
next
  case S_4_ns
  tautology
qed

property (of TLS) C_ni_synch:
  for all #1 the premises
    "role( #1 ) = C"
    "uncompromised( C#1, S#1 )"
    "step(#1, C_4)"
  imply
    "(? #2.
        role( #2 ) = S &
        C#1 = ?C#2 &
        S#1 = S#2 &
        ~nc#1 = ?nc#2 &
        ?ns#1 = ~ns#2 &
        ~pc#1 = ?pc#2 &
        ?ps#1 = ~ps#2 &
        ~sid#1 = ?sid#2 &
        ~pms#1 = ?pms#2 &
        St(#1, C_1) < St(#2, S_1) &
        St(#2, S_1) < St(#2, S_2) &
        St(#2, S_2) < St(#1, C_2) &
        St(#1, C_2) < St(#1, C_3) &
        St(#1, C_3) < St(#2, S_3) &
        St(#2, S_3) < St(#2, S_4) & St(#2, S_4) < St(#1, C_4))"
saturate
resolve 'TLS_msc_typing
sources(
    {'4', ~sid#1, h('PRF', ~pms#1, ~nc#1, ?ns#1), ~nc#1, ~pc#1, C#1, ?ns#1, 
     ?ps#1, S#1}
    h('serverKey', ~nc#1, ?ns#1, h('PRF', ~pms#1, ~nc#1, ?ns#1)) )
  case fake
  contradictory due to 'C_PRF_sec'
next
  case (S_4_enc #2)
  resolve 'nc_first_send' mapping #1 = #1
  resolve 'ns_first_send' mapping #1 = #2
  sources( {'31', ~pms#1}pk(S#1) )
    case fake
    contradictory due to 'C_pms_sec'
  next
    case (C_3_enc #3)
    tautology
  qed
qed

property (of TLS) S_ni_synch:
  for all #2 the premises
    "role( #2 ) = S"
    "uncompromised( S#2, ?C#2 )"
    "step(#2, S_4)"
  imply
    "(? #1.
        role( #1 ) = C &
        C#1 = ?C#2 &
        S#1 = S#2 &
        ~nc#1 = ?nc#2 &
        ?ns#1 = ~ns#2 &
        ~pc#1 = ?pc#2 &
        ?ps#1 = ~ps#2 &
        ~sid#1 = ?sid#2 &
        ~pms#1 = ?pms#2 &
        St(#1, C_1) < St(#2, S_1) &
        St(#2, S_1) < St(#2, S_2) &
        St(#2, S_2) < St(#1, C_2) &
        St(#1, C_2) < St(#1, C_3) &
        St(#1, C_3) < St(#2, S_3) & St(#2, S_3) < St(#2, S_4))"
saturate
resolve 'TLS_msc_typing
sources(
    {'33', ?sid#2, h('PRF', ?pms#2, ?nc#2, ~ns#2), ?nc#2, ?pc#2, ?C#2, 
     ~ns#2, ~ps#2, S#2}
    h('clientKey', ?nc#2, ~ns#2, h('PRF', ?pms#2, ?nc#2, ~ns#2)) )
  case fake
  contradictory due to 'S_PRF_sec'
next
  case (C_3_enc_2 #3)
  resolve 'nc_first_send' mapping #1 = #3
  resolve 'ns_first_send' mapping #1 = #2
  tautology
qed

end