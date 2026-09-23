---------------------------- MODULE MCJuuriTxn ----------------------------
(***************************************************************************)
(* Model values for JuuriTxn: five keys over a two-letter alphabet --      *)
(* enough for a root value, a key with a child, a branch node, splits      *)
(* inside a two-byte segment and merges -- and three starting shapes.      *)
(***************************************************************************)
EXTENDS JuuriTxn

MCKeys == {<<>>, <<1>>, <<1, 1>>, <<1, 2>>, <<2>>}
MCProbes == MCKeys \cup {<<1, 2, 1>>}
MCInitContents == {{}, {<<1, 1>>, <<1, 2>>}, {<<>>, <<1>>, <<1, 2>>, <<2>>}}
=============================================================================
