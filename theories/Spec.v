From Stdlib Require Import Lists.List.
From Tftp Require Import Bytes Packet.
Import ListNotations.

(* A declarative description of complete RFC 1350 datagrams in the
   supported subset. Mode spelling is case insensitive on the wire. *)
Inductive wire_packet : list byte -> packet -> Prop :=
| WireRRQ : forall name raw_mode m,
    request_name name -> bytes_ok raw_mode -> mode_matches raw_mode m ->
    wire_packet ([0; 1] ++ name ++ [0] ++ raw_mode ++ [0]) (RRQ name m)
| WireWRQ : forall name raw_mode m,
    request_name name -> bytes_ok raw_mode -> mode_matches raw_mode m ->
    wire_packet ([0; 2] ++ name ++ [0] ++ raw_mode ++ [0]) (WRQ name m)
| WireDATA : forall hi lo payload,
    byte_ok hi -> byte_ok lo -> bytes_ok payload -> length payload <= 512 ->
    wire_packet ([0; 3; hi; lo] ++ payload)
                (DATA (decode_u16 hi lo) payload)
| WireACK : forall hi lo,
    byte_ok hi -> byte_ok lo ->
    wire_packet [0; 4; hi; lo] (ACK (decode_u16 hi lo))
| WireERROR : forall hi lo message,
    byte_ok hi -> byte_ok lo -> text_field message ->
    wire_packet ([0; 5; hi; lo] ++ message ++ [0])
                (ERROR (decode_u16 hi lo) message).

Lemma wire_packet_valid : forall bs p, wire_packet bs p -> valid_packet p.
Proof.
  intros bs p H; induction H; simpl; auto.
  - repeat split; try assumption. now apply decode_u16_word_ok.
  - now apply decode_u16_word_ok.
  - split; [now apply decode_u16_word_ok|assumption].
Qed.
