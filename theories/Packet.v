From Stdlib Require Import Lists.List.
From Tftp Require Import Bytes.
Import ListNotations.

Inductive mode := Netascii | Octet.

Definition mode_name (m : mode) : list byte :=
  match m with
  | Netascii => [110; 101; 116; 97; 115; 99; 105; 105]
  | Octet => [111; 99; 116; 101; 116]
  end.

Definition mode_matches (raw : list byte) (m : mode) : Prop :=
  map ascii_lower raw = mode_name m.

Inductive packet :=
| RRQ (filename : list byte) (transfer_mode : mode)
| WRQ (filename : list byte) (transfer_mode : mode)
| DATA (block : word16) (payload : list byte)
| ACK (block : word16)
| ERROR (code : word16) (message : list byte).

Definition text_field (xs : list byte) : Prop :=
  bytes_ok xs /\ ~ In 0 xs.

Definition request_name (name : list byte) : Prop :=
  name <> [] /\ text_field name.

Definition valid_packet (p : packet) : Prop :=
  match p with
  | RRQ name _ | WRQ name _ => request_name name
  | DATA block payload => word_ok block /\ bytes_ok payload /\ length payload <= 512
  | ACK block => word_ok block
  | ERROR code message => word_ok code /\ text_field message
  end.

Lemma mode_name_bytes_ok : forall m, bytes_ok (mode_name m).
Proof. destruct m; repeat constructor; unfold byte_ok; auto with arith. Qed.

Lemma mode_name_no_zero : forall m, ~ In 0 (mode_name m).
Proof. destruct m; simpl; intuition discriminate. Qed.

Lemma mode_name_lower : forall m, map ascii_lower (mode_name m) = mode_name m.
Proof. destruct m; reflexivity. Qed.
