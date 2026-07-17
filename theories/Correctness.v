From Stdlib Require Import Lists.List Arith.Arith Bool.Bool micromega.Lia.
From Tftp Require Import Bytes Packet Spec Codec.
Import ListNotations.

Lemma decode_mode_sound : forall raw m,
  decode_mode raw = Some m -> mode_matches raw m.
Proof.
  intros raw m H. unfold decode_mode in H.
  destruct (list_eq_dec Nat.eq_dec (map ascii_lower raw) (mode_name Netascii)) as [E|E].
  - inversion H; subst; exact E.
  - destruct (list_eq_dec Nat.eq_dec (map ascii_lower raw) (mode_name Octet)) as [F|F].
    + inversion H; subst; exact F.
    + discriminate.
Qed.

Lemma decode_mode_complete : forall raw m,
  mode_matches raw m -> decode_mode raw = Some m.
Proof.
  intros raw m H. unfold decode_mode, mode_matches in *.
  rewrite H. destruct m; reflexivity.
Qed.

Lemma parse_request_sound : forall rest name m,
  parse_request rest = Some (name, m) ->
  exists raw, rest = name ++ [0] ++ raw ++ [0] /\
    name <> [] /\ ~ In 0 name /\ ~ In 0 raw /\ mode_matches raw m.
Proof.
  intros rest name m H. unfold parse_request in H.
  destruct (take_zero rest) as [[n tail]|] eqn:E1; try discriminate.
  destruct (Nat.eqb (length n) 0) eqn:En; try discriminate.
  destruct (take_zero tail) as [[raw suffix]|] eqn:E2; try discriminate.
  destruct suffix as [|x suffix]; try discriminate.
  destruct (decode_mode raw) as [m0|] eqn:Em; try discriminate.
  inversion H; subst n m0. clear H.
  apply take_zero_sound in E1 as [Erest Hname].
  apply take_zero_sound in E2 as [Etail Hraw].
  apply Nat.eqb_neq in En.
  exists raw. subst tail rest. split; [reflexivity|].
  split.
  - destruct name; [simpl in En; contradiction|discriminate].
  - repeat split; try assumption. now apply decode_mode_sound.
Qed.

Lemma parse_request_complete : forall name raw m,
  name <> [] -> ~ In 0 name -> ~ In 0 raw -> mode_matches raw m ->
  parse_request (name ++ [0] ++ raw ++ [0]) = Some (name, m).
Proof.
  intros name raw m Hnonempty Hname Hraw Hmode.
  destruct name as [|b name]; [contradiction|].
  unfold parse_request.
  change (match take_zero ((b :: name) ++ 0 :: (raw ++ [0])) with
          | Some (n, tail) =>
              if Nat.eqb (length n) 0 then None else
              match take_zero tail with
              | Some (r, []) =>
                  match decode_mode r with
                  | Some m0 => Some (n, m0) | None => None end
              | _ => None end
          | None => None end = Some (b :: name, m)).
  rewrite take_zero_complete by exact Hname.
  simpl. rewrite take_zero_complete by exact Hraw.
  rewrite (decode_mode_complete raw m Hmode). reflexivity.
Qed.

Lemma bytes_ok_app : forall a b,
  bytes_ok (a ++ b) <-> bytes_ok a /\ bytes_ok b.
Proof. intros; apply Forall_app. Qed.

Lemma bytes_ok_single : forall b, byte_ok b -> bytes_ok [b].
Proof. intros; constructor; [assumption|constructor]. Qed.

Lemma bytes_ok_middle : forall a b c,
  bytes_ok (a ++ b ++ c) -> bytes_ok b.
Proof.
  intros a b c H. apply bytes_ok_app in H as [_ H].
  apply bytes_ok_app in H as [H _]. exact H.
Qed.

Lemma request_bytes_ok : forall opcode name raw,
  bytes_ok ([0; opcode] ++ name ++ [0] ++ raw ++ [0]) ->
  bytes_ok name /\ bytes_ok raw.
Proof.
  intros opcode name raw H. split.
  - eapply (bytes_ok_middle [0; opcode] name ([0] ++ raw ++ [0])); exact H.
  - apply bytes_ok_app in H as [_ H].
    apply bytes_ok_app in H as [_ H].
    apply bytes_ok_app in H as [_ H].
    apply bytes_ok_app in H as [H _]. exact H.
Qed.

Lemma header_bytes_ok : forall op hi lo tail,
  bytes_ok ([0; op; hi; lo] ++ tail) ->
  byte_ok hi /\ byte_ok lo /\ bytes_ok tail.
Proof.
  intros op hi lo tail H.
  apply bytes_ok_app in H as [Hhead Htail].
  unfold bytes_ok in Hhead.
  pose proof (proj1 (@Forall_forall byte byte_ok [0; op; hi; lo]) Hhead) as Hall.
  repeat split; try assumption; apply Hall; simpl; auto.
Qed.

Lemma error_message_ok : forall hi lo message,
  bytes_ok ([0; 5; hi; lo] ++ message ++ [0]) -> bytes_ok message.
Proof.
  intros hi lo message H.
  apply bytes_ok_app in H as [_ H].
  apply bytes_ok_app in H as [H _]. exact H.
Qed.

Theorem parse_sound : forall bs p,
  parse bs = Some p -> wire_packet bs p.
Proof.
  intros bs p Hparse. unfold parse in Hparse.
  destruct (bytes_okb bs) eqn:Ebytes; try discriminate.
  apply bytes_okb_spec in Ebytes.
  destruct bs as [|first bs]; try discriminate.
  destruct first as [|first]; try discriminate.
  destruct bs as [|opcode rest]; try discriminate.
  destruct opcode as [|opcode]; try discriminate.
  destruct opcode as [|opcode].
  - destruct (parse_request rest) as [[name m]|] eqn:Ereq; try discriminate.
    inversion Hparse; subst p. clear Hparse.
    apply parse_request_sound in Ereq as [raw [Erest [Hnonempty [Hname [Hraw Hmode]]]]].
    subst rest. apply WireRRQ.
    + split; [exact Hnonempty|]. split; [apply (request_bytes_ok 1 name raw Ebytes)|exact Hname].
    + apply (request_bytes_ok 1 name raw Ebytes).
    + exact Hmode.
  - destruct opcode as [|opcode].
    + destruct (parse_request rest) as [[name m]|] eqn:Ereq; try discriminate.
      inversion Hparse; subst p. clear Hparse.
      apply parse_request_sound in Ereq as [raw [Erest [Hnonempty [Hname [Hraw Hmode]]]]].
      subst rest. apply WireWRQ.
      * split; [exact Hnonempty|]. split; [apply (request_bytes_ok 2 name raw Ebytes)|exact Hname].
      * apply (request_bytes_ok 2 name raw Ebytes).
      * exact Hmode.
    + destruct opcode as [|opcode].
      * destruct rest as [|hi [|lo payload]]; try discriminate.
        destruct (length payload <=? 512) eqn:Elen; try discriminate.
        inversion Hparse; subst p. clear Hparse.
        apply Nat.leb_le in Elen.
        destruct (header_bytes_ok 3 hi lo payload Ebytes) as [Hhi [Hlo Hpayload]].
        now apply WireDATA.
      * destruct opcode as [|opcode].
        { destruct rest as [|hi [|lo [|extra tail]]]; try discriminate.
          inversion Hparse; subst p. clear Hparse.
          destruct (header_bytes_ok 4 hi lo [] Ebytes) as [Hhi [Hlo _]].
          now apply WireACK. }
        destruct opcode as [|opcode].
        { destruct rest as [|hi [|lo tail]]; try discriminate.
          destruct (take_zero tail) as [[message suffix]|] eqn:Ez; try discriminate.
          destruct suffix as [|extra suffix]; try discriminate.
          inversion Hparse; subst p. clear Hparse.
          apply take_zero_sound in Ez as [Etail Hmessage]. subst tail.
          destruct (header_bytes_ok 5 hi lo (message ++ [0]) Ebytes) as [Hhi [Hlo _]].
          apply WireERROR; try assumption.
          split; [apply (error_message_ok hi lo message Ebytes)|exact Hmessage]. }
        destruct opcode; discriminate.
Qed.

Lemma mode_matches_no_zero : forall raw m,
  mode_matches raw m -> ~ In 0 raw.
Proof.
  intros raw m H Hin. apply (mode_name_no_zero m).
  unfold mode_matches in H. rewrite <- H.
  change (In (ascii_lower 0) (map ascii_lower raw)).
  now apply in_map.
Qed.

Lemma wire_packet_bytes_ok : forall bs p,
  wire_packet bs p -> bytes_ok bs.
Proof.
  intros bs p H; induction H.
  - repeat rewrite bytes_ok_app. repeat split; try assumption.
    + repeat constructor; unfold byte_ok; lia.
    + destruct H as [_ [Hname _]]. exact Hname.
    + repeat constructor; unfold byte_ok; lia.
    + repeat constructor; unfold byte_ok; lia.
  - repeat rewrite bytes_ok_app. repeat split; try assumption.
    + repeat constructor; unfold byte_ok; lia.
    + destruct H as [_ [Hname _]]. exact Hname.
    + repeat constructor; unfold byte_ok; lia.
    + repeat constructor; unfold byte_ok; lia.
  - apply bytes_ok_app. split; [|assumption].
    constructor; [unfold byte_ok; lia|].
    constructor; [unfold byte_ok; lia|].
    constructor; [exact H|].
    constructor; [exact H0|constructor].
  - constructor; [unfold byte_ok; lia|].
    constructor; [unfold byte_ok; lia|].
    constructor; [exact H|].
    constructor; [exact H0|constructor].
  - repeat rewrite bytes_ok_app. repeat split; try assumption.
    + constructor; [unfold byte_ok; lia|].
      constructor; [unfold byte_ok; lia|].
      constructor; [exact H|].
      constructor; [exact H0|constructor].
    + destruct H1 as [Hmessage _]. exact Hmessage.
    + repeat constructor; unfold byte_ok; lia.
Qed.

Theorem parse_complete : forall bs p,
  wire_packet bs p -> parse bs = Some p.
Proof.
  intros bs p Hwire. pose proof (wire_packet_bytes_ok _ _ Hwire) as Hbytes.
  induction Hwire; unfold parse; rewrite (proj2 (bytes_okb_spec _) Hbytes); simpl.
  - replace (name ++ 0 :: raw_mode ++ [0]) with
      (name ++ [0] ++ raw_mode ++ [0]) by reflexivity.
    pose proof (parse_request_complete name raw_mode m
      (proj1 H) (proj2 (proj2 H))
      (mode_matches_no_zero raw_mode m H1) H1) as Hreq.
    destruct (parse_request (name ++ [0] ++ raw_mode ++ [0])) as [[n m0]|] eqn:Ereq.
    + unfold byte in Ereq. congruence.
    + unfold byte in Ereq. congruence.
  - replace (name ++ 0 :: raw_mode ++ [0]) with
      (name ++ [0] ++ raw_mode ++ [0]) by reflexivity.
    pose proof (parse_request_complete name raw_mode m
      (proj1 H) (proj2 (proj2 H))
      (mode_matches_no_zero raw_mode m H1) H1) as Hreq.
    destruct (parse_request (name ++ [0] ++ raw_mode ++ [0])) as [[n m0]|] eqn:Ereq;
      unfold byte in Ereq; congruence.
  - destruct (length payload <=? 512) eqn:E; [reflexivity|].
    apply Nat.leb_gt in E. lia.
  - reflexivity.
  - rewrite take_zero_complete by exact (proj2 H1). reflexivity.
Qed.

Theorem parse_exact : forall bs p,
  parse bs = Some p <-> wire_packet bs p.
Proof. split; [apply parse_sound|apply parse_complete]. Qed.

Lemma encoded_parts_ok : forall n,
  word_ok n -> byte_ok (n / 256) /\ byte_ok (n mod 256).
Proof.
  intros n H. pose proof (encode_u16_bytes_ok n H) as Hb.
  unfold encode_u16, bytes_ok in Hb.
  inversion Hb as [|? ? Hhi Htail]; subst.
  inversion Htail as [|? ? Hlo _]; subst. auto.
Qed.

Theorem encode_spec : forall p,
  valid_packet p -> wire_packet (encode p) p.
Proof.
  intros p Hvalid. destruct p; simpl in *.
  - apply (WireRRQ filename (mode_name transfer_mode) transfer_mode).
    + exact Hvalid.
    + apply mode_name_bytes_ok.
    + apply mode_name_lower.
  - apply (WireWRQ filename (mode_name transfer_mode) transfer_mode).
    + exact Hvalid.
    + apply mode_name_bytes_ok.
    + apply mode_name_lower.
  - destruct Hvalid as [Hblock [Hpayload Hlen]].
    destruct (encoded_parts_ok block Hblock) as [Hhi Hlo].
    change (wire_packet ([0; 3; block / 256; block mod 256] ++ payload)
      (DATA block payload)).
    replace (DATA block payload) with
      (DATA (decode_u16 (block / 256) (block mod 256)) payload)
      by (rewrite decode_encode_u16; reflexivity).
    now apply WireDATA.
  - destruct (encoded_parts_ok block Hvalid) as [Hhi Hlo].
    change (wire_packet [0; 4; block / 256; block mod 256] (ACK block)).
    replace (ACK block) with
      (ACK (decode_u16 (block / 256) (block mod 256)))
      by (rewrite decode_encode_u16; reflexivity).
    now apply WireACK.
  - destruct Hvalid as [Hcode Hmessage].
    destruct (encoded_parts_ok code Hcode) as [Hhi Hlo].
    change (wire_packet ([0; 5; code / 256; code mod 256] ++ message ++ [0])
      (ERROR code message)).
    replace (ERROR code message) with
      (ERROR (decode_u16 (code / 256) (code mod 256)) message)
      by (rewrite decode_encode_u16; reflexivity).
    now apply WireERROR.
Qed.

Theorem parse_encode : forall p,
  valid_packet p -> parse (encode p) = Some p.
Proof. intros p H; apply parse_complete, encode_spec, H. Qed.

Theorem parsed_data_bounded : forall bs block payload,
  parse bs = Some (DATA block payload) -> length payload <= 512.
Proof.
  intros bs block payload H.
  apply parse_sound in H. apply wire_packet_valid in H.
  simpl in H. tauto.
Qed.

Example reject_empty : parse [] = None.
Proof. reflexivity. Qed.

Example reject_bad_opcode : parse [0; 9] = None.
Proof. reflexivity. Qed.

Example reject_truncated_ack : parse [0; 4; 0] = None.
Proof. reflexivity. Qed.

Example reject_trailing_ack : parse [0; 4; 0; 1; 255] = None.
Proof. reflexivity. Qed.

Example reject_unterminated_request :
  parse ([0; 1] ++ [102; 111; 111; 0] ++ mode_name Octet) = None.
Proof. reflexivity. Qed.

Example reject_empty_filename :
  parse ([0; 1; 0] ++ mode_name Octet ++ [0]) = None.
Proof. reflexivity. Qed.

Example reject_unterminated_error :
  parse [0; 5; 0; 1; 102; 111; 111] = None.
Proof. reflexivity. Qed.

Example reject_out_of_range_byte : parse [0; 4; 256; 0] = None.
Proof. reflexivity. Qed.

Example reject_oversized_data :
  parse ([0; 3; 0; 1] ++ repeat 42 513) = None.
Proof. vm_compute. reflexivity. Qed.

Example accept_uppercase_mode :
  parse [0; 1; 102; 111; 111; 0; 79; 67; 84; 69; 84; 0] =
  Some (RRQ [102; 111; 111] Octet).
Proof. reflexivity. Qed.
