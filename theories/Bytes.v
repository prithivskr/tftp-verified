From Stdlib Require Import Lists.List Arith.Arith micromega.Lia Bool.Bool.
Import ListNotations.

(* Naturals make received bytes easy to inspect. The parser rejects values >= 256. *)
Definition byte := nat.
Definition word16 := nat.
Definition byte_ok (b : byte) : Prop := b < 256.
Definition bytes_ok (bs : list byte) : Prop := Forall byte_ok bs.
Definition word_ok (n : word16) : Prop := n < 256 * 256.

Definition byte_okb (b : byte) : bool := b <? 256.
Definition bytes_okb (bs : list byte) : bool := forallb byte_okb bs.

Lemma bytes_okb_spec : forall bs, bytes_okb bs = true <-> bytes_ok bs.
Proof.
  induction bs as [|b bs IH]; simpl.
  - split; constructor.
  - rewrite andb_true_iff, IH. unfold byte_okb, byte_ok.
    rewrite Nat.ltb_lt. split.
    + intros [Hb Hbs]. constructor; assumption.
    + intros H. inversion H; subst. auto.
Qed.

Definition encode_u16 (n : word16) : list byte := [n / 256; n mod 256].
Definition decode_u16 (hi lo : byte) : word16 := 256 * hi + lo.

Lemma decode_encode_u16 : forall n, decode_u16 (n / 256) (n mod 256) = n.
Proof.
  intros n. unfold decode_u16.
  pose proof (Nat.div_mod n 256 ltac:(lia)). lia.
Qed.

Lemma encode_u16_bytes_ok : forall n, word_ok n -> bytes_ok (encode_u16 n).
Proof.
  intros n Hn. unfold word_ok in Hn.
  unfold encode_u16, bytes_ok, byte_ok.
  pose proof (Nat.div_mod n 256 ltac:(lia)).
  pose proof (Nat.mod_upper_bound n 256 ltac:(lia)).
  constructor.
  - lia.
  - constructor; [lia|constructor].
Qed.

Lemma decode_u16_word_ok : forall hi lo,
  byte_ok hi -> byte_ok lo -> word_ok (decode_u16 hi lo).
Proof. unfold byte_ok, word_ok, decode_u16; lia. Qed.

Fixpoint take_zero (bs : list byte) : option (list byte * list byte) :=
  match bs with
  | [] => None
  | 0 :: rest => Some ([], rest)
  | b :: rest =>
      match take_zero rest with
      | Some (before, after) => Some (b :: before, after)
      | None => None
      end
  end.

Lemma take_zero_sound : forall bs before after,
  take_zero bs = Some (before, after) ->
  bs = before ++ 0 :: after /\ ~ In 0 before.
Proof.
  induction bs as [|b bs IH]; intros before after H; simpl in H; try discriminate.
  destruct b as [|b].
  - inversion H; subst; simpl; tauto.
  - destruct (take_zero bs) as [[prefix suffix]|] eqn:E; try discriminate.
    destruct (IH prefix suffix eq_refl) as [HE Hnot].
    inversion H; subst before after; clear H.
    split; simpl; [now rewrite HE|]. intros [Hz|Hz]; [lia|auto].
Qed.

Lemma take_zero_complete : forall before after,
  ~ In 0 before -> take_zero (before ++ 0 :: after) = Some (before, after).
Proof.
  induction before as [|b before IH]; intros after H; simpl.
  - reflexivity.
  - assert (b <> 0 /\ ~ In 0 before) as [Hb Hbefore].
    { split; intro K; apply H; simpl; auto. }
    destruct b as [|b]; [contradiction|].
    rewrite IH by exact Hbefore. reflexivity.
Qed.

Definition ascii_lower (b : byte) : byte :=
  if (65 <=? b) && (b <=? 90) then b + 32 else b.

Lemma ascii_lower_byte_ok : forall b, byte_ok b -> byte_ok (ascii_lower b).
Proof.
  intros b Hb. unfold ascii_lower, byte_ok in *.
  destruct ((65 <=? b) && (b <=? 90)) eqn:E; [|lia].
  apply andb_true_iff in E as [_ E]. apply Nat.leb_le in E. lia.
Qed.
