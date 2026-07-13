From Stdlib Require Import Lists.List Arith.Arith Bool.Bool.
From Tftp Require Import Bytes Packet.
Import ListNotations.

Definition encode (p : packet) : list byte :=
  match p with
  | RRQ name m => [0; 1] ++ name ++ [0] ++ mode_name m ++ [0]
  | WRQ name m => [0; 2] ++ name ++ [0] ++ mode_name m ++ [0]
  | DATA block payload => [0; 3] ++ encode_u16 block ++ payload
  | ACK block => [0; 4] ++ encode_u16 block
  | ERROR code message => [0; 5] ++ encode_u16 code ++ message ++ [0]
  end.

Definition decode_mode (raw : list byte) : option mode :=
  if list_eq_dec Nat.eq_dec (map ascii_lower raw) (mode_name Netascii)
  then Some Netascii
  else if list_eq_dec Nat.eq_dec (map ascii_lower raw) (mode_name Octet)
       then Some Octet else None.

Definition parse_request (rest : list byte) : option (list byte * mode) :=
  match take_zero rest with
  | Some (name, tail) =>
      if Nat.eqb (length name) 0 then None else
      match take_zero tail with
      | Some (raw_mode, []) =>
          match decode_mode raw_mode with
          | Some m => Some (name, m)
          | None => None
          end
      | _ => None
      end
  | None => None
  end.

Definition parse (bs : list byte) : option packet :=
  if bytes_okb bs then
    match bs with
    | 0 :: 1 :: rest =>
        match parse_request rest with
        | Some (name, m) => Some (RRQ name m)
        | None => None
        end
    | 0 :: 2 :: rest =>
        match parse_request rest with
        | Some (name, m) => Some (WRQ name m)
        | None => None
        end
    | 0 :: 3 :: hi :: lo :: payload =>
        if length payload <=? 512
        then Some (DATA (decode_u16 hi lo) payload)
        else None
    | [0; 4; hi; lo] => Some (ACK (decode_u16 hi lo))
    | 0 :: 5 :: hi :: lo :: rest =>
        match take_zero rest with
        | Some (message, []) => Some (ERROR (decode_u16 hi lo) message)
        | _ => None
        end
    | _ => None
    end
  else None.
