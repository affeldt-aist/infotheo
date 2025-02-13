(* infotheo: information theory and error-correcting codes in Coq             *)
(* Copyright (C) 2020 infotheo authors, license: LGPL-2.1-or-later            *)
From mathcomp Require Import all_ssreflect ssralg poly polydiv fingroup perm.
From mathcomp Require Import finalg zmodp matrix mxalgebra mxpoly vector.
Require Import ssralg_ext hamming linearcode decoding channel_code.

(**md**************************************************************************)
(* # McEliece Cryptographic Scheme                                            *)
(*                                                                            *)
(* The McEliece cryptographic scheme can be defined for any linear code but   *)
(* is only known to be secure for Goppa codes [Engelbert 2007]. Our purpose   *)
(* here is just to define encryption and decryption and to verify that the    *)
(* latter undoes the former. We just assume bounded distance decoding.        *)
(******************************************************************************)

Import GRing.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Local Open Scope ring_scope.

Module McEliece.

(* Key Generation:
    Alice chooses a binary (n,k)-linear code C that can correct t errors
    (and for which an efficient decoding algorithm is known) *)
Section mceliece.
Variable k n' : nat.
Let n := n'.+1.
Variable Hdimlen : k <= n.
Variable CSM : 'M['F_2]_(n - k, k).
Local Notation "'H" := (Syslcode.PCM Hdimlen CSM).
Local Notation "'G" := (Syslcode.GEN Hdimlen CSM).
Let encode := Syslcode.encode Hdimlen CSM.
Let discard := @Syslcode.discard 'F_2 _ _ Hdimlen.

Variable repair : repairT 'F_2 'F_2 n.
Variable repair_img : oimg repair \subset kernel 'H.
Variable encode_discard : cancel_on (kernel 'H) encode discard.

Definition C := Syslcode.t repair_img encode_discard.
Let decode := Decoder.dec (Lcode.dec C).

Variable t : nat.

Local Open Scope ecc_scope.

Variable bdd : t.-BDD (C, repair).

(* Alice chooses
   (1) a random non-singular matrix S (the ``row scrambler'' matrix) and
   (2) a random permutation matrix P: *)
Variable S : 'M['F_2]_k.
Variable S_inv : S \in unitmx.
Variables p : 'S_n.
Definition P : 'M['F_2]_n := perm_mx p.

(* S, G (the generator matrix of the code), and P form the private key.
   \hat{G} and t form the public key. *)
Definition pubkey : 'M_(k, n) := S *m 'G *m P.

(* Encryption
   Bob's message is a vector of k bits.
   Bob chooses a random error vector of n bits with t 1's  *)
Variable msg : 'rV['F_2]_k.
Variable z : 'rV['F_2]_n.
Variable Hz : wH z = t.

(* The corresponding ciphertext is: *)
Definition cyp : 'rV_n := msg *m pubkey + z.

(* Decryption:
   Decryption consists of decoding and matrix multiplications as follows: *)
Definition cyp_hat : 'rV_n := cyp *m P^-1.

Variable msg_hat : {m | decode cyp_hat = Some m}.

Definition msg' : 'rV_k := proj1_sig msg_hat *m invmx S.

Lemma decryption_undoes_encryption : msg = msg'.
Proof.
rewrite /msg'.
destruct msg_hat as [msg_hat' Hmsg_hat] => /=.
have : decode cyp_hat = Some (msg *m S).
  have -> : cyp_hat = (msg *m S) *m 'G + (z *m P^-1).
    rewrite /cyp_hat /cyp /pubkey mulmxDl -!mulmxA mulmxV ?mulmx1 //.
    by apply: unitmx_perm.
  rewrite ffunE /=.
  have H : msg *m S *m 'G \in kernel 'H.
    move/subsetP: (Encoder.enc_img (Lcode.enc C)); apply.
    apply/imsetP; exists (msg *m S) => //.
    by rewrite ffunE.
  move: bdd => /=; rewrite /bdd /= => -> //; last first.
    by rewrite /P -perm_mxV wH_perm_mx Hz.
  move: (@encode_discard (msg *m S *m 'G) H).
  rewrite ffunE => K.
  congr Some.
  apply: (@Syslcode.encode_inj _ _ _ Hdimlen CSM).
  by rewrite ffunE /= /Syslcode.encode ffunE.
rewrite Hmsg_hat => -[] ->.
rewrite -mulmxA mulmxV ?mulmx1 //; exact S_inv.
Qed.

End mceliece.

End McEliece.
