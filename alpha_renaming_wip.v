Require Import List Arith Lia.
Import ListNotations.
Require Import curry.

(* ==================================================================== *)
(* WIP, NOT YET INTEGRATED: foundational pieces for an alpha-renaming-  *)
(* invariance lemma for NEval_left, aimed at closing theorem2's last     *)
(* admit (curry_test_leftmost.v:8356, G_CaseFun's second conjunct -- see *)
(* THEOREM2_PROCESS_NOTES.md section 18/19 for the full diagnosis of why *)
(* that admit needs this).  Deliberately kept as a standalone file       *)
(* (rather than spliced into curry_test_leftmost.v) since none of this   *)
(* is wired into the real proof yet.                                     *)
(*                                                                        *)
(* STATUS: only the bijection-extension core below is done and verified  *)
(* (compiles clean).  Still needed, in order, before this closes the     *)
(* admit -- none of it started:                                          *)
(*   1. heap_rename (pointwise: heap_rename sigma tau G w :=              *)
(*      option_map (rename_b sigma) (G (tau w))) plus its interaction    *)
(*      with rename_b/hupd/hupd_list (composition/pushforward lemmas).   *)
(*   2. A 'batch-extend by a finite list of pairs' lemma -- NL_Fun and    *)
(*      NL_Guess each introduce a WHOLE renaming/list at once (not one   *)
(*      variable at a time), so mutual_inverse_extend below needs to be   *)
(*      applied N times in a row, matched positionally against a         *)
(*      computed free_vars_b of the function body / case branch.         *)
(*   3. THE MAIN PIECE: a two-sided simultaneous induction over all 11    *)
(*      NEval_left rules ('if two independently-derived evaluations of   *)
(*      alpha-related expressions from alpha-related heaps agree on      *)
(*      their guard/heap correspondence, their results stay alpha-       *)
(*      related') -- 8 of 11 rules just thread the current (sigma,tau)   *)
(*      through unchanged; NL_Fun/NL_Let/NL_Guess need the extension      *)
(*      from (2).  This is the piece most likely to hide further         *)
(*      surprises, going by how much iteration the small piece below     *)
(*      needed (including a genuine bug: the first cut at 'redirect one   *)
(*      point' silently broke injectivity, caught only via a concrete     *)
(*      counterexample -- a=5,b=7,sigma=tau=identity, ext_tau(ext_sigma   *)
(*      7) came out 5, not 7).                                            *)
(*   4. Wiring the finished lemma into theorem2's G_CaseFun second        *)
(*      conjunct (curry_test_leftmost.v:8350-8356), replacing the admit.  *)
(*                                                                        *)
(* Using Nat.eq_dec (sumbool) throughout instead of Nat.eqb -- much      *)
(* cleaner to case-split and rewrite with than bool+eqb_eq round-trips.  *)
(* ==================================================================== *)

Definition transpose (a b : var) : ren :=
  fun w => if Nat.eq_dec w a then b else if Nat.eq_dec w b then a else w.

Lemma transpose_involutive : forall a b w, transpose a b (transpose a b w) = w.
Proof.
  intros a b w. unfold transpose.
  destruct (Nat.eq_dec w a) as [Hwa | Hwa].
  - subst w. destruct (Nat.eq_dec b a) as [Hba | Hba].
    + subst b. destruct (Nat.eq_dec a a) as [Haa | Haa]; [reflexivity | congruence].
    + destruct (Nat.eq_dec b a) as [Hba' | Hba']; [congruence | ].
      destruct (Nat.eq_dec b b) as [Hbb | Hbb]; [reflexivity | congruence].
  - destruct (Nat.eq_dec w b) as [Hwb | Hwb].
    + subst w. destruct (Nat.eq_dec a a) as [Haa | Haa]; [reflexivity | congruence].
    + destruct (Nat.eq_dec w a) as [Hwa' | Hwa']; [congruence | ].
      destruct (Nat.eq_dec w b) as [Hwb' | Hwb']; [congruence | reflexivity].
Qed.

Definition mutual_inverse (sigma tau : ren) : Prop :=
  (forall w, tau (sigma w) = w) /\ (forall w, sigma (tau w) = w).

Lemma mutual_inverse_id : mutual_inverse (fun w => w) (fun w => w).
Proof. split; intro w; reflexivity. Qed.

Lemma mutual_inverse_injective_l :
  forall sigma tau, mutual_inverse sigma tau -> forall x y, sigma x = sigma y -> x = y.
Proof.
  intros sigma tau [Hst Hts] x y Heq.
  rewrite <- (Hst x), <- (Hst y), Heq. reflexivity.
Qed.

(* Extend (sigma,tau) with one fresh pair (a,b), a <> b: both must already
   be fixed points of the CURRENT bijection.  Must be a genuine SWAP at
   both a and b (not just a redirect at a) to stay a bijection -- verified
   the naive one-sided version via a concrete counterexample (a=5,b=7,
   sigma=tau=identity: ext_tau(ext_sigma 7) came out 5, not 7). *)
Definition ext_sigma (sigma : ren) (a b : var) : ren :=
  fun w => if Nat.eq_dec w a then b else if Nat.eq_dec w b then a else sigma w.
Definition ext_tau (tau : ren) (a b : var) : ren :=
  fun w => if Nat.eq_dec w a then b else if Nat.eq_dec w b then a else tau w.

Lemma ext_sigma_at_a : forall sigma a b, ext_sigma sigma a b a = b.
Proof. intros. unfold ext_sigma. destruct (Nat.eq_dec a a); [reflexivity | congruence]. Qed.

Lemma ext_sigma_at_b : forall sigma a b, a <> b -> ext_sigma sigma a b b = a.
Proof.
  intros. unfold ext_sigma. destruct (Nat.eq_dec b a); [congruence | ].
  destruct (Nat.eq_dec b b); [reflexivity | congruence].
Qed.

Lemma ext_tau_at_a : forall tau a b, ext_tau tau a b a = b.
Proof. intros. unfold ext_tau. destruct (Nat.eq_dec a a); [reflexivity | congruence]. Qed.

Lemma ext_tau_at_b : forall tau a b, a <> b -> ext_tau tau a b b = a.
Proof.
  intros. unfold ext_tau. destruct (Nat.eq_dec b a); [congruence | ].
  destruct (Nat.eq_dec b b); [reflexivity | congruence].
Qed.

Lemma ext_sigma_other :
  forall sigma a b w, w <> a -> w <> b -> ext_sigma sigma a b w = sigma w.
Proof.
  intros sigma a b w Hwa Hwb. unfold ext_sigma.
  destruct (Nat.eq_dec w a); [congruence | destruct (Nat.eq_dec w b); [congruence | reflexivity]].
Qed.

Lemma ext_tau_other :
  forall tau a b w, w <> a -> w <> b -> ext_tau tau a b w = tau w.
Proof.
  intros tau a b w Hwa Hwb. unfold ext_tau.
  destruct (Nat.eq_dec w a); [congruence | destruct (Nat.eq_dec w b); [congruence | reflexivity]].
Qed.

Lemma mutual_inverse_extend :
  forall sigma tau, mutual_inverse sigma tau ->
  forall a b, a <> b -> sigma a = a -> sigma b = b ->
  mutual_inverse (ext_sigma sigma a b) (ext_tau tau a b).
Proof.
  intros sigma tau Hmi a b Hab Hsa Hsb.
  destruct Hmi as [Hst Hts].
  assert (Hta : tau a = a) by (rewrite <- Hsa at 1; exact (Hst a)).
  assert (Htb : tau b = b) by (rewrite <- Hsb at 1; exact (Hst b)).
  split; intro w.
  - destruct (Nat.eq_dec w a) as [Hwa | Hwa].
    + subst w. rewrite ext_sigma_at_a, (ext_tau_at_b tau a b Hab). reflexivity.
    + destruct (Nat.eq_dec w b) as [Hwb | Hwb].
      * subst w. rewrite (ext_sigma_at_b sigma a b Hab), ext_tau_at_a. reflexivity.
      * rewrite (ext_sigma_other sigma a b w Hwa Hwb).
        assert (Hsw_a : sigma w <> a).
        { intro Heq. assert (Hwa' : w = a) by (rewrite <- (Hst w), Heq; exact Hta). congruence. }
        assert (Hsw_b : sigma w <> b).
        { intro Heq. assert (Hwb' : w = b) by (rewrite <- (Hst w), Heq; exact Htb). congruence. }
        rewrite (ext_tau_other tau a b (sigma w) Hsw_a Hsw_b). exact (Hst w).
  - destruct (Nat.eq_dec w a) as [Hwa | Hwa].
    + subst w. rewrite ext_tau_at_a, (ext_sigma_at_b sigma a b Hab). reflexivity.
    + destruct (Nat.eq_dec w b) as [Hwb | Hwb].
      * subst w. rewrite (ext_tau_at_b tau a b Hab), ext_sigma_at_a. reflexivity.
      * rewrite (ext_tau_other tau a b w Hwa Hwb).
        assert (Htw_a : tau w <> a).
        { intro Heq. assert (Hwa' : w = a) by (rewrite <- (Hts w), Heq; exact Hsa). congruence. }
        assert (Htw_b : tau w <> b).
        { intro Heq. assert (Hwb' : w = b) by (rewrite <- (Hts w), Heq; exact Hsb). congruence. }
        rewrite (ext_sigma_other sigma a b (tau w) Htw_a Htw_b). exact (Hts w).
Qed.
