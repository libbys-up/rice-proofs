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
(* STATUS (updated after a second work session):                         *)
(*                                                                        *)
(* DONE, VERIFIED (compiles clean):                                      *)
(*   1a. Bijection-extension core: transpose, mutual_inverse, and         *)
(*       mutual_inverse_extend (extend a mutual-inverse pair by ONE       *)
(*       fresh pair (a,b), both CURRENTLY fixed points, while preserving  *)
(*       mutual-inverse-ness elsewhere -- a genuine two-point SWAP, not   *)
(*       a one-sided redirect; the first cut at this silently broke       *)
(*       injectivity, caught only via a concrete counterexample: a=5,     *)
(*       b=7, sigma=tau=identity, ext_tau(ext_sigma 7) came out 5, not 7).*)
(*   1b. nheap_rename (pointwise: nheap_rename sigma tau G w :=           *)
(*       option_map (rename_b sigma) (G (tau w))), its hupd/hupd_list     *)
(*       commutation lemmas, and rename_b/rename_e0 COMPOSITION           *)
(*       (rename_b sigma1 (rename_b sigma2 b) = rename_b (sigma1.sigma2)  *)
(*       b) -- the latter needed strong induction on blk_size, mirroring  *)
(*       curry.v's own NoBareChoiceB_rename_bound pattern (Blk's own      *)
(*       auto-generated induction principle doesn't give a usable IH for  *)
(*       branch bodies nested inside BCase's brs list).                  *)
(*                                                                        *)
(* NOT DONE -- and (2) below turned out to be its own substantial,        *)
(* separate sub-problem, not a quick iteration of (1a):                  *)
(*   2. A 'batch-extend by a finite list of pairs' lemma -- NL_Fun and    *)
(*      NL_Guess each introduce a WHOLE renaming/list at once, and        *)
(*      CRUCIALLY the two independently-chosen renamings' fresh-name      *)
(*      IMAGES CAN OVERLAP WITH EACH OTHER (nothing rules this out: each  *)
(*      is only required to avoid the ORIGINAL heap's domain, not the     *)
(*      other side's picks) -- so a_i = s(y_i) can coincide with an       *)
(*      EARLIER pair's b_j = s2(y_j) for j<i.  Tried two approaches, both *)
(*      failed on a concrete check: (i) iterating mutual_inverse_extend    *)
(*      pair-by-pair fails outright since its OWN precondition ("both     *)
(*      points currently fixed") can be false by the time we reach pair   *)
(*      i.  (ii) a 'CONS a new pair onto the front, shadowing lookup'      *)
(*      list-of-pairs construction looked promising by hand-trace, but a  *)
(*      concrete numeric check (same style as (1a)'s counterexample)      *)
(*      showed it silently reduces to the SAME single-pair bug from (1a)  *)
(*      when tried with only one pair -- meaning what's actually needed   *)
(*      is a genuine finite-permutation/cycle-decomposition argument      *)
(*      ('any bijection between two finite subsets A,B extends to a       *)
(*      permutation of A union B'), not a straightforward extension of    *)
(*      what's already built here.  UNSTARTED.                           *)
(*   3. THE MAIN PIECE: a two-sided simultaneous induction over all 11    *)
(*      NEval_left rules ('if two independently-derived evaluations of   *)
(*      alpha-related expressions from alpha-related heaps agree on      *)
(*      their guard/heap correspondence, their results stay alpha-       *)
(*      related') -- 8 of 11 rules just thread the current (sigma,tau)   *)
(*      through unchanged; NL_Fun/NL_Let/NL_Guess need (2).  UNSTARTED,   *)
(*      and likely to hide further surprises of its own, going by how    *)
(*      much iteration (1) and (2) each needed.                          *)
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

(* ==================================================================== *)
(* PIECE 1: heap_rename, and its interaction with rename_b/rename_e0/    *)
(* hupd/hupd_list.                                                        *)
(* ==================================================================== *)

Definition heap_rename {A} (rn : ren) (tau : ren) (G : heap A) (renA : ren -> A -> A) : heap A :=
  fun w => option_map (renA rn) (G (tau w)).

(* Specialized to NHeap = heap Blk, using rename_b as the value-renamer. *)
Definition nheap_rename (sigma tau : ren) (G : NHeap) : NHeap :=
  fun w => option_map (rename_b sigma) (G (tau w)).

Lemma nheap_rename_at :
  forall sigma tau, mutual_inverse sigma tau ->
  forall G z, nheap_rename sigma tau G (sigma z) = option_map (rename_b sigma) (G z).
Proof.
  intros sigma tau [Hst Hts] G z. unfold nheap_rename. rewrite Hst. reflexivity.
Qed.

Lemma nheap_rename_hupd :
  forall sigma tau, mutual_inverse sigma tau ->
  forall G x v, forall w,
  nheap_rename sigma tau (hupd G x v) w = hupd (nheap_rename sigma tau G) (sigma x) (rename_b sigma v) w.
Proof.
  intros sigma tau Hmi G x v w. destruct Hmi as [Hst Hts].
  unfold nheap_rename, hupd.
  destruct (Nat.eqb (tau w) x) eqn:Etw.
  - apply Nat.eqb_eq in Etw.
    assert (Hwsx : w = sigma x) by (rewrite <- (Hts w), Etw; reflexivity).
    rewrite Hwsx. rewrite Nat.eqb_refl. reflexivity.
  - apply Nat.eqb_neq in Etw.
    destruct (Nat.eqb w (sigma x)) eqn:Ewsx.
    + apply Nat.eqb_eq in Ewsx. subst w.
      exfalso. apply Etw. rewrite Hst. reflexivity.
    + reflexivity.
Qed.

Lemma nheap_rename_hupd_list :
  forall sigma tau, mutual_inverse sigma tau ->
  forall xs vs G, forall w,
  nheap_rename sigma tau (hupd_list G xs vs) w
    = hupd_list (nheap_rename sigma tau G) (map sigma xs) (map (rename_b sigma) vs) w.
Proof.
  intros sigma tau Hmi xs.
  induction xs as [| x xs' IH]; intros vs G w.
  - destruct vs as [| v vs']; reflexivity.
  - destruct vs as [| v vs'].
    + reflexivity.
    + cbn [hupd_list map].
      rewrite (nheap_rename_hupd sigma tau Hmi (hupd_list G xs' vs') x v w).
      unfold hupd. destruct (Nat.eqb w (sigma x)); [reflexivity | exact (IH vs' G w)].
Qed.

(* rename_b/rename_e0 compose cleanly (both are just structural pushes of a
   ren through the syntax, so composing two renamings is the same as
   applying their pointwise composition once). *)
Lemma rename_e0_comp :
  forall sigma1 sigma2 e, rename_e0 sigma1 (rename_e0 sigma2 e) = rename_e0 (fun w => sigma1 (sigma2 w)) e.
Proof.
  intros sigma1 sigma2 e. destruct e; simpl; try reflexivity.
  - rewrite map_map. reflexivity.
  - rewrite map_map. reflexivity.
Qed.

(* Blk's auto-generated induction principle doesn't give a usable IH for
   branch bodies nested inside brs (BCase's own list argument) -- mirror
   curry.v's own NoBareChoiceB_rename_bound pattern: strong induction on
   blk_size instead. *)
Lemma rename_b_comp_bound :
  forall n b, blk_size b < n ->
  forall sigma1 sigma2, rename_b sigma1 (rename_b sigma2 b) = rename_b (fun w => sigma1 (sigma2 w)) b.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize sigma1 sigma2.
  destruct b as [x e k | x brs | e].
  - simpl in *.
    assert (Hn : blk_size k + 1 < n) by lia.
    assert (Hm : blk_size k < blk_size k + 1) by lia.
    rewrite (IHn (blk_size k + 1) Hn k Hm sigma1 sigma2), rename_e0_comp. reflexivity.
  - simpl in *. f_equal.
    induction brs as [| [[c ps] bd] brs' IHbrs].
    + reflexivity.
    + simpl in Hsize |- *.
      assert (Hbd : blk_size bd + 1 < n) by lia.
      assert (Hm : blk_size bd < blk_size bd + 1) by lia.
      assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_,_,bd0) => bd0 end) + acc) 0 brs') < n)
        by lia.
      rewrite map_map. f_equal.
      * f_equal. exact (IHn (blk_size bd + 1) Hbd bd Hm sigma1 sigma2).
      * exact (IHbrs Hrest).
  - simpl. rewrite rename_e0_comp. reflexivity.
Qed.

Lemma rename_b_comp :
  forall sigma1 sigma2 b, rename_b sigma1 (rename_b sigma2 b) = rename_b (fun w => sigma1 (sigma2 w)) b.
Proof.
  intros sigma1 sigma2 b.
  exact (rename_b_comp_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) sigma1 sigma2).
Qed.
