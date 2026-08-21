Require Import List Arith Lia.
Require Import Sorting.Permutation.
Import ListNotations.
Require Import curry.
Require Import curry_test_leftmost.

(* ==================================================================== *)
(* WIP, NOT YET INTEGRATED: foundational pieces for an alpha-renaming-  *)
(* invariance lemma for NEval_left, aimed at closing theorem2's last     *)
(* admit (curry_test_leftmost.v:8356, G_CaseFun's second conjunct -- see *)
(* THEOREM2_PROCESS_NOTES.md section 18/19 for the full diagnosis of why *)
(* that admit needs this).  No longer fully standalone as of PIECE 3     *)
(* (Require Import curry_test_leftmost, for NEval_left itself) -- fine,  *)
(* piece 4 wires into curry_test_leftmost anyway.                        *)
(*                                                                        *)
(* STATUS (updated after a fifth work session -- PIECE 3 started):        *)
(*                                                                        *)
(* DONE, VERIFIED (compiles clean, ZERO admits anywhere in this file):    *)
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
(*   2a. cyc_extend: the SINGLE-LIST building block.  Realizes "rotate a  *)
(*       whole NoDup list l of CURRENTLY-FIXED points by one position" as *)
(*       a closed-form definition (cyc_sigma/cyc_tau, via list_index into *)
(*       l and its rotate1) -- proven directly, no incremental per-pair   *)
(*       swap ordering needed, because a plain SWAP is provably the WRONG *)
(*       primitive for an interior link of a chain: sigma(b)=a is right   *)
(*       for an isolated pair but wrong when b's chain continues on to    *)
(*       some c, where sigma(b) must be c.  cyc_sigma_succ/cyc_sigma_wrap *)
(*       confirm concretely: cyc_sigma l sigma (l_i) = l_{i+1} for        *)
(*       consecutive positions, and the LAST position wraps to the FIRST. *)
(*   2b. component/component_pair_realized: decomposing an arbitrary set  *)
(*       of "required pairs" ps : list (var*var) (NoDup on both fst and   *)
(*       snd projections; equivalent to two parallel lists A, B, but      *)
(*       avoids ever needing to argue they stay positionally aligned      *)
(*       under filtering) so that ONE starting vertex v0's whole          *)
(*       connected component -- however many pairs long, whether it      *)
(*       terminates in a dangling sink or closes into a cycle -- gets     *)
(*       realized at once by cyc_extend.  The real content is             *)
(*       chase_invariant: a fuel-bounded forward walk (chase) that never  *)
(*       truncates a genuine chain early, via a pigeonhole argument       *)
(*       (length ps <= fuel + length acc + 1, maintained through the      *)
(*       induction) combined with chain_no_premature_repeat (the ONLY    *)
(*       vertex a NoDup chain's own last link can legally jump back to,   *)
(*       given fwd is injective on its domain, is the chain's own first   *)
(*       vertex -- proved via NoDup_nth_error, not an ad hoc argument).   *)
(*       component_pair_realized is the payoff: for every (a,b) in ps    *)
(*       with a landed in v0's component, cyc_sigma sends a to b, via     *)
(*       cyc_sigma_succ for an interior link or cyc_sigma_wrap for the    *)
(*       component's own closing link (using chase_invariant's guarantee *)
(*       that a dangling last link is always either absent or points     *)
(*       back to v0, never to some OTHER earlier vertex).  This directly  *)
(*       resolves the two failed approaches from the prior session: (i)   *)
(*       iterating mutual_inverse_extend pair-by-pair fails outright      *)
(*       since its precondition ("both points currently fixed") can       *)
(*       already be false by the time pair i is reached, if a_i or b_i    *)
(*       collided with an earlier pair; (ii) a naive 'shadowing lookup'   *)
(*       construction silently reduces to the same bug.  Neither is a     *)
(*       concern here: cyc_sigma/cyc_tau are defined once, monolithically *)
(*       (via list_index into the WHOLE already-assembled component),     *)
(*       not built by incrementally patching in one pair at a time.      *)
(*                                                                        *)
(*   2c. batch_extend: the FULL "batch-extend by two parallel lists"      *)
(*       theorem -- given ps (NoDup fst, NoDup snd) and (sigma,tau) with   *)
(*       sigma fixed on all of ps's domain+range, produces (sigma',tau')  *)
(*       realizing EVERY pair in ps, not just one v0's own component.     *)
(*       A well-founded recursion on length ps (mirroring rename_b_comp_  *)
(*       bound's own well_founded_induction lt_wf idiom from piece 1):     *)
(*       pick v0 via pick_source, apply cyc_extend to component ps v0,    *)
(*       filter OUT every consumed pair, recurse on what's left with the  *)
(*       updated sigma.  The one thing 2b's component_pair_realized alone *)
(*       didn't give: v0 CANNOT be picked arbitrarily.  An arbitrary v0    *)
(*       risks starting the chase partway down an open path, silently     *)
(*       missing everything upstream of it -- pick_source instead prefers *)
(*       a genuine PURE SOURCE (no predecessor in ps) whenever one         *)
(*       exists; when none exists, a NoDup/cardinality argument forces    *)
(*       ps's whole remaining structure to be pure closed cycles, so an   *)
(*       arbitrary start is fine there (pick_source_all_cycle_snd_        *)
(*       subset_fst).  Either way this delivers component_backward_       *)
(*       closed: no pair's TARGET can land inside a chosen component      *)
(*       while its SOURCE stays outside it -- exactly what's needed to    *)
(*       filter safely (the recursion's sigma stays fixed on whatever's   *)
(*       left) and to know the recursive result doesn't disturb pairs     *)
(*       the current step already realized.                              *)
(*                                                                        *)
(*   3-prereqs. All three PIECE-3 prerequisites identified while checking *)
(*      batch_extend's interface are now DONE, VERIFIED (zero admits):     *)
(*      (i) vars_of_b/vars_of_e0 -- every syntactic variable POSITION       *)
(*      rename_b/rename_e0 touch (bound and free alike -- confirmed from    *)
(*      their own definitions, so no real binding/shadowing analysis is     *)
(*      needed, just a structural walk mirroring rename_b itself).  (iii)   *)
(*      rename_b_congr/rename_e0_congr -- pointwise agreement of two        *)
(*      renamings on vars_of_b b implies rename_b agrees on the whole b;    *)
(*      turns batch_extend's per-PAIR guarantee into the actual TERM        *)
(*      equality PIECE 3's IH needs.  (ii) NHeapAlpha -- the bisimulation    *)
(*      invariant relating two NHeaps across a mutual-inverse pair,         *)
(*      stated directly as pointwise equality to nheap_rename (piece 1b)    *)
(*      so ALL its hupd/hupd_list commutation lemmas carry over for free    *)
(*      (NHeapAlpha_hupd, NHeapAlpha_hupd_list); NHeapAlpha_domain confirms  *)
(*      the domain-matching fact the containment invariant needs comes      *)
(*      out of NHeapAlpha's OWN definition (option_map's None-preserving    *)
(*      behavior), no separate lemma required, exactly as hoped.            *)
(*   3. THE MAIN PIECE itself: WELL UNDER WAY -- 8 of 11 NEval_left         *)
(*      constructors fully Qed'd (VarCons, VarSelf, VarFree, VarExp,        *)
(*      ValFree, ValCon, Or, Let); 3 remain as individually-flagged admits   *)
(*      (Fun, Select, Guess).  Two real corrections to the STATEMENT itself  *)
(*      were needed before any of this went through, both found by tracing   *)
(*      cases through on paper before coding, not mid-proof:                 *)
(*      (a) the "same expression, same heap" self-confluence draft from the  *)
(*      prior session is true at the TOP level but can't serve as its own    *)
(*      induction hypothesis -- NL_Fun's two continuations are only RELATED  *)
(*      by a renaming, not literally the same expression, and once           *)
(*      expressions diverge the two derivations' HEAPS diverge too.  Fixed   *)
(*      by making the real inductive statement NEval_left_confluence         *)
(*      general (two heaps via NHeapAlpha, two expressions via               *)
(*      rename_b sigma0, an ambient (sigma0,tau0)), with                    *)
(*      NEval_left_self_confluence recovered as a one-line corollary at      *)
(*      sigma0:=tau0:=id (needing rename_b_id/NHeapAlpha_refl, both built).  *)
(*      (b) a single SHARED guard list F broke at NL_VarExp (D1's guard      *)
(*      grows to x::F, D2's to (sigma0 x)::F -- equal only if sigma0 x = x,  *)
(*      not guaranteed) -- fixed by tracking F1,F2 as RELATED (F2 = map      *)
(*      sigma0 F1) rather than shared, which also let the conclusion's       *)
(*      "sigma extends sigma0" conjunct simplify to a single clause:         *)
(*      sigma agrees with sigma0 wherever sigma0 already moved something, OR *)
(*      wherever the location was already in either heap's domain before     *)
(*      this sub-derivation (the second half is what NL_VarExp's own step    *)
(*      needs -- x staying fixed even though it's not itself a sigma0-moved  *)
(*      point, because a DEEPER NL_Fun/NL_Guess's fresh pairs are always      *)
(*      outside the CURRENT heap's domain by construction).  Confirmed the   *)
(*      deterministic cases' shape-matching machinery already exists         *)
(*      (NEval_left_evar_shape, curry_test_leftmost.v) and is directly        *)
(*      reusable.  Three small helper facts built along the way: rename_b_id *)
(*      /rename_e0_id (identity renaming is a no-op), rename_b_not_econ/     *)
(*      _not_evar/_not_efree (rename_b preserves top-level shape, needed so   *)
(*      D2's shape-inversion is forced into the same constructor as D1's at   *)
(*      NL_VarExp), let_content_rename (let_content commutes with renaming,   *)
(*      needed for NL_Let).  REMAINING: NL_Fun and NL_Guess need vars_of_b   *)
(*      body + batch_extend to reconcile the two independently-chosen        *)
(*      renamings/fresh lists, exactly as planned.  NL_Select turned out to   *)
(*      be genuinely as hard as those two, not a quick win: BCase's shape-    *)
(*      inversion is a two-way disjunction (Select vs. Guess, since           *)
(*      NL_Guess ALSO concludes on BCase), so ruling out D2 picking Guess     *)
(*      needs IH1 (on the scrutinee-forcing sub-derivation) applied FIRST --  *)
(*      see NL_Select's own in-proof comment for the exact argument.          *)
(*                                                                            *)
(*      CONTINUED (next work session): (c) a THIRD correction, found by       *)
(*      tracing NL_Fun's own case all the way through by hand before          *)
(*      coding it (same discipline as (a)/(b)) -- batch_extend's Hfix         *)
(*      precondition needs sigma0 to ALREADY fix the two independently-       *)
(*      fresh locations s(y)/s2(y), and nothing about mutual_inverse/         *)
(*      NHeapAlpha alone rules out an ADVERSARIAL sigma0 that happens to      *)
(*      move one -- fixed by adding Hcontain0/Hcontain (sigma0's support      *)
(*      must already avoid the region BOTH heaps leave undefined), threaded   *)
(*      through the theorem's own hypotheses/conclusion and re-proven for     *)
(*      all 8 already-closed cases (mostly mechanical: reuse directly, or     *)
(*      lift through one hupd via the new hupd_preserves_some).  Two new      *)
(*      reusable lemmas: NoDup_map_inj (image of a NoDup list under an        *)
(*      injective function is NoDup) and Hcontain_None_fixed (the OR-         *)
(*      contrapositive of Hcontain0/Hcontain -- EITHER heap being             *)
(*      undefined at w already forces sigma0 w = w, used once per side        *)
(*      since each fresh location is only known undefined in ITS OWN heap).   *)
(*                                                                            *)
(*      CONTINUED AGAIN (next session): (d) a FOURTH hypothesis/conjunct      *)
(*      pair added and re-threaded through all 8 closed cases plus the        *)
(*      corollary -- "F1/F2 are already inside Gam1/Gam2's own domain"        *)
(*      (HFdom1/HFdom2).  NOT true of NEval_left in general (only true        *)
(*      because every actual USE in this codebase starts F at nil and grows   *)
(*      it exclusively via NL_VarExp's own x::F), so it's an explicit         *)
(*      hypothesis, not derivable -- but cheap to thread, since guard growth   *)
(*      ONLY happens at NL_VarExp; every OTHER case either reuses it directly  *)
(*      or lifts it through one hupd.  With (c)+(d) both in place, NL_Fun's    *)
(*      ENTIRE argument now goes through in actual Rocq (not just on paper)    *)
(*      up through proving sigma (batch_extend's output) agrees with sigma0    *)
(*      on the WHOLE guard list F0 -- the exact thing (d) was added for,       *)
(*      using Hcontain0 (d)+HFdom1/HFdom2 together via a two-case split on     *)
(*      whether sigma0 fixes w (Hcontain0 handles "moved", HFdom2 handles      *)
(*      "fixed").  Stops at a FIFTH, narrower gap: applying the outer IH also  *)
(*      needs NHeapAlpha sigma tau G0 Gam2 (sigma/tau, not sigma0/tau0), and   *)
(*      batch_extend's own "outside" guarantee only covers sigma', not tau'.   *)
(*      Traced further: this ISN'T simply "add a symmetric tau' conjunct to    *)
(*      batch_extend" -- rewriting NHeapAlpha into its tau-free form still     *)
(*      needs G0's OWN STORED VALUES to never reference the fresh locations    *)
(*      s(y)/s2(y) AS VALUES (freshness so far only says they're not heap      *)
(*      KEYS) -- a "closed heap" fact (no stored value references a location   *)
(*      outside the heap's own domain), not a renaming fact.  SHARPENED (the   *)
(*      user asked, and checking confirmed): this is real and semantically     *)
(*      EXPECTED for a properly-scoped program (NL_Let, the only rule that     *)
(*      ever writes a fresh cell, stores it with content whose own free vars   *)
(*      must already be bound -- guaranteed by SOURCE well-scoping, not by     *)
(*      NL_Let's own rule, which has no premise checking it at all), but       *)
(*      checked ProgWF/NoBareFreeOrChoiceProgWF (the only two well-formedness  *)
(*      definitions in this whole codebase) and NEITHER captures it -- so a    *)
(*      genuinely NEW invariant to build: (i) a "closed heap" predicate        *)
(*      (every stored value's own variable references are themselves bound),  *)
(*      (ii) a preservation lemma that NEval_left maintains it, (iii)          *)
(*      confirming the eventual theorem2 call site starts closed.  See         *)
(*      NL_Fun's own in-proof comment for the full trace.  Matches this        *)
(*      project's own recurring pattern (see                                 *)
(*      THEOREM2_PROCESS_NOTES.md section 20's "third escalation") of a        *)
(*      gap turning out deeper than the previous diagnosis suggested -- each   *)
(*      discovery has been concrete and load-bearing, not speculative, caught  *)
(*      by tracing through on paper/by hand before writing Rocq, not mid-      *)
(*      proof, and (c)/(d) both went from "diagnosed" to "fully Qed'd and      *)
(*      threaded through 8 cases" within the SAME session they were found.     *)
(*      theorem2 itself is UNCHANGED throughout all of this: still exactly     *)
(*      one admit, curry_test_leftmost.v untouched.                          *)
(*                                                                            *)
(*      CONTINUED AGAIN (this session, "let's start there" on the ClosedHeap  *)
(*      plan): built ClosedHeap and attempted NEval_left_closed_preserved     *)
(*      (PIECE 5, right before NEval_left_confluence).  Tracing by hand       *)
(*      before coding turned up a genuine simplification: the four "heap-     *)
(*      pointer-mediated" constructors (VarCons/VarSelf/VarFree/VarExp) get   *)
(*      closedness of whatever they find "for free" from ClosedHeap G plus    *)
(*      the rule's own G x = Some e premise -- the very existence of the      *)
(*      given derivation already forces it, no separate input needed.  That,  *)
(*      plus ValFree/ValCon/Or, closed 7 of 11 cases outright and compiled     *)
(*      clean on the FIRST try.  The remaining 4 (Let/Fun/Select/Guess) all    *)
(*      "reveal brand-new syntax" (a whole Blk term pulled in from the         *)
(*      program or from e's own structure, not reached via a heap pointer)     *)
(*      and hit a SHARPER version of the same fifth gap: vars_of_b conflates   *)
(*      a term's genuinely free variables with ones a LET/CASE inside that     *)
(*      very term binds for itself (vars_of_b (BLet z EFree (EVar z)) =        *)
(*      [z;z], yet that term is closed under the EMPTY heap) -- so stating      *)
(*      correct hypotheses for these 4 cases needs an actual free-variable      *)
(*      analysis (bound-set-tracking through BLet/BCase), not just vars_of_b,   *)
(*      PLUS a well-scopedness fact about P's function/branch bodies that       *)
(*      doesn't exist anywhere in this codebase yet.  Each case's own comment   *)
(*      in the proof gives its exact stall point.  NOT YET ATTEMPTED.           *)
(*   4. Wiring the finished lemma into theorem2's G_CaseFun second        *)
(*      conjunct (curry_test_leftmost.v:8350-8356), replacing the admit.  *)
(*                                                                        *)
(* Using Nat.eq_dec (sumbool) throughout instead of Nat.eqb -- much      *)
(* cleaner to case-split and rewrite with than bool+eqb_eq round-trips.  *)
(* Recurring gotcha this session (see THEOREM2_PROCESS_NOTES.md T19/T20  *)
(* for both): List.In unfolds as `elem = query \/ ...`, NOT `query =     *)
(* elem \/ ...` -- get this backwards and eq_sym exactly cancels out the *)
(* bug, so it fails with a confusing "wrong type" error rather than an   *)
(* obviously-wrong proof term.  Also, many stdlib list lemmas (nth_error_ *)
(* app1/app2, app_nth2, Permutation_cons_append) have their INDEX/LIST    *)
(* argument marked implicit even though it looks positional in Check's   *)
(* pretty-printed output -- use About, not Check, to see the [brackets]. *)
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

(* ==================================================================== *)
(* PIECE 2a: extending a mutual-inverse pair along a WHOLE finite list   *)
(* of CURRENTLY-FIXED points at once, by treating the list as a single   *)
(* cycle and rotating it by one position.                                *)
(*                                                                        *)
(* WHY per-pair mutual_inverse_extend can't just be iterated (see        *)
(* THEOREM2_PROCESS_NOTES.md section 20): a plain SWAP (a,b) forces      *)
(* sigma(b) = a, which is right for an ISOLATED pair but wrong for an    *)
(* interior link of a longer chain a -> b -> c, where sigma(b) needs to  *)
(* be c, not a.  "Rotate the whole list by one position" is the correct  *)
(* primitive: sigma'(l_i) = l_{i+1}, wrapping the last element back to   *)
(* the first.  It has a direct closed-form definition (no incremental    *)
(* per-pair induction, no swap-ordering to get right).                   *)
(* ==================================================================== *)

Fixpoint list_index (l : list var) (w : var) : option nat :=
  match l with
  | nil => None
  | x :: l' => if Nat.eq_dec x w then Some 0 else option_map S (list_index l' w)
  end.

Lemma list_index_nth_error :
  forall l w i, list_index l w = Some i -> nth_error l i = Some w.
Proof.
  induction l as [| x l' IH]; intros w i H.
  - discriminate H.
  - simpl in H. destruct (Nat.eq_dec x w) as [Hxw | Hxw].
    + injection H as H. subst i x. reflexivity.
    + destruct (list_index l' w) as [i' | ] eqn:E; simpl in H; try discriminate H.
      injection H as H. subst i. simpl. exact (IH w i' E).
Qed.

Lemma list_index_none_not_in :
  forall l w, list_index l w = None -> ~ In w l.
Proof.
  induction l as [| x l' IH]; intros w H.
  - intro Hin; destruct Hin.
  - simpl in H. destruct (Nat.eq_dec x w) as [Hxw | Hxw]; [discriminate H | ].
    destruct (list_index l' w) as [i' | ] eqn:E; simpl in H; try discriminate H.
    intro Hin. destruct Hin as [Hin | Hin]; [congruence | exact (IH w E Hin)].
Qed.

Lemma list_index_nodup_complete :
  forall l, NoDup l -> forall i w, nth_error l i = Some w -> list_index l w = Some i.
Proof.
  induction l as [| x l' IH]; intros HND i w H.
  - destruct i; discriminate H.
  - inversion HND as [| ? ? Hxnin HND']; subst.
    destruct i as [| i'].
    + simpl in H. injection H as H. subst w. simpl.
      destruct (Nat.eq_dec x x); [reflexivity | congruence].
    + simpl in H. simpl.
      destruct (Nat.eq_dec x w) as [Hxw | Hxw].
      * subst w. exfalso. apply Hxnin. eapply nth_error_In. exact H.
      * rewrite (IH HND' i' w H). reflexivity.
Qed.

(* Rotate a list by one position: head moves to the tail. *)
Definition rotate1 (l : list var) : list var :=
  match l with
  | nil => nil
  | x :: l' => l' ++ (x :: nil)
  end.

Lemma rotate1_perm : forall l, Permutation l (rotate1 l).
Proof.
  destruct l as [| x l']; simpl.
  - apply Permutation_refl.
  - apply Permutation_cons_append.
Qed.

Lemma rotate1_length : forall l, length (rotate1 l) = length l.
Proof. intro l. symmetry. exact (Permutation_length (rotate1_perm l)). Qed.

Lemma rotate1_nodup : forall l, NoDup l -> NoDup (rotate1 l).
Proof. intros l HND. exact (Permutation_NoDup (rotate1_perm l) HND). Qed.

(* cyc_sigma/cyc_tau: reindex through l and its rotation.  w = l[i]  |->
   (rotate1 l)[i] = l[i+1 mod length l]; everything outside l falls back
   to the ambient sigma/tau unchanged. *)
Definition cyc_sigma (l : list var) (sigma : ren) : ren :=
  fun w => match list_index l w with
           | Some i => nth i (rotate1 l) 0
           | None => sigma w
           end.

Definition cyc_tau (l : list var) (tau : ren) : ren :=
  fun w => match list_index (rotate1 l) w with
           | Some i => nth i l 0
           | None => tau w
           end.

Lemma cyc_sigma_at :
  forall l sigma w i, NoDup l -> list_index l w = Some i ->
  cyc_sigma l sigma w = nth i (rotate1 l) 0.
Proof. intros l sigma w i HND Hidx. unfold cyc_sigma. rewrite Hidx. reflexivity. Qed.

(* The key reindexing fact: if w = l[i], its cyc_sigma image v = (rotate1
   l)[i] satisfies list_index (rotate1 l) v = Some i too (NoDup carries the
   index across the rename), so cyc_tau finds its way straight back to
   l[i] = w. *)
Lemma cyc_tau_cyc_sigma :
  forall l sigma tau, mutual_inverse sigma tau -> NoDup l ->
  (forall w, In w l -> sigma w = w) ->
  forall w, cyc_tau l tau (cyc_sigma l sigma w) = w.
Proof.
  intros l sigma tau [Hst Hts] HND Hfix w.
  unfold cyc_sigma at 1. destruct (list_index l w) as [i | ] eqn:Eidx.
  - assert (Hwi : nth_error l i = Some w) by exact (list_index_nth_error l w i Eidx).
    assert (Hilt : i < length l) by (eapply nth_error_Some; congruence).
    assert (Hilt' : i < length (rotate1 l)) by (rewrite rotate1_length; exact Hilt).
    assert (Hvi : nth_error (rotate1 l) i = Some (nth i (rotate1 l) 0))
      by (apply nth_error_nth'; exact Hilt').
    assert (Hidx' : list_index (rotate1 l) (nth i (rotate1 l) 0) = Some i)
      by exact (list_index_nodup_complete (rotate1 l) (rotate1_nodup l HND) i _ Hvi).
    unfold cyc_tau. rewrite Hidx'.
    apply (nth_error_nth l i 0 Hwi).
  - unfold cyc_tau.
    assert (Hnin : ~ In w l) by exact (list_index_none_not_in l w Eidx).
    assert (Hnin' : ~ In (sigma w) l).
    { intro Hin.
      assert (Heq : sigma (sigma w) = sigma w) by exact (Hfix (sigma w) Hin).
      assert (Hw' : tau (sigma w) = sigma w) by (rewrite <- Heq at 1; exact (Hst (sigma w))).
      assert (Hw : w = sigma w) by (rewrite <- (Hst w) at 1; exact Hw').
      apply Hnin. rewrite Hw. exact Hin. }
    assert (Hnin2 : ~ In (sigma w) (rotate1 l))
      by (intro Hin; apply Hnin'; exact (Permutation_in (sigma w) (Permutation_sym (rotate1_perm l)) Hin)).
    destruct (list_index (rotate1 l) (sigma w)) as [j | ] eqn:Ej.
    + exfalso. apply Hnin2. exact (nth_error_In (rotate1 l) j (list_index_nth_error (rotate1 l) (sigma w) j Ej)).
    + exact (Hst w).
Qed.

Lemma cyc_sigma_cyc_tau :
  forall l sigma tau, mutual_inverse sigma tau -> NoDup l ->
  (forall w, In w l -> sigma w = w) ->
  forall w, cyc_sigma l sigma (cyc_tau l tau w) = w.
Proof.
  intros l sigma tau [Hst Hts] HND Hfix w.
  assert (Hfix_tau : forall w0, In w0 l -> tau w0 = w0).
  { intros w0 Hin0. assert (Hsw : sigma w0 = w0) by exact (Hfix w0 Hin0).
    rewrite <- Hsw at 1. exact (Hst w0). }
  unfold cyc_tau at 1. destruct (list_index (rotate1 l) w) as [i | ] eqn:Eidx.
  - assert (Hwi : nth_error (rotate1 l) i = Some w) by exact (list_index_nth_error (rotate1 l) w i Eidx).
    assert (Hilt : i < length (rotate1 l)) by (eapply nth_error_Some; congruence).
    assert (Hilt' : i < length l) by (rewrite <- (rotate1_length l); exact Hilt).
    assert (Hai : nth_error l i = Some (nth i l 0)) by (apply nth_error_nth'; exact Hilt').
    assert (Hidx' : list_index l (nth i l 0) = Some i)
      by exact (list_index_nodup_complete l HND i _ Hai).
    unfold cyc_sigma. rewrite Hidx'.
    apply (nth_error_nth (rotate1 l) i 0 Hwi).
  - unfold cyc_sigma.
    assert (Hnin : ~ In w (rotate1 l)) by exact (list_index_none_not_in (rotate1 l) w Eidx).
    assert (Hnin_l : ~ In w l)
      by (intro Hin; apply Hnin; exact (Permutation_in w (rotate1_perm l) Hin)).
    assert (Hnin' : ~ In (tau w) l).
    { intro Hin.
      assert (Heq : tau (tau w) = tau w) by exact (Hfix_tau (tau w) Hin).
      assert (Hw' : sigma (tau w) = tau w) by (rewrite <- Heq at 1; exact (Hts (tau w))).
      assert (Hw : w = tau w) by (rewrite <- (Hts w) at 1; exact Hw').
      apply Hnin_l. rewrite Hw. exact Hin. }
    destruct (list_index l (tau w)) as [j | ] eqn:Ej.
    + exfalso. apply Hnin'. exact (nth_error_In l j (list_index_nth_error l (tau w) j Ej)).
    + exact (Hts w).
Qed.

(* PIECE 2a's actual deliverable: extending a mutual-inverse pair along a
   WHOLE list of currently-fixed points at once, no per-pair swap ordering
   to get right -- the single-component building block for the general
   batch-extend lemma (PIECE 2b, not yet attempted: decomposing an
   arbitrary pair of parallel lists A, B into a list of such components,
   preferring an element with no predecessor as each component's start
   when one exists, falling back to an arbitrary start once only closed
   cycles remain among the leftover pairs). *)
Theorem cyc_extend :
  forall l sigma tau, mutual_inverse sigma tau -> NoDup l ->
  (forall w, In w l -> sigma w = w) ->
  mutual_inverse (cyc_sigma l sigma) (cyc_tau l tau).
Proof.
  intros l sigma tau Hmi HND Hfix. split.
  - exact (cyc_tau_cyc_sigma l sigma tau Hmi HND Hfix).
  - exact (cyc_sigma_cyc_tau l sigma tau Hmi HND Hfix).
Qed.

(* Sanity check that cyc_extend actually delivers the pairing it's meant
   to: consecutive elements of l really do get chained by cyc_sigma. *)
Corollary cyc_sigma_succ :
  forall l sigma i, NoDup l -> S i < length l ->
  cyc_sigma l sigma (nth i l 0) = nth (S i) l 0.
Proof.
  intros l sigma i HND Hlt.
  assert (Hi : nth_error l i = Some (nth i l 0)) by (apply nth_error_nth'; lia).
  assert (Hidx : list_index l (nth i l 0) = Some i) by exact (list_index_nodup_complete l HND i _ Hi).
  unfold cyc_sigma. rewrite Hidx.
  destruct l as [| x l'].
  - simpl in Hlt. lia.
  - simpl. apply app_nth1. simpl in Hlt. lia.
Qed.

(* The mirror-image fact: the LAST element of l wraps back to the FIRST. *)
Lemma cyc_sigma_wrap :
  forall l sigma, NoDup l -> l <> nil ->
  cyc_sigma l sigma (nth (length l - 1) l 0) = hd 0 l.
Proof.
  intros l sigma HND Hnnil.
  destruct l as [| x l']; [congruence | ].
  assert (Hsub : length (x :: l') - 1 = length l') by (simpl; lia).
  rewrite Hsub.
  assert (Hlt : length l' < length (x :: l')) by (simpl; lia).
  assert (Hidx0 : nth_error (x :: l') (length l') = Some (nth (length l') (x :: l') 0))
    by (apply nth_error_nth'; exact Hlt).
  assert (Hidx : list_index (x :: l') (nth (length l') (x :: l') 0) = Some (length l'))
    by exact (list_index_nodup_complete (x :: l') HND (length l') _ Hidx0).
  unfold cyc_sigma. rewrite Hidx. simpl.
  rewrite (app_nth2 l' [x] 0 (Nat.le_refl (length l'))).
  rewrite Nat.sub_diag. reflexivity.
Qed.

(* ==================================================================== *)
(* PIECE 2b: decomposing an arbitrary set of "required pairs" into        *)
(* components ready for cyc_extend.                                      *)
(*                                                                        *)
(* Represent the required pairs as a single list ps : list (var*var)      *)
(* (equivalent to two parallel lists A B, but avoids ever needing to       *)
(* argue the two lists stay positionally aligned under filtering).        *)
(* ==================================================================== *)

Fixpoint fwd (ps : list (var * var)) (w : var) : option var :=
  match ps with
  | nil => None
  | (a, b) :: ps' => if Nat.eq_dec a w then Some b else fwd ps' w
  end.

Lemma fwd_in : forall ps w b, fwd ps w = Some b -> In (w, b) ps.
Proof.
  induction ps as [| [a b'] ps' IH]; intros w b H.
  - discriminate H.
  - simpl in H. destruct (Nat.eq_dec a w) as [Haw | Haw].
    + injection H as H. subst a b'. left. reflexivity.
    + right. exact (IH w b H).
Qed.

Lemma fwd_complete :
  forall ps : list (var * var), NoDup (map fst ps) -> forall a b, In (a, b) ps -> fwd ps a = Some b.
Proof.
  induction ps as [| [a' b'] ps' IH]; intros HND a b Hin.
  - destruct Hin.
  - simpl in HND. inversion HND as [| ? ? Hnin HND']; subst.
    simpl in Hin. simpl. destruct (Nat.eq_dec a' a) as [Haa | Haa].
    + subst a'. destruct Hin as [Hin | Hin].
      * injection Hin as Hin. subst b'. reflexivity.
      * exfalso. apply Hnin. exact (in_map fst ps' (a, b) Hin).
    + destruct Hin as [Hin | Hin]; [ | exact (IH HND' a b Hin)].
      injection Hin as Hin1 Hin2. congruence.
Qed.

Lemma pair_snd_nodup_fst_unique :
  forall ps : list (var * var), NoDup (map snd ps) -> forall a1 a2 b, In (a1, b) ps -> In (a2, b) ps -> a1 = a2.
Proof.
  induction ps as [| [a b'] ps' IH]; intros HND a1 a2 b Hin1 Hin2.
  - destruct Hin1.
  - simpl in HND. inversion HND as [| ? ? Hnin HND']; subst.
    simpl in Hin1, Hin2.
    destruct Hin1 as [Hin1 | Hin1]; destruct Hin2 as [Hin2 | Hin2].
    + injection Hin1 as Hin1a Hin1b; injection Hin2 as Hin2a Hin2b; subst. reflexivity.
    + injection Hin1 as Hin1a Hin1b; subst a b'.
      exfalso. apply Hnin. exact (in_map snd ps' (a2, b) Hin2).
    + injection Hin2 as Hin2a Hin2b; subst a b'.
      exfalso. apply Hnin. exact (in_map snd ps' (a1, b) Hin1).
    + exact (IH HND' a1 a2 b Hin1 Hin2).
Qed.

Lemma fwd_injective :
  forall ps : list (var * var), NoDup (map snd ps) -> forall a1 a2 b, fwd ps a1 = Some b -> fwd ps a2 = Some b -> a1 = a2.
Proof.
  intros ps HND a1 a2 b H1 H2.
  exact (pair_snd_nodup_fst_unique ps HND a1 a2 b (fwd_in ps a1 b H1) (fwd_in ps a2 b H2)).
Qed.

(* A list l "is a chain" if every consecutive pair is linked by fwd. *)
Definition is_chain (ps : list (var * var)) (l : list var) : Prop :=
  forall i x y, nth_error l i = Some x -> nth_error l (S i) = Some y -> fwd ps x = Some y.

Lemma is_chain_snoc :
  forall ps l x v, is_chain ps l -> l <> nil -> nth_error l (length l - 1) = Some x ->
  fwd ps x = Some v -> is_chain ps (l ++ [v]).
Proof.
  intros ps l x v Hchain Hnnil Hlast Hfwd i a b Ha Hb.
  destruct (Nat.lt_ge_cases i (length l - 1)) as [Hi | Hi].
  - assert (Hi1 : i < length l) by lia.
    assert (Hi2 : S i < length l) by lia.
    rewrite (nth_error_app1 l [v] Hi1) in Ha.
    rewrite (nth_error_app1 l [v] Hi2) in Hb.
    exact (Hchain i a b Ha Hb).
  - assert (Hib : i < length l).
    { assert (Hb' : S i < length (l ++ [v])) by (eapply nth_error_Some; congruence).
      rewrite app_length in Hb'. simpl in Hb'. lia. }
    assert (Heq : i = length l - 1) by lia. subst i.
    assert (Hi1 : length l - 1 < length l) by lia.
    rewrite (nth_error_app1 l [v] Hi1) in Ha.
    assert (Ha2 : a = x) by congruence.
    assert (Hi2 : length l <= S (length l - 1)) by lia.
    rewrite (nth_error_app2 l [v] Hi2) in Hb.
    assert (Hsub : S (length l - 1) - length l = 0) by lia.
    rewrite Hsub in Hb. simpl in Hb.
    assert (Hb2 : b = v) by congruence.
    subst a b. exact Hfwd.
Qed.

(* The core combinatorial fact: within a NoDup chain, the ONLY vertex that
   the chain's own last link can legally jump back to (without violating
   NoDup, given fwd is injective on its domain) is the chain's own first
   vertex.  This is what makes "rotate the whole component" well-defined:
   it rules out a chain silently re-merging into itself partway through. *)
Lemma chain_no_premature_repeat :
  forall ps : list (var * var), NoDup (map snd ps) ->
  forall l, is_chain ps l -> NoDup l -> l <> nil ->
  forall cur nxt, nth_error l (length l - 1) = Some cur ->
  fwd ps cur = Some nxt -> In nxt l -> nth_error l 0 = Some nxt.
Proof.
  intros ps HNDsnd l Hchain HNDl Hnnil cur nxt Hlast Hfwd Hin.
  destruct (In_nth_error l nxt Hin) as [j Hj].
  destruct j as [| j'].
  - exact Hj.
  - exfalso.
    assert (Hjlt : S j' < length l) by (eapply nth_error_Some; congruence).
    assert (Hj'lt : j' < length l) by lia.
    destruct (nth_error l j') as [x | ] eqn:Ex.
    2: { exfalso. apply (nth_error_Some l j'); [lia | exact Ex]. }
    assert (Hxnxt : fwd ps x = Some nxt) by exact (Hchain j' x nxt Ex Hj).
    assert (Hxcur : x = cur) by exact (fwd_injective ps HNDsnd x cur nxt Hxnxt Hfwd).
    subst x.
    assert (Heqopt : nth_error l j' = nth_error l (length l - 1)) by congruence.
    assert (Heq2 : j' = length l - 1) by exact (proj1 (NoDup_nth_error l) HNDl j' (length l - 1) Hj'lt Heqopt).
    lia.
Qed.

Fixpoint chase (ps : list (var * var)) (fuel : nat) (start cur : var) : list var :=
  cur :: match fuel with
         | 0 => nil
         | S fuel' =>
           match fwd ps cur with
           | None => nil
           | Some nxt => if Nat.eq_dec nxt start then nil else chase ps fuel' start nxt
           end
         end.

Lemma NoDup_snoc : forall (l : list var) (x : var), NoDup l -> ~ In x l -> NoDup (l ++ [x]).
Proof.
  intros l x HND Hnin.
  exact (Permutation_NoDup (Permutation_cons_append l x) (NoDup_cons x Hnin HND)).
Qed.

(* The main invariant, by induction on fuel: as long as there's enough
   fuel to cover however many DISTINCT sources remain unused in ps (the
   pigeonhole bound: length ps <= fuel + length acc + 1), chase never
   truncates a genuine chain early -- it only ever stops at a real sink
   (fwd = None) or by closing back to start (fwd = Some start), and the
   result stays NoDup + a valid chain throughout. *)
Lemma nth_error_last_cons :
  forall (l : list var) (x : var), l <> nil ->
  nth_error (x :: l) (length (x :: l) - 1) = nth_error l (length l - 1).
Proof.
  intros l x Hnnil. destruct l as [| y l']; [congruence | ].
  simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma chase_invariant :
  forall ps : list (var * var), NoDup (map snd ps) ->
  forall fuel start acc cur,
  NoDup (start :: acc ++ [cur]) ->
  is_chain ps (start :: acc ++ [cur]) ->
  incl (start :: acc) (map fst ps) ->
  length ps <= fuel + length acc + 1 ->
  NoDup (start :: acc ++ chase ps fuel start cur) /\
  is_chain ps (start :: acc ++ chase ps fuel start cur) /\
  (forall x, nth_error (chase ps fuel start cur) (length (chase ps fuel start cur) - 1) = Some x ->
   fwd ps x = None \/ fwd ps x = Some start).
Proof.
  intros ps HNDsnd.
  induction fuel as [| fuel' IH]; intros start acc cur HND Hchain Hincl Hlen.
  - simpl. repeat split; try assumption.
    intros x Hx. simpl in Hx. injection Hx as Hx. subst x.
    destruct (fwd ps cur) as [nxt | ] eqn:Efwd; [ | left; reflexivity].
    right. f_equal.
    destruct (Nat.eq_dec nxt start) as [Heq | Hne]; [exact Heq | ].
    exfalso.
    assert (Hcur_in : In cur (map fst ps)) by exact (in_map fst ps (cur, nxt) (fwd_in ps cur nxt Efwd)).
    assert (Hinclfull : incl (start :: acc ++ [cur]) (map fst ps)).
    { apply incl_cons; [apply Hincl; left; reflexivity | ].
      apply incl_app; [intros w Hw; apply Hincl; right; exact Hw | ].
      intros w Hw. simpl in Hw. destruct Hw as [Hw | Hw]; [subst w; exact Hcur_in | destruct Hw]. }
    assert (Hle := NoDup_incl_length HND Hinclfull).
    rewrite map_length in Hle. simpl in Hle. rewrite app_length in Hle. simpl in Hle.
    lia.
  - simpl. destruct (fwd ps cur) as [nxt | ] eqn:Efwd.
    + destruct (Nat.eq_dec nxt start) as [Heq | Hne].
      * simpl. repeat split; try assumption.
        intros x Hx. simpl in Hx. injection Hx as Hx. subst x. right. subst nxt. exact Efwd.
      * assert (Hcur_in : In cur (map fst ps)) by exact (in_map fst ps (cur, nxt) (fwd_in ps cur nxt Efwd)).
        assert (Hlast : nth_error (start :: acc ++ [cur]) (length (start :: acc ++ [cur]) - 1) = Some cur).
        { assert (Hn : length (start :: acc ++ [cur]) - 1 = S (length acc))
            by (simpl; rewrite app_length; simpl; lia).
          rewrite Hn.
          change (nth_error (start :: acc ++ [cur]) (S (length acc)))
            with (nth_error (acc ++ [cur]) (length acc)).
          rewrite (nth_error_app2 acc [cur] (Nat.le_refl (length acc))).
          rewrite Nat.sub_diag. reflexivity. }
        assert (Hnnil : start :: acc ++ [cur] <> nil) by discriminate.
        assert (HinCheck : ~ In nxt (start :: acc ++ [cur])).
        { intro Hin.
          assert (Hres := chain_no_premature_repeat ps HNDsnd (start :: acc ++ [cur]) Hchain HND Hnnil
                             cur nxt Hlast Efwd Hin).
          simpl in Hres. injection Hres as Hres. exact (Hne (eq_sym Hres)). }
        assert (HND' : NoDup (start :: (acc ++ [cur]) ++ [nxt])).
        { apply NoDup_cons.
          - intro Hin2. apply in_app_or in Hin2.
            destruct Hin2 as [Hin2 | Hin2].
            + assert (HND2 := HND). inversion HND2 as [| ? ? Hnin3 HND3]; subst.
              apply Hnin3. exact Hin2.
            + simpl in Hin2. destruct Hin2 as [Hin2 | Hin2]; [exact (Hne Hin2) | destruct Hin2].
          - apply NoDup_snoc.
            + assert (HND2 := HND). simpl in HND2. inversion HND2 as [| ? ? Hnin3 HND3]; subst. exact HND3.
            + intro Hin2. apply HinCheck. right. exact Hin2. }
        assert (Hchain' : is_chain ps (start :: (acc ++ [cur]) ++ [nxt])).
        { assert (Htmp := is_chain_snoc ps (start :: acc ++ [cur]) cur nxt Hchain Hnnil Hlast Efwd).
          intros i x y Hx Hy.
          assert (Heqlist : (start :: acc ++ [cur]) ++ [nxt] = start :: (acc ++ [cur]) ++ [nxt])
            by reflexivity.
          rewrite Heqlist in Htmp. exact (Htmp i x y Hx Hy). }
        assert (Hincl' : incl (start :: acc ++ [cur]) (map fst ps)).
        { apply incl_cons; [apply Hincl; left; reflexivity | ].
          apply incl_app; [intros w Hw; apply Hincl; right; exact Hw | ].
          intros w Hw. simpl in Hw. destruct Hw as [Hw | Hw]; [subst w; exact Hcur_in | destruct Hw]. }
        assert (Hlen' : length ps <= fuel' + length (acc ++ [cur]) + 1) by (rewrite app_length; simpl; lia).
        assert (IHres := IH start (acc ++ [cur]) nxt HND' Hchain' Hincl' Hlen').
        destruct IHres as [IHnd [IHchain IHterm]].
        rewrite <- app_assoc in IHnd. simpl in IHnd.
        rewrite <- app_assoc in IHchain. simpl in IHchain.
        assert (Hnnil2 : chase ps fuel' start nxt <> nil) by (unfold chase; destruct fuel'; discriminate).
        repeat split.
        -- exact IHnd.
        -- exact IHchain.
        -- intros x Hx.
           rewrite Nat.sub_0_r in Hx.
           assert (Heq0 : length (chase ps fuel' start nxt) = length (cur :: chase ps fuel' start nxt) - 1)
             by (simpl; lia).
           rewrite Heq0 in Hx.
           rewrite (nth_error_last_cons (chase ps fuel' start nxt) cur Hnnil2) in Hx.
           exact (IHterm x Hx).
    + simpl. repeat split; try assumption.
      intros x Hx. simpl in Hx. injection Hx as Hx. subst x. left. exact Efwd.
Qed.

Definition component (ps : list (var * var)) (v0 : var) : list var :=
  chase ps (length ps) v0 v0.

Lemma component_head : forall ps v0, nth_error (component ps v0) 0 = Some v0.
Proof. intros ps v0. unfold component, chase. destruct (length ps); reflexivity. Qed.

Lemma component_hd : forall ps v0, hd 0 (component ps v0) = v0.
Proof.
  intros ps v0. assert (H := component_head ps v0).
  destruct (component ps v0) as [| x l']; simpl in H; simpl; [discriminate H | ].
  injection H as H. exact H.
Qed.

Lemma component_invariant :
  forall ps : list (var * var), NoDup (map snd ps) -> NoDup (map fst ps) ->
  forall v0,
  NoDup (component ps v0) /\ is_chain ps (component ps v0) /\
  (forall x, nth_error (component ps v0) (length (component ps v0) - 1) = Some x ->
   fwd ps x = None \/ fwd ps x = Some v0).
Proof.
  intros ps HNDsnd HNDfst v0. unfold component.
  destruct (length ps) as [| m] eqn:Elen.
  - assert (Hnil : ps = nil) by (apply length_zero_iff_nil; exact Elen).
    subst ps. simpl. repeat split.
    + constructor; [intro Hc; destruct Hc | constructor].
    + intros i x y Hx Hy. destruct i; simpl in Hy; discriminate Hy.
    + intros x Hx. simpl in Hx. injection Hx as Hx. subst x. left. reflexivity.
  - simpl. destruct (fwd ps v0) as [nxt | ] eqn:Efwd.
    + destruct (Nat.eq_dec nxt v0) as [Heq | Hne].
      * simpl. repeat split.
        -- constructor; [intro Hc; destruct Hc | constructor].
        -- intros i x y Hx Hy. destruct i; simpl in Hy; discriminate Hy.
        -- intros x Hx. simpl in Hx. injection Hx as Hx. subst x. right. subst nxt. exact Efwd.
      * assert (Hv0in : In v0 (map fst ps)) by exact (in_map fst ps (v0, nxt) (fwd_in ps v0 nxt Efwd)).
        assert (HNDbase : NoDup (v0 :: nil ++ [nxt])).
        { simpl. apply NoDup_cons; [intro Hc; destruct Hc as [Hc | Hc]; [exact (Hne Hc) | exact Hc] | ].
          constructor; [intro Hc; destruct Hc | constructor]. }
        assert (Hchainbase : is_chain ps (v0 :: nil ++ [nxt])).
        { intros i x y Hx Hy. destruct i as [| [| i']].
          - simpl in Hx, Hy. injection Hx as Hx; injection Hy as Hy; subst x y. exact Efwd.
          - simpl in Hy. discriminate Hy.
          - simpl in Hy. discriminate Hy. }
        assert (Hinclbase : incl (v0 :: nil) (map fst ps))
          by (intros w Hw; simpl in Hw; destruct Hw as [Hw | Hw]; [subst w; exact Hv0in | destruct Hw]).
        assert (Hlenbase : length ps <= m + length (nil : list var) + 1) by (simpl; lia).
        assert (Hres := chase_invariant ps HNDsnd m v0 nil nxt HNDbase Hchainbase Hinclbase Hlenbase).
        simpl in Hres. destruct Hres as [Hnd [Hch Hterm]].
        repeat split; [exact Hnd | exact Hch | ].
        assert (Hnnil2 : chase ps m v0 nxt <> nil) by (unfold chase; destruct m; discriminate).
        intros x Hx. rewrite Nat.sub_0_r in Hx.
        assert (Heq0 : length (chase ps m v0 nxt) = length (v0 :: chase ps m v0 nxt) - 1) by (simpl; lia).
        rewrite Heq0 in Hx.
        rewrite (nth_error_last_cons (chase ps m v0 nxt) v0 Hnnil2) in Hx.
        exact (Hterm x Hx).
    + simpl. repeat split.
      * constructor; [intro Hc; destruct Hc | constructor].
      * intros i x y Hx Hy. destruct i; simpl in Hy; discriminate Hy.
      * intros x Hx. simpl in Hx. injection Hx as Hx. subst x. left. exact Efwd.
Qed.

(* PIECE 2b's actual deliverable: one component realizes ALL of ITS OWN
   required pairs under cyc_sigma -- every (a,b) in ps whose source a
   landed in this component gets sigma(a) = b, whether a is an interior
   link (via cyc_sigma_succ) or the component's own closing link (via
   cyc_sigma_wrap, using chase's "never stops early" guarantee above to
   know the closing link really does have to be either absent or point
   back to v0). *)
Theorem component_pair_realized :
  forall ps : list (var * var), NoDup (map snd ps) -> NoDup (map fst ps) ->
  forall v0 sigma, forall a b, In (a, b) ps -> In a (component ps v0) ->
  cyc_sigma (component ps v0) sigma a = b.
Proof.
  intros ps HNDsnd HNDfst v0 sigma a b Hpair Ha.
  destruct (component_invariant ps HNDsnd HNDfst v0) as [HNDcomp [Hchaincomp Hterm]].
  destruct (In_nth_error (component ps v0) a Ha) as [i Hi].
  assert (Hilt : i < length (component ps v0)) by (eapply nth_error_Some; congruence).
  assert (Hfab : fwd ps a = Some b) by exact (fwd_complete ps HNDfst a b Hpair).
  destruct (Nat.eq_dec i (length (component ps v0) - 1)) as [Hlast | Hnotlast].
  - subst i.
    destruct (Hterm a Hi) as [Hnone | Hsome]; [congruence | ].
    assert (Hb : b = v0) by congruence. subst b.
    assert (Ha' : nth (length (component ps v0) - 1) (component ps v0) 0 = a)
      by exact (nth_error_nth (component ps v0) (length (component ps v0) - 1) 0 Hi).
    rewrite <- Ha'.
    assert (Hnnil : component ps v0 <> nil) by (intro Hc; rewrite Hc in Hi; simpl in Hi; discriminate Hi).
    rewrite (cyc_sigma_wrap (component ps v0) sigma HNDcomp Hnnil).
    exact (component_hd ps v0).
  - assert (Hilt2 : S i < length (component ps v0)) by lia.
    assert (Hne : nth_error (component ps v0) (S i) <> None) by (apply nth_error_Some; exact Hilt2).
    destruct (nth_error (component ps v0) (S i)) as [c | ] eqn:Hc; [ | congruence].
    assert (Hfac : fwd ps a = Some c) by exact (Hchaincomp i a c Hi Hc).
    assert (Hbc : b = c) by congruence. subst c.
    assert (Ha' : nth i (component ps v0) 0 = a) by exact (nth_error_nth (component ps v0) i 0 Hi).
    rewrite <- Ha'.
    rewrite (cyc_sigma_succ (component ps v0) sigma i HNDcomp Hilt2).
    exact (nth_error_nth (component ps v0) (S i) 0 Hc).
Qed.

(* ==================================================================== *)
(* PIECE 2c: wiring 2a/2b into the full batch-extend theorem: given ps    *)
(* (as a whole, not just one v0's own component), produce (sigma',tau')   *)
(* realizing EVERY pair.  The extra ingredient this needs on top of 2b:    *)
(* CHOOSING v0, at each step, as a genuine "pure source" (no predecessor  *)
(* in ps) whenever one exists -- an arbitrary v0 would risk starting the  *)
(* chase partway down an open path, silently missing everything upstream  *)
(* of it.  When no pure source exists, ps's whole remaining structure is  *)
(* forced (by a NoDup/cardinality argument) to be pure closed cycles, so  *)
(* an arbitrary start is fine there.  Either way this delivers the fact   *)
(* actually needed to filter safely: no pair whose TARGET lands inside a  *)
(* chosen component can have its SOURCE outside that component.          *)
(* ==================================================================== *)

Definition has_pred (ps : list (var * var)) (a : var) : bool :=
  if in_dec Nat.eq_dec a (map snd ps) then true else false.

Definition pick_source (ps : list (var * var)) : var :=
  match find (fun p => negb (has_pred ps (fst p))) ps with
  | Some p => fst p
  | None => match ps with (a, _) :: _ => a | nil => 0 end
  end.

Lemma pick_source_in_fst : forall ps : list (var * var), ps <> nil -> In (pick_source ps) (map fst ps).
Proof.
  intros ps Hnnil. unfold pick_source.
  destruct (find (fun p => negb (has_pred ps (fst p))) ps) as [p | ] eqn:E.
  - assert (H := find_some _ _ E). exact (in_map fst ps p (proj1 H)).
  - destruct ps as [| [a b] ps']; [congruence | simpl; left; reflexivity].
Qed.

Lemma pick_source_pure :
  forall ps p, find (fun p => negb (has_pred ps (fst p))) ps = Some p -> ~ In (fst p) (map snd ps).
Proof.
  intros ps p Hfind. assert (H := find_some _ _ Hfind). destruct H as [_ Hpred].
  unfold has_pred in Hpred. destruct (in_dec Nat.eq_dec (fst p) (map snd ps)) as [Hin | Hnin].
  - simpl in Hpred. discriminate Hpred.
  - exact Hnin.
Qed.

Lemma pick_source_none_fst_subset_snd :
  forall ps : list (var * var), find (fun p => negb (has_pred ps (fst p))) ps = None ->
  forall a, In a (map fst ps) -> In a (map snd ps).
Proof.
  intros ps Hfind a Ha. apply in_map_iff in Ha. destruct Ha as [p [Hfst Hin]].
  assert (H := find_none _ _ Hfind p Hin). unfold has_pred in H.
  destruct (in_dec Nat.eq_dec (fst p) (map snd ps)) as [Hin2 | Hnin2].
  - subst a. exact Hin2.
  - simpl in H. discriminate H.
Qed.

Lemma pick_source_no_pred_or_all_cycle :
  forall ps : list (var * var), ps <> nil ->
  ~ In (pick_source ps) (map snd ps) \/ (forall a, In a (map fst ps) -> In a (map snd ps)).
Proof.
  intros ps Hnnil. unfold pick_source.
  destruct (find (fun p => negb (has_pred ps (fst p))) ps) as [p | ] eqn:Efind.
  - left. exact (pick_source_pure ps p Efind).
  - right. exact (pick_source_none_fst_subset_snd ps Efind).
Qed.

(* When there's no pure source, fst-as-a-SET equals snd-as-a-SET (same
   cardinality via NoDup on both, one inclusion given, so the reverse
   inclusion is forced) -- i.e. ps's whole structure is pure closed
   cycles, no dangling paths anywhere. *)
Lemma pick_source_all_cycle_snd_subset_fst :
  forall ps : list (var * var), NoDup (map fst ps) -> NoDup (map snd ps) ->
  (forall a, In a (map fst ps) -> In a (map snd ps)) ->
  forall b, In b (map snd ps) -> In b (map fst ps).
Proof.
  intros ps HNDfst HNDsnd Hsub b Hb.
  assert (Hlen : length (map snd ps) <= length (map fst ps)) by (rewrite !map_length; lia).
  exact (NoDup_length_incl HNDfst Hlen Hsub b Hb).
Qed.

(* Every element of a component is either v0 itself, or was reached via
   some fwd link, hence is a genuine target in ps. *)
Lemma component_subset :
  forall ps : list (var * var), NoDup (map snd ps) -> NoDup (map fst ps) ->
  forall v0 w, In w (component ps v0) -> w = v0 \/ In w (map snd ps).
Proof.
  intros ps HNDsnd HNDfst v0 w Hin.
  destruct (component_invariant ps HNDsnd HNDfst v0) as [HNDcomp [Hchaincomp _]].
  destruct (In_nth_error (component ps v0) w Hin) as [i Hi].
  destruct i as [| i'].
  - left. rewrite (component_head ps v0) in Hi. congruence.
  - right.
    assert (HSilt : S i' < length (component ps v0)) by (eapply nth_error_Some; congruence).
    assert (Hi'lt : i' < length (component ps v0)) by lia.
    assert (Hne2 : nth_error (component ps v0) i' <> None) by (apply nth_error_Some; lia).
    destruct (nth_error (component ps v0) i') as [x | ] eqn:Hx; [ | congruence].
    assert (Hfxw : fwd ps x = Some w) by exact (Hchaincomp i' x w Hx Hi).
    exact (in_map snd ps (x, w) (fwd_in ps x w Hfxw)).
Qed.

(* The fact PIECE 2c's filtering step actually needs: no pair's TARGET can
   land inside a chosen component while its SOURCE stays outside it. *)
Theorem component_backward_closed :
  forall ps : list (var * var), NoDup (map fst ps) -> NoDup (map snd ps) -> ps <> nil ->
  forall a b, In (a, b) ps ->
  In b (component ps (pick_source ps)) -> In a (component ps (pick_source ps)).
Proof.
  intros ps HNDfst HNDsnd Hnnil a b Hpair Hbin.
  set (v0 := pick_source ps).
  destruct (component_invariant ps HNDsnd HNDfst v0) as [HNDcomp [Hchaincomp Hterm]].
  assert (Hfab : fwd ps a = Some b) by exact (fwd_complete ps HNDfst a b Hpair).
  destruct (In_nth_error (component ps v0) b Hbin) as [i Hi].
  destruct i as [| i'].
  - assert (Hb0 : b = v0) by (rewrite (component_head ps v0) in Hi; congruence). subst b.
    destruct (pick_source_no_pred_or_all_cycle ps Hnnil) as [Hpure | Hallsnd].
    + exfalso. apply Hpure. exact (in_map snd ps (a, v0) Hpair).
    + assert (Hnnilc : component ps v0 <> nil) by (intro Hc; rewrite Hc in Hi; simpl in Hi; discriminate Hi).
      assert (Hltx : length (component ps v0) - 1 < length (component ps v0))
        by (destruct (component ps v0) as [| ? ?]; [congruence | simpl; lia]).
      assert (Hnex : nth_error (component ps v0) (length (component ps v0) - 1) <> None)
        by (apply nth_error_Some; exact Hltx).
      destruct (nth_error (component ps v0) (length (component ps v0) - 1)) as [xl | ] eqn:Hxl;
        [ | exfalso; apply Hnex; reflexivity].
      destruct (Hterm xl eq_refl) as [Hnone | Hsome].
      * exfalso.
        assert (Hxlcomp : In xl (component ps v0)) by exact (nth_error_In (component ps v0) _ Hxl).
        destruct (component_subset ps HNDsnd HNDfst v0 xl Hxlcomp) as [Heqxlv0 | Hxlsnd].
        -- subst xl.
           assert (Hv0fst : In v0 (map fst ps)) by exact (pick_source_in_fst ps Hnnil).
           apply in_map_iff in Hv0fst. destruct Hv0fst as [[a0 b0] [Ha0 Hin0]]. simpl in Ha0. subst a0.
           assert (Hfwdv0 : fwd ps v0 = Some b0) by exact (fwd_complete ps HNDfst v0 b0 Hin0).
           rewrite Hfwdv0 in Hnone. discriminate Hnone.
        -- assert (Hxlfst := pick_source_all_cycle_snd_subset_fst ps HNDfst HNDsnd Hallsnd xl Hxlsnd).
           apply in_map_iff in Hxlfst. destruct Hxlfst as [[a1 b1] [Ha1 Hin1]]. simpl in Ha1. subst a1.
           assert (Hfwdxl : fwd ps xl = Some b1) by exact (fwd_complete ps HNDfst xl b1 Hin1).
           rewrite Hfwdxl in Hnone. discriminate Hnone.
      * assert (Ha' : a = xl) by exact (fwd_injective ps HNDsnd a xl v0 Hfab Hsome). subst a.
        exact (nth_error_In (component ps v0) (length (component ps v0) - 1) Hxl).
  - assert (HSilt : S i' < length (component ps v0)) by (eapply nth_error_Some; congruence).
    assert (Hi'lt : i' < length (component ps v0)) by lia.
    assert (Hne2 : nth_error (component ps v0) i' <> None) by (apply nth_error_Some; lia).
    destruct (nth_error (component ps v0) i') as [x | ] eqn:Hx; [ | congruence].
    assert (Hfxb : fwd ps x = Some b) by exact (Hchaincomp i' x b Hx Hi).
    assert (Ha' : a = x) by exact (fwd_injective ps HNDsnd a x b Hfab Hfxb). subst a.
    exact (nth_error_In (component ps v0) i' Hx).
Qed.

Lemma filter_length_lt :
  forall (A : Type) (f : A -> bool) (l : list A) (x : A),
  In x l -> f x = false -> length (filter f l) < length l.
Proof.
  induction l as [| y l' IH]; intros x Hin Hf.
  - destruct Hin.
  - simpl. destruct Hin as [Hin | Hin].
    + subst y. rewrite Hf. simpl. assert (Hle := filter_length_le f l'). lia.
    + destruct (f y) eqn:Ey.
      * simpl. assert (IH' := IH x Hin Hf). lia.
      * assert (IH' := IH x Hin Hf). lia.
Qed.

Lemma NoDup_map_filter :
  forall (A B : Type) (g : A -> B) (f : A -> bool) (l : list A),
  NoDup (map g l) -> NoDup (map g (filter f l)).
Proof.
  intros A B g f. induction l as [| x l' IH]; intro HND.
  - constructor.
  - simpl in HND. inversion HND as [| ? ? Hnin HND']; subst.
    simpl. destruct (f x) eqn:Ef.
    + simpl. apply NoDup_cons.
      * intro Hin. apply Hnin. apply in_map_iff in Hin. destruct Hin as [y [Hgy Hiny]].
        apply filter_In in Hiny. destruct Hiny as [Hiny _]. apply in_map_iff. exists y. split; assumption.
      * exact (IH HND').
    + exact (IH HND').
Qed.

(* PIECE 2c's actual deliverable: the full batch-extend theorem.  Given an
   arbitrary set of required pairs ps (NoDup on both projections) and a
   mutual-inverse pair already fixed on ps's whole domain+range, produces
   an extension realizing EVERY pair in ps at once -- closing the
   permutation-extension gap THEOREM2_PROCESS_NOTES.md section 20/21/22
   traces back to NL_Fun's two independently-chosen fresh renamings. *)
Theorem batch_extend :
  forall n ps, length ps <= n -> NoDup (map fst ps) -> NoDup (map snd ps) ->
  forall sigma tau, mutual_inverse sigma tau ->
  (forall w, In w (map fst ps) \/ In w (map snd ps) -> sigma w = w) ->
  exists sigma' tau', mutual_inverse sigma' tau' /\
    (forall a b, In (a, b) ps -> sigma' a = b) /\
    (forall w, ~ In w (map fst ps) -> ~ In w (map snd ps) -> sigma' w = sigma w).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros ps Hlen HNDfst HNDsnd sigma tau Hmi Hfix.
  destruct ps as [| p ps'].
  - exists sigma, tau.
    split; [exact Hmi | split; [intros a b Hc; destruct Hc | intros w _ _; reflexivity]].
  - set (v0 := pick_source (p :: ps')).
    assert (Hnnil : p :: ps' <> nil) by discriminate.
    destruct (component_invariant (p :: ps') HNDsnd HNDfst v0) as [HNDcomp [Hchaincomp Hterm]].
    assert (Hv0fst : In v0 (map fst (p :: ps'))) by exact (pick_source_in_fst (p :: ps') Hnnil).
    assert (Hv0comp : In v0 (component (p :: ps') v0))
      by exact (nth_error_In (component (p :: ps') v0) 0 (component_head (p :: ps') v0)).
    assert (Hfixcomp : forall w, In w (component (p :: ps') v0) -> sigma w = w).
    { intros w Hw. destruct (component_subset (p :: ps') HNDsnd HNDfst v0 w Hw) as [Heq | Hin2].
      - subst w. apply Hfix. left. exact Hv0fst.
      - apply Hfix. right. exact Hin2. }
    set (sigma1 := cyc_sigma (component (p :: ps') v0) sigma).
    set (tau1 := cyc_tau (component (p :: ps') v0) tau).
    assert (Hmi1 : mutual_inverse sigma1 tau1)
      by exact (cyc_extend (component (p :: ps') v0) sigma tau Hmi HNDcomp Hfixcomp).
    assert (Hsigma1_out : forall w, ~ In w (component (p :: ps') v0) -> sigma1 w = sigma w).
    { intros w Hw. unfold sigma1, cyc_sigma.
      destruct (list_index (component (p :: ps') v0) w) as [i | ] eqn:Ei; [ | reflexivity].
      exfalso. apply Hw. exact (nth_error_In (component (p :: ps') v0) i (list_index_nth_error _ w i Ei)). }
    set (ps_rest := filter (fun q => if in_dec Nat.eq_dec (fst q) (component (p :: ps') v0) then false else true)
                      (p :: ps')).
    assert (Hrest_sub : forall q, In q ps_rest -> In q (p :: ps')).
    { intros q Hq. unfold ps_rest in Hq. apply filter_In in Hq. destruct Hq as [Hq _]. exact Hq. }
    assert (Hrest_out : forall q, In q ps_rest -> ~ In (fst q) (component (p :: ps') v0)).
    { intros q Hq. unfold ps_rest in Hq. apply filter_In in Hq. destruct Hq as [_ Hb].
      destruct (in_dec Nat.eq_dec (fst q) (component (p :: ps') v0)) as [Hin2 | Hnin2];
        [discriminate Hb | exact Hnin2]. }
    assert (Hrest_sub_fst : forall w, In w (map fst ps_rest) -> In w (map fst (p :: ps'))).
    { intros w Hw. apply in_map_iff in Hw. destruct Hw as [q [Hfw Hqin]]. subst w.
      exact (in_map fst (p :: ps') q (Hrest_sub q Hqin)). }
    assert (Hrest_sub_snd : forall w, In w (map snd ps_rest) -> In w (map snd (p :: ps'))).
    { intros w Hw. apply in_map_iff in Hw. destruct Hw as [q [Hsw Hqin]]. subst w.
      exact (in_map snd (p :: ps') q (Hrest_sub q Hqin)). }
    assert (Hv0q : exists q, In q (p :: ps') /\ fst q = v0).
    { apply in_map_iff in Hv0fst. destruct Hv0fst as [q [Hq1 Hq2]]. exists q. split; assumption. }
    destruct Hv0q as [q0 [Hq0in Hq0fst]].
    assert (Hq0false : (if in_dec Nat.eq_dec (fst q0) (component (p :: ps') v0) then false else true) = false).
    { destruct (in_dec Nat.eq_dec (fst q0) (component (p :: ps') v0)) as [_ | Hc]; [reflexivity | ].
      exfalso. apply Hc. rewrite Hq0fst. exact Hv0comp. }
    assert (Hrest_len : length ps_rest < length (p :: ps'))
      by exact (filter_length_lt _ _ (p :: ps') q0 Hq0in Hq0false).
    assert (HNDfst_rest : NoDup (map fst ps_rest)) by exact (NoDup_map_filter _ _ fst _ (p :: ps') HNDfst).
    assert (HNDsnd_rest : NoDup (map snd ps_rest)) by exact (NoDup_map_filter _ _ snd _ (p :: ps') HNDsnd).
    assert (Hfix1 : forall w, In w (map fst ps_rest) \/ In w (map snd ps_rest) -> sigma1 w = w).
    { intros w Hw.
      assert (Hwnotcomp : ~ In w (component (p :: ps') v0)).
      { destruct Hw as [Hw | Hw].
        - apply in_map_iff in Hw. destruct Hw as [q [Hfw Hqin]]. subst w. exact (Hrest_out q Hqin).
        - apply in_map_iff in Hw. destruct Hw as [q [Hsw Hqin]]. subst w.
          intro Hcontra.
          assert (Hqorig : In q (p :: ps')) by exact (Hrest_sub q Hqin).
          assert (Hqpair : In (fst q, snd q) (p :: ps')) by (rewrite <- surjective_pairing; exact Hqorig).
          assert (Hback := component_backward_closed (p :: ps') HNDfst HNDsnd Hnnil (fst q) (snd q) Hqpair Hcontra).
          exact (Hrest_out q Hqin Hback). }
      rewrite (Hsigma1_out w Hwnotcomp).
      apply Hfix. destruct Hw as [Hw | Hw]; [left; exact (Hrest_sub_fst w Hw) | right; exact (Hrest_sub_snd w Hw)]. }
    assert (Hnlen : length ps_rest < n) by lia.
    destruct (IHn (length ps_rest) Hnlen ps_rest (Nat.le_refl _) HNDfst_rest HNDsnd_rest sigma1 tau1 Hmi1 Hfix1)
      as [sigma2 [tau2 [Hmi2 [Hreal2 Hout2]]]].
    exists sigma2, tau2. split; [exact Hmi2 | split].
    + intros a b Hpair2.
      destruct (in_dec Nat.eq_dec a (component (p :: ps') v0)) as [Hin_comp | Hnin_comp].
      * assert (Hab1 : sigma1 a = b)
          by exact (component_pair_realized (p :: ps') HNDsnd HNDfst v0 sigma a b Hpair2 Hin_comp).
        assert (Hao1 : ~ In a (map fst ps_rest)).
        { intro Hc. apply in_map_iff in Hc. destruct Hc as [q [Hfq Hqin]].
          apply (Hrest_out q Hqin). rewrite Hfq. exact Hin_comp. }
        assert (Hao2 : ~ In a (map snd ps_rest)).
        { intro Hc. apply in_map_iff in Hc. destruct Hc as [q [Hsq Hqin]].
          assert (Hqorig : In q (p :: ps')) by exact (Hrest_sub q Hqin).
          assert (Hqpair : In (fst q, snd q) (p :: ps')) by (rewrite <- surjective_pairing; exact Hqorig).
          assert (Ha_eq : a = snd q) by (symmetry; exact Hsq).
          rewrite Ha_eq in Hin_comp.
          assert (Hback := component_backward_closed (p :: ps') HNDfst HNDsnd Hnnil (fst q) (snd q) Hqpair Hin_comp).
          exact (Hrest_out q Hqin Hback). }
        rewrite (Hout2 a Hao1 Hao2). exact Hab1.
      * assert (Hin_rest : In (a, b) ps_rest).
        { unfold ps_rest. apply filter_In. split; [exact Hpair2 | ].
          change ((if in_dec Nat.eq_dec a (component (p :: ps') v0) then false else true) = true).
          destruct (in_dec Nat.eq_dec a (component (p :: ps') v0)) as [Hc | Hc];
            [exfalso; exact (Hnin_comp Hc) | reflexivity]. }
        exact (Hreal2 a b Hin_rest).
    + intros w Hwf Hws.
      assert (Hwnotcomp : ~ In w (component (p :: ps') v0)).
      { intro Hc. destruct (component_subset (p :: ps') HNDsnd HNDfst v0 w Hc) as [Heq | Hin2].
        - subst w. exact (Hwf Hv0fst).
        - exact (Hws Hin2). }
      assert (Hwf_rest : ~ In w (map fst ps_rest)) by (intro Hc; apply Hwf; exact (Hrest_sub_fst w Hc)).
      assert (Hws_rest : ~ In w (map snd ps_rest)) by (intro Hc; apply Hws; exact (Hrest_sub_snd w Hc)).
      rewrite (Hout2 w Hwf_rest Hws_rest). exact (Hsigma1_out w Hwnotcomp).
Qed.

(* ==================================================================== *)
(* PIECE 3, prerequisite (i)+(iii) from the header's PIECE-2c-check note: *)
(* an enumeration of every syntactic variable POSITION rename_b/rename_e0 *)
(* touch (bound and free alike -- confirmed from their own definitions,   *)
(* so no real binding/shadowing analysis is needed here), and the         *)
(* congruence lemma turning batch_extend's per-PAIR guarantee into an     *)
(* actual rename_b TERM equality.                                        *)
(* ==================================================================== *)

Definition vars_of_e0 (e : Expr0) : list var :=
  match e with
  | EVar x => x :: nil
  | EBot => nil
  | EFree => nil
  | EChoice x y => x :: y :: nil
  | EFun f args => args
  | ECon c args => args
  end.

Fixpoint vars_of_b (b : Blk) : list var :=
  match b with
  | BLet x e k => x :: vars_of_e0 e ++ vars_of_b k
  | BCase x brs =>
      x :: fold_right (fun p acc => match p with (c, ps, bd) => ps ++ vars_of_b bd ++ acc end) nil brs
  | BExpr e => vars_of_e0 e
  end.

Lemma rename_e0_congr :
  forall sigma1 sigma2 e, (forall x, In x (vars_of_e0 e) -> sigma1 x = sigma2 x) ->
  rename_e0 sigma1 e = rename_e0 sigma2 e.
Proof.
  intros sigma1 sigma2 e Hagree.
  destruct e as [x | | | x y | f args | c args]; simpl in *; try reflexivity.
  - f_equal. apply Hagree. left. reflexivity.
  - f_equal; [apply Hagree; left; reflexivity | apply Hagree; right; left; reflexivity].
  - f_equal. apply map_ext_in. exact Hagree.
  - f_equal. apply map_ext_in. exact Hagree.
Qed.

Lemma rename_b_congr_bound :
  forall n b, blk_size b < n ->
  forall sigma1 sigma2, (forall x, In x (vars_of_b b) -> sigma1 x = sigma2 x) ->
  rename_b sigma1 b = rename_b sigma2 b.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize sigma1 sigma2 Hagree.
  destruct b as [x e k | x brs | e].
  - simpl in *.
    assert (Hn : blk_size k + 1 < n) by lia.
    assert (Hm : blk_size k < blk_size k + 1) by lia.
    assert (Hxeq : sigma1 x = sigma2 x) by (apply Hagree; left; reflexivity).
    assert (Heeq : rename_e0 sigma1 e = rename_e0 sigma2 e).
    { apply rename_e0_congr. intros y Hy. apply Hagree. right. apply in_or_app. left. exact Hy. }
    assert (Hkeq : rename_b sigma1 k = rename_b sigma2 k).
    { apply (IHn (blk_size k + 1) Hn k Hm sigma1 sigma2).
      intros y Hy. apply Hagree. right. apply in_or_app. right. exact Hy. }
    rewrite Hxeq, Heeq, Hkeq. reflexivity.
  - simpl in *.
    assert (Hxeq : sigma1 x = sigma2 x) by (apply Hagree; left; reflexivity).
    rewrite Hxeq. f_equal.
    induction brs as [| [[c ps] bd] brs' IHbrs].
    + reflexivity.
    + simpl in Hsize |- *.
      assert (Hbd : blk_size bd + 1 < n) by lia.
      assert (Hm : blk_size bd < blk_size bd + 1) by lia.
      assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_, _, bd0) => bd0 end) + acc) 0 brs') < n)
        by lia.
      f_equal.
      * f_equal.
        -- f_equal. apply map_ext_in.
           intros y Hy. apply Hagree. right. apply in_or_app. left. exact Hy.
        -- apply (IHn (blk_size bd + 1) Hbd bd Hm sigma1 sigma2).
           intros y Hy. apply Hagree. right. apply in_or_app. right. apply in_or_app. left. exact Hy.
      * apply IHbrs.
        { exact Hrest. }
        { intros y Hy. destruct Hy as [Hxy | Hy].
          - subst y. exact Hxeq.
          - apply Hagree. right. apply in_or_app. right. apply in_or_app. right. exact Hy. }
  - simpl. f_equal. apply rename_e0_congr. exact Hagree.
Qed.

Lemma rename_b_congr :
  forall b sigma1 sigma2, (forall x, In x (vars_of_b b) -> sigma1 x = sigma2 x) ->
  rename_b sigma1 b = rename_b sigma2 b.
Proof.
  intros b sigma1 sigma2 Hagree.
  exact (rename_b_congr_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) sigma1 sigma2 Hagree).
Qed.

(* ==================================================================== *)
(* PIECE 3, prerequisite (ii): the bisimulation invariant relating two    *)
(* NHeaps across a mutual-inverse pair, and its interaction with hupd/    *)
(* hupd_list -- stated directly as pointwise equality to nheap_rename     *)
(* (piece 1b) so that ALL of nheap_rename's already-proven hupd/hupd_list *)
(* commutation lemmas carry over immediately, with no separate domain-    *)
(* matching lemma needed: Gam1 x = None iff Gam2 (sigma x) = None falls    *)
(* out of option_map's own None-preserving behavior, for free.            *)
(* ==================================================================== *)

Definition NHeapAlpha (sigma tau : ren) (Gam1 Gam2 : NHeap) : Prop :=
  forall w, Gam2 w = nheap_rename sigma tau Gam1 w.

Lemma NHeapAlpha_hupd :
  forall sigma tau, mutual_inverse sigma tau -> forall Gam1 Gam2, NHeapAlpha sigma tau Gam1 Gam2 ->
  forall x v, NHeapAlpha sigma tau (hupd Gam1 x v) (hupd Gam2 (sigma x) (rename_b sigma v)).
Proof.
  intros sigma tau Hmi Gam1 Gam2 Halpha x v w.
  rewrite (nheap_rename_hupd sigma tau Hmi Gam1 x v w).
  assert (Hpt := hupd_list_pointwise (sigma x :: nil) (rename_b sigma v :: nil) Gam2
             (nheap_rename sigma tau Gam1) Halpha w).
  simpl in Hpt. exact Hpt.
Qed.

Lemma NHeapAlpha_hupd_list :
  forall sigma tau, mutual_inverse sigma tau -> forall Gam1 Gam2, NHeapAlpha sigma tau Gam1 Gam2 ->
  forall xs vs,
  NHeapAlpha sigma tau (hupd_list Gam1 xs vs) (hupd_list Gam2 (map sigma xs) (map (rename_b sigma) vs)).
Proof.
  intros sigma tau Hmi Gam1 Gam2 Halpha xs vs w.
  rewrite (nheap_rename_hupd_list sigma tau Hmi xs vs Gam1 w).
  exact (hupd_list_pointwise (map sigma xs) (map (rename_b sigma) vs) Gam2
           (nheap_rename sigma tau Gam1) Halpha w).
Qed.

(* The domain-matching fact PIECE 3's containment invariant needs, for    *)
(* free: NHeapAlpha's own definition already forces it, via option_map's   *)
(* None-preserving behavior -- no separate lemma to prove elsewhere.       *)
Lemma NHeapAlpha_domain :
  forall sigma tau, mutual_inverse sigma tau -> forall Gam1 Gam2, NHeapAlpha sigma tau Gam1 Gam2 ->
  forall x, Gam1 x = None <-> Gam2 (sigma x) = None.
Proof.
  intros sigma tau [Hst Hts] Gam1 Gam2 Halpha x.
  rewrite (Halpha (sigma x)). unfold nheap_rename. rewrite Hst.
  destruct (Gam1 x) as [b | ]; simpl; split; intro H; try discriminate H; try reflexivity.
Qed.

(* ==================================================================== *)
(* PIECE 3: THE MAIN PIECE.                                              *)
(*                                                                        *)
(* CORRECTION to last session's draft, found by actually tracing the      *)
(* NL_Fun case through before touching the induction: the "same           *)
(* expression, same heap" self-confluence statement drafted last session  *)
(* is TRUE at the top level but CANNOT serve as its own induction          *)
(* hypothesis.  NL_Fun's two continuations (rename_b s1 body vs            *)
(* rename_b s2 body) are only RELATED by a renaming, not literally the     *)
(* same expression -- and once expressions diverge, the two derivations'   *)
(* own HEAPS diverge too (each side's later hupd calls only ever touch     *)
(* its own output heap), so "the same shared Gam" stops being available    *)
(* past the first NL_Fun/NL_Guess step either.  The induction genuinely     *)
(* needs the general form section 19 originally called for: two heaps      *)
(* related by NHeapAlpha, two expressions related by rename_b sigma0 --    *)
(* last session's "scope narrowing" was right about what the COROLLARY     *)
(* needs, wrong about what the INDUCTION needs.  Good that this surfaced    *)
(* before, not during, the 11-case proof.                                  *)
(* ==================================================================== *)

Lemma rename_e0_id : forall e, rename_e0 (fun w => w) e = e.
Proof. intros e. destruct e; simpl; try reflexivity; f_equal; apply map_id. Qed.

Lemma rename_b_id_bound : forall n b, blk_size b < n -> rename_b (fun w => w) b = b.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize. destruct b as [x e k | x brs | e].
  - simpl in *.
    assert (Hn : blk_size k + 1 < n) by lia.
    assert (Hm : blk_size k < blk_size k + 1) by lia.
    rewrite (IHn (blk_size k + 1) Hn k Hm), rename_e0_id. reflexivity.
  - simpl in *. f_equal.
    induction brs as [| [[c ps] bd] brs' IHbrs].
    + reflexivity.
    + simpl in Hsize |- *.
      assert (Hbd : blk_size bd + 1 < n) by lia.
      assert (Hm : blk_size bd < blk_size bd + 1) by lia.
      assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_, _, bd0) => bd0 end) + acc) 0 brs') < n)
        by lia.
      f_equal.
      * f_equal; [f_equal; apply map_id | exact (IHn (blk_size bd + 1) Hbd bd Hm)].
      * apply IHbrs. exact Hrest.
  - simpl. f_equal. apply rename_e0_id.
Qed.

Lemma rename_b_id : forall b, rename_b (fun w => w) b = b.
Proof. intros b. exact (rename_b_id_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _)). Qed.

Lemma NHeapAlpha_refl : forall Gam, NHeapAlpha (fun w => w) (fun w => w) Gam Gam.
Proof.
  intros Gam w. unfold nheap_rename.
  destruct (Gam w) as [b | ] eqn:E; [simpl; f_equal; symmetry; apply rename_b_id | reflexivity].
Qed.

(* Three small "rename_b preserves top-level shape" facts, needed to know
   D2's own shape-inversion is forced into the SAME NEval_left constructor
   as D1's at NL_VarExp: if e isn't ECon/EVar-x/EFree shaped, rename_b
   sigma0 e isn't ECon/EVar-(sigma0 x)/EFree shaped either. *)
Lemma rename_b_not_econ :
  forall sigma b, (forall c args, b <> BExpr (ECon c args)) ->
  forall c args, rename_b sigma b <> BExpr (ECon c args).
Proof.
  intros sigma b Hb c args Hcontra.
  destruct b as [x0 e0 k | x0 brs | e0]; simpl in Hcontra; try discriminate Hcontra.
  destruct e0 as [z | | | z1 z2 | f args1 | c0 args0]; simpl in Hcontra; try discriminate Hcontra.
  injection Hcontra as Hcc Haa. exact (Hb c0 args0 eq_refl).
Qed.

Lemma rename_b_not_efree :
  forall sigma b, b <> BExpr EFree -> rename_b sigma b <> BExpr EFree.
Proof.
  intros sigma b Hb Hcontra.
  destruct b as [x0 e0 k | x0 brs | e0]; simpl in Hcontra; try discriminate Hcontra.
  destruct e0 as [z | | | z1 z2 | f args1 | c0 args0]; simpl in Hcontra; try discriminate Hcontra.
  exact (Hb eq_refl).
Qed.

Lemma rename_b_not_evar :
  forall sigma, (forall x y, sigma x = sigma y -> x = y) ->
  forall b x, b <> BExpr (EVar x) -> rename_b sigma b <> BExpr (EVar (sigma x)).
Proof.
  intros sigma Hinj b x Hb Hcontra.
  destruct b as [x0 e0 k | x0 brs | e0]; simpl in Hcontra; try discriminate Hcontra.
  destruct e0 as [y | | | z1 z2 | f args1 | c0 args0]; simpl in Hcontra; try discriminate Hcontra.
  injection Hcontra as Hcontra.
  assert (Hxy : y = x) by (apply Hinj; exact Hcontra).
  subst y. exact (Hb eq_refl).
Qed.

Lemma let_content_rename :
  forall sigma x e, let_content (sigma x) (rename_e0 sigma e) = rename_b sigma (let_content x e).
Proof. intros sigma x e. destruct e; reflexivity. Qed.

(* The actual inductive statement: two heaps related by NHeapAlpha, two      *)
(* expressions related by rename_b sigma0, an ambient (sigma0,tau0); the      *)
(* two guard lists F1,F2 are RELATED (F2 = map sigma0 F1), not shared -- an   *)
(* earlier draft shared a single F and broke at NL_VarExp, where D1's guard    *)
(* grows to x::F1 but D2's grows to (sigma0 x)::F2, equal to map sigma0        *)
(* (x::F1) only via this relation, never literally the same list unless        *)
(* sigma0 x = x.  Concludes an EXTENSION of sigma0: agrees with it wherever    *)
(* sigma0 already moved something, OR wherever the location was ALREADY in     *)
(* either heap's domain before this sub-derivation (the second part is what    *)
(* NL_VarExp's own step needs: x in dom(Gam1) forces sigma to leave x alone,    *)
(* even though sigma0 itself already fixed x, because x can't be one of a       *)
(* DEEPER NL_Fun/NL_Guess step's fresh pairs -- those are always outside the    *)
(* CURRENT heap's domain by construction, and domains only grow). *)
Lemma hupd_preserves_some : forall (G : NHeap) x v w, G w <> None -> hupd G x v w <> None.
Proof.
  intros G x v w H. unfold hupd. destruct (Nat.eqb w x); [discriminate | exact H].
Qed.

Lemma NoDup_map_inj :
  forall (A B : Type) (f : A -> B) (l : list A),
  (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj. induction l as [| a l' IH]; intro HND.
  - constructor.
  - inversion HND as [| ? ? Hnin HND']; subst. simpl. apply NoDup_cons.
    + intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hfy Hiny]].
      apply Hinj in Hfy. subst y. exact (Hnin Hiny).
    + exact (IH HND').
Qed.

(* The OR-contrapositive of the AND-shaped containment hypothesis: EITHER
   heap being undefined at w already suffices to know sigma0 leaves w alone
   -- used at NL_Fun/NL_Guess for each of the two independently-fresh
   locations separately (each is fresh w.r.t. only ITS OWN heap). *)
Lemma Hcontain_None_fixed :
  forall sigma0 (Gam1 Gam2 : NHeap), (forall w, sigma0 w <> w -> Gam1 w <> None /\ Gam2 w <> None) ->
  forall w, Gam1 w = None \/ Gam2 w = None -> sigma0 w = w.
Proof.
  intros sigma0 Gam1 Gam2 Hcontain w Hw.
  destruct (Nat.eq_dec (sigma0 w) w) as [Heq | Hneq]; [exact Heq | ].
  destruct (Hcontain w Hneq) as [H1 H2]. exfalso.
  destruct Hw as [Hw | Hw]; [exact (H1 Hw) | exact (H2 Hw)].
Qed.

(* ==================================================================== *)
(* PIECE 5 (new): the "closed heap" invariant flagged by NL_Fun's fifth   *)
(* gap (see the comment there, and THEOREM2_PROCESS_NOTES.md Sec.27) --   *)
(* no value stored in the heap references a location outside the heap's  *)
(* own domain -- plus an attempt at the preservation lemma showing        *)
(* NEval_left maintains it.  Traced by hand before coding, per this        *)
(* file's usual discipline; the trace turned up a real simplification     *)
(* worth recording up front:                                              *)
(*                                                                        *)
(*   For the four "heap-pointer-mediated" constructors (VarCons/VarSelf/  *)
(*   VarFree/VarExp), closedness of whatever gets FOUND is derivable "for *)
(*   free" from ClosedHeap G together with the rule's own `G x = Some e`  *)
(*   premise -- no separate "is e closed" input is needed, because the    *)
(*   very existence of the given NEval_left derivation already forces it  *)
(*   (if e weren't already bound, no rule could have concluded anything    *)
(*   about it in the first place).                                        *)
(*                                                                        *)
(*   For the "reveals brand-new syntax" constructors (ValCon at the leaf,  *)
(*   and -- more importantly -- Let/Fun/Select/Guess, each of which pulls  *)
(*   a whole new Blk term in from the program or from e's own immediate    *)
(*   structure) there is no such free lunch, and vars_of_b is the WRONG    *)
(*   tool for stating what would be needed: it does not distinguish a      *)
(*   term's genuinely free variables from ones a LET/CASE inside that very *)
(*   term binds for itself.  E.g. vars_of_b (BLet z EFree (BExpr (EVar     *)
(*   z))) = [z; z], yet that term is closed under the EMPTY heap -- z      *)
(*   needs no pre-existing binding, it gets one from the let itself.  A    *)
(*   genuine free-variable analysis (tracking a growing bound-set through  *)
(*   BLet/BCase binders, unlike vars_of_b) would be needed to even STATE a *)
(*   correct hypothesis for those four cases; not attempted here.  See      *)
(*   each case's own comment below for exactly where it stalls.            *)
(* ==================================================================== *)

Definition ClosedHeap (G : NHeap) : Prop :=
  forall z b, G z = Some b -> forall w, In w (vars_of_b b) -> G w <> None.

Theorem NEval_left_closed_preserved :
  forall P F G e G' v, NEval_left P F G e G' v ->
  ClosedHeap G -> (forall w, In w (vars_of_b e) -> G w <> None) ->
  ClosedHeap G' /\ (forall w, In w (vars_of_b v) -> G' w <> None).
Proof.
  intros P F G e G' v H.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v0 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v0 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v0 Hrec IH
    | F0 G0 z c zs brs ys body G1 v0 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v0 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Hclosed Heclosed.
  - (* VarCons: G'=G, v=ECon c args; args' own closedness is exactly
       ClosedHeap G applied at z via Hz -- no other input needed. *)
    split; [exact Hclosed | ].
    simpl. apply (Hclosed z (BExpr (ECon c args)) Hz).
  - (* VarSelf: G'=G, v=EVar z; z's own closedness is Hz itself. *)
    split; [exact Hclosed | ].
    simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
    rewrite Hz. discriminate.
  - (* VarFree: G'=hupd G z (EVar z), v=EVar z; the new cell stores EVar z,
       self-referencing the very key just added -- and every other cell is
       untouched, so ClosedHeap G lifts through hupd unchanged. *)
    split.
    + intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w z) eqn:Heqw.
      * apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        simpl in Hy. destruct Hy as [Hy | []]. subst y.
        unfold hupd. rewrite Nat.eqb_refl. discriminate.
      * apply hupd_preserves_some. apply (Hclosed w b Hwb y Hy).
    + simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
      unfold hupd. rewrite Nat.eqb_refl. discriminate.
  - (* VarExp: the recursive premise's own "e0 is closed" input comes from
       ClosedHeap G0 + Hz (G0 z = Some e0) -- the "for free" case.
       G'=hupd G1 z v0. *)
    assert (He0closed : forall w, In w (vars_of_b e0) -> G0 w <> None)
      by (apply (Hclosed z e0 Hz)).
    destruct (IH Hclosed He0closed) as [HclosedG1 Hv0closed].
    split.
    + intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w z) eqn:Heqw.
      * apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        apply hupd_preserves_some. apply (Hv0closed y Hy).
      * apply hupd_preserves_some. apply (HclosedG1 w b Hwb y Hy).
    + intros w Hw. apply hupd_preserves_some. apply (Hv0closed w Hw).
  - (* ValFree: G'=G, v=EFree, no vars on either side. *)
    split; [exact Hclosed | ].
    intros w Hin. simpl in Hin. destruct Hin.
  - (* ValCon: e = v = ECon c args LITERALLY -- no heap lookup at all.
       This is exactly the "reveals brand-new syntax" shape: NL_ValCon's
       own rule has no premise constraining args, so args' closedness can
       ONLY come from the outer "e is closed" hypothesis -- which for THIS
       case is enough, since vars_of_b e = vars_of_b v = args literally
       (the general problem below is with e/v that have BINDERS inside). *)
    split; [exact Hclosed | exact Heclosed].
  - (* Fun: recursive premise is on `rename_b s body`, a brand-new term
       pulled in from the program P, not reached via any heap pointer.
       vars_of_b body conflates body's true free variables (which should
       be <= ps, if P is well-scoped) with variables body binds for
       itself internally (which get fresh locations via Hfresh and must
       NOT be required closed -- that's the whole point of Hfresh).
       Closing this needs a genuine free-variable analysis plus a
       well-scopedness fact about P; see this file's header STATUS and
       THEOREM2_PROCESS_NOTES.md Sec.27 for the exact plan. NOT YET
       ATTEMPTED. *)
    admit.
  - (* Let: recursive premise is on k, under the NEW binder z.  Same root
       problem as Fun (need z's binding removed from k's own free-var
       requirement, not merely consulted) plus e0's own vars_of_e0 needs
       to already be closed and isn't given by NL_Let's rule (same
       "reveals new syntax, no premise constrains it" gap as ValCon, but
       here it also has to survive past a binder for k). NOT YET
       ATTEMPTED. *)
    admit.
  - (* Or: e = EChoice x1 y1, recursive premise is on EVar x1.  x1's own
       closedness genuinely IS available "for free" from Heclosed
       (EChoice's vars_of_e0 = [x1; y1], so x1 is literally in there) --
       this case does NOT hit the free-variable/binder problem below. *)
    apply IH.
    + exact Hclosed.
    + simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
      apply Heclosed. simpl. left. reflexivity.
  - (* Select: recursive premise 2 is on rename_b (zipsubst ys zs) body, a
       branch body pulled from `brs` -- same "new syntax from the source,
       not the heap" gap as Fun, now for case branches instead of
       function bodies. NOT YET ATTEMPTED. *)
    admit.
  - (* Guess: same gap as Select, for the guessed branch body1.
       NOT YET ATTEMPTED. *)
    admit.
Admitted.

(* ==================================================================== *)
(* PIECE 6: a genuine free-variable analysis (bound-set-aware, unlike     *)
(* vars_of_b) plus program-level well-scopedness, needed to close the     *)
(* four cases PIECE 5 couldn't reach.  See PIECE 5's header note and      *)
(* THEOREM2_PROCESS_NOTES.md Sec.28 for why vars_of_b is the wrong tool.  *)
(* ==================================================================== *)

Definition remove_all (vs : list var) (l : list var) : list var :=
  fold_right (fun x acc => remove Nat.eq_dec x acc) l vs.

Lemma remove_all_in :
  forall vs l w, In w (remove_all vs l) -> In w l /\ ~ In w vs.
Proof.
  induction vs as [| v vs' IH]; intros l w H.
  - simpl in H. split; [exact H | intros []].
  - simpl in H. apply in_remove in H. destruct H as [H Hne].
    destruct (IH l w H) as [Hl Hnvs].
    split; [exact Hl | ]. intros [Heq | Hin]; [exact (Hne (eq_sym Heq)) | exact (Hnvs Hin)].
Qed.

Lemma remove_all_in_intro :
  forall vs l w, In w l -> ~ In w vs -> In w (remove_all vs l).
Proof.
  induction vs as [| v vs' IH]; intros l w Hl Hnvs.
  - simpl. exact Hl.
  - simpl. apply in_in_remove.
    + intro Heq. subst v. apply Hnvs. left. reflexivity.
    + apply IH; [exact Hl | intro H; apply Hnvs; right; exact H].
Qed.

Fixpoint free_vars_b (b : Blk) : list var :=
  match b with
  | BLet x e k => vars_of_e0 e ++ remove Nat.eq_dec x (free_vars_b k)
  | BCase x brs =>
      x :: fold_right (fun p acc => match p with (c, ps, bd) => remove_all ps (free_vars_b bd) ++ acc end) nil brs
  | BExpr e => vars_of_e0 e
  end.

(* Every heap cell ever written (let_content, a NEval_left result v, or the
   fresh singletons NL_Guess writes) is BExpr-shaped, where free_vars_b and
   vars_of_b definitionally coincide -- but ClosedHeap's own statement
   doesn't know that syntactically, so bridge with the general (always-true)
   subset direction instead of relying on any shape fact. *)
Lemma free_vars_b_subset_vars_of_b_bound :
  forall n b, blk_size b < n -> forall w, In w (free_vars_b b) -> In w (vars_of_b b).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize w H.
  destruct b as [x e k | x brs | e].
  - simpl in *. apply in_app_or in H. destruct H as [H | H].
    + right. apply in_or_app. left. exact H.
    + apply in_remove in H. destruct H as [H _].
      assert (Hn : blk_size k + 1 < n) by lia.
      assert (Hm : blk_size k < blk_size k + 1) by lia.
      right. apply in_or_app. right. apply (IHn (blk_size k + 1) Hn k Hm w H).
  - simpl in *. destruct H as [H | H]; [left; exact H | ]. right.
    revert Hsize H. induction brs as [| [[c ps] bd] brs' IHbrs]; intros Hsize H.
    + simpl in H. destruct H.
    + simpl in Hsize, H |- *. apply in_app_or in H. destruct H as [H | H].
      * apply remove_all_in in H. destruct H as [H _].
        assert (Hbd : blk_size bd + 1 < n) by lia.
        assert (Hm : blk_size bd < blk_size bd + 1) by lia.
        apply in_or_app. right. apply in_or_app. left. apply (IHn (blk_size bd + 1) Hbd bd Hm w H).
      * assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_, _, bd0) => bd0 end) + acc) 0 brs') < n)
          by lia.
        apply in_or_app. right. apply in_or_app. right. apply IHbrs; [exact Hrest | exact H].
  - simpl in *. exact H.
Qed.

Lemma free_vars_b_subset_vars_of_b :
  forall b w, In w (free_vars_b b) -> In w (vars_of_b b).
Proof.
  intros b w H.
  exact (free_vars_b_subset_vars_of_b_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) w H).
Qed.

Lemma free_vars_b_rename_subset_bound :
  forall n b, blk_size b < n ->
  forall s w, In w (free_vars_b (rename_b s b)) -> exists y, In y (free_vars_b b) /\ s y = w.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize s w Hin.
  destruct b as [x e k | x brs | e].
  - simpl in *. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + assert (Hex : exists y, In y (vars_of_e0 e) /\ s y = w).
      { destruct e as [x0 | | | x0 y0 | f args | c args]; simpl in *.
        - destruct Hin as [Hin | []]. exists x0. split; [left; reflexivity | exact Hin].
        - destruct Hin.
        - destruct Hin.
        - destruct Hin as [Hin | [Hin | []]].
          + exists x0. split; [left; reflexivity | exact Hin].
          + exists y0. split; [right; left; reflexivity | exact Hin].
        - apply in_map_iff in Hin. destruct Hin as [y0 [Heq Hiny0]]. exists y0. split; [exact Hiny0 | exact Heq].
        - apply in_map_iff in Hin. destruct Hin as [y0 [Heq Hiny0]]. exists y0. split; [exact Hiny0 | exact Heq]. }
      destruct Hex as [y [Hy Hsy]]. exists y. split; [apply in_or_app; left; exact Hy | exact Hsy].
    + apply in_remove in Hin. destruct Hin as [Hin Hne].
      assert (Hn : blk_size k + 1 < n) by lia.
      assert (Hm : blk_size k < blk_size k + 1) by lia.
      destruct (IHn (blk_size k + 1) Hn k Hm s w Hin) as [y [Hy Hsy]].
      exists y. split.
      * apply in_or_app. right. apply in_in_remove.
        -- intro Heq. subst y. exact (Hne (eq_sym Hsy)).
        -- exact Hy.
      * exact Hsy.
  - simpl in *. destruct Hin as [Hin | Hin].
    + exists x. split; [left; reflexivity | exact Hin].
    + revert Hsize Hin. induction brs as [| [[c ps] bd] brs' IHbrs]; intros Hsize Hin.
      * simpl in Hin. destruct Hin.
      * simpl in Hsize, Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        -- assert (Hbd : blk_size bd + 1 < n) by lia.
           assert (Hm : blk_size bd < blk_size bd + 1) by lia.
           apply remove_all_in in Hin. destruct Hin as [Hin Hnmap].
           destruct (IHn (blk_size bd + 1) Hbd bd Hm s w Hin) as [y [Hy Hsy]].
           exists y. split.
           ++ right. apply in_or_app. left. apply remove_all_in_intro.
              ** exact Hy.
              ** intro Hc. apply Hnmap. apply in_map_iff. exists y. split; [exact Hsy | exact Hc].
           ++ exact Hsy.
        -- assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_, _, bd0) => bd0 end) + acc) 0 brs') < n)
             by lia.
           destruct (IHbrs Hrest Hin) as [y [Hy Hsy]].
           exists y. split.
           ++ destruct Hy as [Hy | Hy]; [left; exact Hy | ]. right. apply in_or_app. right. exact Hy.
           ++ exact Hsy.
  - simpl in *.
    assert (Hex : exists y, In y (vars_of_e0 e) /\ s y = w).
    { destruct e as [x0 | | | x0 y0 | f args | c args]; simpl in *.
      - destruct Hin as [Hin | []]. exists x0. split; [left; reflexivity | exact Hin].
      - destruct Hin.
      - destruct Hin.
      - destruct Hin as [Hin | [Hin | []]].
        + exists x0. split; [left; reflexivity | exact Hin].
        + exists y0. split; [right; left; reflexivity | exact Hin].
      - apply in_map_iff in Hin. destruct Hin as [y0 [Heq Hiny0]]. exists y0. split; [exact Hiny0 | exact Heq].
      - apply in_map_iff in Hin. destruct Hin as [y0 [Heq Hiny0]]. exists y0. split; [exact Hiny0 | exact Heq]. }
    exact Hex.
Qed.

Lemma free_vars_b_rename_subset :
  forall s b w, In w (free_vars_b (rename_b s b)) -> exists y, In y (free_vars_b b) /\ s y = w.
Proof.
  intros s b w H.
  exact (free_vars_b_rename_subset_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) s w H).
Qed.

Lemma hupd_list_preserves_some :
  forall (G : NHeap) xs vs w, G w <> None -> hupd_list G xs vs w <> None.
Proof.
  intros G xs. induction xs as [| x xs' IH]; intros vs w Hw; destruct vs as [| v vs'].
  - exact Hw.
  - exact Hw.
  - exact Hw.
  - simpl. apply hupd_preserves_some. apply IH. exact Hw.
Qed.

(* Domain-monotonicity: NEval_left only ever GROWS the heap (via hupd),
   never shrinks it -- needed to carry a closedness fact established
   against an EARLIER heap (e.g. G0/G1 in NL_Select/NL_Guess, before the
   scrutinee-forcing step) across to a LATER one. Standalone and simple by
   design, unlike the closed-preservation induction. *)
Lemma NEval_left_domain_mono :
  forall P F G e G' v, NEval_left P F G e G' v -> forall w, G w <> None -> G' w <> None.
Proof.
  intros P F G e G' v H.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v0 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v0 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v0 Hrec IH
    | F0 G0 z c zs brs ys body G1 v0 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v0 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros w Hw.
  - exact Hw.
  - exact Hw.
  - apply hupd_preserves_some. exact Hw.
  - apply hupd_preserves_some. apply IH. exact Hw.
  - exact Hw.
  - exact Hw.
  - apply IH. exact Hw.
  - apply IH. apply hupd_preserves_some. exact Hw.
  - apply IH. exact Hw.
  - apply IH2. apply IH1. exact Hw.
  - apply IH2. apply hupd_list_preserves_some. apply hupd_preserves_some. apply IH1. exact Hw.
Qed.

(* Program-level well-scopedness: every free variable of a function body
   (using the REAL free_vars_b, so nested lets/cases already correctly
   exclude their own bound variables) is one of the function's own
   parameters.  This is the "genuinely new" fact PIECE 5/Sec.27 flagged --
   nothing in ProgWF/NoBareFreeOrChoiceProgWF captures it, so it's a fresh
   hypothesis, not derivable from anything already in this codebase. *)
Definition FunBodyWellScoped (P : Prog) : Prop :=
  forall f ps body, P f = Some (ps, body) -> forall w, In w (free_vars_b body) -> In w ps.

(* One more invariant NL_Fun's own case exposed as genuinely NECESSARY (not
   just a proof-technique convenience): batch_extend's Hfix precondition
   needs sigma0 to ALREADY fix s(y)/s2(y) for the two independently-chosen
   fresh renamings, but nothing about mutual_inverse/NHeapAlpha alone rules
   out an ADVERSARIAL sigma0 that happens to move a fresh location -- an
   adversarial sigma0 satisfying every OTHER hypothesis here really could
   break the reconciliation, making the statement false without this.
   Hcontain0 fixes it: sigma0's support must already avoid the region BOTH
   heaps leave undefined (so anything G_fresh, by construction outside both
   heaps' current domains, is automatically untouched by sigma0). Threaded
   as both a hypothesis and a matching conclusion conjunct so it survives
   induction the same way the "extends" conjunct does. *)
Theorem NEval_left_confluence :
  forall P F1 Gam1 e1 Gam1' v1, NEval_left P F1 Gam1 e1 Gam1' v1 ->
  forall sigma0 tau0, mutual_inverse sigma0 tau0 ->
  forall F2, F2 = map sigma0 F1 ->
  forall Gam2 e2, e2 = rename_b sigma0 e1 -> NHeapAlpha sigma0 tau0 Gam1 Gam2 ->
  (forall w, sigma0 w <> w -> Gam1 w <> None /\ Gam2 w <> None) ->
  (forall w, In w F1 -> Gam1 w <> None) -> (forall w, In w F2 -> Gam2 w <> None) ->
  forall Gam2' v2, NEval_left P F2 Gam2 e2 Gam2' v2 ->
  exists sigma tau, mutual_inverse sigma tau /\
    (forall w, sigma0 w <> w \/ Gam1 w <> None \/ Gam2 w <> None -> sigma w = sigma0 w) /\
    (forall w, sigma w <> w -> Gam1' w <> None /\ Gam2' w <> None) /\
    NHeapAlpha sigma tau Gam1' Gam2' /\ v2 = rename_b sigma v1.
Proof.
  intros P F1 Gam1 e1 Gam1' v1 H1.
  induction H1 as
    [ F0 G0 x c0 args0 Hgx0                                              (* NL_VarCons *)
    | F0 G0 x Hgx0                                                       (* NL_VarSelf *)
    | F0 G0 x Hgx0                                                       (* NL_VarFree *)
    | F0 G0 x e G1 v Hnf Hgx0 Hnc Hne Hnfr Hrec IH                       (* NL_VarExp *)
    | F0 G0                                                              (* NL_ValFree *)
    | F0 G0 c0 args0                                                     (* NL_ValCon *)
    | F0 G0 G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH    (* NL_Fun *)
    | F0 G0 G1 x e k v Hxfresh Hrec IH                                  (* NL_Let *)
    | F0 G0 x y G1 v Hrec IH                                            (* NL_Or *)
    | F0 G0 x c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2     (* NL_Select *)
    | F0 G0 x G1 x' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlenws HND Hfresh2 Hrec2 IH2 ]
                                                                          (* NL_Guess *)
    ; intros sigma0 tau0 Hmi0 F2 HF2eq Gam2 e2 He2 Halpha0 Hcontain0 HFdom1 HFdom2 Gam2' v2 H2.
  - (* NL_VarCons *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (BExpr (ECon c0 (map sigma0 args0)))).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon _]]]]] ] ] ].
    + rewrite Hgamx in Hc1. injection Hc1 as Hc1. subst v2. subst Gam2'.
      exists sigma0, tau0. split; [exact (conj Hst0 Hts0) | ].
      split; [intros w _; reflexivity | ].
      split; [exact Hcontain0 | ].
      split; [exact Halpha0 | reflexivity].
    + rewrite Hgamx in Hc2. discriminate Hc2.
    + rewrite Hgamx in Hc3. discriminate Hc3.
    + rewrite Hgamx in Hc4. injection Hc4 as Hc4. subst e0.
      exfalso. exact (Hnecon c0 (map sigma0 args0) eq_refl).
  - (* NL_VarSelf *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (BExpr (EVar (sigma0 x)))).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon [Hnevar _]]]]]] ] ] ].
    + exfalso. congruence.
    + subst v2. subst Gam2'. exists sigma0, tau0.
      split; [exact (conj Hst0 Hts0) | ].
      split; [intros w _; reflexivity | ].
      split; [exact Hcontain0 | ].
      split; [exact Halpha0 | reflexivity].
    + exfalso. congruence.
    + exfalso. congruence.
  - (* NL_VarFree *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (BExpr EFree)).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon [Hnevar [Hnefree _]]]]]]] ] ] ].
    + exfalso. congruence.
    + exfalso. congruence.
    + subst v2. exists sigma0, tau0.
      split; [exact (conj Hst0 Hts0) | ].
      split; [intros w _; reflexivity | ].
      split.
      * intros w Hw. destruct (Hcontain0 w Hw) as [Hw1 Hw2].
        split; [exact (hupd_preserves_some G0 x _ w Hw1) | subst Gam2'; exact (hupd_preserves_some Gam2 (sigma0 x) _ w Hw2)].
      * split.
        -- subst Gam2'. intro w.
           assert (Hpt := NHeapAlpha_hupd sigma0 tau0 (conj Hst0 Hts0) G0 Gam2 Halpha0 x (BExpr (EVar x))).
           simpl in Hpt. exact (Hpt w).
        -- reflexivity.
    + exfalso. congruence.
  - (* NL_VarExp *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (rename_b sigma0 e)).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    assert (Hnc' : forall c args, rename_b sigma0 e <> BExpr (ECon c args))
      by (apply rename_b_not_econ; exact Hnc).
    assert (Hne' : rename_b sigma0 e <> BExpr (EVar (sigma0 x)))
      by (apply rename_b_not_evar; [exact (mutual_inverse_injective_l sigma0 tau0 (conj Hst0 Hts0)) | exact Hne]).
    assert (Hnfr' : rename_b sigma0 e <> BExpr EFree) by (apply rename_b_not_efree; exact Hnfr).
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon2 [Hnevar2 [Hnefree2 [Hrec2 HG2eq]]]]]]]]] ] ].
    + exfalso. rewrite Hv2eq in Hc1. rewrite Hgamx in Hc1. injection Hc1 as Hc1. exact (Hnc' cc aa Hc1).
    + exfalso. rewrite Hgamx in Hc2. injection Hc2 as Hc2. exact (Hne' Hc2).
    + exfalso. rewrite Hgamx in Hc3. injection Hc3 as Hc3. exact (Hnfr' Hc3).
    + rewrite Hgamx in Hc4. injection Hc4 as Hc4. subst e0.
      assert (HFdom1' : forall w, In w (x :: F0) -> G0 w <> None).
      { intros w Hw. destruct Hw as [Hw | Hw]; [subst w; rewrite Hgx0; discriminate | exact (HFdom1 w Hw)]. }
      assert (HFdom2' : forall w, In w (sigma0 x :: map sigma0 F0) -> Gam2 w <> None).
      { intros w Hw. destruct Hw as [Hw | Hw]; [subst w; rewrite Hgamx; discriminate | exact (HFdom2 w Hw)]. }
      destruct (IH sigma0 tau0 (conj Hst0 Hts0) (sigma0 x :: map sigma0 F0) eq_refl Gam2
                  (rename_b sigma0 e) eq_refl Halpha0 Hcontain0 HFdom1' HFdom2' G1' v2 Hrec2)
        as [sigma [tau [Hmisig [Hext [Hcont [Halpha Heqv]]]]]].
      exists sigma, tau. split; [exact Hmisig | ].
      split; [exact Hext | ].
      assert (Hxne : G0 x <> None) by (rewrite Hgx0; discriminate).
      assert (Hxeq : sigma x = sigma0 x) by exact (Hext x (or_intror (or_introl Hxne))).
      split.
      { intros w Hw. destruct (Hcont w Hw) as [Hw1 Hw2].
        split; [exact (hupd_preserves_some G1 x v w Hw1) | subst Gam2'; exact (hupd_preserves_some G1' (sigma0 x) v2 w Hw2)]. }
      split.
      * subst Gam2'.
        assert (Hpt := NHeapAlpha_hupd sigma tau Hmisig G1 G1' Halpha x v).
        rewrite Hxeq in Hpt. rewrite <- Heqv in Hpt. exact Hpt.
      * rewrite Heqv. reflexivity.
  - (* NL_ValFree *)
    subst e2. subst F2. simpl in H2.
    remember (BExpr EFree) as target eqn:Ht.
    revert Ht.
    destruct H2 as
      [ F1a G1a z c a Hz | F1a G1a z Hz | F1a G1a z Hz | F1a G1a z e0 G1b v0 Hz1 Hz2 Hz3 Hz4 Hz5 HrecA
      | F1a G1a | F1a G1a c a
      | F1a G1a G1b f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh HrecB
      | F1a G1a G1b z e0 k v1 Hzf HrecC
      | F1a G1a x1 y1 G1b v1 HrecD
      | F1a G1a z c a brs ys body G1b v1 G2 HrecE1 HIn Hlen HrecE2
      | F1a G1a z G1b z' c1 ys1 body1 brs G2 v1 ws HrecF1 Hhd Hlen HND Hfr HrecF2
      ]; intros Ht; try discriminate Ht.
    exists sigma0, tau0.
    split; [exact Hmi0 | ].
    split; [intros w _; reflexivity | ].
    split; [exact Hcontain0 | ].
    split; [exact Halpha0 | reflexivity].
  - (* NL_ValCon *)
    subst e2. subst F2. simpl in H2.
    remember (BExpr (ECon c0 (map sigma0 args0))) as target eqn:Ht.
    revert Ht.
    destruct H2 as
      [ F1a G1a z c a Hz | F1a G1a z Hz | F1a G1a z Hz | F1a G1a z e0 G1b v0 Hz1 Hz2 Hz3 Hz4 Hz5 HrecA
      | F1a G1a | F1a G1a c a
      | F1a G1a G1b f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh HrecB
      | F1a G1a G1b z e0 k v1 Hzf HrecC
      | F1a G1a x1 y1 G1b v1 HrecD
      | F1a G1a z c a brs ys body G1b v1 G2 HrecE1 HIn Hlen HrecE2
      | F1a G1a z G1b z' c1 ys1 body1 brs G2 v1 ws HrecF1 Hhd Hlen HND Hfr HrecF2
      ]; intros Ht; try discriminate Ht.
    exists sigma0, tau0.
    split; [exact Hmi0 | ].
    split; [intros w _; reflexivity | ].
    split; [exact Hcontain0 | ].
    split; [exact Halpha0 | simpl; exact Ht].
  - (* NL_Fun *)
    subst e2. subst F2.
    assert (He2fun : rename_b sigma0 (BExpr (EFun f args)) = BExpr (EFun f (map sigma0 args)))
      by reflexivity.
    rewrite He2fun in H2.
    destruct (NEval_left_fun_shape P (map sigma0 F0) Gam2 f (map sigma0 args) Gam2' v2 H2)
      as [ps2 [body2 [s2 [HPf2 [Hlen2 [Hinj2 [Hmatch2 [Hfresh2 Hrec2]]]]]]]].
    assert (Hpb : Some (ps2, body2) = Some (ps, body)) by (rewrite <- HPf; symmetry; exact HPf2).
    injection Hpb as Hpseq Hbodyeq. subst ps2 body2.
    (* Parameters already agree via sigma0 -- s2 x = sigma0 (s x) -- no
       reconciliation needed there, only for body's OTHER variables. *)
    assert (Hparam : forall x, In x ps -> s2 x = sigma0 (s x)).
    { intros x Hx. apply In_nth_error in Hx. destruct Hx as [i Hi].
      assert (Hib : i < length ps) by (eapply nth_error_Some; congruence).
      assert (Hib2 : i < length args) by (rewrite <- Hlen; exact Hib).
      destruct (nth_error args i) as [a | ] eqn:Ha.
      2: { exfalso. eapply nth_error_Some; [exact Hib2 | exact Ha]. }
      assert (Ha2 : nth_error (map sigma0 args) i = Some (sigma0 a)) by (apply map_nth_error; exact Ha).
      assert (Hsxa : s x = a) by exact (Hmatch i x a Hi Ha).
      assert (Hs2xa : s2 x = sigma0 a) by exact (Hmatch2 i x (sigma0 a) Hi Ha2).
      rewrite Hsxa. exact Hs2xa. }
    set (vs := nodup Nat.eq_dec (filter (fun y => if in_dec Nat.eq_dec y ps then false else true)
                 (vars_of_b body))).
    set (ps_pairs := map (fun y => (s y, s2 y)) vs).
    assert (Hvsnodup : NoDup vs) by (unfold vs; apply NoDup_nodup).
    assert (Hvsnotps : forall y, In y vs -> ~ In y ps).
    { intros y Hy. unfold vs in Hy. apply nodup_In in Hy. apply filter_In in Hy. destruct Hy as [_ Hy].
      destruct (in_dec Nat.eq_dec y ps) as [Hin | Hnin]; [discriminate Hy | exact Hnin]. }
    assert (Hfsteq : map fst ps_pairs = map s vs) by (unfold ps_pairs; rewrite map_map; reflexivity).
    assert (Hsndeq : map snd ps_pairs = map s2 vs) by (unfold ps_pairs; rewrite map_map; reflexivity).
    assert (HNDfst : NoDup (map fst ps_pairs))
      by (rewrite Hfsteq; exact (NoDup_map_inj var var s vs Hinj Hvsnodup)).
    assert (HNDsnd : NoDup (map snd ps_pairs))
      by (rewrite Hsndeq; exact (NoDup_map_inj var var s2 vs Hinj2 Hvsnodup)).
    assert (HfixBE : forall w, In w (map fst ps_pairs) \/ In w (map snd ps_pairs) -> sigma0 w = w).
    { intros w Hw. destruct Hw as [Hw | Hw].
      - rewrite Hfsteq in Hw. apply in_map_iff in Hw. destruct Hw as [y [Hsy Hiny]]. subst w.
        exact (Hcontain_None_fixed sigma0 G0 Gam2 Hcontain0 (s y) (or_introl (Hfresh y (Hvsnotps y Hiny)))).
      - rewrite Hsndeq in Hw. apply in_map_iff in Hw. destruct Hw as [y [Hsy Hiny]]. subst w.
        exact (Hcontain_None_fixed sigma0 G0 Gam2 Hcontain0 (s2 y) (or_intror (Hfresh2 y (Hvsnotps y Hiny)))). }
    destruct (batch_extend (length ps_pairs) ps_pairs (Nat.le_refl _) HNDfst HNDsnd sigma0 tau0 Hmi0 HfixBE)
      as [sigma [tau [Hmisig [Hrealizes Houtside]]]].
    (* A parameter's own image s(x) can never collide with some OTHER
       position's s2(y): assuming it did, D2's freshness + Hcontain_None_
       fixed pins sigma0(s2 y)=s2 y, substituting gives sigma0(s x)=s x;
       combined with the independent parameter fact s2 x = sigma0(s x),
       that forces s2 x = s x = s2 y, and s2's own injectivity then forces
       x = y -- contradicting x in ps, y not in ps. *)
    assert (Houtps : forall x, In x ps -> sigma (s x) = s2 x).
    { intros x Hx.
      assert (Hout1 : ~ In (s x) (map fst ps_pairs)).
      { rewrite Hfsteq. intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hsy Hiny]].
        assert (Hxy : x = y) by exact (Hinj x y (eq_sym Hsy)). subst y. exact (Hvsnotps x Hiny Hx). }
      assert (Hout2 : ~ In (s x) (map snd ps_pairs)).
      { rewrite Hsndeq. intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hsy Hiny]].
        assert (Hynotps : ~ In y ps) by exact (Hvsnotps y Hiny).
        assert (Hfresh2y : Gam2 (s2 y) = None) by exact (Hfresh2 y Hynotps).
        assert (Hfix2y : sigma0 (s2 y) = s2 y)
          by exact (Hcontain_None_fixed sigma0 G0 Gam2 Hcontain0 (s2 y) (or_intror Hfresh2y)).
        assert (Heq1 : sigma0 (s x) = s2 y) by (rewrite <- Hsy; exact Hfix2y).
        assert (Heq2 : s2 x = sigma0 (s x)) by exact (Hparam x Hx).
        assert (Heq3 : s2 x = s2 y) by (rewrite Heq2; exact Heq1).
        assert (Hxy : x = y) by exact (Hinj2 x y Heq3).
        rewrite Hxy in Hx. exact (Hynotps Hx). }
      rewrite (Houtside (s x) Hout1 Hout2). symmetry. exact (Hparam x Hx). }
    assert (Hnonparam : forall y, In y vs -> sigma (s y) = s2 y).
    { intros y Hy. apply Hrealizes. unfold ps_pairs. apply in_map_iff. exists y. split; [reflexivity | exact Hy]. }
    assert (Hagree : forall w, In w (vars_of_b body) -> sigma (s w) = s2 w).
    { intros w Hw. destruct (in_dec Nat.eq_dec w ps) as [Hin | Hnin].
      - exact (Houtps w Hin).
      - assert (Hwvs : In w vs).
        { unfold vs. apply nodup_In. apply filter_In. split; [exact Hw | ].
          destruct (in_dec Nat.eq_dec w ps) as [Hin' | Hnin']; [exfalso; exact (Hnin Hin') | reflexivity]. }
        exact (Hnonparam w Hwvs). }
    assert (Hfinal : rename_b sigma (rename_b s body) = rename_b s2 body).
    { rewrite (rename_b_comp sigma s body). exact (rename_b_congr body (fun w => sigma (s w)) s2 Hagree). }
    (* F0 avoids the pairs list too, so sigma agrees with sigma0 on all of
       it -- this closes what was flagged last session as the blocking gap.
       The s(y) side is clean (F0 subset dom(G0), s(y) fresh w.r.t. G0, same
       heap).  The s2(y) side needs w in dom(Gam2) for w in F0, which the
       NEWLY-added HFdom1/HFdom2 don't give DIRECTLY (they're about F0/G0
       and map-sigma0-F0/Gam2 respectively, not F0/Gam2 mixed) -- resolved
       by casing on whether sigma0 fixes w: if not, Hcontain0 gives
       Gam2 w<>None directly; if so, HFdom2 (at sigma0 w = w) gives it. *)
    assert (HF0dom2 : forall w, In w F0 -> Gam2 (sigma0 w) <> None)
      by (intros w Hw; apply HFdom2; apply in_map; exact Hw).
    assert (HFsigmaeq : forall w, In w F0 -> sigma w = sigma0 w).
    { intros w Hw.
      assert (Hout1 : ~ In w (map fst ps_pairs)).
      { rewrite Hfsteq. intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hsy Hiny]].
        assert (HGam1w : G0 w <> None) by exact (HFdom1 w Hw).
        assert (Hfreshy : G0 (s y) = None) by exact (Hfresh y (Hvsnotps y Hiny)).
        rewrite <- Hsy in HGam1w. exact (HGam1w Hfreshy). }
      assert (Hout2 : ~ In w (map snd ps_pairs)).
      { rewrite Hsndeq. intro Hc. apply in_map_iff in Hc. destruct Hc as [y [Hsy Hiny]].
        assert (Hynotps : ~ In y ps) by exact (Hvsnotps y Hiny).
        assert (Hfresh2y : Gam2 (s2 y) = None) by exact (Hfresh2 y Hynotps).
        assert (HGam2w : Gam2 w <> None).
        { destruct (Nat.eq_dec (sigma0 w) w) as [Heqfix | Hneqfix].
          - rewrite <- Heqfix. exact (HF0dom2 w Hw).
          - exact (proj2 (Hcontain0 w Hneqfix)). }
        rewrite <- Hsy in HGam2w. exact (HGam2w Hfresh2y). }
      exact (Houtside w Hout1 Hout2). }
    assert (HmapFeq : map sigma F0 = map sigma0 F0) by (apply map_ext_in; exact HFsigmaeq).
    (* Where it STOPS: applying the outer IH to body's own continuation
       ALSO needs NHeapAlpha sigma tau G0 Gam2 (sigma/tau, not sigma0/tau0
       -- G0/Gam2 themselves don't change here, only the renaming pair
       does).  batch_extend's own "outside ps_pairs" guarantee is stated
       ONLY for sigma' (Houtside above), not tau'.  A genuine FIFTH gap.

       Traced this one further too, and it's DEEPER than "just add a
       symmetric tau'-outside conjunct to batch_extend" -- rewriting
       NHeapAlpha via mutual_inverse into the tau-free form (forall z,
       Gam2 (sigma z) = option_map (rename_b sigma) (G0 z), quantifying
       over the SOURCE location instead of using tau to look one up)
       sidesteps needing anything about tau' specifically, but for z
       OUTSIDE ps_pairs's domain+range (where sigma z = sigma0 z, from
       Houtside alone) it still needs option_map (rename_b sigma0) (G0 z)
       = option_map (rename_b sigma) (G0 z), i.e. sigma and sigma0 must
       agree on every variable G0's OWN STORED VALUE at z mentions -- true
       if that content's variables stay inside ps_pairs's complement too,
       which needs G0's stored values to never reference the fresh
       locations s(y)/s2(y) as VALUES even though they're fresh as KEYS
       (G0 (s y) = None only says s(y) isn't currently a heap KEY, says
       nothing about whether some OTHER cell's stored content happens to
       mention it as a variable).  That's a genuinely different kind of
       freshness than anything tracked so far in this file -- a heap/value
       well-formedness invariant, not a fact about renamings.

       SHARPENED (checked, not just guessed): this is real and semantically
       expected -- in a properly-scoped, properly-executing program, a heap
       cell should never reference an undefined location, since the only
       rule that ever writes a NEW cell (NL_Let) stores it at a FRESH x
       whose OWN content's free variables must already be bound (guaranteed
       by the SOURCE program being well-scoped, propagated forward as the
       heap grows) -- but checked ProgWF and NoBareFreeOrChoiceProgWF (the
       only two well-formedness definitions in this whole codebase) and
       NEITHER captures this; NL_Let's own rule has exactly one heap
       premise (G x = None, the new cell is fresh) and no premise at all
       constraining e's own free variables.  So this really is a genuinely
       NEW invariant to build, not something already implied by anything
       in scope -- but now it has a precise shape, not just a described
       failure case: (i) a "closed heap" predicate (forall z b, G z=Some b
       -> forall w, In w (vars_of_b b) -> G w<>None -- every stored value's
       own references are themselves bound); (ii) a preservation lemma
       that NEval_left maintains it; (iii) confirming the top-level entry
       point this file's own corollary/theorem2 eventually gets invoked
       from starts closed (plausible almost by construction -- a real
       evaluation starts from an empty/minimal heap -- but not yet
       checked at the actual call site).  NOT YET ATTEMPTED. *)
    admit.
  - (* NL_Let: x is a FIXED source-level name (not freshly chosen the way
       NL_Fun/NL_Guess pick one), so this threads sigma0 through unchanged,
       extending the heap at (sigma0 x) on D2's side via NHeapAlpha_hupd and
       let_content_rename. *)
    subst e2. simpl in H2.
    remember (BLet (sigma0 x) (rename_e0 sigma0 e) (rename_b sigma0 k)) as target eqn:Ht.
    revert Ht HF2eq.
    destruct H2 as
      [ F1a G1a z c a Hz | F1a G1a z Hz | F1a G1a z Hz | F1a G1a z e0 G1b v0 Hz1 Hz2 Hz3 Hz4 Hz5 HrecA
      | F1a G1a | F1a G1a c a
      | F1a G1a G1b f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh HrecB
      | F1a G1a G1b z e0 k1 vres Hzf HrecC
      | F1a G1a x1 y1 G1b v1 HrecD
      | F1a G1a z c a brs ys body G1b v1 G2 HrecE1 HIn Hlen HrecE2
      | F1a G1a z G1b z' c1 ys1 body1 brs G2 v1 ws HrecF1 Hhd Hlen HND Hfr HrecF2
      ]; intros Ht HF2eq; try discriminate Ht.
    injection Ht as Htz Hte0 Htk1. subst z e0 k1.
    assert (HeqGam2'' : hupd G1a (sigma0 x) (let_content (sigma0 x) (rename_e0 sigma0 e))
                         = hupd G1a (sigma0 x) (rename_b sigma0 (let_content x e)))
      by (rewrite (let_content_rename sigma0 x e); reflexivity).
    rewrite HeqGam2'' in HrecC.
    assert (Hpt := NHeapAlpha_hupd sigma0 tau0 Hmi0 G0 G1a Halpha0 x (let_content x e)).
    assert (Hcontain0' : forall w, sigma0 w <> w ->
              hupd G0 x (let_content x e) w <> None /\
              hupd G1a (sigma0 x) (rename_b sigma0 (let_content x e)) w <> None).
    { intros w Hw. destruct (Hcontain0 w Hw) as [Hw1 Hw2].
      split; [exact (hupd_preserves_some G0 x _ w Hw1) | exact (hupd_preserves_some G1a (sigma0 x) _ w Hw2)]. }
    assert (HFdom1' : forall w, In w F0 -> hupd G0 x (let_content x e) w <> None)
      by (intros w Hw; exact (hupd_preserves_some G0 x _ w (HFdom1 w Hw))).
    assert (HFdom2' : forall w, In w F1a -> hupd G1a (sigma0 x) (rename_b sigma0 (let_content x e)) w <> None)
      by (intros w Hw; exact (hupd_preserves_some G1a (sigma0 x) _ w (HFdom2 w Hw))).
    destruct (IH sigma0 tau0 Hmi0 F1a HF2eq (hupd G1a (sigma0 x) (rename_b sigma0 (let_content x e)))
                (rename_b sigma0 k) eq_refl Hpt Hcontain0' HFdom1' HFdom2' G1b vres HrecC)
      as [sigma [tau [Hmisig [Hext [Hcont [Halpha Heqv]]]]]].
    exists sigma, tau. split; [exact Hmisig | ].
    split.
    { intros w Hw. apply Hext. destruct Hw as [Hw | [Hw | Hw]]; [left; exact Hw | | ].
      - right; left. intro Hc. apply Hw. unfold hupd in Hc. unfold hupd.
        destruct (Nat.eqb w x); [discriminate Hc | exact Hc].
      - right; right. intro Hc. apply Hw. unfold hupd in Hc. unfold hupd.
        destruct (Nat.eqb w (sigma0 x)); [discriminate Hc | exact Hc]. }
    split; [exact Hcont | ].
    split; [exact Halpha | exact Heqv].
  - (* NL_Or: threads straight through via the IH on the EVar sub-derivation,
       no fresh renaming involved at all. *)
    subst e2. simpl in H2.
    remember (BExpr (EChoice (sigma0 x) (sigma0 y))) as target eqn:Ht.
    revert Ht HF2eq.
    destruct H2 as
      [ F1a G1a z c a Hz | F1a G1a z Hz | F1a G1a z Hz | F1a G1a z e0 G1b v0 Hz1 Hz2 Hz3 Hz4 Hz5 HrecA
      | F1a G1a | F1a G1a c a
      | F1a G1a G1b f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh HrecB
      | F1a G1a G1b z e0 k v1 Hzf HrecC
      | F1a G1a x1 y1 G1b v1 HrecD
      | F1a G1a z c a brs ys body G1b v1 G2 HrecE1 HIn Hlen HrecE2
      | F1a G1a z G1b z' c1 ys1 body1 brs G2 v1 ws HrecF1 Hhd Hlen HND Hfr HrecF2
      ]; intros Ht HF2eq; try discriminate Ht.
    injection Ht as Htx Hty. subst x1 y1.
    destruct (IH sigma0 tau0 Hmi0 F1a HF2eq G1a (BExpr (EVar (sigma0 x))) eq_refl Halpha0 Hcontain0
                HFdom1 HFdom2 G1b v1 HrecD)
      as [sigma [tau [Hmisig [Hext [Hcont [Halpha Heqv]]]]]].
    exists sigma, tau. split; [exact Hmisig | ].
    split; [exact Hext | ].
    split; [exact Hcont | ].
    split; [exact Halpha | exact Heqv].
  - (* NL_Select: turns out to be genuinely as hard as Fun/Guess, not a quick
       win -- BCase's shape-inversion (NEval_left_bcase_shape,
       curry_test_leftmost.v) is a TWO-way disjunction (Select-shape vs.
       Guess-shape, since NL_Guess ALSO concludes on BCase x brs), so ruling
       out D2 independently picking Guess needs IH1 (on the scrutinee-
       forcing sub-derivation Hrec1) applied FIRST, to show D2's own
       x-forcing is provably ECon-shaped too (v2's shape is pinned by
       rename_b's shape-preservation, via IH1's own v2=rename_b sigma v1
       conjunct) -- only THEN can NEval_left_bcase_shape's Guess branch be
       discharged.  A proper two-step argument, matching the same level of
       intricacy as curry_test_leftmost.v's own G_CaseChoice/G_CaseFun
       proofs (100+ lines each).  NOT YET ATTEMPTED. *)
    admit.
  - (* NL_Guess: the other genuine nondeterminism source (fresh ws vs ws'),
       needs batch_extend the same way NL_Fun does -- NOT YET ATTEMPTED. *)
    admit.
Admitted.

(* The corollary that's actually needed at G_CaseFun (curry_test_leftmost.v
   :8350-8356): two derivations of the literal SAME expression from the
   literal SAME heap, instantiating sigma0 := tau0 := id. *)
(* The (forall w, In w F -> Gam w <> None) hypothesis is trivially satisfied
   whenever F starts at nil, which is how every actual use of NEval_left in
   this codebase invokes it (guard lists only ever grow via NL_VarExp's own
   x::F from a nil start) -- kept general here rather than hardcoding F:=nil,
   so callers with a nonempty guard just supply the (typically easy) proof. *)
Corollary NEval_left_self_confluence :
  forall P F Gam e Gam1 v1, NEval_left P F Gam e Gam1 v1 ->
  (forall w, In w F -> Gam w <> None) ->
  forall Gam2 v2, NEval_left P F Gam e Gam2 v2 ->
  exists sigma tau, mutual_inverse sigma tau /\ NHeapAlpha sigma tau Gam1 Gam2 /\ v2 = rename_b sigma v1.
Proof.
  intros P F Gam e Gam1 v1 H1 HFdom Gam2 v2 H2.
  destruct (NEval_left_confluence P F Gam e Gam1 v1 H1 (fun w => w) (fun w => w) mutual_inverse_id
              F (eq_sym (map_id F)) Gam e (eq_sym (rename_b_id e)) (NHeapAlpha_refl Gam)
              (fun w Hw => match Hw eq_refl with end)
              HFdom HFdom
              Gam2 v2 H2)
    as [sigma [tau [Hmi [_ [_ [Halpha Heq]]]]]].
  exists sigma, tau. split; [exact Hmi | split; [exact Halpha | exact Heq]].
Qed.
