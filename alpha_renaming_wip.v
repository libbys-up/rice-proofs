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
(* ===== CURRENT STATUS (Sec.39 session, supersedes everything below): *)
(* NEval_left_confluence uses BlkAlpha (PIECE 7) in place of the literal   *)
(* "e2 = rename_b sigma0 e1" hypothesis; the nine-piece pa/PaInv/          *)
(* sigma0_TOP apparatus is GONE (Sec.36); Hcontain0 is GONE ENTIRELY       *)
(* (Sec.39 -- turned out to be pure dead weight once splice_sigma removed  *)
(* its only real use, fixed-point facts for a swap); and the "extends"     *)
(* conjunct is simplified to its OWN single live disjunct, "Gam1 w<>None   *)
(* -> sigma w = sigma0 w" (Sec.39 -- the sigma0-already-moved and Gam2-    *)
(* defined disjuncts were NEVER actually used by any of the 11 cases,      *)
(* confirmed by grepping every actual application, not just assumed).      *)
(* PIECE 1a-bis: splice_sigma/splice_tau (near ext_sigma/ext_tau) extend a *)
(* bijection by ONE new edge with NO fixed-point precondition on EITHER    *)
(* endpoint -- a strict generalization of ext_sigma's own swap, needed     *)
(* because NL_Let's own fresh pick can already be moved by an ancestor.    *)
(* NHeapAlpha_splice (near NEval_left_blet_shape) is the matching heap-    *)
(* level lemma.  Both zero admits, fully standalone.                       *)
(* RESULT: 9 of 11 constructors are fully Qed'd -- VarCons, VarSelf,       *)
(* VarFree, VarExp, ValFree, ValCon, Fun, Or, AND NOW Let.  Only TWO        *)
(* admits remain: NL_Select, NL_Guess (mechanism understood -- BCase's own *)
(* shape-inversion is a two-way disjunction with Guess, needing IH1 first  *)
(* to rule out D2 picking the other shape, plus a BrsAlpha-lookup lemma    *)
(* not yet built; NL_Guess additionally needs a BATCH version of splice    *)
(* for its own ws list -- not yet attempted).  File compiles clean end to  *)
(* end (`coqc`), zero unplanned admits, exactly these two.  theorem2       *)
(* itself is UNCHANGED (still its one original admit) -- PIECE 8's own     *)
(* wiring into curry_test_leftmost.v is still the next step, blocked on    *)
(* Select/Guess closing first (the corollary NEval_left_self_confluence,   *)
(* which theorem2's admit actually calls, needs NEval_left_confluence      *)
(* fully Qed'd, not just NL_Fun's own case). See THEOREM2_PROCESS_NOTES.md *)
(* Sec.36-39 for the full history of how this design was reached.         *)
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
(*      (PIECE 5).  Tracing by hand before coding turned up a genuine          *)
(*      simplification: the four "heap-pointer-mediated" constructors         *)
(*      (VarCons/VarSelf/VarFree/VarExp) get closedness of whatever they      *)
(*      find "for free" from ClosedHeap G plus the rule's own G x = Some e    *)
(*      premise -- the very existence of the given derivation already forces  *)
(*      it, no separate input needed.  That, plus ValFree/ValCon/Or, closed    *)
(*      7 of 11 cases outright and compiled clean on the FIRST try.  The       *)
(*      remaining 4 (Let/Fun/Select/Guess) all "reveal brand-new syntax" (a    *)
(*      whole Blk term pulled in from the program or from e's own structure,   *)
(*      not reached via a heap pointer) and hit a SHARPER version of the same  *)
(*      fifth gap: vars_of_b conflates a term's genuinely free variables with  *)
(*      ones a LET/CASE inside that very term binds for itself (vars_of_b     *)
(*      (BLet z EFree (EVar z)) = [z;z], yet that term is closed under the     *)
(*      EMPTY heap).                                                          *)
(*                                                                            *)
(*      CONTINUED AGAIN (same session): built PIECE 6 to close all 4 -- the    *)
(*      real free_vars_b (bound-set-aware, unlike vars_of_b), plus            *)
(*      free_vars_b_rename_subset (renaming/substitution never CREATES new     *)
(*      free variables beyond the image of the old ones -- true for ANY s,     *)
(*      no injectivity needed, since capture can only LOSE apparent free       *)
(*      vars, never add them), NEval_left_domain_mono (heaps only grow, never   *)
(*      shrink -- needed to carry a closedness fact from an earlier heap        *)
(*      across to a later one in Select/Guess), and FunBodyWellScoped (the      *)
(*      well-scopedness fact this codebase never had).  Reordered PIECE 6      *)
(*      ahead of PIECE 5 and restated NEval_left_closed_preserved using         *)
(*      free_vars_b for e's own closedness (vars_of_b stayed for v's, since     *)
(*      v is always one of the 3 terminal ECon/EVar/Free shapes, where the      *)
(*      two coincide anyway, and vars_of_b's STRONGER guarantee is what         *)
(*      VarExp's own hupd step actually needs).  Result: all 11 cases close,    *)
(*      NEval_left_closed_preserved is fully Qed'd, zero admits.  Only NL_Fun   *)
(*      needed FunBodyWellScoped; Let/Select/Guess needed only free_vars_b's    *)
(*      own bound-set tracking plus (Select/Guess) domain-mono to bridge        *)
(*      across the scrutinee-forcing step.  Six small helper lemmas along the   *)
(*      way: let_content_vars, free_vars_b_bcase_branch, hd_error_in,           *)
(*      zipsubst_in/zipsubst_notin, hupd_list_map_self/hupd_list_notin.         *)
(*   4. Fed NEval_left_closed_preserved back into NL_Fun's fifth gap --         *)
(*      DONE, the fifth gap is genuinely CLOSED.  Threading ClosedHeap Gam1/    *)
(*      FunBodyWellScoped P/e1's own free_vars_b-closedness through ALL 11      *)
(*      cases of NEval_left_confluence (mirroring PIECE 5's own per-case        *)
(*      derivations almost verbatim: VarExp/Or/Let each reuse exactly the       *)
(*      technique PIECE 5 already worked out for their own cases) let NL_Fun's  *)
(*      own case build NHeapAlpha sigma tau G0 Gam2 outright and it compiled    *)
(*      clean on the FIRST try -- confirming the fifth gap's diagnosis (G0's    *)
(*      own stored values never reference the fresh locations as VALUES) was    *)
(*      exactly right, and ClosedHeap was exactly the missing piece. Needed     *)
(*      one further addition beyond PIECE 5/6: batch_extend itself gained a     *)
(*      4th conjunct (sigma' keeps ps's whole domain+range closed under         *)
(*      itself, not just fixed OUTSIDE it -- proved via a new cyc_sigma_in      *)
(*      lemma, a rotation never leaves its own list), needed for the "z is a    *)
(*      pure sink" case (z in ps_pairs's range but not its domain) where        *)
(*      nothing else pins down where sigma sends it.                           *)
(*                                                                              *)
(*      A SIXTH gap surfaced immediately behind the fifth, found only once     *)
(*      NHeapAlpha sigma tau G0 Gam2 was in hand and the outer IH's remaining   *)
(*      hypotheses needed supplying: IH also needs "Hcontain0 for sigma" --     *)
(*      forall w, sigma w<>w -> G0 w<>None /\ Gam2 w<>None -- and this is       *)
(*      FALSE, not just unproven: sigma is REQUIRED to move every s(y) to      *)
(*      s2(y) (that's Hrealizes/Hnonparam, load-bearing for Hfinal itself),     *)
(*      yet G0 (s y) = None (Hfresh) and Gam2 (s y) = None (derived, same       *)
(*      technique as the fifth gap's own G0-side reasoning) -- sigma is         *)
(*      forced to move EXACTLY the locations both heaps leave undefined, the    *)
(*      one thing this hypothesis forbids. Independent of anything about       *)
(*      ClosedHeap/free_vars_b -- this was ALWAYS going to block NL_Fun's own   *)
(*      case, just not reached until the fifth gap stopped hiding it. Likely    *)
(*      resolution: Hcontain0 (added as "correction (c)" several sessions ago)  *)
(*      is stronger than its real job needs -- it only has to license           *)
(*      Hcontain_None_fixed at whichever SPECIFIC fresh locations a DEEPER      *)
(*      NL_Fun/NL_Guess call picks, not hold unconditionally for every w --     *)
(*      but weakening it correctly, without re-breaking the 8 cases already     *)
(*      threaded through it (a FOURTH re-verification pass), needs its own      *)
(*      careful trace-first pass. See NL_Fun's own in-proof comment for the     *)
(*      precise stall point.                                                   *)
(*                                                                              *)
(*      TRACED FURTHER (this session, "let's trace the weakened form"): the     *)
(*      natural fix -- thread a growing "reserved region" D (Hcontain0         *)
(*      becomes "~In w D -> ...", D grows by ps_pairs at Fun/Guess, the         *)
(*      conclusion existentially produces its own D' >= D) -- DOES work, and    *)
(*      elegantly resolves a SECOND issue it surfaced along the way: a body-    *)
(*      internal variable inside a NEVER-TAKEN case branch can have its fresh   *)
(*      location go permanently unbound, so the output "both heaps defined"    *)
(*      conjunct can't honestly promise anything about it -- D' (>= ps_pairs)   *)
(*      simply exempts it. But establishing Hfix at THIS level still needs      *)
(*      "s(y) is outside D" in the first place, and s comes from NL_Fun's own   *)
(*      rule (curry_test_leftmost.v), constrained only by injective s and       *)
(*      Hfresh (fresh w.r.t. the CURRENT heap) -- nothing stops s(y) from        *)
(*      numerically coinciding with an ANCESTOR level's own fresh choice that    *)
(*      ALSO never got bound (the SAME dead-branch scenario, one level up).      *)
(*      Checked ProgWF/NoBareFreeOrChoiceProgWF (neither addresses variable-      *)
(*      naming discipline) and var := nat itself (an ordering exists, but        *)
(*      Hfresh never uses it) -- confirmed nothing rules this out, and the       *)
(*      collision scenario is concretely constructible (an unreached branch's    *)
(*      dead let-bound var alongside a reached branch's own nested Fun call).     *)
(*      Reassuring half: this almost certainly does NOT make the THEOREM         *)
(*      false (a dead branch never affects the final value, so alpha-             *)
(*      equivalence shouldn't depend on how its throwaway pair reconciles) --      *)
(*      it breaks THIS PROOF TECHNIQUE specifically, because batch_extend's        *)
(*      Hfix demands sigma0 already fix every one of vs's images unconditionally,  *)
(*      dead ones included.                                                        *)
(*                                                                                  *)
(*      RESOLVED (this session, continued): rejected generalizing batch_extend      *)
(*      itself (cyc_extend's "l is currently fixed" precondition is genuinely       *)
(*      load-bearing -- its own proof needs it to rule out something OUTSIDE l      *)
(*      mapping INTO it -- so tolerating a pre-existing move would mean re-doing    *)
(*      component/chase over a COMBINED graph, real new combinatorics, not a        *)
(*      patch). Landed instead on: NEVER reuse a level's own batch_extend OUTPUT    *)
(*      as the next level's starting point. Thread FOUR new top-level constants     *)
(*      (Gam1_TOP, Gam2_TOP, sigma0_TOP, tau0_TOP, fixed for the WHOLE induction)    *)
(*      plus monotonicity hooks (Gam1_TOP/Gam2_TOP's own domain is <= the current   *)
(*      level's Gam1/Gam2, via NEval_left_domain_mono), plus a growing "pa : list    *)
(*      (var*var)" (every Fun/Guess pair introduced so far), and at EVERY Fun/       *)
(*      Guess step call batch_extend FRESH -- on pa ++ (this level's own new         *)
(*      pairs), starting from sigma0_TOP/tau0_TOP, NEVER from the incoming per-       *)
(*      level sigma0. Hfix for the combined list then follows from Hcontain0 AT      *)
(*      THE TOP (never re-examined per level) plus monotonicity: anything fresh       *)
(*      relative to a LATER heap is fresh relative to Gam1_TOP too (contrapositive     *)
(*      of domain_mono) -- no generalized batch_extend, no risk of an open-ended        *)
(*      combinatorial problem.                                                          *)
(*                                                                                       *)
(*      Chasing this to a working statement surfaced one more piece, now RESOLVED:       *)
(*      relating the CURRENT level's own sigma0 (needed for Hparam/Hmatch, since           *)
(*      D2's shape-inversion is stated in terms of it) to the FRESHLY-recomputed            *)
(*      sigma at a PARAMETER position that happens to be an ANCESTOR's own already-          *)
(*      introduced pair (e.g. a let-bound local passed as an argument to a NESTED             *)
(*      call -- this is completely ordinary program structure, not a corner case).             *)
(*      First worried this needed a NEW "same variable, live or dead in lockstep across        *)
(*      D1/D2" semantic fact (a genuinely different, deeper kind of gap) -- but it            *)
(*      does NOT: batch_extend's Hrealizes conjunct is UNCONDITIONAL (sigma'(a)=b for          *)
(*      EVERY (a,b) in its input list, regardless of what else that list contains or          *)
(*      merges with). Maintaining "Hrealize_accum: forall a b, In (a,b) pa -> sigma0 a=b"      *)
(*      as an invariant (trivial at the top; trivially carried through every non-Fun/          *)
(*      Guess case; free at Fun/Guess since pa is a SUBSET of the combined list the             *)
(*      fresh batch_extend call is run on) gives EXACT agreement on pa's domain              *)
(*      directly -- no liveness reasoning needed at all, and its mutual-inverse             *)
(*      corollary gives the matching fact on the range side via tau for free too.          *)
(*                                                                                          *)
(*      Net design (STATEMENT drafted, NOT YET IMPLEMENTED -- see below for exact           *)
(*      scope): thread, alongside the existing parameters, Gam1_TOP/Gam2_TOP/               *)
(*      sigma0_TOP/tau0_TOP/their own mutual_inverse+Hcontain0, two monotonicity            *)
(*      hooks, and pa with its own NoDup/Hfix/Hrealize_accum facts; the conclusion          *)
(*      existentially produces pa' (>= pa) with the SAME three facts carried forward,        *)
(*      and Hcontain0/the output "both heaps defined" conjunct get exempted via              *)
(*      "~In w (map fst pa' ++ map snd pa')" (the ONLY conjuncts that actually need           *)
(*      it -- extends does NOT, since Hrealize_accum already makes it hold on pa's            *)
(*      domain directly, and pa's range side goes through tau, which agrees for free).        *)
(*      This is roughly NINE new pieces threaded through 11 cases, on top of the four         *)
(*      passes already done for Hcontain0/HFdom1/HFdom2/ClosedHeap.                            *)
(*                                                                                              *)
(*      BUILT (next session): the statement change, bundled as two Definitions (PaInv --       *)
(*      NoDup+Hfix+Hrealize_accum, PLUS a FOURTH fact discovered necessary while actually       *)
(*      writing it, Houtside_accum: current sigma0 agrees with sigma0_TOP outside pa, needed    *)
(*      because batch_extend's own "outside" conjunct is now stated relative to sigma0_TOP,     *)
(*      not the current sigma0, so nothing else bridges the two -- and PaSub, "pa' extends      *)
(*      pa"), threaded through all 8 non-Fun/Select/Guess cases (VarCons/VarSelf/VarFree/       *)
(*      ValFree/ValCon/VarExp/Let/Or), ALL fully re-proven and Qed'd, zero admits among them,    *)
(*      confirmed via coqc. NL_Fun's own case gets as far as HfixBE_TOP (Hfix for THIS level's  *)
(*      ps_pairs relative to sigma0_TOP, via HGam1mono/HGam2mono's contrapositive plus the       *)
(*      original Hcontain0_TOP -- exactly as the design predicted, and it works) before hitting  *)
(*      a SEVENTH gap: calling batch_extend on the COMBINED list pa++ps_pairs needs pa and       *)
(*      ps_pairs to be DISJOINT (for NoDup of the concatenation), and this is NOT provable --    *)
(*      a pa element introduced from an ANCESTOR's own DEAD (never-taken) case branch stays      *)
(*      outside every heap's domain forever, indistinguishable from an ordinary unused fresh     *)
(*      number, so nothing stops THIS level's s/s2 from independently landing on it. Distinct    *)
(*      from gap 6 (which blocked the OUTPUT "both heaps defined" conjunct, fixed by exempting   *)
(*      dead locations after the fact via pa'/D'): this blocks batch_extend's own INPUT NoDup    *)
(*      precondition, before Hfinal is even reachable, so after-the-fact exemption can't help.   *)
(*      See NL_Fun's own in-proof comment for the full argument, including why FunBodyWellScoped *)
(*      narrows but doesn't close it (rules out the ordinary "let-bound-then-passed-as-an-       *)
(*      argument" case, not the dead-branch case). Select/Guess left exactly as before (still    *)
(*      admits, for their own pre-existing reasons, untouched this pass). NOT YET RESOLVED.       *)
(*                                                                                                 *)
(*      RESOLUTION DIRECTION CHOSEN (next session, "weaken Hfinal"): traced by hand FIRST (as       *)
(*      always) why the obvious cheap version fails -- rename_b is plain structural substitution,   *)
(*      so "e2 = rename_b sigma0 e1" is either exactly true at EVERY position (dead ones too) or     *)
(*      false; there is no "don't care about dead positions" reading of a literal term equation.     *)
(*      The real fix isn't a weaker equation, it's not requiring ONE global bijection to relate       *)
(*      e1/e2 at all. PIECE 7 (BUILT, foundation only): BlkAlpha/Expr0Alpha, a NON-bijective            *)
(*      structural correspondence relation -- at every BINDER (Let's own x, a Case branch's own         *)
(*      pattern vars) it allows a LOCALLY-overridden correspondence function instead of the ambient       *)
(*      sigma, via a PLAIN function override (ren_override2) rather than a bijection extension, so        *)
(*      it needs no NoDup/Hfix precondition and no collision is ever possible -- only genuinely LIVE        *)
(*      positions (Let's RHS, a Case's scrutinee) still go through the ambient sigma. The key lemma,         *)
(*      BlkAlpha_rename_scoped (replaces Hfinal): needs agreement only on body's own free_vars_b (scope-      *)
(*      aware, tiny per FunBodyWellScoped) rather than the whole structural vars_of_b -- fully Qed'd, zero     *)
(*      admits, for BExpr/BLet/BCase all three. NOT YET WIRED into NEval_left_confluence itself -- that's      *)
(*      the next, larger step: restate the theorem against BlkAlpha instead of literal rename_b equality,       *)
(*      redo all 11 cases. See THEOREM2_PROCESS_NOTES.md Sec.34 for the full trace.                              *)
(*   5. Wiring the finished lemma into theorem2's G_CaseFun second        *)
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

Lemma mutual_inverse_injective_r :
  forall sigma tau, mutual_inverse sigma tau -> forall x y, tau x = tau y -> x = y.
Proof.
  intros sigma tau [Hst Hts] x y Heq.
  rewrite <- (Hts x), <- (Hts y), Heq. reflexivity.
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
(* PIECE 1a-bis (Sec.37/38 of the process notes): the "chain-redirect"    *)
(* primitive gap 8 needs.  mutual_inverse_extend/ext_sigma require BOTH   *)
(* endpoints to ALREADY be fixed points -- exactly what breaks one level   *)
(* into NL_Let, where the source point (this level's own "x") can already  *)
(* be moved by an ANCESTOR's own swap.  splice_sigma/splice_tau insert a   *)
(* NEW edge a -> d into an EXISTING bijection by reconnecting whatever a    *)
(* used to map to (a' := sigma a) and whatever used to map to d (d' :=      *)
(* tau d): d' now maps to a', closing the gap left by the redirect.  ext_  *)
(* sigma/ext_tau's own swap is the special case a'=a, d'=d (both already    *)
(* fixed) -- this is a STRICT GENERALIZATION, with NO fixed-point           *)
(* precondition needed at all. *)
Definition splice_sigma (sigma tau : ren) (a d : var) : ren :=
  fun w => if Nat.eq_dec w a then d else if Nat.eq_dec w (tau d) then sigma a else sigma w.
Definition splice_tau (sigma tau : ren) (a d : var) : ren :=
  fun w => if Nat.eq_dec w d then a else if Nat.eq_dec w (sigma a) then tau d else tau w.

Lemma splice_sigma_at_a : forall sigma tau a d, splice_sigma sigma tau a d a = d.
Proof. intros. unfold splice_sigma. destruct (Nat.eq_dec a a); [reflexivity | congruence]. Qed.

Lemma splice_sigma_at_td :
  forall sigma tau a d, tau d <> a -> splice_sigma sigma tau a d (tau d) = sigma a.
Proof.
  intros sigma tau a d Hne. unfold splice_sigma.
  destruct (Nat.eq_dec (tau d) a); [congruence | ].
  destruct (Nat.eq_dec (tau d) (tau d)); [reflexivity | congruence].
Qed.

Lemma splice_sigma_other :
  forall sigma tau a d w, w <> a -> w <> tau d -> splice_sigma sigma tau a d w = sigma w.
Proof.
  intros sigma tau a d w Hwa Hwtd. unfold splice_sigma.
  destruct (Nat.eq_dec w a); [congruence | ]. destruct (Nat.eq_dec w (tau d)); [congruence | reflexivity].
Qed.

Lemma splice_tau_at_d : forall sigma tau a d, splice_tau sigma tau a d d = a.
Proof. intros. unfold splice_tau. destruct (Nat.eq_dec d d); [reflexivity | congruence]. Qed.

Lemma splice_tau_at_sa :
  forall sigma tau a d, sigma a <> d -> splice_tau sigma tau a d (sigma a) = tau d.
Proof.
  intros sigma tau a d Hne. unfold splice_tau.
  destruct (Nat.eq_dec (sigma a) d); [congruence | ].
  destruct (Nat.eq_dec (sigma a) (sigma a)); [reflexivity | congruence].
Qed.

Lemma splice_tau_other :
  forall sigma tau a d w, w <> d -> w <> sigma a -> splice_tau sigma tau a d w = tau w.
Proof.
  intros sigma tau a d w Hwd Hwsa. unfold splice_tau.
  destruct (Nat.eq_dec w d); [congruence | ]. destruct (Nat.eq_dec w (sigma a)); [congruence | reflexivity].
Qed.

Lemma splice_mutual_inverse :
  forall sigma tau, mutual_inverse sigma tau ->
  forall a d, mutual_inverse (splice_sigma sigma tau a d) (splice_tau sigma tau a d).
Proof.
  intros sigma tau Hmi a d.
  pose proof Hmi as [Hst Hts].
  split; intro w.
  - destruct (Nat.eq_dec w a) as [Hwa | Hwa].
    + subst w. rewrite splice_sigma_at_a, splice_tau_at_d. reflexivity.
    + destruct (Nat.eq_dec w (tau d)) as [Hwtd | Hwtd].
      * subst w. rewrite (splice_sigma_at_td sigma tau a d Hwa).
        destruct (Nat.eq_dec (sigma a) d) as [Hsad | Hsad].
        -- unfold splice_tau. destruct (Nat.eq_dec (sigma a) d); [ | congruence].
           rewrite <- Hsad, Hst. reflexivity.
        -- rewrite (splice_tau_at_sa sigma tau a d Hsad). reflexivity.
      * assert (Hsw_sa : sigma w <> sigma a)
          by (intro Hc; apply Hwa; exact (mutual_inverse_injective_l sigma tau Hmi w a Hc)).
        assert (Hsw_d : sigma w <> d).
        { intro Hc. apply Hwtd. apply (mutual_inverse_injective_l sigma tau Hmi).
          rewrite Hc. symmetry. exact (Hts d). }
        rewrite (splice_sigma_other sigma tau a d w Hwa Hwtd).
        rewrite (splice_tau_other sigma tau a d (sigma w) Hsw_d Hsw_sa).
        exact (Hst w).
  - destruct (Nat.eq_dec w d) as [Hwd | Hwd].
    + subst w. rewrite splice_tau_at_d, splice_sigma_at_a. reflexivity.
    + destruct (Nat.eq_dec w (sigma a)) as [Hwsa | Hwsa].
      * subst w. rewrite (splice_tau_at_sa sigma tau a d Hwd).
        destruct (Nat.eq_dec (tau d) a) as [Htda' | Htda'].
        -- unfold splice_sigma. destruct (Nat.eq_dec (tau d) a); [ | congruence].
           rewrite <- Htda', Hts. reflexivity.
        -- rewrite (splice_sigma_at_td sigma tau a d Htda'). reflexivity.
      * assert (Htw_a : tau w <> a).
        { intro Hc. apply Hwsa. apply (mutual_inverse_injective_r sigma tau Hmi).
          rewrite Hc. symmetry. exact (Hst a). }
        assert (Htw_td : tau w <> tau d)
          by (intro Hc; apply Hwd; exact (mutual_inverse_injective_r sigma tau Hmi w d Hc)).
        rewrite (splice_tau_other sigma tau a d w Hwd Hwsa).
        rewrite (splice_sigma_other sigma tau a d (tau w) Htw_a Htw_td).
        exact (Hts w).
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

(* cyc_sigma maps l INTO l: for w already in l, the rotated lookup lands
   back inside l (a rotation is a permutation, so "index i of rotate1 l" is
   always some element l already has).  Needed later (batch_extend's own
   4th conjunct) to know sigma' keeps the whole pairs-list domain+range
   closed under itself, not just fixed OUTSIDE it. *)
Lemma cyc_sigma_in : forall l sigma w, In w l -> In (cyc_sigma l sigma w) l.
Proof.
  intros l sigma w Hw. unfold cyc_sigma.
  destruct (list_index l w) as [i | ] eqn:Ei.
  - assert (Hne : nth_error l i = Some w) by exact (list_index_nth_error l w i Ei).
    assert (Hilt : i < length l) by (apply nth_error_Some; rewrite Hne; discriminate).
    assert (Hilt2 : i < length (rotate1 l)) by (rewrite rotate1_length; exact Hilt).
    assert (Hin_rot : In (nth i (rotate1 l) 0) (rotate1 l)) by exact (nth_In (rotate1 l) 0 Hilt2).
    exact (Permutation_in (nth i (rotate1 l) 0) (Permutation_sym (rotate1_perm l)) Hin_rot).
  - exfalso. exact (list_index_none_not_in l w Ei Hw).
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
    (forall w, ~ In w (map fst ps) -> ~ In w (map snd ps) -> sigma' w = sigma w) /\
    (forall w, In w (map fst ps) \/ In w (map snd ps) ->
       In (sigma' w) (map fst ps) \/ In (sigma' w) (map snd ps)).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros ps Hlen HNDfst HNDsnd sigma tau Hmi Hfix.
  destruct ps as [| p ps'].
  - exists sigma, tau.
    split; [exact Hmi | split; [intros a b Hc; destruct Hc | split; [intros w _ _; reflexivity | ]]].
    intros w Hw. destruct Hw as [Hw | Hw]; destruct Hw.
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
      as [sigma2 [tau2 [Hmi2 [Hreal2 [Hout2 Hmap2]]]]].
    exists sigma2, tau2. split; [exact Hmi2 | split; [ | split]].
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
    + intros w Hw.
      destruct (in_dec Nat.eq_dec w (component (p :: ps') v0)) as [Hwcomp | Hwncomp].
      * (* w in the component: sigma2 agrees with sigma1 there (w avoids
           ps_rest's own domain+range, same argument as Hfix1 above), and
           sigma1 keeps it inside the component (cyc_sigma_in), which sits
           inside (p::ps')'s domain+range via component_subset + Hv0fst. *)
        assert (Hwof : ~ In w (map fst ps_rest)).
        { intro Hc. apply in_map_iff in Hc. destruct Hc as [q [Hfq Hqin]].
          apply (Hrest_out q Hqin). rewrite Hfq. exact Hwcomp. }
        assert (Hwos : ~ In w (map snd ps_rest)).
        { intro Hc. apply in_map_iff in Hc. destruct Hc as [q [Hsq Hqin]].
          assert (Hqorig : In q (p :: ps')) by exact (Hrest_sub q Hqin).
          assert (Hqpair : In (fst q, snd q) (p :: ps')) by (rewrite <- surjective_pairing; exact Hqorig).
          assert (Hwq : w = snd q) by (symmetry; exact Hsq).
          rewrite Hwq in Hwcomp.
          assert (Hback := component_backward_closed (p :: ps') HNDfst HNDsnd Hnnil (fst q) (snd q) Hqpair Hwcomp).
          exact (Hrest_out q Hqin Hback). }
        rewrite (Hout2 w Hwof Hwos).
        assert (Hsigma1in : In (sigma1 w) (component (p :: ps') v0))
          by exact (cyc_sigma_in (component (p :: ps') v0) sigma w Hwcomp).
        destruct (component_subset (p :: ps') HNDsnd HNDfst v0 (sigma1 w) Hsigma1in) as [Heq | Hin2].
        -- left. rewrite Heq. exact Hv0fst.
        -- right. exact Hin2.
      * (* w outside the component: since w is in (p::ps')'s domain+range,
           it must be in ps_rest's (the filter only ever drops component-
           side entries), so the recursive 4th conjunct (Hmap2) applies and
           lifts back up via Hrest_sub_fst/Hrest_sub_snd. *)
        assert (Hwrest : In w (map fst ps_rest) \/ In w (map snd ps_rest)).
        { destruct Hw as [Hw | Hw].
          - left. apply in_map_iff in Hw. destruct Hw as [q [Hfq Hqin]]. apply in_map_iff. exists q.
            split; [exact Hfq | ]. unfold ps_rest. apply filter_In. split; [exact Hqin | ].
            change ((if in_dec Nat.eq_dec (fst q) (component (p :: ps') v0) then false else true) = true).
            destruct (in_dec Nat.eq_dec (fst q) (component (p :: ps') v0)) as [Hc | Hc]; [ | reflexivity].
            exfalso. apply Hwncomp. rewrite <- Hfq. exact Hc.
          - apply in_map_iff in Hw. destruct Hw as [q [Hsq Hqin]].
            assert (Hfstnotcomp : ~ In (fst q) (component (p :: ps') v0)).
            { intro Hc.
              assert (Hqpair : In (fst q, snd q) (p :: ps')) by (rewrite <- surjective_pairing; exact Hqin).
              assert (Hb : cyc_sigma (component (p :: ps') v0) sigma (fst q) = snd q)
                by exact (component_pair_realized (p :: ps') HNDsnd HNDfst v0 sigma (fst q) (snd q) Hqpair Hc).
              assert (Hsndin : In (snd q) (component (p :: ps') v0))
                by (rewrite <- Hb; exact (cyc_sigma_in (component (p :: ps') v0) sigma (fst q) Hc)).
              rewrite Hsq in Hsndin. exact (Hwncomp Hsndin). }
            right. apply in_map_iff. exists q. split; [exact Hsq | ].
            unfold ps_rest. apply filter_In. split; [exact Hqin | ].
            change ((if in_dec Nat.eq_dec (fst q) (component (p :: ps') v0) then false else true) = true).
            destruct (in_dec Nat.eq_dec (fst q) (component (p :: ps') v0)) as [Hc | Hc];
              [exfalso; exact (Hfstnotcomp Hc) | reflexivity]. }
        destruct (Hmap2 w Hwrest) as [Hm | Hm].
        -- left. exact (Hrest_sub_fst (sigma2 w) Hm).
        -- right. exact (Hrest_sub_snd (sigma2 w) Hm).
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


(* Small helper lemmas the four remaining cases each need, gathered here so
   the theorem's own case-by-case proof stays readable. *)

(* let_content only special-cases EFree; every other case is a bare BExpr
   wrapper, so its own vars are exactly e0's, plus (in the EFree case) the
   let-bound x itself. *)
Lemma let_content_vars :
  forall x e0 w, In w (vars_of_b (let_content x e0)) -> w = x \/ In w (vars_of_e0 e0).
Proof.
  intros x e0 w H. destruct e0 eqn:He; simpl in H.
  - right. exact H.
  - destruct H.
  - destruct H as [H | []]. left. exact (eq_sym H).
  - right. exact H.
  - right. exact H.
  - right. exact H.
Qed.

(* A branch's own (bound-set-corrected) free variables are part of the
   whole BCase's free variables -- the fact that lets NL_Select/NL_Guess
   get a branch body's closedness from Heclosed directly, with no separate
   well-scopedness hypothesis needed (unlike NL_Fun, which pulls body in
   from OUTSIDE e's own structure). *)
Lemma free_vars_b_bcase_branch :
  forall x brs c ys bd, In (c, ys, bd) brs ->
  forall w, In w (remove_all ys (free_vars_b bd)) -> In w (free_vars_b (BCase x brs)).
Proof.
  intros x brs c ys bd Hin w Hw.
  simpl. right. induction brs as [| [[c' ys'] bd'] brs' IHbrs].
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + injection Heq as Hc Hys Hbd. subst c' ys' bd'.
      apply in_or_app. left. exact Hw.
    + apply in_or_app. right. apply IHbrs. exact Hin.
Qed.

(* ==================================================================== *)
(* PIECE 7 (new): BlkAlpha -- a NON-bijective structural correspondence   *)
(* relation, meant to eventually REPLACE the plain "e2 = rename_b sigma0  *)
(* e1" hypothesis NEval_left_confluence currently needs.  Built to        *)
(* resolve the SEVENTH gap (THEOREM2_PROCESS_NOTES.md Sec.33): trying to  *)
(* reconcile NL_Fun's two independently-fresh renamings s/s2 via ONE      *)
(* global bijection forced DEAD (never-taken-branch) positions to agree   *)
(* too, and nothing rules out two UNRELATED levels' independently-fresh   *)
(* choices numerically colliding there (batch_extend's own NoDup          *)
(* precondition then fails, with no fix in sight -- see NL_Fun's own      *)
(* in-proof comment). The fix: don't require ONE global sigma to relate   *)
(* e1/e2 at EVERY position. At every BINDER (Let's own x, a Case branch's  *)
(* own pattern vars), allow a LOCALLY-overridden correspondence function   *)
(* instead of the ambient sigma -- a PLAIN function override, not a        *)
(* bijection extension, so it is ALWAYS constructible: no NoDup/Hfix        *)
(* precondition, no collision possible, ever (overriding a function at a    *)
(* finite set of points needs nothing but the finite set itself). Only      *)
(* genuinely LIVE positions (Let's own RHS e, a Case's own scrutinee)        *)
(* still go through the ambient sigma -- exactly the positions the REST      *)
(* of this file's machinery (heap correspondence, shape-inversion) ever      *)
(* needs to agree on. A dead branch's own pattern vars/body get their OWN     *)
(* local correspondence, unconstrained by and never composed with anything    *)
(* else -- so two dead pairs from unrelated levels simply never meet.          *)
(* NOT YET WIRED into NEval_left_confluence itself -- that is the next,        *)
(* larger step (restate the theorem against BlkAlpha instead of literal        *)
(* rename_b equality, redo all 11 cases). This piece is the foundation:         *)
(* the relation itself, plus the key construction lemma (BlkAlpha_rename_       *)
(* scoped) that will replace Hfinal at NL_Fun's own call site. *)
Inductive Expr0Alpha (sigma : ren) : Expr0 -> Expr0 -> Prop :=
| EA0_Var : forall x, Expr0Alpha sigma (EVar x) (EVar (sigma x))
| EA0_Bot : Expr0Alpha sigma EBot EBot
| EA0_Free : Expr0Alpha sigma EFree EFree
| EA0_Choice : forall x y, Expr0Alpha sigma (EChoice x y) (EChoice (sigma x) (sigma y))
| EA0_Fun : forall f args, Expr0Alpha sigma (EFun f args) (EFun f (map sigma args))
| EA0_Con : forall c args, Expr0Alpha sigma (ECon c args) (ECon c (map sigma args)).

Inductive BlkAlpha (sigma : ren) : Blk -> Blk -> Prop :=
| BA_Expr : forall e1 e2, Expr0Alpha sigma e1 e2 -> BlkAlpha sigma (BExpr e1) (BExpr e2)
| BA_Let : forall x1 x2 e1 e2 k1 k2 sigma',
    Expr0Alpha sigma e1 e2 ->
    sigma' x1 = x2 ->
    (forall w, w <> x1 -> sigma' w = sigma w) ->
    BlkAlpha sigma' k1 k2 ->
    BlkAlpha sigma (BLet x1 e1 k1) (BLet x2 e2 k2)
| BA_Case : forall x brs1 brs2,
    BrsAlpha sigma brs1 brs2 ->
    BlkAlpha sigma (BCase x brs1) (BCase (sigma x) brs2)
with BrsAlpha (sigma : ren) : list (cname * list var * Blk) -> list (cname * list var * Blk) -> Prop :=
| BrsA_nil : BrsAlpha sigma nil nil
| BrsA_cons : forall c ys1 ys2 b1 b2 brs1 brs2 sigma',
    Forall2 (fun y1 y2 => sigma' y1 = y2) ys1 ys2 ->
    (forall w, ~ In w ys1 -> sigma' w = sigma w) ->
    BlkAlpha sigma' b1 b2 ->
    BrsAlpha sigma brs1 brs2 ->
    BrsAlpha sigma ((c, ys1, b1) :: brs1) ((c, ys2, b2) :: brs2).

(* A plain, always-total FUNCTION override at finitely many points -- NOT a
   bijection extension, so unlike ext_sigma/batch_extend it needs no
   fixed-point precondition at all: overriding a function's value at a
   point never has to worry about what else might already map there. *)
Fixpoint ren_override2 (ys1 ys2 : list var) (sigma : ren) : ren :=
  match ys1, ys2 with
  | y1 :: ys1', y2 :: ys2' => fun w => if Nat.eq_dec w y1 then y2 else ren_override2 ys1' ys2' sigma w
  | _, _ => sigma
  end.

Lemma ren_override2_notin :
  forall ys1 ys2 sigma w, ~ In w ys1 -> ren_override2 ys1 ys2 sigma w = sigma w.
Proof.
  induction ys1 as [| y1 ys1' IH]; intros ys2 sigma w Hw; destruct ys2 as [| y2 ys2']; try reflexivity.
  simpl. destruct (Nat.eq_dec w y1) as [Heq | Hneq].
  - exfalso. apply Hw. left. exact (eq_sym Heq).
  - apply IH. intro Hc. apply Hw. right. exact Hc.
Qed.

(* Pointwise version: injective s means s w = s y forces w = y, so the
   override at s w always lands on the pair actually keyed by w, regardless
   of what else ys contains -- no NoDup needed. *)
Lemma ren_override2_map_in :
  forall (ys : list var) (s s2 sigma : ren), injective s ->
  forall w, In w ys -> ren_override2 (map s ys) (map s2 ys) sigma (s w) = s2 w.
Proof.
  induction ys as [| y ys' IH]; intros s s2 sigma Hinj w Hw.
  - destruct Hw.
  - simpl. destruct (Nat.eq_dec (s w) (s y)) as [Heq | Hneq].
    + assert (Hwy : w = y) by (apply Hinj; exact Heq). subst w. reflexivity.
    + destruct Hw as [Hw | Hw].
      * subst w. exfalso. exact (Hneq eq_refl).
      * apply IH; [exact Hinj | exact Hw].
Qed.

Lemma Forall2_map_intro :
  forall (A B : Type) (f g : A -> B) (R : B -> B -> Prop) (l : list A),
  (forall a, In a l -> R (f a) (g a)) -> Forall2 R (map f l) (map g l).
Proof.
  intros A B f g R l. induction l as [| a l' IH]; intro H.
  - constructor.
  - simpl. constructor.
    + apply H. left. reflexivity.
    + apply IH. intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma ren_override2_map_Forall2 :
  forall (ys : list var) (s s2 sigma : ren), injective s ->
  Forall2 (fun a b => ren_override2 (map s ys) (map s2 ys) sigma a = b) (map s ys) (map s2 ys).
Proof.
  intros ys s s2 sigma Hinj. apply Forall2_map_intro.
  intros w Hw. apply ren_override2_map_in; [exact Hinj | exact Hw].
Qed.

Lemma Expr0Alpha_rename_scoped :
  forall e s s2 sigma,
  (forall w, In w (vars_of_e0 e) -> sigma (s w) = s2 w) ->
  Expr0Alpha sigma (rename_e0 s e) (rename_e0 s2 e).
Proof.
  intros e s s2 sigma H. destruct e as [x | | | x y | f args | c args]; simpl.
  - assert (Hx : sigma (s x) = s2 x) by (apply H; left; reflexivity).
    rewrite <- Hx. constructor.
  - constructor.
  - constructor.
  - assert (Hx : sigma (s x) = s2 x) by (apply H; left; reflexivity).
    assert (Hy : sigma (s y) = s2 y) by (apply H; right; left; reflexivity).
    rewrite <- Hx, <- Hy. constructor.
  - assert (Hmap : map s2 args = map sigma (map s args)).
    { rewrite map_map. apply map_ext_in. intros w Hw. symmetry. apply H. exact Hw. }
    rewrite Hmap. constructor.
  - assert (Hmap : map s2 args = map sigma (map s args)).
    { rewrite map_map. apply map_ext_in. intros w Hw. symmetry. apply H. exact Hw. }
    rewrite Hmap. constructor.
Qed.

(* THE KEY LEMMA: replaces Hfinal.  Only needs agreement on body's own
   FREE variables (per-position, scope-aware, via free_vars_b) -- NOT on
   every syntactic position vars_of_b would enumerate -- because every
   BINDER (Let, Case's own branches) gets its own local override instead
   of demanding the ambient sigma already know what to do there. *)
Lemma BlkAlpha_rename_scoped :
  forall n body, blk_size body < n ->
  forall s s2 sigma, injective s ->
  (forall w, In w (free_vars_b body) -> sigma (s w) = s2 w) ->
  BlkAlpha sigma (rename_b s body) (rename_b s2 body).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros body Hsize s s2 sigma Hinj H.
  destruct body as [x e k | x brs | e].
  - simpl.
    assert (He : Expr0Alpha sigma (rename_e0 s e) (rename_e0 s2 e)).
    { apply Expr0Alpha_rename_scoped. intros w Hw. apply H. simpl. apply in_or_app. left. exact Hw. }
    set (sigma' := fun w => if Nat.eq_dec w (s x) then s2 x else sigma w).
    apply (BA_Let sigma (s x) (s2 x) (rename_e0 s e) (rename_e0 s2 e) (rename_b s k) (rename_b s2 k) sigma').
    + exact He.
    + unfold sigma'. destruct (Nat.eq_dec (s x) (s x)) as [_ | Hne]; [reflexivity | congruence].
    + intros w Hne. unfold sigma'. destruct (Nat.eq_dec w (s x)) as [Heq | Hneq]; [congruence | reflexivity].
    + assert (Hn : blk_size k + 1 < n) by (simpl in Hsize; lia).
      assert (Hm : blk_size k < blk_size k + 1) by lia.
      apply (IHn (blk_size k + 1) Hn k Hm s s2 sigma' Hinj).
      intros w Hw. unfold sigma'. destruct (Nat.eq_dec (s w) (s x)) as [Heq | Hneq].
      * assert (Hwx : w = x) by (apply Hinj; exact Heq).
        subst w. reflexivity.
      * apply H. simpl. apply in_or_app. right.
        apply in_in_remove; [intro Hc; apply Hneq; f_equal; exact Hc | exact Hw].
  - simpl.
    assert (Hx : sigma (s x) = s2 x) by (apply H; left; reflexivity).
    rewrite <- Hx.
    constructor.
    assert (Hbrs : forall brs', (forall c ys bd, In (c, ys, bd) brs' -> In (c, ys, bd) brs) ->
      BrsAlpha sigma
        (map (fun p => match p with (c, ps, bd) => (c, map s ps, rename_b s bd) end) brs')
        (map (fun p => match p with (c, ps, bd) => (c, map s2 ps, rename_b s2 bd) end) brs')).
    { induction brs' as [| [[c ys] bd] brs'' IHbrs]; intros Hsub.
      - constructor.
      - simpl. assert (HinHead : In (c, ys, bd) brs) by (apply Hsub; left; reflexivity).
        apply (BrsA_cons sigma c (map s ys) (map s2 ys) (rename_b s bd) (rename_b s2 bd)
                 (map (fun p => match p with (c0, ps, bd0) => (c0, map s ps, rename_b s bd0) end) brs'')
                 (map (fun p => match p with (c0, ps, bd0) => (c0, map s2 ps, rename_b s2 bd0) end) brs'')
                 (ren_override2 (map s ys) (map s2 ys) sigma)).
        + exact (ren_override2_map_Forall2 ys s s2 sigma Hinj).
        + intros w Hw. apply ren_override2_notin. exact Hw.
        + assert (Hn : blk_size bd + 1 < n).
          { assert (Hlt : blk_size bd < blk_size (BCase x brs)) by exact (blk_size_in_bound x brs c ys bd HinHead).
            lia. }
          assert (Hm : blk_size bd < blk_size bd + 1) by lia.
          apply (IHn (blk_size bd + 1) Hn bd Hm s s2 (ren_override2 (map s ys) (map s2 ys) sigma) Hinj).
          intros w Hw.
            destruct (in_dec Nat.eq_dec w ys) as [Hyin | Hynin].
            -- (* w is one of THIS branch's own pattern vars -- the override
                  pins it directly, independent of the ambient sigma/H. *)
               apply ren_override2_map_in; [exact Hinj | exact Hyin].
            -- (* w is genuinely free in bd (not a pattern var of ITS OWN
                  branch) -- falls through to the ambient sigma, and is
                  covered by H via free_vars_b_bcase_branch. *)
               rewrite (ren_override2_notin (map s ys) (map s2 ys) sigma (s w))
                 by (intro Hc; apply in_map_iff in Hc; destruct Hc as [y' [Hsy' Hiny']];
                     apply Hynin; assert (Hwy' : w = y') by (apply Hinj; exact (eq_sym Hsy')); subst y'; exact Hiny').
               apply H. apply (free_vars_b_bcase_branch x brs c ys bd HinHead).
               apply remove_all_in_intro; [exact Hw | exact Hynin].
        + apply (IHbrs (fun c0 ys0 bd0 Hin0 => Hsub c0 ys0 bd0 (or_intror Hin0))). }
    apply Hbrs. intros c ys bd Hin. exact Hin.
  - simpl. constructor. apply Expr0Alpha_rename_scoped. intros w Hw. apply H. exact Hw.
Qed.

Lemma hd_error_in : forall (l : list (cname * list var * Blk)) x, hd_error l = Some x -> In x l.
Proof.
  intros l x H. destruct l as [| a l']; simpl in H; [discriminate | ].
  injection H as H. subst a. left. reflexivity.
Qed.

Lemma zipsubst_notin : forall ys zs y, ~ In y ys -> zipsubst ys zs y = y.
Proof.
  induction ys as [| y0 ys' IH]; intros zs y Hnin; destruct zs as [| z0 zs'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. destruct (Nat.eqb y y0) eqn:Heq.
    + exfalso. apply Nat.eqb_eq in Heq. apply Hnin. left. exact (eq_sym Heq).
    + apply IH. intro H. apply Hnin. right. exact H.
Qed.

Lemma zipsubst_in : forall ys zs, length ys = length zs -> forall y, In y ys -> In (zipsubst ys zs y) zs.
Proof.
  induction ys as [| y0 ys' IH]; intros zs Hlen y Hy.
  - destruct Hy.
  - destruct zs as [| z0 zs']; simpl in Hlen; [discriminate | ].
    simpl in Hy. destruct Hy as [Hy | Hy].
    + subst y0. simpl. rewrite Nat.eqb_refl. left. reflexivity.
    + simpl. destruct (Nat.eqb y y0) eqn:Heq.
      * left. reflexivity.
      * right. apply IH; [injection Hlen as Hlen; exact Hlen | exact Hy].
Qed.

Lemma hupd_list_map_self :
  forall (ws : list var) (h : NHeap) w,
  In w ws -> hupd_list h ws (map (fun w0 => BExpr (EVar w0)) ws) w = Some (BExpr (EVar w)).
Proof.
  induction ws as [| x ws' IH]; intros h w Hw.
  - destruct Hw.
  - simpl. unfold hupd. destruct (Nat.eqb w x) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst w. reflexivity.
    + apply IH. simpl in Hw. destruct Hw as [Hw | Hw].
      * exfalso. apply Nat.eqb_neq in Heq. apply Heq. exact (eq_sym Hw).
      * exact Hw.
Qed.

Lemma hupd_list_notin :
  forall (ws : list var) (h : NHeap) (vs : list Blk) w, ~ In w ws -> hupd_list h ws vs w = h w.
Proof.
  induction ws as [| x ws' IH]; intros h vs w Hnin; destruct vs as [| v vs'].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - simpl. unfold hupd. destruct (Nat.eqb w x) eqn:Heq.
    + exfalso. apply Nat.eqb_eq in Heq. apply Hnin. left. exact (eq_sym Heq).
    + apply IH. intro H. apply Hnin. right. exact H.
Qed.

(* PIECE 5, restated with free_vars_b (bound-set-aware) instead of vars_of_b
   for e/v's own closedness, plus FunBodyWellScoped -- the two fixes PIECE
   6's trace showed were necessary and sufficient.  All 11 cases now go
   through: the corrected tool (free_vars_b) plus one genuinely external
   fact (FunBodyWellScoped, needed ONLY at NL_Fun, the sole point where a
   term is pulled in from outside e's own structure) closes what vars_of_b
   alone could not. *)
Theorem NEval_left_closed_preserved :
  forall P F G e G' v, NEval_left P F G e G' v ->
  FunBodyWellScoped P ->
  ClosedHeap G -> (forall w, In w (free_vars_b e) -> G w <> None) ->
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
    ]; intros HScoped Hclosed Heclosed.
  - (* VarCons *)
    split; [exact Hclosed | ].
    simpl. apply (Hclosed z (BExpr (ECon c args)) Hz).
  - (* VarSelf *)
    split; [exact Hclosed | ].
    simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
    rewrite Hz. discriminate.
  - (* VarFree *)
    split.
    + intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w z) eqn:Heqw.
      * apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        simpl in Hy. destruct Hy as [Hy | []]. subst y.
        unfold hupd. rewrite Nat.eqb_refl. discriminate.
      * apply hupd_preserves_some. apply (Hclosed w b Hwb y Hy).
    + simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
      unfold hupd. rewrite Nat.eqb_refl. discriminate.
  - (* VarExp *)
    assert (He0closed : forall w, In w (free_vars_b e0) -> G0 w <> None).
    { intros w Hw. apply (Hclosed z e0 Hz). apply free_vars_b_subset_vars_of_b. exact Hw. }
    destruct (IH HScoped Hclosed He0closed) as [HclosedG1 Hv0closed].
    split.
    + intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w z) eqn:Heqw.
      * apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        apply hupd_preserves_some. apply (Hv0closed y Hy).
      * apply hupd_preserves_some. apply (HclosedG1 w b Hwb y Hy).
    + intros w Hw. apply hupd_preserves_some. apply (Hv0closed w Hw).
  - (* ValFree *)
    split; [exact Hclosed | ].
    intros w Hin. simpl in Hin. destruct Hin.
  - (* ValCon *)
    split; [exact Hclosed | exact Heclosed].
  - (* Fun *)
    assert (Hbodyclosed : forall w, In w (free_vars_b (rename_b s body)) -> G0 w <> None).
    { intros w Hw. destruct (free_vars_b_rename_subset s body w Hw) as [y [Hy Hsy]].
      assert (Hyps : In y ps) by (exact (HScoped f ps body HPf y Hy)).
      destruct (In_nth_error ps y Hyps) as [i Hi].
      assert (Hips : i < length ps) by (apply nth_error_Some; rewrite Hi; discriminate).
      assert (Hiargs : i < length args) by (rewrite <- Hlen; exact Hips).
      destruct (nth_error args i) as [a | ] eqn:Ha.
      - assert (Hsya : s y = a) by (exact (Hmatch i y a Hi Ha)).
        apply Heclosed. rewrite <- Hsy, Hsya. eapply nth_error_In. exact Ha.
      - exfalso. assert (Ha' : nth_error args i <> None) by (apply nth_error_Some; exact Hiargs).
        apply Ha'. exact Ha. }
    exact (IH HScoped Hclosed Hbodyclosed).
  - (* Let *)
    assert (He0closed : forall w, In w (vars_of_e0 e0) -> G0 w <> None).
    { intros w Hw. apply Heclosed. simpl. apply in_or_app. left. exact Hw. }
    assert (Hkclosed : forall w, In w (free_vars_b k) -> hupd G0 z (let_content z e0) w <> None).
    { intros w Hw. destruct (Nat.eq_dec w z) as [Heq | Hneq].
      - subst w. unfold hupd. rewrite Nat.eqb_refl. discriminate.
      - apply hupd_preserves_some. apply Heclosed. simpl. apply in_or_app. right.
        apply in_in_remove; [exact Hneq | exact Hw]. }
    assert (HnewClosed : ClosedHeap (hupd G0 z (let_content z e0))).
    { intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w z) eqn:Heqw.
      - apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        apply let_content_vars in Hy. destruct Hy as [Hy | Hy].
        + subst y. unfold hupd. rewrite Nat.eqb_refl. discriminate.
        + apply hupd_preserves_some. apply He0closed. exact Hy.
      - apply hupd_preserves_some. apply (Hclosed w b Hwb y Hy). }
    exact (IH HScoped HnewClosed Hkclosed).
  - (* Or *)
    apply IH.
    + exact HScoped.
    + exact Hclosed.
    + simpl. intros w Hin. destruct Hin as [Hw | []]. subst w.
      apply Heclosed. simpl. left. reflexivity.
  - (* Select *)
    assert (Hzclosed : forall w, In w (free_vars_b (BExpr (EVar z))) -> G0 w <> None).
    { intros w Hw. simpl in Hw. destruct Hw as [Hw | []]. subst w.
      apply Heclosed. simpl. left. reflexivity. }
    destruct (IH1 HScoped Hclosed Hzclosed) as [HclosedG1 Hzsclosed].
    simpl in Hzsclosed.
    assert (Hbodyclosed : forall w, In w (free_vars_b (rename_b (zipsubst ys zs) body)) -> G1 w <> None).
    { intros w Hw. destruct (free_vars_b_rename_subset (zipsubst ys zs) body w Hw) as [y [Hy Hsy]].
      destruct (in_dec Nat.eq_dec y ys) as [Hyin | Hynin].
      - assert (Hwzs : In w zs) by (rewrite <- Hsy; apply (zipsubst_in ys zs Hlen y Hyin)).
        apply Hzsclosed. exact Hwzs.
      - assert (Hzid : zipsubst ys zs y = y) by (apply zipsubst_notin; exact Hynin).
        assert (HinBCase : In y (free_vars_b (BCase z brs))).
        { apply (free_vars_b_bcase_branch z brs c ys body HIn).
          apply remove_all_in_intro; [exact Hy | exact Hynin]. }
        assert (HG0y : G0 y <> None) by (apply Heclosed; exact HinBCase).
        assert (HG1y : G1 y <> None)
          by (exact (NEval_left_domain_mono P F0 G0 (BExpr (EVar z)) G1 (BExpr (ECon c zs)) Hrec1 y HG0y)).
        rewrite <- Hsy, Hzid. exact HG1y. }
    exact (IH2 HScoped HclosedG1 Hbodyclosed).
  - (* Guess *)
    assert (Hzclosed : forall w, In w (free_vars_b (BExpr (EVar z))) -> G0 w <> None).
    { intros w Hw. simpl in Hw. destruct Hw as [Hw | []]. subst w.
      apply Heclosed. simpl. left. reflexivity. }
    destruct (IH1 HScoped Hclosed Hzclosed) as [HclosedG1 Hz'closed].
    simpl in Hz'closed. assert (HG1z' : G1 z' <> None) by (apply Hz'closed; left; reflexivity).
    assert (Hbr1In : In (c1, ys1, body1) brs) by (apply (hd_error_in brs (c1, ys1, body1) Hhd)).
    set (Hnew := hupd G1 z' (BExpr (ECon c1 ws))).
    assert (HnewClosed : ClosedHeap (hupd_list Hnew ws (map (fun w => BExpr (EVar w)) ws))).
    { intros w b Hwb y Hy. destruct (in_dec Nat.eq_dec w ws) as [Hwws | Hwnws].
      - rewrite (hupd_list_map_self ws Hnew w Hwws) in Hwb. injection Hwb as Hwb; subst b.
        simpl in Hy. destruct Hy as [Hy | []]. subst y.
        rewrite (hupd_list_map_self ws Hnew w Hwws). discriminate.
      - rewrite (hupd_list_notin ws Hnew _ w Hwnws) in Hwb.
        unfold Hnew in Hwb. unfold hupd in Hwb.
        destruct (Nat.eqb w z') eqn:Heqw.
        + apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
          simpl in Hy. rewrite (hupd_list_map_self ws Hnew y Hy). discriminate.
        + destruct (in_dec Nat.eq_dec y ws) as [Hyws | Hynws].
          * rewrite (hupd_list_map_self ws Hnew y Hyws). discriminate.
          * rewrite (hupd_list_notin ws Hnew _ y Hynws). unfold Hnew. apply hupd_preserves_some.
            apply (HclosedG1 w b Hwb y Hy). }
    assert (Hbodyclosed :
      forall w, In w (free_vars_b (rename_b (zipsubst ys1 ws) body1)) ->
      hupd_list Hnew ws (map (fun w0 => BExpr (EVar w0)) ws) w <> None).
    { intros w Hw. destruct (free_vars_b_rename_subset (zipsubst ys1 ws) body1 w Hw) as [y [Hy Hsy]].
      destruct (in_dec Nat.eq_dec y ys1) as [Hyin | Hynin].
      - assert (Hwws : In w ws) by (rewrite <- Hsy; apply (zipsubst_in ys1 ws (eq_sym Hlen) y Hyin)).
        rewrite (hupd_list_map_self ws Hnew w Hwws). discriminate.
      - assert (Hzid : zipsubst ys1 ws y = y) by (apply zipsubst_notin; exact Hynin).
        assert (HinBCase : In y (free_vars_b (BCase z brs))).
        { apply (free_vars_b_bcase_branch z brs c1 ys1 body1 Hbr1In).
          apply remove_all_in_intro; [exact Hy | exact Hynin]. }
        assert (HG0y : G0 y <> None) by (apply Heclosed; exact HinBCase).
        assert (HG1y : G1 y <> None)
          by (exact (NEval_left_domain_mono P F0 G0 (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 y HG0y)).
        destruct (in_dec Nat.eq_dec y ws) as [Hyws | Hynws].
        + exfalso. apply HG1y. apply (Hfr y Hyws).
        + rewrite <- Hsy, Hzid. rewrite (hupd_list_notin ws Hnew _ y Hynws). unfold Hnew.
          apply hupd_preserves_some. exact HG1y. }
    exact (IH2 HScoped HnewClosed Hbodyclosed).
Qed.

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

(* NINE-PIECE DESIGN (Section 32 of THEOREM2_PROCESS_NOTES.md), now being
   BUILT: bundles the "pa" invariant's three named facts (NoDup on both
   projections, Hfix relative to the FIXED sigma0_TOP, Hrealize_accum
   relative to the CURRENT level's own sigma0) plus a FOURTH fact
   discovered necessary while actually writing this (Houtside_accum: the
   current sigma0 agrees with sigma0_TOP outside pa) into one Definition,
   so every pass-through case can carry it opaquely instead of
   re-destructuring four facts at every call site. Houtside_accum wasn't
   named in the original design write-up but is needed the moment NL_Fun's
   own Houtps argument is redone: batch_extend's own "outside" conjunct is
   now stated relative to sigma0_TOP (since the fresh call starts FROM
   sigma0_TOP, not the current sigma0), so recovering "sigma agrees with
   the CURRENT sigma0" for a parameter outside pa/ps_pairs needs this
   bridge -- without it there'd be no way to connect sigma0_TOP-relative
   and sigma0-relative agreement at all. *)
Definition PaInv (sigma0_TOP sigma0 : ren) (pa : list (var * var)) : Prop :=
  NoDup (map fst pa) /\ NoDup (map snd pa) /\
  (forall w, In w (map fst pa) \/ In w (map snd pa) -> sigma0_TOP w = w) /\
  (forall a b, In (a, b) pa -> sigma0 a = b) /\
  (forall w, ~ In w (map fst pa) -> ~ In w (map snd pa) -> sigma0 w = sigma0_TOP w).

Definition PaSub (pa pa' : list (var * var)) : Prop :=
  (forall w, In w (map fst pa) -> In w (map fst pa')) /\
  (forall w, In w (map snd pa) -> In w (map snd pa')).

Lemma PaSub_refl : forall pa, PaSub pa pa.
Proof. intro pa. split; intros w H; exact H. Qed.

Lemma PaSub_trans : forall pa1 pa2 pa3, PaSub pa1 pa2 -> PaSub pa2 pa3 -> PaSub pa1 pa3.
Proof.
  intros pa1 pa2 pa3 [H1a H1b] [H2a H2b].
  split; intros w H; [exact (H2a w (H1a w H)) | exact (H2b w (H1b w H))].
Qed.

Lemma PaInv_nil : forall sigma0_TOP, PaInv sigma0_TOP sigma0_TOP nil.
Proof.
  intro sigma0_TOP. unfold PaInv.
  split; [constructor | ].
  split; [constructor | ].
  split; [intros w [[] | []] | ].
  split; [intros a b [] | ].
  intros w _ _. reflexivity.
Qed.

(* ==================================================================== *)
(* PIECE 8: wiring BlkAlpha into NEval_left_confluence.  The restated      *)
(* theorem below drops the WHOLE nine-piece pa/PaInv/sigma0_TOP apparatus   *)
(* (Sec.32-33 of THEOREM2_PROCESS_NOTES.md): with BlkAlpha replacing the    *)
(* literal "e2 = rename_b sigma0 e1" equation, NL_Fun's own term            *)
(* correspondence needs NO reconciliation of non-parameter body-internal    *)
(* names at all (BlkAlpha_rename_scoped only needs agreement on              *)
(* free_vars_b body, which FunBodyWellScoped already confines to ps) -- and  *)
(* separately, the INDUCTION itself only ever visits LIVE binders (a         *)
(* genuinely dead branch is never part of any NEval_left derivation, so the  *)
(* induction can never even reach one), so the HEAP-level bijection only     *)
(* ever needs extending ONE live pair (Let) or one live batch (Guess) at a   *)
(* time, directly off the CURRENT sigma0/tau0 -- no cross-level merging, no  *)
(* NoDup-disjointness question, ever.  See Sec.35 for the reasoning that led *)
(* here. NOT YET VERIFIED past the helper lemmas below -- the theorem's own  *)
(* case-by-case reproof is in progress. *)

(* Expr0Alpha is fully deterministic in both directions: none of its six    *)
(* constructors leaves any freedom given e's own shape, so "Expr0Alpha       *)
(* sigma e1 e2" and "e2 = rename_e0 sigma e1" carry exactly the same         *)
(* information -- converted between freely below. *)
Lemma Expr0Alpha_det : forall sigma e1 e2, Expr0Alpha sigma e1 e2 -> e2 = rename_e0 sigma e1.
Proof. intros sigma e1 e2 H. destruct H; reflexivity. Qed.

Lemma Expr0Alpha_intro : forall sigma e, Expr0Alpha sigma e (rename_e0 sigma e).
Proof. intros sigma e. destruct e as [x | | | x y | f args | c args]; simpl; constructor. Qed.

(* The congruence BlkAlpha needs but rename_b_congr alone doesn't give: if   *)
(* sigma1/sigma2 agree on b1's own FREE variables (free_vars_b, bound-set-   *)
(* aware), a BlkAlpha derivation built under sigma1 transports to one under  *)
(* sigma2, with the SAME b2. Unlike rename_b_congr this needs NO injectivity *)
(* anywhere: BlkAlpha's own binder-crossing machinery already tolerates an   *)
(* arbitrary local override at every binder, so the proof just re-overrides  *)
(* with a plain "if w is bound here, keep the old value" swap at each        *)
(* binder -- no NoDup needed either, for the same reason ren_override2       *)
(* itself needs none. Used to move from the ambient sigma0-relative BlkAlpha *)
(* an inversion happens to hand back to whatever DIFFERENT (but agreeing on  *)
(* the live positions) renaming a case's own construction actually needs. *)
Lemma BlkAlpha_change_sigma_bound :
  forall n b1, blk_size b1 < n ->
  forall sigma1 sigma2 b2,
  (forall w, In w (free_vars_b b1) -> sigma1 w = sigma2 w) ->
  BlkAlpha sigma1 b1 b2 -> BlkAlpha sigma2 b1 b2.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b1 Hsize sigma1 sigma2 b2 Hagree Hba.
  destruct b1 as [x e k | x brs | e].
  - remember (BLet x e k) as target eqn:Ht.
    destruct Hba as [ | x1 x2 e1 e2 k1 k2 sigma1'' He Hx Hoff Hbk | ]; try discriminate Ht.
    injection Ht as Htx Hte Htk; subst x1 e1 k1.
    assert (He2 : e2 = rename_e0 sigma1 e) by (apply Expr0Alpha_det; exact He).
    assert (Heagree : forall w, In w (vars_of_e0 e) -> sigma1 w = sigma2 w).
    { intros w Hw. apply Hagree. simpl. apply in_or_app. left. exact Hw. }
    assert (He2' : e2 = rename_e0 sigma2 e) by (rewrite He2; apply rename_e0_congr; exact Heagree).
    set (sigma2' := fun w => if Nat.eq_dec w x then x2 else sigma2 w).
    apply (BA_Let sigma2 x x2 e e2 k k2 sigma2').
    + rewrite He2'. apply Expr0Alpha_intro.
    + unfold sigma2'. destruct (Nat.eq_dec x x); [reflexivity | congruence].
    + intros w Hne. unfold sigma2'. destruct (Nat.eq_dec w x); [congruence | reflexivity].
    + assert (Hn : blk_size k + 1 < n) by (simpl in Hsize; lia).
      assert (Hm : blk_size k < blk_size k + 1) by lia.
      apply (IHn (blk_size k + 1) Hn k Hm sigma1'' sigma2' k2).
      * intros w Hw. unfold sigma2'. destruct (Nat.eq_dec w x) as [Heq | Hneq].
        -- subst w. exact Hx.
        -- rewrite (Hoff w Hneq). apply Hagree. simpl. apply in_or_app. right.
           apply in_in_remove; [exact Hneq | exact Hw].
      * exact Hbk.
  - remember (BCase x brs) as target eqn:Ht.
    destruct Hba as [ | | x1' brs1' brs2' Hbrs ]; try discriminate Ht.
    injection Ht as Htx Htbrs; subst x1' brs1'.
    assert (Hxeq : sigma1 x = sigma2 x) by (apply Hagree; left; reflexivity).
    rewrite Hxeq.
    constructor.
    assert (Hbrs' : forall brs', (forall c ys bd, In (c, ys, bd) brs' -> In (c, ys, bd) brs) ->
      forall brsO, BrsAlpha sigma1 brs' brsO -> BrsAlpha sigma2 brs' brsO).
    { induction brs' as [| [[c ys] bd] brs'' IHbrs]; intros Hsub brsO Hb.
      - remember (@nil (cname * list var * Blk)) as tgt eqn:Htg.
        destruct Hb as [ | ]; try discriminate Htg. constructor.
      - remember ((c, ys, bd) :: brs'') as tgt eqn:Htg.
        destruct Hb as [ | c0 ys1 ys2 b1 b2 brsA brsB sigma1''' HF2 Hoff2 Hbk2 Hbrest ];
          try discriminate Htg.
        injection Htg as Htgc Htgys Htgbd Htgrest. subst c0 ys1 b1 brsA.
        assert (HinHead : In (c, ys, bd) brs) by (apply Hsub; left; reflexivity).
        set (sigma2''' := fun w => if in_dec Nat.eq_dec w ys then sigma1''' w else sigma2 w).
        apply (BrsA_cons sigma2 c ys ys2 bd b2 brs'' brsB sigma2''').
        + assert (Hys : forall ysA ys2A, Forall2 (fun y1 y2 => sigma1''' y1 = y2) ysA ys2A ->
                    (forall y, In y ysA -> In y ys) ->
                    Forall2 (fun y1 y2 => sigma2''' y1 = y2) ysA ys2A).
          { clear HF2. intros ysA. induction ysA as [| yA ysA' IHys]; intros ys2A HF Hsub2.
            - destruct ys2A as [| y2A ys2A']; [constructor | inversion HF].
            - destruct ys2A as [| y2A ys2A']; [inversion HF | ].
              inversion HF as [|a1 a2 a3 a4 Hrel Hrest Heq1 Heq2].
              constructor.
              + unfold sigma2'''. destruct (in_dec Nat.eq_dec yA ys) as [_ | Hnin].
                * exact Hrel.
                * exfalso. apply Hnin. apply Hsub2. left. reflexivity.
              + apply IHys; [exact Hrest | intros y Hy'; apply Hsub2; right; exact Hy']. }
          apply (Hys ys ys2 HF2 (fun y Hy => Hy)).
        + intros w Hw. unfold sigma2'''. destruct (in_dec Nat.eq_dec w ys) as [Hin | _];
            [exfalso; exact (Hw Hin) | reflexivity].
        + assert (Hn : blk_size bd + 1 < n).
          { assert (Hlt : blk_size bd < blk_size (BCase x brs)) by exact (blk_size_in_bound x brs c ys bd HinHead).
            lia. }
          assert (Hm : blk_size bd < blk_size bd + 1) by lia.
          apply (IHn (blk_size bd + 1) Hn bd Hm sigma1''' sigma2''' b2).
          * intros w Hw. unfold sigma2'''. destruct (in_dec Nat.eq_dec w ys) as [Hin | Hnin];
              [reflexivity | ].
            rewrite (Hoff2 w Hnin). apply Hagree. apply (free_vars_b_bcase_branch x brs c ys bd HinHead).
            apply remove_all_in_intro; [exact Hw | exact Hnin].
          * exact Hbk2.
        + apply (IHbrs (fun c0 ys0 bd0 Hin0 => Hsub c0 ys0 bd0 (or_intror Hin0)) brsB Hbrest). }
    exact (Hbrs' brs (fun c ys bd Hin => Hin) brs2' Hbrs).
  - remember (BExpr e) as target eqn:Ht.
    destruct Hba as [e1' e2' He | | ]; try discriminate Ht.
    injection Ht as Hte; subst e1'.
    constructor.
    assert (He2 : e2' = rename_e0 sigma1 e) by (apply Expr0Alpha_det; exact He).
    assert (He2' : e2' = rename_e0 sigma2 e).
    { rewrite He2. apply rename_e0_congr. intros w Hw. apply Hagree. exact Hw. }
    rewrite He2'. apply Expr0Alpha_intro.
Qed.

Lemma BlkAlpha_change_sigma :
  forall b1 sigma1 sigma2 b2,
  (forall w, In w (free_vars_b b1) -> sigma1 w = sigma2 w) ->
  BlkAlpha sigma1 b1 b2 -> BlkAlpha sigma2 b1 b2.
Proof.
  intros b1 sigma1 sigma2 b2 H Hba.
  exact (BlkAlpha_change_sigma_bound (S (blk_size b1)) b1 (Nat.lt_succ_diag_r _) sigma1 sigma2 b2 H Hba).
Qed.

(* NHeapAlpha is preserved when sigma/tau is extended via splice_sigma/
   splice_tau at a genuinely fresh pair (x fresh in Gam1, x2 fresh in
   Gam2) -- the heap-level analogue of gap 8's fix (Sec.37/38 of the
   process notes): no fixed-point precondition on x needed, unlike
   ext_sigma/mutual_inverse_extend. Needs ClosedHeap Gam1 to know
   sigma/sigma' agree on every STORED value's own free variables: the two
   positions splice_sigma changes, x and (tau x2), are both outside
   Gam1's own domain, hence never referenced as a VALUE by anything Gam1
   itself stores. *)
Lemma NHeapAlpha_splice :
  forall sigma tau, mutual_inverse sigma tau ->
  forall Gam1 Gam2, NHeapAlpha sigma tau Gam1 Gam2 -> ClosedHeap Gam1 ->
  forall x x2, Gam1 x = None -> Gam2 x2 = None ->
  NHeapAlpha (splice_sigma sigma tau x x2) (splice_tau sigma tau x x2) Gam1 Gam2.
Proof.
  intros sigma tau Hmi Gam1 Gam2 Halpha Hclosed x x2 Hx1 Hx2 w.
  destruct Hmi as [Hst Hts].
  assert (Hgtx2 : Gam1 (tau x2) = None).
  { assert (H := Halpha x2). unfold nheap_rename in H. rewrite Hx2 in H.
    destruct (Gam1 (tau x2)) as [b | ] eqn:E; simpl in H; [discriminate H | reflexivity]. }
  assert (Hgsx : Gam2 (sigma x) = None).
  { assert (H := Halpha (sigma x)). unfold nheap_rename in H. rewrite Hst in H. rewrite Hx1 in H.
    simpl in H. exact H. }
  destruct (Nat.eq_dec w x2) as [Hwx2 | Hwx2].
  - subst w. unfold nheap_rename.
    rewrite (splice_tau_at_d sigma tau x x2). rewrite Hx1. simpl. exact Hx2.
  - destruct (Nat.eq_dec w (sigma x)) as [Hwsx | Hwsx].
    + subst w. unfold nheap_rename.
      rewrite (splice_tau_at_sa sigma tau x x2 Hwx2).
      rewrite Hgtx2. simpl. exact Hgsx.
    + assert (H := Halpha w). unfold nheap_rename in H. unfold nheap_rename.
      rewrite (splice_tau_other sigma tau x x2 w Hwx2 Hwsx).
      destruct (Gam1 (tau w)) as [b | ] eqn:E; simpl in H |- *.
      * rewrite H. f_equal. apply rename_b_congr. intros w0 Hw0.
        unfold splice_sigma. destruct (Nat.eq_dec w0 x) as [Heq0 | Hneq0].
        -- subst w0. exfalso.
           assert (HinDom : Gam1 x <> None) by (apply (Hclosed (tau w) b E x); exact Hw0).
           exact (HinDom Hx1).
        -- destruct (Nat.eq_dec w0 (tau x2)) as [Heq2 | Hneq2]; [ | reflexivity].
           subst w0. exfalso.
           assert (HinDom : Gam1 (tau x2) <> None) by (apply (Hclosed (tau w) b E (tau x2)); exact Hw0).
           exact (HinDom Hgtx2).
      * exact H.
Qed.

(* BLet's own shape-inversion lemma, mirroring NEval_left_evar_shape/
   NEval_left_bcase_shape's established style exactly -- only NL_Let can
   ever conclude on a BLet-shaped expression, so this is a simple, single-
   case inversion. *)
Lemma NEval_left_blet_shape :
  forall P F Gam x e k G' v, NEval_left P F Gam (BLet x e k) G' v ->
  Gam x = None /\ NEval_left P F (hupd Gam x (let_content x e)) k G' v.
Proof.
  intros P F Gam x e k G' v H.
  remember (BLet x e k) as target eqn:Ht.
  revert x e k Ht.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k1 v1 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v1 Hrec IH
    | F0 G0 z c zs brs ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros x e k Ht; try discriminate Ht.
  injection Ht as Htz Hte Htk; subst z e0 k1.
  split; [exact HzFresh | exact Hrec].
Qed.

(* Two small helpers that make the leaf/pass-through cases below close
   almost mechanically: BlkAlpha at a bare BExpr is fully deterministic
   (mirrors Expr0Alpha_det), and BlkAlpha relates ANY b to its own
   rename_b sigma image (a trivial corollary of BlkAlpha_rename_scoped at
   s := id, needed at NL_VarExp where the recursive premise's own "e" is
   an arbitrary Blk, not necessarily BExpr-shaped). *)
Lemma BlkAlpha_bexpr_det : forall sigma e b2, BlkAlpha sigma (BExpr e) b2 -> b2 = BExpr (rename_e0 sigma e).
Proof.
  intros sigma e b2 H.
  remember (BExpr e) as target eqn:Ht.
  destruct H as [e1' e2' He | | ]; try discriminate Ht.
  injection Ht as Hte; subst e1'.
  f_equal. apply Expr0Alpha_det. exact He.
Qed.

Lemma BlkAlpha_refl : forall sigma b, BlkAlpha sigma b (rename_b sigma b).
Proof.
  intros sigma b.
  assert (H := BlkAlpha_rename_scoped (S (blk_size b)) b (Nat.lt_succ_diag_r _)
                 (fun w => w) sigma sigma (fun x y H => H) (fun w _ => eq_refl (sigma w))).
  rewrite (rename_b_id b) in H. exact H.
Qed.

(* mutual_inverse_extend, generalized to allow a = b (a genuine no-op in
   that case: ext_sigma sigma a a agrees with sigma pointwise wherever it
   matters, since sigma a = a is already given). Needed because NL_Let's
   own D1/D2 fresh choices x/x2 are NOT guaranteed distinct a priori. *)
Lemma mutual_inverse_extend_gen :
  forall sigma tau, mutual_inverse sigma tau ->
  forall a b, sigma a = a -> sigma b = b ->
  mutual_inverse (ext_sigma sigma a b) (ext_tau tau a b).
Proof.
  intros sigma tau Hmi a b Hsa Hsb.
  destruct (Nat.eq_dec a b) as [Heq | Hneq].
  - subst b. destruct Hmi as [Hst Hts].
    split; intro w; destruct (Nat.eq_dec w a) as [Hwa | Hwa].
    + subst w. rewrite (ext_sigma_at_a sigma a a). exact (ext_tau_at_a tau a a).
    + rewrite (ext_sigma_other sigma a a w Hwa Hwa).
      assert (Hswa : sigma w <> a).
      { intro Heqc. apply Hwa. apply (mutual_inverse_injective_l sigma tau (conj Hst Hts)).
        rewrite Heqc. symmetry. exact Hsa. }
      rewrite (ext_tau_other tau a a (sigma w) Hswa Hswa). exact (Hst w).
    + subst w. rewrite (ext_tau_at_a tau a a). exact (ext_sigma_at_a sigma a a).
    + rewrite (ext_tau_other tau a a w Hwa Hwa).
      assert (Hta : tau a = a) by (specialize (Hst a); rewrite Hsa in Hst; exact Hst).
      assert (Htwa : tau w <> a).
      { intro Heqc. apply Hwa. apply (mutual_inverse_injective_l tau sigma (conj Hts Hst)).
        rewrite Heqc. symmetry. exact Hta. }
      rewrite (ext_sigma_other sigma a a (tau w) Htwa Htwa). exact (Hts w).
  - exact (mutual_inverse_extend sigma tau Hmi a b Hneq Hsa Hsb).
Qed.

Theorem NEval_left_confluence :
  forall P F1 Gam1 e1 Gam1' v1, NEval_left P F1 Gam1 e1 Gam1' v1 ->
  forall sigma0 tau0, mutual_inverse sigma0 tau0 ->
  forall F2, F2 = map sigma0 F1 ->
  forall Gam2 e2, BlkAlpha sigma0 e1 e2 -> NHeapAlpha sigma0 tau0 Gam1 Gam2 ->
  (forall w, In w F1 -> Gam1 w <> None) -> (forall w, In w F2 -> Gam2 w <> None) ->
  FunBodyWellScoped P -> ClosedHeap Gam1 -> (forall w, In w (free_vars_b e1) -> Gam1 w <> None) ->
  forall Gam2' v2, NEval_left P F2 Gam2 e2 Gam2' v2 ->
  exists sigma tau, mutual_inverse sigma tau /\
    (forall w, Gam1 w <> None -> sigma w = sigma0 w) /\
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
    ; intros sigma0 tau0 Hmi0 F2 HF2eq Gam2 e2 He2 Halpha0
      HFdom1 HFdom2 HScoped Hclosed1 He1closed Gam2' v2 H2.
  - (* NL_VarCons *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (BExpr (ECon c0 (map sigma0 args0)))).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    assert (He2eq : e2 = BExpr (EVar (sigma0 x))) by (apply (BlkAlpha_bexpr_det sigma0 (EVar x)); exact He2).
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon _]]]]] ] ] ].
    + rewrite Hgamx in Hc1. injection Hc1 as Hc1. subst v2. subst Gam2'.
      exists sigma0, tau0. split; [exact (conj Hst0 Hts0) | ].
      split; [intros w _; reflexivity | ].
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
    assert (He2eq : e2 = BExpr (EVar (sigma0 x))) by (apply (BlkAlpha_bexpr_det sigma0 (EVar x)); exact He2).
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
      split; [exact Halpha0 | reflexivity].
    + exfalso. congruence.
    + exfalso. congruence.
  - (* NL_VarFree *)
    destruct Hmi0 as [Hst0 Hts0].
    assert (Hgamx : Gam2 (sigma0 x) = Some (BExpr EFree)).
    { assert (H := Halpha0 (sigma0 x)). unfold nheap_rename in H. rewrite Hst0 in H. rewrite Hgx0 in H.
      simpl in H. exact H. }
    assert (He2eq : e2 = BExpr (EVar (sigma0 x))) by (apply (BlkAlpha_bexpr_det sigma0 (EVar x)); exact He2).
    subst e2. subst F2.
    destruct (NEval_left_evar_shape P (map sigma0 F0) Gam2 (sigma0 x) Gam2' v2 H2) as
      [ [Hc1 [HG2eq [cc [aa Hv2eq]]]]
      | [ [Hc2 [HG2eq Hv2eq]]
        | [ [Hc3 [HG2eq Hv2eq]]
          | [Hnin [e0 [G1' [Hc4 [Hnecon [Hnevar [Hnefree _]]]]]]]] ] ].
    + exfalso. congruence.
    + exfalso. congruence.
    + subst v2. exists sigma0, tau0.
      split; [exact (conj Hst0 Hts0) | ].
      split; [intros w _; reflexivity | ].
      split.
      * subst Gam2'. intro w.
        assert (Hpt := NHeapAlpha_hupd sigma0 tau0 (conj Hst0 Hts0) G0 Gam2 Halpha0 x (BExpr (EVar x))).
        simpl in Hpt. exact (Hpt w).
      * reflexivity.
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
    assert (He2eq : e2 = BExpr (EVar (sigma0 x))) by (apply (BlkAlpha_bexpr_det sigma0 (EVar x)); exact He2).
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
      assert (He0closed : forall w, In w (free_vars_b e) -> G0 w <> None).
      { intros w Hw. apply (Hclosed1 x e Hgx0). apply free_vars_b_subset_vars_of_b. exact Hw. }
      destruct (IH sigma0 tau0 (conj Hst0 Hts0) (sigma0 x :: map sigma0 F0) eq_refl Gam2
                  (rename_b sigma0 e) (BlkAlpha_refl sigma0 e) Halpha0
                  HFdom1' HFdom2'
                  HScoped Hclosed1 He0closed G1' v2 Hrec2)
        as [sigma [tau [Hmisig [Hext [Halpha Heqv]]]]].
      exists sigma, tau. split; [exact Hmisig | ].
      split; [exact Hext | ].
      assert (Hxne : G0 x <> None) by (rewrite Hgx0; discriminate).
      assert (Hxeq : sigma x = sigma0 x) by exact (Hext x Hxne).
      split.
      * subst Gam2'.
        assert (Hpt := NHeapAlpha_hupd sigma tau Hmisig G1 G1' Halpha x v).
        rewrite Hxeq in Hpt. rewrite <- Heqv in Hpt. exact Hpt.
      * rewrite Heqv. reflexivity.
  - (* NL_ValFree *)
    assert (He2eq : e2 = BExpr EFree) by (apply (BlkAlpha_bexpr_det sigma0 EFree); exact He2).
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
    split; [exact Halpha0 | reflexivity].
  - (* NL_ValCon *)
    assert (He2eq : e2 = BExpr (ECon c0 (map sigma0 args0))) by (apply (BlkAlpha_bexpr_det sigma0 (ECon c0 args0)); exact He2).
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
    split; [exact Halpha0 | simpl; exact Ht].
  - (* NL_Fun: the payoff case.  Gap 7 (THEOREM2_PROCESS_NOTES.md Sec.33-34)
       is gone entirely: BlkAlpha_rename_scoped only needs sigma0 to agree
       with s/s2 on body's own free_vars_b, which FunBodyWellScoped confines
       to ps -- exactly Hparam's own conclusion, already available with no
       reconciliation of non-parameter names at all.  No batch_extend, no
       ps_pairs, no pa: the heaps/renaming feeding the recursive IH call are
       G0/Gam2/sigma0/tau0 UNCHANGED, since NL_Fun itself never touches the
       heap before recursing. *)
    assert (He2eq : e2 = BExpr (EFun f (map sigma0 args))) by (apply (BlkAlpha_bexpr_det sigma0 (EFun f args)); exact He2).
    subst e2. subst F2.
    destruct (NEval_left_fun_shape P (map sigma0 F0) Gam2 f (map sigma0 args) Gam2' v2 H2)
      as [ps2 [body2 [s2 [HPf2 [Hlen2 [Hinj2 [Hmatch2 [Hfresh2 Hrec2]]]]]]]].
    assert (Hpb : Some (ps2, body2) = Some (ps, body)) by (rewrite <- HPf; symmetry; exact HPf2).
    injection Hpb as Hpseq Hbodyeq. subst ps2 body2.
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
    assert (Hagree : forall w, In w (free_vars_b body) -> sigma0 (s w) = s2 w).
    { intros w Hw. symmetry. apply Hparam. apply (HScoped f ps body HPf w Hw). }
    assert (HBA : BlkAlpha sigma0 (rename_b s body) (rename_b s2 body))
      by exact (BlkAlpha_rename_scoped (S (blk_size body)) body (Nat.lt_succ_diag_r _) s s2 sigma0 Hinj Hagree).
    assert (Hbodyclosed : forall w, In w (free_vars_b (rename_b s body)) -> G0 w <> None).
    { intros w Hw. destruct (free_vars_b_rename_subset s body w Hw) as [y [Hy Hsy]].
      assert (Hyps : In y ps) by (apply (HScoped f ps body HPf); exact Hy).
      apply In_nth_error in Hyps. destruct Hyps as [i Hi].
      assert (Hib : i < length ps) by (eapply nth_error_Some; congruence).
      assert (Hib2 : i < length args) by (rewrite <- Hlen; exact Hib).
      destruct (nth_error args i) as [a | ] eqn:Ha.
      2: { exfalso. eapply nth_error_Some; [exact Hib2 | exact Ha]. }
      assert (Hsya : s y = a) by exact (Hmatch i y a Hi Ha).
      assert (HGa : G0 a <> None) by (apply He1closed; simpl; exact (nth_error_In args i Ha)).
      rewrite <- Hsy, Hsya. exact HGa. }
    destruct (IH sigma0 tau0 Hmi0 (map sigma0 F0) eq_refl Gam2 (rename_b s2 body) HBA Halpha0
                HFdom1 HFdom2 HScoped Hclosed1 Hbodyclosed Gam2' v2 Hrec2)
      as [sigma [tau [Hmisig [Hext [Halpha Heqv]]]]].
    exists sigma, tau. split; [exact Hmisig | ].
    split; [exact Hext | ].
    split; [exact Halpha | exact Heqv].
  - (* NL_Let: closed via splice_sigma/splice_tau (PIECE 1a-bis) +
       NHeapAlpha_splice, using the SIMPLIFIED (Gam1-only) "extends" claim
       (Sec.39 of the process notes) -- gap 8 is genuinely gone, and so is
       the follow-on Hcontain0 bookkeeping problem: neither x nor tau0 x2n
       is ever G0-defined, so "extends" is automatically vacuous at both,
       with no exemption tracking of any kind needed. *)
    remember (BLet x e k) as target eqn:Ht.
    destruct He2 as [ | x1 x2n e1n e2n k1n k2n sigma0' He Hxeq' Hoff' Hbk | ]; try discriminate Ht.
    injection Ht as Htx Hte Htk. subst x1 e1n k1n.
    assert (He2eq : e2n = rename_e0 sigma0 e) by (apply Expr0Alpha_det; exact He).
    subst e2n.
    destruct (NEval_left_blet_shape P F2 Gam2 x2n (rename_e0 sigma0 e) k2n Gam2' v2 H2)
      as [Hx2fresh Hrec2].
    destruct Hmi0 as [Hst0 Hts0].
    set (sigma0'' := splice_sigma sigma0 tau0 x x2n).
    set (tau0'' := splice_tau sigma0 tau0 x x2n).
    assert (Hmi'' : mutual_inverse sigma0'' tau0'')
      by exact (splice_mutual_inverse sigma0 tau0 (conj Hst0 Hts0) x x2n).
    assert (Hsx : sigma0'' x = x2n) by exact (splice_sigma_at_a sigma0 tau0 x x2n).
    assert (HG0tx2n : G0 (tau0 x2n) = None).
    { assert (H := Halpha0 x2n). unfold nheap_rename in H. rewrite Hx2fresh in H.
      destruct (G0 (tau0 x2n)) as [b | ] eqn:E; simpl in H; [discriminate H | reflexivity]. }
    assert (Hagreek : forall w, In w (free_vars_b k) -> sigma0' w = sigma0'' w).
    { intros w Hw. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      - subst w. rewrite Hxeq'. exact (eq_sym Hsx).
      - rewrite (Hoff' w Hnewx).
        assert (Hnetx2n : w <> tau0 x2n).
        { intro Heq. subst w.
          assert (HinBLet : In (tau0 x2n) (free_vars_b (BLet x e k))).
          { simpl. apply in_or_app. right. apply in_in_remove; [exact Hnewx | exact Hw]. }
          assert (HG0w : G0 (tau0 x2n) <> None) by (apply He1closed; exact HinBLet).
          exact (HG0w HG0tx2n). }
        exact (eq_sym (splice_sigma_other sigma0 tau0 x x2n w Hnewx Hnetx2n)). }
    assert (Hbk'' : BlkAlpha sigma0'' k k2n) by exact (BlkAlpha_change_sigma k sigma0' sigma0'' k2n Hagreek Hbk).
    assert (Heclosed : forall w, In w (vars_of_e0 e) -> G0 w <> None).
    { intros w Hw. apply He1closed. simpl. apply in_or_app. left. exact Hw. }
    assert (Hxnotine : ~ In x (vars_of_e0 e)).
    { intro Hin. exact (Heclosed x Hin Hxfresh). }
    assert (Htx2notine : ~ In (tau0 x2n) (vars_of_e0 e)).
    { intro Hin. exact (Heclosed (tau0 x2n) Hin HG0tx2n). }
    assert (Heagree : forall w, In w (vars_of_e0 e) -> sigma0 w = sigma0'' w).
    { intros w Hw. destruct (Nat.eq_dec w x) as [Heqx | Hneqx]; [subst w; exfalso; exact (Hxnotine Hw) | ].
      destruct (Nat.eq_dec w (tau0 x2n)) as [Heqx2 | Hneqx2]; [subst w; exfalso; exact (Htx2notine Hw) | ].
      exact (eq_sym (splice_sigma_other sigma0 tau0 x x2n w Hneqx Hneqx2)). }
    assert (Herename : rename_e0 sigma0 e = rename_e0 sigma0'' e) by (apply rename_e0_congr; exact Heagree).
    assert (Halpha0'' : NHeapAlpha sigma0'' tau0'' G0 Gam2)
      by exact (NHeapAlpha_splice sigma0 tau0 (conj Hst0 Hts0) G0 Gam2 Halpha0 Hclosed1 x x2n Hxfresh Hx2fresh).
    assert (Hpt := NHeapAlpha_hupd sigma0'' tau0'' Hmi'' G0 Gam2 Halpha0'' x (let_content x e)).
    rewrite Hsx in Hpt.
    assert (Hrename2 : rename_b sigma0'' (let_content x e) = let_content x2n (rename_e0 sigma0 e)).
    { rewrite Herename. rewrite <- (let_content_rename sigma0'' x e). f_equal. exact Hsx. }
    rewrite Hrename2 in Hpt.
    assert (HFdom1' : forall w, In w F0 -> hupd G0 x (let_content x e) w <> None)
      by (intros w Hw; exact (hupd_preserves_some G0 x _ w (HFdom1 w Hw))).
    assert (HFdom2' : forall w, In w F2 -> hupd Gam2 x2n (let_content x2n (rename_e0 sigma0 e)) w <> None)
      by (intros w Hw; exact (hupd_preserves_some Gam2 x2n _ w (HFdom2 w Hw))).
    assert (Hkclosed : forall w, In w (free_vars_b k) -> hupd G0 x (let_content x e) w <> None).
    { intros w Hw. destruct (Nat.eq_dec w x) as [Heq | Hneq].
      - subst w. unfold hupd. rewrite Nat.eqb_refl. discriminate.
      - apply hupd_preserves_some. apply He1closed. simpl. apply in_or_app. right.
        apply in_in_remove; [exact Hneq | exact Hw]. }
    assert (HnewClosed : ClosedHeap (hupd G0 x (let_content x e))).
    { intros w b Hwb y Hy. unfold hupd in Hwb.
      destruct (Nat.eqb w x) eqn:Heqw.
      - apply Nat.eqb_eq in Heqw; subst w. injection Hwb as Hwb; subst b.
        apply let_content_vars in Hy. destruct Hy as [Hy | Hy].
        + subst y. unfold hupd. rewrite Nat.eqb_refl. discriminate.
        + apply hupd_preserves_some. apply Heclosed. exact Hy.
      - apply hupd_preserves_some. apply (Hclosed1 w b Hwb y Hy). }
    assert (Hxnotinf0 : ~ In x F0) by (intro Hin; exact (HFdom1 x Hin Hxfresh)).
    assert (Htx2notinf0 : ~ In (tau0 x2n) F0) by (intro Hin; exact (HFdom1 (tau0 x2n) Hin HG0tx2n)).
    assert (HF2eq'' : F2 = map sigma0'' F0).
    { rewrite HF2eq. apply map_ext_in. intros w Hw.
      destruct (Nat.eq_dec w x) as [Heqx | Hneqx]; [subst w; exfalso; exact (Hxnotinf0 Hw) | ].
      destruct (Nat.eq_dec w (tau0 x2n)) as [Heqx2 | Hneqx2]; [subst w; exfalso; exact (Htx2notinf0 Hw) | ].
      exact (eq_sym (splice_sigma_other sigma0 tau0 x x2n w Hneqx Hneqx2)). }
    destruct (IH sigma0'' tau0'' Hmi'' F2 HF2eq'' (hupd Gam2 x2n (let_content x2n (rename_e0 sigma0 e)))
                k2n Hbk'' Hpt
                HFdom1' HFdom2'
                HScoped HnewClosed Hkclosed Gam2' v2 Hrec2)
      as [sigma [tau [Hmisig [Hext [Halpha Heqv]]]]].
    exists sigma, tau. split; [exact Hmisig | ].
    split.
    { intros w Hw.
      assert (Hw' : hupd G0 x (let_content x e) w <> None) by exact (hupd_preserves_some G0 x _ w Hw).
      assert (Hseq := Hext w Hw').
      destruct (Nat.eq_dec w x) as [Heqx | Hneqx]; [subst w; exfalso; exact (Hw Hxfresh) | ].
      destruct (Nat.eq_dec w (tau0 x2n)) as [Heqx2 | Hneqx2]; [subst w; exfalso; exact (Hw HG0tx2n) | ].
      unfold sigma0'' in Hseq. rewrite (splice_sigma_other sigma0 tau0 x x2n w Hneqx Hneqx2) in Hseq. exact Hseq. }
    split; [exact Halpha | exact Heqv].
  - (* NL_Or: threads straight through, no fresh renaming involved. *)
    assert (He2eq : e2 = BExpr (EChoice (sigma0 x) (sigma0 y)))
      by (apply (BlkAlpha_bexpr_det sigma0 (EChoice x y)); exact He2).
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
    assert (Hxclosed : forall w, In w (free_vars_b (BExpr (EVar x))) -> G0 w <> None).
    { intros w Hw. simpl in Hw. destruct Hw as [Hw | []]. subst w. apply He1closed. simpl. left. reflexivity. }
    assert (HBAx : BlkAlpha sigma0 (BExpr (EVar x)) (BExpr (EVar (sigma0 x))))
      by (constructor; apply Expr0Alpha_intro).
    destruct (IH sigma0 tau0 Hmi0 F1a HF2eq G1a (BExpr (EVar (sigma0 x))) HBAx Halpha0
                HFdom1 HFdom2 HScoped Hclosed1 Hxclosed G1b v1 HrecD)
      as [sigma [tau [Hmisig [Hext [Halpha Heqv]]]]].
    exists sigma, tau. split; [exact Hmisig | ].
    split; [exact Hext | ].
    split; [exact Halpha | exact Heqv].
  - (* NL_Select: BCase's shape-inversion (NEval_left_bcase_shape) is a
       TWO-way disjunction shared with NL_Guess, so ruling out D2
       independently picking Guess needs IH1 applied first (on the
       scrutinee-forcing sub-derivation) to pin D2's own scrutinee result
       as provably ECon-shaped too; then the matching branch in brs2 has to
       be related back to (c0,ys,body) via Hbrs (BrsAlpha), which needs its
       own lookup lemma (given In (c,ys,bd) brs1 and BrsAlpha sigma brs1
       brs2, find the corresponding (c,ys2,bd2) in brs2) -- not yet built.
       A proper two-step argument, matching G_CaseChoice/G_CaseFun's own
       intricacy in curry_test_leftmost.v.  NOT YET ATTEMPTED under the new
       (BlkAlpha-based) statement; the mechanism is understood (see this
       session's own discussion), just not written. *)
    admit.
  - (* NL_Guess: needs batch_extend restricted to JUST ws (no pa merging
       needed under the new design, unlike gap 7's own old blocker), plus
       the same BrsAlpha-lookup machinery NL_Select needs to identify
       brs2's own first branch. NOT YET ATTEMPTED under the new statement. *)
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
  FunBodyWellScoped P -> ClosedHeap Gam -> (forall w, In w (free_vars_b e) -> Gam w <> None) ->
  forall Gam2 v2, NEval_left P F Gam e Gam2 v2 ->
  exists sigma tau, mutual_inverse sigma tau /\ NHeapAlpha sigma tau Gam1 Gam2 /\ v2 = rename_b sigma v1.
Proof.
  intros P F Gam e Gam1 v1 H1 HFdom HScoped Hclosed Heclosed Gam2 v2 H2.
  assert (HBAid : BlkAlpha (fun w => w) e e).
  { assert (H := BlkAlpha_refl (fun w => w) e). rewrite (rename_b_id e) in H. exact H. }
  destruct (NEval_left_confluence P F Gam e Gam1 v1 H1
              (fun w => w) (fun w => w) mutual_inverse_id
              F (eq_sym (map_id F)) Gam e HBAid
              (NHeapAlpha_refl Gam)
              HFdom HFdom
              HScoped Hclosed Heclosed
              Gam2 v2 H2)
    as [sigma [tau [Hmi [_ [Halpha Heq]]]]].
  exists sigma, tau. split; [exact Hmi | split; [exact Halpha | exact Heq]].
Qed.
