Require Import List Arith Lia.
Import ListNotations.
Require Import curry.

(* ======================================================================= *)
(* failed_attempts.v -- superseded targets, abandoned invariants, and the  *)
(* counterexamples that killed them, kept here as a process record.  This  *)
(* file is deliberately NOT imported by curry_test_leftmost.v -- nothing   *)
(* in the active development depends on anything here.  See                *)
(* THEOREM2_PROCESS_NOTES.md for the full narrative this is excerpted from. *)
(* ======================================================================= *)


(* ======================================================================= *)
(* 1. THE ORIGINAL theorem2 (curry.v) -- superseded target.                *)
(*                                                                         *)
(* This is curry.v's own theorem (see curry.v, "Theorem theorem2"), left  *)
(* Admitted there and NOT modified -- it is quoted here verbatim (as a     *)
(* comment, not re-declared) purely for the record, since curry.v is the   *)
(* base file everything else builds on and isn't ours to gut.              *)
(*                                                                         *)
(*   Theorem theorem2 :                                                    *)
(*     forall P G e G' v,                                                  *)
(*       GEval P G e G' v ->                                                *)
(*       forall c args, CorrV G' v (BExpr (ECon c args)) ->                 *)
(*       forall Gam, HeapCorr G Gam ->                                      *)
(*       exists Gam', NEval P nil Gam e Gam' (BExpr (ECon c args)) /\        *)
(*                     HeapCorr G' Gam'.                                    *)
(*                                                                          *)
(* Why it's stuck: NEval's own N_Or is genuinely nondeterministic           *)
(* (`i = x \/ i = y`), picking EITHER EChoice operand, while GEval's        *)
(* G_CaseChoice is deterministic (always forwards to the FIRST operand,     *)
(* via a hard-coded rule with no companion rule for the second).  So        *)
(* "GEval reaches v implies NEval reaches v" genuinely is NOT provable as   *)
(* stated: there are GEval derivations whose ONLY matching NEval            *)
(* derivation requires N_Or to have picked the side GEval structurally      *)
(* never takes.  curry.v's own proof script gets through most of theorem2's *)
(* 13 GEval-constructor cases and stalls specifically here.                 *)
(*                                                                          *)
(* THE FIX (still active, in curry_test_leftmost.v): NEval_left, a         *)
(* restriction of NEval where N_Or is forced to always pick the FIRST       *)
(* operand (matching G_CaseChoice exactly).  Every NEval_left derivation    *)
(* is trivially also a valid NEval derivation, so proving the analogous     *)
(* statement for NEval_left is strictly sufficient to reprove theorem2 as   *)
(* curry.v originally intended it, modulo swapping NEval for NEval_left.    *)
(* ======================================================================= *)


(* ======================================================================= *)
(* 2. HeapCorr (curry.v's base notion) -- kept alive via HeapCorr2, not    *)
(* itself abandoned, but recorded here because of what it CAN'T represent.  *)
(*                                                                          *)
(*   Definition HeapCorr (G : Graph) (Gam : NHeap) : Prop :=                *)
(*     forall x, match G x with                                             *)
(*               | None => Gam x = None                                     *)
(*               | Some _ => exists b, Gam x = Some b /\ CorrE G x b        *)
(*               end.                                                       *)
(*                                                                          *)
(* CorrE (also curry.v's) requires, for every live graph location x, a Gam  *)
(* witness that either directly translates x's own IMMEDIATE content, or   *)
(* -- for a forwarding node G x = GFwd y -- is either the lazy one-hop      *)
(* alias `EVar y`, or (CorrE_FwdAchievedCon) a skip-ahead to an achieved    *)
(* constructor, but ONLY if y ITSELF (one hop, not further) already holds   *)
(* it directly.                                                            *)
(* ======================================================================= *)


(* ======================================================================= *)
(* 3. COUNTEREXAMPLE: bare HeapCorr allows x's witness to get "ahead of" y  *)
(* in a way no real evaluation would ever produce, motivating              *)
(* ChainConsistent / HeapCorr2.                                            *)
(*                                                                          *)
(* Question tested: does HeapCorr allow x to already hold the achieved      *)
(* shortcut constructor while y's OWN heap slot is still a lazy, unresolved *)
(* alias -- even though no real execution would ever produce exactly this   *)
(* by forcing x itself (forcing x, if it really chases through y, would     *)
(* memoize y too)?                                                          *)
(*                                                                          *)
(* Witness graph: w --Con--, y --Fwd--> w, x --Fwd--> y (a 2-hop chain,     *)
(* w already resolved).  Witness Gam: w = Con (forced, unique), y = EVar w  *)
(* (still lazy -- a valid CorrE_FwdHere witness), x = Con DIRECTLY (the     *)
(* achieved CorrE_FwdAchievedCon shortcut, valid because w -- y's ultimate  *)
(* target -- is already Con, even though y's OWN slot hasn't caught up).    *)
(* ======================================================================= *)

Definition ex_G : Graph := fun z =>
  if Nat.eqb z 0 then Some (GExpr (ECon 0 nil))
  else if Nat.eqb z 1 then Some (GFwd 0)
  else if Nat.eqb z 2 then Some (GFwd 1)
  else None.

Definition ex_Gam : NHeap := fun z =>
  if Nat.eqb z 0 then Some (BExpr (ECon 0 nil))
  else if Nat.eqb z 1 then Some (BExpr (EVar 0))
  else if Nat.eqb z 2 then Some (BExpr (ECon 0 nil))
  else None.

Lemma ex_x_ahead_of_y_reachable : HeapCorr ex_G ex_Gam.
Proof.
  intro z.
  unfold ex_G.
  destruct (Nat.eqb z 0) eqn:E0.
  - exists (BExpr (ECon 0 nil)). split.
    + unfold ex_Gam. rewrite E0. reflexivity.
    + apply CorrE_Con. unfold ex_G. rewrite E0. reflexivity.
  - destruct (Nat.eqb z 1) eqn:E1.
    + exists (BExpr (EVar 0)). split.
      * unfold ex_Gam. rewrite E0, E1. reflexivity.
      * apply CorrE_FwdHere. unfold ex_G. rewrite E0, E1. reflexivity.
    + destruct (Nat.eqb z 2) eqn:E2.
      * exists (BExpr (ECon 0 nil)). split.
        -- unfold ex_Gam. rewrite E0, E1, E2. reflexivity.
        -- eapply CorrE_FwdAchievedCon.
           ++ unfold ex_G. rewrite E0, E1, E2. reflexivity.
           ++ eapply CL_Fwd.
              ** reflexivity.
              ** eapply CL_Here. reflexivity.
           ++ reflexivity.
      * unfold ex_Gam. rewrite E0, E1, E2. reflexivity.
Qed.

(* CONFIRMED: this combination is REACHABLE per HeapCorr's own (purely     *)
(* pointwise, declarative) definition -- nothing in CorrE ties x's own     *)
(* witness choice to y's.  So theorem2, which quantifies over ANY Gam       *)
(* satisfying HeapCorr, genuinely has to contend with it; it can't be        *)
(* dismissed as "not even a valid HeapCorr instance."                         *)

(* ======================================================================= *)
(* 4. THE FIX (v1): ChainConsistent + HeapCorr2.                          *)
(*                                                                          *)
(* Strengthen HeapCorr itself so the "x already achieved, y still lazy"     *)
(* combination is simply not a valid correspondence at all -- ruling out    *)
(* ex_x_ahead_of_y_reachable above by DEFINITION rather than needing to      *)
(* survive it inside every downstream proof.                                *)
(*                                                                          *)
(* ChainConsistent: whenever x forwards to y and x's OWN witness has        *)
(* already been promoted to the achieved constructor, y's witness must      *)
(* ALREADY be that SAME constructor too -- never still lazy.                *)
(*                                                                          *)
(* (ChainConsistent and HeapCorr2 = HeapCorr /\ ChainConsistent are         *)
(* duplicated here, verbatim, from curry_test_leftmost.v purely so this     *)
(* file can state and check the counterexample below on its own -- the      *)
(* LIVE, load-bearing copies that ~150 lemmas and theorems in the main      *)
(* file actually depend on remain there, unchanged.  HeapCorr2 itself was   *)
(* NOT abandoned: it is still exactly what NEval_left_force_free_sound,     *)
(* all three theorem2_G_CaseXXX_case theorems, and the whole                *)
(* HeapCorr2_update_* lemma layer are built on.  What's recorded here is    *)
(* only its own history -- the counterexample that motivated it, and (in    *)
(* section 5 below) the LATER counterexample-shaped gap that HeapCorr2      *)
(* itself turned out to have, which HeapCorr3 was built to fix.) *)
(* ======================================================================= *)

Definition ChainConsistent (G : Graph) (Gam : NHeap) : Prop :=
  forall x y, G x = Some (GFwd y) ->
    forall c args, Gam x = Some (BExpr (ECon c args)) -> Gam y = Some (BExpr (ECon c args)).

Definition HeapCorr2 (G : Graph) (Gam : NHeap) : Prop :=
  HeapCorr G Gam /\ ChainConsistent G Gam.

(* Confirms the strengthening actually bites: the earlier witness is        *)
(* NOT HeapCorr2, precisely because it violates ChainConsistent.            *)
Lemma ex_x_ahead_of_y_not_chain_consistent : ~ ChainConsistent ex_G ex_Gam.
Proof.
  intro HCC.
  specialize (HCC 2 1 eq_refl 0 nil eq_refl).
  discriminate HCC.
Qed.


(* ======================================================================= *)
(* 5. THE SECOND GAP: HeapCorr2 itself can't represent ordinary multi-hop   *)
(* memoization, motivating HeapCorr3 (now renamed HeapCorr in the main      *)
(* file -- see curry_test_leftmost.v).                                     *)
(*                                                                          *)
(* This is NOT a counterexample lemma (no witness graph was built for it   *)
(* the way section 3's was) -- it's a structural gap discovered while       *)
(* trying to prove NEval_left_fwd_transfer_fwdhere_free: when a location x  *)
(* is a lazy one-hop alias to y (Gam x = EVar y, matching CorrE_FwdHere),   *)
(* and forcing x actually recurses through FORCING y (via NL_VarExp), the   *)
(* natural semantics does NOT bother re-writing every intermediate hop of   *)
(* y's own alias chain -- it memoizes x's slot DIRECTLY to whatever the     *)
(* FINAL forced value turned out to be, however many hops away that was.    *)
(*                                                                          *)
(* Concretely: if the graph has x -> y -> z (y itself just another          *)
(* forwarding node, NOT the achieved constructor -- G_CaseFun/G_CaseFwd     *)
(* never re-compress an intermediate Fwd edge, so this is completely        *)
(* ordinary, not a corner case) and z holds the achieved constructor, and   *)
(* the Nat-heap has ALREADY memoized Gam x = Con c args directly (skipping  *)
(* y entirely, since that's just what forcing x produced) -- CorrE's own    *)
(* constructors have no way to certify this.  CorrE_FwdAchievedCon only     *)
(* covers a ONE-HOP skip-ahead (x's own immediate target y must directly    *)
(* hold the constructor); it says nothing about a skip past TWO OR MORE     *)
(* hops.  So this is a completely ordinary, frequently-arising Nat-heap     *)
(* state that plain CorrE/HeapCorr2 simply cannot witness -- not a proof    *)
(* difficulty, a definitional gap.                                          *)
(*                                                                          *)
(* THE FIX: HeapCorr3 (CorrE3), which adds a third disjunct to CorrE:       *)
(* even if x's IMMEDIATE graph content doesn't literally match Gam's        *)
(* witness, the correspondence is still accepted if SOME graph-side         *)
(* ContractLoc chase from x (arbitrary length, not just one hop) reaches a   *)
(* constructor, backed by a purely Nat-heap-side variable-alias hop-chain   *)
(* (VarChase) reaching the same constructor.  It also drops                 *)
(* ChainConsistent's ordering requirement entirely.  See                    *)
(* curry_test_leftmost.v's CorrE3/HeapCorr definitions (renamed from        *)
(* CorrE3/HeapCorr3) and the comment on NEval_left_fwd_transfer_fwdhere_free *)
(* for the live version of this argument.                                   *)
(*                                                                          *)
(* CONSEQUENCE FOR theorem2_left: HeapCorr2 turns out to be too strong to   *)
(* survive as the AMBIENT invariant threaded through a general induction    *)
(* over GEval -- any branch that goes through a real multi-hop chase (which *)
(* is most of them) can only ever hand back HeapCorr3/HeapCorr, never       *)
(* HeapCorr2, as its own conclusion.  So the combined theorem2 (in          *)
(* curry_test_leftmost.v, replacing this file's section-1 target) uses      *)
(* HeapCorr (formerly HeapCorr3) uniformly, both as hypothesis and          *)
(* conclusion, rather than HeapCorr2 with a downgrade at the end.            *)
(* ======================================================================= *)

(* ======================================================================= *)
(* 6. BlkAlpha's FIRST design (Sec.40-42 of THEOREM2_PROCESS_NOTES.md,      *)
(* alpha_renaming_wip.v) -- unconstrained branch-pattern names, killed by a *)
(* concrete, machine-checked counterexample.                                *)
(*                                                                          *)
(* alpha_renaming_wip.v's BlkAlpha/BrsAlpha originally let a BCase branch's *)
(* own target-side pattern names (ys2) be ANY names at all, with no         *)
(* disjointness from anything -- BrsA_cons only required the pattern-var    *)
(* renaming itself (Forall2) and off-ys agreement with the ambient sigma.   *)
(* This is UNSOUND: it lets ys2 collide with what the ambient renaming does *)
(* to a name free OUTSIDE the branch, so a later substitution into ys2      *)
(* (e.g. NL_Select's own zipsubst) can capture a reference that was         *)
(* supposed to stay free.  Confirmed, not just suspected: the lemma below   *)
(* derives False from NEval_left_confluence's OWN STATEMENT (frozen here    *)
(* exactly as it read before the Sec.42 fix, using the locally-defined      *)
(* BlkAlphaOld/BrsAlphaOld below rather than the live BlkAlpha, which has   *)
(* since been strengthened with a capture-avoidance premise precisely to    *)
(* rule this out) taken as a hypothesis, using a fully concrete instance.   *)
(* `Print Assumptions` on it reports "Closed under the global context" --   *)
(* zero axioms.  So this was a genuine inconsistency of the statement as    *)
(* originally written, not a proof-technique shortfall.                    *)
(*                                                                          *)
(* THE CONCRETE COUNTEREXAMPLE: sigma0 := tau0 := id.  e1 := BCase 0        *)
(* [(0, [2], BExpr (EVar 1))] -- forcing x=0 (stored as Con 0 [3]) selects  *)
(* the one branch, substitutes its pattern var 2 (unused in the body) for   *)
(* 3, then forces the body's own free var 1 (stored as nullary Con 100),    *)
(* giving v1 = Con 100 []. e2 := BCase 0 [(0, [1], BExpr (EVar 1))] -- a    *)
(* PERFECTLY VALID BlkAlphaOld id-witness for e1 (BrsA_consOld only         *)
(* requires the pattern-var renaming 2|->1 and offset-agreement elsewhere,  *)
(* both of which hold here with sigma' := 2|->1, id elsewhere) -- but       *)
(* branch2's OWN pattern var (1) happens to equal exactly the free variable *)
(* (1) its body was alpha-corresponding to.  Running e2 on the SAME heap:   *)
(* forcing x=0 again selects the branch, but substituting ITS pattern var 1 *)
(* for 3 now captures the body's own EVar 1 -- rewriting it to EVar 3       *)
(* BEFORE evaluation, so D2 forces position 3 (stored as nullary Con 200)   *)
(* instead of position 1.  v2 = Con 200 [], which cannot equal rename_b     *)
(* sigma v1 (= Con 100 [] for every sigma, since v1 has no free variables)  *)
(* for ANY sigma -- the theorem's own conclusion is unsatisfiable for this  *)
(* instance, even though every hypothesis (mutual_inverse, NHeapAlpha,      *)
(* ClosedHeap, BrsUniqHeap, BrsUniqB e1, ProgBrsUniqWF, FunBodyWellScoped,   *)
(* the free-var-closedness of e1) holds outright.                          *)
(*                                                                          *)
(* THE FIX (now live in alpha_renaming_wip.v): BrsA_cons gained a fourth    *)
(* premise, `forall w, In w (free_vars_b b1) -> ~In w ys1 -> ~In (sigma w)  *)
(* ys2`, ruling out exactly this collision.  Reproving this file's own     *)
(* HBA below under the REAL (fixed) BlkAlpha genuinely fails at that new    *)
(* obligation (as it must, since the fact it demands is false for this      *)
(* instance) -- confirming the fix actually blocks the bad witness, not     *)
(* just relocates the gap.                                                  *)
(* ======================================================================= *)

Require Import curry_test_leftmost.
Require Import alpha_renaming_wip.

(* Exact copy of BlkAlpha/BrsAlpha as they stood before the Sec.42 fix --
   renamed so this file compiles independently of whatever the live
   BlkAlpha (alpha_renaming_wip.v) has since become. *)
Inductive BlkAlphaOld (sigma : ren) : Blk -> Blk -> Prop :=
| BA_ExprOld : forall e1 e2, Expr0Alpha sigma e1 e2 -> BlkAlphaOld sigma (BExpr e1) (BExpr e2)
| BA_LetOld : forall x1 x2 e1 e2 k1 k2 sigma',
    Expr0Alpha sigma e1 e2 ->
    sigma' x1 = x2 ->
    (forall w, w <> x1 -> sigma' w = sigma w) ->
    BlkAlphaOld sigma' k1 k2 ->
    BlkAlphaOld sigma (BLet x1 e1 k1) (BLet x2 e2 k2)
| BA_CaseOld : forall x brs1 brs2,
    BrsAlphaOld sigma brs1 brs2 ->
    BlkAlphaOld sigma (BCase x brs1) (BCase (sigma x) brs2)
with BrsAlphaOld (sigma : ren) : list (cname * list var * Blk) -> list (cname * list var * Blk) -> Prop :=
| BrsA_nilOld : BrsAlphaOld sigma nil nil
| BrsA_consOld : forall c ys1 ys2 b1 b2 brs1 brs2 sigma',
    Forall2 (fun y1 y2 => sigma' y1 = y2) ys1 ys2 ->
    (forall w, ~ In w ys1 -> sigma' w = sigma w) ->
    BlkAlphaOld sigma' b1 b2 ->
    BrsAlphaOld sigma brs1 brs2 ->
    BrsAlphaOld sigma ((c, ys1, b1) :: brs1) ((c, ys2, b2) :: brs2).

Lemma Expr0Alpha_intro_old : forall sigma e, Expr0Alpha sigma e (rename_e0 sigma e).
Proof. exact Expr0Alpha_intro. Qed.

Lemma NEval_left_confluence_stmt_is_false :
  (forall P F1 Gam1 e1 Gam1' v1, NEval_left P F1 Gam1 e1 Gam1' v1 ->
   forall sigma0 tau0, mutual_inverse sigma0 tau0 ->
   forall F2, F2 = map sigma0 F1 ->
   forall Gam2 e2, BlkAlphaOld sigma0 e1 e2 -> NHeapAlpha sigma0 tau0 Gam1 Gam2 ->
   (forall w, In w F1 -> Gam1 w <> None) -> (forall w, In w F2 -> Gam2 w <> None) ->
   FunBodyWellScoped P -> ProgBrsUniqWF P ->
   ClosedHeap Gam1 -> BrsUniqHeap Gam1 ->
   (forall w, In w (free_vars_b e1) -> Gam1 w <> None) -> BrsUniqB e1 ->
   forall Gam2' v2, NEval_left P F2 Gam2 e2 Gam2' v2 ->
   exists sigma tau, mutual_inverse sigma tau /\
     (forall w, Gam1 w <> None -> sigma w = sigma0 w) /\
     NHeapAlpha sigma tau Gam1' Gam2' /\ v2 = rename_b sigma v1)
  -> False.
Proof.
  intro Hthm.
  pose (Gam1 := fun n : nat =>
    if Nat.eqb n 0 then Some (BExpr (ECon 0 (3 :: nil)))
    else if Nat.eqb n 1 then Some (BExpr (ECon 100 nil))
    else if Nat.eqb n 3 then Some (BExpr (ECon 200 nil))
    else None).
  pose (brs1 := (0, (2 :: nil), BExpr (EVar 1)) :: nil).
  pose (e1 := BCase 0 brs1).
  pose (brs2 := (0, (1 :: nil), BExpr (EVar 1)) :: nil).
  pose (e2 := BCase 0 brs2).
  pose (P0 := fun _ : fname => @None (list var * Blk)).
  assert (H1 : NEval_left P0 nil Gam1 e1 Gam1 (BExpr (ECon 100 nil))).
  { unfold e1, brs1.
    eapply NL_Select.
    - apply NL_VarCons. reflexivity.
    - left. reflexivity.
    - reflexivity.
    - simpl. apply NL_VarCons. reflexivity.
  }
  assert (H2 : NEval_left P0 nil Gam1 e2 Gam1 (BExpr (ECon 200 nil))).
  { unfold e2, brs2.
    eapply NL_Select.
    - apply NL_VarCons. reflexivity.
    - left. reflexivity.
    - reflexivity.
    - simpl. apply NL_VarCons. reflexivity.
  }
  assert (HBA : BlkAlphaOld (fun w => w) e1 e2).
  { unfold e1, e2, brs1, brs2.
    replace 0 with ((fun w:nat => w) 0) at 2 by reflexivity.
    apply BA_CaseOld.
    apply (BrsA_consOld (fun w:nat => w) 0 (2::nil) (1::nil) (BExpr (EVar 1)) (BExpr (EVar 1)) nil nil
             (fun w => if Nat.eqb w 2 then 1 else w)).
    - constructor; [reflexivity | constructor].
    - intros w Hw. simpl. destruct (Nat.eqb w 2) eqn:E; [ | reflexivity].
      apply Nat.eqb_eq in E. subst w. exfalso. apply Hw. left. reflexivity.
    - apply BA_ExprOld. apply Expr0Alpha_intro_old.
    - apply BrsA_nilOld.
  }
  assert (HScoped : FunBodyWellScoped P0) by (intros f ps body Hf; discriminate Hf).
  assert (HProgBrsUniq : ProgBrsUniqWF P0) by (intros f ps body Hf; discriminate Hf).
  assert (HClosed : ClosedHeap Gam1).
  { intros z b Hzb w Hw. unfold Gam1 in Hzb.
    destruct (Nat.eqb z 0) eqn:E0.
    - injection Hzb as Hzb; subst b. simpl in Hw. destruct Hw as [Hw | []]. subst w. unfold Gam1. discriminate.
    - destruct (Nat.eqb z 1) eqn:E1.
      + injection Hzb as Hzb; subst b. simpl in Hw. destruct Hw.
      + destruct (Nat.eqb z 3) eqn:E3.
        * injection Hzb as Hzb; subst b. simpl in Hw. destruct Hw.
        * discriminate Hzb.
  }
  assert (HBrsUniqHeap : BrsUniqHeap Gam1).
  { intros z b Hzb. unfold Gam1 in Hzb.
    destruct (Nat.eqb z 0); [injection Hzb as Hzb; subst b; exact I | ].
    destruct (Nat.eqb z 1); [injection Hzb as Hzb; subst b; exact I | ].
    destruct (Nat.eqb z 3); [injection Hzb as Hzb; subst b; exact I | discriminate Hzb].
  }
  assert (Heclosed1 : forall w, In w (free_vars_b e1) -> Gam1 w <> None).
  { unfold e1, brs1. simpl. intros w Hw.
    destruct Hw as [Hw | [Hw | []]]; subst w; unfold Gam1; discriminate.
  }
  assert (He1BrsUniq : BrsUniqB e1).
  { unfold e1, brs1. simpl.
    split; [ | split; [exact I | exact I]].
    constructor; [intro H; destruct H | constructor]. }
  destruct (Hthm P0 nil Gam1 e1 Gam1 (BExpr (ECon 100 nil)) H1
              (fun w => w) (fun w => w) mutual_inverse_id
              nil (eq_sym (map_id nil)) Gam1 e2 HBA (NHeapAlpha_refl Gam1)
              (fun w H => False_rect _ H) (fun w H => False_rect _ H)
              HScoped HProgBrsUniq HClosed HBrsUniqHeap Heclosed1 He1BrsUniq
              Gam1 (BExpr (ECon 200 nil)) H2)
    as [sigma [tau [Hmi [Hext [Halpha Heq]]]]].
  simpl in Heq.
  discriminate Heq.
Qed.

(* Print Assumptions NEval_left_confluence_stmt_is_false. reports "Closed
   under the global context" -- zero axioms, fully verified. *)
Print Assumptions NEval_left_confluence_stmt_is_false.
