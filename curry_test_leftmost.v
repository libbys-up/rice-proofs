Require Import List Arith Lia.
Import ListNotations.
Require Import curry.

(* ==================================================================== *)
(* GEval is a DETERMINISTIC execution model (a real compiler has to be):  *)
(* G_CaseChoice only ever forwards to the FIRST operand of an EChoice,    *)
(* never the second (there is no companion rule).  NEval's own N_Or is    *)
(* genuinely nondeterministic (i = x \/ i = y).  So "GEval reaches v      *)
(* implies NEval reaches v" (theorem2 as stated) cannot be strengthened   *)
(* to a full "NEval reaches v implies GEval reaches v" -- NEval can take   *)
(* the right branch, which GEval structurally never can.                  *)
(*                                                                        *)
(* NEval_left below is NEval with that extra nondeterminism removed:      *)
(* N_Or is forced to i = x (the FIRST EChoice operand), exactly matching  *)
(* G_CaseChoice's own bias.  Every NEval_left derivation is trivially      *)
(* also a valid NEval derivation (NEval_left_to_NEval below), so if we    *)
(* can prove                                                              *)
(*    GEval P G e G' v -> exists Gam', NEval_left P nil Gam e Gam' v'     *)
(* that is STRICTLY SUFFICIENT to reprove theorem2 exactly as stated.      *)
(* The point of doing it via NEval_left rather than NEval directly: the    *)
(* obstruction that blocks curry.v's own `NEval_fwd_transfer` is exactly   *)
(* an inability to relate two INDEPENDENT evaluations of "the same"        *)
(* sub-expression (does forcing y disturb x, does re-deriving y's value    *)
(* inside a replayed continuation give the same result) -- and every       *)
(* historical counterexample in curry.v that exploited this                *)
(* (`blackhole_counterexample`, the removed `fc_*` section) did so by       *)
(* having an Or-choice pick DIFFERENT branches on the two evaluations.      *)
(* Removing Or's nondeterminism should remove that entire attack surface:  *)
(* re-deriving "the same" sub-computation from an equivalent heap now       *)
(* has to reach the SAME result, by determinism -- turning the missing     *)
(* "NEval soundness relative to G" non-interference fact into an ordinary   *)
(* confluence-under-replay argument.                                       *)
(* ==================================================================== *)

Section NatSemanticsLeft.
Variable P : Prog.

Inductive NEval_left : list var -> NHeap -> Blk -> NHeap -> Blk -> Prop :=
| NL_VarCons : forall F G x c args,
    G x = Some (BExpr (ECon c args)) ->
    NEval_left F G (BExpr (EVar x)) G (BExpr (ECon c args))
| NL_VarSelf : forall F G x,
    G x = Some (BExpr (EVar x)) ->
    NEval_left F G (BExpr (EVar x)) G (BExpr (EVar x))
| NL_VarFree : forall F G x,
    G x = Some (BExpr EFree) ->
    NEval_left F G (BExpr (EVar x)) (hupd G x (BExpr (EVar x))) (BExpr (EVar x))
| NL_VarExp : forall F G x e G1 v,
    ~ In x F ->
    G x = Some e ->
    (forall c args, e <> BExpr (ECon c args)) ->
    e <> BExpr (EVar x) ->
    e <> BExpr EFree ->
    NEval_left (x :: F) G e G1 v ->
    NEval_left F G (BExpr (EVar x)) (hupd G1 x v) v
| NL_ValFree : forall F G,
    NEval_left F G (BExpr EFree) G (BExpr EFree)
| NL_ValCon : forall F G c args,
    NEval_left F G (BExpr (ECon c args)) G (BExpr (ECon c args))
| NL_Fun : forall F G G1 f args ps body v s,
    P f = Some (ps, body) ->
    length ps = length args ->
    injective s ->
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) ->
    (forall y, ~ In y ps -> G (s y) = None) ->
    NEval_left F G (rename_b s body) G1 v ->
    NEval_left F G (BExpr (EFun f args)) G1 v
| NL_Let : forall F G G1 x (e : Expr0) k v,
    G x = None ->
    NEval_left F (hupd G x (let_content x e)) k G1 v ->
    NEval_left F G (BLet x e k) G1 v
(* THE ONLY CHANGE from NEval: N_Or's `i = x \/ i = y` becomes just `i = x` --
   always the FIRST EChoice operand, matching G_CaseChoice exactly. *)
| NL_Or : forall F G x y G1 v,
    NEval_left F G (BExpr (EVar x)) G1 v ->
    NEval_left F G (BExpr (EChoice x y)) G1 v
| NL_Select : forall F G x c zs brs ys body G1 v G2,
    NEval_left F G (BExpr (EVar x)) G1 (BExpr (ECon c zs)) ->
    List.In (c, ys, body) brs ->
    length ys = length zs ->
    NEval_left F G1 (rename_b (zipsubst ys zs) body) G2 v ->
    NEval_left F G (BCase x brs) G2 v
| NL_Guess : forall F G x G1 x' c1 ys1 body1 brs G2 v ws,
    NEval_left F G (BExpr (EVar x)) G1 (BExpr (EVar x')) ->
    hd_error brs = Some (c1, ys1, body1) ->
    length ws = length ys1 ->
    NoDup ws ->
    (forall w, In w ws -> G1 w = None) ->
    NEval_left F (hupd_list (hupd G1 x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
           (rename_b (zipsubst ys1 ws) body1)
           G2 v ->
    NEval_left F G (BCase x brs) G2 v.

End NatSemanticsLeft.

Lemma NEval_left_to_NEval :
  forall P F Gam e Gam' v, NEval_left P F Gam e Gam' v -> NEval P F Gam e Gam' v.
Proof.
  intros P F Gam e Gam' v H.
  induction H as
    [ F0 G z c args Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c args
    | F0 G G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ].
  - apply N_VarCons. exact Hz.
  - apply N_VarSelf. exact Hz.
  - apply N_VarFree. exact Hz.
  - eapply N_VarExp; [exact HzF | exact Hz | exact Hne1 | exact Hne2 | exact Hne3 | exact IH].
  - apply N_ValFree.
  - apply N_ValCon.
  - eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | exact IH].
  - apply N_Let; [exact HzFresh | exact IH].
  - eapply N_Or; [left; reflexivity | exact IH].
  - eapply N_Select; [exact IH1 | exact HIn | exact Hlen | exact IH2].
  - eapply N_Guess; [exact IH1 | exact Hhd | exact Hlen | exact HND | exact Hfr | exact IH2].
Qed.

(* Port of curry.v's NEval_pointwise_heap. *)
Lemma NEval_left_pointwise_heap :
  forall P F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  forall Gam2, (forall w, Gam2 w = Gam w) ->
  exists Gam2', NEval_left P F Gam2 e Gam2' v /\ (forall w, Gam2' w = Gam' w).
Proof.
  intros P F Gam e Gam' v H.
  induction H as
    [ F0 G z c args Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HnF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c args
    | F0 G G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Gam2 Heq.
  - exists Gam2. split; [apply NL_VarCons; rewrite Heq; exact Hz | intro w; apply Heq].
  - exists Gam2. split; [apply NL_VarSelf; rewrite Heq; exact Hz | intro w; apply Heq].
  - exists (hupd Gam2 z (BExpr (EVar z))). split.
    + apply NL_VarFree; rewrite Heq; exact Hz.
    + intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists (hupd G2' z v0). split.
    + eapply NL_VarExp;
        [exact HnF | rewrite Heq; exact Hz | exact Hne1 | exact Hne2 | exact Hne3 | exact HNE2].
    + intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq2].
  - exists Gam2. split; [apply NL_ValFree | intro w; apply Heq].
  - exists Gam2. split; [apply NL_ValCon | intro w; apply Heq].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE2].
    intros w Hw. rewrite Heq. exact (Hfresh w Hw).
  - assert (Heq' : forall w, hupd Gam2 z (let_content z e0) w = hupd G z (let_content z e0) w).
    { intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq]. }
    destruct (IH (hupd Gam2 z (let_content z e0)) Heq') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    apply NL_Let; [rewrite Heq; exact HzFresh | exact HNE2].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists G2'. split; [eapply NL_Or; exact HNE2 | exact Heq2].
  - destruct (IH1 Gam2 Heq) as [G1' [HNE1 Heq1]].
    assert (Heq1' : forall w, G1' w = G1 w) by exact Heq1.
    destruct (IH2 G1' Heq1') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply NL_Select; [exact HNE1 | exact HIn | exact Hlen | exact HNE2].
  - destruct (IH1 Gam2 Heq) as [G1' [HNE1 Heq1]].
    assert (Heq'0 : forall w, hupd G1' z' (BExpr (ECon c1 ws)) w = hupd G1 z' (BExpr (ECon c1 ws)) w).
    { intro w; unfold hupd; destruct (Nat.eqb w z'); [reflexivity | apply Heq1]. }
    assert (Heq' : forall w,
      hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w =
      hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w)
      by (apply hupd_list_pointwise; exact Heq'0).
    destruct (IH2 _ Heq') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply NL_Guess; [exact HNE1 | exact Hhd | exact Hlen | exact HND | | exact HNE2].
    intros w Hw. rewrite Heq1. exact (Hfr w Hw).
Qed.

(* Port of curry.v's NEval_evar_forced_shape. *)
Lemma NEval_left_evar_shape :
  forall P F Gam y G' v, NEval_left P F Gam (BExpr (EVar y)) G' v ->
  (Gam y = Some v /\ G' = Gam /\ (exists c args, v = BExpr (ECon c args))) \/
  (Gam y = Some (BExpr (EVar y)) /\ G' = Gam /\ v = BExpr (EVar y)) \/
  (Gam y = Some (BExpr EFree) /\ G' = hupd Gam y (BExpr (EVar y)) /\ v = BExpr (EVar y)) \/
  (~ In y F /\ exists e0 G1,
     Gam y = Some e0 /\ (forall c args, e0 <> BExpr (ECon c args)) /\
     e0 <> BExpr (EVar y) /\ e0 <> BExpr EFree /\
     NEval_left P (y :: F) Gam e0 G1 v /\ G' = hupd G1 y v).
Proof.
  intros P F Gam y G' v H.
  remember (BExpr (EVar y)) as target eqn:Ht.
  revert y Ht.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v1 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v1 Hrec IH
    | F0 G0 z c zs brs ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros y Ht; try discriminate Ht.
  - injection Ht as Ht; subst z.
    left. split; [exact Hz | split; [reflexivity | exists c, args; reflexivity]].
  - injection Ht as Ht; subst z.
    right; left. split; [exact Hz | split; [reflexivity | reflexivity]].
  - injection Ht as Ht; subst z.
    right; right; left. split; [exact Hz | split; [reflexivity | reflexivity]].
  - injection Ht as Ht; subst z.
    right; right; right.
    split; [exact HzF | exists e0, G1].
    split; [exact Hz | split; [exact Hne1 | split; [exact Hne2 | split; [exact Hne3 | split; [exact Hrec | reflexivity]]]]].
Qed.

(* Port of curry.v's NEval_bcase_forced_shape. *)
Lemma NEval_left_bcase_shape :
  forall P F Gam x brs G' v, NEval_left P F Gam (BCase x brs) G' v ->
  (exists c zs ys body G1,
     NEval_left P F Gam (BExpr (EVar x)) G1 (BExpr (ECon c zs)) /\
     In (c, ys, body) brs /\ length ys = length zs /\
     NEval_left P F G1 (rename_b (zipsubst ys zs) body) G' v)
  \/
  (exists x' G1 c1 ys1 body1 ws,
     NEval_left P F Gam (BExpr (EVar x)) G1 (BExpr (EVar x')) /\
     hd_error brs = Some (c1, ys1, body1) /\ length ws = length ys1 /\ NoDup ws /\
     (forall w, In w ws -> G1 w = None) /\
     NEval_left P F (hupd_list (hupd G1 x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
           (rename_b (zipsubst ys1 ws) body1) G' v).
Proof.
  intros P F Gam x brs G' v H.
  remember (BCase x brs) as target eqn:Ht.
  revert x brs Ht.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v1 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v1 Hrec IH
    | F0 G0 z c zs brs0 ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1 ys1 body1 brs0 G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros x brs Ht; try discriminate Ht.
  - injection Ht as Ht1 Ht2. subst z brs0.
    left. exists c, zs, ys, body, G1.
    split; [exact Hrec1 | split; [exact HIn | split; [exact Hlen | exact Hrec2]]].
  - injection Ht as Ht1 Ht2. subst z brs0.
    right. exists z', G1, c1, ys1, body1, ws.
    split; [exact Hrec1 | split; [exact Hhd | split; [exact Hlen | split; [exact HND |
      split; [exact Hfr | exact Hrec2]]]]].
Qed.

(* Forcing a variable always memoizes ITS OWN slot to the result, whichever  *)
(* of the four rules actually fires -- no need to go through HeapCorr at all. *)
Lemma NEval_left_own_slot :
  forall P F G y0 G' v, NEval_left P F G (BExpr (EVar y0)) G' v -> G' y0 = Some v.
Proof.
  intros P F G y0 G' v H.
  destruct (NEval_left_evar_shape P F G y0 G' v H) as
    [ [Hcase [HeqG _]]
    | [ [Hcase [HeqG Heqv]]
      | [ [Hcase [HeqG Heqv]]
        | [_ [e0 [G1 [Hz [_ [_ [_ [_ HeqG]]]]]]]]] ] ].
  - subst G'. exact Hcase.
  - subst G' v. exact Hcase.
  - subst G' v. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
  - subst G'. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
Qed.

(* ==================================================================== *)
(* The counterexample motivating ChainConsistent/HeapCorr2 below (bare    *)
(* HeapCorr allows x's witness to be "ahead of" y's in a way no real       *)
(* execution ever produces) has been moved to failed_attempts.v (section   *)
(* 3), along with the confirmation that ChainConsistent excludes it        *)
(* (section 4).  ChainConsistent and HeapCorr2 themselves are NOT dead --   *)
(* they remain the live, load-bearing invariant for everything below       *)
(* (NEval_left_force_free_sound, the theorem2_G_CaseXXX_case theorems,      *)
(* and the whole HeapCorr2_update_* lemma layer), kept here as the         *)
(* HeapCorr2-era apparatus pending a HeapCorr-based port (see             *)
(* THEOREM2_PROCESS_NOTES.md and failed_attempts.v section 5 for why       *)
(* HeapCorr2 itself later turned out not to be strong enough to serve as    *)
(* theorem2's own ambient invariant either).                               *)
(* ==================================================================== *)

Definition ChainConsistent (G : Graph) (Gam : NHeap) : Prop :=
  forall x y, G x = Some (GFwd y) ->
    forall c args, Gam x = Some (BExpr (ECon c args)) -> Gam y = Some (BExpr (ECon c args)).

(* AliasConsistent: whenever x forwards to y and x's OWN Nat-heap witness
   is a "skip-ahead" alias EVar w (w <> y, i.e. NOT the direct, one-hop
   CorrE_FwdHere shape), y's OWN witness must ALREADY be that SAME alias
   EVar w too -- never some OTHER, unrelated location, and never still the
   "un-forced" EVar y.  ChainConsistent's own counterpart for the
   ACHIEVED-constructor case; this is the analogous fact for the
   compressed-ALIAS case, and is exactly what rules out the "x0 skips
   ahead via some UNRELATED w0', y0 shows something else" scenario that
   blocked G_CaseFwd across S4/S7/S8/S9 (see DEAD_ENDS.md).

   Operational justification (mirrors ChainConsistent's own): Gam x starts
   life as EXACTLY EVar y (created together with the GFwd edge).  The ONLY
   way it can later differ is by x itself being forced -- which recurses
   INTO forcing y, and NL_VarExp's own memoization sets BOTH x and y to
   the identical final value in that SAME operation.  So x's alias can
   never "outrun" y's to a DIFFERENT target; the only way y's witness
   changes WITHOUT x's changing is y being forced independently, in which
   case x's witness is untouched and still exactly EVar y (the vacuous,
   disjunct-1 case for THIS invariant). *)
Definition AliasConsistent (G : Graph) (Gam : NHeap) : Prop :=
  forall x y, G x = Some (GFwd y) ->
    forall w, Gam x = Some (BExpr (EVar w)) -> w <> y -> Gam y = Some (BExpr (EVar w)).

Definition HeapCorr2 (G : Graph) (Gam : NHeap) : Prop :=
  HeapCorr G Gam /\ ChainConsistent G Gam.

(* Sanity check 1: HeapCorr2 is preserved by extending at a completely      *)
(* fresh location (the G_Let case) -- mirrors curry.v's HeapCorr_extend,    *)
(* plus showing ChainConsistent survives too (trivially: a fresh location    *)
(* can't be involved in any EXISTING forwarding pair, on EITHER end, since    *)
(* nothing already points at it and it doesn't yet point anywhere itself     *)
(* unless its own new content is GFwd, and even then it's a BRAND NEW        *)
(* pair with a not-yet-promoted witness). *)
(* NOTE: needs `WellFoundedFwd G` -- without it, HeapCorr's bare definition   *)
(* doesn't even rule out a DANGLING forward pointer (`G p = GFwd x` while     *)
(* `G x = None`), which would let a totally unrelated, pre-existing forward   *)
(* edge "coincidentally" target the very location being freshly bound here.   *)
(* WellFoundedFwd (already in curry.v) says every GFwd chain terminates at a  *)
(* real, non-None location, which is exactly what rules that out. *)
Lemma HeapCorr2_extend :
  forall G Gam x e,
    HeapCorr2 G Gam -> WellFoundedFwd G -> G x = None ->
    HeapCorr2 (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x e [HGC HCC] HWF Hx.
  split.
  - apply HeapCorr_extend; assumption.
  - intros p q Hpq c args Hpc.
    destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + (* p = x : (hupd G x (GExpr e)) x = GExpr e, which can never equal
         GFwd q regardless of e's own shape. *)
      subst p. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq.
    + (* p <> x : both Hpq and Hpc reduce to their G/Gam-only content. *)
      rewrite (hupd_neq G x (GExpr e) p Hnepx) in Hpq.
      assert (Hqx : q <> x).
      { intro Heq; subst q.
        destruct (HWF p x Hpq) as [z Hcl].
        inversion Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0]; subst.
        - congruence.
        - assert (y0 = x) by congruence; subst y0.
          exact (ContractLoc_dom G x z Hcl0 Hx). }
      rewrite (hupd_neq Gam x (let_content x e) p Hnepx) in Hpc.
      rewrite (hupd_neq Gam x (let_content x e) q Hqx).
      exact (HCC p q Hpq c args Hpc).
Qed.

(* ==================================================================== *)
(* The key promotion step: does ChainConsistent survive updating z's OWN  *)
(* Gam-witness to the achieved constructor (mirroring what curry.v's       *)
(* NEval_fwd_transfer_fwdhere_con already does via HeapCorr_update_consistent *)
(* + CorrE_FwdAchievedCon)?  Answer: yes, PROVIDED z's own forward target   *)
(* y has ALREADY achieved that same constructor in Gam first -- i.e.        *)
(* PROVIDED promotion happens in dependency order (target before source),   *)
(* which is exactly what N_VarExp's own recursive-then-memoize structure    *)
(* naturally enforces (the inner call finishes and memoizes before the      *)
(* outer one does).  Only one side condition is genuinely needed: z does     *)
(* not forward to itself.  The other tricky sub-case (some OTHER, already-    *)
(* achieved p also forwarding to z) is not excluded by hypothesis -- it's      *)
(* RECONCILED: p's own achieved value must chase, via z, through the SAME       *)
(* canonical target w that z's own achievement uses (ContractLoc is             *)
(* functional), so p's existing achieved constructor is FORCED to already        *)
(* equal c/args -- the update doesn't change what p sees, it just confirms it. *)
Lemma HeapCorr2_update_achieved :
  forall G Gam z y w c args,
    HeapCorr2 G Gam ->
    G z = Some (GFwd y) ->
    y <> z ->
    ContractLoc G y w ->
    G w = Some (GExpr (ECon c args)) ->
    Gam y = Some (BExpr (ECon c args)) ->
    HeapCorr2 G (hupd Gam z (BExpr (ECon c args))).
Proof.
  intros G Gam z y w c args [HGC HCC] Hgz Hyz Hcl Hgw Hgamy.
  split.
  - apply HeapCorr_update_consistent; [exact HGC | eapply CorrE_FwdAchievedCon; [exact Hgz | exact Hcl | exact Hgw]].
  - intros p q Hpq c' args' Hpc.
    destruct (Nat.eq_dec p z) as [Heqpz | Hnepz].
    + subst p.
      assert (Hqy : q = y) by congruence. subst q.
      unfold hupd in Hpc. rewrite Nat.eqb_refl in Hpc.
      injection Hpc as Hceq Hargseq; subst c' args'.
      rewrite (hupd_neq Gam z (BExpr (ECon c args)) y Hyz). exact Hgamy.
    + unfold hupd in Hpc. rewrite <- Nat.eqb_neq in Hnepz. rewrite Hnepz in Hpc.
      apply Nat.eqb_neq in Hnepz.
      destruct (Nat.eq_dec q z) as [Heqqz | Hneqz].
      * subst q.
        unfold hupd. rewrite Nat.eqb_refl.
        specialize (HGC p). rewrite Hpq in HGC. destruct HGC as [b [Hb HCE]].
        assert (Hbeq : b = BExpr (ECon c' args')) by congruence. subst b.
        destruct (CorrE_con_to_contractloc G p c' args' HCE) as [z1 [Hcl1 Hz1]].
        assert (Hclz : ContractLoc G z z1).
        { inversion Hcl1 as [x1 e1 Hx1 | x1 y1 z1' Hx1 Hcl1'']; subst.
          - rewrite Hpq in Hx1. discriminate Hx1.
          - rewrite Hpq in Hx1. injection Hx1 as Hx1; subst y1. exact Hcl1''. }
        assert (Hcl1' : ContractLoc G y z1).
        { inversion Hclz as [x2 e2 Hx2 | x2 y2 z2 Hx2 Hcl2]; subst.
          - rewrite Hgz in Hx2. discriminate Hx2.
          - rewrite Hgz in Hx2. injection Hx2 as Hx2; subst y2. exact Hcl2. }
        assert (Hz1w : z1 = w) by (eapply ContractLoc_functional; [exact Hcl1' | exact Hcl]).
        subst z1. rewrite Hgw in Hz1. injection Hz1 as Hceq Hargseq. subst c' args'.
        reflexivity.
      * rewrite (hupd_neq Gam z (BExpr (ECon c args)) q Hneqz).
        exact (HCC p q Hpq c' args' Hpc).
Qed.

(* Narrowing an existing free-variable location x to a constructor          *)
(* (G_CaseConFree) also preserves ChainConsistent.  The interesting sub-case *)
(* (some p already forwards to x, p already achieved Con) is actually        *)
(* VACUOUS here: while G x = Free (direct, non-forwarding), ContractLoc from  *)
(* x can only ever be x itself (CL_Here), so any p with G p = GFwd x could    *)
(* only ever have achieved Con via chasing to a location holding Free, which  *)
(* CorrE_FwdAchievedCon's own definition never allows -- so Gam p could only   *)
(* ever have been the lazy alias EVar x, never Con, before this update.        *)
Lemma HeapCorr2_update_free :
  forall G Gam x c args,
    HeapCorr2 G Gam -> G x = Some (GExpr EFree) ->
    HeapCorr2 (hupd G x (GExpr (ECon c args))) (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x c args [HGC HCC] Hx.
  split.
  - apply HeapCorr_update_free; assumption.
  - intros p q Hpq c' args' Hpc.
    destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + subst p. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq.
    + rewrite (hupd_neq G x (GExpr (ECon c args)) p Hnepx) in Hpq.
      rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx) in Hpc.
      destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
      * subst q.
        exfalso.
        specialize (HGC p). rewrite Hpq in HGC. destruct HGC as [b [Hb HCE]].
        assert (Hbeq : b = BExpr (ECon c' args')) by congruence. subst b.
        inversion HCE as
          [ x0 c0 args0 H0 Heq1 Heq2
          | x0 H0 Heq1 Heq2
          | x0 f0 args0 H0 Heq1 Heq2
          | x0 y0 z0 H0 Heq1 Heq2
          | x0 z0 H0 Heq1 Heq2
          | x0 H0 Heq1 Heq2
          | x0 y0 H0 Heq1 Heq2
          | x0 y0 z0 c0 args0 H0 Hcl0 Hz0 Heq1 Heq2 ]; subst; try discriminate Heq2.
        -- congruence.
        -- (* FwdAchievedCon : ContractLoc G x z0 with G x = Free forces z0 = x
              (CL_Here), so G z0 = Free, contradicting G z0 = Con c0 args0. *)
           assert (Hy0x : y0 = x) by congruence. subst y0.
           assert (Hz0x : z0 = x) by (eapply ContractLoc_nonfwd; [exact Hx | exact Hcl0]).
           subst z0. rewrite Hx in Hz0. discriminate Hz0.
      * rewrite (hupd_neq Gam x (BExpr (ECon c args)) q Hneqx).
        exact (HCC p q Hpq c' args' Hpc).
Qed.

(* ==================================================================== *)
(* G_CaseChoice and G_CaseFun both update an EXISTING (non-fresh) graph    *)
(* location x's DIRECT content to something new -- either straight to      *)
(* another direct value (G_CaseFun landing on Con/Free/Choice/Bot), or to   *)
(* a BRAND NEW forward edge (G_CaseChoice's EChoice->GFwd, or G_CaseFun     *)
(* landing on a bare variable read).  Both preserve ChainConsistent for      *)
(* the SAME underlying reason as HeapCorr2_update_free: x's OLD content       *)
(* was never Con-shaped (EFun/EChoice, like Free, can't be an achieved         *)
(* chase target), so nothing could have ALREADY achieved a shortcut THROUGH    *)
(* x before the update -- the tricky sub-case is vacuous by construction,       *)
(* not by luck, exactly as before.  We generalize ContractLoc_update_free_other  *)
(* / CorrE_update_free_other (both in curry.v, previously specific to EFree)      *)
(* to work for ANY non-forwarding, non-Con starting content.                       *)
(* ==================================================================== *)

Lemma ContractLoc_update_nonfwd_other :
  forall G y0 ztarget, ContractLoc G y0 ztarget ->
  forall x gnew, (forall w, G x <> Some (GFwd w)) -> ztarget <> x ->
  ContractLoc (hupd G x gnew) y0 ztarget.
Proof.
  intros G y0 ztarget H.
  induction H as [x0 e0 H0 | x0 y1 z0 H0 Hcl0 IH]; intros x gnew Hxnonfwd Hzx.
  - eapply CL_Here. rewrite (hupd_neq G x gnew x0 Hzx). exact H0.
  - assert (Hx0x : x0 <> x).
    { intro Heq; subst x0. exact (Hxnonfwd y1 H0). }
    eapply CL_Fwd.
    + rewrite (hupd_neq G x gnew x0 Hx0x). exact H0.
    + apply IH; [exact Hxnonfwd | exact Hzx].
Qed.

(* Companion to ContractLoc_update_nonfwd_other, for the OPPOSITE case: the
   chain's own target IS the location being updated. Since x is
   non-forwarding both before and after, x can only ever appear as the
   chain's OWN final hop (a non-forwarding location always terminates a
   ContractLoc chase), so every hop strictly before it is untouched by the
   update, and the final CL_Here step just uses x's NEW content instead. *)
Lemma ContractLoc_update_nonfwd_to_target :
  forall G y0 x, ContractLoc G y0 x ->
  forall enew, (forall w, G x <> Some (GFwd w)) ->
  ContractLoc (hupd G x (GExpr enew)) y0 x.
Proof.
  intros G y0 x H.
  induction H as [x0 e0 H0 | x0 y1 z0 H0 Hcl0 IH]; intros enew Hxnonfwd.
  - eapply CL_Here. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
  - assert (Hx0z0 : x0 <> z0) by (intro Heq; subst x0; exact (Hxnonfwd y1 H0)).
    eapply CL_Fwd.
    + rewrite (hupd_neq G z0 (GExpr enew) x0 Hx0z0). exact H0.
    + exact (IH enew Hxnonfwd).
Qed.

(* Companion for the case where x's NEW content is itself a Fwd edge (so,
   unlike ContractLoc_update_nonfwd_to_target, x can no longer serve as a
   CL_Here terminal at all): any chain that USED to terminate exactly at x
   now continues one hop further, through x's own new edge, to wherever
   THAT was already known to reach. *)
Lemma ContractLoc_update_choice_extend :
  forall G w x, ContractLoc G w x ->
  forall y ytgt, (forall ww, G x <> Some (GFwd ww)) ->
  ContractLoc (hupd G x (GFwd y)) y ytgt ->
  ContractLoc (hupd G x (GFwd y)) w ytgt.
Proof.
  intros G w x H.
  induction H as [x0 e0 H0 | x0 y1 z0 H0 Hcl0 IH]; intros y ytgt Hxnonfwd Hclyt.
  - eapply CL_Fwd.
    + unfold hupd; rewrite Nat.eqb_refl. reflexivity.
    + exact Hclyt.
  - assert (Hx0z0 : x0 <> z0) by (intro Heq; subst x0; exact (Hxnonfwd y1 H0)).
    eapply CL_Fwd.
    + rewrite (hupd_neq G z0 (GFwd y) x0 Hx0z0). exact H0.
    + exact (IH y ytgt Hxnonfwd Hclyt).
Qed.

Lemma CorrE_update_nonfwd_noncon_other :
  forall G z b, CorrE G z b ->
  forall x gnew, (forall w, G x <> Some (GFwd w)) -> (forall c args, G x <> Some (GExpr (ECon c args))) ->
  z <> x ->
  CorrE (hupd G x gnew) z b.
Proof.
  intros G z b H.
  induction H as
    [ z0 c0 args0 H0
    | z0 H0
    | z0 f0 fargs0 H0
    | z0 y0 w0 H0
    | z0 w0 H0
    | z0 H0
    | z0 y0 H0
    | z0 y0 z1 c1 args1 H0 Hcl0 Hz1
    ];
  intros x gnew Hxnonfwd Hxnoncon Hzx.
  - eapply CorrE_Con.    rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_Free.   rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_Fun.    rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_Choice. rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_VarThunk. rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_Bot.    rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - eapply CorrE_FwdHere. rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
  - assert (Hz1x : z1 <> x) by (intro Heq; subst z1; exact (Hxnoncon c1 args1 Hz1)).
    eapply CorrE_FwdAchievedCon.
    + rewrite (hupd_neq G x gnew z0 Hzx). exact H0.
    + exact (ContractLoc_update_nonfwd_other G y0 z1 Hcl0 x gnew Hxnonfwd Hz1x).
    + rewrite (hupd_neq G x gnew z1 Hz1x). exact Hz1.
Qed.

(* The general update step: x's OLD content was direct and non-Con        *)
(* (EFun/EChoice/etc, matching G_CaseFun/CaseChoice's own premises), and     *)
(* it updates to ANY new graph content gnew, with Gam's witness for x         *)
(* updated to any CorrE-valid witness bnew for gnew.  ChainConsistent           *)
(* survives regardless of what gnew/bnew are (even a brand new GFwd edge),       *)
(* because the only way it could break -- something already having achieved       *)
(* a shortcut THROUGH x -- was already impossible before the update. *)
(* Two clean, split lemmas rather than one fully general one: the update  *)
(* always installs a LAZY witness for x (never the achieved shortcut) --  *)
(* achieving x is handled separately, later, by HeapCorr2_update_achieved *)
(* above, once whatever x now points at has ITSELF actually resolved.     *)
(* Keeping the two steps separate is exactly what makes the p = x branch  *)
(* of ChainConsistent trivial in both cases below: a lazy witness is never *)
(* Con-shaped, so the antecedent is simply false. *)

Lemma HeapCorr2_update_to_direct :
  forall G Gam x gold e,
    HeapCorr2 G Gam ->
    G x = Some gold ->
    (forall w, gold <> GFwd w) ->
    (forall c args, gold <> GExpr (ECon c args)) ->
    HeapCorr2 (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x gold e [HGC HCC] Hgx Hnonfwd Hnoncon.
  assert (Hxnonfwd : forall w, G x <> Some (GFwd w))
    by (intros w Heq; rewrite Hgx in Heq; injection Heq as Heq; exact (Hnonfwd w Heq)).
  assert (Hxnoncon : forall c args, G x <> Some (GExpr (ECon c args)))
    by (intros c args Heq; rewrite Hgx in Heq; injection Heq as Heq; exact (Hnoncon c args Heq)).
  split.
  - intro p. destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + subst p. unfold hupd. rewrite Nat.eqb_refl.
      eexists. split; [reflexivity | ].
      destruct e; simpl.
      * eapply CorrE_VarThunk. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * eapply CorrE_Bot. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * eapply CorrE_Free. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * eapply CorrE_Choice. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * eapply CorrE_Fun. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * eapply CorrE_Con. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (hupd_neq G x (GExpr e) p Hnepx).
      specialize (HGC p). destruct (G p) as [gp | ] eqn:EGp.
      * destruct HGC as [b [Hb HCE]].
        exists b. split.
        -- rewrite (hupd_neq Gam x (let_content x e) p Hnepx). exact Hb.
        -- eapply CorrE_update_nonfwd_noncon_other; [exact HCE | exact Hxnonfwd | exact Hxnoncon | exact Hnepx].
      * rewrite (hupd_neq Gam x (let_content x e) p Hnepx). exact HGC.
  - intros p q Hpq c' args' Hpc.
    destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + subst p. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq.
    + rewrite (hupd_neq G x (GExpr e) p Hnepx) in Hpq.
      rewrite (hupd_neq Gam x (let_content x e) p Hnepx) in Hpc.
      destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
      * subst q. exfalso.
        specialize (HGC p). rewrite Hpq in HGC. destruct HGC as [b [Hb HCE]].
        assert (Hbeq : b = BExpr (ECon c' args')) by congruence. subst b.
        destruct (CorrE_con_to_contractloc G p c' args' HCE) as [z0 [Hcl0 Hz0]].
        assert (Hz0x : z0 <> x) by (intro Heq; subst z0; exact (Hxnoncon c' args' Hz0)).
        assert (Hcl0' : ContractLoc G x z0).
        { inversion Hcl0 as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hcl1]; subst.
          - congruence.
          - rewrite Hpq in Hx1. injection Hx1 as Hx1; subst y1. exact Hcl1. }
        assert (Hgxe : exists e', gold = GExpr e').
        { destruct gold as [e' | w']; [exists e'; reflexivity | exfalso; exact (Hnonfwd w' eq_refl)]. }
        destruct Hgxe as [e' Hgxe]. rewrite Hgxe in Hgx.
        assert (Hz0eqx : z0 = x) by (eapply ContractLoc_nonfwd; [exact Hgx | exact Hcl0']).
        exact (Hz0x Hz0eqx).
      * rewrite (hupd_neq Gam x (let_content x e) q Hneqx).
        exact (HCC p q Hpq c' args' Hpc).
Qed.

Lemma HeapCorr2_update_to_fwd_lazy :
  forall G Gam x gold y,
    HeapCorr2 G Gam ->
    G x = Some gold ->
    (forall w, gold <> GFwd w) ->
    (forall c args, gold <> GExpr (ECon c args)) ->
    HeapCorr2 (hupd G x (GFwd y)) (hupd Gam x (BExpr (EVar y))).
Proof.
  intros G Gam x gold y [HGC HCC] Hgx Hnonfwd Hnoncon.
  assert (Hxnonfwd : forall w, G x <> Some (GFwd w))
    by (intros w Heq; rewrite Hgx in Heq; injection Heq as Heq; exact (Hnonfwd w Heq)).
  assert (Hxnoncon : forall c args, G x <> Some (GExpr (ECon c args)))
    by (intros c args Heq; rewrite Hgx in Heq; injection Heq as Heq; exact (Hnoncon c args Heq)).
  split.
  - intro p. destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + subst p. unfold hupd. rewrite Nat.eqb_refl.
      eexists. split; [reflexivity | ]. apply CorrE_FwdHere. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (hupd_neq G x (GFwd y) p Hnepx).
      specialize (HGC p). destruct (G p) as [gp | ] eqn:EGp.
      * destruct HGC as [b [Hb HCE]].
        exists b. split.
        -- rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx). exact Hb.
        -- eapply CorrE_update_nonfwd_noncon_other; [exact HCE | exact Hxnonfwd | exact Hxnoncon | exact Hnepx].
      * rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx). exact HGC.
  - intros p q Hpq c' args' Hpc.
    destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
    + subst p. unfold hupd in Hpc. rewrite Nat.eqb_refl in Hpc. discriminate Hpc.
    + rewrite (hupd_neq G x (GFwd y) p Hnepx) in Hpq.
      rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx) in Hpc.
      destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
      * subst q. exfalso.
        specialize (HGC p). rewrite Hpq in HGC. destruct HGC as [b [Hb HCE]].
        assert (Hbeq : b = BExpr (ECon c' args')) by congruence. subst b.
        destruct (CorrE_con_to_contractloc G p c' args' HCE) as [z0 [Hcl0 Hz0]].
        assert (Hz0x : z0 <> x) by (intro Heq; subst z0; exact (Hxnoncon c' args' Hz0)).
        assert (Hcl0' : ContractLoc G x z0).
        { inversion Hcl0 as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hcl1]; subst.
          - congruence.
          - rewrite Hpq in Hx1. injection Hx1 as Hx1; subst y1. exact Hcl1. }
        assert (Hgxe : exists e', gold = GExpr e').
        { destruct gold as [e' | w']; [exists e'; reflexivity | exfalso; exact (Hnonfwd w' eq_refl)]. }
        destruct Hgxe as [e' Hgxe]. rewrite Hgxe in Hgx.
        assert (Hz0eqx : z0 = x) by (eapply ContractLoc_nonfwd; [exact Hgx | exact Hcl0']).
        exact (Hz0x Hz0eqx).
      * rewrite (hupd_neq Gam x (BExpr (EVar y)) q Hneqx).
        exact (HCC p q Hpq c' args' Hpc).
Qed.

(* ==================================================================== *)
(* REASSEMBLY: rebuilding theorem2 with NEval_left + HeapCorr2 throughout. *)
(* Port of curry.v's force_var_N/force_var, needed for the G_Var case --   *)
(* this only ever uses NL_VarCons/NL_VarExp (no Or/Fun involved in chasing  *)
(* a pure alias chain to a constructor), so it's a mostly mechanical port,   *)
(* strengthened at the one memoization step to ALSO carry ChainConsistent    *)
(* via HeapCorr2_update_achieved. *)
(* ==================================================================== *)

Lemma CorrE_evar_shape_for_fwd :
  forall G x y0 y1, G x = Some (GFwd y0) -> CorrE G x (BExpr (EVar y1)) -> y1 = y0.
Proof.
  intros G x y0 y1 Hgx HCE.
  destruct (CorrE_forced_shape G x (BExpr (EVar y1)) HCE) as
    [ [c0 [args0 [Hgx0 Hbeq]]]
    | [ [Hgx0 Hbeq]
      | [ [f0 [args0 [Hgx0 Hbeq]]]
        | [ [ya [yb [Hgx0 Hbeq]]]
          | [ [z0 [Hgx0 Hbeq]]
            | [ [Hgx0 Hbeq]
              | [ [y2 [Hgx0 Hbeq]]
                | [y2 [z0 [c0 [args0 [Hgx0 [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
    rewrite Hgx in Hgx0.
  - discriminate Hgx0.
  - discriminate Hgx0.
  - discriminate Hgx0.
  - discriminate Hgx0.
  - discriminate Hgx0.
  - discriminate Hgx0.
  - injection Hgx0 as Hgx0; subst y2. injection Hbeq as Hbeq. congruence.
  - discriminate Hbeq.
Qed.

Lemma force_var_N_left :
  forall P n G x y, ContractLocN G n x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  forall F, (forall z, In z F -> exists nz, ContractLocN G nz z y /\ n < nz) ->
  exists Gam', NEval_left P F Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G Gam'.
Proof.
  intros P.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros G x y Hcln c args Hy Gam HGam2 F Hdisj.
  assert (HxF : ~ In x F).
  { intro Hin. destruct (Hdisj x Hin) as [nz [Hclnz Hgt]].
    destruct (ContractLocN_functional G n x y Hcln nz y Hclnz) as [Heqn _].
    lia. }
  destruct n as [| n0].
  - assert (Hyx : y = x) by (eapply ContractLocN_zero; eauto). subst y.
    assert (Hb := Gam_from_con G x c args Hy Gam (proj1 HGam2)).
    exists Gam. split.
    + apply NL_VarCons. exact Hb.
    + exact HGam2.
  - destruct (ContractLocN_succ G n0 x y Hcln) as [y0 [Hxy0 Hcln0]].
    assert (HGamx := proj1 HGam2 x).
    assert (HGx : G x <> None) by congruence.
    destruct (G x) eqn:GX; [clear HGx | congruence].
    injection Hxy0 as Hxy0; subst g.
    destruct HGamx as [b [Hb HCE]].
    assert (Hprog := CorrE_con_progress_N G x b HCE (S n0) y c args Hcln Hy).
    destruct Hprog as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
    + subst b. exists Gam. split.
      * apply NL_VarCons. exact Hb.
      * exact HGam2.
    + subst b.
      assert (Hy1x : y1 <> x).
      { intro Heq; subst y1.
        destruct (ContractLocN_functional G m x y Hcln1 (S n0) y Hcln) as [Hmn _].
        lia. }
      (* y1 is exactly x's own direct graph forward target y0: G x = GFwd y0
         (Hxy0) already rules out CorrE_Free/CorrE_VarThunk matching HCE
         (both need G x direct, contradicting Hxy0), so HCE must be
         CorrE_FwdHere, forcing y1 = y0. *)
      assert (Hy1y0 : y1 = y0) by (eapply CorrE_evar_shape_for_fwd; [rewrite GX; reflexivity | exact HCE]).
      subst y1.
      assert (Hdisj' : forall z, In z (x :: F) -> exists nz, ContractLocN G nz z y /\ m < nz).
      { intros z Hin.
        destruct Hin as [Heq | Hin].
        - subst z. exists (S n0). split; [exact Hcln | exact Hm].
        - destruct (Hdisj z Hin) as [nz [Hclnz Hgt]].
          exists nz. split; [exact Hclnz | lia]. }
      destruct (IHn m Hm G y0 y Hcln1 c args Hy Gam HGam2 (x :: F) Hdisj') as [Gam1 [HNE HHC2]].
      assert (Hy0x : y0 <> x) by exact Hy1x.
      assert (Hgamy0 : Gam1 y0 = Some (BExpr (ECon c args)))
        by (eapply NEval_left_own_slot; exact HNE).
      exists (hupd Gam1 x (BExpr (ECon c args))).
      split.
      * eapply NL_VarExp.
        -- exact HxF.
        -- exact Hb.
        -- intros c' args' Heq; discriminate.
        -- intro Heq; injection Heq as Heq'; congruence.
        -- intro Heq; discriminate.
        -- exact HNE.
      * eapply HeapCorr2_update_achieved.
        -- exact HHC2.
        -- rewrite GX. reflexivity.
        -- exact Hy0x.
        -- exact (ContractLocN_to_ContractLoc G n0 y0 y Hcln0).
        -- exact Hy.
        -- exact Hgamy0.
Qed.

Lemma force_var_left :
  forall P G x y, ContractLoc G x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam', NEval_left P nil Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G Gam'.
Proof.
  intros P G x y H c args Hy Gam HGam.
  destruct (ContractLoc_to_N G x y H) as [n Hn].
  eapply force_var_N_left; eauto.
  intros z Hin; destruct Hin.
Qed.

(* ==================================================================== *)
(* Ports of curry.v's NEval_selfloop_result_persists / NEval_con_persists /  *)
(* NEval_alias_or_con_persists -- purely structural facts about NEval_left's  *)
(* OWN derivation shape (no HeapCorr involved at all), so these are exact      *)
(* mechanical ports: only the N_Or case changes shape (NL_Or drops the two-way *)
(* choice, nothing else differs). *)
(* ==================================================================== *)

Lemma NEval_left_selfloop_result_persists :
  forall P F G e G' z', NEval_left P F G e G' (BExpr (EVar z')) -> G' z' = Some (BExpr (EVar z')).
Proof.
  intros P F G e G' z' H.
  remember (BExpr (EVar z')) as target eqn:Ht.
  revert z' Ht.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HnF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v Hrec IH
    | F0 G0 z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z'0 c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros z' Ht; try discriminate Ht.
  - injection Ht as Ht; subst z. exact Hz.
  - injection Ht as Ht; subst z. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
  - specialize (IH z' Ht). subst v0.
    unfold hupd. destruct (Nat.eqb z' z) eqn:E.
    + reflexivity.
    + exact IH.
  - exact (IH z' Ht).
  - exact (IH z' Ht).
  - exact (IH z' Ht).
  - exact (IH2 z' Ht).
  - exact (IH2 z' Ht).
Qed.

Lemma NEval_left_con_persists :
  forall P F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  forall w c cargs, Gam w = Some (BExpr (ECon c cargs)) -> Gam' w = Some (BExpr (ECon c cargs)).
Proof.
  intros P F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HnF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros w c cargs Hw.
  - exact Hw.
  - exact Hw.
  - destruct (Nat.eq_dec w z) as [Heq | Hne].
    + subst w. rewrite Hz in Hw. discriminate Hw.
    + unfold hupd. apply Nat.eqb_neq in Hne. rewrite Hne. exact Hw.
  - destruct (Nat.eq_dec w z) as [Heq | Hne].
    + subst w. rewrite Hz in Hw. injection Hw as Hw; subst e0. exfalso. exact (Hne1 c cargs eq_refl).
    + unfold hupd. apply Nat.eqb_neq in Hne. rewrite Hne. exact (IH w c cargs Hw).
  - exact Hw.
  - exact Hw.
  - exact (IH w c cargs Hw).
  - destruct (Nat.eq_dec w z) as [Heq | Hne].
    + subst w. rewrite HzFresh in Hw. discriminate Hw.
    + assert (Hw' : hupd G z (let_content z e0) w = Some (BExpr (ECon c cargs))).
      { unfold hupd. apply Nat.eqb_neq in Hne. rewrite Hne. exact Hw. }
      exact (IH w c cargs Hw').
  - exact (IH w c cargs Hw).
  - exact (IH2 w c cargs (IH1 w c cargs Hw)).
  - assert (Hw1 := IH1 w c cargs Hw).
    assert (Hwnotin : ~ In w ws).
    { intro Hin. specialize (Hfr w Hin). rewrite Hw1 in Hfr. discriminate Hfr. }
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hwz' : w <> z').
    { intro Heq; subst w. rewrite Hw1 in HG1z'. discriminate HG1z'. }
    assert (Hw2 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws
                    (map (fun w0 => BExpr (EVar w0)) ws) w = Some (BExpr (ECon c cargs))).
    { rewrite hupd_list_notin by exact Hwnotin.
      rewrite hupd_neq by exact Hwz'.
      exact Hw1. }
    exact (IH2 w c cargs Hw2).
Qed.

Lemma NEval_left_alias_or_con_persists :
  forall P x y c args, x <> y ->
  forall F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  (Gam x = Some (BExpr (EVar y)) \/ Gam x = Some (BExpr (ECon c args))) ->
  Gam y = Some (BExpr (ECon c args)) ->
  (Gam' x = Some (BExpr (EVar y)) \/ Gam' x = Some (BExpr (ECon c args))) /\
  Gam' y = Some (BExpr (ECon c args)).
Proof.
  intros P x y c args Hxy F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HnF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Hgx Hgy.
  - split; [exact Hgx | exact Hgy].
  - split; [exact Hgx | exact Hgy].
  - assert (Hxz : x <> z).
    { intro Heq; subst x. destruct Hgx as [Hgx' | Hgx']; rewrite Hz in Hgx'; discriminate Hgx'. }
    assert (Hyz : y <> z) by (intro Heq; subst y; rewrite Hz in Hgy; discriminate Hgy).
    split.
    + destruct Hgx as [Hgx' | Hgx']; [left | right]; rewrite hupd_neq by exact Hxz; assumption.
    + rewrite hupd_neq by exact Hyz. exact Hgy.
  - assert (Hyz : y <> z).
    { intro Heq; subst y. rewrite Hgy in Hz. injection Hz as Hz; subst e0. exact (Hne1 c args eq_refl). }
    destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z.
      assert (He0 : e0 = BExpr (EVar y)).
      { destruct Hgx as [Hgx' | Hgx'].
        - congruence.
        - rewrite Hgx' in Hz. injection Hz as Hz; subst e0. exfalso. exact (Hne1 c args eq_refl). }
      subst e0.
      assert (HG1 : G1 = G) by (inversion Hrec; subst; try congruence; reflexivity).
      assert (Hv0 : v0 = BExpr (ECon c args)) by (inversion Hrec; subst; try congruence).
      subst G1 v0.
      split.
      * right. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * rewrite hupd_neq by exact (not_eq_sym Hxy). exact Hgy.
    + assert (Hxz : x <> z) by (intro Heq; subst x; exact (Hnezx eq_refl)).
      destruct Hgx as [Hgx' | Hgx'].
      * destruct (IH (or_introl Hgx') Hgy) as [IHx IHy].
        split.
        -- destruct IHx as [IHx' | IHx']; [left | right]; rewrite hupd_neq by exact Hxz; assumption.
        -- rewrite hupd_neq by exact Hyz. exact IHy.
      * destruct (IH (or_intror Hgx') Hgy) as [IHx IHy].
        split.
        -- destruct IHx as [IHx' | IHx']; [left | right]; rewrite hupd_neq by exact Hxz; assumption.
        -- rewrite hupd_neq by exact Hyz. exact IHy.
  - split; [exact Hgx | exact Hgy].
  - split; [exact Hgx | exact Hgy].
  - exact (IH Hgx Hgy).
  - assert (Hxz : x <> z) by (intro Heq; subst x; destruct Hgx as [Hgx' | Hgx']; congruence).
    assert (Hyz : y <> z) by (intro Heq; subst y; congruence).
    assert (Hgx2 : hupd G z (let_content z e0) x = Some (BExpr (EVar y)) \/
                   hupd G z (let_content z e0) x = Some (BExpr (ECon c args))).
    { rewrite hupd_neq by exact Hxz. exact Hgx. }
    assert (Hgy2 : hupd G z (let_content z e0) y = Some (BExpr (ECon c args))).
    { rewrite hupd_neq by exact Hyz. exact Hgy. }
    exact (IH Hgx2 Hgy2).
  - exact (IH Hgx Hgy).
  - destruct (IH1 Hgx Hgy) as [IH1x IH1y]. exact (IH2 IH1x IH1y).
  - destruct (IH1 Hgx Hgy) as [IH1x IH1y].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. destruct IH1x as [IH1x' | IH1x']; rewrite HG1z' in IH1x'; injection IH1x' as IH1x'; congruence. }
    assert (Hyz' : y <> z').
    { intro Heq; subst y. rewrite HG1z' in IH1y. discriminate IH1y. }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin).
      destruct IH1x as [IH1x' | IH1x']; rewrite Hfr in IH1x'; discriminate IH1x'. }
    assert (Hynotin : ~ In y ws).
    { intro Hin. specialize (Hfr y Hin). rewrite Hfr in IH1y. discriminate IH1y. }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (EVar y)) \/
                   hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite hupd_neq by exact Hxz'. exact IH1x. }
    assert (Hgy3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hynotin. rewrite hupd_neq by exact Hyz'. exact IH1y. }
    exact (IH2 Hgx3 Hgy3).
Qed.

(* A derivation valid under a LARGER guard remains valid under any SUBSET
   of it: every NL_VarExp step's own "~ In z F" precondition only ever
   gets EASIER to satisfy as F shrinks. *)
Lemma NEval_left_guard_shrink :
  forall P F1 F2, (forall w, In w F2 -> In w F1) ->
  forall Gam e Gam' v, NEval_left P F1 Gam e Gam' v -> NEval_left P F2 Gam e Gam' v.
Proof.
  intros P F1 F2 Hsub Gam e Gam' v H.
  revert F2 Hsub.
  induction H as
    [ F0 G z c args Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c args
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros F2 Hsub.
  - apply NL_VarCons. exact Hz.
  - apply NL_VarSelf. exact Hz.
  - apply NL_VarFree. exact Hz.
  - eapply NL_VarExp.
    + intro Hin. apply HzF. apply Hsub. exact Hin.
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply IH. intros w [Heq | Hin]; [left; exact Heq | right; apply Hsub; exact Hin].
  - apply NL_ValFree.
  - apply NL_ValCon.
  - eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | apply IH; exact Hsub].
  - apply NL_Let; [exact HzFresh | apply IH; exact Hsub].
  - eapply NL_Or; apply IH; exact Hsub.
  - eapply NL_Select; [apply IH1; exact Hsub | exact HIn | exact Hlen | apply IH2; exact Hsub].
  - eapply NL_Guess; [apply IH1; exact Hsub | exact Hhd | exact Hlen | exact HND | exact Hfr | apply IH2; exact Hsub].
Qed.

Lemma NEval_left_F_perm :
  forall P F1 F2, (forall w, In w F1 <-> In w F2) ->
  forall Gam e Gam' v, NEval_left P F1 Gam e Gam' v -> NEval_left P F2 Gam e Gam' v.
Proof.
  intros P F1 F2 Hperm Gam e Gam' v H.
  revert F2 Hperm.
  induction H as
    [ F0 G z c args Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c args
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros F2 Hperm.
  - apply NL_VarCons. exact Hz.
  - apply NL_VarSelf. exact Hz.
  - apply NL_VarFree. exact Hz.
  - eapply NL_VarExp.
    + intro Hin. apply HzF. apply (Hperm z). exact Hin.
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply IH. intro w; simpl; split.
      * intros [Heq | Hin]; [left; exact Heq | right; apply (Hperm w); exact Hin].
      * intros [Heq | Hin]; [left; exact Heq | right; apply (Hperm w); exact Hin].
  - apply NL_ValFree.
  - apply NL_ValCon.
  - eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | apply IH; exact Hperm].
  - apply NL_Let; [exact HzFresh | apply IH; exact Hperm].
  - eapply NL_Or; apply IH; exact Hperm.
  - eapply NL_Select; [apply IH1; exact Hperm | exact HIn | exact Hlen | apply IH2; exact Hperm].
  - eapply NL_Guess; [apply IH1; exact Hperm | exact Hhd | exact Hlen | exact HND | exact Hfr | apply IH2; exact Hperm].
Qed.

Lemma NEval_left_alias_frozen :
  forall P x y, x <> y ->
  forall e0y, (forall c args, e0y <> BExpr (ECon c args)) -> e0y <> BExpr (EVar y) -> e0y <> BExpr EFree ->
  forall F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  In y F ->
  Gam x = Some (BExpr (EVar y)) ->
  Gam y = Some e0y ->
  Gam' x = Some (BExpr (EVar y)) /\ Gam' y = Some e0y.
Proof.
  intros P x y Hxy e0y Hey1 Hey2 Hey3 F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e1 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e1 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HyF Hgx Hgy.
  - assert (Hzx : z <> x) by (intro Heq; subst z; rewrite Hz in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey1 c0 args0 eq_refl)).
    split; assumption.
  - assert (Hzx : z <> x).
    { intro Heq; subst z; rewrite Hz in Hgx; injection Hgx as Hgx. exact (Hxy Hgx). }
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey2 eq_refl)).
    split; assumption.
  - assert (Hzx : z <> x) by (intro Heq; subst z; rewrite Hz in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey3 eq_refl)).
    split.
    + rewrite (hupd_neq G z (BExpr (EVar z)) x (not_eq_sym Hzx)). exact Hgx.
    + rewrite (hupd_neq G z (BExpr (EVar z)) y (not_eq_sym Hzy)). exact Hgy.
  - destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z.
      assert (He1 : e1 = BExpr (EVar y)) by (rewrite Hz in Hgx; congruence).
      subst e1.
      assert (HyF' : In y (x :: F0)) by (right; exact HyF).
      exfalso.
      destruct (NEval_left_evar_shape P (x :: F0) G y G1 v0 Hrec) as
        [ [Hcase1 [_ [c' [args' Heqv0]]]]
        | [ [Hcase2 [_ Heqv0]]
          | [ [Hcase3 [_ Heqv0]]
            | [HnotIn _] ] ] ].
      * rewrite Hgy in Hcase1. injection Hcase1 as Hcase1. subst v0.
        exact (Hey1 c' args' Heqv0).
      * rewrite Hgy in Hcase2. injection Hcase2 as Hcase2. subst e0y.
        exact (Hey2 eq_refl).
      * rewrite Hgy in Hcase3. injection Hcase3 as Hcase3. subst e0y.
        exact (Hey3 eq_refl).
      * exact (HnotIn HyF').
    + destruct (Nat.eq_dec z y) as [Heqzy | Hnezy].
      * subst z. exfalso. exact (HzF HyF).
      * assert (HyF' : In y (z :: F0)) by (right; exact HyF).
        destruct (IH HyF' Hgx Hgy) as [IHx IHy].
        split.
        -- rewrite (hupd_neq G1 z v0 x (not_eq_sym Hnezx)). exact IHx.
        -- rewrite (hupd_neq G1 z v0 y (not_eq_sym Hnezy)). exact IHy.
  - split; assumption.
  - split; assumption.
  - exact (IH HyF Hgx Hgy).
  - assert (Hzx : z <> x) by (intro Heq; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite HzFresh in Hgy; discriminate Hgy).
    assert (Hgx2 : hupd G z (let_content z e1) x = Some (BExpr (EVar y)))
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    assert (Hgy2 : hupd G z (let_content z e1) y = Some e0y)
      by (rewrite (hupd_neq G z (let_content z e1) y (not_eq_sym Hzy)); exact Hgy).
    exact (IH HyF Hgx2 Hgy2).
  - exact (IH HyF Hgx Hgy).
  - destruct (IH1 HyF Hgx Hgy) as [IH1x IH1y].
    exact (IH2 HyF IH1x IH1y).
  - destruct (IH1 HyF Hgx Hgy) as [IH1x IH1y].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. rewrite HG1z' in IH1x. injection IH1x as IH1x. exact (Hxy IH1x). }
    assert (Hyz' : y <> z').
    { intro Heq; subst y. rewrite HG1z' in IH1y. injection IH1y as IH1y. exact (Hey2 (eq_sym IH1y)). }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). rewrite Hfr in IH1x. discriminate IH1x. }
    assert (Hynotin : ~ In y ws).
    { intro Hin. specialize (Hfr y Hin). rewrite Hfr in IH1y. discriminate IH1y. }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (EVar y))).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact IH1x. }
    assert (Hgy3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                     = Some e0y).
    { rewrite hupd_list_notin by exact Hynotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) y Hyz'). exact IH1y. }
    exact (IH2 HyF Hgx3 Hgy3).
Qed.

Lemma NEval_left_alias_weaken :
  forall P x y, x <> y ->
  forall e0y, (forall c args, e0y <> BExpr (ECon c args)) -> e0y <> BExpr (EVar y) -> e0y <> BExpr EFree ->
  forall F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  In y F ->
  Gam x = Some (BExpr (EVar y)) ->
  Gam y = Some e0y ->
  NEval_left P (x :: F) Gam e Gam' v.
Proof.
  intros P x y Hxy e0y Hey1 Hey2 Hey3 F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e1 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e1 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HyF Hgx Hgy.
  - apply NL_VarCons. exact Hz.
  - apply NL_VarSelf. exact Hz.
  - apply NL_VarFree. exact Hz.
  - destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z.
      assert (He1 : e1 = BExpr (EVar y)) by (rewrite Hz in Hgx; congruence).
      subst e1.
      assert (HyF' : In y (x :: F0)) by (right; exact HyF).
      exfalso.
      destruct (NEval_left_evar_shape P (x :: F0) G y G1 v0 Hrec) as
        [ [Hcase1 [_ [c' [args' Heqv0]]]]
        | [ [Hcase2 [_ Heqv0]]
          | [ [Hcase3 [_ Heqv0]]
            | [HnotIn _] ] ] ].
      * rewrite Hgy in Hcase1. injection Hcase1 as Hcase1. subst v0.
        exact (Hey1 c' args' Heqv0).
      * rewrite Hgy in Hcase2. injection Hcase2 as Hcase2. subst e0y.
        exact (Hey2 eq_refl).
      * rewrite Hgy in Hcase3. injection Hcase3 as Hcase3. subst e0y.
        exact (Hey3 eq_refl).
      * exact (HnotIn HyF').
    + destruct (Nat.eq_dec z y) as [Heqzy | Hnezy].
      * subst z. exfalso. exact (HzF HyF).
      * assert (HyF' : In y (z :: F0)) by (right; exact HyF).
        assert (HzxF : ~ In z (x :: F0)).
        { intro Hin. destruct Hin as [Heq | Hin]; [exact (Hnezx (eq_sym Heq)) | exact (HzF Hin)]. }
        eapply NL_VarExp.
        -- exact HzxF.
        -- exact Hz.
        -- exact Hne1.
        -- exact Hne2.
        -- exact Hne3.
        -- apply (NEval_left_F_perm P (x :: z :: F0) (z :: x :: F0)).
           ++ intro w; simpl; tauto.
           ++ exact (IH HyF' Hgx Hgy).
  - apply NL_ValFree.
  - apply NL_ValCon.
  - eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | ].
    exact (IH HyF Hgx Hgy).
  - assert (Hzx : z <> x) by (intro Heq; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite HzFresh in Hgy; discriminate Hgy).
    assert (Hgx2 : hupd G z (let_content z e1) x = Some (BExpr (EVar y)))
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    assert (Hgy2 : hupd G z (let_content z e1) y = Some e0y)
      by (rewrite (hupd_neq G z (let_content z e1) y (not_eq_sym Hzy)); exact Hgy).
    apply NL_Let; [exact HzFresh | exact (IH HyF Hgx2 Hgy2)].
  - eapply NL_Or; exact (IH HyF Hgx Hgy).
  - destruct (NEval_left_alias_frozen P x y Hxy e0y Hey1 Hey2 Hey3 F0 G (BExpr (EVar z)) G1 (BExpr (ECon c0 zs)) Hrec1 HyF Hgx Hgy)
      as [IH1x IH1y].
    eapply NL_Select; [exact (IH1 HyF Hgx Hgy) | exact HIn | exact Hlen | exact (IH2 HyF IH1x IH1y)].
  - destruct (NEval_left_alias_frozen P x y Hxy e0y Hey1 Hey2 Hey3 F0 G (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 HyF Hgx Hgy)
      as [IH1x IH1y].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. rewrite HG1z' in IH1x. injection IH1x as IH1x. exact (Hxy IH1x). }
    assert (Hyz' : y <> z').
    { intro Heq; subst y. rewrite HG1z' in IH1y. injection IH1y as IH1y. exact (Hey2 (eq_sym IH1y)). }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). rewrite Hfr in IH1x. discriminate IH1x. }
    assert (Hynotin : ~ In y ws).
    { intro Hin. specialize (Hfr y Hin). rewrite Hfr in IH1y. discriminate IH1y. }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (EVar y))).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact IH1x. }
    assert (Hgy3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                     = Some e0y).
    { rewrite hupd_list_notin by exact Hynotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) y Hyz'). exact IH1y. }
    eapply NL_Guess; [exact (IH1 HyF Hgx Hgy) | exact Hhd | exact Hlen | exact HND | exact Hfr | exact (IH2 HyF Hgx3 Hgy3)].
Qed.

Lemma NEval_left_alias_weaken_force_y :
  forall P x y, x <> y ->
  forall Gam Gmid v, NEval_left P nil Gam (BExpr (EVar y)) Gmid v ->
  Gam x = Some (BExpr (EVar y)) ->
  NEval_left P (x :: nil) Gam (BExpr (EVar y)) Gmid v.
Proof.
  intros P x y Hxy Gam Gmid v H Hgx.
  destruct (NEval_left_evar_shape P nil Gam y Gmid v H) as
    [ [Hcase1 [HeqG [c [args Heqv]]]]
    | [ [Hcase2 [HeqG Heqv]]
      | [ [Hcase3 [HeqG Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqG]]]]]]]] ] ] ].
  - subst Gmid v. apply NL_VarCons. exact Hcase1.
  - subst Gmid v. apply NL_VarSelf. exact Hcase2.
  - subst Gmid v. apply NL_VarFree. exact Hcase3.
  - subst Gmid.
    eapply NL_VarExp.
    + intro Hin. destruct Hin as [Heq | Hin]; [exact (Hxy Heq) | destruct Hin].
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply (NEval_left_F_perm P (x :: y :: nil) (y :: x :: nil)).
      * intro w; simpl; tauto.
      * apply (NEval_left_alias_weaken P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil) Gam e0 G1 v Hrec).
        -- left; reflexivity.
        -- exact Hgx.
        -- exact Hz.
Qed.

(* HeapCorr2 only ever inspects Gam through pointwise lookups (in BOTH its   *)
(* HeapCorr and ChainConsistent halves), so it transfers freely across        *)
(* pointwise-equal heaps -- needed because NEval_left_shortcut_alias's own      *)
(* conclusion only pins Gam1' down UP TO pointwise equality, not literal =.     *)
(* Generalization of NEval_left_alias_weaken_force_y from a nil starting
   guard to an ARBITRARY starting guard F0 disjoint from {x, y} -- needed so
   the fwd/choice-transfer machinery can be reused while forcing a function
   body under a guard already carrying x (added by NL_VarExp when forcing the
   call itself), not just from a completely empty guard. *)
Lemma NEval_left_alias_weaken_force_y_F :
  forall P x y F0, x <> y -> ~ In x F0 -> ~ In y F0 ->
  forall Gam Gmid v, NEval_left P F0 Gam (BExpr (EVar y)) Gmid v ->
  Gam x = Some (BExpr (EVar y)) ->
  NEval_left P (x :: F0) Gam (BExpr (EVar y)) Gmid v.
Proof.
  intros P x y F0 Hxy HxF0 HyF0 Gam Gmid v H Hgx.
  destruct (NEval_left_evar_shape P F0 Gam y Gmid v H) as
    [ [Hcase1 [HeqG [c [args Heqv]]]]
    | [ [Hcase2 [HeqG Heqv]]
      | [ [Hcase3 [HeqG Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqG]]]]]]]] ] ] ].
  - subst Gmid v. apply NL_VarCons. exact Hcase1.
  - subst Gmid v. apply NL_VarSelf. exact Hcase2.
  - subst Gmid v. apply NL_VarFree. exact Hcase3.
  - subst Gmid.
    eapply NL_VarExp.
    + intro Hin. destruct Hin as [Heq | Hin]; [exact (Hxy Heq) | exact (HyF0 Hin)].
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply (NEval_left_F_perm P (x :: y :: F0) (y :: x :: F0)).
      * intro w; simpl; tauto.
      * apply (NEval_left_alias_weaken P x y Hxy e0 Hne1 Hne2 Hne3 (y :: F0) Gam e0 G1 v Hrec).
        -- left; reflexivity.
        -- exact Hgx.
        -- exact Hz.
Qed.

(* x's alias to y is untouched by FORCING y itself (not just by evaluating
   some unrelated e while y sits guarded) -- needed for the Nat-Guess case:
   after chasing x's alias into y and reaching a free-variable self-loop x',
   we need to know x' <> x, which follows from x's own slot staying `EVar y`
   throughout (so x' = x would force `EVar y = EVar x`, i.e. y = x). *)
Lemma NEval_left_alias_persists_through_force :
  forall P x y, x <> y ->
  forall Gam Gmid v, NEval_left P nil Gam (BExpr (EVar y)) Gmid v ->
  Gam x = Some (BExpr (EVar y)) ->
  Gmid x = Some (BExpr (EVar y)).
Proof.
  intros P x y Hxy Gam Gmid v H Hgx.
  destruct (NEval_left_evar_shape P nil Gam y Gmid v H) as
    [ [Hcase1 [HeqG _]]
    | [ [Hcase2 [HeqG _]]
      | [ [Hcase3 [HeqG _]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqG]]]]]]]] ] ] ].
  - subst Gmid. exact Hgx.
  - subst Gmid. exact Hgx.
  - subst Gmid. rewrite (hupd_neq Gam y (BExpr (EVar y)) x Hxy). exact Hgx.
  - subst Gmid.
    assert (HG1x : G1 x = Some (BExpr (EVar y)))
      by (exact (proj1 (NEval_left_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil)
                   Gam e0 G1 v Hrec (or_introl eq_refl) Hgx Hz))).
    rewrite (hupd_neq G1 y v x Hxy). exact HG1x.
Qed.

Lemma HeapCorr2_pointwise :
  forall G Gam Gam', HeapCorr2 G Gam -> (forall w, Gam' w = Gam w) -> HeapCorr2 G Gam'.
Proof.
  intros G Gam Gam' [HGC HCC] Heq.
  split.
  - intro x. rewrite Heq. exact (HGC x).
  - intros p q Hpq c args Hpc. rewrite Heq. rewrite Heq in Hpc. exact (HCC p q Hpq c args Hpc).
Qed.

Lemma NEval_left_shortcut_alias :
  forall P x y c args, x <> y ->
  forall F Gam e Gam1 v, NEval_left P F Gam e Gam1 v ->
  (Gam x = Some (BExpr (EVar y)) \/ Gam x = Some (BExpr (ECon c args))) ->
  Gam y = Some (BExpr (ECon c args)) ->
  exists Gam1', NEval_left P F (hupd Gam x (BExpr (ECon c args))) e Gam1' v /\
  (forall w, Gam1' w = hupd Gam1 x (BExpr (ECon c args)) w).
Proof.
  intros P x y c args Hxy F Gam e Gam1 v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e0 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Hgx Hgy.
  - destruct (Nat.eq_dec z x) as [Heq | Hne].
    + subst z.
      assert (Heqcc : BExpr (ECon c0 args0) = BExpr (ECon c args)).
      { destruct Hgx as [Hgx' | Hgx']; rewrite Hz in Hgx'; [discriminate | congruence]. }
      exists (hupd G x (BExpr (ECon c args))). split.
      * apply NL_VarCons. unfold hupd; rewrite Nat.eqb_refl. congruence.
      * intro w; reflexivity.
    + exists (hupd G x (BExpr (ECon c args))). split.
      * apply NL_VarCons. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
      * intro w; reflexivity.
  - destruct (Nat.eq_dec z x) as [Heq | Hne].
    + subst z. destruct Hgx as [Hgx' | Hgx'].
      * rewrite Hz in Hgx'. injection Hgx' as Hgx'. exfalso. apply Hxy. congruence.
      * rewrite Hz in Hgx'. discriminate.
    + exists (hupd G x (BExpr (ECon c args))). split.
      * apply NL_VarSelf. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
      * intro w; reflexivity.
  - assert (Hne : z <> x).
    { intro Heq; subst z. destruct Hgx as [Hgx' | Hgx']; rewrite Hz in Hgx'; discriminate. }
    exists (hupd (hupd G x (BExpr (ECon c args))) z (BExpr (EVar z))). split.
    + apply NL_VarFree. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
    + intro w. exact (hupd_comm G x (BExpr (ECon c args)) z (BExpr (EVar z)) (not_eq_sym Hne) w).
  - destruct (Nat.eq_dec z x) as [Heq | Hne].
    + subst z.
      assert (He0 : e0 = BExpr (EVar y)).
      { destruct Hgx as [Hgx' | Hgx'].
        - congruence.
        - rewrite Hgx' in Hz. injection Hz as Hz; subst e0. exfalso. exact (Hne1 c args eq_refl). }
      subst e0.
      assert (HG1eq : G1 = G) by (inversion Hrec; subst; try congruence; reflexivity).
      assert (Hv0 : v0 = BExpr (ECon c args)) by (inversion Hrec; subst; try congruence).
      subst G1 v0.
      exists (hupd G x (BExpr (ECon c args))). split.
      * apply NL_VarCons. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * intro w; unfold hupd; destruct (Nat.eqb w x); reflexivity.
    + assert (Hyz : y <> z).
      { intro Heq'; subst y. rewrite Hgy in Hz. injection Hz as Hz; subst e0. exact (Hne1 c args eq_refl). }
      destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
      exists (hupd G1' z v0). split.
      * eapply NL_VarExp.
        -- exact HzF.
        -- rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
        -- exact Hne1.
        -- exact Hne2.
        -- exact Hne3.
        -- exact HNE'.
      * assert (Hcong : forall w, hupd G1' z v0 w = hupd (hupd G1 x (BExpr (ECon c args))) z v0 w).
        { intro w0; unfold hupd; rewrite (Heq' w0); reflexivity. }
        intro w. rewrite (Hcong w). exact (hupd_comm G1 x (BExpr (ECon c args)) z v0 (not_eq_sym Hne) w).
  - exists (hupd G x (BExpr (ECon c args))). split.
    + apply NL_ValFree.
    + intro w; reflexivity.
  - exists (hupd G x (BExpr (ECon c args))). split.
    + apply NL_ValCon.
    + intro w; reflexivity.
  - destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
    exists G1'. split.
    + eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE'].
      intros y0 Hy0.
      assert (Hne : s y0 <> x).
      { intro Heq. specialize (Hfresh y0 Hy0). rewrite Heq in Hfresh.
        destruct Hgx as [Hgx' | Hgx']; rewrite Hgx' in Hfresh; discriminate. }
      rewrite (hupd_neq G x (BExpr (ECon c args)) (s y0) Hne). exact (Hfresh y0 Hy0).
    + exact Heq'.
  - assert (Hzx : z <> x).
    { intro Heq; subst z. destruct Hgx as [Hgx' | Hgx']; rewrite HzFresh in Hgx'; discriminate. }
    assert (Hzy : z <> y).
    { intro Heq; subst z. rewrite HzFresh in Hgy; discriminate. }
    assert (Hgx2 : hupd G z (let_content z e0) x = Some (BExpr (EVar y)) \/
                   hupd G z (let_content z e0) x = Some (BExpr (ECon c args))).
    { destruct Hgx as [Hgx' | Hgx']; [left | right]; rewrite (hupd_neq G z (let_content z e0) x (not_eq_sym Hzx)); assumption. }
    assert (Hgy2 : hupd G z (let_content z e0) y = Some (BExpr (ECon c args))).
    { rewrite (hupd_neq G z (let_content z e0) y (not_eq_sym Hzy)); exact Hgy. }
    destruct (IH Hgx2 Hgy2) as [G1' [HNE' Heq']].
    assert (Hcong : forall w, hupd (hupd G x (BExpr (ECon c args))) z (let_content z e0) w
                             = hupd (hupd G z (let_content z e0)) x (BExpr (ECon c args)) w).
    { intro w; exact (hupd_comm G x (BExpr (ECon c args)) z (let_content z e0) (not_eq_sym Hzx) w). }
    destruct (NEval_left_pointwise_heap P F0 (hupd (hupd G z (let_content z e0)) x (BExpr (ECon c args))) k G1' v HNE'
                (hupd (hupd G x (BExpr (ECon c args))) z (let_content z e0)) Hcong)
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + apply NL_Let.
      * rewrite (hupd_neq G x (BExpr (ECon c args)) z Hzx). exact HzFresh.
      * exact HNE2''.
    + intro w. rewrite (Heq2'' w). exact (Heq' w).
  - destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
    exists G1'. split.
    + eapply NL_Or; exact HNE'.
    + exact Heq'.
  - destruct (IH1 Hgx Hgy) as [G1' [HNE1' Heq1']].
    destruct (NEval_left_alias_or_con_persists P x y c args Hxy F0 G (BExpr (EVar z)) G1 (BExpr (ECon c0 zs)) Hrec1 Hgx Hgy) as [Hgx2 Hgy2].
    destruct (IH2 Hgx2 Hgy2) as [G2' [HNE2' Heq2']].
    destruct (NEval_left_pointwise_heap P F0 (hupd G1 x (BExpr (ECon c args))) (rename_b (zipsubst ys zs) body) G2' v HNE2' G1' Heq1')
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + eapply NL_Select; [exact HNE1' | exact HIn | exact Hlen | exact HNE2''].
    + intro w. rewrite (Heq2'' w). exact (Heq2' w).
  - destruct (IH1 Hgx Hgy) as [G1' [HNE1' Heq1']].
    destruct (NEval_left_alias_or_con_persists P x y c args Hxy F0 G (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 Hgx Hgy) as [Hgx2 Hgy2].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. destruct Hgx2 as [Hgx2' | Hgx2']; rewrite HG1z' in Hgx2'; injection Hgx2' as Hgx2'; congruence. }
    assert (Hyz' : y <> z').
    { intro Heq; subst y. rewrite HG1z' in Hgy2. discriminate Hgy2. }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). destruct Hgx2 as [Hgx2' | Hgx2']; rewrite Hfr in Hgx2'; discriminate. }
    assert (Hynotin : ~ In y ws).
    { intro Hin. specialize (Hfr y Hin). rewrite Hfr in Hgy2. discriminate Hgy2. }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (EVar y)) \/
                   hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact Hgx2. }
    assert (Hgy3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hynotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) y Hyz'). exact Hgy2. }
    destruct (IH2 Hgx3 Hgy3) as [G2' [HNE2' Heq2']].
    assert (Hcong1 : forall w, hupd G1' z' (BExpr (ECon c1 ws)) w
                              = hupd (hupd G1 x (BExpr (ECon c args))) z' (BExpr (ECon c1 ws)) w).
    { intro w0; unfold hupd; rewrite (Heq1' w0); reflexivity. }
    assert (Hcong2 : forall w, hupd (hupd G1 x (BExpr (ECon c args))) z' (BExpr (ECon c1 ws)) w
                              = hupd (hupd G1 z' (BExpr (ECon c1 ws))) x (BExpr (ECon c args)) w).
    { intro w0; exact (hupd_comm G1 x (BExpr (ECon c args)) z' (BExpr (ECon c1 ws)) Hxz' w0). }
    assert (Hcong3 : forall w, hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
                              = hupd_list (hupd (hupd G1 z' (BExpr (ECon c1 ws))) x (BExpr (ECon c args))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
    { apply hupd_list_pointwise. intro w0. rewrite (Hcong1 w0). exact (Hcong2 w0). }
    assert (Hcong4 : forall w, hupd_list (hupd (hupd G1 z' (BExpr (ECon c1 ws))) x (BExpr (ECon c args))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
                              = hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)) w).
    { intro w0. exact (hupd_list_hupd_swap ws (map (fun w1 => BExpr (EVar w1)) ws) (hupd G1 z' (BExpr (ECon c1 ws))) x (BExpr (ECon c args)) Hxnotin w0). }
    assert (Hcong : forall w, hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
                             = hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)) w).
    { intro w0. rewrite (Hcong3 w0). exact (Hcong4 w0). }
    destruct (NEval_left_pointwise_heap P F0
                (hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)))
                (rename_b (zipsubst ys1 ws) body1) G2' v HNE2'
                (hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                Hcong)
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + eapply NL_Guess; [exact HNE1' | exact Hhd | exact Hlen | exact HND | | exact HNE2''].
      intros w Hw.
      destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      * subst w. exfalso. exact (Hxnotin Hw).
      * rewrite (Heq1' w).
        assert (Hw1 := Hfr w Hw).
        rewrite (hupd_neq G1 x (BExpr (ECon c args)) w Hnewx). exact Hw1.
    + intro w. rewrite (Heq2'' w). exact (Heq2' w).
Qed.

Lemma hupd_list_map_in :
  forall {A} (f : var -> A) (ws : list var) (h : heap A) w, In w ws -> hupd_list h ws (map f ws) w = Some (f w).
Proof.
  induction ws as [| w0 ws' IH]; intros h w Hin; simpl in Hin.
  - destruct Hin.
  - simpl. destruct Hin as [Heq | Hin].
    + subst w0. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eq_dec w w0) as [Heq | Hne].
      * subst w. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * unfold hupd. apply Nat.eqb_neq in Hne. rewrite Hne. exact (IH h w Hin).
Qed.

(* "Downgrade" companion to NEval_left_shortcut_alias: instead of PROMOTING   *)
(* an alias to an achieved constructor, take a derivation where some         *)
(* location x ALREADY directly holds a constructor and produce a matching    *)
(* derivation where x instead holds a lazy one-hop alias to a DIFFERENT      *)
(* location z that achieves the SAME constructor.  Sound because forcing     *)
(* either representation is a single, deterministic step reaching the        *)
(* identical value.  Unlike shortcut_alias's own output (which is exactly    *)
(* pointwise-equal, since a fully-achieved x never changes again), x's OWN    *)
(* slot here CAN change during the given derivation (NL_VarExp memoizes it   *)
(* back to the constructor if it's ever read) -- so the result is pointwise- *)
(* equal only AWAY from x, and AT x is either still the lazy alias or (if    *)
(* read) re-promoted to the constructor directly; both are fed back into     *)
(* shortcut_alias/pointwise_heap by whichever caller needs them next. *)
Lemma NEval_left_shortcut_alias_relax :
  forall P x z c args, x <> z ->
  forall F, ~ In x F ->
  forall Gam e Gam1 v, NEval_left P F Gam e Gam1 v ->
  Gam x = Some (BExpr (ECon c args)) ->
  Gam z = Some (BExpr (ECon c args)) ->
  exists Gam1', NEval_left P F (hupd Gam x (BExpr (EVar z))) e Gam1' v /\
  (forall w, w <> x -> Gam1' w = Gam1 w) /\
  (Gam1' x = Some (BExpr (EVar z)) \/ Gam1' x = Some (BExpr (ECon c args))).
Proof.
  intros P x z c args Hxz F HxF Gam e Gam1 v H.
  induction H as
    [ F0 G z0 c0 args0 Hz0
    | F0 G z0 Hz0
    | F0 G z0 Hz0
    | F0 G z0 e0 G1 v0 Hz0F Hz0 Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z0 e0 k v1 Hz0Fresh Hrec IH
    | F0 G x1 y1 G1 v1 Hrec IH
    | F0 G z0 c0 zs brs ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z0 G1 z' c1 ys1 body1 brs G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Hgx Hgz.
  - (* NL_VarCons *)
    destruct (Nat.eq_dec z0 x) as [Heq | Hne].
    + subst z0.
      assert (Heqcc : BExpr (ECon c0 args0) = BExpr (ECon c args)) by congruence.
      injection Heqcc as Heqc Heqargs; subst c0 args0.
      exists (hupd (hupd G x (BExpr (EVar z))) x (BExpr (ECon c args))). split.
      * eapply NL_VarExp.
        -- exact HxF.
        -- unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        -- intros c1' args1' Hcontra; discriminate Hcontra.
        -- intro Hcontra; injection Hcontra as Hcontra; exact (Hxz (eq_sym Hcontra)).
        -- intro Hcontra; discriminate Hcontra.
        -- apply NL_VarCons. rewrite (hupd_neq G x (BExpr (EVar z)) z (not_eq_sym Hxz)). exact Hgz.
      * split.
        -- intros w Hw. unfold hupd. destruct (Nat.eqb w x) eqn:E.
           ++ apply Nat.eqb_eq in E; congruence.
           ++ reflexivity.
        -- right. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
    + exists (hupd G x (BExpr (EVar z))). split.
      * apply NL_VarCons. rewrite (hupd_neq G x (BExpr (EVar z)) z0 Hne). exact Hz0.
      * split.
        -- intros w Hw. exact (hupd_neq G x (BExpr (EVar z)) w Hw).
        -- left. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
  - (* NL_VarSelf *)
    assert (Hne : z0 <> x) by (intro Heq; subst z0; rewrite Hgx in Hz0; discriminate Hz0).
    exists (hupd G x (BExpr (EVar z))). split.
    + apply NL_VarSelf. rewrite (hupd_neq G x (BExpr (EVar z)) z0 Hne). exact Hz0.
    + split; [intros w Hw; exact (hupd_neq G x (BExpr (EVar z)) w Hw) | left; unfold hupd; rewrite Nat.eqb_refl; reflexivity].
  - (* NL_VarFree *)
    assert (Hne : z0 <> x) by (intro Heq; subst z0; rewrite Hgx in Hz0; discriminate Hz0).
    exists (hupd (hupd G x (BExpr (EVar z))) z0 (BExpr (EVar z0))). split.
    + apply NL_VarFree. rewrite (hupd_neq G x (BExpr (EVar z)) z0 Hne). exact Hz0.
    + split.
      * intros w Hw.
        destruct (Nat.eq_dec w z0) as [Heqwz0 | Hnewz0].
        -- subst w. unfold hupd at 1; rewrite Nat.eqb_refl. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
        -- rewrite (hupd_neq (hupd G x (BExpr (EVar z))) z0 (BExpr (EVar z0)) w Hnewz0).
           rewrite (hupd_neq G z0 (BExpr (EVar z0)) w Hnewz0).
           rewrite (hupd_neq G x (BExpr (EVar z)) w Hw). reflexivity.
      * left. rewrite (hupd_neq (hupd G x (BExpr (EVar z))) z0 (BExpr (EVar z0)) x (not_eq_sym Hne)).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity.
  - (* NL_VarExp: forcing z0 via a further chase *)
    assert (Hne : z0 <> x).
    { intro Heq; subst z0. rewrite Hgx in Hz0. injection Hz0 as Hz0; subst e0. exact (Hne1 c args eq_refl). }
    assert (HxF0 : ~ In x (z0 :: F0)).
    { intro Hin. destruct Hin as [Heq | Hin]; [exact (Hne Heq) | exact (HxF Hin)]. }
    destruct (IH HxF0 Hgx Hgz) as [G1' [HNE' [Hptw Hdisj]]].
    exists (hupd G1' z0 v0). split.
    + eapply NL_VarExp.
      -- exact Hz0F.
      -- rewrite (hupd_neq G x (BExpr (EVar z)) z0 Hne). exact Hz0.
      -- exact Hne1.
      -- exact Hne2.
      -- exact Hne3.
      -- exact HNE'.
    + split.
      * intros w Hw. unfold hupd. destruct (Nat.eqb w z0) eqn:E; [reflexivity | exact (Hptw w Hw)].
      * rewrite (hupd_neq G1' z0 v0 x (not_eq_sym Hne)). exact Hdisj.
  - (* NL_ValFree *)
    exists (hupd G x (BExpr (EVar z))). split.
    + apply NL_ValFree.
    + split; [intros w Hw; exact (hupd_neq G x (BExpr (EVar z)) w Hw) | left; unfold hupd; rewrite Nat.eqb_refl; reflexivity].
  - (* NL_ValCon *)
    exists (hupd G x (BExpr (EVar z))). split.
    + apply NL_ValCon.
    + split; [intros w Hw; exact (hupd_neq G x (BExpr (EVar z)) w Hw) | left; unfold hupd; rewrite Nat.eqb_refl; reflexivity].
  - (* NL_Fun *)
    destruct (IH HxF Hgx Hgz) as [G1' [HNE' [Hptw Hdisj]]].
    exists G1'. split.
    + eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE'].
      intros y0 Hy0.
      assert (Hne : s y0 <> x).
      { intro Heq. specialize (Hfresh y0 Hy0). rewrite Heq in Hfresh. rewrite Hgx in Hfresh. discriminate Hfresh. }
      rewrite (hupd_neq G x (BExpr (EVar z)) (s y0) Hne). exact (Hfresh y0 Hy0).
    + split; [exact Hptw | exact Hdisj].
  - (* NL_Let *)
    assert (Hzx0 : z0 <> x) by (intro Heq; subst z0; rewrite Hz0Fresh in Hgx; discriminate Hgx).
    assert (Hzz0 : z0 <> z) by (intro Heq; subst z0; rewrite Hz0Fresh in Hgz; discriminate Hgz).
    assert (Hgx2 : hupd G z0 (let_content z0 e0) x = Some (BExpr (ECon c args))).
    { rewrite (hupd_neq G z0 (let_content z0 e0) x (not_eq_sym Hzx0)). exact Hgx. }
    assert (Hgz2 : hupd G z0 (let_content z0 e0) z = Some (BExpr (ECon c args))).
    { rewrite (hupd_neq G z0 (let_content z0 e0) z (not_eq_sym Hzz0)). exact Hgz. }
    destruct (IH HxF Hgx2 Hgz2) as [G1' [HNE' [Hptw Hdisj]]].
    assert (Hcong : forall w, hupd (hupd G x (BExpr (EVar z))) z0 (let_content z0 e0) w
                             = hupd (hupd G z0 (let_content z0 e0)) x (BExpr (EVar z)) w).
    { intro w; exact (hupd_comm G x (BExpr (EVar z)) z0 (let_content z0 e0) (not_eq_sym Hzx0) w). }
    destruct (NEval_left_pointwise_heap P F0 (hupd (hupd G z0 (let_content z0 e0)) x (BExpr (EVar z))) k G1' v1 HNE'
                (hupd (hupd G x (BExpr (EVar z))) z0 (let_content z0 e0))
                Hcong)
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + apply NL_Let.
      * rewrite (hupd_neq G x (BExpr (EVar z)) z0 Hzx0). exact Hz0Fresh.
      * exact HNE2''.
    + split.
      * intros w Hw. rewrite (Heq2'' w). exact (Hptw w Hw).
      * rewrite (Heq2'' x). exact Hdisj.
  - (* NL_Or *)
    destruct (IH HxF Hgx Hgz) as [G1' [HNE' [Hptw Hdisj]]].
    exists G1'. split; [eapply NL_Or; exact HNE' | split; [exact Hptw | exact Hdisj]].
  - (* NL_Select *)
    destruct (IH1 HxF Hgx Hgz) as [G1' [HNE1' [Hptw1 Hdisj1]]].
    assert (Hgx1 : G1 x = Some (BExpr (ECon c args)))
      by exact (NEval_left_con_persists P F0 G (BExpr (EVar z0)) G1 (BExpr (ECon c0 zs)) Hrec1 x c args Hgx).
    assert (Hgz1 : G1 z = Some (BExpr (ECon c args)))
      by exact (NEval_left_con_persists P F0 G (BExpr (EVar z0)) G1 (BExpr (ECon c0 zs)) Hrec1 z c args Hgz).
    destruct (IH2 HxF Hgx1 Hgz1) as [G2' [HNE2' [Hptw2 Hdisj2]]].
    destruct Hdisj1 as [Hd1 | Hd1].
    + assert (Hptw1' : forall w, G1' w = hupd G1 x (BExpr (EVar z)) w).
      { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        - subst w. rewrite Hd1. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        - rewrite (Hptw1 w Hnewx). rewrite (hupd_neq G1 x (BExpr (EVar z)) w Hnewx). reflexivity. }
      destruct (NEval_left_pointwise_heap P F0 (hupd G1 x (BExpr (EVar z))) (rename_b (zipsubst ys zs) body) G2' v1 HNE2' G1' Hptw1')
        as [G2'' [HNE2'' Heq2'']].
      exists G2''. split.
      * eapply NL_Select; [exact HNE1' | exact HIn | exact Hlen | exact HNE2''].
      * split.
        -- intros w Hw. rewrite (Heq2'' w). exact (Hptw2 w Hw).
        -- rewrite (Heq2'' x). exact Hdisj2.
    + assert (HcombW : forall w, hupd (hupd G1 x (BExpr (EVar z))) x (BExpr (ECon c args)) w = G1' w).
      { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        - subst w. unfold hupd at 1; rewrite Nat.eqb_refl. exact (eq_sym Hd1).
        - rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) x (BExpr (ECon c args)) w Hnewx).
          rewrite (hupd_neq G1 x (BExpr (EVar z)) w Hnewx).
          exact (eq_sym (Hptw1 w Hnewx)). }
      assert (Hxeq : hupd G1 x (BExpr (EVar z)) x = Some (BExpr (EVar z)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hgz1' : hupd G1 x (BExpr (EVar z)) z = Some (BExpr (ECon c args)))
        by (rewrite (hupd_neq G1 x (BExpr (EVar z)) z (not_eq_sym Hxz)); exact Hgz1).
      destruct (NEval_left_shortcut_alias P x z c args Hxz F0 (hupd G1 x (BExpr (EVar z)))
                  (rename_b (zipsubst ys zs) body) G2' v1 HNE2'
                  (or_introl Hxeq) Hgz1') as [G2a [HNE2a Heq2a]].
      destruct (NEval_left_pointwise_heap P F0 (hupd (hupd G1 x (BExpr (EVar z))) x (BExpr (ECon c args)))
                  (rename_b (zipsubst ys zs) body) G2a v1 HNE2a G1' (fun w => eq_sym (HcombW w)))
        as [G2'' [HNE2'' Heq2'']].
      exists G2''. split.
      * eapply NL_Select; [exact HNE1' | exact HIn | exact Hlen | exact HNE2''].
      * split.
        -- intros w Hw. rewrite (Heq2'' w). rewrite (Heq2a w).
           rewrite (hupd_neq G2' x (BExpr (ECon c args)) w Hw). exact (Hptw2 w Hw).
        -- rewrite (Heq2'' x). rewrite (Heq2a x). right. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
  - (* NL_Guess *)
    destruct (IH1 HxF Hgx Hgz) as [G1' [HNE1' [Hptw1 Hdisj1]]].
    assert (Hgx1 : G1 x = Some (BExpr (ECon c args)))
      by exact (NEval_left_con_persists P F0 G (BExpr (EVar z0)) G1 (BExpr (EVar z')) Hrec1 x c args Hgx).
    assert (Hgz1a : G1 z = Some (BExpr (ECon c args)))
      by exact (NEval_left_con_persists P F0 G (BExpr (EVar z0)) G1 (BExpr (EVar z')) Hrec1 z c args Hgz).
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z0)) G1 z' Hrec1).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. rewrite HG1z' in Hgx1. discriminate Hgx1. }
    assert (Hzz' : z <> z').
    { intro Heq; subst z. rewrite HG1z' in Hgz1a. discriminate Hgz1a. }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). rewrite Hfr in Hgx1. discriminate Hgx1. }
    assert (Hznotin : ~ In z ws).
    { intro Hin. specialize (Hfr z Hin). rewrite Hfr in Hgz1a. discriminate Hgz1a. }
    assert (Hgx2 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact Hgx1. }
    assert (Hgz2 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) z
                     = Some (BExpr (ECon c args))).
    { rewrite hupd_list_notin by exact Hznotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) z Hzz'). exact Hgz1a. }
    destruct (IH2 HxF Hgx2 Hgz2) as [G2' [HNE2' [Hptw2 Hdisj2]]].
    destruct Hdisj1 as [Hd1 | Hd1].
    + assert (Hptw1' : forall w, G1' w = hupd G1 x (BExpr (EVar z)) w).
      { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        - subst w. rewrite Hd1. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        - rewrite (Hptw1 w Hnewx). rewrite (hupd_neq G1 x (BExpr (EVar z)) w Hnewx). reflexivity. }
      assert (Hcong : forall w,
          hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
        = hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w).
      { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
        - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
          assert (Hwx : w <> x) by (intro Heq; subst w; exact (Hxnotin Hin)).
          rewrite (hupd_neq (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w Hwx).
          rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
        - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          + subst w.
            assert (HR : hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) x = Some (BExpr (EVar z)))
              by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
            rewrite HR.
            rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) x Hxz'). exact Hd1.
          + rewrite (hupd_neq (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w Hnewx).
            rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
            destruct (Nat.eq_dec w z') as [Heqwz' | Hnewz'].
            * subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
            * rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) w Hnewz').
              rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) w Hnewz').
              exact (Hptw1 w Hnewx). }
      destruct (NEval_left_pointwise_heap P F0
                  (hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)))
                  (rename_b (zipsubst ys1 ws) body1) G2' v1 HNE2'
                  (hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  Hcong)
        as [G2'' [HNE2'' Heq2'']].
      exists G2''. split.
      * eapply NL_Guess; [exact HNE1' | exact Hhd | exact Hlen | exact HND | | exact HNE2''].
        intros w Hw.
        destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        -- subst w. exfalso. exact (Hxnotin Hw).
        -- rewrite (Hptw1 w Hnewx). exact (Hfr w Hw).
      * split.
        -- intros w Hw. rewrite (Heq2'' w). exact (Hptw2 w Hw).
        -- rewrite (Heq2'' x). exact Hdisj2.
    + assert (Hbasehit : hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) x
                        = Some (BExpr (EVar z))).
      { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotin).
        rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws)) x Hxz').
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      assert (Hbasez : hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) z
                      = Some (BExpr (ECon c args))).
      { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ z Hznotin).
        rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws)) z Hzz').
        rewrite (hupd_neq G1 x (BExpr (EVar z)) z (not_eq_sym Hxz)).
        exact Hgz1a. }
      assert (HcongIn : forall w,
          hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
        = hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w).
      { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
        - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
          assert (Hwx : w <> x) by (intro Heq; subst w; exact (Hxnotin Hin)).
          rewrite (hupd_neq (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w Hwx).
          rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
        - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          + subst w.
            assert (HR : hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) x
                       = Some (BExpr (EVar z)))
              by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
            rewrite HR.
            rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws)) x Hxz').
            unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          + rewrite (hupd_neq (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)) w Hnewx).
            rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
            destruct (Nat.eq_dec w z') as [Heqwz' | Hnewz'].
            * subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
            * rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws)) w Hnewz').
              rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) w Hnewz').
              exact (hupd_neq G1 x (BExpr (EVar z)) w Hnewx). }
      destruct (NEval_left_pointwise_heap P F0
                  (hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (EVar z)))
                  (rename_b (zipsubst ys1 ws) body1) G2' v1 HNE2'
                  (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  HcongIn)
        as [G2p [HNE2p Heq2p]].
      destruct (NEval_left_shortcut_alias P x z c args Hxz F0
                  (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  (rename_b (zipsubst ys1 ws) body1) G2p v1 HNE2p
                  (or_introl Hbasehit) Hbasez) as [G2a [HNE2a Heq2a]].
      assert (HcombW : forall w,
          hupd (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)) w
        = hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
      { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        - subst w.
          assert (HR : hupd (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)) x
                     = Some (BExpr (ECon c args)))
            by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
          rewrite HR.
          rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotin).
          rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) x Hxz'). exact (eq_sym Hd1).
        - rewrite (hupd_neq (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)) w Hnewx).
          destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
          + rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
            rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
          + rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
            rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
            destruct (Nat.eq_dec w z') as [Heqwz' | Hnewz'].
            * subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
            * rewrite (hupd_neq (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws)) w Hnewz').
              rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) w Hnewz').
              rewrite (hupd_neq G1 x (BExpr (EVar z)) w Hnewx).
              exact (eq_sym (Hptw1 w Hnewx)). }
      destruct (NEval_left_pointwise_heap P F0
                  (hupd (hupd_list (hupd (hupd G1 x (BExpr (EVar z))) z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)))
                  (rename_b (zipsubst ys1 ws) body1) G2a v1 HNE2a
                  (hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  (fun w => eq_sym (HcombW w)))
        as [G2'' [HNE2'' Heq2'']].
      exists G2''. split.
      * eapply NL_Guess; [exact HNE1' | exact Hhd | exact Hlen | exact HND | | exact HNE2''].
        intros w Hw.
        destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        -- subst w. exfalso. exact (Hxnotin Hw).
        -- rewrite (Hptw1 w Hnewx). exact (Hfr w Hw).
      * split.
        -- intros w Hw. rewrite (Heq2'' w). rewrite (Heq2a w).
           rewrite (hupd_neq G2p x (BExpr (ECon c args)) w Hw). rewrite (Heq2p w). exact (Hptw2 w Hw).
        -- rewrite (Heq2'' x). rewrite (Heq2a x). right. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma NEval_left_fwd_transfer_fwdhere_con :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Some (BExpr (EVar y)) ->
  forall brs c zs ys body Gmid Gam' v',
    NEval_left P nil Gam (BExpr (EVar y)) Gmid (BExpr (ECon c zs)) ->
    In (c, ys, body) brs ->
    length ys = length zs ->
    NEval_left P nil Gmid (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr2 G1 Gam' -> HeapCorr2 G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hb brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2.
  destruct (NEval_left_evar_shape P nil Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
    [ [Hcase1 [HeqGmid _]]
    | [ [Hcase2 [_ Heqv]]
      | [ [Hcase3 [_ Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
  - subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hcase1 in Hb. discriminate Hb. }
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - apply NL_VarCons. exact Hcase1. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hb) Hcase1) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1x HHC2.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_left_con_persists P nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hcase1). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2) | exact Hcy]).
      destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr2 G1v (hupd Gam' x (BExpr (ECon c zs)))).
      { eapply HeapCorr2_update_achieved; [exact HHC2 | exact HG1x | exact (not_eq_sym Hxy) | exact Hcl1 | exact Hz1 | exact Hcy]. }
      eapply HeapCorr2_pointwise; [exact HHC2' | exact Heq2'].
  - subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hz in Hb. injection Hb as Hb. exact (Hne2 Hb). }
    assert (HforceY : NEval_left P (x :: nil) Gam (BExpr (EVar y)) (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { exact (NEval_left_alias_weaken_force_y P x y Hxy Gam (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs)) Hrec1 Hb). }
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x))
               (hupd (hupd G1 y (BExpr (ECon c zs))) x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - exact HforceY. }
    assert (HG1xy : G1 x = Some (BExpr (EVar y)) /\ G1 y = Some e0).
    { exact (NEval_left_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil) Gam e0 G1 (BExpr (ECon c zs)) Hrec
               (or_introl eq_refl) Hb Hz). }
    destruct HG1xy as [HG1x HG1y].
    assert (Hgmidx : hupd G1 y (BExpr (ECon c zs)) x = Some (BExpr (EVar y))).
    { rewrite (hupd_neq G1 y (BExpr (ECon c zs)) x Hxy). exact HG1x. }
    assert (Hgmidy : hupd G1 y (BExpr (ECon c zs)) y = Some (BExpr (ECon c zs))).
    { unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy nil (hupd G1 y (BExpr (ECon c zs)))
                (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hgmidx) Hgmidy) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1vx HHC2.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_left_con_persists P nil (hupd G1 y (BExpr (ECon c zs)))
                 (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hgmidy). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2) | exact Hcy]).
      destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr2 G1v (hupd Gam' x (BExpr (ECon c zs)))).
      { eapply HeapCorr2_update_achieved; [exact HHC2 | exact HG1vx | exact (not_eq_sym Hxy) | exact Hcl1 | exact Hz1 | exact Hcy]. }
      eapply HeapCorr2_pointwise; [exact HHC2' | exact Heq2'].
Qed.

Lemma NEval_left_force_reaches_achieved :
  forall P G Gam, HeapCorr G Gam ->
  forall F e Gam' v, NEval_left P F Gam e Gam' v ->
  forall y, e = BExpr (EVar y) ->
  forall z1 c1 args1, ContractLoc G y z1 -> G z1 = Some (GExpr (ECon c1 args1)) ->
  v = BExpr (ECon c1 args1).
Proof.
  intros P G Gam HGam F e Gam' v H.
  induction H as
    [ F0 G0 z c args Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G0
    | F0 G0 c args
    | F0 G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G0 G1 z e0 k v1 HzFresh Hrec IH
    | F0 G0 x1 y1 G1 v1 Hrec IH
    | F0 G0 z c zs brs ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1' ys1 body1 brs G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros y Ht z1 c1 args1 Hcl1 Hz1; try discriminate Ht.
  - injection Ht as Ht; subst z.
    assert (HCEy : CorrE G y (BExpr (ECon c args))) by (eapply HeapCorr_Gam_CorrE; [exact HGam | exact Hz]).
    destruct (CorrE_con_to_contractloc G y c args HCEy) as [z2 [Hcl2 Hz2]].
    assert (Heqz : z1 = z2) by (eapply ContractLoc_functional; [exact Hcl1 | exact Hcl2]).
    subst z2. rewrite Hz1 in Hz2. injection Hz2 as Hz2. subst c1 args1. reflexivity.
  - injection Ht as Ht; subst z.
    exfalso.
    assert (HCEy : CorrE G y (BExpr (EVar y))) by (eapply HeapCorr_Gam_CorrE; [exact HGam | exact Hz]).
    destruct (CorrE_forced_shape G y (BExpr (EVar y)) HCEy) as
      [ [c [args [Hgy Hb]]]
      | [ [Hgy Hb]
        | [ [f [args [Hgy Hb]]]
          | [ [y1 [y2 [Hgy Hb]]]
            | [ [z0 [Hgy Hb]]
              | [ [Hgy Hb]
                | [ [y0 [Hgy Hb]]
                  | [y0 [z0 [c0 [args0 [Hgy [Hcl0 [Hz0 Hb]]]]]]] ] ] ] ] ] ] ]; try discriminate Hb.
    + assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + injection Hb as Hb. subst z0.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + injection Hb as Hb. subst y0.
      exact (ContractLoc_no_selfFwd G y z1 Hcl1 Hgy).
  - injection Ht as Ht; subst z.
    exfalso.
    assert (HCEy : CorrE G y (BExpr EFree)) by (eapply HeapCorr_Gam_CorrE; [exact HGam | exact Hz]).
    destruct (CorrE_forced_shape G y (BExpr EFree) HCEy) as
      [ [c [args [Hgy Hb]]]
      | [ [Hgy Hb]
        | [ [f [args [Hgy Hb]]]
          | [ [y1 [y2 [Hgy Hb]]]
            | [ [z0 [Hgy Hb]]
              | [ [Hgy Hb]
                | [ [y0 [Hgy Hb]]
                  | [y0 [z0 [c0 [args0 [Hgy [Hcl0 [Hz0 Hb]]]]]]] ] ] ] ] ] ] ]; try discriminate Hb.
  - injection Ht as Ht; subst z.
    assert (HCEy : CorrE G y e0) by (eapply HeapCorr_Gam_CorrE; [exact HGam | exact Hz]).
    destruct (CorrE_forced_shape G y e0 HCEy) as
      [ [c [args [Hgy Hb]]]
      | [ [Hgy Hb]
        | [ [f [args [Hgy Hb]]]
          | [ [y1 [y2 [Hgy Hb]]]
            | [ [z0 [Hgy Hb]]
              | [ [Hgy Hb]
                | [ [y0 [Hgy Hb]]
                  | [y0 [z0 [c0 [args0 [Hgy [Hcl0 [Hz0 Hb]]]]]]] ] ] ] ] ] ] ].
    + exfalso. subst e0. exact (Hne1 c args eq_refl).
    + exfalso. subst e0. exact (Hne2 eq_refl).
    + exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + subst e0.
      assert (Hcl1' : ContractLoc G y0 z1).
      { inversion Hcl1 as [x0 e1 Hx0 | x0 y0' z0' Hx0 Hcl0']; subst.
        - rewrite Hgy in Hx0; discriminate Hx0.
        - rewrite Hgy in Hx0; injection Hx0 as Hx0; subst y0'; exact Hcl0'. }
      exact (IH HGam y0 eq_refl z1 c1 args1 Hcl1' Hz1).
    + exfalso. subst e0. exact (Hne1 c0 args0 eq_refl).
Qed.

Lemma NEval_left_fwd_transfer_fwdchase_con :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Gam y ->
  forall brs c zs ys body Gam' v',
    Gam y = Some (BExpr (ECon c zs)) ->
    In (c, ys, body) brs ->
    length ys = length zs ->
    NEval_left P nil Gam (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr2 G1 Gam' -> HeapCorr2 G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hxy brs c zs ys body Gam' v' Hy HIn Hlen Hrec2.
  assert (Hx : Gam x = Some (BExpr (ECon c zs))) by (rewrite Hxy; exact Hy).
  exists Gam'. split.
  - eapply NL_Select; [apply NL_VarCons; exact Hx | exact HIn | exact Hlen | exact Hrec2].
  - intros G1 _ HHC. exact HHC.
Qed.

(* HeapCorr: a strictly WEAKER correspondence than HeapCorr2, used ONLY as
   the output type of the hardest sub-case below (a genuine multi-hop Fwd
   chain landing on Free).  The problem HeapCorr2 cannot accommodate there:
   NL_VarExp's memoization ALWAYS path-compresses a forced variable straight
   to its fully-resolved value -- so when x forces THROUGH y to a free
   variable x' that a later guess narrows to Con c args, x's own witness
   ends up EVar x' (skipping y entirely), not EVar y.  CorrE (curry.v) has
   no room for that: CorrE_FwdHere only accepts the IMMEDIATE Fwd target,
   and the "skip a hop" shortcut (CorrE_FwdAchievedCon) exists ONLY for an
   already-ACHIEVED constructor -- curry.v's own comment on CorrE explains
   why there is deliberately no analogous shortcut for a further ALIAS
   ("FwdAchievedFree"): Con is permanent once written, so a skip-ahead Con
   witness can never go stale, but an alias could be re-pointed later, so
   skipping to one isn't safe in general.

   HeapCorr grants a Fwd location one more way to be valid: instead of
   matching CorrE outright, its OWN witness and its Fwd target's OWN witness
   may instead each independently chase, via PURE Nat-heap variable-to-
   variable hops (VarChase below -- never copying raw, possibly-still-
   changing content the way curry.v's old, reverted CorrE_FwdChase did),
   down to the SAME terminal value.  That terminal value, in every use here,
   is a genuine achieved constructor -- exactly the case CorrE_FwdAchievedCon
   already trusts as permanent, just reached one hop later than CorrE alone
   can see.  This is strictly LOCAL to this file: curry.v's own CorrE/
   HeapCorr are untouched, and HeapCorr2 (still HeapCorr /\ ChainConsistent)
   trivially embeds into HeapCorr below, so nothing upstream needs to
   change to supply the (still-stronger) HeapCorr2 hypothesis this lemma
   takes in. *)
Inductive VarChase (Gam : NHeap) : var -> Blk -> Prop :=
| VChase_Here : forall w b, Gam w = Some b ->
    (forall w', b = BExpr (EVar w') -> w' = w) ->
    VarChase Gam w b
| VChase_Hop : forall w w' e, Gam w = Some (BExpr (EVar w')) -> w' <> w ->
    VarChase Gam w' e -> VarChase Gam w e.

(* VarChaseN / VarChaseN_functional: a nat-indexed twin of VarChase (needed
   because VarChase itself lives in Prop, and Coq forbids eliminating a
   non-singleton Prop into Set/Type -- so a "VarChase_size" Fixpoint
   computing a nat directly from a VarChase proof term is not constructible;
   the standard workaround is exactly this, an independent nat-indexed
   relation plus an existence lemma).  Since Gam is a function, the FIRST
   step any VarChase derivation from a given w can take is forced
   (VChaseN_Here applies iff Gam w isn't EVar-of-something-else,
   VChaseN_Hop applies iff it is) -- so for FIXED (Gam, w, e), the n such
   that VarChaseN Gam n w e holds is unique.  This is the key fact used
   below to rule out a VarChase chain looping back through an
   already-visited node: looping back would force TWO DIFFERENT n's for
   the same (Gam, w, e), which functionality rules out arithmetically. *)
Inductive VarChaseN (Gam : NHeap) : nat -> var -> Blk -> Prop :=
| VChaseN_Here : forall w b, Gam w = Some b ->
    (forall w', b = BExpr (EVar w') -> w' = w) ->
    VarChaseN Gam 0 w b
| VChaseN_Hop : forall n w w' e, Gam w = Some (BExpr (EVar w')) -> w' <> w ->
    VarChaseN Gam n w' e -> VarChaseN Gam (S n) w e.

Lemma VarChase_to_VarChaseN : forall Gam w e, VarChase Gam w e -> exists n, VarChaseN Gam n w e.
Proof.
  intros Gam w e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec [n IHn]].
  - exists 0. apply VChaseN_Here; assumption.
  - exists (S n). eapply VChaseN_Hop; eassumption.
Qed.

Lemma VarChaseN_to_VarChase : forall Gam n w e, VarChaseN Gam n w e -> VarChase Gam w e.
Proof.
  intros Gam n w e H.
  induction H as [w0 b0 Hb0 Hself | n0 w0 w0' e0 Hw0 Hne Hrec IH].
  - apply VChase_Here; assumption.
  - eapply VChase_Hop; eassumption.
Qed.

Lemma VarChaseN_functional :
  forall Gam n1 n2 w e, VarChaseN Gam n1 w e -> VarChaseN Gam n2 w e -> n1 = n2.
Proof.
  intros Gam n1 n2 w e H1.
  revert n2.
  induction H1 as [w0 b0 Hb0 Hself | n0 w0 w0' e0 Hw0 Hne Hrec IH]; intros n2 H2.
  - destruct H2 as [w2 b2 Hb2 Hself2 | n2 w2 w2' e2 Hw2 Hne2 Hrec2].
    + reflexivity.
    + exfalso.
      rewrite Hw2 in Hb0. injection Hb0 as Hb0.
      exact (Hne2 (Hself w2' (eq_sym Hb0))).
  - destruct H2 as [w2 b2 Hb2 Hself2 | n2 w2 w2' e2 Hw2 Hne2 Hrec2].
    + exfalso.
      rewrite Hw0 in Hb2. injection Hb2 as Hb2. subst b2.
      exact (Hne (Hself2 w0' eq_refl)).
    + rewrite Hw0 in Hw2. injection Hw2 as Hw2. subst w2'.
      f_equal. exact (IH n2 Hrec2).
Qed.

(* The VarChase-to-NEval_left conversion, mirroring force_var_N_left's own
   Hdisj-threading pattern exactly, but on VarChaseN's own size instead of
   ContractLocN's graph distance -- this is what lets the guard-freshness
   argument close: any z already in the guard F has a STRICTLY LARGER
   VarChaseN distance to the same target than the current position, so if
   the chase ever tried to revisit z, VarChaseN_functional would force z's
   distance to equal the (smaller) current one, contradicting the strict
   inequality via lia. *)
(* GamChainTo Gam F w: F, read head-to-tail, is a pure Nat-heap alias chain
   ending at w (head's Gam-value is EVar w, second element's Gam-value is
   EVar-of-head, etc.) -- exactly the invariant a graph-distance-driven
   force_var recursion maintains on its own guard list whenever it takes
   CorrE's FwdHere branch (which gives Gam x_i = EVar x_(i+1), the SAME
   shape VChaseN_Hop needs), letting a VarChaseN witness picked up partway
   through (CorrE3's own shortcut disjunct) be freely PREPENDED with the
   guard's own already-established chain. *)
Fixpoint GamChainTo (Gam : NHeap) (chain : list var) (w : var) : Prop :=
  match chain with
  | nil => True
  | x :: rest => Gam x = Some (BExpr (EVar w)) /\ GamChainTo Gam rest x
  end.

Lemma GamChainTo_prepend_VarChaseN :
  forall Gam F w, GamChainTo Gam F w -> NoDup (w :: F) ->
  forall n e, VarChaseN Gam n w e ->
  forall z, In z F -> exists m, VarChaseN Gam m z e /\ n < m.
Proof.
  intros Gam F.
  induction F as [ | x rest IHrest]; intros w Hchain Hnodup n e Hvcn z Hin.
  - destruct Hin.
  - simpl in Hchain. destruct Hchain as [Hgx Hchainrest].
    assert (Hxw : x <> w).
    { intro Heq; subst x. inversion Hnodup as [| a l Hnotin Hnd Heql]; subst.
      apply Hnotin. left. reflexivity. }
    assert (HvcnX : VarChaseN Gam (S n) x e)
      by (eapply VChaseN_Hop; [exact Hgx | exact (not_eq_sym Hxw) | exact Hvcn]).
    destruct Hin as [Heq | Hin].
    + subst z. exists (S n). split; [exact HvcnX | lia].
    + assert (Hnodup' : NoDup (x :: rest)).
      { inversion Hnodup as [| a l Hnotin Hnd Heql]; subst. exact Hnd. }
      destruct (IHrest x Hchainrest Hnodup' (S n) e HvcnX z Hin) as [m [Hm Hlt]].
      exists m. split; [exact Hm | lia].
Qed.

Lemma VarChase_functional : forall Gam w e1 e2, VarChase Gam w e1 -> VarChase Gam w e2 -> e1 = e2.
Proof.
  intros Gam w e1 e2 H1.
  revert e2.
  induction H1 as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH]; intros e2 H2.
  - destruct H2 as [w2 b2 Hb2 Hself2 | w2 w2' e2' Hw2 Hne2 Hrec2].
    + congruence.
    + exfalso. rewrite Hw2 in Hb0. injection Hb0 as Hb0.
      exact (Hne2 (Hself w2' (eq_sym Hb0))).
  - destruct H2 as [w2 b2 Hb2 Hself2 | w2 w2' e2' Hw2 Hne2 Hrec2].
    + exfalso. rewrite Hw0 in Hb2. injection Hb2 as Hb2. subst b2.
      exact (Hne (Hself2 w0' eq_refl)).
    + rewrite Hw0 in Hw2. injection Hw2 as Hw2. subst w2'.
      exact (IH e2' Hrec2).
Qed.

(* Extracts w's OWN immediate content and how the chase used it, without
   requiring the caller to destruct/invert the VarChase witness directly
   against a fixed non-variable target index (which is fragile -- see
   DEAD_ENDS.md). Isolated here as its own lemma so the destruct happens in
   a minimal, self-contained context where Coq's automatic generalization
   of w/e (both already-fixed local variables that appear nowhere else)
   is unproblematic. *)
Lemma VarChase_first_step :
  forall Gam w e, VarChase Gam w e ->
  exists b, Gam w = Some b /\
    (b = e \/ (exists w', b = BExpr (EVar w') /\ w' <> w /\ VarChase Gam w' e)).
Proof.
  intros Gam w e H.
  destruct H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec].
  - exists b0. split; [exact Hb0 | left; reflexivity].
  - exists (BExpr (EVar w0')). split; [exact Hw0 | right; exists w0'; split; [reflexivity | split; [exact Hne | exact Hrec]]].
Qed.

(* If y's OWN Nat-heap chase (VarChase, a STATIC fact about Gam, before any
   forcing) ALREADY reaches Con c args, then ACTUALLY forcing y (any guard,
   any resulting heap) can only ever compute that SAME value: forcing
   re-derives the identical hop-by-hop structure VarChase already describes
   (NEval_left_evar_shape's own case split mirrors VarChase's Here/Hop
   split exactly), so by induction on the VarChase witness the two notions
   agree. Needed to reconcile a location's STATIC skip-ahead witness with
   what some OTHER location's forcing dynamically computes when both
   happen to alias the same intermediate. *)
Lemma NEval_left_force_matches_VarChase :
  forall Gam y e, VarChase Gam y e ->
  forall c args, e = BExpr (ECon c args) ->
  forall P F Gmid v, NEval_left P F Gam (BExpr (EVar y)) Gmid v ->
  v = e.
Proof.
  intros Gam y e Hchase.
  induction Hchase as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH];
    intros c args Heqe P F Gmid v H.
  - destruct (NEval_left_evar_shape P F Gam w0 Gmid v H) as
      [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1 [Hz [Hne1 _]]]]]]]].
    + congruence.
    + congruence.
    + congruence.
    + exfalso. apply (Hne1 c args). congruence.
  - destruct (NEval_left_evar_shape P F Gam w0 Gmid v H) as
      [ [Hcase1 [_ [c1 [args1 Heqv1]]]]
      | [ [Hcase2 _]
        | [ [Hcase3 _]
          | [_ [e1 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec2 HeqGmid]]]]]]]]]]].
    + congruence.
    + exfalso. apply Hne. congruence.
    + congruence.
    + assert (Heqe1 : e1 = BExpr (EVar w0')) by congruence.
      rewrite Heqe1 in Hrec2.
      exact (IH c args Heqe P (w0 :: F) G1 v Hrec2).
Qed.

(* Transporting an EXISTING VarChase witness (for any p) across memoizing x
   directly to a constructor x was already known (via SOME VarChase of its
   own, whatever shape it took) to chase to -- needed because NL_VarExp's
   own conclusion always performs exactly this hupd, so force_var's own
   result heap has to be shown to still satisfy HeapCorr.  Deliberately
   general: does NOT need to know x's own immediate Gam-alias, or that it
   matches x's own graph-level forward target -- only that x's chase
   (however it's routed) reaches Con c args, which is exactly what
   CorrE3's disjunct 2 already hands over regardless of whether x's alias
   happens to agree with its graph target.  Any OTHER location p's chase
   either never touches x (untouched, trivial), or touches x and (by
   VarChase_functional, since x's own chase target was already pinned to
   Con c args) is forced to reach the SAME Con c args at x -- so it just
   terminates one hop earlier after the update, via VChase_Here, instead
   of continuing through whatever x's own alias used to be. *)
Lemma VarChase_transport_shorten :
  forall Gam x c args, VarChase Gam x (BExpr (ECon c args)) ->
  forall p e, VarChase Gam p e -> VarChase (hupd Gam x (BExpr (ECon c args))) p e.
Proof.
  intros Gam x c args Hchase p e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH].
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + assert (Heq : b0 = BExpr (ECon c args)).
      { apply (VarChase_functional Gam w0 b0 (BExpr (ECon c args)) (VChase_Here Gam w0 b0 Hb0 Hself)).
        rewrite Heqwx. exact Hchase. }
      subst b0.
      apply VChase_Here.
      * rewrite Heqwx. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * intros w' Hcontra; discriminate Hcontra.
    + apply VChase_Here.
      * rewrite (hupd_neq Gam x (BExpr (ECon c args)) w0 Hnewx). exact Hb0.
      * exact Hself.
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + assert (Heq : e0 = BExpr (ECon c args)).
      { apply (VarChase_functional Gam w0 e0 (BExpr (ECon c args)) (VChase_Hop Gam w0 w0' e0 Hw0 Hne Hrec)).
        rewrite Heqwx. exact Hchase. }
      subst e0.
      apply VChase_Here.
      * rewrite Heqwx. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      * intros w' Hcontra; discriminate Hcontra.
    + eapply VChase_Hop.
      * rewrite (hupd_neq Gam x (BExpr (ECon c args)) w0 Hnewx). exact Hw0.
      * exact Hne.
      * exact IH.
Qed.

(* Exact converse of VarChase_transport_shorten: if x's OWN chase (in the
   heap BEFORE memoizing it) already reaches Con c args, then memoizing x
   to that same value is a genuine no-op for VarChase purposes in BOTH
   directions -- this is the "peel the memoization back off" half, needed
   to walk a VarChase fact computed against a doubly-forced heap back down
   to the original, still-lazy heap. Proof mirrors _shorten's case split
   exactly, just with the roles of the two heaps swapped. *)
Lemma VarChase_transport_unshorten :
  forall Gam x c args, VarChase Gam x (BExpr (ECon c args)) ->
  forall Gam1 p e, VarChase Gam1 p e -> Gam1 = hupd Gam x (BExpr (ECon c args)) -> VarChase Gam p e.
Proof.
  intros Gam x c args Hchase Gam1 p e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH]; intro Heq.
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. rewrite Heq in Hb0. unfold hupd in Hb0. rewrite Nat.eqb_refl in Hb0.
      injection Hb0 as Hb0. subst b0. exact Hchase.
    + apply VChase_Here.
      * rewrite Heq in Hb0. rewrite (hupd_neq Gam x (BExpr (ECon c args)) w0 Hnewx) in Hb0. exact Hb0.
      * exact Hself.
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. rewrite Heq in Hw0. unfold hupd in Hw0. rewrite Nat.eqb_refl in Hw0. discriminate Hw0.
    + eapply VChase_Hop.
      * rewrite Heq in Hw0. rewrite (hupd_neq Gam x (BExpr (ECon c args)) w0 Hnewx) in Hw0. exact Hw0.
      * exact Hne.
      * exact (IH Heq).
Qed.

(* Companion to VarChase_transport_shorten, for the OPPOSITE direction:
   downgrading y0's OWN slot from an achieved Con c args back to a one-hop
   alias EVar w -- valid ONLY because w ITSELF ALREADY resolves to the
   SAME Con c args, so every OTHER location's existing chase survives
   unchanged (chases untouched by y0 pass straight through; a chase that
   used to terminate AT y0 via VChase_Here now takes one extra hop through
   w, landing on the identical final value). Needed when a location gets
   "reset" to an earlier, less-resolved-but-still-consistent alias, e.g.
   G_CaseFwd's skip-ahead reconciliation, where y0's Nat-heap slot may end
   up back at its ORIGINAL pre-forcing alias rather than staying achieved. *)
Lemma VarChase_transport_downgrade_evar :
  forall Gam y0 w c args, Gam y0 = Some (BExpr (ECon c args)) ->
  Gam w = Some (BExpr (ECon c args)) -> w <> y0 ->
  forall p e, VarChase Gam p e -> VarChase (hupd Gam y0 (BExpr (EVar w))) p e.
Proof.
  intros Gam y0 w c args Hgy0 Hgw Hwy0 p e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH].
  - destruct (Nat.eq_dec w0 y0) as [Heqwy0 | Hnewy0].
    + subst w0. rewrite Hgy0 in Hb0. injection Hb0 as Hb0. subst b0.
      eapply VChase_Hop.
      * unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * exact Hwy0.
      * apply VChase_Here.
        -- rewrite (hupd_neq Gam y0 (BExpr (EVar w)) w Hwy0). exact Hgw.
        -- intros w' Hcontra; discriminate Hcontra.
    + apply VChase_Here.
      * rewrite (hupd_neq Gam y0 (BExpr (EVar w)) w0 Hnewy0). exact Hb0.
      * exact Hself.
  - destruct (Nat.eq_dec w0 y0) as [Heqwy0 | Hnewy0].
    + subst w0. rewrite Hgy0 in Hw0. discriminate Hw0.
    + eapply VChase_Hop.
      * rewrite (hupd_neq Gam y0 (BExpr (EVar w)) w0 Hnewy0). exact Hw0.
      * exact Hne.
      * exact IH.
Qed.

(* ContractLoc's own two constructors, used directly (not via inversion, whose
   auto-generated names are unpredictable): CL_Here forces x = z, so whenever
   x <> z the ONLY possibility is CL_Fwd, handing back the immediate hop. *)
Lemma ContractLoc_first_hop :
  forall G x z, ContractLoc G x z -> x <> z -> exists w, G x = Some (GFwd w) /\ ContractLoc G w z.
Proof.
  intros G x z H.
  destruct H as [x0 e0 H0 | x0 y0 z0 H0 Hcl0]; intro Hxz.
  - exfalso. exact (Hxz eq_refl).
  - exists y0. split; [exact H0 | exact Hcl0].
Qed.

Lemma ContractLoc_trans :
  forall G x y z, ContractLoc G x y -> ContractLoc G y z -> ContractLoc G x z.
Proof.
  intros G x y z Hxy Hyz.
  destruct (ContractLoc_to_N G x y Hxy) as [n Hn].
  exact (ContractLocN_ContractLoc_compose G n x y Hn z Hyz).
Qed.

(* CorrE3's own "chase" disjunct, corrected: a forwarding location's Nat-heap
   witness can be validated not just against its IMMEDIATE Fwd target (as
   plain CorrE requires) but against wherever that target's own MULTI-HOP
   ContractLoc chain ends up -- exactly the graph-level slack
   CorrE_FwdAchievedCon already trusts for an outright achieved witness, now
   extended to a witness that's still a Nat-heap alias one hop short of it.
   (An earlier version of this required the Fwd target's OWN Nat-heap value
   to ALSO chase to the same terminal -- unnecessary, and wrong whenever the
   graph-level chain from that immediate target is itself more than one hop:
   G_CaseFun/G_CaseFwd never re-compress an intermediate Fwd edge, so a real
   multi-hop chain is completely ordinary, not a corner case.) *)
Definition CorrE3 (G : Graph) (Gam : NHeap) (x : var) (b : Blk) : Prop :=
  CorrE G x b \/
  (exists y0 z c args, G x = Some (GFwd y0) /\ ContractLoc G y0 z /\
     G z = Some (GExpr (ECon c args)) /\ VarChase Gam x (BExpr (ECon c args))).

Definition HeapCorr (G : Graph) (Gam : NHeap) : Prop :=
  forall x, match G x with
            | None => Gam x = None
            | Some _ => exists b, Gam x = Some b /\ CorrE3 G Gam x b
            end.

(* NOTE: the hypothesis here is deliberately curry.HeapCorr (the ORIGINAL,
   base notion from curry.v), qualified explicitly because it is otherwise
   shadowed from this point on by this file's own HeapCorr (renamed from
   HeapCorr3) -- this lemma is precisely the "old HeapCorr implies new
   HeapCorr" embedding. *)
Lemma HeapCorr_to_HeapCorr : forall G Gam, curry.HeapCorr G Gam -> HeapCorr G Gam.
Proof.
  intros G Gam HGC x. specialize (HGC x).
  destruct (G x) as [gx | ]; [ | exact HGC].
  destruct HGC as [b [Hb HCE]]. exists b. split; [exact Hb | left; exact HCE].
Qed.

Lemma HeapCorr2_to_HeapCorr : forall G Gam, HeapCorr2 G Gam -> HeapCorr G Gam.
Proof. intros G Gam [HGC _]. exact (HeapCorr_to_HeapCorr G Gam HGC). Qed.

(* HeapCorr's own analogue of HeapCorr2_update_achieved -- simpler than the
   HeapCorr2 version, since HeapCorr is purely pointwise (no ChainConsistent
   cross-location invariant to re-establish): the memoized location x gets
   its new witness directly from CorrE_FwdAchievedCon (graph-only, doesn't
   even look at Gam), and every OTHER location p's existing witness is
   either Gam-independent (CorrE, disjunct 1, untouched) or a VarChase chase
   that VarChase_transport_shorten carries across the update unchanged.
   Deliberately does NOT require Gam x to be any particular alias (in
   particular, NOT that it matches y0) -- only that x's OWN chase (via
   VarChase, whichever way CorrE3 happens to justify it) already reaches
   Con c args, which is exactly what's available at an intermediate hop of
   someone else's "skip-ahead" chase, not just at a location whose alias
   happens to agree with its own graph-level forward target. *)
Lemma HeapCorr_update_achieved :
  forall G Gam x y0 ytgt c args,
    HeapCorr G Gam ->
    G x = Some (GFwd y0) ->
    ContractLoc G y0 ytgt ->
    G ytgt = Some (GExpr (ECon c args)) ->
    VarChase Gam x (BExpr (ECon c args)) ->
    HeapCorr G (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x y0 ytgt c args HGam Hgx Hcl Hgtgt Hchase_x p.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. rewrite Hgx. unfold hupd. rewrite Nat.eqb_refl.
    exists (BExpr (ECon c args)). split; [reflexivity | ].
    left. eapply CorrE_FwdAchievedCon; [exact Hgx | exact Hcl | exact Hgtgt].
  - specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp.
    2: { rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx). exact HGam. }
    destruct HGam as [b [Hb HCE3]].
    rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx).
    exists b. split; [exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. exact HCE.
    + right. exists y1, z1, c1, args1.
      repeat split; try assumption.
      exact (VarChase_transport_shorten Gam x c args Hchase_x p
               (BExpr (ECon c1 args1)) HVC).
Qed.

(* HeapCorr's own analogue of VarChase_transport_downgrade_evar: resetting
   y0's slot back to a one-hop alias EVar w (w already independently
   achieved to the SAME value) preserves HeapCorr, GIVEN the caller
   separately justifies y0's OWN new witness (its graph-level shape can
   vary -- FwdHere or the VarChase-skip-ahead disjunct -- so it isn't
   derived here, only threaded through); every OTHER location's existing
   witness survives via VarChase_transport_downgrade_evar. *)
Lemma HeapCorr_downgrade_evar :
  forall G Gam y0 w c args, HeapCorr G Gam ->
  Gam y0 = Some (BExpr (ECon c args)) -> Gam w = Some (BExpr (ECon c args)) -> w <> y0 ->
  CorrE3 G (hupd Gam y0 (BExpr (EVar w))) y0 (BExpr (EVar w)) ->
  HeapCorr G (hupd Gam y0 (BExpr (EVar w))).
Proof.
  intros G Gam y0 w c args HGam Hgy0 Hgw Hwy0 HCEy0 p.
  destruct (Nat.eq_dec p y0) as [Heqpy0 | Hnepy0].
  - subst p.
    assert (HGamy0 := HGam y0).
    destruct (G y0) as [gy0 | ] eqn:EGy0; [ | rewrite HGamy0 in Hgy0; discriminate Hgy0].
    unfold hupd; rewrite Nat.eqb_refl.
    exists (BExpr (EVar w)). split; [reflexivity | exact HCEy0].
  - specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp.
    2: { rewrite (hupd_neq Gam y0 (BExpr (EVar w)) p Hnepy0). exact HGam. }
    destruct HGam as [b [Hb HCE3]].
    rewrite (hupd_neq Gam y0 (BExpr (EVar w)) p Hnepy0).
    exists b. split; [exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. exact HCE.
    + right. exists y1, z1, c1, args1.
      repeat split; try assumption.
      exact (VarChase_transport_downgrade_evar Gam y0 w c args Hgy0 Hgw Hwy0 p
               (BExpr (ECon c1 args1)) HVC).
Qed.

(* ChainConsistent's own analogue of HeapCorr_update_achieved: promoting x
   from its lazy one-hop alias EVar y0 to the achieved constructor preserves
   ChainConsistent, PROVIDED y0 is ALREADY achieved to the SAME value first
   (matching the order force_var_N's own recursive construction already
   uses: the inner call for y0 finishes and memoizes before the outer one
   for x does).  x's own PRIOR witness being EVar y0 (not yet Con) is what
   rules out the one dangerous case: some OTHER, already-achieved p forwarding
   to x -- ChainConsistent (before the update) would already force x's own
   PRIOR witness to be Con-shaped too, contradicting EVar y0. *)
Lemma ChainConsistent_update_achieved :
  forall G Gam x y0 c args,
    ChainConsistent G Gam ->
    G x = Some (GFwd y0) ->
    Gam x = Some (BExpr (EVar y0)) ->
    Gam y0 = Some (BExpr (ECon c args)) ->
    ChainConsistent G (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x y0 c args HCC Hgx Hgamx Hgamy0 p q Hpq c' args' Hpc'.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p.
    assert (Hqy0 : q = y0) by congruence. subst q.
    unfold hupd in Hpc'. rewrite Nat.eqb_refl in Hpc'.
    injection Hpc' as Hc' Hargs'; subst c' args'.
    destruct (Nat.eq_dec y0 x) as [Heqy0x | Hney0x].
    + subst y0. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + rewrite (hupd_neq Gam x (BExpr (ECon c args)) y0 Hney0x).
      exact Hgamy0.
  - rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx) in Hpc'.
    destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
    + subst q. exfalso.
      assert (Hgamx' : Gam x = Some (BExpr (ECon c' args'))) by exact (HCC p x Hpq c' args' Hpc').
      rewrite Hgamx in Hgamx'. discriminate Hgamx'.
    + rewrite (hupd_neq Gam x (BExpr (ECon c args)) q Hneqx).
      exact (HCC p q Hpq c' args' Hpc').
Qed.

(* Extending Gam at a fresh location x (Gam x = None) leaves every OTHER
   location's VarChase witness intact -- mirrors curry.v's own
   ContractLoc_extend exactly: a chase can never pass THROUGH a None
   location (VarChase's own Here/Hop cases both require Gam _ = Some _ at
   every step), so a chase that never touched x before still doesn't. *)
Lemma VarChase_extend_fresh :
  forall Gam x newval, Gam x = None ->
  forall y target, VarChase Gam y target -> VarChase (hupd Gam x newval) y target.
Proof.
  intros Gam x newval Hx y target H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH].
  - assert (Hne0 : w0 <> x) by (intro Heq; subst w0; rewrite Hx in Hb0; discriminate Hb0).
    apply VChase_Here.
    + rewrite (hupd_neq Gam x newval w0 Hne0). exact Hb0.
    + exact Hself.
  - assert (Hne0 : w0 <> x) by (intro Heq; subst w0; rewrite Hx in Hw0; discriminate Hw0).
    eapply VChase_Hop.
    + rewrite (hupd_neq Gam x newval w0 Hne0). exact Hw0.
    + exact Hne.
    + exact IH.
Qed.

(* HeapCorr's own analogue of curry.v's/HeapCorr2's HeapCorr_extend --
   simpler than either, since HeapCorr is purely pointwise: x's own new
   witness comes directly from let_content's own case analysis (mirroring
   HeapCorr2_update_to_direct's identical case split), and every OTHER
   location p's existing witness survives untouched, since x being FRESH
   in both G and Gam (the latter following from HeapCorr itself) means no
   ContractLoc or VarChase chain could ever have passed through it in the
   first place -- no WellFoundedFwd needed at all, unlike the ChainConsistent
   half of the old HeapCorr2_extend. *)
Lemma HeapCorr_extend :
  forall G Gam x e, HeapCorr G Gam -> G x = None ->
  HeapCorr (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x e HGam Hx p.
  assert (HGamx : Gam x = None) by (specialize (HGam x); rewrite Hx in HGam; exact HGam).
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. unfold hupd. rewrite Nat.eqb_refl.
    eexists. split; [reflexivity | ].
    destruct e; simpl.
    + left. eapply CorrE_VarThunk. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + left. eapply CorrE_Bot. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + left. eapply CorrE_Free. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + left. eapply CorrE_Choice. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + left. eapply CorrE_Fun. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
    + left. eapply CorrE_Con. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
  - rewrite (hupd_neq G x (GExpr e) p Hnepx).
    specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp; [ | rewrite (hupd_neq Gam x (let_content x e) p Hnepx); exact HGam].
    destruct HGam as [b [Hb HCE3]].
    exists b. split; [rewrite (hupd_neq Gam x (let_content x e) p Hnepx); exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. destruct HCE as
        [ x1 c0 args0 H0 | x1 H0 | x1 f0 args0 H0 | x1 y0 z0 H0 | x1 z0 H0 | x1 H0
        | x1 y0 H0 | x1 y0 z0 c0 args0 H0 Hcl0 Hz0 ].
      * eapply CorrE_Con. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_Free. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_Fun. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_Choice. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_VarThunk. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_Bot. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_FwdHere. rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
      * eapply CorrE_FwdAchievedCon.
        -- rewrite (hupd_neq G x (GExpr e) x1 Hnepx). exact H0.
        -- exact (ContractLoc_extend G x (GExpr e) Hx y0 z0 Hcl0).
        -- assert (Hz0x : z0 <> x) by (intro Heq; subst z0; rewrite Hx in Hz0; discriminate Hz0).
           rewrite (hupd_neq G x (GExpr e) z0 Hz0x). exact Hz0.
    + right. exists y1, z1, c1, args1.
      split; [rewrite (hupd_neq G x (GExpr e) p Hnepx); exact Hgp | ].
      split; [exact (ContractLoc_extend G x (GExpr e) Hx y1 z1 Hcl1) | ].
      split; [assert (Hz1x : z1 <> x) by (intro Heq; subst z1; rewrite Hx in Hz1; discriminate Hz1);
               rewrite (hupd_neq G x (GExpr e) z1 Hz1x); exact Hz1 | ].
      exact (VarChase_extend_fresh Gam x (let_content x e) HGamx p (BExpr (ECon c1 args1)) HVC).
Qed.

Lemma HeapCorr_extend_free_list :
  forall ws G Gam,
    HeapCorr G Gam -> NoDup ws -> (forall w, In w ws -> G w = None) ->
    HeapCorr (hupd_list G ws (map (fun _ => GExpr EFree) ws))
             (hupd_list Gam ws (map (fun w => BExpr (EVar w)) ws)).
Proof.
  induction ws as [| w ws' IHws]; intros G Gam HGC HND Hfresh; simpl.
  - exact HGC.
  - assert (HNDtl : NoDup ws') by (inversion HND; assumption).
    assert (Hwnotin : ~ In w ws') by (inversion HND; assumption).
    assert (Hfreshtl : forall w', In w' ws' -> G w' = None)
      by (intros w' Hin; apply Hfresh; right; exact Hin).
    assert (Hw : G w = None) by (apply Hfresh; left; reflexivity).
    assert (Hrec := IHws G Gam HGC HNDtl Hfreshtl).
    assert (HwFresh' : hupd_list G ws' (map (fun _ => GExpr EFree) ws') w = None).
    { rewrite hupd_list_notin; [exact Hw | exact Hwnotin]. }
    exact (HeapCorr_extend _ _ w EFree Hrec HwFresh').
Qed.

(* Companion to VarChase_transport_shorten/downgrade_evar: a location x
   that's CURRENTLY free (Gam x = EVar x, a self-loop) can never be an
   intermediate hop of ANY other location's achieved-chase witness --
   reaching x via VarChase would force the chase's OWN target to be EVar x
   itself (VarChase's functionality), never a Con-shaped value -- so
   updating x's Nat-heap slot (however, e.g. G_CaseConFree narrowing it to
   an achieved constructor) can never invalidate an EXISTING achieved
   witness for any other location. *)
Lemma VarChase_transport_free_to_con :
  forall Gam x, Gam x = Some (BExpr (EVar x)) ->
  forall p e, VarChase Gam p e ->
  forall c args, e = BExpr (ECon c args) ->
  forall gnew, VarChase (hupd Gam x gnew) p e.
Proof.
  intros Gam x Hself p e H.
  induction H as [w0 b0 Hb0 Hself0 | w0 w0' e0 Hw0 Hne Hrec IH];
    intros c args Heqe gnew.
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. congruence.
    + apply VChase_Here.
      * rewrite (hupd_neq Gam x gnew w0 Hnewx). exact Hb0.
      * intros w' Hcontra. exact (Hself0 w' Hcontra).
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. exfalso. apply Hne. congruence.
    + eapply VChase_Hop.
      * rewrite (hupd_neq Gam x gnew w0 Hnewx). exact Hw0.
      * exact Hne.
      * exact (IH c args Heqe gnew).
Qed.

(* HeapCorr's own analogue of HeapCorr_update_free (curry.v's base version,
   which only ever had to worry about plain CorrE): x's OLD content is
   free (never Fwd, never Con, so CorrE_update_nonfwd_noncon_other handles
   every OTHER location's disjunct-1 witness exactly as before), and x's
   OWN Nat-heap slot was a self-loop, so VarChase_transport_free_to_con
   handles every OTHER location's disjunct-2 witness too. *)
Lemma HeapCorr_update_free :
  forall G Gam x c args, HeapCorr G Gam -> G x = Some (GExpr EFree) ->
  HeapCorr (hupd G x (GExpr (ECon c args))) (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x c args HGam Hx.
  assert (Hgamx : Gam x = Some (BExpr (EVar x))).
  { assert (HGamx := HGam x). rewrite Hx in HGamx.
    destruct HGamx as [b [Hb HCE3]].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgxfwd _]]]]]].
    - destruct (CorrE_forced_shape G x b HCE) as
        [ [c0 [args0 [Hg1 Hb1]]]
        | [ [Hg1 Hb1]
          | [ [f1 [args1 [Hg1 Hb1]]]
            | [ [y1 [y2 [Hg1 Hb1]]]
              | [ [z1 [Hg1 Hb1]]
                | [ [Hg1 Hb1]
                  | [ [y1 [Hg1 Hb1]]
                    | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
        rewrite Hx in Hg1; try discriminate Hg1.
      subst b. exact Hb.
    - rewrite Hx in Hgxfwd. discriminate Hgxfwd. }
  intro p.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. unfold hupd; rewrite Nat.eqb_refl.
    exists (BExpr (ECon c args)). split; [reflexivity | ].
    left. eapply CorrE_Con. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
  - rewrite (hupd_neq G x (GExpr (ECon c args)) p Hnepx).
    specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp;
      [ | rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx); exact HGam].
    destruct HGam as [b [Hb HCE3]].
    rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx).
    exists b. split; [exact Hb | ].
    assert (Hxnonfwd : forall w, G x <> Some (GFwd w))
      by (intros w Heq; rewrite Hx in Heq; discriminate Heq).
    assert (Hxnoncon : forall c' args', G x <> Some (GExpr (ECon c' args')))
      by (intros c' args' Heq; rewrite Hx in Heq; discriminate Heq).
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. exact (CorrE_update_nonfwd_noncon_other G p b HCE x (GExpr (ECon c args)) Hxnonfwd Hxnoncon Hnepx).
    + right. exists y1, z1, c1, args1.
      assert (Hz1x : z1 <> x) by (intro Heq; subst z1; exact (Hxnoncon c1 args1 Hz1)).
      split; [rewrite (hupd_neq G x (GExpr (ECon c args)) p Hnepx); exact Hgp | ].
      split; [exact (ContractLoc_update_nonfwd_other G y1 z1 Hcl1 x (GExpr (ECon c args)) Hxnonfwd Hz1x) | ].
      split; [rewrite (hupd_neq G x (GExpr (ECon c args)) z1 Hz1x); exact Hz1 | ].
      exact (VarChase_transport_free_to_con Gam x Hgamx p (BExpr (ECon c1 args1)) HVC c1 args1 eq_refl
               (BExpr (ECon c args))).
Qed.

(* NoVarThunk: no graph location directly holds a bare EVar (a "var-thunk",
   arising only from evaluating a BLet whose right-hand side is itself a
   bare variable -- G_Let is the ONLY GEval rule that ever stores an
   arbitrary literal Expr0 into the graph; G_Var, by contrast, evaluates a
   bare-EVar EXPRESSION and produces GFwd, never GExpr(EVar _), and no
   other rule's hupd ever writes anything but GFwd/ECon/EBot/EFree
   directly).  So this is exactly the invariant a compiler pass that
   eliminates `let x = y in e` (substituting y for x) establishes and
   preserves for the whole program -- see THEOREM2_PROCESS_NOTES.md for
   the worked argument (every GEval constructor checked) and the concrete
   counterexample motivating it (a var-thunk reached via a Nat-heap
   "skip-ahead" alias, which CorrE3's own graph-only reasoning has no way
   to certify).  Threaded here as a standing hypothesis, exactly like
   WellFoundedFwd already is elsewhere in this file, rather than derived
   from a source-level well-formedness predicate within this proof. *)
Definition NoVarThunk (G : Graph) : Prop :=
  forall x z, G x <> Some (GExpr (EVar z)).

(* Under NoVarThunk, ANY location whose Gam-witness is a lazy alias to some
   OTHER location (y <> x) is forced to be a genuine graph-level forward
   node -- regardless of which CorrE3 disjunct happens to justify it.  Two
   sub-cases, kept SEPARATE (not collapsed) because they carry genuinely
   different information: if plain CorrE (via CorrE_FwdHere, the only
   CorrE shape matching an EVar witness once CorrE_VarThunk is excluded by
   NoVarThunk and CorrE_Free is excluded by y<>x) is what justifies it,
   x's graph target is EXACTLY y (matching the Nat-heap alias); if it's
   CorrE3's own second disjunct instead, x's graph target could be a
   DIFFERENT location entirely (the "skip-ahead" case), but that disjunct
   hands over a complete achieved-witness for whatever it does target. *)
Lemma HeapCorr_alias_shape :
  forall G Gam, HeapCorr G Gam -> NoVarThunk G ->
  forall x y, Gam x = Some (BExpr (EVar y)) -> y <> x ->
  G x = Some (GFwd y) \/
  (exists y0 ytgt c args, G x = Some (GFwd y0) /\ ContractLoc G y0 ytgt /\
     G ytgt = Some (GExpr (ECon c args)) /\ VarChase Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam HGam HNVT x y Hgamx Hyx.
  assert (Hx := HGam x).
  destruct (G x) as [gx | ] eqn:EGx.
  - destruct Hx as [b [Hb HCE3]].
    rewrite Hgamx in Hb. injection Hb as Hb. subst b.
    destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
    + left.
      destruct (CorrE_forced_shape G x (BExpr (EVar y)) HCE) as
        [ [c0 [args0 [Hg1 Hb1]]]
        | [ [Hg2 Hb2]
          | [ [f0 [args0 [Hg3 Hb3]]]
            | [ [y1 [y2 [Hg4 Hb4]]]
              | [ [z0 [Hg5 Hb5]]
                | [ [Hg6 Hb6]
                  | [ [y0 [Hg7 Hb7]]
                    | [y0 [z0 [c0 [args0 [Hg8 [Hcl8 [Hz8 Hb8]]]]]]] ] ] ] ] ] ] ].
      * discriminate Hb1.
      * exfalso. injection Hb2 as Hb2. exact (Hyx Hb2).
      * discriminate Hb3.
      * discriminate Hb4.
      * exfalso. injection Hb5 as Hb5. subst z0.
        exact (HNVT x y Hg5).
      * discriminate Hb6.
      * injection Hb7 as Hb7. subst y0. rewrite EGx in Hg7. exact Hg7.
      * discriminate Hb8.
    + right. exists yd, zd, cd, argsd.
      rewrite EGx in Hgxfwd.
      repeat split; assumption.
  - rewrite Hgamx in Hx. discriminate Hx.
Qed.

(* The VarChase-to-NEval_left conversion, now carrying its own HeapCorr
   preservation AND a graph-side achievement witness throughout, so it can
   be used at ANY hop of a chase (not just a chase's own starting point)
   without a separate lemma to re-establish either fact afterward.  The
   graph-side witness is derived FRESH at each step from HeapCorr_alias_shape
   (using NoVarThunk): if the Nat-heap hop is justified by plain CorrE
   (CorrE_FwdHere), it matches the IH's own achievement witness for the
   NEXT hop exactly (same location); if it's CorrE3's own shortcut
   disjunct instead, that disjunct hands over an INDEPENDENT achievement
   witness (possibly a different graph location entirely), reconciled with
   the target via VarChase_functional inside HeapCorr_update_achieved. *)
Lemma NEval_left_frozen_at :
  forall x ex, (forall c args, ex <> BExpr (ECon c args)) -> ex <> BExpr (EVar x) -> ex <> BExpr EFree ->
  forall P F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  In x F ->
  Gam x = Some ex ->
  Gam' x = Some ex.
Proof.
  intros x ex Hex1 Hex2 Hex3 P F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e1 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e1 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HxF Hgx.
  - assert (Hzx : z <> x).
    { intro Heq; subst z. assert (Hexeq : ex = BExpr (ECon c0 args0)) by congruence. exact (Hex1 c0 args0 Hexeq). }
    exact Hgx.
  - assert (Hzx : z <> x).
    { intro Heq; subst z. assert (Hexeq : ex = BExpr (EVar x)) by congruence. exact (Hex2 Hexeq). }
    exact Hgx.
  - assert (Hzx : z <> x).
    { intro Heq; subst z. assert (Hexeq : ex = BExpr EFree) by congruence. exact (Hex3 Hexeq). }
    rewrite (hupd_neq G z (BExpr (EVar z)) x (not_eq_sym Hzx)). exact Hgx.
  - destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z. exfalso. exact (HzF HxF).
    + assert (HxF' : In x (z :: F0)) by (right; exact HxF).
      rewrite (hupd_neq G1 z v0 x (not_eq_sym Hnezx)). exact (IH HxF' Hgx).
  - exact Hgx.
  - exact Hgx.
  - exact (IH HxF Hgx).
  - assert (Hzx : z <> x) by (intro Heq; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Hgx2 : hupd G z (let_content z e1) x = Some ex)
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    exact (IH HxF Hgx2).
  - exact (IH HxF Hgx).
  - exact (IH2 HxF (IH1 HxF Hgx)).
  - assert (HG1x := IH1 HxF Hgx).
    assert (Hxz' : x <> z').
    { intro Heq; subst x. assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
        by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
      rewrite HG1z' in HG1x. injection HG1x as HG1x. exact (Hex2 (eq_sym HG1x)). }
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). rewrite Hfr in HG1x. discriminate HG1x. }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x
                     = Some ex).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact HG1x. }
    exact (IH2 HxF Hgx3).
Qed.

Lemma VarChaseN_to_NEval_left :
  forall P G Gam, HeapCorr G Gam -> NoVarThunk G ->
  forall n w c args, VarChaseN Gam n w (BExpr (ECon c args)) ->
  forall F, (forall z, In z F -> exists nz, VarChaseN Gam nz z (BExpr (ECon c args)) /\ n < nz) ->
  exists Gam' ytgt, NEval_left P F Gam (BExpr (EVar w)) Gam' (BExpr (ECon c args)) /\
    HeapCorr G Gam' /\ ContractLoc G w ytgt /\ G ytgt = Some (GExpr (ECon c args)).
Proof.
  intros P G Gam HGam HNVT n w c args H.
  remember (BExpr (ECon c args)) as target eqn:Htarget.
  revert c args Htarget.
  induction H as [w0 b0 Hb0 Hself | n0 w0 w0' e0 Hw0 Hne Hrec IH]; intros c args Htarget F Hdisj.
  - subst b0.
    assert (Hach : exists ytgt, ContractLoc G w0 ytgt /\ G ytgt = Some (GExpr (ECon c args))).
    { assert (Hx := HGam w0).
      destruct (G w0) as [gw0 | ] eqn:EGw0.
      - destruct Hx as [b [Hb HCE3]].
        rewrite Hb0 in Hb. injection Hb as Hb. subst b.
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        + destruct (CorrE_forced_shape G w0 (BExpr (ECon c args)) HCE) as
            [ [c0 [args0 [Hg1 Hb1]]]
            | [ [Hg2 Hb2]
              | [ [f0 [args0 [Hg3 Hb3]]]
                | [ [y1 [y2 [Hg4 Hb4]]]
                  | [ [z0 [Hg5 Hb5]]
                    | [ [Hg6 Hb6]
                      | [ [y0 [Hg7 Hb7]]
                        | [y0 [z0 [c0 [args0 [Hg8 [Hcl8 [Hz8 Hb8]]]]]]] ] ] ] ] ] ] ].
          * injection Hb1 as Hb1a Hb1b. subst c0 args0.
            exists w0. split; [eapply CL_Here; exact Hg1 | exact Hg1].
          * discriminate Hb2.
          * discriminate Hb3.
          * discriminate Hb4.
          * discriminate Hb5.
          * discriminate Hb6.
          * discriminate Hb7.
          * exists z0. injection Hb8 as Hb8a Hb8b. subst c0 args0.
            split; [eapply CL_Fwd; [exact Hg8 | exact Hcl8] | exact Hz8].
        + assert (Heqcd : cd = c /\ argsd = args).
          { assert (Heq := VarChase_functional Gam w0 (BExpr (ECon cd argsd)) (BExpr (ECon c args)) HVCd
                             (VChase_Here Gam w0 (BExpr (ECon c args)) Hb0 Hself)).
            injection Heq as Heq1 Heq2. split; assumption. }
          destruct Heqcd as [Heqcd Heqargsd]. subst cd argsd.
          exists zd. split; [eapply CL_Fwd; [exact Hgxfwd | exact Hcld] | exact Hzd].
      - rewrite Hb0 in Hx. discriminate Hx. }
    destruct Hach as [ytgt [Hclytgt Hgytgt]].
    exists Gam, ytgt. split; [apply NL_VarCons; exact Hb0 | split; [exact HGam | split; [exact Hclytgt | exact Hgytgt]]].
  - subst e0.
    assert (Hthis : VarChaseN Gam (S n0) w0 (BExpr (ECon c args)))
      by (eapply VChaseN_Hop; eassumption).
    assert (Hw0F : ~ In w0 F).
    { intro Hin. destruct (Hdisj w0 Hin) as [nz [Hvcn Hlt]].
      assert (Heq := VarChaseN_functional Gam (S n0) nz w0 (BExpr (ECon c args)) Hthis Hvcn).
      lia. }
    assert (Hdisj' : forall z, In z (w0 :: F) ->
              exists nz, VarChaseN Gam nz z (BExpr (ECon c args)) /\ n0 < nz).
    { intros z Hin. destruct Hin as [Heq | Hin].
      - subst z. exists (S n0). split; [exact Hthis | lia].
      - destruct (Hdisj z Hin) as [nz [Hvcn Hlt]]. exists nz. split; [exact Hvcn | lia]. }
    destruct (IH c args eq_refl (w0 :: F) Hdisj') as [Gam1 [ytgt1 [HNE [HHC1 [Hcl1 Hg1]]]]].
    assert (Hgamw0' : Gam1 w0' = Some (BExpr (ECon c args)))
      by (eapply NEval_left_own_slot; exact HNE).
    assert (Hw0F' : ~ In w0 F) by exact Hw0F.
    assert (Hex1 : forall c' args', BExpr (EVar w0') <> BExpr (ECon c' args'))
      by (intros c' args' Hcontra; discriminate Hcontra).
    assert (Hex2 : BExpr (EVar w0') <> BExpr (EVar w0))
      by (intro Hcontra; injection Hcontra as Hcontra; exact (Hne Hcontra)).
    assert (Hex3 : BExpr (EVar w0') <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
    assert (Hgamw0 : Gam1 w0 = Some (BExpr (EVar w0'))).
    { eapply NEval_left_frozen_at.
      - exact Hex1.
      - exact Hex2.
      - exact Hex3.
      - exact HNE.
      - left; reflexivity.
      - exact Hw0. }
    assert (Hchase_w0 : VarChase Gam1 w0 (BExpr (ECon c args))).
    { eapply VChase_Hop.
      - exact Hgamw0.
      - exact Hne.
      - apply VChase_Here.
        + exact Hgamw0'.
        + intros w' Hcontra; discriminate Hcontra. }
    destruct (HeapCorr_alias_shape G Gam HGam HNVT w0 w0' Hw0 Hne) as
      [ Hmatch | [yd [ytgtd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
    + exists (hupd Gam1 w0 (BExpr (ECon c args))), ytgt1.
      split.
      * eapply NL_VarExp; [exact Hw0F | exact Hw0 | intros c' args' Hcontra; discriminate Hcontra
        | intro Hcontra; injection Hcontra as Hcontra; exact (Hne Hcontra)
        | intro Hcontra; discriminate Hcontra | exact HNE].
      * split; [ | split].
        -- eapply HeapCorr_update_achieved; [exact HHC1 | exact Hmatch | exact Hcl1 | exact Hg1 | exact Hchase_w0].
        -- eapply CL_Fwd; [exact Hmatch | exact Hcl1].
        -- exact Hg1.
    + assert (Hchase_w0_orig : VarChase Gam w0 (BExpr (ECon c args))).
      { eapply VChase_Hop; [exact Hw0 | exact Hne | exact (VarChaseN_to_VarChase Gam n0 w0' (BExpr (ECon c args)) Hrec)]. }
      assert (Heqcd : cd = c /\ argsd = args).
      { assert (Heq := VarChase_functional Gam w0 (BExpr (ECon cd argsd)) (BExpr (ECon c args)) HVCd Hchase_w0_orig).
        injection Heq as Heq1 Heq2. split; assumption. }
      destruct Heqcd as [Heqcd Heqargsd]. subst cd argsd.
      exists (hupd Gam1 w0 (BExpr (ECon c args))), ytgtd.
      split.
      * eapply NL_VarExp; [exact Hw0F | exact Hw0 | intros c' args' Hcontra; discriminate Hcontra
        | intro Hcontra; injection Hcontra as Hcontra; exact (Hne Hcontra)
        | intro Hcontra; discriminate Hcontra | exact HNE].
      * split; [ | split].
        -- eapply HeapCorr_update_achieved; [exact HHC1 | exact Hgxfwd | exact Hcld | exact Hzd | exact Hchase_w0].
        -- eapply CL_Fwd; [exact Hgxfwd | exact Hcld].
        -- exact Hzd.
Qed.

(* force_var_N: the HeapCorr (new) analogue of force_var_N_left, built by
   well-founded induction on GRAPH distance exactly like the HeapCorr2
   version, but with an extra case at every step: CorrE3's own shortcut
   disjunct, handled by handing off to VarChaseN_to_NEval_left.  GamChainTo
   Gam F x / NoDup (x::F) are threaded alongside the existing graph-distance
   guard invariant specifically so that shortcut hand-off has a matching
   VarChaseN-distance-based guard-freshness certificate available for F,
   via GamChainTo_prepend_VarChaseN, without which the shortcut's own
   internal chase could not be shown to avoid revisiting anything already
   in F. *)
Lemma force_var_N :
  forall P n G x y, ContractLocN G n x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr G Gam -> NoVarThunk G ->
  forall F, (forall z, In z F -> exists nz, ContractLocN G nz z y /\ n < nz) ->
  GamChainTo Gam F x -> NoDup (x :: F) ->
  exists Gam', NEval_left P F Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr G Gam'.
Proof.
  intros P.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros G x y Hcln c args Hy Gam HGam HNVT F Hdisj Hchain Hnodup.
  assert (HxF : ~ In x F).
  { intro Hin. destruct (Hdisj x Hin) as [nz [Hclnz Hgt]].
    destruct (ContractLocN_functional G n x y Hcln nz y Hclnz) as [Heqn _].
    lia. }
  destruct n as [| n0].
  - assert (Hyx : y = x) by (eapply ContractLocN_zero; eauto). subst y.
    assert (Hx := HGam x). rewrite Hy in Hx.
    destruct Hx as [b [Hb HCE3]].
    assert (Hbeq : b = BExpr (ECon c args)).
    { destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd _]]]]]].
      - eapply CorrE_from_con; [exact Hy | exact HCE].
      - rewrite Hy in Hgxfwd. discriminate Hgxfwd. }
    subst b.
    exists Gam. split; [apply NL_VarCons; exact Hb | exact HGam].
  - destruct (ContractLocN_succ G n0 x y Hcln) as [y0 [Hxy0 Hcln0]].
    assert (HGamx := HGam x).
    assert (HGx : G x <> None) by congruence.
    destruct (G x) eqn:GX; [clear HGx | congruence].
    injection Hxy0 as Hxy0; subst g.
    destruct HGamx as [b [Hb HCE3]].
    destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
    + (* disjunct 1: bare CorrE, mirrors force_var_N_left's own logic *)
      assert (Hprog := CorrE_con_progress_N G x b HCE (S n0) y c args Hcln Hy).
      destruct Hprog as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
      * subst b. exists Gam. split; [apply NL_VarCons; exact Hb | exact HGam].
      * subst b.
        assert (Hy1x : y1 <> x).
        { intro Heq; subst y1.
          destruct (ContractLocN_functional G m x y Hcln1 (S n0) y Hcln) as [Hmn _].
          lia. }
        assert (Hy1y0 : y1 = y0) by (eapply CorrE_evar_shape_for_fwd; [rewrite GX; reflexivity | exact HCE]).
        subst y1.
        assert (Hdisj' : forall z, In z (x :: F) -> exists nz, ContractLocN G nz z y /\ m < nz).
        { intros z Hin.
          destruct Hin as [Heqz | Hin].
          - subst z. exists (S n0). split; [exact Hcln | exact Hm].
          - destruct (Hdisj z Hin) as [nz [Hclnz Hgt]]. exists nz. split; [exact Hclnz | lia]. }
        assert (Hy0F : ~ In y0 F).
        { intro Hin. destruct (Hdisj y0 Hin) as [nz [Hclnz Hgt]].
          destruct (ContractLocN_functional G n0 y0 y Hcln0 nz y Hclnz) as [Heqn0 _].
          lia. }
        assert (Hchain' : GamChainTo Gam (x :: F) y0) by (split; [exact Hb | exact Hchain]).
        assert (Hnodup' : NoDup (y0 :: x :: F)).
        { apply NoDup_cons.
          - intro Hin. destruct Hin as [Heq0 | Hin].
            + exact (Hy1x (eq_sym Heq0)).
            + exact (Hy0F Hin).
          - exact Hnodup. }
        destruct (IHn m Hm G y0 y Hcln1 c args Hy Gam HGam HNVT (x :: F) Hdisj' Hchain' Hnodup')
          as [Gam1 [HNE HHC1]].
        assert (Hgamy0 : Gam1 y0 = Some (BExpr (ECon c args)))
          by (eapply NEval_left_own_slot; exact HNE).
        assert (Hgamx1 : Gam1 x = Some (BExpr (EVar y0))).
        { eapply NEval_left_frozen_at.
          - intros c' args' Hcontra; discriminate Hcontra.
          - intro Hcontra; injection Hcontra as Hcontra'; exact (Hy1x Hcontra').
          - intro Hcontra; discriminate Hcontra.
          - exact HNE.
          - left; reflexivity.
          - exact Hb. }
        assert (Hchase_x : VarChase Gam1 x (BExpr (ECon c args))).
        { eapply VChase_Hop.
          - exact Hgamx1.
          - exact Hy1x.
          - apply VChase_Here; [exact Hgamy0 | intros w' Hcontra; discriminate Hcontra]. }
        exists (hupd Gam1 x (BExpr (ECon c args))).
        split.
        -- eapply NL_VarExp.
           ++ exact HxF.
           ++ exact Hb.
           ++ intros c' args' Hcontra; discriminate Hcontra.
           ++ intro Hcontra; injection Hcontra as Hcontra'; exact (Hy1x Hcontra').
           ++ intro Hcontra; discriminate Hcontra.
           ++ exact HNE.
        -- eapply HeapCorr_update_achieved.
           ++ exact HHC1.
           ++ rewrite GX. reflexivity.
           ++ exact (ContractLocN_to_ContractLoc G n0 y0 y Hcln0).
           ++ exact Hy.
           ++ exact Hchase_x.
    + (* disjunct 2: CorrE3's own shortcut, hand off to VarChaseN_to_NEval_left *)
      assert (Hydeq : yd = y0) by (rewrite GX in Hgxfwd; injection Hgxfwd as Hgxfwd; exact (eq_sym Hgxfwd)).
      subst yd.
      assert (Hzdeq : zd = y)
        by (eapply ContractLoc_functional; [exact Hcld | exact (ContractLocN_to_ContractLoc G n0 y0 y Hcln0)]).
      subst zd.
      assert (Heqcd : cd = c /\ argsd = args)
        by (rewrite Hy in Hzd; injection Hzd as Hzd1 Hzd2; split; [exact (eq_sym Hzd1) | exact (eq_sym Hzd2)]).
      destruct Heqcd as [Heqcd Heqargsd]. subst cd argsd.
      destruct (VarChase_to_VarChaseN Gam x (BExpr (ECon c args)) HVCd) as [nvc Hvcn].
      assert (Hdisj_vc : forall z, In z F -> exists nz, VarChaseN Gam nz z (BExpr (ECon c args)) /\ nvc < nz).
      { exact (GamChainTo_prepend_VarChaseN Gam F x Hchain Hnodup nvc (BExpr (ECon c args)) Hvcn). }
      destruct (VarChaseN_to_NEval_left P G Gam HGam HNVT nvc x c args Hvcn F Hdisj_vc)
        as [Gam' [ytgt' [HNE [HHC' [Hclytgt' Hgytgt']]]]].
      exists Gam'. split; [exact HNE | exact HHC'].
Qed.

(* Top-level wrapper, mirroring force_var_left's own: nil guard, nil chain. *)
Lemma force_var :
  forall P G x y, ContractLoc G x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr G Gam -> NoVarThunk G ->
  exists Gam', NEval_left P nil Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr G Gam'.
Proof.
  intros P G x y H c args Hy Gam HGam HNVT.
  destruct (ContractLoc_to_N G x y H) as [n Hn].
  apply (force_var_N P n G x y Hn c args Hy Gam HGam HNVT nil).
  - intros z Hin; destruct Hin.
  - exact I.
  - apply NoDup_cons; [intro Hin; destruct Hin | apply NoDup_nil].
Qed.

(* Nat-Guess analogue of NEval_left_fwd_transfer_fwdhere_con: x aliases y
   (the only possibility for a Fwd-y node when y turns out to be free --
   there is deliberately no "FwdAchievedFree" shortcut, per curry.v's own
   comment), and forcing y reaches a free-variable self-loop x' rather than
   a constructor.  Two sub-cases, matching evar_shape's own split on the
   "forcing y" derivation:
   - x' = y directly (y itself is free, reached via NL_VarSelf/NL_VarFree,
     which don't check the guard at all): x's own alias EVar y IS ALREADY
     EVar x', so forcing x lands on the exact same heap (up to the trivial
     x:=EVar y no-op), and Hrec2 transfers via plain pointwise equality --
     no promotion/shortcut machinery needed at all.
   - x' <> y (y itself forwards further, through more aliases, before
     reaching x'): forcing x (via NL_VarExp) is forced to memoize x directly
     to EVar x' (skipping y) -- this is sound (both x and y still chase, via
     pure Nat-heap aliasing, to whatever x' eventually achieves) but is NOT
     a shape plain CorrE/HeapCorr2 can certify (see HeapCorr's own comment
     above) -- so the conclusion here is HeapCorr, not HeapCorr2.  The
     extra "x' <> y -> ContractLoc G1 y x'" hypothesis pins down the ONE
     graph fact this purely Nat-heap-side lemma cannot itself derive: that
     y's own graph-level forward chain (however many GFwd hops -- G_CaseFun/
     G_CaseFwd never re-compress an intermediate hop, so this is genuinely
     multi-hop in general, NOT a single edge) terminates at x'.  True by the
     theorem's own overall correspondence, but out of reach without the
     GEval-side half of it, so it is taken as a hypothesis here rather than
     re-derived.  Vacuous whenever x' = y, so it costs the other three
     branches nothing. *)
Lemma NEval_left_fwd_transfer_fwdhere_free :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) -> x <> y ->
  Gam x = Some (BExpr (EVar y)) ->
  forall brs x' c1 ys1 body1 ws Gmid Gam' v',
    NEval_left P nil Gam (BExpr (EVar y)) Gmid (BExpr (EVar x')) ->
    hd_error brs = Some (c1, ys1, body1) -> length ws = length ys1 -> NoDup ws ->
    (forall w, In w ws -> Gmid w = None) ->
    NEval_left P nil (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
               (rename_b (zipsubst ys1 ws) body1) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) ->
                  (x' <> y -> ContractLoc G1 y x') ->
                  HeapCorr2 G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hxy Hb brs x' c1 ys1 body1 ws Gmid Gam' v' Hrec1 Hhd Hlen HND Hfr Hrec2.
  destruct (NEval_left_evar_shape P nil Gam y Gmid (BExpr (EVar x')) Hrec1) as
    [ [Hcase1 [HeqGmid [c'' [args'' Heqv]]]]
    | [ [Hcase2 [HeqGmid Heqv]]
      | [ [Hcase3 [HeqGmid Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ].
  - discriminate Heqv.
  - (* VarSelf: Gam y = EVar y, x' = y, Gmid = Gam *)
    injection Heqv as Heqx'. subst x'. subst Gmid.
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam x (BExpr (EVar y))) (BExpr (EVar y))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - apply NL_VarSelf. exact Hcase2. }
    assert (Heq : forall w, hupd_list (hupd (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                    (map (fun w => BExpr (EVar w)) ws) w
                  = hupd_list (hupd Gam y (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) w).
    { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
      - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
        rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
      - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        + rewrite (hupd_neq (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          rewrite (hupd_neq Gam y (BExpr (ECon c1 ws)) w Hnewy).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          * subst w. unfold hupd; rewrite Nat.eqb_refl. exact (eq_sym Hb).
          * rewrite (hupd_neq Gam x (BExpr (EVar y)) w Hnewx). reflexivity. }
    destruct (NEval_left_pointwise_heap P nil
                (hupd_list (hupd Gam y (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                (hupd_list (hupd (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                Heq)
      as [Gam2 [HNE2 HeqGam2]].
    exists Gam2. split.
    + eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
      intros w Hin.
      assert (Hwx : x <> w) by (intro Heqxw; subst w; rewrite (Hfr x Hin) in Hb; discriminate Hb).
      rewrite (hupd_neq Gam x (BExpr (EVar y)) w (not_eq_sym Hwx)). exact (Hfr w Hin).
    + intros G1v HG1x Hxfwd HHC2.
      apply HeapCorr2_to_HeapCorr. eapply HeapCorr2_pointwise; [exact HHC2 | exact HeqGam2].
  - (* VarFree: Gam y = Free, x' = y, Gmid = hupd Gam y (EVar y) *)
    injection Heqv as Heqx'. subst x'. subst Gmid.
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x))
               (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) (BExpr (EVar y))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - apply NL_VarFree. exact Hcase3. }
    assert (Heq : forall w,
              hupd_list (hupd (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                (map (fun w => BExpr (EVar w)) ws) w
              = hupd_list (hupd (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                (map (fun w => BExpr (EVar w)) ws) w).
    { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
      - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
        rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
      - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        + rewrite (hupd_neq (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          * subst w.
            assert (HLHS : (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) x = Some (BExpr (EVar y)))
              by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
            rewrite HLHS. rewrite (hupd_neq Gam y (BExpr (EVar y)) x Hxy). exact (eq_sym Hb).
          * rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y)) w Hnewx). reflexivity. }
    destruct (NEval_left_pointwise_heap P nil
                (hupd_list (hupd (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                (hupd_list
                   (hupd (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                Heq)
      as [Gam2 [HNE2 HeqGam2]].
    exists Gam2. split.
    + eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
      intros w Hin.
      assert (Hwy : y <> w).
      { intro Heqyw; subst w. assert (Hfry := Hfr y Hin).
        assert (Hyy : (hupd Gam y (BExpr (EVar y))) y = Some (BExpr (EVar y)))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        rewrite Hyy in Hfry. discriminate Hfry. }
      assert (Hwx : x <> w).
      { intro Heqxw; subst w.
        assert (Hfrx := Hfr x Hin). rewrite (hupd_neq Gam y (BExpr (EVar y)) x Hxy) in Hfrx.
        rewrite Hfrx in Hb. discriminate Hb. }
      rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y)) w (not_eq_sym Hwx)).
      rewrite (hupd_neq Gam y (BExpr (EVar y)) w (not_eq_sym Hwy)).
      assert (Hfrw := Hfr w Hin). rewrite (hupd_neq Gam y (BExpr (EVar y)) w (not_eq_sym Hwy)) in Hfrw.
      exact Hfrw.
    + intros G1v HG1x Hxfwd HHC2.
      apply HeapCorr2_to_HeapCorr. eapply HeapCorr2_pointwise; [exact HHC2 | exact HeqGam2].
  - (* VarExp: y's own content e0 needs further forcing (guard [y]),
       reaching x'.  KEY INSIGHT (from working through why z can't just be
       "still free and untouched"): Hrec2's own starting heap already shows
       y ALIASING x' (not x' being some independent, unrelated location) --
       and, once x' gets narrowed, y's own alias becomes a genuine "y aliases
       an ACHIEVED constructor" situation, valid for shortcut_alias directly.
       So we promote in two stages: first y (aliasing x', now achieved),
       then x (aliasing y, now ALSO achieved) -- both via the EXISTING
       shortcut_alias, no new "re-point an alias" machinery needed at all. *)
    assert (Hgmidx : Gmid x = Some (BExpr (EVar y)))
      by exact (NEval_left_alias_persists_through_force P x y Hxy Gam Gmid (BExpr (EVar x')) Hrec1 Hb).
    assert (Hxnotinws : ~ In x ws).
    { intro Hin. assert (Hfrx := Hfr x Hin). rewrite Hgmidx in Hfrx. discriminate Hfrx. }
    assert (Hgmidx' : Gmid x' = Some (BExpr (EVar x')))
      by exact (NEval_left_selfloop_result_persists P nil Gam (BExpr (EVar y)) Gmid x' Hrec1).
    assert (Hx'notinws : ~ In x' ws).
    { intro Hin. assert (Hfrx' := Hfr x' Hin). rewrite Hgmidx' in Hfrx'. discriminate Hfrx'. }
    assert (HforceY := NEval_left_alias_weaken_force_y P x y Hxy Gam Gmid (BExpr (EVar x')) Hrec1 Hb).
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gmid x (BExpr (EVar x'))) (BExpr (EVar x'))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - exact HforceY. }
    destruct (Nat.eq_dec x' y) as [Heqx'y | Hnex'y].
    + (* x' = y: y's own alias-chain loops back to itself.  Narrowing x'(=y)
         narrows y DIRECTLY, and HforceX's own output already has x = EVar y
         (matching x' = y) -- so this is really the SAME shape as the
         VarSelf/VarFree cases above: plain pointwise equality, no promotion
         (shortcut_alias) needed at all. *)
      subst x'.
      assert (Heq : forall w,
                hupd_list (hupd (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                  (map (fun w0 => BExpr (EVar w0)) ws) w
                = hupd_list (hupd Gmid y (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
      { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
        - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
          rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
        - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
          + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          + rewrite (hupd_neq (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
            rewrite (hupd_neq Gmid y (BExpr (ECon c1 ws)) w Hnewy).
            destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
            * subst w. unfold hupd; rewrite Nat.eqb_refl. exact (eq_sym Hgmidx).
            * rewrite (hupd_neq Gmid x (BExpr (EVar y)) w Hnewx). reflexivity. }
      destruct (NEval_left_pointwise_heap P nil
                  (hupd_list (hupd Gmid y (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (hupd_list (hupd (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                     (map (fun w0 => BExpr (EVar w0)) ws))
                  Heq) as [Gam2 [HNE2 HeqGam2]].
      exists Gam2. split.
      * eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
        intros w Hin.
        assert (Hwx : x <> w).
        { intro Heqxw; subst w. assert (Hfrw := Hfr x Hin). rewrite Hgmidx in Hfrw. discriminate Hfrw. }
        rewrite (hupd_neq Gmid x (BExpr (EVar y)) w (not_eq_sym Hwx)). exact (Hfr w Hin).
      * intros G1v HG1x Hxfwd HHC2.
        apply HeapCorr2_to_HeapCorr. eapply HeapCorr2_pointwise; [exact HHC2 | exact HeqGam2].
    + (* x' <> y: y forwards through ANOTHER alias before reaching x'.
         Promote y (aliasing x', now achieved) then x (aliasing y, now also
         achieved) via shortcut_alias, twice.  Then DEMOTE back down via the
         downgrade lemma (shortcut_alias_relax), twice, to match the raw shape
         NL_Guess's own third premise structurally needs (built from
         HforceX's output, x aliasing x' directly -- and, since demoting can
         re-memoize a demoted location if the replayed derivation reads it
         again, y ALSO needs demoting a second time to undo the artifact of
         its own earlier promotion).  Finally, re-promote x and y ONE more
         time -- now directly against the TARGET heap's own KNOWN (not
         disjunctive) x'/y values -- to land on a clean, non-disjunctive
         result heap, and separately re-derive that SAME clean heap's
         HeapCorr2 directly from HeapCorr2 G1 Gam' via HeapCorr2_update_achieved,
         using the new "G1's y is never a bare var-thunk" hypothesis to rule
         out the one CorrE reading (CorrE_VarThunk) that would make this
         unsound. *)
      assert (Hgmidy : Gmid y = Some (BExpr (EVar x')))
        by (rewrite HeqGmid; unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hynotinws : ~ In y ws).
      { intro Hin. assert (Hfry := Hfr y Hin). rewrite Hgmidy in Hfry. discriminate Hfry. }
      assert (Hxx' : x <> x') by (intro Heq; subst x'; congruence).
      assert (Hy_in : hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                    = Some (BExpr (EVar x'))).
      { rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ y Hynotinws).
        rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)). exact Hgmidy. }
      assert (Hx'_in : hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x'
                    = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x' Hx'notinws).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      destruct (NEval_left_alias_or_con_persists P y x' c1 ws (not_eq_sym Hnex'y) nil
                  (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (or_introl Hy_in) Hx'_in) as [Hgamy_disj Hgamx'_val].
      (* STEP 1: promote y *)
      destruct (NEval_left_shortcut_alias P y x' c1 ws (not_eq_sym Hnex'y) nil
                  (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (or_introl Hy_in) Hx'_in) as [Gamy' [HNEy' Heqy']].
      (* STEP 2: promote x *)
      assert (Hx_in : hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)) x
                    = Some (BExpr (EVar y))).
      { rewrite (hupd_neq _ y (BExpr (ECon c1 ws)) x Hxy).
        rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x Hxnotinws).
        rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) x Hxx'). exact Hgmidx. }
      assert (Hy_in2 : hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)) y
                    = Some (BExpr (ECon c1 ws)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      destruct (NEval_left_shortcut_alias P x y c1 ws Hxy nil
                  (hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)))
                  (rename_b (zipsubst ys1 ws) body1) Gamy' v' HNEy'
                  (or_introl Hx_in) Hy_in2) as [Gamx' [HNEx' Heqx'2]].
      set (Step1 := hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws))) in *.
      (* STEP 3: demote x back down to EVar x' *)
      assert (HxF_nil : ~ In x (@nil var)) by (intro Hin; destruct Hin).
      assert (Hx_hit : hupd Step1 x (BExpr (ECon c1 ws)) x = Some (BExpr (ECon c1 ws)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hx'_step1 : Step1 x' = Some (BExpr (ECon c1 ws))).
      { unfold Step1. rewrite (hupd_neq _ y (BExpr (ECon c1 ws)) x' Hnex'y).
        rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x' Hx'notinws).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      assert (Hx'_step1' : hupd Step1 x (BExpr (ECon c1 ws)) x' = Some (BExpr (ECon c1 ws)))
        by (rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) x' (not_eq_sym Hxx')); exact Hx'_step1).
      destruct (NEval_left_shortcut_alias_relax P x x' c1 ws Hxx' nil HxF_nil
                  (hupd Step1 x (BExpr (ECon c1 ws))) (rename_b (zipsubst ys1 ws) body1) Gamx' v' HNEx'
                  Hx_hit Hx'_step1') as [Gamx'' [HNEx'' [Hptwx'' _]]].
      (* STEP 4: demote y back down to EVar x' too *)
      assert (Hy_step2 : hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) y = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) y (not_eq_sym Hxy)).
        rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) y (not_eq_sym Hxy)).
        unfold Step1. unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      assert (Hx'_step2 : hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) x' = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) x' (not_eq_sym Hxx')).
        rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) x' (not_eq_sym Hxx')). exact Hx'_step1. }
      assert (HyF_nil : ~ In y (@nil var)) by (intro Hin; destruct Hin).
      destruct (NEval_left_shortcut_alias_relax P y x' c1 ws (not_eq_sym Hnex'y) nil HyF_nil
                  (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) (rename_b (zipsubst ys1 ws) body1) Gamx'' v' HNEx''
                  Hy_step2 Hx'_step2) as [Gamfinal [HNEfinal [Hptwfinal _]]].
      (* bridge to TARGET, the raw heap NL_Guess's own third premise needs *)
      assert (Hcong : forall w,
          hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
        = hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w).
      { intro w. destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        - subst w. unfold hupd at 3; rewrite Nat.eqb_refl.
          rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ y Hynotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)).
          rewrite (hupd_neq Gmid x (BExpr (EVar x')) y (not_eq_sym Hxy)).
          exact Hgmidy.
        - destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          + subst w.
            assert (HR : hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) x = Some (BExpr (EVar x'))).
            { rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) x Hxy).
              unfold hupd at 1; rewrite Nat.eqb_refl; reflexivity. }
            rewrite HR.
            rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotinws).
            rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) x Hxx').
            unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          + destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
            * rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
              assert (Hwy : w <> y) by (intro Heq; subst w; exact (Hynotinws Hin)).
              rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w Hwy).
              rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) w Hnewx).
              rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) w Hnewx).
              unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) w Hwy).
              rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
            * rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
              rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w Hnewy).
              rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) w Hnewx).
              rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) w Hnewx).
              destruct (Nat.eq_dec w x') as [Heqwx' | Hnewx'].
              -- subst w. unfold hupd; rewrite Nat.eqb_refl.
                 unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) x' Hnex'y).
                 rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x' Hx'notinws).
                 unfold hupd; rewrite Nat.eqb_refl; reflexivity.
              -- rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) w Hnewx').
                 rewrite (hupd_neq Gmid x (BExpr (EVar x')) w Hnewx).
                 unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) w Hnewy).
                 rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
                 rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) w Hnewx'). reflexivity. }
      destruct (NEval_left_pointwise_heap P nil
                  (hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')))
                  (rename_b (zipsubst ys1 ws) body1) Gamfinal v' HNEfinal
                  (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  Hcong)
        as [Gam2raw [HNEtarget Heq2raw]].
      (* away from {x, y}, Gamfinal (hence Gam2raw) matches Gam' exactly *)
      assert (Hfinal_away : forall w, w <> x -> w <> y -> Gamfinal w = Gam' w).
      { intros w Hwx Hwy. rewrite (Hptwfinal w Hwy). rewrite (Hptwx'' w Hwx).
        rewrite (Heqx'2 w). rewrite (hupd_neq Gamy' x (BExpr (ECon c1 ws)) w Hwx).
        rewrite (Heqy' w). rewrite (hupd_neq Gam' y (BExpr (ECon c1 ws)) w Hwy). reflexivity. }
      (* HNEtarget/Gam2raw is EXACTLY the raw derivation NL_Guess needs (its
         own starting heap already matches HforceX's own output) -- no
         further promotion is needed to supply the FIRST half of the
         existential.  What remains is the SECOND half: HeapCorr, not
         HeapCorr2, since x's own final witness may legitimately still be
         the compressed alias EVar x' rather than an achieved constructor
         (see HeapCorr's own comment above for why plain CorrE has no room
         for that shape here). *)
      exists Gam2raw. split.
      * eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNEtarget].
        intros w Hin.
        assert (Hwx : x <> w) by (intro Heqxw; subst w; exact (Hxnotinws Hin)).
        rewrite (hupd_neq Gmid x (BExpr (EVar x')) w (not_eq_sym Hwx)). exact (Hfr w Hin).
      * intros G1v HG1x Hxfwd HHC2.
        assert (Hcl_yx' : ContractLoc G1v y x') by exact (Hxfwd Hnex'y).
        destruct (ContractLoc_first_hop G1v y x' Hcl_yx' (not_eq_sym Hnex'y)) as [y0 [HG1y Hcl_y0x']].
        assert (HCEx' : CorrE G1v x' (BExpr (ECon c1 ws)))
          by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2) | exact Hgamx'_val]).
        destruct (CorrE_con_to_contractloc G1v x' c1 ws HCEx') as [wit [Hclwit Hgwit]].
        assert (Hcl_y : ContractLoc G1v y wit) by (eapply ContractLoc_trans; [exact Hcl_yx' | exact Hclwit]).
        assert (Hcl_y0 : ContractLoc G1v y0 wit) by (eapply ContractLoc_trans; [exact Hcl_y0x' | exact Hclwit]).
        assert (Hx'_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) x'
                       = Some (BExpr (ECon c1 ws))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x' Hx'notinws).
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        assert (Hgam2rawx' : Gam2raw x' = Some (BExpr (ECon c1 ws)))
          by exact (NEval_left_con_persists P nil
                      (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                      (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget x' c1 ws Hx'_tgt).
        assert (Hx_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) x
                       = Some (BExpr (EVar x'))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) x Hxx').
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        destruct (NEval_left_alias_or_con_persists P x x' c1 ws Hxx' nil
                    (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                    (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget
                    (or_introl Hx_tgt) Hx'_tgt) as [Hgam2rawx_disj _].
        assert (Hy_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) y
                       = Some (BExpr (EVar x'))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ y Hynotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)).
          rewrite (hupd_neq Gmid x (BExpr (EVar x')) y (not_eq_sym Hxy)). exact Hgmidy. }
        destruct (NEval_left_alias_or_con_persists P y x' c1 ws (not_eq_sym Hnex'y) nil
                    (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                    (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget
                    (or_introl Hy_tgt) Hx'_tgt) as [Hgam2rawy_disj _].
        assert (HVCy : VarChase Gam2raw y (BExpr (ECon c1 ws))).
        { destruct Hgam2rawy_disj as [Hya | Hyc].
          - eapply VChase_Hop; [exact Hya | exact Hnex'y | ].
            eapply VChase_Here; [exact Hgam2rawx' | intros w' Hcontra; discriminate Hcontra].
          - eapply VChase_Here; [exact Hyc | intros w' Hcontra; discriminate Hcontra]. }
        intro w0. destruct (G1v w0) as [gw0 | ] eqn:HGw0.
        -- destruct (Nat.eq_dec w0 x) as [Heqw0x | Hnew0x].
           ++ subst w0. destruct Hgam2rawx_disj as [Hxa | Hxc].
              ** exists (BExpr (EVar x')). split; [exact Hxa | ].
                 right. exists y, wit, c1, ws. split; [exact HG1x | split; [exact Hcl_y | split; [exact Hgwit | ]]].
                 eapply VChase_Hop; [exact Hxa | exact (not_eq_sym Hxx') | ].
                 eapply VChase_Here; [exact Hgam2rawx' | intros w' Hcontra; discriminate Hcontra].
              ** exists (BExpr (ECon c1 ws)). split; [exact Hxc | ].
                 left. eapply CorrE_FwdAchievedCon; [exact HG1x | exact Hcl_y | exact Hgwit].
           ++ destruct (Nat.eq_dec w0 y) as [Heqw0y | Hnew0y].
              ** subst w0. destruct Hgam2rawy_disj as [Hya | Hyc].
                 { exists (BExpr (EVar x')). split; [exact Hya | ].
                   right. exists y0, wit, c1, ws. split; [exact HG1y | split; [exact Hcl_y0 | split; [exact Hgwit | exact HVCy]]]. }
                 { exists (BExpr (ECon c1 ws)). split; [exact Hyc | ].
                   left. eapply CorrE_FwdAchievedCon; [exact HG1y | exact Hcl_y0 | exact Hgwit]. }
              ** assert (HGw0' : G1v w0 = Some gw0) by exact HGw0.
                 assert (HHCw0 := proj1 HHC2 w0). rewrite HGw0' in HHCw0.
                 destruct HHCw0 as [b [Hb' HCE]]. exists b. split.
                 { rewrite (Heq2raw w0). rewrite (Hfinal_away w0 Hnew0x Hnew0y). exact Hb'. }
                 { left. exact HCE. }
        -- destruct (Nat.eq_dec w0 x) as [Heqw0x | Hnew0x];
             [subst w0; rewrite HG1x in HGw0; discriminate HGw0 | ].
           destruct (Nat.eq_dec w0 y) as [Heqw0y | Hnew0y];
             [subst w0; rewrite HG1y in HGw0; discriminate HGw0 | ].
           assert (HGw0' : G1v w0 = None) by exact HGw0.
           assert (HHCw0 := proj1 HHC2 w0). rewrite HGw0' in HHCw0.
           rewrite (Heq2raw w0). rewrite (Hfinal_away w0 Hnew0x Hnew0y). exact HHCw0.
Qed.

(* F-generalized versions of the two lemmas above (starting guard F0,     *)
(* disjoint from {x, y}, rather than hardcoded nil) -- needed to run the   *)
(* fwd/choice transfer while forcing a function call's body under a guard  *)
(* that already carries x (added by NL_VarExp forcing the call itself).    *)
Lemma NEval_left_fwd_transfer_fwdhere_con_F :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Some (BExpr (EVar y)) ->
  forall F0, ~ In x F0 -> ~ In y F0 ->
  forall brs c zs ys body Gmid Gam' v',
    NEval_left P F0 Gam (BExpr (EVar y)) Gmid (BExpr (ECon c zs)) ->
    In (c, ys, body) brs -> length ys = length zs ->
    NEval_left P F0 Gmid (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval_left P F0 Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr2 G1 Gam' -> HeapCorr2 G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hb F0 HxF0 HyF0 brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2.
  destruct (NEval_left_evar_shape P F0 Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
    [ [Hcase1 [HeqGmid _]]
    | [ [Hcase2 [_ Heqv]]
      | [ [Hcase3 [_ Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
  - subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hcase1 in Hb. discriminate Hb. }
    assert (HforceX : NEval_left P F0 Gam (BExpr (EVar x)) (hupd Gam x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - exact HxF0.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - apply NL_VarCons. exact Hcase1. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy F0 Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hb) Hcase1) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1x HHC2.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_left_con_persists P F0 Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hcase1). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2) | exact Hcy]).
      destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr2 G1v (hupd Gam' x (BExpr (ECon c zs)))).
      { eapply HeapCorr2_update_achieved; [exact HHC2 | exact HG1x | exact (not_eq_sym Hxy) | exact Hcl1 | exact Hz1 | exact Hcy]. }
      eapply HeapCorr2_pointwise; [exact HHC2' | exact Heq2'].
  - subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hz in Hb. injection Hb as Hb. exact (Hne2 Hb). }
    assert (HforceY : NEval_left P (x :: F0) Gam (BExpr (EVar y)) (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { exact (NEval_left_alias_weaken_force_y_F P x y F0 Hxy HxF0 HyF0 Gam (hupd G1 y (BExpr (ECon c zs)))
               (BExpr (ECon c zs)) Hrec1 Hb). }
    assert (HforceX : NEval_left P F0 Gam (BExpr (EVar x))
               (hupd (hupd G1 y (BExpr (ECon c zs))) x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - exact HxF0.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - exact HforceY. }
    assert (HG1xy : G1 x = Some (BExpr (EVar y)) /\ G1 y = Some e0).
    { exact (NEval_left_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: F0) Gam e0 G1 (BExpr (ECon c zs)) Hrec
               (or_introl eq_refl) Hb Hz). }
    destruct HG1xy as [HG1x HG1y].
    assert (Hgmidx : hupd G1 y (BExpr (ECon c zs)) x = Some (BExpr (EVar y))).
    { rewrite (hupd_neq G1 y (BExpr (ECon c zs)) x Hxy). exact HG1x. }
    assert (Hgmidy : hupd G1 y (BExpr (ECon c zs)) y = Some (BExpr (ECon c zs))).
    { unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy F0 (hupd G1 y (BExpr (ECon c zs)))
                (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hgmidx) Hgmidy) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1vx HHC2.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_left_con_persists P F0 (hupd G1 y (BExpr (ECon c zs)))
                 (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hgmidy). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2) | exact Hcy]).
      destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr2 G1v (hupd Gam' x (BExpr (ECon c zs)))).
      { eapply HeapCorr2_update_achieved; [exact HHC2 | exact HG1vx | exact (not_eq_sym Hxy) | exact Hcl1 | exact Hz1 | exact Hcy]. }
      eapply HeapCorr2_pointwise; [exact HHC2' | exact Heq2'].
Qed.

Lemma NEval_left_fwd_transfer_fwdchase_con_F :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Gam y ->
  forall F0, ~ In x F0 -> ~ In y F0 ->
  forall brs c zs ys body Gam' v',
    Gam y = Some (BExpr (ECon c zs)) ->
    In (c, ys, body) brs -> length ys = length zs ->
    NEval_left P F0 Gam (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval_left P F0 Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr2 G1 Gam' -> HeapCorr2 G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hxy F0 HxF0 HyF0 brs c zs ys body Gam' v' Hy HIn Hlen Hrec2.
  assert (Hx : Gam x = Some (BExpr (ECon c zs))) by (rewrite Hxy; exact Hy).
  exists Gam'. split.
  - eapply NL_Select; [apply NL_VarCons; exact Hx | exact HIn | exact Hlen | exact Hrec2].
  - intros G1 _ HHC. exact HHC.
Qed.

Lemma NEval_left_fwd_transfer_F :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  forall F0, ~ In x F0 -> ~ In y F0 ->
  forall brs Gam' v', NEval_left P F0 Gam (BCase y brs) Gam' v' ->
  exists Gam'', NEval_left P F0 Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr2 G1 Gam' -> HeapCorr2 G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx F0 HxF0 HyF0 brs Gam' v' H.
  destruct (NEval_left_bcase_shape P F0 Gam y brs Gam' v' H) as
    [ [c [zs [ys [body [Gmid [Hrec1 [HIn [Hlen Hrec2]]]]]]]]
    | [x' [Gmid [c1' [ys1 [body1 [ws [Hrec1 [Hhd [Hlen [HND [Hfr Hrec2]]]]]]]]]]] ].
  - assert (HGamx := proj1 HGam x). rewrite HGx in HGamx.
    destruct HGamx as [b [Hb HCEx]].
    destruct (CorrE_forced_shape G x b HCEx) as
      [ [c0 [args0 [Hgx Hbeq]]]
      | [ [Hgx Hbeq]
        | [ [f0 [args0 [Hgx Hbeq]]]
          | [ [y1 [y2 [Hgx Hbeq]]]
            | [ [z0 [Hgx Hbeq]]
              | [ [Hgx Hbeq]
                | [ [y0 [Hgx Hbeq]]
                  | [y0 [z0 [c0 [args0 [Hgx [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite HGx in Hgx; discriminate Hgx).
    + rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      exact (NEval_left_fwd_transfer_fwdhere_con_F P G Gam HGam x y HGx Hb
               F0 HxF0 HyF0 brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2).
    + rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      assert (Heqv : BExpr (ECon c zs) = BExpr (ECon c0 args0))
        by (eapply NEval_left_force_reaches_achieved; [exact (proj1 HGam) | exact Hrec1 | reflexivity | exact Hcl0 | exact Hz0]).
      injection Heqv as Heqc Heqargs. subst c0 args0.
      assert (Hx : Gam x = Some (BExpr (ECon c zs))) by exact Hb.
      destruct (NEval_left_evar_shape P F0 Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
        [ [Hcase1 [HeqGmid _]]
        | [ [Hcase2 [_ Heqv2]]
          | [ [Hcase3 [_ Heqv2]]
            | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv2.
      * subst Gmid.
        assert (Hxy : Gam x = Gam y) by (rewrite Hx; rewrite Hcase1; reflexivity).
        exact (NEval_left_fwd_transfer_fwdchase_con_F P G Gam HGam x y HGx Hxy
                 F0 HxF0 HyF0 brs c zs ys body Gam' v' Hcase1 HIn Hlen Hrec2).
      * exfalso.
        assert (Hgy : Gam y = Some (BExpr (ECon c zs))) by exact (proj2 HGam x y HGx c zs Hx).
        rewrite Hz in Hgy. injection Hgy as Hgy. exact (Hne1 c zs Hgy).
  - admit.
Admitted.

(* ==================================================================== *)
(* Unwind a function call's OWN graph derivation (G_Fun -> a chain of       *)
(* G_Let's -> G_Var) into a matching NL_Fun/NL_Let construction that lets    *)
(* us SPLICE IN an arbitrary continuation for forcing the final result y,    *)
(* rather than needing NL_Fun's own (necessarily eager) evaluation to reach   *)
(* a value that matches, relative to G1, on its own.  This is the piece that   *)
(* sidesteps the unsoundness found earlier: no HeapCorr2 claim is made at any   *)
(* INTERMEDIATE point relative to G1 -- Gam1 here is only ever used to plug a    *)
(* continuation back into Gam's own evaluation of e, and HeapCorr2 is only ever  *)
(* asserted relative to G1 itself (a REAL, valid claim, unlike relative to the    *)
(* the still-to-be-mutated y).                                                    *)
(*                                                                                  *)
(* SCOPE: only handles function bodies that are (nested G_Fun/G_Let calls with) NO  *)
(* case expression before reaching the final EVar result -- i.e. the running         *)
(* example `let y = (p ? q) in y`, and anything shaped like it.  A body that does     *)
(* case on something (its own argument, say) before reaching a Fwd-tail result is      *)
(* a further, separate extension (would need lifting NEval_left_fwd_transfer_F's       *)
(* exact-output-heap tracking through an existential heap-changing step) and is         *)
(* left admitted here, honestly flagged, not silently assumed away.                      *)
(*                                                                                        *)
(* Also assumes G1 x = G x (x's own slot survives evaluating the call) as an EXPLICIT     *)
(* hypothesis at the call site, rather than deriving it: it holds for any ordinary,        *)
(* non-self-referential call (x is not among the call's own arguments), by a terminationa   *)
(* argument (re-entering x's own not-yet-resolved EFun-thunk would require an infinite        *)
(* GEval derivation); formalizing that argument itself is a separate, orthogonal task.         *)
(* ==================================================================== *)

Lemma NEval_left_let_chain_to_fwd :
  forall P G e G1 y, GEval P G e G1 (GFwd y) ->
  forall Gam, HeapCorr2 G Gam -> WellFoundedFwd G ->
  forall x, G x <> None -> G1 x = G x ->
  exists Gam1, HeapCorr2 G1 Gam1 /\ Gam1 x = Gam x /\
    forall F0 Gamk vk, NEval_left P F0 Gam1 (BExpr (EVar y)) Gamk vk -> NEval_left P F0 Gam e Gamk vk.
Proof.
  intros P G e G1 y H.
  remember (GFwd y) as v0 eqn:Hv0.
  revert y Hv0.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs Hgx0
    | G0 x0 y0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 f args brs G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 c zs brs ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c1 ys1 body1 brs G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros y Hv0; try discriminate Hv0.
  - (* G_Var *)
    injection Hv0 as Hv0; subst x0.
    intros Gam HGam HWF x Hxdom Hxeq.
    exists Gam. split; [exact HGam | split; [reflexivity | ]].
    intros F0 Gamk vk H. exact H.
  - (* G_Fun *)
    intros Gam HGam HWF x Hxdom Hxeq.
    destruct (IH y Hv0 Gam HGam HWF x Hxdom Hxeq) as [Gam1 [HHC1 [Hgx1 Hplug]]].
    exists Gam1. split; [exact HHC1 | split; [exact Hgx1 | ]].
    intros F0 Gamk vk Hforce.
    assert (HfreshGam : forall y0, ~ In y0 ps -> Gam (s y0) = None).
    { intros y0 Hin. specialize (Hfresh y0 Hin). specialize (proj1 HGam (s y0)) as HGamsy0.
      rewrite Hfresh in HGamsy0. exact HGamsy0. }
    eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact HfreshGam | ].
    exact (Hplug F0 Gamk vk Hforce).
  - (* G_Let *)
    intros Gam HGam HWF x Hxdom Hxeq.
    assert (Hxz : x <> x0).
    { intro Heq; subst x. rewrite HxFresh in Hxdom. exact (Hxdom eq_refl). }
    assert (HGam_ext : HeapCorr2 (hupd G0 x0 (GExpr e0)) (hupd Gam x0 (let_content x0 e0)))
      by (eapply HeapCorr2_extend; [exact HGam | exact HWF | exact HxFresh]).
    assert (HWF_ext : WellFoundedFwd (hupd G0 x0 (GExpr e0)))
      by (eapply WellFoundedFwd_extend; [exact HWF | exact HxFresh]).
    assert (Hxdom_ext : hupd G0 x0 (GExpr e0) x <> None).
    { rewrite (hupd_neq G0 x0 (GExpr e0) x Hxz). exact Hxdom. }
    assert (Hxeq_ext : G1 x = hupd G0 x0 (GExpr e0) x).
    { rewrite (hupd_neq G0 x0 (GExpr e0) x Hxz). exact Hxeq. }
    destruct (IH y Hv0 (hupd Gam x0 (let_content x0 e0)) HGam_ext HWF_ext x Hxdom_ext Hxeq_ext)
      as [Gam1 [HHC1 [Hgx1 Hplug]]].
    exists Gam1. split; [exact HHC1 | split; [ | ] ].
    + rewrite Hgx1. rewrite (hupd_neq Gam x0 (let_content x0 e0) x Hxz). reflexivity.
    + intros F0 Gamk vk Hforce.
      assert (HGamx0 : Gam x0 = None)
        by (specialize (proj1 HGam x0) as HGamx0'; rewrite HxFresh in HGamx0'; exact HGamx0').
      apply NL_Let; [exact HGamx0 | exact (Hplug F0 Gamk vk Hforce)].
  - (* G_CaseFwd: body cases on something before reaching y -- not yet handled *)
    admit.
  - (* G_CaseFun: body cases (via ANOTHER unevaluated call) before reaching y -- not yet handled *)
    admit.
  - (* G_CaseChoice: body cases on a choice before reaching y -- not yet handled *)
    admit.
  - (* G_CaseCon: body cases on a constructor before reaching y -- not yet handled *)
    admit.
  - (* G_CaseConFree: body cases on a free variable before reaching y -- not yet handled *)
    admit.
Admitted.

(* Sibling of NEval_left_let_chain_to_fwd, targeting a Con-shaped result       *)
(* directly (terminal, no continuation to splice in) -- built the same way so   *)
(* it is guard-generic FROM THE START (unlike theorem2's own Con-only IH, which   *)
(* is always nil-guard, since theorem2's own statement is), avoiding a separate    *)
(* "add an unused variable to the guard" lemma entirely: NL_Fun/NL_Let are guard-   *)
(* generic already, so building this construction directly at guard F0 sidesteps    *)
(* ever having to weaken an opaque, already-built nil-guard fact. *)
Lemma NEval_left_let_chain_to_con :
  forall P G e G1 c args, GEval P G e G1 (GExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam -> WellFoundedFwd G ->
  forall x, G x <> None -> G1 x = G x ->
  forall F0,
  exists Gam1, HeapCorr2 G1 Gam1 /\ Gam1 x = Gam x /\
    NEval_left P F0 Gam e Gam1 (BExpr (ECon c args)).
Proof.
  intros P G e G1 c args H.
  remember (GExpr (ECon c args)) as v0 eqn:Hv0.
  revert c args Hv0.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs Hgx0
    | G0 x0 y0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 f args1 brs G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 c0 zs brs ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c1 ys1 body1 brs G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros c args Hv0; try discriminate Hv0.
  - (* G_Con *)
    injection Hv0 as Hv0c Hv0a; subst c0 args0.
    intros Gam HGam HWF x Hxdom Hxeq F0.
    assert (Hb : Gam x = Gam x) by reflexivity.
    exists Gam. split; [exact HGam | split; [reflexivity | apply NL_ValCon] ].
  - (* G_Fun *)
    intros Gam HGam HWF x Hxdom Hxeq F0.
    destruct (IH c args Hv0 Gam HGam HWF x Hxdom Hxeq F0) as [Gam1 [HHC1 [Hgx1 HNE]]].
    exists Gam1. split; [exact HHC1 | split; [exact Hgx1 | ]].
    assert (HfreshGam : forall y0, ~ In y0 ps -> Gam (s y0) = None).
    { intros y0 Hin. specialize (Hfresh y0 Hin). specialize (proj1 HGam (s y0)) as HGamsy0.
      rewrite Hfresh in HGamsy0. exact HGamsy0. }
    eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact HfreshGam | exact HNE].
  - (* G_Let *)
    intros Gam HGam HWF x Hxdom Hxeq F0.
    assert (Hxz : x <> x0).
    { intro Heq; subst x. rewrite HxFresh in Hxdom. exact (Hxdom eq_refl). }
    assert (HGam_ext : HeapCorr2 (hupd G0 x0 (GExpr e0)) (hupd Gam x0 (let_content x0 e0)))
      by (eapply HeapCorr2_extend; [exact HGam | exact HWF | exact HxFresh]).
    assert (HWF_ext : WellFoundedFwd (hupd G0 x0 (GExpr e0)))
      by (eapply WellFoundedFwd_extend; [exact HWF | exact HxFresh]).
    assert (Hxdom_ext : hupd G0 x0 (GExpr e0) x <> None).
    { rewrite (hupd_neq G0 x0 (GExpr e0) x Hxz). exact Hxdom. }
    assert (Hxeq_ext : G1 x = hupd G0 x0 (GExpr e0) x).
    { rewrite (hupd_neq G0 x0 (GExpr e0) x Hxz). exact Hxeq. }
    destruct (IH c args Hv0 (hupd Gam x0 (let_content x0 e0)) HGam_ext HWF_ext x Hxdom_ext Hxeq_ext F0)
      as [Gam1 [HHC1 [Hgx1 HNE]]].
    exists Gam1. split; [exact HHC1 | split; [ | ] ].
    + rewrite Hgx1. rewrite (hupd_neq Gam x0 (let_content x0 e0) x Hxz). reflexivity.
    + assert (HGamx0 : Gam x0 = None)
        by (specialize (proj1 HGam x0) as HGamx0'; rewrite HxFresh in HGamx0'; exact HGamx0').
      apply NL_Let; [exact HGamx0 | exact HNE].
  - (* G_CaseFwd: not yet handled, see NEval_left_let_chain_to_fwd's own scope note *)
    admit.
  - (* G_CaseFun: not yet handled *)
    admit.
  - (* G_CaseChoice: not yet handled *)
    admit.
  - (* G_CaseCon: not yet handled *)
    admit.
  - (* G_CaseConFree: not yet handled *)
    admit.
Admitted.

(* ==================================================================== *)
(* THE PAYOFF.  Under plain HeapCorr, the "y needs further forcing"       *)
(* sub-case of FwdAchievedCon was OPEN (curry.v's own NEval_fwd_transfer,   *)
(* admitted) -- it needed to know forcing y's OWN raw content never         *)
(* touches anything the continuation separately depends on, which HeapCorr  *)
(* alone cannot supply.  Under HeapCorr2, this sub-case is VACUOUS: x already *)
(* holding the achieved shortcut, combined with ChainConsistent applied        *)
(* directly to the SAME (x, y) pair G x = GFwd y gives Gam y = Con c zs          *)
(* IMMEDIATELY -- contradicting "y still needs forcing" (non-terminal content)    *)
(* outright.  No replay, no non-interference argument, no admit.                  *)
(*                                                                                  *)
(* The OTHER open case (Nat-Guess, y resolving to a free-variable self-loop         *)
(* rather than a constructor) is a genuinely SEPARATE gap -- ChainConsistent, as     *)
(* stated, is only about CONSTRUCTOR achievement, and does not (yet) say anything     *)
(* about free-variable results.  Left admitted here, unchanged from curry.v.           *)
(* ==================================================================== *)

Lemma NEval_left_fwd_transfer :
  forall P G Gam, HeapCorr2 G Gam ->
  forall x y, G x = Some (GFwd y) ->
  forall brs Gam' v', NEval_left P nil Gam (BCase y brs) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) ->
                  (forall x' Gmid', NEval_left P nil Gam (BExpr (EVar y)) Gmid' (BExpr (EVar x')) ->
                    x' <> y -> ContractLoc G1 y x') ->
                  HeapCorr2 G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx brs Gam' v' H.
  destruct (NEval_left_bcase_shape P nil Gam y brs Gam' v' H) as
    [ [c [zs [ys [body [Gmid [Hrec1 [HIn [Hlen Hrec2]]]]]]]]
    | [x' [Gmid [c1' [ys1 [body1 [ws [Hrec1 [Hhd [Hlen [HND [Hfr Hrec2]]]]]]]]]]] ].
  - assert (HGamx := proj1 HGam x). rewrite HGx in HGamx.
    destruct HGamx as [b [Hb HCEx]].
    destruct (CorrE_forced_shape G x b HCEx) as
      [ [c0 [args0 [Hgx Hbeq]]]
      | [ [Hgx Hbeq]
        | [ [f0 [args0 [Hgx Hbeq]]]
          | [ [y1 [y2 [Hgx Hbeq]]]
            | [ [z0 [Hgx Hbeq]]
              | [ [Hgx Hbeq]
                | [ [y0 [Hgx Hbeq]]
                  | [y0 [z0 [c0 [args0 [Hgx [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite HGx in Hgx; discriminate Hgx).
    + rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      destruct (NEval_left_fwd_transfer_fwdhere_con P G Gam HGam x y HGx Hb
               brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2) as [Gam'' [HNE HTrans]].
      exists Gam''. split; [exact HNE | intros G1 HG1x _ HHC2; apply HeapCorr2_to_HeapCorr; exact (HTrans G1 HG1x HHC2)].
    + rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      assert (Heqv : BExpr (ECon c zs) = BExpr (ECon c0 args0))
        by (eapply NEval_left_force_reaches_achieved; [exact (proj1 HGam) | exact Hrec1 | reflexivity | exact Hcl0 | exact Hz0]).
      injection Heqv as Heqc Heqargs. subst c0 args0.
      assert (Hx : Gam x = Some (BExpr (ECon c zs))) by exact Hb.
      destruct (NEval_left_evar_shape P nil Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
        [ [Hcase1 [HeqGmid _]]
        | [ [Hcase2 [_ Heqv2]]
          | [ [Hcase3 [_ Heqv2]]
            | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv2.
      * subst Gmid.
        assert (Hxy : Gam x = Gam y) by (rewrite Hx; rewrite Hcase1; reflexivity).
        destruct (NEval_left_fwd_transfer_fwdchase_con P G Gam HGam x y HGx Hxy
                 brs c zs ys body Gam' v' Hcase1 HIn Hlen Hrec2) as [Gam'' [HNE HTrans]].
        exists Gam''. split; [exact HNE | intros G1v HG1x _ HHC2; apply HeapCorr2_to_HeapCorr; exact (HTrans G1v HG1x HHC2)].
      * (* VACUOUS under HeapCorr2: ChainConsistent applied to (x, y) with
           G x = GFwd y and Gam x = Con c zs forces Gam y = Con c zs directly
           -- but Hz/Hne1 say Gam y = e0 with e0 never Con-shaped.  Contradiction. *)
        exfalso.
        assert (Hgy : Gam y = Some (BExpr (ECon c zs))) by exact (proj2 HGam x y HGx c zs Hx).
        rewrite Hz in Hgy. injection Hgy as Hgy. exact (Hne1 c zs Hgy).
  - destruct (Nat.eq_dec x y) as [Heqxy | Hxy].
    + subst y. exists Gam'. split.
      * eapply NL_Guess; [exact Hrec1 | exact Hhd | exact Hlen | exact HND | exact Hfr | exact Hrec2].
      * intros G1 _ _ HHC. apply HeapCorr2_to_HeapCorr. exact HHC.
    + assert (HGamx := proj1 HGam x). rewrite HGx in HGamx.
      destruct HGamx as [b [Hb HCEx]].
      destruct (CorrE_forced_shape G x b HCEx) as
        [ [c0 [args0 [Hgx Hbeq]]]
        | [ [Hgx Hbeq]
          | [ [f0 [args0 [Hgx Hbeq]]]
            | [ [y1 [y2 [Hgx Hbeq]]]
              | [ [z0 [Hgx Hbeq]]
                | [ [Hgx Hbeq]
                  | [ [y0 [Hgx Hbeq]]
                    | [y0 [z0 [c0 [args0 [Hgx [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
        try (rewrite HGx in Hgx; discriminate Hgx).
      * rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
        destruct (NEval_left_fwd_transfer_fwdhere_free P G Gam HGam x y HGx Hxy Hb
                 brs x' c1' ys1 body1 ws Gmid Gam' v' Hrec1 Hhd Hlen HND Hfr Hrec2) as [Gam'' [HNE HTrans]].
        exists Gam''. split.
        -- exact HNE.
        -- intros G1 HG1x Hxfwd_general HHC2.
           exact (HTrans G1 HG1x (Hxfwd_general x' Gmid Hrec1) HHC2).
      * rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
        exfalso.
        assert (Heqv : BExpr (EVar x') = BExpr (ECon c0 args0))
          by (eapply NEval_left_force_reaches_achieved; [exact (proj1 HGam) | exact Hrec1 | reflexivity | exact Hcl0 | exact Hz0]).
        discriminate Heqv.
Qed.

(* A GFwd edge, once created, is PERMANENT for the rest of any GEval        *)
(* derivation -- no rule ever mutates a location whose current content is    *)
(* already GFwd (every mutating rule's own precondition requires the target's *)
(* CURRENT content to be a specific direct GExpr shape: EChoice, EFun, or Free). *)
Lemma GEval_fwd_permanent :
  forall P G e G' v, GEval P G e G' v -> forall x y, G x = Some (GFwd y) -> G' x = Some (GFwd y).
Proof.
  intros P G e G' v H.
  induction H as
    [ G0
    | G0
    | G0 c args
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs Hgx0
    | G0 x0 y0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 f args brs G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 c zs brs ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c1 ys1 body1 brs G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros x y Hxy.
  - exact Hxy.
  - exact Hxy.
  - exact Hxy.
  - exact Hxy.
  - exact Hxy.
  - exact (IH x y Hxy).
  - assert (Hxx0 : x <> x0) by (intro Heq; subst x; congruence).
    apply IH. rewrite (hupd_neq G0 x0 (GExpr e0) x Hxx0). exact Hxy.
  - exact Hxy.
  - exact (IH x y Hxy).
  - assert (Hxx0 : x <> x0) by (intro Heq; subst x; congruence).
    apply IH2. rewrite (hupd_neq G1 x0 vx x Hxx0). exact (IH1 x y Hxy).
  - assert (Hxx0 : x <> x0) by (intro Heq; subst x; congruence).
    apply IH. rewrite (hupd_neq G0 x0 (GFwd y0) x Hxx0). exact Hxy.
  - exact (IH x y Hxy).
  - assert (Hxx0 : x <> x0) by (intro Heq; subst x; congruence).
    apply IH.
    assert (Hxws : ~ In x ws).
    { intro Hin. specialize (Hfresh x Hin). congruence. }
    rewrite (hupd_list_notin ws (map (fun _ => GExpr EFree) ws) (hupd G0 x0 (GExpr (ECon c1 ws))) x Hxws).
    rewrite (hupd_neq G0 x0 (GExpr (ECon c1 ws)) x Hxx0). exact Hxy.
Qed.

(* Mirrors GEval_fwd_permanent exactly, for ECon instead of GFwd: once a    *)
(* location is achieved, no rule's own precondition can ever match it        *)
(* again (CaseFun/CaseChoice/CaseConFree all require a DIFFERENT current      *)
(* shape), and Let/CaseConFree's fresh binders require None, which an          *)
(* already-Some (Con-shaped) location never is. *)
Lemma GEval_con_persists :
  forall P G e G' v, GEval P G e G' v ->
  forall p cc al, G p = Some (GExpr (ECon cc al)) -> G' p = Some (GExpr (ECon cc al)).
Proof.
  intros P G e G' v H.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs Hgx0
    | G0 x0 y0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 f args brs G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 c0 zs brs ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c0 ys1 body1 brs G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros p cc al Hx.
  - exact Hx.
  - exact Hx.
  - exact Hx.
  - exact Hx.
  - exact Hx.
  - exact (IH p cc al Hx).
  - assert (Hxx0 : p <> x0) by (intro Heq; subst p; congruence).
    apply IH. rewrite (hupd_neq G0 x0 (GExpr e0) p Hxx0). exact Hx.
  - exact Hx.
  - exact (IH p cc al Hx).
  - assert (Hxx0 : p <> x0) by (intro Heq; subst p; congruence).
    apply IH2. rewrite (hupd_neq G1 x0 vx p Hxx0). exact (IH1 p cc al Hx).
  - assert (Hxx0 : p <> x0) by (intro Heq; subst p; congruence).
    apply IH. rewrite (hupd_neq G0 x0 (GFwd y0) p Hxx0). exact Hx.
  - exact (IH p cc al Hx).
  - assert (Hxx0 : p <> x0) by (intro Heq; subst p; congruence).
    apply IH.
    assert (Hxws : ~ In p ws).
    { intro Hin. specialize (Hfresh p Hin). congruence. }
    rewrite (hupd_list_notin ws (map (fun _ => GExpr EFree) ws) (hupd G0 x0 (GExpr (ECon c0 ws))) p Hxws).
    rewrite (hupd_neq G0 x0 (GExpr (ECon c0 ws)) p Hxx0). exact Hx.
Qed.

(* An ALREADY fully-achieved ContractLoc chain (terminal already Con-shaped)
   survives any further GEval step: every hop is a Fwd edge (permanent, via
   GEval_fwd_permanent) except the terminal, which is Con-shaped and hence
   ALSO permanent (via GEval_con_persists, no rule ever mutates an
   already-Con location). *)
Lemma ContractLoc_persists_when_achieved :
  forall P G0 e G1 v', GEval P G0 e G1 v' ->
  forall y z c args, ContractLoc G0 y z -> G0 z = Some (GExpr (ECon c args)) ->
  ContractLoc G1 y z.
Proof.
  intros P G0 e G1 v' HG y z c args Hcl.
  induction Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH]; intro Hz.
  - eapply CL_Here. exact (GEval_con_persists P G0 e G1 v' HG x0 c args Hz).
  - eapply CL_Fwd.
    + exact (GEval_fwd_permanent P G0 e G1 v' HG x0 y0 H0).
    + exact (IH Hz).
Qed.

(* If y's OWN Nat-heap witness is a NON-self-loop alias EVar w (w <> y),
   it's justified either via CorrE_FwdHere (G0 y = GFwd w directly) or via
   CorrE3's own VarChase-skip-ahead disjunct (G0 y = GFwd y0', an achieved
   chase from y0'); CorrE_Free is excluded since it always self-loops
   (b = EVar y, contradicting w <> y), and CorrE_VarThunk is excluded by
   NoVarThunk. The FwdHere disjunct is graph-monotone outright (Fwd edges
   permanent). The skip-ahead disjunct's own achieved chain is ALSO
   graph-monotone, but its Nat-heap witness (VarChase Gam y (Con c1 args1),
   for whatever c1/args1 its OWN internal justification used) does NOT
   need transporting from Gam to a caller-supplied Gam2 at all: forcing w
   directly (Hforcew, rooted at Gam) is shown to compute EXACTLY that same
   c1/args1 via NEval_left_force_matches_VarChase (since w is y's own
   first hop), so c1/args1 is forced to coincide with whatever Hforcew
   already computed -- and a FRESH one-hop VarChase witness for Gam2 is
   then built directly from the caller's own y/w values, sidestepping the
   need to relate Gam2 to Gam's static structure at all. *)
Lemma HeapCorr_evar_witness_graph_persists :
  forall G0 Gam, HeapCorr G0 Gam -> NoVarThunk G0 ->
  forall y w, y <> w -> Gam y = Some (BExpr (EVar w)) ->
  forall P F Gmid c args, NEval_left P F Gam (BExpr (EVar w)) Gmid (BExpr (ECon c args)) ->
  forall e G1 v', GEval P G0 e G1 v' ->
  forall Gam2, Gam2 y = Some (BExpr (EVar w)) -> Gam2 w = Some (BExpr (ECon c args)) ->
  CorrE3 G1 Gam2 y (BExpr (EVar w)).
Proof.
  intros G0 Gam HGam HNVT y w Hyw Hgamyw P F Gmid c args Hforcew e G1 v' HG Gam2 Hgam2y Hgam2w.
  assert (HGamy := HGam y). destruct (G0 y) as [gy | ] eqn:EGy;
    [ | rewrite HGamy in Hgamyw; discriminate Hgamyw].
  destruct HGamy as [b [Hb HCE3]]. rewrite Hb in Hgamyw. injection Hgamyw as Hgamyw. subst b.
  destruct HCE3 as [HCE | [y0' [z0 [c0 [args0 [Hgy0fwd [Hcl0 [Hz0 HVC]]]]]]]].
  - destruct (CorrE_forced_shape G0 y (BExpr (EVar w)) HCE) as
      [ [c1 [args1 [Hg1 Hb1]]]
      | [ [Hg1 Hb1]
        | [ [f1 [args1 [Hg1 Hb1]]]
          | [ [y1 [y2 [Hg1 Hb1]]]
            | [ [z1 [Hg1 Hb1]]
              | [ [Hg1 Hb1]
                | [ [y1 [Hg1 Hb1]]
                  | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ]; try discriminate Hb1.
    + injection Hb1 as Hb1. exfalso. exact (Hyw (eq_sym Hb1)).
    + injection Hb1 as Hb1. subst z1. exfalso. exact (HNVT y w Hg1).
    + injection Hb1 as Hb1. subst y1.
      left. eapply CorrE_FwdHere. exact (GEval_fwd_permanent P G0 e G1 v' HG y w Hg1).
  - destruct (VarChase_first_step Gam y (BExpr (ECon c0 args0)) HVC) as
      [b1 [Hb1 [Heqb1 | [w1 [Heqb1 [Hnew1y Hrecw1]]]]]].
    + rewrite Hb in Hb1. injection Hb1 as Hb1. rewrite Heqb1 in Hb1. discriminate Hb1.
    + rewrite Hb in Hb1. injection Hb1 as Hb1. rewrite Heqb1 in Hb1.
      injection Hb1 as Hb1. subst w1.
      assert (Heq_cargs : BExpr (ECon c args) = BExpr (ECon c0 args0))
        by exact (NEval_left_force_matches_VarChase Gam w (BExpr (ECon c0 args0)) Hrecw1 c0 args0 eq_refl
                    P F Gmid (BExpr (ECon c args)) Hforcew).
      injection Heq_cargs as Heqc Heqargs. subst c0 args0.
      right. exists y0', z0, c, args.
      split; [exact (GEval_fwd_permanent P G0 e G1 v' HG y y0' Hgy0fwd) | ].
      split; [exact (ContractLoc_persists_when_achieved P G0 e G1 v' HG y0' z0 c args Hcl0 Hz0) | ].
      split; [exact (GEval_con_persists P G0 e G1 v' HG z0 c args Hz0) | ].
      eapply VChase_Hop; [exact Hgam2y | exact (not_eq_sym Hyw) | ].
      apply VChase_Here; [exact Hgam2w | intros w' Hcontra; discriminate Hcontra].
Qed.

(* GEval never RESULTS in a bare, unforced variable reference -- G_Var       *)
(* immediately wraps it as GFwd, and every other rule's result is either      *)
(* inherited from a smaller GEval derivation (covered by IH) or a literal,     *)
(* non-EVar constant (EBot/EFree/ECon/EChoice). *)
Lemma GEval_result_not_var_thunk :
  forall P G e G' v, GEval P G e G' v -> forall z, v <> GExpr (EVar z).
Proof.
  intros P G e G' v H.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs Hgx0
    | G0 x0 y0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 f args brs G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs G1 v1 Hgx0 Hrec IH
    | G0 x0 c0 zs brs ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c0 ys1 body1 brs G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros z Hcontra.
  - discriminate Hcontra.
  - discriminate Hcontra.
  - discriminate Hcontra.
  - discriminate Hcontra.
  - discriminate Hcontra.
  - exact (IH z Hcontra).
  - exact (IH z Hcontra).
  - discriminate Hcontra.
  - exact (IH z Hcontra).
  - exact (IH2 z Hcontra).
  - exact (IH z Hcontra).
  - exact (IH z Hcontra).
  - exact (IH z Hcontra).
Qed.

(* The graph-side counterpart of the natural-semantics VarThunk ambiguity   *)
(* the previous section's admit ran into: whenever a location is genuinely   *)
(* CASED (as x below), its FINAL content (after the complete derivation)      *)
(* can never be a bare, unforced GExpr(EVar _) -- either it started as        *)
(* something else and no rule ever OVERWRITES a matching location back to     *)
(* a var-thunk (GEval_con_persists/GEval_fwd_permanent cover the two shapes    *)
(* that get WRITTEN by the case rules), or it recurses further via CaseFwd/    *)
(* CaseFun and the SAME fact applies by induction, or its result comes from    *)
(* evaluating a call (CaseFun's vx), which GEval_result_not_var_thunk rules     *)
(* out directly. *)
Lemma GEval_case_result_not_var_thunk :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v -> forall z, G' x <> Some (GExpr (EVar z)).
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 f args brs0 G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 c0 zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c0 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros x1 brs1 He; try discriminate He; intros z Hcontra.
  - (* G_CaseBot *)
    injection He as He1 He2; subst x1 brs1.
    rewrite Hgx0 in Hcontra. discriminate Hcontra.
  - (* G_CaseFwd *)
    injection He as He1 He2; subst x1 brs1.
    assert (HG1 : G1 x0 = Some (GFwd y0)) by exact (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0).
    rewrite HG1 in Hcontra. discriminate Hcontra.
  - (* G_CaseFun: IH2 is for the recursive premise which cases x0 AGAIN *)
    injection He as He1 He2; subst x1 brs1.
    exact (IH2 x0 brs0 eq_refl z Hcontra).
  - (* G_CaseChoice *)
    injection He as He1 He2; subst x1 brs1.
    assert (Hhit : hupd G0 x0 (GFwd y0) x0 = Some (GFwd y0)) by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
    assert (HG1 : G1 x0 = Some (GFwd y0)) by exact (GEval_fwd_permanent P (hupd G0 x0 (GFwd y0)) (BCase y0 brs0) G1 v1 Hrec x0 y0 Hhit).
    rewrite HG1 in Hcontra. discriminate Hcontra.
  - (* G_CaseCon *)
    injection He as He1 He2; subst x1 brs1.
    assert (HG1 : G1 x0 = Some (GExpr (ECon c0 zs)))
      by exact (GEval_con_persists P G0 (rename_b (zipsubst ys zs) body) G1 v1 Hrec x0 c0 zs Hgx0).
    rewrite HG1 in Hcontra. discriminate Hcontra.
  - (* G_CaseConFree *)
    injection He as He1 He2; subst x1 brs1.
    assert (Hxnotin : ~ In x0 ws).
    { intro Hin. specialize (Hfresh x0 Hin). rewrite Hgx0 in Hfresh. discriminate Hfresh. }
    assert (Hhit : hupd_list (hupd G0 x0 (GExpr (ECon c0 ws))) ws (map (fun _ => GExpr EFree) ws) x0 = Some (GExpr (ECon c0 ws))).
    { rewrite (hupd_list_notin ws (map (fun _ => GExpr EFree) ws) (hupd G0 x0 (GExpr (ECon c0 ws))) x0 Hxnotin).
      unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    assert (HG1 : G1 x0 = Some (GExpr (ECon c0 ws)))
      by exact (GEval_con_persists P (hupd_list (hupd G0 x0 (GExpr (ECon c0 ws))) ws (map (fun _ => GExpr EFree) ws))
                  (rename_b (zipsubst ys1 ws) body1) G1 v1 Hrec x0 c0 ws Hhit).
    rewrite HG1 in Hcontra. discriminate Hcontra.
Qed.

(* ==================================================================== *)
(* EXPLORATORY: the "deep" counterpart to curry.v's GEval_case_gives_      *)
(* ContractLoc, which only gives the SHALLOW target (relative to the        *)
(* STARTING graph G) because its own G_CaseFun/G_CaseChoice cases don't      *)
(* recurse into the continuation's own GEval premise.  Restated relative to   *)
(* G' (the FINAL graph) instead, that continuation premise (already BCase-    *)
(* shaped for G_CaseFun) becomes directly reusable as the induction's own      *)
(* IH, and GEval_fwd_permanent/GEval_con_persists carry the rest.  Purely      *)
(* graph-side: no Nat-heap, no HeapCorr, at all. *)
Lemma GEval_case_gives_ContractLoc_deep :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v -> exists w, ContractLoc G' x w.
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H as
    [ G0
    | G0
    | G0 c args
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros x1 brs1 He; try discriminate He.
  - (* G_CaseBot *) injection He as He1 He2; subst x1 brs1.
    exists x0. eapply CL_Here; exact Hgx0.
  - (* G_CaseFwd *) injection He as He1 He2; subst x1 brs1.
    destruct (IH y0 brs0 eq_refl) as [w Hcl].
    exists w. eapply CL_Fwd; [ | exact Hcl].
    exact (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0).
  - (* G_CaseFun *) injection He as He1 He2; subst x1 brs1.
    destruct (IH2 x0 brs0 eq_refl) as [w Hcl].
    exists w. exact Hcl.
  - (* G_CaseChoice *) injection He as He1 He2; subst x1 brs1.
    destruct (IH y0 brs0 eq_refl) as [w Hcl].
    assert (Hxfwd : G1 x0 = Some (GFwd y0)).
    { eapply GEval_fwd_permanent; [exact Hrec | ].
      unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    exists w. eapply CL_Fwd; [exact Hxfwd | exact Hcl].
  - (* G_CaseCon *) injection He as He1 He2; subst x1 brs1.
    exists x0. eapply CL_Here.
    exact (GEval_con_persists P G0 (rename_b (zipsubst ys zs) body) G1 v1 Hrec x0 c zs Hgx0).
  - (* G_CaseConFree *) injection He as He1 He2; subst x1 brs1.
    exists x0. eapply CL_Here.
    assert (Hhit : hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws) x0
                 = Some (GExpr (ECon c1 ws))).
    { assert (Hxws : ~ In x0 ws).
      { intro Hin. specialize (Hfresh x0 Hin). congruence. }
      rewrite (hupd_list_notin ws (map (fun _ => GExpr EFree) ws) (hupd G0 x0 (GExpr (ECon c1 ws))) x0 Hxws).
      unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    exact (GEval_con_persists P
             (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
             (rename_b (zipsubst ys1 ws) body1) G1 v1 Hrec x0 c1 ws Hhit).
Qed.



(* ==================================================================== *)
(* G_CaseChoice needs a new piece: x's OWN content starts as EChoice y z    *)
(* (not yet an alias at all), and after forcing picks y, the recursive        *)
(* premise runs under guard [x] from the ORIGINAL Gam -- but theorem2's IH      *)
(* naturally hands us a derivation over Gam_mid = hupd Gam x (EVar y) instead    *)
(* (the heap matching the UPDATED graph).  Relating "forcing y under guard [x]    *)
(* from Gam" to "from Gam_mid" needs a genuine frame fact: a guarded location's     *)
(* specific content is irrelevant to the rest of the derivation, whatever it is,     *)
(* PROVIDED it's non-terminal in both heaps (so neither NL_VarCons/VarSelf/VarFree    *)
(* can ever match it directly, bypassing the guard) -- generalizing                   *)
(* NEval_left_alias_weaken's OWN technique, but simpler: the "z = x" dangerous          *)
(* branch is now an IMMEDIATE contradiction (x is ALREADY in F, so N_VarExp's own        *)
(* `~In z F0` fails outright), no aliasing argument needed at all. *)

Lemma NEval_left_frame_guarded :
  forall x ex, (forall c args, ex <> BExpr (ECon c args)) -> ex <> BExpr (EVar x) -> ex <> BExpr EFree ->
  forall ex2, (forall c args, ex2 <> BExpr (ECon c args)) -> ex2 <> BExpr (EVar x) -> ex2 <> BExpr EFree ->
  forall P F Gam e Gam' v, NEval_left P F Gam e Gam' v ->
  In x F ->
  Gam x = Some ex ->
  forall Gam2, (forall w, w <> x -> Gam2 w = Gam w) -> Gam2 x = Some ex2 ->
  exists Gam2', NEval_left P F Gam2 e Gam2' v /\ (forall w, w <> x -> Gam2' w = Gam' w).
Proof.
  intros x ex Hex1 Hex2 Hex3 ex2 Hex2_1 Hex2_2 Hex2_3 P F Gam e Gam' v H.
  induction H as
    [ F0 G z c0 args0 Hz
    | F0 G z Hz
    | F0 G z Hz
    | F0 G z e1 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec IH
    | F0 G
    | F0 G c0 args0
    | F0 G G1 f args1 ps body v s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | F0 G G1 z e1 k v HzFresh Hrec IH
    | F0 G x1 y1 G1 v Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HxF Hgx Gam2 Heq Hgx2.
  - assert (Hzx : z <> x).
    { intro Heq'; subst z. assert (Hexeq : ex = BExpr (ECon c0 args0)) by congruence. exact (Hex1 c0 args0 Hexeq). }
    exists Gam2. split.
    + apply NL_VarCons. rewrite (Heq z Hzx). exact Hz.
    + intros w Hwx; exact (Heq w Hwx).
  - assert (Hzx : z <> x).
    { intro Heq'; subst z. assert (Hexeq : ex = BExpr (EVar x)) by congruence. exact (Hex2 Hexeq). }
    exists Gam2. split.
    + apply NL_VarSelf. rewrite (Heq z Hzx). exact Hz.
    + intros w Hwx; exact (Heq w Hwx).
  - assert (Hzx : z <> x).
    { intro Heq'; subst z. assert (Hexeq : ex = BExpr EFree) by congruence. exact (Hex3 Hexeq). }
    exists (hupd Gam2 z (BExpr (EVar z))). split.
    + apply NL_VarFree. rewrite (Heq z Hzx). exact Hz.
    + intros w Hwx. unfold hupd. destruct (Nat.eqb w z) eqn:E; [reflexivity | apply Heq; exact Hwx].
  - destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z. exfalso. exact (HzF HxF).
    + assert (HxF' : In x (z :: F0)) by (right; exact HxF).
      destruct (IH HxF' Hgx Gam2 Heq Hgx2) as [G2' [HNE2 Heq2]].
      exists (hupd G2' z v0). split.
      * eapply NL_VarExp.
        -- exact HzF.
        -- rewrite (Heq z Hnezx). exact Hz.
        -- exact Hne1.
        -- exact Hne2.
        -- exact Hne3.
        -- exact HNE2.
      * intros w Hwx. unfold hupd. destruct (Nat.eqb w z) eqn:E; [reflexivity | apply Heq2; exact Hwx].
  - exists Gam2. split; [apply NL_ValFree | intros w Hwx; exact (Heq w Hwx)].
  - exists Gam2. split; [apply NL_ValCon | intros w Hwx; exact (Heq w Hwx)].
  - destruct (IH HxF Hgx Gam2 Heq Hgx2) as [G2' [HNE2 Heq2]].
    exists G2'. split.
    + eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE2].
      intros y0 Hy0.
      assert (Hsyx : s y0 <> x).
      { intro Heqsy. specialize (Hfresh y0 Hy0). rewrite Heqsy in Hfresh. rewrite Hgx in Hfresh. discriminate Hfresh. }
      rewrite (Heq (s y0) Hsyx). exact (Hfresh y0 Hy0).
    + exact Heq2.
  - assert (Hzx : z <> x) by (intro Heq'; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Heq' : forall w, w <> x -> hupd Gam2 z (let_content z e1) w = hupd G z (let_content z e1) w).
    { intros w Hwx. unfold hupd. destruct (Nat.eqb w z) eqn:E; [reflexivity | apply Heq; exact Hwx]. }
    assert (Hgx' : hupd G z (let_content z e1) x = Some ex)
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    assert (Hgx2' : hupd Gam2 z (let_content z e1) x = Some ex2)
      by (rewrite (hupd_neq Gam2 z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx2).
    destruct (IH HxF Hgx' (hupd Gam2 z (let_content z e1)) Heq' Hgx2') as [G2' [HNE2 Heq2]].
    exists G2'. split.
    + apply NL_Let; [rewrite (Heq z Hzx); exact HzFresh | exact HNE2].
    + exact Heq2.
  - destruct (IH HxF Hgx Gam2 Heq Hgx2) as [G2' [HNE2 Heq2]].
    exists G2'. split; [eapply NL_Or; exact HNE2 | exact Heq2].
  - destruct (IH1 HxF Hgx Gam2 Heq Hgx2) as [G1' [HNE1 Heq1]].
    assert (HG1x : G1 x = Some ex) by exact (NEval_left_frozen_at x ex Hex1 Hex2 Hex3 P F0 G (BExpr (EVar z)) G1 (BExpr (ECon c0 zs)) Hrec1 HxF Hgx).
    assert (HG1x' : G1' x = Some ex2) by exact (NEval_left_frozen_at x ex2 Hex2_1 Hex2_2 Hex2_3 P F0 Gam2 (BExpr (EVar z)) G1' (BExpr (ECon c0 zs)) HNE1 HxF Hgx2).
    destruct (IH2 HxF HG1x G1' Heq1 HG1x') as [G2' [HNE2 Heq2]].
    exists G2'. split; [eapply NL_Select; [exact HNE1 | exact HIn | exact Hlen | exact HNE2] | exact Heq2].
  - destruct (IH1 HxF Hgx Gam2 Heq Hgx2) as [G1' [HNE1 Heq1]].
    assert (HG1x : G1 x = Some ex) by exact (NEval_left_frozen_at x ex Hex1 Hex2 Hex3 P F0 G (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 HxF Hgx).
    assert (HG1x' : G1' x = Some ex2) by exact (NEval_left_frozen_at x ex2 Hex2_1 Hex2_2 Hex2_3 P F0 Gam2 (BExpr (EVar z)) G1' (BExpr (EVar z')) HNE1 HxF Hgx2).
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (HG1'z' : G1' z' = Some (BExpr (EVar z')))
      by exact (NEval_left_selfloop_result_persists P F0 Gam2 (BExpr (EVar z)) G1' z' HNE1).
    assert (Hxz' : x <> z') by (intro Heq'; subst x; rewrite HG1z' in HG1x; injection HG1x as HG1x; exact (Hex2 (eq_sym HG1x))).
    assert (Hxnotin : ~ In x ws).
    { intro Hin. specialize (Hfr x Hin). rewrite Hfr in HG1x. discriminate HG1x. }
    assert (Heq1' : forall w, w <> x -> hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
                             = hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
    { intros w Hwx. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
      - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws (hupd G1' z' (BExpr (ECon c1 ws))) w Hin).
        rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws (hupd G1 z' (BExpr (ECon c1 ws))) w Hin).
        reflexivity.
      - rewrite (hupd_list_notin ws _ _ w Hnin). rewrite (hupd_list_notin ws _ _ w Hnin).
        destruct (Nat.eq_dec w z') as [Heqwz | Hnewz].
        + subst w. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
        + rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) w Hnewz).
          rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) w Hnewz).
          exact (Heq1 w Hwx). }
    assert (Hgx3 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x = Some ex).
    { assert (Hxnotin' : ~ In x ws) by exact Hxnotin.
      rewrite hupd_list_notin by exact Hxnotin'. rewrite (hupd_neq G1 z' (BExpr (ECon c1 ws)) x Hxz'). exact HG1x. }
    assert (Hgx3' : hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x = Some ex2).
    { rewrite hupd_list_notin by exact Hxnotin. rewrite (hupd_neq G1' z' (BExpr (ECon c1 ws)) x Hxz'). exact HG1x'. }
    destruct (IH2 HxF Hgx3 _ Heq1' Hgx3') as [G2' [HNE2 Heq2]].
    exists G2'. split.
    + eapply NL_Guess; [exact HNE1 | exact Hhd | exact Hlen | exact HND | | exact HNE2].
      intros w Hw.
      destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      * subst w. exfalso. exact (Hxnotin Hw).
      * rewrite (Heq1 w Hnewx). exact (Hfr w Hw).
    + exact Heq2.
Qed.

(* Curry's `?` always picks its LEFT operand under NL_Or (this whole file's
   point), so a location holding `EChoice y z` behaves EXACTLY like a
   location holding the one-hop alias `EVar y`, for the ONE thing that ever
   matters about it: forcing it. `NEval_left_evar_shape` forces `Gam x =
   EVar y` (y<>x) down to the SOLE consistent shape, NL_VarExp, whose own
   recursive premise forces `y` under the WIDENED guard `x::nil` -- and
   THAT sub-derivation genuinely has `x` in its guard, so the EXISTING
   `NEval_left_frame_guarded` transports it to the EChoice-holding heap
   directly, no new induction needed. Re-wrapping via NL_VarExp+NL_Or on
   the EChoice side reconstructs the SAME final memoized value. This is
   the missing piece to bridge `_shortcut_alias`-style reasoning (which
   only understands the literal one-hop-alias shape) across to a location
   whose Nat-heap content is a not-yet-collapsed choice, e.g. `x0` in
   G_CaseChoice, whose slot is `EChoice y0 z0`, never `EVar y0` outright. *)
Lemma NEval_left_choice_as_alias_force :
  forall P x y z, x <> y ->
  forall Gam Gam1 v, NEval_left P nil Gam (BExpr (EVar x)) Gam1 v ->
  Gam x = Some (BExpr (EVar y)) ->
  forall Gam2, (forall w, w <> x -> Gam2 w = Gam w) -> Gam2 x = Some (BExpr (EChoice y z)) ->
  exists Gam1', NEval_left P nil Gam2 (BExpr (EVar x)) Gam1' v /\ (forall w, Gam1' w = Gam1 w).
Proof.
  intros P x y z Hxy Gam Gam1 v H Hgx Gam2 Heq Hgx2.
  destruct (NEval_left_evar_shape P nil Gam x Gam1 v H) as
    [ [Hcase1 [_ [c0 [args0 Heqv]]]]
    | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGam1]]]]]]]]]]].
  - rewrite Heqv in Hcase1. rewrite Hgx in Hcase1. discriminate Hcase1.
  - exfalso. rewrite Hgx in Hcase2. injection Hcase2 as Hcase2. exact (Hxy (eq_sym Hcase2)).
  - rewrite Hgx in Hcase3; discriminate Hcase3.
  - assert (Heqe0 : e0 = BExpr (EVar y)) by (rewrite Hz in Hgx; injection Hgx as Hgx; exact Hgx).
    subst e0.
    assert (HxF : In x (x :: nil)) by (left; reflexivity).
    assert (Hex1 : forall c args, BExpr (EVar y) <> BExpr (ECon c args))
      by (intros c args Hcontra; discriminate Hcontra).
    assert (Hex2 : BExpr (EVar y) <> BExpr (EVar x))
      by (intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra))).
    assert (Hex3 : BExpr (EVar y) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
    assert (Hex2_1 : forall c args, BExpr (EChoice y z) <> BExpr (ECon c args))
      by (intros c args Hcontra; discriminate Hcontra).
    assert (Hex2_2 : BExpr (EChoice y z) <> BExpr (EVar x)) by (intro Hcontra; discriminate Hcontra).
    assert (Hex2_3 : BExpr (EChoice y z) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
    destruct (NEval_left_frame_guarded x (BExpr (EVar y)) Hex1 Hex2 Hex3
                (BExpr (EChoice y z)) Hex2_1 Hex2_2 Hex2_3
                P (x :: nil) Gam (BExpr (EVar y)) G1 v Hrec HxF Hz
                Gam2 Heq Hgx2) as [G2' [HNE2 Heq2]].
    exists (hupd G2' x v). split.
    + eapply NL_VarExp.
      * intro Hin; destruct Hin.
      * exact Hgx2.
      * intros c args Hcontra; discriminate Hcontra.
      * intro Hcontra; discriminate Hcontra.
      * intro Hcontra; discriminate Hcontra.
      * apply NL_Or. exact HNE2.
    + intro w. rewrite HeqGam1. unfold hupd. destruct (Nat.eqb w x) eqn:E.
      * reflexivity.
      * apply Heq2. exact (proj1 (Nat.eqb_neq w x) E).
Qed.

(* Lifts NEval_left_choice_as_alias_force across a whole BCase: both
   NL_Select and NL_Guess force their scrutinee `x` FIRST (as a bare `EVar
   x`), so bridging just that piece and replaying the SAME continuation
   pointwise (NEval_left_pointwise_heap) is enough -- no separate induction
   over the branch body is needed. *)
Lemma NEval_left_choice_as_alias_bcase :
  forall P x y z, x <> y ->
  forall brs Gam Gam1 v, NEval_left P nil Gam (BCase x brs) Gam1 v ->
  Gam x = Some (BExpr (EVar y)) ->
  forall Gam2, (forall w, w <> x -> Gam2 w = Gam w) -> Gam2 x = Some (BExpr (EChoice y z)) ->
  exists Gam1', NEval_left P nil Gam2 (BCase x brs) Gam1' v /\ (forall w, Gam1' w = Gam1 w).
Proof.
  intros P x y z Hxy brs Gam Gam1 v H Hgx Gam2 Heq Hgx2.
  destruct (NEval_left_bcase_shape P nil Gam x brs Gam1 v H) as
    [ [c [zs [ys [body [Gmid [Hforce [HIn [Hlen Hbody]]]]]]]]
    | [x' [Gmid [c1 [ys1 [body1 [ws [Hforce [Hhd [Hlenws [HNDws [Hfrws Hbodyguess]]]]]]]]]]] ].
  - destruct (NEval_left_choice_as_alias_force P x y z Hxy Gam Gmid (BExpr (ECon c zs)) Hforce Hgx Gam2 Heq Hgx2)
      as [Gmid' [Hforce' Heqmid]].
    destruct (NEval_left_pointwise_heap P nil Gmid (rename_b (zipsubst ys zs) body) Gam1 v Hbody Gmid' Heqmid)
      as [Gam1' [Hbody' Heqfinal]].
    exists Gam1'. split.
    + eapply NL_Select; [exact Hforce' | exact HIn | exact Hlen | exact Hbody'].
    + exact Heqfinal.
  - destruct (NEval_left_choice_as_alias_force P x y z Hxy Gam Gmid (BExpr (EVar x')) Hforce Hgx Gam2 Heq Hgx2)
      as [Gmid' [Hforce' Heqmid]].
    assert (Heqguessheap : forall w,
        hupd_list (hupd Gmid' x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
      = hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
    { apply hupd_list_pointwise. intro w. unfold hupd. destruct (Nat.eqb w x'); [reflexivity | apply Heqmid]. }
    destruct (NEval_left_pointwise_heap P nil
                (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                (rename_b (zipsubst ys1 ws) body1) Gam1 v Hbodyguess _ Heqguessheap)
      as [Gam1' [Hbodyguess' Heqfinal]].
    exists Gam1'. split.
    + eapply NL_Guess; [exact Hforce' | exact Hhd | exact Hlenws | exact HNDws | | exact Hbodyguess'].
      intros w Hw. rewrite (Heqmid w). exact (Hfrws w Hw).
    + exact Heqfinal.
Qed.

(* Small helper: forcing x0 to a genuinely free result (EVar x') rules out
   x0's own Gam-witness ever having already been an achieved constructor --
   used repeatedly below to discharge CorrE_forced_shape sub-cases that
   would otherwise require Hrec1 to reach a Con instead. *)
(* NL_Or is the sole constructor producing NEval_left ... (EChoice x y) ...,
   so this just unwraps it -- built as a dedicated lemma rather than inline
   inversion, since inversion's own auto-generated hypothesis names for a
   6-var-plus-premise constructor aren't worth hand-guessing. *)
Lemma NEval_left_echoice_shape :
  forall P F G x y G' v, NEval_left P F G (BExpr (EChoice x y)) G' v ->
  NEval_left P F G (BExpr (EVar x)) G' v.
Proof.
  intros P F G x y G' v H.
  remember (BExpr (EChoice x y)) as e eqn:He.
  destruct H as
    [ F0 G0 z c0 args0 Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec
    | F0 G0
    | F0 G0 c0 args0
    | F0 G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec
    | F0 G0 G1 z e0 k v1 HzFresh Hrec
    | F0 G0 x1 y1 G1 v1 Hrec
    | F0 G0 z c zs brs ys body G1 v1 Hrec1 HIn Hlen Hrec2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v1 ws Hrec1 Hhd Hlen HND Hfr Hrec2
    ]; try discriminate He.
  injection He as He1 He2; subst x1 y1.
  exact Hrec.
Qed.

(* NL_Fun is the sole constructor producing NEval_left ... (EFun f args) ...,
   so this just unwraps it -- same style as NEval_left_echoice_shape. *)
Lemma NEval_left_fun_shape :
  forall P F Gam f args G' v, NEval_left P F Gam (BExpr (EFun f args)) G' v ->
  exists ps body s,
    P f = Some (ps, body) /\ length ps = length args /\ injective s /\
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) /\
    (forall y, ~ In y ps -> Gam (s y) = None) /\
    NEval_left P F Gam (rename_b s body) G' v.
Proof.
  intros P F Gam f args G' v H.
  remember (BExpr (EFun f args)) as e eqn:He.
  destruct H as
    [ F0 G0 z c0 args0 Hz
    | F0 G0 z Hz
    | F0 G0 z Hz
    | F0 G0 z e0 G1 v0 HzF Hz Hne1 Hne2 Hne3 Hrec
    | F0 G0
    | F0 G0 c0 args0
    | F0 G0 G1 f1 args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec
    | F0 G0 G1 z e0 k v1 HzFresh Hrec
    | F0 G0 x1 y1 G1 v1 Hrec
    | F0 G0 z c zs brs ys body G1 v1 Hrec1 HIn Hlen Hrec2
    | F0 G0 z G1 z' c1 ys1 body1 brs G2 v1 ws Hrec1 Hhd Hlen HND Hfr Hrec2
    ]; try discriminate He.
  injection He as He1 He2; subst f1 args1.
  exists ps, body, s. repeat split; assumption.
Qed.

(* Mirrors NEval_left_fun_shape exactly, for GEval's own G_Fun. *)
Lemma GEval_fun_shape :
  forall P G f args G' v, GEval P G (BExpr (EFun f args)) G' v ->
  exists ps body s,
    P f = Some (ps, body) /\ length ps = length args /\ injective s /\
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) /\
    (forall y, ~ In y ps -> G (s y) = None) /\
    GEval P G (rename_b s body) G' v.
Proof.
  intros P G f args G' v H.
  remember (BExpr (EFun f args)) as e eqn:He.
  destruct H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f1 args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec
    | G0 G1 x0 e0 k v1 HxFresh Hrec
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1 Hrec2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec
    ]; try discriminate He.
  injection He as He1 He2; subst f1 args1.
  exists ps, body, s. repeat split; assumption.
Qed.

(* G_Var is the sole constructor producing GEval ... (BExpr (EVar x)) ...,
   and it makes NO heap change at all -- G' = G outright. *)
Lemma GEval_var_shape :
  forall P G x G' v, GEval P G (BExpr (EVar x)) G' v -> G' = G /\ v = GFwd x.
Proof.
  intros P G x G' v H.
  remember (BExpr (EVar x)) as e eqn:He.
  destruct H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f1 args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec
    | G0 G1 x0 e0 k v1 HxFresh Hrec
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1 Hrec2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec
    ]; try discriminate He.
  injection He as He1; subst x0.
  split; reflexivity.
Qed.

(* G_Choice is the sole constructor producing GEval ... (BExpr (EChoice x y)) ...,
   and it too makes NO heap change at all -- G' = G outright, mirroring
   GEval_var_shape. *)
Lemma GEval_echoice_shape :
  forall P G x y G' v, GEval P G (BExpr (EChoice x y)) G' v ->
  G' = G /\ v = GExpr (EChoice x y).
Proof.
  intros P G x y G' v H.
  remember (BExpr (EChoice x y)) as e eqn:He.
  destruct H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 x0 y0
    | G0 x0
    | G0 G1 f1 args1 ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec
    | G0 G1 x0 e0 k v1 HxFresh Hrec
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1 Hrec2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec
    ]; try discriminate He.
  injection He as He1 He2; subst x0 y0.
  split; reflexivity.
Qed.

Lemma NEval_left_evar_not_con :
  forall P F Gam x0 G' x', NEval_left P F Gam (BExpr (EVar x0)) G' (BExpr (EVar x')) ->
  forall c args, Gam x0 <> Some (BExpr (ECon c args)).
Proof.
  intros P F Gam x0 G' x' Hrec1 c args Heq.
  destruct (NEval_left_evar_shape P F Gam x0 G' (BExpr (EVar x')) Hrec1) as
    [ [Hcase1 [_ [c' [args' Heqv]]]]
    | [ [Hcase2 _]
      | [ [Hcase3 _]
        | [_ [e1 [G1' [Hz [Hne1 _]]]]]]]].
  - discriminate Heqv.
  - rewrite Heq in Hcase2; discriminate Hcase2.
  - rewrite Heq in Hcase3; discriminate Hcase3.
  - rewrite Heq in Hz. injection Hz as Hz. exact (Hne1 c args (eq_sym Hz)).
Qed.

(* rename_b/rename_e0 are simple shape-preserving homomorphisms, so an EVar
   result can only come from an EVar input -- used to recover a function
   body's own (unrenamed) shape from its renamed image. *)
Lemma rename_b_evar_preimage :
  forall s body w0, rename_b s body = BExpr (EVar w0) ->
  exists y1, body = BExpr (EVar y1) /\ s y1 = w0.
Proof.
  intros s body w0 H.
  destruct body as [z e k | z brs2 | e]; simpl in H; try discriminate H.
  destruct e as [y1 | | | y1' y2' | f' args' | c' args']; simpl in H; try discriminate H.
  injection H as H. exists y1. split; [reflexivity | exact H].
Qed.

(* Mirrors rename_b_evar_preimage, for EChoice. *)
Lemma rename_b_echoice_preimage :
  forall s body y1' y2', rename_b s body = BExpr (EChoice y1' y2') ->
  exists y1 y2, body = BExpr (EChoice y1 y2) /\ s y1 = y1' /\ s y2 = y2'.
Proof.
  intros s body y1' y2' H.
  destruct body as [z e k | z brs2 | e]; simpl in H; try discriminate H.
  destruct e as [w | | | y1 y2 | f' args' | c' args']; simpl in H; try discriminate H.
  injection H as H1 H2. exists y1, y2. split; [reflexivity | split; assumption].
Qed.

(* EXPLORATORY, INCOMPLETE (see the admitted G_CaseFun case): the Nat-heap
   half of the "second theorem" curry.v's own Theorem 2 flagged as missing --
   restricted to exactly the shape needed here (forcing a CASE SCRUTINEE
   reaches a genuinely free variable), which is what lets G_CaseFwd/
   G_CaseChoice/G_CaseCon/G_CaseConFree go through with NOTHING beyond
   HeapCorr2 + CorrE_forced_shape + the graph's own permanence facts --
   exactly mirroring GEval_case_gives_ContractLoc_deep's own induction, one
   layer at a time, using HeapCorr2 to keep the Nat-heap side in lockstep.
   Generalizing over the guard F (rather than fixing nil) is what makes the
   G_CaseFwd/G_CaseChoice recursive step free: NL_VarExp's own recursive
   premise is already under x0::F, matching the IH's own F exactly, with no
   separate "drop the guard" lemma needed.

   G_CaseFun is where this stops being free: NL_Fun's recursive premise
   fully resolves the renamed function body in ONE Nat-heap step, whereas
   the graph's own G_CaseFun only shallowly resolves it (vx) before
   recursing at the CASE level (G_CaseFwd et al.) for possibly many more
   steps.  Relating "NL_Fun forces the body to x'" to "the graph's own
   vx, chased via the continuation, reaches x' too" needs its own argument
   -- provisionally: relate NL_Fun's body-forcing to the SAME kind of
   case-dispatch correspondence this lemma already proves, but applied to a
   FRESH case wrapping the body (matching the graph's own G_CaseFun/
   G_CaseFwd recursion structurally) -- not yet built. *)
Lemma NEval_left_force_free_sound :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v ->
  forall Gam, HeapCorr2 G Gam ->
  forall F Gmid x', NEval_left P F Gam (BExpr (EVar x)) Gmid (BExpr (EVar x')) ->
  ContractLoc G' x x'.
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H as
    [ G0
    | G0
    | G0 c args
    | G0 x0 y0
    | G0 x0
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH
    | G0 x0 brs0 Hgx0
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1g IH1 Hrec2g IH2
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec IH
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec IH
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros x1 brs1 He; try discriminate He;
    injection He as He1 He2; subst x1 brs1; intros Gam HGam2 F Gmid x' Hrec1.
  - (* G_CaseBot *)
    exfalso.
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [args0 [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f0 [args0 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    subst b.
    destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hrec1) as
      [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1' [Hz [_ [_ [_ [Hrec2 _]]]]]]]]]]].
    + rewrite Hb in Hcase1; discriminate Hcase1.
    + rewrite Hb in Hcase2; discriminate Hcase2.
    + rewrite Hb in Hcase3; discriminate Hcase3.
    + rewrite Hb in Hz. injection Hz as Hz. subst e1.
      inversion Hrec2 as [ | | | | | | | | | | ]; discriminate.
  - (* G_CaseFwd *)
    assert (Hxy_neq : x0 <> y0).
    { intro Heqxy; subst y0.
      destruct (GEval_case_gives_ContractLoc P G0 x0 brs0 G1 v1
                  (G_CaseFwd P G0 x0 x0 brs0 G1 v1 Hgx0 Hrec)) as [w Hcl].
      exact (ContractLoc_no_selfFwd G0 x0 w Hcl Hgx0). }
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [args0 [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f0 [args0 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    + (* FwdHere: b = EVar yc0, which must equal the OUTER target y0 *)
      assert (Heqy : yc0 = y0) by (rewrite Hgx0 in Hgx0'; injection Hgx0' as Hgx0'; exact (eq_sym Hgx0')).
      subst yc0. subst b.
      destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hrec1) as
        [ [Hcase1 [_ [c' [args' Heqv]]]]
        | [ [Hcase2 _]
          | [ [Hcase3 _]
            | [_ [e1 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec2 _]]]]]]]]]]].
      * discriminate Heqv.
      * exfalso. rewrite Hb in Hcase2. injection Hcase2 as Hcase2. exact (Hxy_neq (eq_sym Hcase2)).
      * rewrite Hb in Hcase3; discriminate Hcase3.
      * rewrite Hb in Hz. injection Hz as Hz. subst e1.
        assert (Hcl : ContractLoc G1 y0 x') by exact (IH y0 brs0 eq_refl Gam HGam2 (x0::F) G1' x' Hrec2).
        eapply CL_Fwd; [ | exact Hcl].
        exact (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0).
    + (* FwdAchievedCon: x0 already Con, contradicting Hrec1's own free result *)
      exfalso. subst b.
      exact (NEval_left_evar_not_con P F Gam x0 Gmid x' Hrec1 c0 args0 Hb).
  - (* G_CaseFun *)
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [argsw [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f1 [args1 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [argsw [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    rewrite Hgx0 in Hgx0'. injection Hgx0' as Hgx0'1 Hgx0'2. subst f1 args1.
    subst b.
    destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hrec1) as
      [ [Hcase1 [_ [c' [args' Heqv]]]]
      | [ [Hcase2 _]
        | [ [Hcase3 _]
          | [HxF0 [e1 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec2 _]]]]]]]]]]].
    + discriminate Heqv.
    + rewrite Hb in Hcase2; discriminate Hcase2.
    + rewrite Hb in Hcase3; discriminate Hcase3.
    + rewrite Hb in Hz. injection Hz as Hz. subst e1.
      destruct (NEval_left_fun_shape P (x0::F) Gam f0 args0 G1' (BExpr (EVar x')) Hrec2)
        as [ps [body [s [HPf [Hlen [Hinj [Hmatch [Hfresh2 Hrec3]]]]]]]].
      destruct (rename_b s body) as [z e0 k | z brs2 | e0] eqn:Hbodyshape.
      * (* rename_b s body = BLet z e0 k: NL_Let picks z fresh w.r.t. Gam (via
           s); G_Fun's own s' picks fresh w.r.t. G0 instead -- s and s' can
           genuinely choose different concrete names for body's own internal
           bound variables.  Needs an alpha-renaming-invariance argument, ON TOP
           OF the universal blocker below (HeapCorr2 G1 Gam). *)
        admit.
      * (* rename_b s body = BCase z brs2: NL_Select/NL_Guess fire -- would be a
           fresh (non-inductive) application of NEval_left_force_free_sound itself
           to the embedded GEval derivation for BCase (s y1) ... inside Hrec1g
           (matching z = s y1 via the same "agree on params" argument as EVar
           below).  Blocked by the SAME universal gap as EVar/EChoice/EFun below:
           relating Hrec2g's continuation back to G2 needs HeapCorr2 G1 Gam first. *)
        admit.
      * (* rename_b s body = BExpr e0 *)
        destruct e0 as [ w0 | | | y1' y2' | f2 args2 | c1 args2 ].
        -- (* EVar w0: forcing w0 directly, guard x0::F -- matched by vx = GFwd w0
              via G_Var (body = BExpr (EVar y1) for some parameter y1, s y1 = w0).
              NOT a cheap reuse of G_CaseFwd's logic: concluding ContractLoc G2 x0 x'
              needs IH2 on Hrec2g, which needs HeapCorr2 (hupd G1 x0 (GFwd w0)) Gam'
              for some Gam' -- which needs HeapCorr2 G1 Gam first, i.e. HeapCorr2
              surviving the NESTED function-body evaluation Hrec1g : GEval P G0
              (BExpr (EFun f0 args0)) G1 vx from G0 to G1.  That is exactly the
              still-open gap NEval_left_let_chain_to_fwd/NEval_left_let_chain_to_con
              carry as an unproven raw hypothesis (G1 x = G x, "the call doesn't
              touch its own scrutinee"), and even granting it, theorem2_G_CaseFun_case's
              own matching GFwd branch needs ~100 lines of machinery
              (HeapCorr2_update_to_fwd_lazy + NEval_left_frame_guarded +
              NEval_left_pointwise_heap + HeapCorr2_update_achieved) specialized to a
              CorrV conclusion, not ContractLoc -- EXCEPT: this specific shape (body
              itself is a BARE EVar) sidesteps that gap entirely, because forcing a
              bare EVar via GEval (G_Var) makes NO heap change at all (G1 = G0
              outright), so HeapCorr2 G1 Gam is just HGam2 itself, nothing to
              re-derive. *)
           destruct (rename_b_evar_preimage s body w0 Hbodyshape) as [y1 [Hbody_eq Hsy1]].
           assert (HGamw0 : Gam w0 <> None).
           { destruct (NEval_left_evar_shape P (x0::F) Gam w0 G1' (BExpr (EVar x')) Hrec3) as
               [ [Hc1 _] | [ [Hc2 _] | [ [Hc3 _] | [_ [e1 [G1'' [Hz1 _]]]]]]];
             [ rewrite Hc1 | rewrite Hc2 | rewrite Hc3 | rewrite Hz1 ]; discriminate. }
           assert (Hy1in : In y1 ps).
           { destruct (in_dec Nat.eq_dec y1 ps) as [Hin | Hnin]; [exact Hin | ].
             exfalso. apply HGamw0. rewrite <- Hsy1. exact (Hfresh2 y1 Hnin). }
           destruct (GEval_fun_shape P G0 f0 args0 G1 vx Hrec1g) as
             [psG [bodyG [sG [HPfG [HlenG [HinjG [HmatchG [HfreshG Hrec1g']]]]]]]].
           assert (Hpp : psG = ps /\ bodyG = body).
           { rewrite HPf in HPfG. injection HPfG as HPfG1 HPfG2. split; congruence. }
           destruct Hpp as [Hpps Hbb]; subst psG bodyG.
           assert (Hssy1 : s y1 = sG y1).
           { destruct (List.In_nth_error ps y1 Hy1in) as [i Hi].
             destruct (nth_error args0 i) as [a | ] eqn:Ha.
             - rewrite (Hmatch i y1 a Hi Ha). rewrite (HmatchG i y1 a Hi Ha). reflexivity.
             - exfalso. apply nth_error_None in Ha.
               assert (Hib : i < length ps) by (apply nth_error_Some; rewrite Hi; discriminate).
               rewrite Hlen in Hib. lia. }
           assert (Hbodyshape' : rename_b sG body = BExpr (EVar w0)).
           { rewrite Hbody_eq. simpl. rewrite <- Hssy1. rewrite Hsy1. reflexivity. }
           rewrite Hbodyshape' in Hrec1g'.
           destruct (GEval_var_shape P G0 w0 G1 vx Hrec1g') as [HG1eq Hvxeq].
           rewrite HG1eq, Hvxeq in Hrec2g.
           (* Hrec1g' : GEval P G0 (BExpr (EVar w0)) G1 vx -- only G_Var matches,
              forcing G1 = G0 and vx = GFwd w0 with NO heap change at all;
              Hrec2g is rewritten (not the binders G1/vx themselves) to avoid
              disturbing w0's own name via an over-eager subst. *)
           assert (Hw0x0 : w0 <> x0).
           { intro Heq; rewrite Heq in Hrec2g.
             destruct (GEval_case_gives_ContractLoc P (hupd G0 x0 (GFwd x0)) x0 brs0 G2 v1 Hrec2g) as [ww Hcl].
             assert (Hself : (hupd G0 x0 (GFwd x0)) x0 = Some (GFwd x0))
               by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
             exact (ContractLoc_no_selfFwd (hupd G0 x0 (GFwd x0)) x0 ww Hcl Hself). }
           assert (HGam' : HeapCorr2 (hupd G0 x0 (GFwd w0)) (hupd Gam x0 (BExpr (EVar w0)))).
           { eapply HeapCorr2_update_to_fwd_lazy; [exact HGam2 | exact Hgx0 | | ].
             - intros ww Hcontra; discriminate Hcontra.
             - intros cc argsc Hcontra; discriminate Hcontra. }
           rewrite <- HG1eq, <- Hvxeq in HGam'.
           (* HGam' : HeapCorr2 (hupd G1 x0 vx) (hupd Gam x0 (BExpr (EVar w0))),
              matching IH2's own expected antecedent shape exactly. *)
           assert (Hgamx0w0 : (hupd Gam x0 (BExpr (EVar w0))) x0 = Some (BExpr (EVar w0)))
             by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
           destruct (NEval_left_evar_shape P (x0::F) Gam w0 G1' (BExpr (EVar x')) Hrec3) as
             [ [Hcase1w [_ [cw [argsw2 Heqvw]]]]
             | [ [Hcase2w [_ Heqd2]]
               | [ [Hcase3w [_ Heqd3]]
                 | [HxF0w [e1 [G1w [Hzw [Hne1w [Hne2w [Hne3w [Hrecw _]]]]]]]]]]].
           ++ discriminate Heqvw.
           ++ (* w0 self-loops in Gam: x' = w0 directly *)
              injection Heqd2 as Heqd2. subst x'.
              assert (Hgamw0self : (hupd Gam x0 (BExpr (EVar w0))) w0 = Some (BExpr (EVar w0)))
                by (rewrite (hupd_neq Gam x0 (BExpr (EVar w0)) w0 Hw0x0); exact Hcase2w).
              assert (HforceW0 : NEval_left P (x0::F) (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0)) (hupd Gam x0 (BExpr (EVar w0))) (BExpr (EVar w0))).
              { apply NL_VarSelf. exact Hgamw0self. }
              assert (HforceX0 : NEval_left P F (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar x0)) (hupd (hupd Gam x0 (BExpr (EVar w0))) x0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0))).
              { eapply NL_VarExp.
                - exact HxF0.
                - exact Hgamx0w0.
                - intros cc argsc Hcontra; discriminate Hcontra.
                - intro Hcontra; injection Hcontra as Hcontra; exact (Hw0x0 Hcontra).
                - intro Hcontra; discriminate Hcontra.
                - exact HforceW0. }
              exact (IH2 x0 brs0 eq_refl (hupd Gam x0 (BExpr (EVar w0))) HGam' F
                       (hupd (hupd Gam x0 (BExpr (EVar w0))) x0 (BExpr (EVar w0))) w0 HforceX0).
           ++ (* w0 is genuinely free in Gam: x' = w0 directly (after memoizing) *)
              injection Heqd3 as Heqd3. subst x'.
              assert (Hgamw0free : (hupd Gam x0 (BExpr (EVar w0))) w0 = Some (BExpr EFree))
                by (rewrite (hupd_neq Gam x0 (BExpr (EVar w0)) w0 Hw0x0); exact Hcase3w).
              assert (HforceW0 : NEval_left P (x0::F) (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0))
                                    (hupd (hupd Gam x0 (BExpr (EVar w0))) w0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0))).
              { apply NL_VarFree. exact Hgamw0free. }
              assert (HforceX0 : NEval_left P F (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar x0))
                                    (hupd (hupd (hupd Gam x0 (BExpr (EVar w0))) w0 (BExpr (EVar w0))) x0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0))).
              { eapply NL_VarExp.
                - exact HxF0.
                - exact Hgamx0w0.
                - intros cc argsc Hcontra; discriminate Hcontra.
                - intro Hcontra; injection Hcontra as Hcontra; exact (Hw0x0 Hcontra).
                - intro Hcontra; discriminate Hcontra.
                - exact HforceW0. }
              exact (IH2 x0 brs0 eq_refl (hupd Gam x0 (BExpr (EVar w0))) HGam' F
                       (hupd (hupd (hupd Gam x0 (BExpr (EVar w0))) w0 (BExpr (EVar w0))) x0 (BExpr (EVar w0)))
                       w0 HforceX0).
           ++ (* w0 needs further forcing: replay Hrecw (guard w0::x0::F) across the
                 x0-guarded heap update via NEval_left_frame_guarded, then wrap with
                 an outer NL_VarExp forcing w0, then another forcing x0. *)
              assert (Hex1 : forall cc argsc, BExpr (EFun f0 args0) <> BExpr (ECon cc argsc))
                by (intros cc argsc Hcontra; discriminate Hcontra).
              assert (Hex2 : BExpr (EFun f0 args0) <> BExpr (EVar x0))
                by (intro Hcontra; discriminate Hcontra).
              assert (Hex3 : BExpr (EFun f0 args0) <> BExpr EFree)
                by (intro Hcontra; discriminate Hcontra).
              assert (Hex2_1 : forall cc argsc, BExpr (EVar w0) <> BExpr (ECon cc argsc))
                by (intros cc argsc Hcontra; discriminate Hcontra).
              assert (Hex2_2 : BExpr (EVar w0) <> BExpr (EVar x0))
                by (intro Hcontra; injection Hcontra as Hcontra; exact (Hw0x0 Hcontra)).
              assert (Hex2_3 : BExpr (EVar w0) <> BExpr EFree)
                by (intro Hcontra; discriminate Hcontra).
              assert (Hagree : forall ww, ww <> x0 -> hupd Gam x0 (BExpr (EVar w0)) ww = Gam ww)
                by (intros ww Hww; exact (hupd_neq Gam x0 (BExpr (EVar w0)) ww Hww)).
              assert (Hx0in : In x0 (w0 :: x0 :: F)) by (right; left; reflexivity).
              destruct (NEval_left_frame_guarded x0 (BExpr (EFun f0 args0)) Hex1 Hex2 Hex3
                          (BExpr (EVar w0)) Hex2_1 Hex2_2 Hex2_3
                          P (w0 :: x0 :: F) Gam e1 G1w (BExpr (EVar x')) Hrecw
                          Hx0in Hb
                          (hupd Gam x0 (BExpr (EVar w0))) Hagree Hgamx0w0)
                as [Gam2w [HNE2w Heq2w]].
              assert (Hgamw0e1 : (hupd Gam x0 (BExpr (EVar w0))) w0 = Some e1)
                by (rewrite (hupd_neq Gam x0 (BExpr (EVar w0)) w0 Hw0x0); exact Hzw).
              assert (HforceW0 : NEval_left P (x0::F) (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar w0)) (hupd Gam2w w0 (BExpr (EVar x')))
                                    (BExpr (EVar x'))).
              { eapply NL_VarExp.
                - exact HxF0w.
                - exact Hgamw0e1.
                - exact Hne1w.
                - exact Hne2w.
                - exact Hne3w.
                - exact HNE2w. }
              assert (HforceX0 : NEval_left P F (hupd Gam x0 (BExpr (EVar w0)))
                                    (BExpr (EVar x0))
                                    (hupd (hupd Gam2w w0 (BExpr (EVar x'))) x0 (BExpr (EVar x')))
                                    (BExpr (EVar x'))).
              { eapply NL_VarExp.
                - exact HxF0.
                - exact Hgamx0w0.
                - intros cc argsc Hcontra; discriminate Hcontra.
                - intro Hcontra; injection Hcontra as Hcontra; exact (Hw0x0 Hcontra).
                - intro Hcontra; discriminate Hcontra.
                - exact HforceW0. }
              exact (IH2 x0 brs0 eq_refl (hupd Gam x0 (BExpr (EVar w0))) HGam' F
                       (hupd (hupd Gam2w w0 (BExpr (EVar x'))) x0 (BExpr (EVar x')))
                       x' HforceX0).
        -- (* EBot: no NEval_left rule reaches EVar x' from bare EBot -- vacuous. *)
           inversion Hrec3.
        -- (* EFree: NL_ValFree forces the result to be EFree, not EVar x' -- vacuous. *)
           inversion Hrec3.
        -- (* EChoice y1' y2': NL_Or recurses into forcing y1' -- matched by
              vx = GExpr (EChoice y1' y2') via G_Choice, which (like EVar/G_Var)
              makes NO heap change at all, sidestepping the universal blocker.
              Unlike the EVar case, x0's Gam-witness is kept AS a direct EChoice
              value (via HeapCorr2_update_to_direct, already fully generic over
              any Expr0 shape) rather than collapsed to a GFwd/EVar alias, so the
              second operand (sG y2, a graph-only variable with no guaranteed
              Nat-heap counterpart) never needs to be related to anything -- it's
              simply carried along verbatim, matching how G_CaseChoice itself
              never reads it either. *)
           destruct (rename_b_echoice_preimage s body y1' y2' Hbodyshape) as [y1 [y2 [Hbody_eq [Hsy1 Hsy2]]]].
           assert (Hforce_y1' := NEval_left_echoice_shape P (x0::F) Gam y1' y2' G1' (BExpr (EVar x')) Hrec3).
           assert (HGamy1' : Gam y1' <> None).
           { destruct (NEval_left_evar_shape P (x0::F) Gam y1' G1' (BExpr (EVar x')) Hforce_y1') as
               [ [Hc1 _] | [ [Hc2 _] | [ [Hc3 _] | [_ [e1 [G1'' [Hz1 _]]]]]]];
             [ rewrite Hc1 | rewrite Hc2 | rewrite Hc3 | rewrite Hz1 ]; discriminate. }
           assert (Hy1in : In y1 ps).
           { destruct (in_dec Nat.eq_dec y1 ps) as [Hin | Hnin]; [exact Hin | ].
             exfalso. apply HGamy1'. rewrite <- Hsy1. exact (Hfresh2 y1 Hnin). }
           destruct (GEval_fun_shape P G0 f0 args0 G1 vx Hrec1g) as
             [psG [bodyG [sG [HPfG [HlenG [HinjG [HmatchG [HfreshG Hrec1g']]]]]]]].
           assert (Hpp : psG = ps /\ bodyG = body).
           { rewrite HPf in HPfG. injection HPfG as HPfG1 HPfG2. split; congruence. }
           destruct Hpp as [Hpps Hbb]; subst psG bodyG.
           assert (Hssy1 : s y1 = sG y1).
           { destruct (List.In_nth_error ps y1 Hy1in) as [i Hi].
             destruct (nth_error args0 i) as [a | ] eqn:Ha.
             - rewrite (Hmatch i y1 a Hi Ha). rewrite (HmatchG i y1 a Hi Ha). reflexivity.
             - exfalso. apply nth_error_None in Ha.
               assert (Hib : i < length ps) by (apply nth_error_Some; rewrite Hi; discriminate).
               rewrite Hlen in Hib. lia. }
           assert (Hbodyshape' : rename_b sG body = BExpr (EChoice y1' (sG y2))).
           { rewrite Hbody_eq. simpl. rewrite <- Hssy1. rewrite Hsy1. reflexivity. }
           rewrite Hbodyshape' in Hrec1g'.
           destruct (GEval_echoice_shape P G0 y1' (sG y2) G1 vx Hrec1g') as [HG1eq Hvxeq].
           rewrite HG1eq, Hvxeq in Hrec2g.
           assert (HGam' : HeapCorr2 (hupd G0 x0 (GExpr (EChoice y1' (sG y2))))
                             (hupd Gam x0 (BExpr (EChoice y1' (sG y2))))).
           { eapply HeapCorr2_update_to_direct; [exact HGam2 | exact Hgx0 | | ].
             - intros ww Hcontra; discriminate Hcontra.
             - intros cc argsc Hcontra; discriminate Hcontra. }
           rewrite <- HG1eq, <- Hvxeq in HGam'.
           (* HGam' : HeapCorr2 (hupd G1 x0 vx) (hupd Gam x0 (BExpr (EChoice y1' (sG y2)))),
              matching IH2's own expected antecedent shape exactly. *)
           assert (Hgamx0e : (hupd Gam x0 (BExpr (EChoice y1' (sG y2)))) x0
                                = Some (BExpr (EChoice y1' (sG y2))))
             by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
           assert (Hex1 : forall cc argsc, BExpr (EFun f0 args0) <> BExpr (ECon cc argsc))
             by (intros cc argsc Hcontra; discriminate Hcontra).
           assert (Hex2 : BExpr (EFun f0 args0) <> BExpr (EVar x0))
             by (intro Hcontra; discriminate Hcontra).
           assert (Hex3 : BExpr (EFun f0 args0) <> BExpr EFree)
             by (intro Hcontra; discriminate Hcontra).
           assert (Hex2_1 : forall cc argsc, BExpr (EChoice y1' (sG y2)) <> BExpr (ECon cc argsc))
             by (intros cc argsc Hcontra; discriminate Hcontra).
           assert (Hex2_2 : BExpr (EChoice y1' (sG y2)) <> BExpr (EVar x0))
             by (intro Hcontra; discriminate Hcontra).
           assert (Hex2_3 : BExpr (EChoice y1' (sG y2)) <> BExpr EFree)
             by (intro Hcontra; discriminate Hcontra).
           assert (Hagree : forall ww, ww <> x0 -> hupd Gam x0 (BExpr (EChoice y1' (sG y2))) ww = Gam ww)
             by (intros ww Hww; exact (hupd_neq Gam x0 (BExpr (EChoice y1' (sG y2))) ww Hww)).
           assert (HxF0in : In x0 (x0::F)) by (left; reflexivity).
           destruct (NEval_left_frame_guarded x0 (BExpr (EFun f0 args0)) Hex1 Hex2 Hex3
                       (BExpr (EChoice y1' (sG y2))) Hex2_1 Hex2_2 Hex2_3
                       P (x0::F) Gam (BExpr (EVar y1')) G1' (BExpr (EVar x')) Hforce_y1'
                       HxF0in Hb
                       (hupd Gam x0 (BExpr (EChoice y1' (sG y2)))) Hagree Hgamx0e)
             as [Gam2' [HNE2' Heq2']].
           assert (HforceX0 : NEval_left P F (hupd Gam x0 (BExpr (EChoice y1' (sG y2))))
                                 (BExpr (EVar x0)) (hupd Gam2' x0 (BExpr (EVar x')))
                                 (BExpr (EVar x'))).
           { eapply NL_VarExp.
             - exact HxF0.
             - exact Hgamx0e.
             - intros cc argsc Hcontra; discriminate Hcontra.
             - intro Hcontra; discriminate Hcontra.
             - intro Hcontra; discriminate Hcontra.
             - apply NL_Or. exact HNE2'. }
           exact (IH2 x0 brs0 eq_refl (hupd Gam x0 (BExpr (EChoice y1' (sG y2)))) HGam' F
                    (hupd Gam2' x0 (BExpr (EVar x'))) x' HforceX0).
        -- (* EFun f2 args2: NL_Fun fires again, one level deeper -- structural
              recursion on the SAME argument (Hrec3 is strictly smaller), which
              would need a separate nested/well-founded induction on Hrec3 itself
              (the outer induction here is on H : GEval ... (BCase x brs) ..., not
              on Hrec3).  ALSO blocked by the same universal HeapCorr2 G1 Gam gap
              as EVar above, independently of the induction-setup issue. *)
           admit.
        -- (* ECon c1 args2: NL_ValCon forces Con, not EVar x' -- vacuous. *)
           inversion Hrec3.
  - (* G_CaseChoice *)
    assert (Hxy_neq : x0 <> y0).
    { intro Heqxy; subst y0.
      destruct (GEval_case_gives_ContractLoc P (hupd G0 x0 (GFwd x0)) x0 brs0 G1 v1 Hrec) as [w Hcl].
      assert (Hself : (hupd G0 x0 (GFwd x0)) x0 = Some (GFwd x0))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      exact (ContractLoc_no_selfFwd (hupd G0 x0 (GFwd x0)) x0 w Hcl Hself). }
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [args0 [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f0 [args0 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    rewrite Hgx0 in Hgx0'. injection Hgx0' as Hgx0' Hgz0'. subst y1 y2.
    subst b.
    destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hrec1) as
      [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec2 _]]]]]]]]]]].
    + rewrite Hb in Hcase1; discriminate Hcase1.
    + rewrite Hb in Hcase2; discriminate Hcase2.
    + rewrite Hb in Hcase3; discriminate Hcase3.
    + rewrite Hb in Hz. injection Hz as Hz. subst e1.
      (* e0 = EChoice y0 z0 forces via NL_Or, always the LEFT operand y0, under
         guard x0::F.  IH itself needs HeapCorr2 relative to the GRAPH-level
         update (x0 : EChoice -> GFwd y0), matched by moving to the Nat-heap
         where x0 : EVar y0 too -- x0's own slot is never actually read while
         forcing y0 (it's guarded), so NEval_left_frame_guarded transports the
         SAME derivation across that heap change for free. *)
      assert (Hrec3 := NEval_left_echoice_shape P (x0::F) Gam y0 z0 G1' (BExpr (EVar x')) Hrec2).
      assert (HGam2' : HeapCorr2 (hupd G0 x0 (GFwd y0)) (hupd Gam x0 (BExpr (EVar y0)))).
      { eapply HeapCorr2_update_to_fwd_lazy; [exact HGam2 | exact Hgx0 | | ].
        - intros w Hcontra; discriminate Hcontra.
        - intros c' args' Hcontra; discriminate Hcontra. }
      assert (Hex1 : forall c' args', BExpr (EChoice y0 z0) <> BExpr (ECon c' args'))
        by (intros c' args' Hcontra; discriminate Hcontra).
      assert (Hex2 : BExpr (EChoice y0 z0) <> BExpr (EVar x0)) by (intro Hcontra; discriminate Hcontra).
      assert (Hex3 : BExpr (EChoice y0 z0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
      assert (Hex2_1 : forall c' args', BExpr (EVar y0) <> BExpr (ECon c' args'))
        by (intros c' args' Hcontra; discriminate Hcontra).
      assert (Hex2_2 : BExpr (EVar y0) <> BExpr (EVar x0))
        by (intro Hcontra; injection Hcontra as Hcontra; exact (Hxy_neq (eq_sym Hcontra))).
      assert (Hex2_3 : BExpr (EVar y0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
      assert (HxF : In x0 (x0::F)) by (left; reflexivity).
      assert (Hgamx0eq : hupd Gam x0 (BExpr (EVar y0)) x0 = Some (BExpr (EVar y0)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      destruct (NEval_left_frame_guarded x0 (BExpr (EChoice y0 z0)) Hex1 Hex2 Hex3
                  (BExpr (EVar y0)) Hex2_1 Hex2_2 Hex2_3
                  P (x0::F) Gam (BExpr (EVar y0)) G1' (BExpr (EVar x')) Hrec3 HxF Hb
                  (hupd Gam x0 (BExpr (EVar y0)))
                  (fun w Hw => hupd_neq Gam x0 (BExpr (EVar y0)) w Hw) Hgamx0eq)
        as [Gam2' [Hrec3' _]].
      assert (Hcl : ContractLoc G1 y0 x')
        by exact (IH y0 brs0 eq_refl (hupd Gam x0 (BExpr (EVar y0))) HGam2' (x0::F) Gam2' x' Hrec3').
      assert (Hxfwd : G1 x0 = Some (GFwd y0)).
      { eapply GEval_fwd_permanent; [exact Hrec | ].
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      eapply CL_Fwd; [exact Hxfwd | exact Hcl].
  - (* G_CaseCon: x0 already achieved, contradicting Hrec1's own free result *)
    exfalso.
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [args0 [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f0 [args0 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    subst b.
    exact (NEval_left_evar_not_con P F Gam x0 Gmid x' Hrec1 c0 args0 Hb).
  - (* G_CaseConFree: x0 itself is the free self-loop, x' = x0 *)
    assert (HGamx0 := proj1 HGam2 x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCEx0]].
    destruct (CorrE_forced_shape G0 x0 b HCEx0) as
      [ [c0 [args0 [Hgx0' Hbeq]]]
      | [ [Hgx0' Hbeq]
        | [ [f0 [args0 [Hgx0' Hbeq]]]
          | [ [y1 [y2 [Hgx0' Hbeq]]]
            | [ [zc0 [Hgx0' Hbeq]]
              | [ [Hgx0' Hbeq]
                | [ [yc0 [Hgx0' Hbeq]]
                  | [yc0 [zc0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
      try (rewrite Hgx0 in Hgx0'; discriminate Hgx0').
    subst b.
    destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hrec1) as
      [ [Hcase1 [_ [c' [args' Heqv]]]]
      | [ [Hcase2 [_ Heqv2]]
        | [ [Hcase3 _]
          | [_ [e1 [G1' [Hz [_ [Hne2 _]]]]]]]]].
    + discriminate Heqv.
    + injection Heqv2 as Heqv2. subst x'.
      assert (Hhit : hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws) x0
                   = Some (GExpr (ECon c1 ws))).
      { assert (Hxws : ~ In x0 ws).
        { intro Hin. specialize (Hfresh x0 Hin). congruence. }
        rewrite (hupd_list_notin ws (map (fun _ => GExpr EFree) ws) (hupd G0 x0 (GExpr (ECon c1 ws))) x0 Hxws).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      eapply CL_Here.
      exact (GEval_con_persists P
               (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
               (rename_b (zipsubst ys1 ws) body1) G1 v1 Hrec x0 c1 ws Hhit).
    + rewrite Hb in Hcase3; discriminate Hcase3.
    + exfalso. rewrite Hb in Hz. injection Hz as Hz. exact (Hne2 (eq_sym Hz)).
Admitted.

(* theorem2's actual G_CaseFwd case, wired up end to end: given the        *)
(* induction hypothesis for the y-subderivation (exactly what theorem2's     *)
(* own structural induction would hand this case), produce the matching       *)
(* witness for x.  This is the concrete, fully-assembled payoff -- for any      *)
(* Con-shaped result, G_CaseFwd closes completely under HeapCorr2, with no       *)
(* admit anywhere in this path (Nat-Guess/free-variable results aside, which      *)
(* is the one pre-existing, separate gap NEval_left_fwd_transfer still carries).  *)
(* ==================================================================== *)

Theorem theorem2_G_CaseFwd_case :
  forall P G x y brs G1 v,
  G x = Some (GFwd y) ->
  GEval P G (BCase y brs) G1 v ->
  (forall c args, CorrV G1 v (BExpr (ECon c args)) ->
    forall Gam, HeapCorr2 G Gam ->
    exists Gam', NEval_left P nil Gam (BCase y brs) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam') ->
  forall c args, CorrV G1 v (BExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam', NEval_left P nil Gam (BCase x brs) Gam' (BExpr (ECon c args)) /\ HeapCorr G1 Gam'.
Proof.
  intros P G x y brs G1 v HGx HGE IH c args Hcorr Gam HGam2.
  destruct (IH c args Hcorr Gam HGam2) as [Gam1 [HNE1 HHC1]].
  destruct (NEval_left_fwd_transfer P G Gam HGam2 x y HGx brs Gam1 (BExpr (ECon c args)) HNE1)
    as [Gam2 [HNE2 HTransfer]].
  exists Gam2. split.
  - exact HNE2.
  - apply HTransfer.
    + exact (GEval_fwd_permanent P G (BCase y brs) G1 v HGE x y HGx).
    + (* the one hypothesis NEval_left_fwd_transfer still can't derive itself
         is now PROVEN, not assumed -- NEval_left_force_free_sound, applied
         directly to the SAME GEval derivation HGE this whole case already
         has in hand.  Its own x' <> y premise isn't even needed: the graph
         fact holds unconditionally, VarSelf/VarFree's x'=y branches are
         just ContractLoc's own CL_Here (reflexive) case. *)
      intros x' Gmid' Hforce _.
      exact (NEval_left_force_free_sound P G y brs G1 v HGE Gam HGam2 nil Gmid' x' Hforce).
    + exact HHC1.
Qed.

(* ==================================================================== *)
(* G_CaseChoice.  x's OWN content starts as EChoice y z (not yet forwarding *)
(* at all) -- forcing it goes N_VarExp(x) -> NL_Or (picks y, always the      *)
(* FIRST operand, matching G_CaseChoice exactly) -> force EVar y.  Mirrors    *)
(* NEval_left_fwd_transfer_fwdhere_con's two sub-cases (y already resolved,    *)
(* y needs further forcing) closely, with one extra layer: theorem2's IH is     *)
(* naturally stated over Gam_mid = hupd Gam x (EVar y) (matching the UPDATED      *)
(* graph hupd G x (GFwd y)), so NEval_left_frame_guarded bridges "forcing y        *)
(* under guard [x] from Gam_mid" back to "...from Gam itself" once the guard        *)
(* is in place (via alias_weaken_force_y first).  The case-body replay then          *)
(* uses NEval_left_shortcut_alias exactly as fwdhere_con does, once we know           *)
(* Gmid' x = EVar y still (via alias_frozen on the inner sub-derivation, or             *)
(* trivially when y was already resolved). *)
Theorem theorem2_G_CaseChoice_case :
  forall P G x y z brs G1 v,
  x <> y ->
  G x = Some (GExpr (EChoice y z)) ->
  GEval P (hupd G x (GFwd y)) (BCase y brs) G1 v ->
  (forall c args, CorrV G1 v (BExpr (ECon c args)) ->
    forall Gam_mid, HeapCorr2 (hupd G x (GFwd y)) Gam_mid ->
    exists Gam1, NEval_left P nil Gam_mid (BCase y brs) Gam1 (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam1) ->
  forall c args, CorrV G1 v (BExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam', NEval_left P nil Gam (BCase x brs) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam'.
Proof.
  intros P G x y z brs G1 v Hxy HGx HGE IH c args Hcorr Gam HGam2.
  assert (Hgamx : Gam x = Some (BExpr (EChoice y z))).
  { assert (HGamx := proj1 HGam2 x). rewrite HGx in HGamx. destruct HGamx as [b [Hb HCE]].
    assert (Hbeq : b = let_content x (EChoice y z)) by (eapply CorrE_direct_unique; [exact HGx | exact HCE]).
    simpl in Hbeq. subst b. exact Hb. }
  assert (HGam_mid : HeapCorr2 (hupd G x (GFwd y)) (hupd Gam x (BExpr (EVar y)))).
  { eapply HeapCorr2_update_to_fwd_lazy; [exact HGam2 | exact HGx | | ].
    - intros w Hcontra; discriminate Hcontra.
    - intros c' args' Hcontra; discriminate Hcontra. }
  destruct (IH c args Hcorr (hupd Gam x (BExpr (EVar y))) HGam_mid) as [Gam1 [HNE1 HHC1]].
  destruct (NEval_left_bcase_shape P nil (hupd Gam x (BExpr (EVar y))) y brs Gam1 (BExpr (ECon c args)) HNE1) as
    [ [c0 [zs [ys [body [Gmid' [Hrec1 [HIn [Hlen Hrec2]]]]]]]]
    | [x' [Gmid' [c1' [ys1 [body1 [ws [Hrec1 [Hhd [Hlen [HND [Hfr Hrec2]]]]]]]]]]] ].
  - (* Nat-Select : y forces (from Gam_mid) to a constructor c0 zs *)
    assert (Hgmidx : hupd Gam x (BExpr (EVar y)) x = Some (BExpr (EVar y)))
      by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
    assert (HforceY : NEval_left P (x :: nil) (hupd Gam x (BExpr (EVar y))) (BExpr (EVar y)) Gmid' (BExpr (ECon c0 zs)))
      by (exact (NEval_left_alias_weaken_force_y P x y Hxy (hupd Gam x (BExpr (EVar y))) Gmid' (BExpr (ECon c0 zs)) Hrec1 Hgmidx)).
    assert (Hex1 : forall c' args', BExpr (EVar y) <> BExpr (ECon c' args'))
      by (intros c' args' Hcontra; discriminate Hcontra).
    assert (Hex2 : BExpr (EVar y) <> BExpr (EVar x))
      by (intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra))).
    assert (Hex3 : BExpr (EVar y) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
    assert (Hex2_1 : forall c' args', BExpr (EChoice y z) <> BExpr (ECon c' args'))
      by (intros c' args' Hcontra; discriminate Hcontra).
    assert (Hex2_2 : BExpr (EChoice y z) <> BExpr (EVar x)) by (intro Hcontra; discriminate Hcontra).
    assert (Hex2_3 : BExpr (EChoice y z) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
    assert (Hagree : forall w, w <> x -> Gam w = hupd Gam x (BExpr (EVar y)) w)
      by (intros w Hwx; rewrite (hupd_neq Gam x (BExpr (EVar y)) w Hwx); reflexivity).
    destruct (NEval_left_frame_guarded x (BExpr (EVar y)) Hex1 Hex2 Hex3 (BExpr (EChoice y z)) Hex2_1 Hex2_2 Hex2_3
                P (x :: nil) (hupd Gam x (BExpr (EVar y))) (BExpr (EVar y)) Gmid' (BExpr (ECon c0 zs)) HforceY
                (or_introl eq_refl) Hgmidx Gam Hagree Hgamx)
      as [Gam_res [HNE_res Heq_res]].
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam_res x (BExpr (ECon c0 zs))) (BExpr (ECon c0 zs))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hgamx.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; discriminate Hcontra.
      - intro Hcontra; discriminate Hcontra.
      - eapply NL_Or. exact HNE_res. }
    assert (Hgmidyx : Gmid' x = Some (BExpr (EVar y))).
    { destruct (NEval_left_evar_shape P nil (hupd Gam x (BExpr (EVar y))) y Gmid' (BExpr (ECon c0 zs)) Hrec1) as
        [ [Hcase1 [HeqGmid _]]
        | [ [Hcase2 [_ Heqv]]
          | [ [Hcase3 [_ Heqv]]
            | [_ [e0 [G1y [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
      - subst Gmid'. exact Hgmidx.
      - subst Gmid'.
        assert (HG1xy : G1y x = Some (BExpr (EVar y)) /\ G1y y = Some e0).
        { exact (NEval_left_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil)
                   (hupd Gam x (BExpr (EVar y))) e0 G1y (BExpr (ECon c0 zs)) Hrec
                   (or_introl eq_refl) Hgmidx Hz). }
        rewrite (hupd_neq G1y y (BExpr (ECon c0 zs)) x Hxy). exact (proj1 HG1xy). }
    assert (Hgmidyy : Gmid' y = Some (BExpr (ECon c0 zs)))
      by (eapply NEval_left_own_slot; exact Hrec1).
    destruct (NEval_left_shortcut_alias P x y c0 zs Hxy nil Gmid' (rename_b (zipsubst ys zs) body) Gam1
                (BExpr (ECon c args)) Hrec2 (or_introl Hgmidyx) Hgmidyy) as [Gam1' [HNE2' Heq2']].
    assert (Hfullagree : forall w, hupd Gam_res x (BExpr (ECon c0 zs)) w = hupd Gmid' x (BExpr (ECon c0 zs)) w).
    { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      - subst w. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
      - rewrite (hupd_neq Gam_res x (BExpr (ECon c0 zs)) w Hnewx).
        rewrite (hupd_neq Gmid' x (BExpr (ECon c0 zs)) w Hnewx).
        exact (Heq_res w Hnewx). }
    destruct (NEval_left_pointwise_heap P nil (hupd Gmid' x (BExpr (ECon c0 zs)))
                (rename_b (zipsubst ys zs) body) Gam1' (BExpr (ECon c args)) HNE2'
                (hupd Gam_res x (BExpr (ECon c0 zs))) Hfullagree) as [Gam2'' [HNE2'' Heq2'']].
    exists Gam2''. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2''].
    + assert (Hgam1y : Gam1 y = Some (BExpr (ECon c0 zs)))
        by exact (NEval_left_con_persists P nil Gmid' (rename_b (zipsubst ys zs) body) Gam1
                    (BExpr (ECon c args)) Hrec2 y c0 zs Hgmidyy).
      assert (HCEy : CorrE G1 y (BExpr (ECon c0 zs))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC1) | exact Hgam1y]).
      destruct (CorrE_con_to_contractloc G1 y c0 zs HCEy) as [w0 [Hclw0 Hgw0]].
      assert (HGxfwd0 : (hupd G x (GFwd y)) x = Some (GFwd y))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (HG1xfwd : G1 x = Some (GFwd y))
        by exact (GEval_fwd_permanent P (hupd G x (GFwd y)) (BCase y brs) G1 v HGE x y HGxfwd0).
      assert (HHC2final : HeapCorr2 G1 (hupd Gam1 x (BExpr (ECon c0 zs)))).
      { eapply HeapCorr2_update_achieved;
          [exact HHC1 | exact HG1xfwd | exact (not_eq_sym Hxy) | exact Hclw0 | exact Hgw0 | exact Hgam1y]. }
      eapply HeapCorr2_pointwise; [exact HHC2final | ].
      intro w. rewrite (Heq2'' w). exact (Heq2' w).
  - admit.
Admitted.

(* No GEval rule's own conclusion is ever a bare GExpr(EVar _) or GExpr(EFun _ _)
   -- G_Var concludes GFwd, not GExpr(EVar _), and G_Fun always further evaluates
   its body rather than stopping at the raw call.  A clean structural fact,
   useful for ruling out two of vx's seven syntactic shapes in G_CaseFun below. *)
Lemma GEval_casebot_forces_bot :
  forall P G' x brs G2 v, GEval P G' (BCase x brs) G2 v -> G' x = Some (GExpr EBot) -> v = GExpr EBot.
Proof.
  intros P G' x brs G2 v H.
  inversion H; subst; intro Hx; congruence.
Qed.

Lemma GEval_never_var_or_fun :
  forall P G e G' v, GEval P G e G' v ->
  (forall z, v <> GExpr (EVar z)) /\ (forall f args, v <> GExpr (EFun f args)).
Proof.
  intros P G e G' v H. induction H;
    try (split; intros; discriminate); try (exact IHGEval); try assumption.
Qed.

(* ==================================================================== *)
(* G_CaseFun.  x's own content starts as EFun f args (an unevaluated call). *)
(* The graph-level result vx of evaluating that call can be Bot, Free, Con, *)
(* or Fwd y -- and, unlike G_CaseChoice, vx can NEVER be a bare EChoice      *)
(* directly (NoBareChoiceB forbids a function body from being a raw choice   *)
(* at its own top level) -- but vx = Fwd y where y's OWN canonical content    *)
(* is a raw, un-cased EChoice is perfectly realizable (e.g. body               *)
(* `let y = (p ? q) in y`), and this is exactly the scenario `force_var_left`   *)
(* cannot handle: it only knows how to chase a Fwd-chain down to a genuine       *)
(* constructor, not through an unresolved choice.  ContractLoc2N/force_var2_left  *)
(* below generalize the chase to ALSO step through EChoice's first operand        *)
(* (matching G_CaseChoice's/NL_Or's shared left-bias), closing that gap.           *)
(* ==================================================================== *)

Inductive ContractLoc2N (G : Graph) : nat -> var -> var -> Prop :=
| CL2N_Here : forall x e, G x = Some (GExpr e) -> (forall y1 y2, e <> EChoice y1 y2) ->
                ContractLoc2N G 0 x x
| CL2N_Fwd  : forall n x y z, G x = Some (GFwd y) -> ContractLoc2N G n y z ->
                ContractLoc2N G (S n) x z
| CL2N_Choice : forall n x y1 y2 z, G x = Some (GExpr (EChoice y1 y2)) -> ContractLoc2N G n y1 z ->
                ContractLoc2N G (S n) x z.

Lemma ContractLoc2N_zero : forall G x y, ContractLoc2N G 0 x y -> y = x.
Proof.
  intros G x y H. inversion H as [x0 e0 H0 H1 | | ]; subst; reflexivity.
Qed.

Lemma ContractLoc2N_succ :
  forall G n x z, ContractLoc2N G (S n) x z ->
  (exists y, G x = Some (GFwd y) /\ ContractLoc2N G n y z) \/
  (exists y1 y2, G x = Some (GExpr (EChoice y1 y2)) /\ ContractLoc2N G n y1 z).
Proof.
  intros G n x z H. inversion H as [ | n0 x0 y0 z0 H0 H1 | n0 x0 y1 y2 z0 H0 H1 ]; subst.
  - left. exists y0. split; [exact H0 | exact H1].
  - right. exists y1, y2. split; [exact H0 | exact H1].
Qed.

Lemma ContractLoc2N_functional :
  forall G n1 x y1, ContractLoc2N G n1 x y1 ->
  forall n2 y2, ContractLoc2N G n2 x y2 -> n1 = n2 /\ y1 = y2.
Proof.
  intros G n1 x y1 H. induction H as
    [ x0 e0 H0 Hne | n0 x0 y0 z0 H0 Hcl0 IH | n0 x0 y1a y2a z0 H0 Hcl0 IH ];
  intros n2 y2 H2.
  - inversion H2 as [x1 e1 H1 Hne1 | n3 x1 y3 z1 H1 Hcl1 | n3 x1 y1b y2b z1 H1 Hcl1]; subst.
    + split; reflexivity.
    + congruence.
    + congruence.
  - inversion H2 as [x1 e1 H1 Hne1 | n3 x1 y3 z1 H1 Hcl1 | n3 x1 y1b y2b z1 H1 Hcl1]; subst.
    + congruence.
    + assert (y0 = y3) by congruence. subst y3.
      destruct (IH n3 y2 Hcl1) as [Heqn Heqz]. split; congruence.
    + congruence.
  - inversion H2 as [x1 e1 H1 Hne1 | n3 x1 y3 z1 H1 Hcl1 | n3 x1 y1b y2b z1 H1 Hcl1]; subst.
    + congruence.
    + congruence.
    + assert (Heq : Some (GExpr (EChoice y1a y2a)) = Some (GExpr (EChoice y1b y2b))) by congruence.
      injection Heq as Heqy1 Heqy2. subst y1b y2b.
      destruct (IH n3 y2 Hcl1) as [Heqn Heqz]. split; congruence.
Qed.

(* A PLAIN (Fwd-only) ContractLoc chase to a NON-choice target is also a valid
   ContractLoc2N chase (with the same endpoint) -- the two relations agree
   whenever no choice-hop is actually needed. *)
(* IMPORTANT CORRECTION, discovered while trying to build a "force_var2_left"
   on top of this: chasing through a raw, un-mutated EChoice with G held
   FIXED is UNSOUND relative to HeapCorr2.  CorrE_Choice + CorrE_direct_unique
   mean that whenever G x = GExpr (EChoice y1 y2) (unmutated), ANY Gam with
   HeapCorr2 G Gam is FORCED to have Gam x = EChoice y1 y2 exactly -- there is
   no "achieved" shortcut for a direct (non-Fwd) choice node the way there is
   for a Fwd node chasing to a permanent Con (CorrE_FwdAchievedCon).  Con is
   a TERMINAL, PERMANENT graph shape; a raw choice is not -- it only becomes
   "resolved" via an EXPLICIT G_CaseChoice mutation (turning it into GFwd),
   which is a GRAPH-LEVEL event, not something NL_Or's eager natural-semantics
   resolution can retroactively justify against a graph that never performed
   it.  So ContractLoc2N/CorrE_con_progress_N2 below, while true, do NOT
   support a sound "force_var2_left" (memoizing an eagerly-resolved value
   while G still shows an unmutated choice would violate HeapCorr2 the moment
   we tried to state HeapCorr2 G Gam' for the unchanged G).  Kept here as
   honest, self-contained (if not directly useful) graph theory; see the
   comment above theorem2's G_CaseFun assembly below for the actual fix. *)

Lemma ContractLoc_to_ContractLoc2N :
  forall G x y, ContractLoc G x y ->
  forall e, G y = Some (GExpr e) -> (forall y1 y2, e <> EChoice y1 y2) ->
  exists n, ContractLoc2N G n x y.
Proof.
  intros G x y H. induction H as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH]; intros e He Hne.
  - exists 0. eapply CL2N_Here; [exact He | exact Hne].
  - destruct (IH e He Hne) as [n Hn]. exists (S n). eapply CL2N_Fwd; [exact H0 | exact Hn].
Qed.

(* Analogue of curry.v's CorrE_con_progress_N, generalized to a target y
   reached via the COMBINED (Fwd + left-Choice) chase.  Three outcomes for
   x's own CorrE witness b: it's already the target constructor; it's a lazy
   alias EVar y1 strictly closer to y (Fwd case); or x is ITSELF a raw,
   un-cased choice (b = EChoice y1 y2), in which case forcing x must recurse
   into forcing y1 (matching NL_Or's left bias) -- the one shape the ORIGINAL
   (Fwd-only) CorrE_con_progress_N never has to consider, since plain
   ContractLocN never steps through a choice at all. *)
Lemma CorrE_con_progress_N2 :
  forall G x b, CorrE G x b ->
  forall n y c args, ContractLoc2N G n x y -> G y = Some (GExpr (ECon c args)) ->
  b = BExpr (ECon c args) \/
  (exists m y1, m < n /\ b = BExpr (EVar y1) /\ ContractLoc2N G m y1 y) \/
  (exists y1 y2, b = BExpr (EChoice y1 y2) /\ G x = Some (GExpr (EChoice y1 y2)) /\ n > 0).
Proof.
  intros G x b H.
  induction H as
    [ x0 c0 args0 H0
    | x0 H0
    | x0 f0 fargs0 H0
    | x0 y1 z1 H0
    | x0 z1 H0
    | x0 H0
    | x0 y0 H0
    | x0 y0 z0 c0' args0' H0 Hcl0 Hz0
    ];
  intros n y c args Hcln Hy.
  - (* Con: x0 itself canonical *)
    left.
    assert (Hn0 : n = 0 /\ y = x0).
    { inversion Hcln as [x1 e1 H1 Hne1 | | ]; subst; [split; reflexivity | congruence | congruence]. }
    destruct Hn0 as [_ Hyx0]. subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - (* Free -- contradiction with target Con *)
    exfalso.
    assert (Hn0 : n = 0 /\ y = x0).
    { inversion Hcln as [x1 e1 H1 Hne1 | | ]; subst; [split; reflexivity | congruence | congruence]. }
    destruct Hn0 as [_ Hyx0]. subst y. rewrite H0 in Hy. discriminate.
  - (* Fun *) exfalso.
    assert (Hn0 : n = 0 /\ y = x0).
    { inversion Hcln as [x1 e1 H1 Hne1 | | ]; subst; [split; reflexivity | congruence | congruence]. }
    destruct Hn0 as [_ Hyx0]. subst y. rewrite H0 in Hy. discriminate.
  - (* Choice: x0 itself directly EChoice y1 z1 -- ContractLoc2N MUST use
       CL2N_Choice (n = S n0), recursing into y1 *)
    right; right.
    inversion Hcln as [x1 e1 H1 Hne1 | n3 x1 y3 z1' H1 Hcl1 | n3 x1 y1' y2' z1' H1 Hcl1]; subst.
    + exfalso. assert (Heqe : e1 = EChoice y1 z1) by congruence. exact (Hne1 y1 z1 Heqe).
    + congruence.
    + assert (Heq : Some (GExpr (EChoice y1 z1)) = Some (GExpr (EChoice y1' y2'))) by congruence.
      injection Heq as Heq1 Heq2. subst y1' y2'.
      exists y1, z1. split; [reflexivity | split; [exact H0 | lia]].
  - (* VarThunk *) exfalso.
    assert (Hn0 : n = 0 /\ y = x0).
    { inversion Hcln as [x1 e1 H1 Hne1 | | ]; subst; [split; reflexivity | congruence | congruence]. }
    destruct Hn0 as [_ Hyx0]. subst y. rewrite H0 in Hy. discriminate.
  - (* Bot *) exfalso.
    assert (Hn0 : n = 0 /\ y = x0).
    { inversion Hcln as [x1 e1 H1 Hne1 | | ]; subst; [split; reflexivity | congruence | congruence]. }
    destruct Hn0 as [_ Hyx0]. subst y. rewrite H0 in Hy. discriminate.
  - (* FwdHere: b = EVar y0, x0 -fwd-> y0 *)
    right; left.
    inversion Hcln as [x1 e1 H1 Hne1 | n3 x1 y3 z1 H1 Hcl1 | n3 x1 y1' y2' z1 H1 Hcl1]; subst.
    + congruence.
    + assert (y3 = y0) by congruence. subst y3.
      exists n3, y0. split; [lia | split; [reflexivity | exact Hcl1]].
    + congruence.
  - (* FwdAchievedCon: G x0 = GFwd y0, PLAIN ContractLoc G y0 z0 reaching a
       direct Con -- reconcile against the combined chase for y via
       ContractLoc_to_ContractLoc2N + functionality. *)
    left.
    inversion Hcln as [x1 e1 H1 Hne1 | n3 x1 y3 z1 H1 Hcl1 | n3 x1 y1' y2' z1 H1 Hcl1]; subst.
    + congruence.
    + assert (y3 = y0) by congruence. subst y3.
      assert (Hnec : forall y1 y2, ECon c0' args0' <> EChoice y1 y2)
        by (intros y1 y2 Hcontra; discriminate Hcontra).
      destruct (ContractLoc_to_ContractLoc2N G y0 z0 Hcl0 (ECon c0' args0') Hz0 Hnec) as [m Hm2].
      destruct (ContractLoc2N_functional G m y0 z0 Hm2 n3 y Hcl1) as [_ Heqz]. subst z0.
      rewrite Hz0 in Hy. injection Hy as Hy1 Hy2. subst c0' args0'. reflexivity.
    + congruence.
Qed.

(* ==================================================================== *)
(* theorem2's actual G_CaseFun case, wired up end to end.  vx (the graph      *)
(* result of evaluating the call) is one of seven syntactic shapes; five        *)
(* are dispatched here (Bot: vacuous; Con: direct, reusing IH1 unchanged;        *)
(* EVar/EFun as a FINAL value: impossible, GEval_never_var_or_fun), leaving       *)
(* two admits: Free (the pre-existing, separate Nat-Guess gap) and EChoice        *)
(* (ruled out for well-formed programs by NoBareChoiceB, which is not carried      *)
(* as a hypothesis here).  The interesting case, Fwd y, is the one this whole       *)
(* session's remaining work was for: NEval_left_let_chain_to_fwd unwinds the         *)
(* call's own G_Fun/G_Let derivation into a matching NL_Fun/NL_Let construction,      *)
(* IH2 (applied uniformly to the case-continuation, regardless of vx's shape)          *)
(* supplies the ALREADY-RESOLVED "case x via brs" derivation from a hypothetical        *)
(* Gam_mid (x aliasing y), and NEval_left_alias_weaken_force_y_F + frame_guarded         *)
(* bridge the two back together -- exactly theorem2_G_CaseChoice_case's own Nat-          *)
(* Select pattern, with NL_Fun's let-chain in place of NL_Or.                              *)
(* ==================================================================== *)

Theorem theorem2_G_CaseFun_case :
  forall P G x f args brs G1 vx G2 v,
  G x = Some (GExpr (EFun f args)) ->
  GEval P G (BExpr (EFun f args)) G1 vx ->
  G1 x = G x ->
  WellFoundedFwd G ->
  GEval P (hupd G1 x vx) (BCase x brs) G2 v ->
  (forall c args', CorrV G1 vx (BExpr (ECon c args')) ->
    forall Gam, HeapCorr2 G Gam ->
    exists Gam1, NEval_left P nil Gam (BExpr (EFun f args)) Gam1 (BExpr (ECon c args')) /\ HeapCorr2 G1 Gam1) ->
  (forall Gam1, HeapCorr2 (hupd G1 x vx) Gam1 ->
    forall c args', CorrV G2 v (BExpr (ECon c args')) ->
    exists Gam2, NEval_left P nil Gam1 (BCase x brs) Gam2 (BExpr (ECon c args')) /\ HeapCorr2 G2 Gam2) ->
  forall c args', CorrV G2 v (BExpr (ECon c args')) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam2, NEval_left P nil Gam (BCase x brs) Gam2 (BExpr (ECon c args')) /\ HeapCorr2 G2 Gam2.
Proof.
  intros P G x f args brs G1 vx G2 v HGx Hrec1 Hxeq HWF Hrec2 IH1 IH2 c args' Hcorr Gam HGam.
  destruct vx as [e0 | y].
  - destruct e0 as [ z | | | y1 y2 | f0 args0 | c0 zs0 ].
    + (* EVar z as vx: impossible, no GEval rule ever concludes GExpr(EVar _) *)
      exfalso. destruct (GEval_never_var_or_fun P G (BExpr (EFun f args)) G1 (GExpr (EVar z)) Hrec1) as [Hnv _].
      exact (Hnv z eq_refl).
    + (* EBot: Hrec2's own scrutinee is EBot, forcing v = EBot, contradicting Con *)
      exfalso.
      assert (Hxb : (hupd G1 x (GExpr EBot)) x = Some (GExpr EBot))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hvb : v = GExpr EBot) by (eapply GEval_casebot_forces_bot; [exact Hrec2 | exact Hxb]).
      subst v. inversion Hcorr.
    + (* EFree: Nat-Guess, the same pre-existing gap NEval_left_fwd_transfer carries *)
      admit.
    + (* EChoice: ruled out for well-formed programs by NoBareChoiceB, not assumed here *)
      admit.
    + (* EFun as vx: impossible, G_Fun always further evaluates its body *)
      exfalso. destruct (GEval_never_var_or_fun P G (BExpr (EFun f args)) G1 (GExpr (EFun f0 args0)) Hrec1) as [_ Hnf].
      exact (Hnf f0 args0 eq_refl).
    + (* ECon c0 zs0: direct, via the let-chain unwinding at guard [x], then IH2 *)
      assert (Hxdom : G x <> None) by congruence.
      destruct (NEval_left_let_chain_to_con P G (BExpr (EFun f args)) G1 c0 zs0 Hrec1
                  Gam HGam HWF x Hxdom Hxeq (x :: nil)) as [Gam1 [HHC1 [Hgx1 HNE1]]].
      assert (Hgold : G1 x = Some (GExpr (EFun f args))) by (rewrite Hxeq; exact HGx).
      assert (HHCd : HeapCorr2 (hupd G1 x (GExpr (ECon c0 zs0))) (hupd Gam1 x (BExpr (ECon c0 zs0)))).
      { eapply HeapCorr2_update_to_direct; [exact HHC1 | exact Hgold | | ].
        - intros w Hcontra; discriminate Hcontra.
        - intros c' args'' Hcontra; discriminate Hcontra. }
      destruct (IH2 (hupd Gam1 x (BExpr (ECon c0 zs0))) HHCd c args' Hcorr) as [Gam2 [HNE2 HHC2]].
      exists Gam2. split; [ | exact HHC2].
      assert (Hb : Gam x = Some (BExpr (EFun f args)))
        by (assert (Hb0 := Gam_from_direct G x (EFun f args) HGx Gam (proj1 HGam)); exact Hb0).
      assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam1 x (BExpr (ECon c0 zs0))) (BExpr (ECon c0 zs0))).
      { eapply NL_VarExp.
        - intro Hin; destruct Hin.
        - exact Hb.
        - intros c' args'' Heq; discriminate.
        - intro Heq; discriminate.
        - intro Heq; discriminate.
        - exact HNE1. }
      assert (Hxeqc : (hupd Gam1 x (BExpr (ECon c0 zs0))) x = Some (BExpr (ECon c0 zs0)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      destruct (NEval_left_bcase_shape P nil (hupd Gam1 x (BExpr (ECon c0 zs0))) x brs Gam2
                  (BExpr (ECon c args')) HNE2) as
        [ [c1 [zs1 [ys1 [body1 [Gmid1 [Hrec1' [HIn1 [Hlen1 Hrec2']]]]]]]]
        | [x' [Gmid1 [c1' [ys1' [body1' [ws [Hrec1' [Hhd1 [Hlen1' [HND1 [Hfr1 Hrec2']]]]]]]]]]] ].
      * destruct (NEval_left_evar_shape P nil (hupd Gam1 x (BExpr (ECon c0 zs0))) x Gmid1
                    (BExpr (ECon c1 zs1)) Hrec1') as
          [ [Hcase1 [HeqGmid _]]
          | [ [Hcase2 [_ Heqv]]
            | [ [Hcase3 [_ Heqv]]
              | [_ [e1 [G1x [Hz1 [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
        -- rewrite Hxeqc in Hcase1. injection Hcase1 as Heqc1 Heqzs1. subst c1 zs1 Gmid1.
           eapply NL_Select; [exact HforceX | exact HIn1 | exact Hlen1 | exact Hrec2'].
        -- exfalso. rewrite Hxeqc in Hz1. injection Hz1 as Heqz1. exact (Hne1 c0 zs0 (eq_sym Heqz1)).
      * exfalso.
        destruct (NEval_left_evar_shape P nil (hupd Gam1 x (BExpr (ECon c0 zs0))) x Gmid1
                    (BExpr (EVar x')) Hrec1') as
          [ [Hcase1 [_ [c1'' [args1'' Heqv]]]]
          | [ [Hcase2 [_ Heqv]]
            | [ [Hcase3 [_ Heqv]]
              | [_ [e1 [G1x [Hz1 [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
        -- rewrite Hxeqc in Hcase2. discriminate Hcase2.
        -- rewrite Hxeqc in Hcase3. discriminate Hcase3.
        -- rewrite Hxeqc in Hz1. injection Hz1 as Heqz1. exact (Hne1 c0 zs0 (eq_sym Heqz1)).
  - (* GFwd y: the main construction, mirroring theorem2_G_CaseChoice_case's own
       Nat-Select pattern with the let-chain (Hplug) standing in for NL_Or. *)
    assert (Hxy : x <> y).
    (* Self-forwarding (x's own call resolving back to x) would force Hrec2 to
       contain an equal copy of itself (G_CaseFwd's recursive premise would be
       the identical goal) -- impossible for a finite derivation, same
       termination argument as the G1 x = G x assumption. *)
    { admit. }
    assert (Hxdom : G x <> None) by congruence.
    destruct (NEval_left_let_chain_to_fwd P G (BExpr (EFun f args)) G1 y Hrec1
                Gam HGam HWF x Hxdom Hxeq) as [Gam1' [HHC1' [Hgx1' Hplug]]].
    assert (Hgold : G1 x = Some (GExpr (EFun f args))) by (rewrite Hxeq; exact HGx).
    assert (HGam_mid : HeapCorr2 (hupd G1 x (GFwd y)) (hupd Gam1' x (BExpr (EVar y)))).
    { eapply HeapCorr2_update_to_fwd_lazy; [exact HHC1' | exact Hgold | | ].
      - intros w Hcontra; discriminate Hcontra.
      - intros c' args'' Hcontra; discriminate Hcontra. }
    destruct (IH2 (hupd Gam1' x (BExpr (EVar y))) HGam_mid c args' Hcorr) as [Gam2_res [HNE2_res HHC2_res]].
    destruct (NEval_left_bcase_shape P nil (hupd Gam1' x (BExpr (EVar y))) x brs Gam2_res
                (BExpr (ECon c args')) HNE2_res) as
      [ [c0 [zs0 [ys0 [body0 [Gmid'' [Hrec1'' [HIn'' [Hlen'' Hrec2'']]]]]]]]
      | [x' [Gmid'' [c1' [ys1' [body1' [ws [Hrec1'' [Hhd'' [Hlen1' [HND'' [Hfr'' Hrec2'']]]]]]]]]]] ].
    + (* Nat-Select : x forces (from Gam_mid) via its alias to y, to a constructor c0 zs0.
         Unlike theorem2_G_CaseChoice_case (which decomposes CASING y, the deeper
         location), here bcase_shape already decomposed CASING x itself (x is what
         G_CaseFun/IH2 cases directly) -- so Hrec1'' is x's OWN forcing, and, since
         Gam_mid x = EVar y, evar_shape applied to IT (not y) extracts the inner
         "force y" derivation directly, ALREADY at guard [x] (no alias_weaken_force_y
         needed), and Gmid'' already has x memoized to the achieved constructor
         (no shortcut_alias/alias promotion needed either). *)
      assert (Hgmidx : hupd Gam1' x (BExpr (EVar y)) x = Some (BExpr (EVar y)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      destruct (NEval_left_evar_shape P nil (hupd Gam1' x (BExpr (EVar y))) x Gmid'' (BExpr (ECon c0 zs0)) Hrec1'') as
        [ [Hcase1 [HeqGmid _]]
        | [ [Hcase2 [_ Heqv]]
          | [ [Hcase3 [_ Heqv]]
            | [_ [e0 [G1y [Hz [Hne1 [Hne2 [Hne3 [HforceY HeqGmid]]]]]]]] ] ] ].
      1: { exfalso. rewrite Hgmidx in Hcase1. discriminate Hcase1. }
      1: { exfalso. rewrite Hgmidx in Hcase2. injection Hcase2 as Hcase2. exact (Hxy (eq_sym Hcase2)). }
      1: { exfalso. rewrite Hgmidx in Hcase3. discriminate Hcase3. }
      assert (Heqy : e0 = BExpr (EVar y)) by (rewrite Hgmidx in Hz; congruence).
      subst e0. subst Gmid''.
      assert (Hex1 : forall c' args'', BExpr (EVar y) <> BExpr (ECon c' args''))
        by (intros c' args'' Hcontra; discriminate Hcontra).
      assert (Hex2 : BExpr (EVar y) <> BExpr (EVar x))
        by (intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra))).
      assert (Hex3 : BExpr (EVar y) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
      assert (Hex2_1 : forall c' args'', BExpr (EFun f args) <> BExpr (ECon c' args''))
        by (intros c' args'' Hcontra; discriminate Hcontra).
      assert (Hex2_2 : BExpr (EFun f args) <> BExpr (EVar x)) by (intro Hcontra; discriminate Hcontra).
      assert (Hex2_3 : BExpr (EFun f args) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
      assert (Hagree : forall w, w <> x -> Gam1' w = hupd Gam1' x (BExpr (EVar y)) w)
        by (intros w Hwx; rewrite (hupd_neq Gam1' x (BExpr (EVar y)) w Hwx); reflexivity).
      assert (Hgx1'' : Gam1' x = Some (BExpr (EFun f args))).
      { rewrite Hgx1'. assert (Hb0 := Gam_from_direct G x (EFun f args) HGx Gam (proj1 HGam)). exact Hb0. }
      destruct (NEval_left_frame_guarded x (BExpr (EVar y)) Hex1 Hex2 Hex3 (BExpr (EFun f args)) Hex2_1 Hex2_2 Hex2_3
                  P (x :: nil) (hupd Gam1' x (BExpr (EVar y))) (BExpr (EVar y)) G1y (BExpr (ECon c0 zs0)) HforceY
                  (or_introl eq_refl) Hgmidx Gam1' Hagree Hgx1'')
        as [Gam_res [HNE_res Heq_res]].
      assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam_res x (BExpr (ECon c0 zs0))) (BExpr (ECon c0 zs0))).
      { eapply NL_VarExp.
        - intro Hin; destruct Hin.
        - assert (Hb0 := Gam_from_direct G x (EFun f args) HGx Gam (proj1 HGam)). exact Hb0.
        - intros c' args'' Hcontra; discriminate Hcontra.
        - intro Hcontra; discriminate Hcontra.
        - intro Hcontra; discriminate Hcontra.
        - exact (Hplug (x :: nil) Gam_res (BExpr (ECon c0 zs0)) HNE_res). }
      assert (Hgmidyy : hupd G1y x (BExpr (ECon c0 zs0)) y = Some (BExpr (ECon c0 zs0))).
      { assert (Hxy' : x <> y) by exact Hxy.
        rewrite (hupd_neq G1y x (BExpr (ECon c0 zs0)) y (not_eq_sym Hxy')).
        eapply NEval_left_own_slot. exact HforceY. }
      assert (Hfullagree : forall w, hupd Gam_res x (BExpr (ECon c0 zs0)) w = hupd G1y x (BExpr (ECon c0 zs0)) w).
      { intro w. destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
        - subst w. unfold hupd. rewrite Nat.eqb_refl. reflexivity.
        - rewrite (hupd_neq Gam_res x (BExpr (ECon c0 zs0)) w Hnewx).
          rewrite (hupd_neq G1y x (BExpr (ECon c0 zs0)) w Hnewx).
          exact (Heq_res w Hnewx). }
      destruct (NEval_left_pointwise_heap P nil (hupd G1y x (BExpr (ECon c0 zs0)))
                  (rename_b (zipsubst ys0 zs0) body0) Gam2_res (BExpr (ECon c args')) Hrec2''
                  (hupd Gam_res x (BExpr (ECon c0 zs0))) Hfullagree) as [Gam2'' [HNE2'' Heq2'']].
      exists Gam2''. split.
      * eapply NL_Select; [exact HforceX | exact HIn'' | exact Hlen'' | exact HNE2''].
      * assert (Hgam2y : Gam2_res y = Some (BExpr (ECon c0 zs0)))
          by exact (NEval_left_con_persists P nil (hupd G1y x (BExpr (ECon c0 zs0)))
                      (rename_b (zipsubst ys0 zs0) body0) Gam2_res
                      (BExpr (ECon c args')) Hrec2'' y c0 zs0 Hgmidyy).
        assert (HCEy : CorrE G2 y (BExpr (ECon c0 zs0))) by (eapply HeapCorr_Gam_CorrE; [exact (proj1 HHC2_res) | exact Hgam2y]).
        destruct (CorrE_con_to_contractloc G2 y c0 zs0 HCEy) as [w0 [Hclw0 Hgw0]].
        assert (HGxfwd0 : (hupd G1 x (GFwd y)) x = Some (GFwd y))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        assert (HG2xfwd : G2 x = Some (GFwd y))
          by exact (GEval_fwd_permanent P (hupd G1 x (GFwd y)) (BCase x brs) G2 v Hrec2 x y HGxfwd0).
        assert (HHC2final : HeapCorr2 G2 (hupd Gam2_res x (BExpr (ECon c0 zs0)))).
        { eapply HeapCorr2_update_achieved;
            [exact HHC2_res | exact HG2xfwd | exact (not_eq_sym Hxy) | exact Hclw0 | exact Hgw0 | exact Hgam2y]. }
        assert (Hgam2x : Gam2_res x = Some (BExpr (ECon c0 zs0))).
        { assert (Hgmidx0 : (hupd G1y x (BExpr (ECon c0 zs0))) x = Some (BExpr (ECon c0 zs0)))
            by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
          exact (NEval_left_con_persists P nil (hupd G1y x (BExpr (ECon c0 zs0)))
                   (rename_b (zipsubst ys0 zs0) body0) Gam2_res (BExpr (ECon c args'))
                   Hrec2'' x c0 zs0 Hgmidx0). }
        eapply HeapCorr2_pointwise; [exact HHC2final | ].
        intro w. rewrite (Heq2'' w).
        destruct (Nat.eq_dec w x) as [Heqwx | Hnewx];
          [ subst w; rewrite Hgam2x; unfold hupd; rewrite Nat.eqb_refl; reflexivity
          | rewrite (hupd_neq Gam2_res x (BExpr (ECon c0 zs0)) w Hnewx); reflexivity ].
    + admit. (* Nat-Guess: same pre-existing gap *)
Admitted.

(* ======================================================================= *)
(* theorem2 -- the MAIN RESULT this whole file is building toward,          *)
(* replacing curry.v's own (Admitted, NEval/curry.HeapCorr-based) theorem2  *)
(* -- see failed_attempts.v section 1 for that original statement and why   *)
(* it's stuck (NEval's N_Or nondeterminism vs. GEval's deterministic         *)
(* G_CaseChoice).                                                           *)
(*                                                                          *)
(* This is curry.v's theorem2, restated with NEval_left in place of NEval,  *)
(* and HeapCorr (this file's own, formerly HeapCorr3) in place of            *)
(* curry.HeapCorr -- plus a second conjunct folding in                      *)
(* NEval_left_force_free_sound's own conclusion (vacuously true whenever e   *)
(* isn't a BCase), so that a single `induction H` over ALL of GEval's 13     *)
(* constructors hands every recursive premise (G_Fun's body evaluation,      *)
(* both of G_CaseFun's sub-derivations, G_Let's continuation, ...) a strong   *)
(* enough induction hypothesis to use directly -- no separate lemma, no       *)
(* well-founded recursion needed.                                            *)
(*                                                                          *)
(* HeapCorr (not HeapCorr2) is used UNIFORMLY here, both hypothesis and      *)
(* conclusion: HeapCorr2 cannot survive as the invariant threaded through     *)
(* the induction's own IH-to-IH chaining (e.g. G_CaseFun's IH1 can only ever  *)
(* hand back HeapCorr-strength correspondence for the function-call           *)
(* sub-evaluation, since real multi-hop memoization is ordinary there, but    *)
(* IH2 would need HeapCorr2 as its OWN hypothesis if the statement used it)   *)
(* -- see failed_attempts.v section 5.                                       *)
(*                                                                          *)
(* STATUS: Admitted, not yet attempted.  The per-constructor pieces already   *)
(* proven elsewhere in this file (theorem2_G_CaseFwd_case,                   *)
(* theorem2_G_CaseChoice_case, theorem2_G_CaseFun_case,                      *)
(* NEval_left_force_free_sound's six GEval-shape cases) are HeapCorr2-based    *)
(* and would need porting to HeapCorr -- i.e. HeapCorr-analogues of the       *)
(* HeapCorr2_update_* lemma layer -- before they can be reused as branches     *)
(* of this induction directly; they remain in place as templates for that     *)
(* port, per THEOREM2_PROCESS_NOTES.md. *)
(* ======================================================================= *)

(* Two small CorrV inversion helpers, using the remember+destruct+injection
   pattern (rather than bare `inversion`, whose auto-substitution across two
   simultaneously-unified indices is unpredictable -- see
   THEOREM2_PROCESS_NOTES.md's tactics glossary). *)
Lemma CorrV_direct_eq : forall G e1 e2, CorrV G (GExpr e1) (BExpr e2) -> e1 = e2.
Proof.
  intros G e1 e2 H.
  remember (GExpr e1) as gn eqn:Hgn.
  remember (BExpr e2) as bn eqn:Hbn.
  destruct H as [e | x b Hcvt].
  - injection Hgn as Hgn. injection Hbn as Hbn. subst. reflexivity.
  - discriminate Hgn.
Qed.

Lemma CorrV_fwd_inv : forall G x b, CorrV G (GFwd x) b -> CorrVTerm G x b.
Proof.
  intros G x b H.
  remember (GFwd x) as gn eqn:Hgn.
  destruct H as [e | x0 b0 Hcvt].
  - discriminate Hgn.
  - injection Hgn as Hgn. subst x0. exact Hcvt.
Qed.

(* Source-level counterpart of NoVarThunk: "no aliasing lets" -- no BLet's
   RHS is ever a bare EVar.  Mirrors curry.v's own NoBareChoiceB exactly
   (same recursive shape, same rename/branch-inheritance lemma pattern):
   this is precisely what a compiler pass eliminating `let x = y in e`
   (substituting y for x throughout) establishes and preserves for the
   whole program.  G_Let is the only GEval rule that ever writes a literal
   Expr0 into the graph, so ruling out a bare-EVar RHS here is exactly what
   keeps NoVarThunk closed under G_Let's own graph extension. *)
Fixpoint NoAliasLetB (b : Blk) : Prop :=
  match b with
  | BLet x e k => (forall y, e <> EVar y) /\ NoAliasLetB k
  | BCase x brs =>
      fold_right (fun p acc => NoAliasLetB (match p with (_, _, bd) => bd end) /\ acc) True brs
  | BExpr e => True
  end.

Lemma NoAliasLetB_in :
  forall brs c ys bd, In (c, ys, bd) brs ->
  fold_right (fun (p : cname * list var * Blk) acc =>
                NoAliasLetB (match p with (_, _, bd0) => bd0 end) /\ acc) True brs ->
  NoAliasLetB bd.
Proof.
  induction brs as [| [[c0 ys0] bd0] brs' IH]; intros c ys bd Hin Hnal.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + injection Heq as Heq1 Heq2 Heq3; subst c0 ys0 bd0. exact (proj1 Hnal).
    + exact (IH c ys bd Hin (proj2 Hnal)).
Qed.

Lemma NoAliasLetB_rename_bound :
  forall n b, blk_size b < n -> forall s, NoAliasLetB b -> NoAliasLetB (rename_b s b).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize s Hnal.
  destruct b as [x e k | x brs | e].
  - simpl in *.
    assert (Hn : blk_size k + 1 < n) by lia.
    assert (Hm : blk_size k < blk_size k + 1) by lia.
    destruct Hnal as [Hne Hnalk].
    split.
    + destruct e as [z | | | z1 z2 | f0 args0 | c0 args0]; simpl;
        try (intro y0; discriminate).
      exfalso. exact (Hne z eq_refl).
    + exact (IHn (blk_size k + 1) Hn k Hm s Hnalk).
  - simpl in *.
    induction brs as [| [[c ys] bd] brs' IHbrs].
    + exact I.
    + simpl in Hsize.
      assert (Hbd : blk_size bd + 1 < n) by lia.
      assert (Hm : blk_size bd < blk_size bd + 1) by lia.
      assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_,_,bd0) => bd0 end) + acc) 0 brs') < n)
        by lia.
      split.
      * exact (IHn (blk_size bd + 1) Hbd bd Hm s (proj1 Hnal)).
      * apply IHbrs; [exact Hrest | exact (proj2 Hnal)].
  - exact I.
Qed.

Lemma NoAliasLetB_rename : forall s b, NoAliasLetB b -> NoAliasLetB (rename_b s b).
Proof.
  intros s b H.
  exact (NoAliasLetB_rename_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) s H).
Qed.

(* Well-formed-program counterpart of curry.v's ProgWF, for the "no
   aliasing lets" discipline: every function body is itself alias-let-free
   at every reachable position, needed to let NoAliasLetB propagate
   through G_Fun's own unfolding (rename_b), not just through the syntax
   of a single expression. *)
Definition NoAliasLetProgWF (P : Prog) : Prop :=
  forall f ps body, P f = Some (ps, body) -> NoAliasLetB body.

(* NoVarThunk is closed under G_Let's own graph extension, exactly when the
   fresh binding's RHS is itself not a bare EVar -- i.e. exactly the fact
   NoAliasLetB's BLet case supplies. *)
Lemma NoVarThunk_extend :
  forall G x e, NoVarThunk G -> G x = None -> (forall y, e <> EVar y) ->
  NoVarThunk (hupd G x (GExpr e)).
Proof.
  intros G x e Hnvt Hx Hne z w Heq.
  unfold hupd in Heq. destruct (Nat.eqb z x) eqn:Ez.
  - apply Nat.eqb_eq in Ez. subst z. injection Heq as Heq. exact (Hne w Heq).
  - exact (Hnvt z w Heq).
Qed.

(* When x's own graph slot is known NOT to be a GFwd, CorrE3's "skip-ahead"
   disjunct (whose very first conjunct requires G x = Some (GFwd _)) can
   never apply, leaving x's Gam-witness governed by plain CorrE alone --
   i.e. CorrE_forced_shape's full 8-way case split is available directly. *)
Lemma HeapCorr_witness_nonfwd :
  forall G Gam x, HeapCorr G Gam ->
  G x <> None -> (forall y0, G x <> Some (GFwd y0)) ->
  exists b, Gam x = Some b /\ CorrE G x b.
Proof.
  intros G Gam x HGam Hsome Hnofwd.
  specialize (HGam x). destruct (G x) as [gx | ] eqn:EGx; [ | exfalso; exact (Hsome eq_refl)].
  destruct HGam as [b [Hb HCE3]].
  exists b. split; [exact Hb | ].
  destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp _]]]]]].
  - exact HCE.
  - exfalso. apply (Hnofwd y1). rewrite <- EGx. exact Hgp.
Qed.

(* HeapCorr's own analogue of curry.v's CorrE_con_to_contractloc, lifted
   through HeapCorr's extra "skip-ahead" disjunct: whenever a location's
   Nat-heap witness has ALREADY been achieved to a genuine constructor,
   there is a real graph location realizing it -- either directly (plain
   CorrE, handled by the original lemma verbatim) or via the skip-ahead
   witness's own achieved target, reconciled against the direct witness by
   VarChase_functional (since Gam y = Con c args pins VarChase's own base
   case uniquely, forcing the skip-ahead witness's (c0,args0) to agree). *)
Lemma HeapCorr_con_to_contractloc :
  forall G Gam y c args, HeapCorr G Gam -> Gam y = Some (BExpr (ECon c args)) ->
  exists ytgt, ContractLoc G y ytgt /\ G ytgt = Some (GExpr (ECon c args)).
Proof.
  intros G Gam y c args HGam Hgamy.
  assert (HGamy := HGam y).
  destruct (G y) as [gy | ] eqn:EGy; [ | rewrite HGamy in Hgamy; discriminate Hgamy].
  destruct HGamy as [b [Hb HCE3]].
  rewrite Hb in Hgamy. injection Hgamy as Hgamy. subst b.
  destruct HCE3 as [HCE | [y0 [z0 [c0 [args0 [Hgy0 [Hcl0 [Hz0 HVC]]]]]]]].
  - exact (CorrE_con_to_contractloc G y c args HCE).
  - assert (HVC0 : VarChase Gam y (BExpr (ECon c args)))
      by (apply VChase_Here; [exact Hb | intros w' Hcontra; discriminate Hcontra]).
    assert (Heqcc := VarChase_functional Gam y (BExpr (ECon c args)) (BExpr (ECon c0 args0)) HVC0 HVC).
    injection Heqcc as Heqc Heqargs. subst c0 args0.
    exists z0. split; [ | exact Hz0].
    eapply CL_Fwd; [exact Hgy0 | exact Hcl0].
Qed.

(* A GFwd self-loop can never satisfy ContractLocN at all: the chase can
   only ever re-traverse the SAME edge, so it never reaches CLN_Here's own
   GExpr-shaped terminal -- proven by induction on the chase itself, with
   Hself reverted first so its own occurrence of x is safely generalized
   alongside ContractLocN's own index (avoiding the auto-substitution
   pitfall of inducting with a shared free variable still in context). *)
Lemma ContractLocN_no_selfloop :
  forall G n x z, G x = Some (GFwd x) -> ContractLocN G n x z -> False.
Proof.
  intros G n x z Hself Hcln.
  revert Hself.
  induction Hcln as [x1 e1 H1 | n1 x1 y1 z1 Hg1 Hcl1 IH]; intro Hself.
  - rewrite Hself in H1. discriminate H1.
  - rewrite Hself in Hg1. injection Hg1 as Hg1. subst y1.
    exact (IH Hself).
Qed.

(* Converse-flavored companion to HeapCorr_con_to_contractloc: whenever the
   GRAPH already shows y's own ContractLoc chase reaching an achieved
   constructor, y's Nat-heap witness (under ANY HeapCorr-satisfying Gam,
   not just ones this file happens to construct) is GUARANTEED to VarChase
   to that same value -- possibly via several hops, but never stuck at a
   raw, non-terminal shape or an unrelated location.  Proven by induction
   on the ContractLocN chase itself: the only non-trivial step is
   CorrE_FwdHere (y's own witness is the lazy 1-hop alias to its immediate
   Fwd target), which recurses via IH; CorrE_FwdAchievedCon and CorrE3's
   own disjunct 2 both terminate immediately (after reconciling against
   the KNOWN target via ContractLoc_functional / ContractLoc's own
   functionality), since they already hand back an achieved witness. *)
Lemma HeapCorr_achieved_to_VarChase :
  forall G Gam, HeapCorr G Gam ->
  forall n y z c args, ContractLocN G n y z -> G z = Some (GExpr (ECon c args)) ->
  VarChase Gam y (BExpr (ECon c args)).
Proof.
  intros G Gam HGam.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros y z c args Hcln Hz.
  destruct n as [| n0].
  - assert (Hyz : y = z) by (inversion Hcln; congruence). subst y.
    assert (HGamy := HGam z). rewrite Hz in HGamy.
    destruct HGamy as [b [Hb HCE3]].
    assert (Hbeq : b = BExpr (ECon c args)).
    { destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd _]]]]]].
      - destruct (CorrE_forced_shape G z b HCE) as
          [ [c1 [args1 [Hg1 Hb1]]]
          | [ [Hg1 Hb1]
            | [ [f1 [args1 [Hg1 Hb1]]]
              | [ [y1 [y2 [Hg1 Hb1]]]
                | [ [z1 [Hg1 Hb1]]
                  | [ [Hg1 Hb1]
                    | [ [y1 [Hg1 Hb1]]
                      | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
          rewrite Hz in Hg1; try discriminate Hg1.
        injection Hg1 as Hg1. subst c1 args1. exact Hb1.
      - rewrite Hz in Hgxfwd. discriminate Hgxfwd. }
    subst b. apply VChase_Here; [exact Hb | intros w' Hcontra; discriminate Hcontra].
  - destruct (ContractLocN_succ G n0 y z Hcln) as [y0 [Hgy Hcln0]].
    assert (Hchase_y0 : VarChase Gam y0 (BExpr (ECon c args)))
      by exact (IHn n0 (Nat.lt_succ_diag_r n0) y0 z c args Hcln0 Hz).
    assert (HGamy := HGam y). rewrite Hgy in HGamy.
    destruct HGamy as [b [Hb HCE3]].
    destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
    + destruct (CorrE_forced_shape G y b HCE) as
        [ [c1 [args1 [Hg1 Hb1]]]
        | [ [Hg1 Hb1]
          | [ [f1 [args1 [Hg1 Hb1]]]
            | [ [y1 [y2 [Hg1 Hb1]]]
              | [ [z1 [Hg1 Hb1]]
                | [ [Hg1 Hb1]
                  | [ [y1 [Hg1 Hb1]]
                    | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
        rewrite Hgy in Hg1; try discriminate Hg1.
      * injection Hg1 as Hg1. subst y1. subst b.
        eapply VChase_Hop; [exact Hb | | exact Hchase_y0].
        intro Heq; subst y0.
        exact (ContractLocN_no_selfloop G n0 y z Hgy Hcln0).
      * subst b.
        injection Hg1 as Hg1. subst y1.
        assert (Heqz : z1 = z)
          by (eapply ContractLoc_functional; [exact Hcl1 | exact (ContractLocN_to_ContractLoc G n0 y0 z Hcln0)]).
        subst z1.
        rewrite Hz in Hz1. injection Hz1 as Hz1a Hz1b. subst c1 args1.
        apply VChase_Here; [exact Hb | intros w' Hcontra; discriminate Hcontra].
    + assert (Hydeq : yd = y0).
      { rewrite Hgy in Hgxfwd. injection Hgxfwd as Hgxfwd. exact (eq_sym Hgxfwd). }
      subst yd.
      assert (Heqz : zd = z)
        by (eapply ContractLoc_functional; [exact Hcld | exact (ContractLocN_to_ContractLoc G n0 y0 z Hcln0)]).
      subst zd.
      rewrite Hz in Hzd. injection Hzd as Hzda Hzdb. subst cd argsd.
      exact HVCd.
Qed.

(* Directly OVERRIDE y's own Nat-heap slot to the achieved constructor its
   own graph chain reaches -- unlike HeapCorr_update_achieved (which
   updates a location x FORWARDING to y), this updates y ITSELF.  y's own
   new witness is justified via CorrE directly (CorrE_Con if y is itself
   the achieved location, CorrE_FwdAchievedCon if y forwards further,
   split via ContractLoc_first_hop); every OTHER location's existing
   witness survives untouched (disjunct 1 verbatim; disjunct 2 transported
   through the update via VarChase_transport_shorten, using
   HeapCorr_achieved_to_VarChase to supply the needed VarChase Gam y (Con
   c args) fact). *)
Lemma HeapCorr_set_achieved_at_target :
  forall G Gam y z c args, HeapCorr G Gam -> ContractLoc G y z -> G z = Some (GExpr (ECon c args)) ->
  HeapCorr G (hupd Gam y (BExpr (ECon c args))).
Proof.
  intros G Gam y z c args HGam Hcl Hz p.
  destruct (ContractLoc_to_N G y z Hcl) as [n Hcln].
  assert (Hchase_y : VarChase Gam y (BExpr (ECon c args)))
    by exact (HeapCorr_achieved_to_VarChase G Gam HGam n y z c args Hcln Hz).
  destruct (Nat.eq_dec p y) as [Heqpy | Hnepy].
  - subst p.
    assert (HGy : G y <> None) by exact (ContractLoc_dom G y z Hcl).
    destruct (G y) as [gy | ] eqn:EGy; [ | exfalso; exact (HGy eq_refl)].
    unfold hupd. rewrite Nat.eqb_refl.
    eexists. split; [reflexivity | ].
    left. destruct (Nat.eq_dec y z) as [Heqyz | Hneyz].
    + subst z. eapply CorrE_Con. exact Hz.
    + destruct (ContractLoc_first_hop G y z Hcl Hneyz) as [w [Hgy Hclw]].
      eapply CorrE_FwdAchievedCon; [exact Hgy | exact Hclw | exact Hz].
  - rewrite (hupd_neq Gam y (BExpr (ECon c args)) p Hnepy).
    specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp; [ | exact HGam].
    destruct HGam as [b [Hb HCE3]].
    exists b. split; [exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. exact HCE.
    + right. exists y1, z1, c1, args1.
      repeat split; try assumption.
      exact (VarChase_transport_shorten Gam y c args Hchase_y p (BExpr (ECon c1 args1)) HVC).
Qed.

(* Pointwise-heap transport for VarChase / HeapCorr -- both are defined
   purely in terms of Gam's VALUES (never its identity as a function), so
   swapping in any pointwise-equal Gam' preserves them. Needed to relate
   NEval_left_shortcut_alias's own returned heap (only known pointwise-equal
   to an hupd) back to a HeapCorr fact established directly about that hupd. *)
Lemma VarChase_pointwise :
  forall Gam Gam', (forall w, Gam' w = Gam w) ->
  forall x e, VarChase Gam x e -> VarChase Gam' x e.
Proof.
  intros Gam Gam' Heq x e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH].
  - apply VChase_Here; [rewrite Heq; exact Hb0 | exact Hself].
  - eapply VChase_Hop; [rewrite Heq; exact Hw0 | exact Hne | exact IH].
Qed.

(* Two-location generalization: if x AND y both already (via VarChase, in
   EITHER heap independently) reach the SAME Con c args, and the two heaps
   agree everywhere else, then VarChase transports between them freely --
   this is exactly the "genuine two-hop generalization" flagged as missing
   in HeapCorr_fwd_transfer_fwdhere_free's own stuck comment. Built from
   the two single-location transport lemmas above: force BOTH heaps up to
   a common "x and y both achieved" representative (two _shorten steps
   each), use VarChase_pointwise to cross between the two representatives
   (now pointwise IDENTICAL, since forcing already-achieved values at x/y
   erases whatever the two heaps disagreed about there), then peel the
   target heap's own forcing back off (two _unshorten steps) to land back
   on the ACTUAL target heap, which may still be lazy at x/y. *)
Lemma VarChase_transport_two_locations :
  forall Gam1 Gam2 x y c args, x <> y ->
  (forall w, w <> x -> w <> y -> Gam1 w = Gam2 w) ->
  VarChase Gam1 x (BExpr (ECon c args)) -> VarChase Gam1 y (BExpr (ECon c args)) ->
  VarChase Gam2 x (BExpr (ECon c args)) -> VarChase Gam2 y (BExpr (ECon c args)) ->
  forall w0 e, VarChase Gam1 w0 e -> VarChase Gam2 w0 e.
Proof.
  intros Gam1 Gam2 x y c args Hxy Heq Hc1x Hc1y Hc2x Hc2y w0 e H.
  assert (Hstep1 : VarChase (hupd Gam1 x (BExpr (ECon c args))) y (BExpr (ECon c args)))
    by exact (VarChase_transport_shorten Gam1 x c args Hc1x y (BExpr (ECon c args)) Hc1y).
  assert (H1 : VarChase (hupd (hupd Gam1 x (BExpr (ECon c args))) y (BExpr (ECon c args))) w0 e)
    by exact (VarChase_transport_shorten (hupd Gam1 x (BExpr (ECon c args))) y c args Hstep1 w0 e
                (VarChase_transport_shorten Gam1 x c args Hc1x w0 e H)).
  assert (HptwF : forall w,
             hupd (hupd Gam2 x (BExpr (ECon c args))) y (BExpr (ECon c args)) w
           = hupd (hupd Gam1 x (BExpr (ECon c args))) y (BExpr (ECon c args)) w).
  { intro w. destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
    - subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
    - rewrite (hupd_neq (hupd Gam2 x (BExpr (ECon c args))) y (BExpr (ECon c args)) w Hnewy).
      rewrite (hupd_neq (hupd Gam1 x (BExpr (ECon c args))) y (BExpr (ECon c args)) w Hnewy).
      destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      + rewrite (hupd_neq Gam2 x (BExpr (ECon c args)) w Hnewx).
        rewrite (hupd_neq Gam1 x (BExpr (ECon c args)) w Hnewx).
        exact (eq_sym (Heq w Hnewx Hnewy)). }
  assert (H2 : VarChase (hupd (hupd Gam2 x (BExpr (ECon c args))) y (BExpr (ECon c args))) w0 e)
    by exact (VarChase_pointwise _ _ HptwF w0 e H1).
  assert (Hstep2 : VarChase (hupd Gam2 x (BExpr (ECon c args))) y (BExpr (ECon c args)))
    by exact (VarChase_transport_shorten Gam2 x c args Hc2x y (BExpr (ECon c args)) Hc2y).
  assert (H3 : VarChase (hupd Gam2 x (BExpr (ECon c args))) w0 e)
    by exact (VarChase_transport_unshorten (hupd Gam2 x (BExpr (ECon c args))) y c args Hstep2
                _ w0 e H2 eq_refl).
  exact (VarChase_transport_unshorten Gam2 x c args Hc2x _ w0 e H3 eq_refl).
Qed.

Lemma HeapCorr_pointwise :
  forall G Gam Gam', HeapCorr G Gam -> (forall w, Gam' w = Gam w) -> HeapCorr G Gam'.
Proof.
  intros G Gam Gam' HGam Heq x.
  specialize (HGam x). destruct (G x) as [gx | ] eqn:EGx.
  - destruct HGam as [b [Hb HCE3]]. exists b. split.
    + rewrite Heq. exact Hb.
    + destruct HCE3 as [HCE | [y0 [z0 [c0 [args0 [Hgy0 [Hcl0 [Hz0 HVC]]]]]]]].
      * left. exact HCE.
      * right. exists y0, z0, c0, args0.
        split; [exact Hgy0 | split; [exact Hcl0 | split; [exact Hz0 |
          exact (VarChase_pointwise Gam Gam' Heq x (BExpr (ECon c0 args0)) HVC) ]]].
  - rewrite Heq. exact HGam.
Qed.

(* HeapCorr's own analogue of NEval_left_fwd_transfer_fwdhere_con: x's OWN
   Nat-heap witness is EXACTLY the one-hop alias EVar y matching its graph
   forward target (the "clean" CorrE_FwdHere case, no VarChase skip-ahead
   involved). Structurally identical to the HeapCorr2 original, except the
   final HeapCorr-preservation step routes through HeapCorr_con_to_contractloc
   + HeapCorr_update_achieved (which -- unlike the HeapCorr2 version --
   genuinely needs a VarChase Gam' x witness, since HeapCorr's own CorrE3 has
   a skip-ahead disjunct that a plain CorrE-based update doesn't: supplied
   here via NEval_left_alias_or_con_persists, run over the SAME body
   derivation that produces Gam' itself). *)
Lemma HeapCorr_fwd_transfer_fwdhere_con :
  forall P G Gam, HeapCorr G Gam ->
  forall x y, x <> y -> G x = Some (GFwd y) ->
  Gam x = Some (BExpr (EVar y)) ->
  forall brs c zs ys body Gmid Gam' v',
    NEval_left P nil Gam (BExpr (EVar y)) Gmid (BExpr (ECon c zs)) ->
    In (c, ys, body) brs ->
    length ys = length zs ->
    NEval_left P nil Gmid (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y Hxy HGx Hb brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2.
  destruct (NEval_left_evar_shape P nil Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
    [ [Hcase1 [HeqGmid _]]
    | [ [Hcase2 [_ Heqv]]
      | [ [Hcase3 [_ Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
  - subst Gmid.
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - apply NL_VarCons. exact Hcase1. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hb) Hcase1) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1x HHC2.
      destruct (NEval_left_alias_or_con_persists P x y c zs Hxy nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                  (or_introl Hb) Hcase1) as [HxAfter Hcy].
      assert (Hchase_x : VarChase Gam' x (BExpr (ECon c zs))).
      { destruct HxAfter as [Hxe | Hxe].
        - eapply VChase_Hop; [exact Hxe | exact (not_eq_sym Hxy) | apply VChase_Here; [exact Hcy | intros w' Hcontra; discriminate Hcontra] ].
        - apply VChase_Here; [exact Hxe | intros w' Hcontra; discriminate Hcontra]. }
      destruct (HeapCorr_con_to_contractloc G1v Gam' y c zs HHC2 Hcy) as [ytgt [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr G1v (hupd Gam' x (BExpr (ECon c zs))))
        by exact (HeapCorr_update_achieved G1v Gam' x y ytgt c zs HHC2 HG1x Hcl1 Hz1 Hchase_x).
      eapply HeapCorr_pointwise; [exact HHC2' | exact Heq2'].
  - subst Gmid.
    assert (HforceY : NEval_left P (x :: nil) Gam (BExpr (EVar y)) (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { exact (NEval_left_alias_weaken_force_y P x y Hxy Gam (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs)) Hrec1 Hb). }
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x))
               (hupd (hupd G1 y (BExpr (ECon c zs))) x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - exact HforceY. }
    assert (HG1xy : G1 x = Some (BExpr (EVar y)) /\ G1 y = Some e0).
    { exact (NEval_left_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil) Gam e0 G1 (BExpr (ECon c zs)) Hrec
               (or_introl eq_refl) Hb Hz). }
    destruct HG1xy as [HG1x HG1y].
    assert (Hgmidx : hupd G1 y (BExpr (ECon c zs)) x = Some (BExpr (EVar y))).
    { rewrite (hupd_neq G1 y (BExpr (ECon c zs)) x Hxy). exact HG1x. }
    assert (Hgmidy : hupd G1 y (BExpr (ECon c zs)) y = Some (BExpr (ECon c zs))).
    { unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    destruct (NEval_left_shortcut_alias P x y c zs Hxy nil (hupd G1 y (BExpr (ECon c zs)))
                (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hgmidx) Hgmidy) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply NL_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1vx HHC2.
      destruct (NEval_left_alias_or_con_persists P x y c zs Hxy nil (hupd G1 y (BExpr (ECon c zs)))
                  (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                  (or_introl Hgmidx) Hgmidy) as [HxAfter Hcy].
      assert (Hchase_x : VarChase Gam' x (BExpr (ECon c zs))).
      { destruct HxAfter as [Hxe | Hxe].
        - eapply VChase_Hop; [exact Hxe | exact (not_eq_sym Hxy) | apply VChase_Here; [exact Hcy | intros w' Hcontra; discriminate Hcontra] ].
        - apply VChase_Here; [exact Hxe | intros w' Hcontra; discriminate Hcontra]. }
      destruct (HeapCorr_con_to_contractloc G1v Gam' y c zs HHC2 Hcy) as [ytgt [Hcl1 Hz1]].
      assert (HHC2' : HeapCorr G1v (hupd Gam' x (BExpr (ECon c zs))))
        by exact (HeapCorr_update_achieved G1v Gam' x y ytgt c zs HHC2 HG1vx Hcl1 Hz1 Hchase_x).
      eapply HeapCorr_pointwise; [exact HHC2' | exact Heq2'].
Qed.

Lemma HeapCorr_fwd_transfer_fwdhere_free :
  forall P G Gam, HeapCorr G Gam ->
  forall x y, G x = Some (GFwd y) -> x <> y ->
  Gam x = Some (BExpr (EVar y)) ->
  forall brs x' c1 ys1 body1 ws Gmid Gam' v',
    NEval_left P nil Gam (BExpr (EVar y)) Gmid (BExpr (EVar x')) ->
    hd_error brs = Some (c1, ys1, body1) -> length ws = length ys1 -> NoDup ws ->
    (forall w, In w ws -> Gmid w = None) ->
    NEval_left P nil (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
               (rename_b (zipsubst ys1 ws) body1) Gam' v' ->
  exists Gam'', NEval_left P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) ->
                  (x' <> y -> ContractLoc G1 y x') ->
                  HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hxy Hb brs x' c1 ys1 body1 ws Gmid Gam' v' Hrec1 Hhd Hlen HND Hfr Hrec2.
  destruct (NEval_left_evar_shape P nil Gam y Gmid (BExpr (EVar x')) Hrec1) as
    [ [Hcase1 [HeqGmid [c'' [args'' Heqv]]]]
    | [ [Hcase2 [HeqGmid Heqv]]
      | [ [Hcase3 [HeqGmid Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ].
  - discriminate Heqv.
  - (* VarSelf: Gam y = EVar y, x' = y, Gmid = Gam *)
    injection Heqv as Heqx'. subst x'. subst Gmid.
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gam x (BExpr (EVar y))) (BExpr (EVar y))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - apply NL_VarSelf. exact Hcase2. }
    assert (Heq : forall w, hupd_list (hupd (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                    (map (fun w => BExpr (EVar w)) ws) w
                  = hupd_list (hupd Gam y (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) w).
    { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
      - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
        rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
      - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        + rewrite (hupd_neq (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          rewrite (hupd_neq Gam y (BExpr (ECon c1 ws)) w Hnewy).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          * subst w. unfold hupd; rewrite Nat.eqb_refl. exact (eq_sym Hb).
          * rewrite (hupd_neq Gam x (BExpr (EVar y)) w Hnewx). reflexivity. }
    destruct (NEval_left_pointwise_heap P nil
                (hupd_list (hupd Gam y (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                (hupd_list (hupd (hupd Gam x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                Heq)
      as [Gam2 [HNE2 HeqGam2]].
    exists Gam2. split.
    + eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
      intros w Hin.
      assert (Hwx : x <> w) by (intro Heqxw; subst w; rewrite (Hfr x Hin) in Hb; discriminate Hb).
      rewrite (hupd_neq Gam x (BExpr (EVar y)) w (not_eq_sym Hwx)). exact (Hfr w Hin).
    + intros G1v HG1x Hxfwd HHC2.
      eapply HeapCorr_pointwise; [exact HHC2 | exact HeqGam2].
  - (* VarFree: Gam y = Free, x' = y, Gmid = hupd Gam y (EVar y) *)
    injection Heqv as Heqx'. subst x'. subst Gmid.
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x))
               (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) (BExpr (EVar y))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - apply NL_VarFree. exact Hcase3. }
    assert (Heq : forall w,
              hupd_list (hupd (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                (map (fun w => BExpr (EVar w)) ws) w
              = hupd_list (hupd (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                (map (fun w => BExpr (EVar w)) ws) w).
    { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
      - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
        rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
      - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
        destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
        + rewrite (hupd_neq (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
          destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          * subst w.
            assert (HLHS : (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) x = Some (BExpr (EVar y)))
              by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
            rewrite HLHS. rewrite (hupd_neq Gam y (BExpr (EVar y)) x Hxy). exact (eq_sym Hb).
          * rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y)) w Hnewx). reflexivity. }
    destruct (NEval_left_pointwise_heap P nil
                (hupd_list (hupd (hupd Gam y (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                (hupd_list
                   (hupd (hupd (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                   (map (fun w => BExpr (EVar w)) ws))
                Heq)
      as [Gam2 [HNE2 HeqGam2]].
    exists Gam2. split.
    + eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
      intros w Hin.
      assert (Hwy : y <> w).
      { intro Heqyw; subst w. assert (Hfry := Hfr y Hin).
        assert (Hyy : (hupd Gam y (BExpr (EVar y))) y = Some (BExpr (EVar y)))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        rewrite Hyy in Hfry. discriminate Hfry. }
      assert (Hwx : x <> w).
      { intro Heqxw; subst w.
        assert (Hfrx := Hfr x Hin). rewrite (hupd_neq Gam y (BExpr (EVar y)) x Hxy) in Hfrx.
        rewrite Hfrx in Hb. discriminate Hb. }
      rewrite (hupd_neq (hupd Gam y (BExpr (EVar y))) x (BExpr (EVar y)) w (not_eq_sym Hwx)).
      rewrite (hupd_neq Gam y (BExpr (EVar y)) w (not_eq_sym Hwy)).
      assert (Hfrw := Hfr w Hin). rewrite (hupd_neq Gam y (BExpr (EVar y)) w (not_eq_sym Hwy)) in Hfrw.
      exact Hfrw.
    + intros G1v HG1x Hxfwd HHC2.
      eapply HeapCorr_pointwise; [exact HHC2 | exact HeqGam2].
  - (* VarExp: y's own content e0 needs further forcing (guard [y]),
       reaching x'.  KEY INSIGHT (from working through why z can't just be
       "still free and untouched"): Hrec2's own starting heap already shows
       y ALIASING x' (not x' being some independent, unrelated location) --
       and, once x' gets narrowed, y's own alias becomes a genuine "y aliases
       an ACHIEVED constructor" situation, valid for shortcut_alias directly.
       So we promote in two stages: first y (aliasing x', now achieved),
       then x (aliasing y, now ALSO achieved) -- both via the EXISTING
       shortcut_alias, no new "re-point an alias" machinery needed at all. *)
    assert (Hgmidx : Gmid x = Some (BExpr (EVar y)))
      by exact (NEval_left_alias_persists_through_force P x y Hxy Gam Gmid (BExpr (EVar x')) Hrec1 Hb).
    assert (Hxnotinws : ~ In x ws).
    { intro Hin. assert (Hfrx := Hfr x Hin). rewrite Hgmidx in Hfrx. discriminate Hfrx. }
    assert (Hgmidx' : Gmid x' = Some (BExpr (EVar x')))
      by exact (NEval_left_selfloop_result_persists P nil Gam (BExpr (EVar y)) Gmid x' Hrec1).
    assert (Hx'notinws : ~ In x' ws).
    { intro Hin. assert (Hfrx' := Hfr x' Hin). rewrite Hgmidx' in Hfrx'. discriminate Hfrx'. }
    assert (HforceY := NEval_left_alias_weaken_force_y P x y Hxy Gam Gmid (BExpr (EVar x')) Hrec1 Hb).
    assert (HforceX : NEval_left P nil Gam (BExpr (EVar x)) (hupd Gmid x (BExpr (EVar x'))) (BExpr (EVar x'))).
    { eapply NL_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Hcontra; discriminate Hcontra.
      - intro Hcontra; injection Hcontra as Hcontra; exact (Hxy (eq_sym Hcontra)).
      - intro Hcontra; discriminate Hcontra.
      - exact HforceY. }
    destruct (Nat.eq_dec x' y) as [Heqx'y | Hnex'y].
    + (* x' = y: y's own alias-chain loops back to itself.  Narrowing x'(=y)
         narrows y DIRECTLY, and HforceX's own output already has x = EVar y
         (matching x' = y) -- so this is really the SAME shape as the
         VarSelf/VarFree cases above: plain pointwise equality, no promotion
         (shortcut_alias) needed at all. *)
      subst x'.
      assert (Heq : forall w,
                hupd_list (hupd (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                  (map (fun w0 => BExpr (EVar w0)) ws) w
                = hupd_list (hupd Gmid y (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
      { intro w. destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
        - rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
          rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
        - rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
          destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
          + subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          + rewrite (hupd_neq (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws)) w Hnewy).
            rewrite (hupd_neq Gmid y (BExpr (ECon c1 ws)) w Hnewy).
            destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
            * subst w. unfold hupd; rewrite Nat.eqb_refl. exact (eq_sym Hgmidx).
            * rewrite (hupd_neq Gmid x (BExpr (EVar y)) w Hnewx). reflexivity. }
      destruct (NEval_left_pointwise_heap P nil
                  (hupd_list (hupd Gmid y (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (hupd_list (hupd (hupd Gmid x (BExpr (EVar y))) y (BExpr (ECon c1 ws))) ws
                     (map (fun w0 => BExpr (EVar w0)) ws))
                  Heq) as [Gam2 [HNE2 HeqGam2]].
      exists Gam2. split.
      * eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNE2].
        intros w Hin.
        assert (Hwx : x <> w).
        { intro Heqxw; subst w. assert (Hfrw := Hfr x Hin). rewrite Hgmidx in Hfrw. discriminate Hfrw. }
        rewrite (hupd_neq Gmid x (BExpr (EVar y)) w (not_eq_sym Hwx)). exact (Hfr w Hin).
      * intros G1v HG1x Hxfwd HHC2.
        eapply HeapCorr_pointwise; [exact HHC2 | exact HeqGam2].
    + (* x' <> y: y forwards through ANOTHER alias before reaching x'.
         Promote y (aliasing x', now achieved) then x (aliasing y, now also
         achieved) via shortcut_alias, twice.  Then DEMOTE back down via the
         downgrade lemma (shortcut_alias_relax), twice, to match the raw shape
         NL_Guess's own third premise structurally needs (built from
         HforceX's output, x aliasing x' directly -- and, since demoting can
         re-memoize a demoted location if the replayed derivation reads it
         again, y ALSO needs demoting a second time to undo the artifact of
         its own earlier promotion).  Finally, re-promote x and y ONE more
         time -- now directly against the TARGET heap's own KNOWN (not
         disjunctive) x'/y values -- to land on a clean, non-disjunctive
         result heap, and separately re-derive that SAME clean heap's
         HeapCorr2 directly from HeapCorr2 G1 Gam' via HeapCorr2_update_achieved,
         using the new "G1's y is never a bare var-thunk" hypothesis to rule
         out the one CorrE reading (CorrE_VarThunk) that would make this
         unsound. *)
      assert (Hgmidy : Gmid y = Some (BExpr (EVar x')))
        by (rewrite HeqGmid; unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hynotinws : ~ In y ws).
      { intro Hin. assert (Hfry := Hfr y Hin). rewrite Hgmidy in Hfry. discriminate Hfry. }
      assert (Hxx' : x <> x') by (intro Heq; subst x'; congruence).
      assert (Hy_in : hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) y
                    = Some (BExpr (EVar x'))).
      { rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ y Hynotinws).
        rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)). exact Hgmidy. }
      assert (Hx'_in : hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws) x'
                    = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x' Hx'notinws).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      destruct (NEval_left_alias_or_con_persists P y x' c1 ws (not_eq_sym Hnex'y) nil
                  (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (or_introl Hy_in) Hx'_in) as [Hgamy_disj Hgamx'_val].
      (* STEP 1: promote y *)
      destruct (NEval_left_shortcut_alias P y x' c1 ws (not_eq_sym Hnex'y) nil
                  (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                  (rename_b (zipsubst ys1 ws) body1) Gam' v' Hrec2
                  (or_introl Hy_in) Hx'_in) as [Gamy' [HNEy' Heqy']].
      (* STEP 2: promote x *)
      assert (Hx_in : hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)) x
                    = Some (BExpr (EVar y))).
      { rewrite (hupd_neq _ y (BExpr (ECon c1 ws)) x Hxy).
        rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x Hxnotinws).
        rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) x Hxx'). exact Hgmidx. }
      assert (Hy_in2 : hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)) y
                    = Some (BExpr (ECon c1 ws)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      destruct (NEval_left_shortcut_alias P x y c1 ws Hxy nil
                  (hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws)))
                  (rename_b (zipsubst ys1 ws) body1) Gamy' v' HNEy'
                  (or_introl Hx_in) Hy_in2) as [Gamx' [HNEx' Heqx'2]].
      set (Step1 := hupd (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)) y (BExpr (ECon c1 ws))) in *.
      (* STEP 3: demote x back down to EVar x' *)
      assert (HxF_nil : ~ In x (@nil var)) by (intro Hin; destruct Hin).
      assert (Hx_hit : hupd Step1 x (BExpr (ECon c1 ws)) x = Some (BExpr (ECon c1 ws)))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      assert (Hx'_step1 : Step1 x' = Some (BExpr (ECon c1 ws))).
      { unfold Step1. rewrite (hupd_neq _ y (BExpr (ECon c1 ws)) x' Hnex'y).
        rewrite (hupd_list_notin ws (map (fun w => BExpr (EVar w)) ws) _ x' Hx'notinws).
        unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      assert (Hx'_step1' : hupd Step1 x (BExpr (ECon c1 ws)) x' = Some (BExpr (ECon c1 ws)))
        by (rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) x' (not_eq_sym Hxx')); exact Hx'_step1).
      destruct (NEval_left_shortcut_alias_relax P x x' c1 ws Hxx' nil HxF_nil
                  (hupd Step1 x (BExpr (ECon c1 ws))) (rename_b (zipsubst ys1 ws) body1) Gamx' v' HNEx'
                  Hx_hit Hx'_step1') as [Gamx'' [HNEx'' [Hptwx'' _]]].
      (* STEP 4: demote y back down to EVar x' too *)
      assert (Hy_step2 : hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) y = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) y (not_eq_sym Hxy)).
        rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) y (not_eq_sym Hxy)).
        unfold Step1. unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
      assert (Hx'_step2 : hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) x' = Some (BExpr (ECon c1 ws))).
      { rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) x' (not_eq_sym Hxx')).
        rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) x' (not_eq_sym Hxx')). exact Hx'_step1. }
      assert (HyF_nil : ~ In y (@nil var)) by (intro Hin; destruct Hin).
      destruct (NEval_left_shortcut_alias_relax P y x' c1 ws (not_eq_sym Hnex'y) nil HyF_nil
                  (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) (rename_b (zipsubst ys1 ws) body1) Gamx'' v' HNEx''
                  Hy_step2 Hx'_step2) as [Gamfinal [HNEfinal [Hptwfinal _]]].
      (* bridge to TARGET, the raw heap NL_Guess's own third premise needs *)
      assert (Hcong : forall w,
          hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w
        = hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w).
      { intro w. destruct (Nat.eq_dec w y) as [Heqwy | Hnewy].
        - subst w. unfold hupd at 3; rewrite Nat.eqb_refl.
          rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ y Hynotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)).
          rewrite (hupd_neq Gmid x (BExpr (EVar x')) y (not_eq_sym Hxy)).
          exact Hgmidy.
        - destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
          + subst w.
            assert (HR : hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) x = Some (BExpr (EVar x'))).
            { rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) x Hxy).
              unfold hupd at 1; rewrite Nat.eqb_refl; reflexivity. }
            rewrite HR.
            rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotinws).
            rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) x Hxx').
            unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          + destruct (in_dec Nat.eq_dec w ws) as [Hin | Hnin].
            * rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin).
              assert (Hwy : w <> y) by (intro Heq; subst w; exact (Hynotinws Hin)).
              rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w Hwy).
              rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) w Hnewx).
              rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) w Hnewx).
              unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) w Hwy).
              rewrite (hupd_list_map_in (fun w0 => BExpr (EVar w0)) ws _ w Hin). reflexivity.
            * rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
              rewrite (hupd_neq (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')) w Hnewy).
              rewrite (hupd_neq (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x')) w Hnewx).
              rewrite (hupd_neq Step1 x (BExpr (ECon c1 ws)) w Hnewx).
              destruct (Nat.eq_dec w x') as [Heqwx' | Hnewx'].
              -- subst w. unfold hupd; rewrite Nat.eqb_refl.
                 unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) x' Hnex'y).
                 rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x' Hx'notinws).
                 unfold hupd; rewrite Nat.eqb_refl; reflexivity.
              -- rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) w Hnewx').
                 rewrite (hupd_neq Gmid x (BExpr (EVar x')) w Hnewx).
                 unfold Step1. rewrite (hupd_neq (hupd_list (hupd Gmid x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) y (BExpr (ECon c1 ws)) w Hnewy).
                 rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ w Hnin).
                 rewrite (hupd_neq Gmid x' (BExpr (ECon c1 ws)) w Hnewx'). reflexivity. }
      destruct (NEval_left_pointwise_heap P nil
                  (hupd (hupd (hupd Step1 x (BExpr (ECon c1 ws))) x (BExpr (EVar x'))) y (BExpr (EVar x')))
                  (rename_b (zipsubst ys1 ws) body1) Gamfinal v' HNEfinal
                  (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                  Hcong)
        as [Gam2raw [HNEtarget Heq2raw]].
      (* away from {x, y}, Gamfinal (hence Gam2raw) matches Gam' exactly *)
      assert (Hfinal_away : forall w, w <> x -> w <> y -> Gamfinal w = Gam' w).
      { intros w Hwx Hwy. rewrite (Hptwfinal w Hwy). rewrite (Hptwx'' w Hwx).
        rewrite (Heqx'2 w). rewrite (hupd_neq Gamy' x (BExpr (ECon c1 ws)) w Hwx).
        rewrite (Heqy' w). rewrite (hupd_neq Gam' y (BExpr (ECon c1 ws)) w Hwy). reflexivity. }
      (* HNEtarget/Gam2raw is EXACTLY the raw derivation NL_Guess needs (its
         own starting heap already matches HforceX's own output) -- no
         further promotion is needed to supply the FIRST half of the
         existential.  What remains is the SECOND half: HeapCorr, not
         HeapCorr2, since x's own final witness may legitimately still be
         the compressed alias EVar x' rather than an achieved constructor
         (see HeapCorr's own comment above for why plain CorrE has no room
         for that shape here). *)
      exists Gam2raw. split.
      * eapply NL_Guess; [exact HforceX | exact Hhd | exact Hlen | exact HND | | exact HNEtarget].
        intros w Hin.
        assert (Hwx : x <> w) by (intro Heqxw; subst w; exact (Hxnotinws Hin)).
        rewrite (hupd_neq Gmid x (BExpr (EVar x')) w (not_eq_sym Hwx)). exact (Hfr w Hin).
      * intros G1v HG1x Hxfwd HHC2.
        assert (Hcl_yx' : ContractLoc G1v y x') by exact (Hxfwd Hnex'y).
        destruct (ContractLoc_first_hop G1v y x' Hcl_yx' (not_eq_sym Hnex'y)) as [y0 [HG1y Hcl_y0x']].
        destruct (HeapCorr_con_to_contractloc G1v Gam' x' c1 ws HHC2 Hgamx'_val) as [wit [Hclwit Hgwit]].
        assert (Hcl_y : ContractLoc G1v y wit) by (eapply ContractLoc_trans; [exact Hcl_yx' | exact Hclwit]).
        assert (Hcl_y0 : ContractLoc G1v y0 wit) by (eapply ContractLoc_trans; [exact Hcl_y0x' | exact Hclwit]).
        assert (Hx'_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) x'
                       = Some (BExpr (ECon c1 ws))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x' Hx'notinws).
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        assert (Hgam2rawx' : Gam2raw x' = Some (BExpr (ECon c1 ws)))
          by exact (NEval_left_con_persists P nil
                      (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                      (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget x' c1 ws Hx'_tgt).
        assert (Hx_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) x
                       = Some (BExpr (EVar x'))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ x Hxnotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) x Hxx').
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        destruct (NEval_left_alias_or_con_persists P x x' c1 ws Hxx' nil
                    (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                    (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget
                    (or_introl Hx_tgt) Hx'_tgt) as [Hgam2rawx_disj _].
        assert (Hy_tgt : hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) y
                       = Some (BExpr (EVar x'))).
        { rewrite (hupd_list_notin ws (map (fun w0 => BExpr (EVar w0)) ws) _ y Hynotinws).
          rewrite (hupd_neq (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws)) y (not_eq_sym Hnex'y)).
          rewrite (hupd_neq Gmid x (BExpr (EVar x')) y (not_eq_sym Hxy)). exact Hgmidy. }
        destruct (NEval_left_alias_or_con_persists P y x' c1 ws (not_eq_sym Hnex'y) nil
                    (hupd_list (hupd (hupd Gmid x (BExpr (EVar x'))) x' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                    (rename_b (zipsubst ys1 ws) body1) Gam2raw v' HNEtarget
                    (or_introl Hy_tgt) Hx'_tgt) as [Hgam2rawy_disj _].
        assert (HVCy : VarChase Gam2raw y (BExpr (ECon c1 ws))).
        { destruct Hgam2rawy_disj as [Hya | Hyc].
          - eapply VChase_Hop; [exact Hya | exact Hnex'y | ].
            eapply VChase_Here; [exact Hgam2rawx' | intros w' Hcontra; discriminate Hcontra].
          - eapply VChase_Here; [exact Hyc | intros w' Hcontra; discriminate Hcontra]. }
        assert (HVCx : VarChase Gam2raw x (BExpr (ECon c1 ws))).
        { destruct Hgam2rawx_disj as [Hxa | Hxc].
          - eapply VChase_Hop; [exact Hxa | exact (not_eq_sym Hxx') | ].
            eapply VChase_Here; [exact Hgam2rawx' | intros w' Hcontra; discriminate Hcontra].
          - eapply VChase_Here; [exact Hxc | intros w' Hcontra; discriminate Hcontra]. }
        (* Gam''s own side: the SAME two-shape argument, using the Nat-heap
           persistence facts already established for the (y,x') pair
           (Hgamy_disj/Hgamx'_val) for y directly, and the graph-level
           CorrE3-forced-shape argument (only FwdHere/FwdAchievedCon are
           consistent with G1v x = GFwd y, and FwdAchievedCon's own target
           is PINNED to wit/c1/ws by ContractLoc_functional, since Hcl_y
           already witnesses y's chain reaches wit) for x. This is exactly
           the "genuine TWO-HOP generalization" the original stuck comment
           here asked for -- closed below via VarChase_transport_two_locations. *)
        assert (HVCy' : VarChase Gam' y (BExpr (ECon c1 ws))).
        { destruct Hgamy_disj as [Hya | Hyc].
          - eapply VChase_Hop; [exact Hya | exact Hnex'y | ].
            eapply VChase_Here; [exact Hgamx'_val | intros w' Hcontra; discriminate Hcontra].
          - eapply VChase_Here; [exact Hyc | intros w' Hcontra; discriminate Hcontra]. }
        assert (HVCx' : VarChase Gam' x (BExpr (ECon c1 ws))).
        { assert (HHCx := HHC2 x). rewrite HG1x in HHCx.
          destruct HHCx as [bx [Hbx HCE3x]].
          destruct HCE3x as [HCEx | [y1 [z1 [c1' [args1' [Hgx1 [Hcl1 [Hz1 HVCx0]]]]]]]].
          - destruct (CorrE_forced_shape G1v x bx HCEx) as
              [ [c0 [args0 [Hg1 Hb1]]]
              | [ [Hg1 Hb1]
                | [ [f0 [args0 [Hg1 Hb1]]]
                  | [ [y1' [y2' [Hg1 Hb1]]]
                    | [ [z0 [Hg1 Hb1]]
                      | [ [Hg1 Hb1]
                        | [ [yfh [Hg1 Hb1]]
                          | [yfa [zfa [cfa [argsfa [Hg1 [Hclfa [Hzfa Hb1]]]]]]] ] ] ] ] ] ] ];
              rewrite HG1x in Hg1; try discriminate Hg1.
            + (* FwdHere : bx = EVar y *)
              injection Hg1 as Hg1; subst yfh. rewrite Hb1 in Hbx.
              eapply VChase_Hop; [exact Hbx | exact (not_eq_sym Hxy) | exact HVCy'].
            + (* FwdAchievedCon : bx = Con cfa argsfa, cfa/argsfa PINNED to c1/ws
                 since y's own chain (Hcl_y) already reaches wit *)
              injection Hg1 as Hg1; subst yfa.
              assert (Heqz : zfa = wit) by (eapply ContractLoc_functional; [exact Hclfa | exact Hcl_y]).
              subst zfa. rewrite Hgwit in Hzfa. injection Hzfa as Hzfa1 Hzfa2. subst cfa argsfa.
              rewrite Hb1 in Hbx.
              eapply VChase_Here; [exact Hbx | intros w' Hcontra; discriminate Hcontra].
          - rewrite HG1x in Hgx1. injection Hgx1 as Hgx1. subst y1.
            assert (Heqz : z1 = wit) by (eapply ContractLoc_functional; [exact Hcl1 | exact Hcl_y]).
            subst z1. rewrite Hgwit in Hz1. injection Hz1 as Hz1a Hz1b. subst c1' args1'.
            exact HVCx0. }
        assert (Haway2 : forall w, w <> x -> w <> y -> Gam' w = Gam2raw w).
        { intros w Hwx Hwy. exact (eq_sym (eq_trans (Heq2raw w) (Hfinal_away w Hwx Hwy))). }
        intro w0. destruct (G1v w0) as [gw0 | ] eqn:HGw0.
        -- destruct (Nat.eq_dec w0 x) as [Heqw0x | Hnew0x].
           ++ subst w0. destruct Hgam2rawx_disj as [Hxa | Hxc].
              ** exists (BExpr (EVar x')). split; [exact Hxa | ].
                 right. exists y, wit, c1, ws. split; [exact HG1x | split; [exact Hcl_y | split; [exact Hgwit | ]]].
                 eapply VChase_Hop; [exact Hxa | exact (not_eq_sym Hxx') | ].
                 eapply VChase_Here; [exact Hgam2rawx' | intros w' Hcontra; discriminate Hcontra].
              ** exists (BExpr (ECon c1 ws)). split; [exact Hxc | ].
                 left. eapply CorrE_FwdAchievedCon; [exact HG1x | exact Hcl_y | exact Hgwit].
           ++ destruct (Nat.eq_dec w0 y) as [Heqw0y | Hnew0y].
              ** subst w0. destruct Hgam2rawy_disj as [Hya | Hyc].
                 { exists (BExpr (EVar x')). split; [exact Hya | ].
                   right. exists y0, wit, c1, ws. split; [exact HG1y | split; [exact Hcl_y0 | split; [exact Hgwit | exact HVCy]]]. }
                 { exists (BExpr (ECon c1 ws)). split; [exact Hyc | ].
                   left. eapply CorrE_FwdAchievedCon; [exact HG1y | exact Hcl_y0 | exact Hgwit]. }
              ** assert (HGw0' : G1v w0 = Some gw0) by exact HGw0.
                 assert (HHCw0 := HHC2 w0). rewrite HGw0' in HHCw0.
                 destruct HHCw0 as [b [Hb' HCE3]]. exists b. split.
                 { rewrite (Heq2raw w0). rewrite (Hfinal_away w0 Hnew0x Hnew0y). exact Hb'. }
                 { destruct HCE3 as [HCE | [y1 [z1 [c1' [args1' [Hgw01 [Hclw1 [Hzw1 HVCw0]]]]]]]].
                   - left. exact HCE.
                   - right. exists y1, z1, c1', args1'.
                     split; [exact Hgw01 | split; [exact Hclw1 | split; [exact Hzw1 |
                       exact (VarChase_transport_two_locations Gam' Gam2raw x y c1 ws Hxy Haway2
                                HVCx' HVCy' HVCx HVCy w0 (BExpr (ECon c1' args1')) HVCw0) ]]]. }
        -- destruct (Nat.eq_dec w0 x) as [Heqw0x | Hnew0x];
             [subst w0; rewrite HG1x in HGw0; discriminate HGw0 | ].
           destruct (Nat.eq_dec w0 y) as [Heqw0y | Hnew0y];
             [subst w0; rewrite HG1y in HGw0; discriminate HGw0 | ].
           assert (HGw0' : G1v w0 = None) by exact HGw0.
           assert (HHCw0 := HHC2 w0). rewrite HGw0' in HHCw0.
           rewrite (Heq2raw w0). rewrite (Hfinal_away w0 Hnew0x Hnew0y). exact HHCw0.
Admitted.

(* ChainConsistent, revived: whenever x forwards to y and x's OWN Nat-heap
   witness is ALREADY achieved to a constructor, y's witness must ALREADY
   be that SAME constructor too -- never still lazy.  This is the SAME
   definition dropped when HeapCorr2 was superseded by HeapCorr3/HeapCorr
   (see DEAD_ENDS.md H2/H3a for why that earlier attempt was rejected, and
   the resolution: every GFwd edge is created by a case-forcing step that
   ALSO sets the matching Gam witness to EVar y at that same moment, and
   the ONLY way x's witness can later become MORE resolved than that is by
   forcing EVar x again -- which, via NL_VarExp's own recursive structure,
   necessarily ALSO memoizes y (and every further hop) to the identical
   value.  So this is NOT the same over-strong exclusion ChainConsistent
   used to represent; it is compatible with ordinary multi-hop path
   compression, which memoizes every hop, not just the outermost one.) *)

(* Extending G at a FRESH location x can never break ChainConsistent: any
   EXISTING GFwd edge p -> q survives untouched (x is fresh, so p <> x
   trivially, and q <> x follows from WellFoundedFwd -- a dangling GFwd
   edge into the about-to-be-bound x is impossible, mirroring the old
   HeapCorr2_extend's own use of WellFoundedFwd for exactly this). *)
Lemma ChainConsistent_extend :
  forall G Gam x e, ChainConsistent G Gam -> WellFoundedFwd G -> G x = None ->
  ChainConsistent (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x e HCC HWF Hx p q Hpq c args Hpc.
  assert (Hpx : p <> x).
  { intro Heq; subst p. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq. }
  rewrite (hupd_neq G x (GExpr e) p Hpx) in Hpq.
  assert (Hqx : q <> x).
  { intro Heq; subst q.
    destruct (HWF p x Hpq) as [z Hcl].
    inversion Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0]; subst.
    - congruence.
    - assert (y0 = x) by congruence; subst y0.
      exact (ContractLoc_dom G x z Hcl0 Hx). }
  rewrite (hupd_neq Gam x (let_content x e) p Hpx) in Hpc.
  rewrite (hupd_neq Gam x (let_content x e) q Hqx).
  exact (HCC p q Hpq c args Hpc).
Qed.

(* AliasConsistent's own extend, mirroring ChainConsistent_extend exactly
   (same p<>x/q<>x argument via WellFoundedFwd -- a fresh location can
   never be an EXISTING GFwd edge's own source or target). *)
Lemma AliasConsistent_extend :
  forall G Gam x e, AliasConsistent G Gam -> WellFoundedFwd G -> G x = None ->
  AliasConsistent (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x e HAC HWF Hx p q Hpq w Hpw Hwq.
  assert (Hpx : p <> x).
  { intro Heq; subst p. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq. }
  rewrite (hupd_neq G x (GExpr e) p Hpx) in Hpq.
  assert (Hqx : q <> x).
  { intro Heq; subst q.
    destruct (HWF p x Hpq) as [z Hcl].
    inversion Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0]; subst.
    - congruence.
    - assert (y0 = x) by congruence; subst y0.
      exact (ContractLoc_dom G x z Hcl0 Hx). }
  rewrite (hupd_neq Gam x (let_content x e) p Hpx) in Hpw.
  rewrite (hupd_neq Gam x (let_content x e) q Hqx).
  exact (HAC p q Hpq w Hpw Hwq).
Qed.

(* STANDALONE TEST (not yet wired into theorem2): validates the core
   "skip-ahead" reconciliation mechanism AliasConsistent is meant to
   unlock, for G_CaseFwd's own disjunct-2 scenario, using only ALREADY
   Qed'd machinery (shortcut_alias, shortcut_alias_relax, guard_shrink,
   alias_weaken_force_y) plus the new AliasConsistent fact -- BEFORE
   committing to threading AliasConsistent through theorem2's own,
   invasive, whole-proof restatement.

   Hgin_y0/Hgam_x0 (below) encode "forcing w never touches y0's own slot,
   and y0's own forcing never touches x0's own slot" -- semantically
   obvious (forward-only chase), taken as explicit hypotheses here to
   validate the ASSEMBLY mechanism first; whether they're easy to
   discharge as real lemmas is checked separately afterward. *)
Lemma skip_ahead_reconcile_test :
  forall P x0 y0 w c args Gam Gmid_inner v1,
  x0 <> y0 -> w <> y0 -> w <> x0 ->
  Gam x0 = Some (BExpr (EVar w)) ->
  Gam y0 = Some (BExpr (EVar w)) ->
  NEval_left P (y0::nil) Gam (BExpr (EVar w)) Gmid_inner (BExpr (ECon c args)) ->
  let Gmid := hupd Gmid_inner y0 (BExpr (ECon c args)) in
  forall body Gamy0, NEval_left P nil Gmid body Gamy0 v1 ->
  exists Gam', NEval_left P nil Gam (BExpr (EVar x0)) Gam' (BExpr (ECon c args)) /\
    exists Gamx0, NEval_left P nil Gam' body Gamx0 v1 /\
      (forall p, p <> x0 -> p <> y0 -> Gamx0 p = Gamy0 p) /\
      Gamx0 x0 = Some (BExpr (ECon c args)) /\
      (Gamx0 y0 = Some (BExpr (EVar w)) \/ Gamx0 y0 = Some (BExpr (ECon c args))).
Proof.
  intros P x0 y0 w c args Gam Gmid_inner v1 Hx0y0 Hwy0 Hwx0 Hgx0 Hgy0 Hrecw Gmid body Gamy0 Hbody.
  (* Step 2: shrink Hrecw from (y0::nil) to nil. *)
  assert (Hrecw_nil : NEval_left P nil Gam (BExpr (EVar w)) Gmid_inner (BExpr (ECon c args))).
  { apply (NEval_left_guard_shrink P (y0::nil) nil (fun w0 H => False_ind _ H) Gam
             (BExpr (EVar w)) Gmid_inner (BExpr (ECon c args)) Hrecw). }
  (* Derive Hginx0/Hginy0 (forcing w never touches x0/y0's own slots) from
     Hrecw_nil directly, via the ALREADY Qed'd NEval_left_alias_persists_through_force. *)
  assert (Hginx0 : Gmid_inner x0 = Some (BExpr (EVar w)))
    by exact (NEval_left_alias_persists_through_force P x0 w (not_eq_sym Hwx0)
                Gam Gmid_inner (BExpr (ECon c args)) Hrecw_nil Hgx0).
  assert (Hginy0 : Gmid_inner y0 = Some (BExpr (EVar w)))
    by exact (NEval_left_alias_persists_through_force P y0 w (not_eq_sym Hwy0)
                Gam Gmid_inner (BExpr (ECon c args)) Hrecw_nil Hgy0).
  (* Step 3: widen from nil to (x0::nil), using Gam x0 = EVar w. *)
  assert (Hrecw_x0 : NEval_left P (x0::nil) Gam (BExpr (EVar w)) Gmid_inner (BExpr (ECon c args))).
  { exact (NEval_left_alias_weaken_force_y P x0 w (not_eq_sym Hwx0) Gam Gmid_inner (BExpr (ECon c args)) Hrecw_nil Hgx0). }
  (* Step 4: build x0's own NL_VarExp. *)
  assert (Hforcex0 : NEval_left P nil Gam (BExpr (EVar x0)) (hupd Gmid_inner x0 (BExpr (ECon c args))) (BExpr (ECon c args))).
  { eapply NL_VarExp.
    - intro Hin; destruct Hin.
    - exact Hgx0.
    - intros c' args' Hcontra; discriminate Hcontra.
    - intro Hcontra; injection Hcontra as Hcontra; exact (Hwx0 Hcontra).
    - intro Hcontra; discriminate Hcontra.
    - exact Hrecw_x0. }
  exists (hupd Gmid_inner x0 (BExpr (ECon c args))). split; [exact Hforcex0 | ].
  (* Step 5: downgrade Hbody at y0 (Con c args -> EVar w), landing exactly on Gmid_inner. *)
  assert (Hgmidw : Gmid w = Some (BExpr (ECon c args))).
  { unfold Gmid. rewrite (hupd_neq Gmid_inner y0 (BExpr (ECon c args)) w Hwy0).
    exact (NEval_left_own_slot P (y0::nil) Gam w Gmid_inner (BExpr (ECon c args)) Hrecw). }
  assert (Hgmidy0 : Gmid y0 = Some (BExpr (ECon c args))).
  { unfold Gmid. unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
  destruct (NEval_left_shortcut_alias_relax P y0 w c args (not_eq_sym Hwy0) nil
              (fun H => H) Gmid body Gamy0 v1 Hbody Hgmidy0 Hgmidw)
    as [Gamdown [Hbodydown Heqdown]].
  assert (Heqdown_ptw : forall p, hupd Gmid y0 (BExpr (EVar w)) p = Gmid_inner p).
  { intro p. destruct (Nat.eq_dec p y0) as [Heq | Hne].
    - subst p. unfold hupd; rewrite Nat.eqb_refl. exact (eq_sym Hginy0).
    - rewrite (hupd_neq Gmid y0 (BExpr (EVar w)) p Hne). unfold Gmid.
      rewrite (hupd_neq Gmid_inner y0 (BExpr (ECon c args)) p Hne). reflexivity. }
  assert (Hbody_inner : exists Gamdown', NEval_left P nil Gmid_inner body Gamdown' v1 /\
            (forall p, Gamdown' p = Gamdown p)).
  { destruct (NEval_left_pointwise_heap P nil (hupd Gmid y0 (BExpr (EVar w))) body Gamdown v1 Hbodydown
                Gmid_inner (fun p => eq_sym (Heqdown_ptw p))) as [Gamdown' [Hbodydown' Heqdown']].
    exists Gamdown'. split; [exact Hbodydown' | exact Heqdown']. }
  destruct Hbody_inner as [Gamdown' [Hbody_inner Heqdown'_ptw]].
  (* Step 6: promote x0 on top of Hbody_inner, using Gmid_inner x0 = EVar w, Gmid_inner w = Con c args. *)
  assert (Hginw : Gmid_inner w = Some (BExpr (ECon c args))).
  { exact (NEval_left_own_slot P (y0::nil) Gam w Gmid_inner (BExpr (ECon c args)) Hrecw). }
  destruct (NEval_left_shortcut_alias P x0 w c args (not_eq_sym Hwx0) nil Gmid_inner body Gamdown' v1 Hbody_inner
              (or_introl Hginx0) Hginw) as [Gamfinal [Hbodyfinal HeqGamfinal]].
  exists Gamfinal. split; [exact Hbodyfinal | ].
  destruct Heqdown as [Heqdown1 Heqdown2].
  split.
  { intros p Hpx0 Hpy0.
    rewrite (HeqGamfinal p). rewrite (hupd_neq Gamdown' x0 (BExpr (ECon c args)) p Hpx0).
    rewrite (Heqdown'_ptw p). exact (Heqdown1 p Hpy0). }
  split.
  { rewrite (HeqGamfinal x0). unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
  { rewrite (HeqGamfinal y0). rewrite (hupd_neq Gamdown' x0 (BExpr (ECon c args)) y0 (not_eq_sym Hx0y0)).
    rewrite (Heqdown'_ptw y0). exact Heqdown2. }
Qed.

(* The remaining invariants (NoVarThunk, WellFoundedFwd, ChainConsistent,
   AliasConsistent) all survive narrowing a free location x to an achieved
   constructor, needed for G_CaseConFree. NoVarThunk/WellFoundedFwd are
   graph-only (Gam-independent) so the argument is purely structural;
   ChainConsistent/AliasConsistent both go through vacuously, using x's OWN
   pre-update self-loop witness (Gam x = EVar x) to show no OTHER location
   could already have been relying on x staying unresolved. *)
Lemma NoVarThunk_update_free :
  forall G x c args, NoVarThunk G -> G x = Some (GExpr EFree) ->
  NoVarThunk (hupd G x (GExpr (ECon c args))).
Proof.
  intros G x c args Hnvt Hx z w Heq.
  destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
  - subst z. unfold hupd in Heq. rewrite Nat.eqb_refl in Heq. discriminate Heq.
  - rewrite (hupd_neq G x (GExpr (ECon c args)) z Hnezx) in Heq. exact (Hnvt z w Heq).
Qed.

Lemma WellFoundedFwd_update_free :
  forall G x c args, WellFoundedFwd G -> G x = Some (GExpr EFree) ->
  WellFoundedFwd (hupd G x (GExpr (ECon c args))).
Proof.
  intros G x c args HWF Hx w y Hwy.
  destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
  - subst w. exfalso. unfold hupd in Hwy. rewrite Nat.eqb_refl in Hwy. discriminate Hwy.
  - rewrite (hupd_neq G x (GExpr (ECon c args)) w Hnewx) in Hwy.
    destruct (HWF w y Hwy) as [z Hcl].
    assert (Hxnonfwd : forall ww, G x <> Some (GFwd ww)) by (intros ww Heq; rewrite Hx in Heq; discriminate Heq).
    destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + subst z. exists x. exact (ContractLoc_update_nonfwd_to_target G w x Hcl (ECon c args) Hxnonfwd).
    + exists z. exact (ContractLoc_update_nonfwd_other G w z Hcl x (GExpr (ECon c args)) Hxnonfwd Hnezx).
Qed.

Lemma ChainConsistent_update_free :
  forall G Gam x c args, ChainConsistent G Gam -> G x = Some (GExpr EFree) ->
  Gam x = Some (BExpr (EVar x)) ->
  ChainConsistent (hupd G x (GExpr (ECon c args))) (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x c args HCC Hx Hgamx p q Hpq c' args' Hpc'.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. exfalso. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq.
  - rewrite (hupd_neq G x (GExpr (ECon c args)) p Hnepx) in Hpq.
    rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx) in Hpc'.
    destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
    + subst q. exfalso.
      assert (Hgx_achieved := HCC p x Hpq c' args' Hpc').
      rewrite Hgamx in Hgx_achieved. discriminate Hgx_achieved.
    + rewrite (hupd_neq Gam x (BExpr (ECon c args)) q Hneqx).
      exact (HCC p q Hpq c' args' Hpc').
Qed.

Lemma AliasConsistent_update_free :
  forall G Gam x c args, AliasConsistent G Gam -> G x = Some (GExpr EFree) ->
  Gam x = Some (BExpr (EVar x)) ->
  AliasConsistent (hupd G x (GExpr (ECon c args))) (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x c args HAC Hx Hgamx p q Hpq w Hpw Hwq.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. exfalso. unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. discriminate Hpq.
  - rewrite (hupd_neq G x (GExpr (ECon c args)) p Hnepx) in Hpq.
    rewrite (hupd_neq Gam x (BExpr (ECon c args)) p Hnepx) in Hpw.
    destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
    + subst q. exfalso.
      assert (Hgxw := HAC p x Hpq w Hpw Hwq).
      rewrite Hgamx in Hgxw. injection Hgxw as Hgxw. exact (Hwq (eq_sym Hgxw)).
    + rewrite (hupd_neq Gam x (BExpr (ECon c args)) q Hneqx).
      exact (HAC p q Hpq w Hpw Hwq).
Qed.

(* Batch (list) versions of the four fresh-extend lemmas, for narrowing a
   free location's own case-branch's fresh pattern variables ws all at
   once -- mirrors HeapCorr_extend_free_list's own induction exactly. *)
Lemma NoVarThunk_extend_free_list :
  forall ws G, NoVarThunk G -> NoDup ws -> (forall w, In w ws -> G w = None) ->
  NoVarThunk (hupd_list G ws (map (fun _ => GExpr EFree) ws)).
Proof.
  induction ws as [| w ws' IHws]; intros G Hnvt HND Hfresh; simpl.
  - exact Hnvt.
  - assert (HNDtl : NoDup ws') by (inversion HND; assumption).
    assert (Hfreshtl : forall w', In w' ws' -> G w' = None)
      by (intros w' Hin; apply Hfresh; right; exact Hin).
    assert (Hw : G w = None) by (apply Hfresh; left; reflexivity).
    assert (Hrec := IHws G Hnvt HNDtl Hfreshtl).
    assert (HwFresh' : hupd_list G ws' (map (fun _ => GExpr EFree) ws') w = None)
      by (rewrite hupd_list_notin; [exact Hw | inversion HND; assumption]).
    exact (NoVarThunk_extend _ w EFree Hrec HwFresh' (ltac:(intros y Heq; discriminate Heq))).
Qed.

Lemma WellFoundedFwd_extend_free_list :
  forall ws G, WellFoundedFwd G -> NoDup ws -> (forall w, In w ws -> G w = None) ->
  WellFoundedFwd (hupd_list G ws (map (fun _ => GExpr EFree) ws)).
Proof.
  induction ws as [| w ws' IHws]; intros G HWF HND Hfresh; simpl.
  - exact HWF.
  - assert (HNDtl : NoDup ws') by (inversion HND; assumption).
    assert (Hfreshtl : forall w', In w' ws' -> G w' = None)
      by (intros w' Hin; apply Hfresh; right; exact Hin).
    assert (Hw : G w = None) by (apply Hfresh; left; reflexivity).
    assert (Hrec := IHws G HWF HNDtl Hfreshtl).
    assert (HwFresh' : hupd_list G ws' (map (fun _ => GExpr EFree) ws') w = None)
      by (rewrite hupd_list_notin; [exact Hw | inversion HND; assumption]).
    exact (WellFoundedFwd_extend _ w EFree Hrec HwFresh').
Qed.

Lemma ChainConsistent_extend_free_list :
  forall ws G Gam, ChainConsistent G Gam -> WellFoundedFwd G ->
  NoDup ws -> (forall w, In w ws -> G w = None) ->
  ChainConsistent (hupd_list G ws (map (fun _ => GExpr EFree) ws))
                  (hupd_list Gam ws (map (fun w => BExpr (EVar w)) ws)).
Proof.
  induction ws as [| w ws' IHws]; intros G Gam HCC HWF HND Hfresh; simpl.
  - exact HCC.
  - assert (HNDtl : NoDup ws') by (inversion HND; assumption).
    assert (Hfreshtl : forall w', In w' ws' -> G w' = None)
      by (intros w' Hin; apply Hfresh; right; exact Hin).
    assert (Hw : G w = None) by (apply Hfresh; left; reflexivity).
    assert (HrecCC := IHws G Gam HCC HWF HNDtl Hfreshtl).
    assert (HrecWF := WellFoundedFwd_extend_free_list ws' G HWF HNDtl Hfreshtl).
    assert (HwFresh' : hupd_list G ws' (map (fun _ => GExpr EFree) ws') w = None)
      by (rewrite hupd_list_notin; [exact Hw | inversion HND; assumption]).
    exact (ChainConsistent_extend _ _ w EFree HrecCC HrecWF HwFresh').
Qed.

Lemma AliasConsistent_extend_free_list :
  forall ws G Gam, AliasConsistent G Gam -> WellFoundedFwd G ->
  NoDup ws -> (forall w, In w ws -> G w = None) ->
  AliasConsistent (hupd_list G ws (map (fun _ => GExpr EFree) ws))
                  (hupd_list Gam ws (map (fun w => BExpr (EVar w)) ws)).
Proof.
  induction ws as [| w ws' IHws]; intros G Gam HAC HWF HND Hfresh; simpl.
  - exact HAC.
  - assert (HNDtl : NoDup ws') by (inversion HND; assumption).
    assert (Hfreshtl : forall w', In w' ws' -> G w' = None)
      by (intros w' Hin; apply Hfresh; right; exact Hin).
    assert (Hw : G w = None) by (apply Hfresh; left; reflexivity).
    assert (HrecAC := IHws G Gam HAC HWF HNDtl Hfreshtl).
    assert (HrecWF := WellFoundedFwd_extend_free_list ws' G HWF HNDtl Hfreshtl).
    assert (HwFresh' : hupd_list G ws' (map (fun _ => GExpr EFree) ws') w = None)
      by (rewrite hupd_list_notin; [exact Hw | inversion HND; assumption]).
    exact (AliasConsistent_extend _ _ w EFree HrecAC HrecWF HwFresh').
Qed.

(* ==================================================================== *)
(* G_CaseChoice's own update: x goes from a direct EChoice content to a NEW
   GFwd edge (toward the first operand), matching HeapCorr2_update_to_fwd_lazy
   but ported to HeapCorr/ChainConsistent/AliasConsistent separately. *)
(* ==================================================================== *)

(* Companion to VarChase_transport_free_to_con, for a location x whose OLD
   Nat-heap witness is NEITHER EVar-shaped (so no other chase could have
   continued THROUGH it) NOR already Con-shaped (so no other chase could
   have legitimately TERMINATED at it as an achieved value) -- x's own
   slot changing (to anything at all) can't invalidate any OTHER
   location's existing achieved witness. *)
Lemma VarChase_transport_nonvar_noncon_to_con :
  forall Gam x, (forall w', Gam x <> Some (BExpr (EVar w'))) ->
  (forall c args, Gam x <> Some (BExpr (ECon c args))) ->
  forall p e, VarChase Gam p e ->
  forall c args, e = BExpr (ECon c args) ->
  forall gnew, VarChase (hupd Gam x gnew) p e.
Proof.
  intros Gam x Hxnonvar Hxnoncon p e H.
  induction H as [w0 b0 Hb0 Hself0 | w0 w0' e0 Hw0 Hne Hrec IH];
    intros c args Heqe gnew.
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. exfalso. rewrite Heqe in Hb0. exact (Hxnoncon c args Hb0).
    + apply VChase_Here.
      * rewrite (hupd_neq Gam x gnew w0 Hnewx). exact Hb0.
      * intros w' Hcontra. exact (Hself0 w' Hcontra).
  - destruct (Nat.eq_dec w0 x) as [Heqwx | Hnewx].
    + subst w0. exfalso. exact (Hxnonvar w0' Hw0).
    + eapply VChase_Hop.
      * rewrite (hupd_neq Gam x gnew w0 Hnewx). exact Hw0.
      * exact Hne.
      * exact (IH c args Heqe gnew).
Qed.

(* Unlike ChainConsistent/AliasConsistent (whose own transport only ever
   worries about ACHIEVED, Con-shaped targets -- and x's OLD content,
   EChoice, structurally can't be one), WellFoundedFwd's own witnesses can
   terminate at ANY GExpr-shaped location, so a chain that used to
   terminate exactly at x needs to be EXTENDED through x's new edge
   (via ContractLoc_update_choice_extend) rather than just transported. *)
Lemma WellFoundedFwd_update_choice_to_fwd :
  forall G x y z, WellFoundedFwd G -> G x = Some (GExpr (EChoice y z)) ->
  (exists ytgt, ContractLoc (hupd G x (GFwd y)) y ytgt) ->
  WellFoundedFwd (hupd G x (GFwd y)).
Proof.
  intros G x y z HWF Hgx Hyexists w y1 Hwy1.
  destruct Hyexists as [ytgt Hclyt].
  destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
  - subst w. unfold hupd in Hwy1; rewrite Nat.eqb_refl in Hwy1; injection Hwy1 as Hwy1; subst y1.
    exists ytgt. eapply CL_Fwd; [unfold hupd; rewrite Nat.eqb_refl; reflexivity | exact Hclyt].
  - rewrite (hupd_neq G x (GFwd y) w Hnewx) in Hwy1.
    destruct (HWF w y1 Hwy1) as [ztgt Hcl].
    assert (Hxnonfwd : forall ww, G x <> Some (GFwd ww)) by (intros ww Heq; rewrite Hgx in Heq; discriminate Heq).
    destruct (Nat.eq_dec ztgt x) as [Heqzx | Hnezx].
    + subst ztgt.
      exists ytgt. exact (ContractLoc_update_choice_extend G w x Hcl y ytgt Hxnonfwd Hclyt).
    + exists ztgt. exact (ContractLoc_update_nonfwd_other G w ztgt Hcl x (GFwd y) Hxnonfwd Hnezx).
Qed.

Lemma HeapCorr_update_choice_to_fwd :
  forall G Gam x y z, HeapCorr G Gam -> G x = Some (GExpr (EChoice y z)) ->
  HeapCorr (hupd G x (GFwd y)) (hupd Gam x (BExpr (EVar y))).
Proof.
  intros G Gam x y z HGam Hgx.
  assert (Hgamx : Gam x = Some (BExpr (EChoice y z))).
  { assert (HGamx := HGam x). rewrite Hgx in HGamx.
    destruct HGamx as [b [Hb HCE3]].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgxfwd _]]]]]].
    - destruct (CorrE_forced_shape G x b HCE) as
        [ [c0 [args0 [Hg1 Hb1]]]
        | [ [Hg1 Hb1]
          | [ [f1 [args1 [Hg1 Hb1]]]
            | [ [y1' [y2' [Hg1 Hb1]]]
              | [ [z1' [Hg1 Hb1]]
                | [ [Hg1 Hb1]
                  | [ [y1 [Hg1 Hb1]]
                    | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
        rewrite Hgx in Hg1; try discriminate Hg1.
      injection Hg1 as Hg1a Hg1b. subst y1' y2'. rewrite Hb1 in Hb. exact Hb.
    - rewrite Hgx in Hgxfwd. discriminate Hgxfwd. }
  assert (Hxnonfwd : forall w, G x <> Some (GFwd w))
    by (intros w Heq; rewrite Hgx in Heq; discriminate Heq).
  assert (Hxnoncon : forall c args, G x <> Some (GExpr (ECon c args)))
    by (intros c args Heq; rewrite Hgx in Heq; discriminate Heq).
  assert (Hgamx_nonvar : forall w', Gam x <> Some (BExpr (EVar w')))
    by (intros w' Heq; rewrite Hgamx in Heq; discriminate Heq).
  assert (Hgamx_noncon : forall c' args', Gam x <> Some (BExpr (ECon c' args')))
    by (intros c' args' Heq; rewrite Hgamx in Heq; discriminate Heq).
  intro p.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. unfold hupd; rewrite Nat.eqb_refl.
    exists (BExpr (EVar y)). split; [reflexivity | ].
    left. apply CorrE_FwdHere. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
  - rewrite (hupd_neq G x (GFwd y) p Hnepx).
    specialize (HGam p). destruct (G p) as [gp | ] eqn:EGp;
      [ | rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx); exact HGam].
    destruct HGam as [b [Hb HCE3]].
    rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx).
    exists b. split; [exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. exact (CorrE_update_nonfwd_noncon_other G p b HCE x (GFwd y) Hxnonfwd Hxnoncon Hnepx).
    + right. exists y1, z1, c1, args1.
      assert (Hz1x : z1 <> x) by (intro Heq; subst z1; exact (Hxnoncon c1 args1 Hz1)).
      split; [rewrite (hupd_neq G x (GFwd y) p Hnepx); exact Hgp | ].
      split; [exact (ContractLoc_update_nonfwd_other G y1 z1 Hcl1 x (GFwd y) Hxnonfwd Hz1x) | ].
      split; [rewrite (hupd_neq G x (GFwd y) z1 Hz1x); exact Hz1 | ].
      exact (VarChase_transport_nonvar_noncon_to_con Gam x Hgamx_nonvar Hgamx_noncon p
               (BExpr (ECon c1 args1)) HVC c1 args1 eq_refl (BExpr (EVar y))).
Qed.

Lemma ChainConsistent_update_to_fwd_lazy :
  forall G Gam x y gamold, ChainConsistent G Gam ->
  Gam x = Some gamold -> (forall c args, gamold <> BExpr (ECon c args)) ->
  ChainConsistent (hupd G x (GFwd y)) (hupd Gam x (BExpr (EVar y))).
Proof.
  intros G Gam x y gamold HCC Hgamx Hnoncon p q Hpq c' args' Hpc'.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. exfalso. unfold hupd in Hpc'. rewrite Nat.eqb_refl in Hpc'. discriminate Hpc'.
  - rewrite (hupd_neq G x (GFwd y) p Hnepx) in Hpq.
    rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx) in Hpc'.
    destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
    + subst q. exfalso.
      assert (Hgx_achieved := HCC p x Hpq c' args' Hpc').
      rewrite Hgamx in Hgx_achieved. injection Hgx_achieved as Hgx_achieved.
      exact (Hnoncon c' args' Hgx_achieved).
    + rewrite (hupd_neq Gam x (BExpr (EVar y)) q Hneqx).
      exact (HCC p q Hpq c' args' Hpc').
Qed.

Lemma AliasConsistent_update_to_fwd_lazy :
  forall G Gam x y gamold, AliasConsistent G Gam ->
  Gam x = Some gamold -> (forall w, gamold <> BExpr (EVar w)) ->
  AliasConsistent (hupd G x (GFwd y)) (hupd Gam x (BExpr (EVar y))).
Proof.
  intros G Gam x y gamold HAC Hgamx Hnonvar p q Hpq w Hpw Hwq.
  destruct (Nat.eq_dec p x) as [Heqpx | Hnepx].
  - subst p. exfalso.
    unfold hupd in Hpq. rewrite Nat.eqb_refl in Hpq. injection Hpq as Hpq. subst q.
    unfold hupd in Hpw. rewrite Nat.eqb_refl in Hpw. injection Hpw as Hpw. subst w.
    exact (Hwq eq_refl).
  - rewrite (hupd_neq G x (GFwd y) p Hnepx) in Hpq.
    rewrite (hupd_neq Gam x (BExpr (EVar y)) p Hnepx) in Hpw.
    destruct (Nat.eq_dec q x) as [Heqqx | Hneqx].
    + subst q. exfalso.
      assert (Hgxw := HAC p x Hpq w Hpw Hwq).
      rewrite Hgamx in Hgxw. injection Hgxw as Hgxw. exact (Hnonvar w Hgxw).
    + rewrite (hupd_neq Gam x (BExpr (EVar y)) q Hneqx).
      exact (HAC p q Hpq w Hpw Hwq).
Qed.

Definition GNode_mirror (vx : GNode) : Blk :=
  match vx with
  | GFwd y => BExpr (EVar y)
  | GExpr e0 => BExpr e0
  end.

(* Companion to GNode_mirror, for use as a CorrE WITNESS AT A SPECIFIC
   LOCATION x0 rather than as a Nat expression to force: differs from
   GNode_mirror ONLY at Free, where the correct CorrE witness (CorrE_Free's
   own conclusion) is the SELF-LOOP EVar x0, not the literal token EFree --
   matching the file's own "a free variable is a variable mapped to itself"
   convention. Every other shape's CorrE witness matches its own graph
   content directly, same as GNode_mirror. *)
Definition GNode_witness_at (x0 : var) (vx : GNode) : Blk :=
  match vx with
  | GFwd y => BExpr (EVar y)
  | GExpr EFree => BExpr (EVar x0)
  | GExpr e0 => BExpr e0
  end.

(* x0's OLD content being EFun (non-alias, non-achieved) means no existing
   VarChase chain reaching an achieved Con could ever have passed through
   x0: VChase_Hop needs an EVar-shaped hop, and VChase_Here terminating AT
   x0 would force Gam x0 itself to equal the achieved Con -- impossible,
   EFun <> ECon. So every such chain avoids x0 entirely and transports
   across ANY update there, unconditionally on the new value. *)
Lemma VarChase_avoids_fun_loc :
  forall Gam x0 f0 args0, Gam x0 = Some (BExpr (EFun f0 args0)) ->
  forall p e, VarChase Gam p e -> e <> BExpr (EFun f0 args0) ->
  forall enew, VarChase (hupd Gam x0 enew) p e.
Proof.
  intros Gam x0 f0 args0 Hgx0 p e H.
  induction H as [w0 b0 Hb0 Hself | w0 w0' e0 Hw0 Hne Hrec IH]; intro Hne0.
  - intro enew.
    assert (Hw0x0 : w0 <> x0).
    { intro Heq; subst w0. rewrite Hgx0 in Hb0. injection Hb0 as Hb0. subst b0. exact (Hne0 eq_refl). }
    apply VChase_Here.
    + rewrite (hupd_neq Gam x0 enew w0 Hw0x0). exact Hb0.
    + exact Hself.
  - intro enew.
    assert (Hw0x0 : w0 <> x0).
    { intro Heq; subst w0. rewrite Hgx0 in Hw0. discriminate Hw0. }
    eapply VChase_Hop.
    + rewrite (hupd_neq Gam x0 enew w0 Hw0x0). exact Hw0.
    + exact Hne.
    + exact (IH Hne0 enew).
Qed.

(* HeapCorr's own analogue of HeapCorr_update_choice_to_fwd, generalized
   from "EChoice -> GFwd specifically" to "EFun -> ANY GNode": x0's own new
   Nat-witness is GNode_mirror vx, the SAME trivial, evaluation-free
   correspondence HeapCorr_extend already uses for a freshly-let-bound
   location, just applied to an UPDATE instead of an extension. Every OTHER
   location's witness survives: x0's OLD content (EFun) was never
   Fwd-shaped (ruling out any chain hopping THROUGH x0, via
   ContractLoc_update_nonfwd_other) and never Con-achieved-reachable either
   (ruling out any VarChase chain passing through it, via
   VarChase_avoids_fun_loc) -- the SAME "old content couldn't have been a
   shortcut target" argument HeapCorr_update_choice_to_fwd already relies
   on, just needing both halves (ContractLoc AND VarChase) since CorrE3's
   skip-ahead disjunct combines them. *)
Lemma HeapCorr_update_from_fun :
  forall G Gam x0 f0 args0 vx, HeapCorr G Gam ->
  G x0 = Some (GExpr (EFun f0 args0)) ->
  HeapCorr (hupd G x0 vx) (hupd Gam x0 (GNode_witness_at x0 vx)).
Proof.
  intros G Gam x0 f0 args0 vx HGam Hgx0 p.
  assert (Hxnonfwd : forall w, G x0 <> Some (GFwd w))
    by (intros w Heq; rewrite Hgx0 in Heq; discriminate Heq).
  assert (Hgamx0 : Gam x0 = Some (BExpr (EFun f0 args0))).
  { assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
    destruct HGamx0 as [b [Hb HCE3x0]].
    destruct HCE3x0 as [HCEx0 | [y1' [z1' [c1' [args1' [Hgp' _]]]]]].
    - destruct (CorrE_forced_shape G x0 b HCEx0) as
        [ [c0 [args0' [Hg1 Hb1]]]
        | [ [Hg1 Hb1]
          | [ [f1 [args1 [Hg1 Hb1]]]
            | [ [y1 [y2 [Hg1 Hb1]]]
              | [ [z1 [Hg1 Hb1]]
                | [ [Hg1 Hb1]
                  | [ [y1 [Hg1 Hb1]]
                    | [y1 [z1 [c0 [args0' [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
        rewrite Hgx0 in Hg1; try discriminate Hg1.
      injection Hg1 as Hg1a Hg1b. subst f1 args1. rewrite Hb1 in Hb. exact Hb.
    - rewrite Hgx0 in Hgp'; discriminate Hgp'. }
  destruct (Nat.eq_dec p x0) as [Heqpx0 | Hnepx0].
  - subst p. unfold hupd; rewrite Nat.eqb_refl.
    exists (GNode_witness_at x0 vx). split; [reflexivity | ].
    left. destruct vx as [e0 | y].
    + destruct e0; simpl.
      * eapply CorrE_VarThunk. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * eapply CorrE_Bot. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * eapply CorrE_Free. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * eapply CorrE_Choice. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * eapply CorrE_Fun. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * eapply CorrE_Con. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
    + eapply CorrE_FwdHere. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
  - rewrite (hupd_neq G x0 vx p Hnepx0).
    assert (HGamp := HGam p). destruct (G p) as [gp | ] eqn:EGp;
      [ | rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) p Hnepx0); exact HGamp].
    destruct HGamp as [b [Hb HCE3]].
    exists b. split; [rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) p Hnepx0); exact Hb | ].
    destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgp [Hcl1 [Hz1 HVC]]]]]]]].
    + left. destruct HCE as
        [ x1 c0 args0' H0 | x1 H0 | x1 f1 args1' H0 | x1 y0 z0 H0 | x1 z0 H0 | x1 H0
        | x1 y0 H0 | x1 y0 z0 c0 args0' H0 Hcl0 Hz0 ].
      * eapply CorrE_Con. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_Free. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_Fun. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_Choice. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_VarThunk. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_Bot. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * eapply CorrE_FwdHere. rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
      * assert (Hz0x0 : z0 <> x0)
          by (intro Heq; subst z0; rewrite Hgx0 in Hz0; discriminate Hz0).
        eapply CorrE_FwdAchievedCon.
        -- rewrite (hupd_neq G x0 vx x1 Hnepx0). exact H0.
        -- exact (ContractLoc_update_nonfwd_other G y0 z0 Hcl0 x0 vx Hxnonfwd Hz0x0).
        -- rewrite (hupd_neq G x0 vx z0 Hz0x0). exact Hz0.
    + assert (Hz1x0 : z1 <> x0)
        by (intro Heq; subst z1; rewrite Hgx0 in Hz1; discriminate Hz1).
      right. exists y1, z1, c1, args1.
      split; [rewrite (hupd_neq G x0 vx p Hnepx0); exact Hgp | ].
      split; [exact (ContractLoc_update_nonfwd_other G y1 z1 Hcl1 x0 vx Hxnonfwd Hz1x0) | ].
      split; [rewrite (hupd_neq G x0 vx z1 Hz1x0); exact Hz1 |
        exact (VarChase_avoids_fun_loc Gam x0 f0 args0 Hgamx0 p (BExpr (ECon c1 args1)) HVC
                 (ltac:(intro Hcontra; discriminate Hcontra)) (GNode_witness_at x0 vx))].
Qed.

(* WellFoundedFwd's own analogue of HeapCorr_update_from_fun: x0's OLD
   content (EFun) is non-Fwd, so any chain that used to terminate exactly
   at x0 (CL_Here) survives via ContractLoc_update_nonfwd_to_target if x0's
   NEW content is ALSO non-Fwd, or extends one hop further via
   ContractLoc_update_choice_extend if x0's new content IS a Fwd edge
   (needing the caller to separately supply that this new edge itself
   terminates, exactly as WellFoundedFwd_update_choice_to_fwd already
   required for the EChoice-specific case this generalizes). *)
Lemma WellFoundedFwd_update_from_fun :
  forall G x0 f0 args0 vx, WellFoundedFwd G -> G x0 = Some (GExpr (EFun f0 args0)) ->
  (forall y, vx = GFwd y -> exists ytgt, ContractLoc (hupd G x0 vx) y ytgt) ->
  WellFoundedFwd (hupd G x0 vx).
Proof.
  intros G x0 f0 args0 vx HWF Hgx0 Hvxfwd w y Hwy1.
  assert (Hxnonfwd : forall ww, G x0 <> Some (GFwd ww))
    by (intros ww Heq; rewrite Hgx0 in Heq; discriminate Heq).
  destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
  - subst w. unfold hupd in Hwy1; rewrite Nat.eqb_refl in Hwy1.
    destruct vx as [e0 | y0']; [discriminate Hwy1 | ].
    injection Hwy1 as Hwy1; subst y0'.
    destruct (Hvxfwd y eq_refl) as [ytgt Hclyt].
    exists ytgt. eapply CL_Fwd; [unfold hupd; rewrite Nat.eqb_refl; reflexivity | exact Hclyt].
  - rewrite (hupd_neq G x0 vx w Hnewx0) in Hwy1.
    destruct (HWF w y Hwy1) as [ztgt Hcl].
    destruct (Nat.eq_dec ztgt x0) as [Heqzx0 | Hnezx0].
    + subst ztgt. destruct vx as [e0 | y0'].
      * exists x0. exact (ContractLoc_update_nonfwd_to_target G w x0 Hcl e0 Hxnonfwd).
      * destruct (Hvxfwd y0' eq_refl) as [ytgt Hclyt].
        exists ytgt. exact (ContractLoc_update_choice_extend G w x0 Hcl y0' ytgt Hxnonfwd Hclyt).
    + exists ztgt. exact (ContractLoc_update_nonfwd_other G w ztgt Hcl x0 vx Hxnonfwd Hnezx0).
Qed.

(* ChainConsistent's own analogue: x0's OLD Nat-witness being literally
   EFun f0 args0 (never a Con) means no location forwarding TO x0 could
   already have an achieved-Con witness pointing there -- ChainConsistent
   itself, applied BEFORE the update, would force Gam x0 = Con c args in
   that scenario, contradicting Gam x0 = EFun directly. So the only new
   fact ChainConsistent's own quantification could need (some p already
   forwarding to x0) is vacuous, and x0's own new GNode_witness_at value is
   never itself a bare Con (Fwd-shaped vx witnesses via EVar, non-Fwd
   shapes witness directly but combined with x0 x0 being ITS OWN "p" is
   ruled out the same way) -- no graph-level ContractLoc/VarChase
   reasoning needed at all, unlike HeapCorr_update_from_fun. *)
Lemma ChainConsistent_update_from_fun :
  forall G Gam x0 f0 args0 vx, ChainConsistent G Gam -> Gam x0 = Some (BExpr (EFun f0 args0)) ->
  ChainConsistent (hupd G x0 vx) (hupd Gam x0 (GNode_witness_at x0 vx)).
Proof.
  intros G Gam x0 f0 args0 vx HCC Hgamx0 p q Hpq c args Hpc.
  destruct (Nat.eq_dec p x0) as [Heqpx0 | Hnepx0].
  - subst p. unfold hupd in Hpq; rewrite Nat.eqb_refl in Hpq.
    unfold hupd in Hpc; rewrite Nat.eqb_refl in Hpc.
    destruct vx as [e0 | y0']; [discriminate Hpq | ].
    injection Hpq as Hpq; subst y0'.
    simpl in Hpc. discriminate Hpc.
  - rewrite (hupd_neq G x0 vx p Hnepx0) in Hpq.
    rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) p Hnepx0) in Hpc.
    destruct (Nat.eq_dec q x0) as [Heqqx0 | Hneqx0].
    + subst q. exfalso.
      assert (Hgx0con := HCC p x0 Hpq c args Hpc).
      rewrite Hgamx0 in Hgx0con. discriminate Hgx0con.
    + rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) q Hneqx0).
      exact (HCC p q Hpq c args Hpc).
Qed.

(* AliasConsistent's own analogue, same style as ChainConsistent_update_from_fun. *)
Lemma AliasConsistent_update_from_fun :
  forall G Gam x0 f0 args0 vx, AliasConsistent G Gam -> Gam x0 = Some (BExpr (EFun f0 args0)) ->
  AliasConsistent (hupd G x0 vx) (hupd Gam x0 (GNode_witness_at x0 vx)).
Proof.
  intros G Gam x0 f0 args0 vx HAC Hgamx0 p q Hpq w Hpw Hwq.
  destruct (Nat.eq_dec p x0) as [Heqpx0 | Hnepx0].
  - subst p. exfalso.
    unfold hupd in Hpq; rewrite Nat.eqb_refl in Hpq.
    destruct vx as [e0 | y0']; [discriminate Hpq | ].
    injection Hpq as Hpq; subst q.
    unfold hupd in Hpw; rewrite Nat.eqb_refl in Hpw.
    simpl in Hpw. injection Hpw as Hpw; subst w.
    exact (Hwq eq_refl).
  - rewrite (hupd_neq G x0 vx p Hnepx0) in Hpq.
    rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) p Hnepx0) in Hpw.
    destruct (Nat.eq_dec q x0) as [Heqqx0 | Hneqx0].
    + subst q. exfalso.
      assert (Hgxw := HAC p x0 Hpq w Hpw Hwq).
      rewrite Hgamx0 in Hgxw. discriminate Hgxw.
    + rewrite (hupd_neq Gam x0 (GNode_witness_at x0 vx) q Hneqx0).
      exact (HAC p q Hpq w Hpw Hwq).
Qed.

(* Generalizes the older, HeapCorr2-based NEval_left_let_chain_to_fwd/_to_con
   (lines ~3696/3775 above) two ways at once: ported to the CURRENT
   HeapCorr/CorrE3, and unified across ALL FIVE possible GEval results
   (Bot/Free/Con/Choice/Fwd) via GNode_mirror, rather than one lemma per
   shape -- every non-case-tail GEval rule either produces its OWN result
   value DIRECTLY (matching e up to GNode_mirror exactly) or just delegates
   to a smaller sub-derivation with the SAME target, so one induction
   handles all five uniformly. x's own slot is proven UNCHANGED (G1 x = G x)
   as part of the conclusion rather than assumed as the older lemmas did --
   for this fragment (no case before reaching the final value), nothing but
   G_Let's OWN, always-fresh extension ever touches ANY location, so x's
   slot survives automatically given only that x is already in G's domain.
   SCOPE: still restricted to function bodies whose let-chain ends in a
   plain expression, not a nested case -- the six admitted GEval cases below
   match exactly the scope the older _to_fwd/_to_con already had (see their
   own comments); closing them is a separate, further piece of work. *)
Lemma NEval_left_let_chain_to_value :
  forall P, NoAliasLetProgWF P ->
  forall G e G1 vx, GEval P G e G1 vx ->
  forall Gam, HeapCorr G Gam -> NoVarThunk G -> NoAliasLetB e ->
    WellFoundedFwd G -> ChainConsistent G Gam -> AliasConsistent G Gam ->
  forall x, G x <> None ->
  G1 x = G x /\ NoVarThunk G1 /\ WellFoundedFwd G1 /\
  exists Gam1, HeapCorr G1 Gam1 /\ ChainConsistent G1 Gam1 /\ AliasConsistent G1 Gam1 /\ Gam1 x = Gam x /\
    forall F0 Gamk vk, NEval_left P F0 Gam1 (GNode_mirror vx) Gamk vk -> NEval_left P F0 Gam e Gamk vk.
Proof.
  intros P HPWF G e G1 vx H.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 xh yh
    | G0 xh
    | G0 G1' f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1' xh eh k v1 HxFresh Hrec IH
    | G0 xh brs Hgx0
    | G0 xh yh brs G1' v1 Hgx0 Hrec IH
    | G0 xh f args brs G1' vx0 G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 xh yh zh brs G1' v1 Hgx0 Hrec IH
    | G0 xh c zs brs ys body G1' v1 Hgx0 HIn Hlen Hrec IH
    | G0 xh c1 ys1 body1 brs G1' v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intros Gam HGam HNVT HNAL HWF HCC HAC x Hxdom.
  - (* G_Bot *)
    split; [reflexivity | split; [exact HNVT | split; [exact HWF |
      exists Gam; split; [exact HGam | split; [exact HCC | split; [exact HAC | split; [reflexivity |
        intros F0 Gamk vk H0; exact H0]]]]]]].
  - (* G_Free *)
    split; [reflexivity | split; [exact HNVT | split; [exact HWF |
      exists Gam; split; [exact HGam | split; [exact HCC | split; [exact HAC | split; [reflexivity |
        intros F0 Gamk vk H0; exact H0]]]]]]].
  - (* G_Con *)
    split; [reflexivity | split; [exact HNVT | split; [exact HWF |
      exists Gam; split; [exact HGam | split; [exact HCC | split; [exact HAC | split; [reflexivity |
        intros F0 Gamk vk H0; exact H0]]]]]]].
  - (* G_Choice *)
    split; [reflexivity | split; [exact HNVT | split; [exact HWF |
      exists Gam; split; [exact HGam | split; [exact HCC | split; [exact HAC | split; [reflexivity |
        intros F0 Gamk vk H0; exact H0]]]]]]].
  - (* G_Var *)
    split; [reflexivity | split; [exact HNVT | split; [exact HWF |
      exists Gam; split; [exact HGam | split; [exact HCC | split; [exact HAC | split; [reflexivity |
        intros F0 Gamk vk H0; exact H0]]]]]]].
  - (* G_Fun *)
    assert (HNALbody : NoAliasLetB (rename_b s body))
      by (apply NoAliasLetB_rename; exact (HPWF f ps body HPf)).
    destruct (IH Gam HGam HNVT HNALbody HWF HCC HAC x Hxdom)
      as [Hxeq [HNVT1 [HWF1 [Gam1 [HHC1 [HCC1 [HAC1 [Hgx1 Hplug]]]]]]]].
    split; [exact Hxeq | split; [exact HNVT1 | split; [exact HWF1 | ]]].
    exists Gam1. split; [exact HHC1 | split; [exact HCC1 | split; [exact HAC1 | split; [exact Hgx1 | ]]]].
    intros F0 Gamk vk Hforce.
    assert (HfreshGam : forall y0, ~ In y0 ps -> Gam (s y0) = None).
    { intros y0 Hin. specialize (Hfresh y0 Hin).
      assert (HGamsy0 := HGam (s y0)). rewrite Hfresh in HGamsy0. exact HGamsy0. }
    eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact HfreshGam | ].
    exact (Hplug F0 Gamk vk Hforce).
  - (* G_Let *)
    destruct HNAL as [Hne0 HNALk].
    assert (Hxz : x <> xh).
    { intro Heq; subst x. rewrite HxFresh in Hxdom. exact (Hxdom eq_refl). }
    assert (HGam_ext : HeapCorr (hupd G0 xh (GExpr eh)) (hupd Gam xh (let_content xh eh)))
      by (eapply HeapCorr_extend; [exact HGam | exact HxFresh]).
    assert (HNVT_ext : NoVarThunk (hupd G0 xh (GExpr eh)))
      by (eapply NoVarThunk_extend; [exact HNVT | exact HxFresh | exact Hne0]).
    assert (HWF_ext : WellFoundedFwd (hupd G0 xh (GExpr eh)))
      by (eapply WellFoundedFwd_extend; [exact HWF | exact HxFresh]).
    assert (HCC_ext : ChainConsistent (hupd G0 xh (GExpr eh)) (hupd Gam xh (let_content xh eh)))
      by (eapply ChainConsistent_extend; [exact HCC | exact HWF | exact HxFresh]).
    assert (HAC_ext : AliasConsistent (hupd G0 xh (GExpr eh)) (hupd Gam xh (let_content xh eh)))
      by (eapply AliasConsistent_extend; [exact HAC | exact HWF | exact HxFresh]).
    assert (Hxdom_ext : hupd G0 xh (GExpr eh) x <> None).
    { rewrite (hupd_neq G0 xh (GExpr eh) x Hxz). exact Hxdom. }
    destruct (IH (hupd Gam xh (let_content xh eh)) HGam_ext HNVT_ext HNALk HWF_ext HCC_ext HAC_ext x Hxdom_ext)
      as [Hxeq' [HNVT1 [HWF1 [Gam1 [HHC1 [HCC1 [HAC1 [Hgx1 Hplug]]]]]]]].
    assert (Hxeq : G1' x = G0 x).
    { rewrite Hxeq'. rewrite (hupd_neq G0 xh (GExpr eh) x Hxz). reflexivity. }
    split; [exact Hxeq | split; [exact HNVT1 | split; [exact HWF1 | ]]].
    exists Gam1. split; [exact HHC1 | split; [exact HCC1 | split; [exact HAC1 | split; [ | ]]]].
    + rewrite Hgx1. rewrite (hupd_neq Gam xh (let_content xh eh) x Hxz). reflexivity.
    + intros F0 Gamk vk Hforce.
      assert (HGamxh : Gam xh = None)
        by (assert (HGamxh' := HGam xh); rewrite HxFresh in HGamxh'; exact HGamxh').
      apply NL_Let; [exact HGamxh | exact (Hplug F0 Gamk vk Hforce)].
  - (* G_CaseBot: body cases on something before reaching a value -- same
       scope limit the older _to_fwd/_to_con already had; not yet handled *)
    admit.
  - (* G_CaseFwd: ditto *)
    admit.
  - (* G_CaseFun: ditto *)
    admit.
  - (* G_CaseChoice: ditto *)
    admit.
  - (* G_CaseCon: ditto *)
    admit.
  - (* G_CaseConFree: ditto *)
    admit.
Admitted.

(* Mirrors curry.v's own NoBareChoiceB exactly, but ALSO excludes a bare,
   un-let-bound `free` at a tail position -- matching the same real-syntax
   fact NoBareChoiceB already captures for `?`: Curry's own surface syntax
   has no way to write a free variable except via `let x = free in ...`
   (`let_content`'s own case, and G_Let/NL_Let's shared treatment of it as
   an opaque heap value, is the ONLY legitimate use), so a restricted-
   FlatCurry program actually produced by translating real Curry source
   never has `free` sitting bare at a function body's own tail, a
   let-continuation, or a case-branch body -- exactly the same restriction
   NoBareChoiceB already imposes for `?`, just for BOTH shapes at once
   (both allowed ONLY as a let-binding's own RHS). *)
Fixpoint NoBareFreeOrChoiceB (b : Blk) : Prop :=
  match b with
  | BLet x e k => NoBareFreeOrChoiceB k
  | BCase x brs =>
      fold_right (fun p acc => NoBareFreeOrChoiceB (match p with (_, _, bd) => bd end) /\ acc) True brs
  | BExpr e => match e with EChoice _ _ => False | EFree => False | _ => True end
  end.

Lemma NoBareFreeOrChoiceB_in :
  forall brs c ys bd, In (c, ys, bd) brs ->
  fold_right (fun (p : cname * list var * Blk) acc =>
                NoBareFreeOrChoiceB (match p with (_, _, bd0) => bd0 end) /\ acc) True brs ->
  NoBareFreeOrChoiceB bd.
Proof.
  induction brs as [| [[c0 ys0] bd0] brs' IH]; intros c ys bd Hin Hnbc.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + injection Heq as Heq1 Heq2 Heq3; subst c0 ys0 bd0. exact (proj1 Hnbc).
    + exact (IH c ys bd Hin (proj2 Hnbc)).
Qed.

Lemma NoBareFreeOrChoiceB_rename_bound :
  forall n b, blk_size b < n -> forall s, NoBareFreeOrChoiceB b -> NoBareFreeOrChoiceB (rename_b s b).
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros b Hsize s Hnbc.
  destruct b as [x e k | x brs | e].
  - simpl in *.
    assert (Hn : blk_size k + 1 < n) by lia.
    assert (Hm : blk_size k < blk_size k + 1) by lia.
    exact (IHn (blk_size k + 1) Hn k Hm s Hnbc).
  - simpl in *.
    induction brs as [| [[c ys] bd] brs' IHbrs].
    + exact I.
    + simpl in Hsize.
      assert (Hbd : blk_size bd + 1 < n) by lia.
      assert (Hm : blk_size bd < blk_size bd + 1) by lia.
      assert (Hrest : S (fold_right (fun p acc => blk_size (match p with (_,_,bd0) => bd0 end) + acc) 0 brs') < n)
        by lia.
      split.
      * exact (IHn (blk_size bd + 1) Hbd bd Hm s (proj1 Hnbc)).
      * apply IHbrs; [exact Hrest | exact (proj2 Hnbc)].
  - simpl in *. destruct e; simpl; try exact I; try exact Hnbc; destruct Hnbc.
Qed.

Lemma NoBareFreeOrChoiceB_rename :
  forall s b, NoBareFreeOrChoiceB b -> NoBareFreeOrChoiceB (rename_b s b).
Proof.
  intros s b H.
  exact (NoBareFreeOrChoiceB_rename_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) s H).
Qed.

Definition NoBareFreeOrChoiceProgWF (P : Prog) : Prop :=
  forall f ps body, P f = Some (ps, body) -> NoBareFreeOrChoiceB body.

(* The payoff: given the program-wide restriction above, GEval's own result
   can NEVER be a bare, direct Free or Choice node -- provable by a PLAIN
   structural induction on GEval itself, no scope restriction needed at all
   (unlike NEval_left_let_chain_to_value, which has to actually CONSTRUCT a
   Nat-heap derivation and gets stuck on the six case-tail GEval rules; this
   lemma only needs to track a SHAPE fact through them, and NoBareFreeOrChoiceB
   restricted to a BCase doesn't even depend on the scrutinee, so every
   BCase-to-BCase step -- G_CaseFwd/G_CaseChoice/G_CaseFun's own second
   premise -- reuses the SAME hypothesis unchanged). *)
Lemma GEval_result_not_free_or_choice :
  forall P, NoBareFreeOrChoiceProgWF P ->
  forall G e G1 vx, GEval P G e G1 vx -> NoBareFreeOrChoiceB e ->
  vx <> GExpr EFree /\ (forall y z, vx <> GExpr (EChoice y z)).
Proof.
  intros P HPWF2 G e G1 vx H.
  induction H as
    [ G0
    | G0
    | G0 c0 args0
    | G0 xh yh
    | G0 xh
    | G0 G1' f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH
    | G0 G1' xh eh k v1 HxFresh Hrec IH
    | G0 xh brs Hgx0
    | G0 xh yh brs G1' v1 Hgx0 Hrec IH
    | G0 xh f args brs G1' vx0 G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2
    | G0 xh yh zh brs G1' v1 Hgx0 Hrec IH
    | G0 xh c zs brs ys body G1' v1 Hgx0 HIn Hlen Hrec IH
    | G0 xh c1 ys1 body1 brs G1' v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH
    ]; intro Hnbfc.
  - (* G_Bot *) split; [discriminate | intros y z Hcontra; discriminate Hcontra].
  - (* G_Free *) simpl in Hnbfc. destruct Hnbfc.
  - (* G_Con *) split; [discriminate | intros y z Hcontra; discriminate Hcontra].
  - (* G_Choice *) simpl in Hnbfc. destruct Hnbfc.
  - (* G_Var *) split; [discriminate | intros y z Hcontra; discriminate Hcontra].
  - (* G_Fun *)
    assert (Hnbfcbody : NoBareFreeOrChoiceB (rename_b s body))
      by (apply NoBareFreeOrChoiceB_rename; exact (HPWF2 f ps body HPf)).
    exact (IH Hnbfcbody).
  - (* G_Let *) exact (IH Hnbfc).
  - (* G_CaseBot *) split; [discriminate | intros y z Hcontra; discriminate Hcontra].
  - (* G_CaseFwd: same brs0, scrutinee-independent, reuse Hnbfc directly *)
    exact (IH Hnbfc).
  - (* G_CaseFun: Hrec2's own brs is the SAME brs, reuse Hnbfc directly (Hrec1/IH1 unused) *)
    exact (IH2 Hnbfc).
  - (* G_CaseChoice: same brs0, reuse Hnbfc directly *)
    exact (IH Hnbfc).
  - (* G_CaseCon *)
    assert (Hnbfcbrs : NoBareFreeOrChoiceB body)
      by exact (NoBareFreeOrChoiceB_in brs c ys body HIn Hnbfc).
    assert (Hnbfcbody : NoBareFreeOrChoiceB (rename_b (zipsubst ys zs) body))
      by (apply NoBareFreeOrChoiceB_rename; exact Hnbfcbrs).
    exact (IH Hnbfcbody).
  - (* G_CaseConFree *)
    assert (HInhd : In (c1, ys1, body1) brs).
    { destruct brs as [| p brs']; [discriminate Hhd | ].
      injection Hhd as Hhd. subst p. left. reflexivity. }
    assert (Hnbfcbrs : NoBareFreeOrChoiceB body1)
      by exact (NoBareFreeOrChoiceB_in brs c1 ys1 body1 HInhd Hnbfc).
    assert (Hnbfcbody : NoBareFreeOrChoiceB (rename_b (zipsubst ys1 ws) body1))
      by (apply NoBareFreeOrChoiceB_rename; exact Hnbfcbrs).
    exact (IH Hnbfcbody).
Qed.

Theorem theorem2 :
  forall P, NoAliasLetProgWF P -> NoBareFreeOrChoiceProgWF P ->
  forall G e G' v, GEval P G e G' v ->
  forall Gam, HeapCorr G Gam -> NoVarThunk G -> NoAliasLetB e ->
    WellFoundedFwd G -> ChainConsistent G Gam -> AliasConsistent G Gam ->
  (forall c args, CorrV G' v (BExpr (ECon c args)) ->
     exists Gam', NEval_left P nil Gam e Gam' (BExpr (ECon c args)) /\ HeapCorr G' Gam')
  /\
  (forall x brs, e = BCase x brs ->
     forall F Gmid x', NEval_left P F Gam (BExpr (EVar x)) Gmid (BExpr (EVar x')) ->
     ContractLoc G' x x').
Proof.
  intros P HPWF HNBFC G e G' v H.
  induction H as
    [ G0                                                                (* G_Bot *)
    | G0                                                                (* G_Free *)
    | G0 c0 args0                                                       (* G_Con *)
    | G0 x0 y0                                                          (* G_Choice *)
    | G0 x0                                                             (* G_Var *)
    | G0 G1 f args ps body v1 s HPf Hlen Hinj Hmatch Hfresh Hrec IH     (* G_Fun *)
    | G0 G1 x0 e0 k v1 HxFresh Hrec IH                                  (* G_Let *)
    | G0 x0 brs0 Hgx0                                                   (* G_CaseBot *)
    | G0 x0 y0 brs0 G1 v1 Hgx0 Hrec IH                                  (* G_CaseFwd *)
    | G0 x0 f0 args0 brs0 G1 vx G2 v1 Hgx0 Hrec1 IH1 Hrec2 IH2          (* G_CaseFun *)
    | G0 x0 y0 z0 brs0 G1 v1 Hgx0 Hrec IH                               (* G_CaseChoice *)
    | G0 x0 c zs brs0 ys body G1 v1 Hgx0 HIn Hlen Hrec IH               (* G_CaseCon *)
    | G0 x0 c1 ys1 body1 brs0 G1 v1 ws Hgx0 Hhd Hlen HND Hfresh Hrec IH (* G_CaseConFree *)
    ]; intros Gam HGam HNVT HNAL HWF HCC HAC.
  - (* G_Bot *)
    split.
    + intros c args Hcorr. exfalso. inversion Hcorr.
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Free *)
    split.
    + intros c args Hcorr. exfalso. inversion Hcorr.
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Con *)
    split.
    + intros c args Hcorr.
      assert (Heq := CorrV_direct_eq G0 (ECon c0 args0) (ECon c args) Hcorr).
      injection Heq as Heqc Heqargs. subst c args.
      exists Gam. split; [apply NL_ValCon | exact HGam].
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Choice *)
    split.
    + intros c args Hcorr. exfalso. inversion Hcorr.
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Var *)
    split.
    + intros c args Hcorr.
      destruct (CorrVTerm_inv G0 x0 (BExpr (ECon c args)) (CorrV_fwd_inv G0 x0 (BExpr (ECon c args)) Hcorr))
        as [y [yc [Hcl [Hgy Hlc]]]].
      destruct yc as [z | | | y1 y2 | f0 args0 | c0 args0]; simpl in Hlc; try discriminate Hlc.
      injection Hlc as Hlc1 Hlc2. subst c0 args0.
      exact (force_var P G0 x0 y Hcl c args Hgy Gam HGam HNVT).
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Fun *)
    split.
    + intros c args' Hcorr.
      assert (HNALbody : NoAliasLetB (rename_b s body))
        by (apply NoAliasLetB_rename; exact (HPWF f ps body HPf)).
      destruct (IH Gam HGam HNVT HNALbody HWF HCC HAC) as [IH1 _].
      destruct (IH1 c args' Hcorr) as [Gam1 [HNE HHC1]].
      assert (HfreshGam : forall y0, ~ In y0 ps -> Gam (s y0) = None).
      { intros y0 Hin. specialize (Hfresh y0 Hin).
        specialize (HGam (s y0)) as HGamsy0. rewrite Hfresh in HGamsy0. exact HGamsy0. }
      exists Gam1. split.
      * eapply NL_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact HfreshGam | exact HNE].
      * exact HHC1.
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_Let *)
    destruct HNAL as [Hne0 HNALk].
    split.
    + intros c args Hcorr.
      assert (HGamx0 : Gam x0 = None)
        by (specialize (HGam x0); rewrite HxFresh in HGam; exact HGam).
      assert (HHCext : HeapCorr (hupd G0 x0 (GExpr e0)) (hupd Gam x0 (let_content x0 e0)))
        by exact (HeapCorr_extend G0 Gam x0 e0 HGam HxFresh).
      assert (HNVText : NoVarThunk (hupd G0 x0 (GExpr e0)))
        by exact (NoVarThunk_extend G0 x0 e0 HNVT HxFresh Hne0).
      assert (HWText : WellFoundedFwd (hupd G0 x0 (GExpr e0)))
        by exact (WellFoundedFwd_extend G0 x0 e0 HWF HxFresh).
      assert (HCCext : ChainConsistent (hupd G0 x0 (GExpr e0)) (hupd Gam x0 (let_content x0 e0)))
        by exact (ChainConsistent_extend G0 Gam x0 e0 HCC HWF HxFresh).
      assert (HACext : AliasConsistent (hupd G0 x0 (GExpr e0)) (hupd Gam x0 (let_content x0 e0)))
        by exact (AliasConsistent_extend G0 Gam x0 e0 HAC HWF HxFresh).
      destruct (IH (hupd Gam x0 (let_content x0 e0)) HHCext HNVText HNALk HWText HCCext HACext) as [IH1 _].
      destruct (IH1 c args Hcorr) as [Gam' [HNE HHC]].
      exists Gam'. split.
      * eapply NL_Let; [exact HGamx0 | exact HNE].
      * exact HHC.
    + intros x brs Hcontra. discriminate Hcontra.
  - (* G_CaseBot *)
    split.
    + intros c args Hcorr. exfalso.
      assert (Heq := CorrV_direct_eq G0 EBot (ECon c args) Hcorr). discriminate Heq.
    + intros x brs Heqxbrs. injection Heqxbrs as Heqx Heqbrs. subst x brs.
      intros F Gmid x' Hforce. exfalso.
      assert (Hsome : G0 x0 <> None) by (rewrite Hgx0; discriminate).
      assert (Hnofwd : forall y0, G0 x0 <> Some (GFwd y0))
        by (intros y0 Heq; rewrite Hgx0 in Heq; discriminate Heq).
      destruct (HeapCorr_witness_nonfwd G0 Gam x0 HGam Hsome Hnofwd) as [b [Hb HCE]].
      destruct (CorrE_forced_shape G0 x0 b HCE) as
        [ [c0 [args0 [Hgx0' Hbeq]]]
        | [ [Hgx0' Hbeq]
          | [ [f0 [args0 [Hgx0' Hbeq]]]
            | [ [ya [yb [Hgx0' Hbeq]]]
              | [ [z0 [Hgx0' Hbeq]]
                | [ [Hgx0' Hbeq]
                  | [ [y2 [Hgx0' Hbeq]]
                    | [y2 [z0 [c0 [args0 [Hgx0' [Hcl0 [Hz0 Hbeq]]]]]]] ] ] ] ] ] ] ];
        rewrite Hgx0 in Hgx0'; try discriminate Hgx0'.
      subst b.
      destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hforce) as
        [ [Hgamx0 _] | [ [Hgamx0 _] | [ [Hgamx0 _] | [_ [e0 [G1 [Hgamx0 [_ [Hne2 [_ [Hrec _]]]]]]]]]]];
        rewrite Hb in Hgamx0; try discriminate Hgamx0.
      injection Hgamx0 as Hgamx0. subst e0.
      inversion Hrec.
  - (* G_CaseFwd *)
    assert (Hx0y0 : x0 <> y0).
    { intro Heqxy; subst y0.
      destruct (GEval_case_gives_ContractLoc P G0 x0 brs0 G1 v1
                  (G_CaseFwd P G0 x0 x0 brs0 G1 v1 Hgx0 Hrec)) as [w Hcl].
      exact (ContractLoc_no_selfFwd G0 x0 w Hcl Hgx0). }
    split.
    + intros c args Hcorr.
      destruct (IH Gam HGam HNVT HNAL HWF HCC HAC) as [IH1 _].
      destruct (IH1 c args Hcorr) as [Gamy0 [HNEy HHCy0]].
      destruct (NEval_left_bcase_shape P nil Gam y0 brs0 Gamy0 (BExpr (ECon c args)) HNEy) as
        [ [c' [zs [ys [body [Gmid [Hforcey0 [HIn [Hlen Hbody]]]]]]]]
        | [x' [Gmid [c1' [ys1 [body1 [ws [Hforcey0 [Hhd [Hlenws [HNDws [Hfrws Hbodyguess]]]]]]]]]]] ].
      * (* NL_Select shape: y0's own scrutinee-forcing reaches an achieved constructor directly *)
        assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]].
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        -- destruct (CorrE_forced_shape G0 x0 b HCE) as
             [ [c0 [args0 [Hg1 Hb1]]]
             | [ [Hg1 Hb1]
               | [ [f1 [args1 [Hg1 Hb1]]]
                 | [ [y1 [y2 [Hg1 Hb1]]]
                   | [ [z1 [Hg1 Hb1]]
                     | [ [Hg1 Hb1]
                       | [ [y1 [Hg1 Hb1]]
                         | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
             rewrite Hgx0 in Hg1; try discriminate Hg1.
           ++ (* CorrE_FwdHere: Gam x0 = EVar y0 exactly ("clean" alias case) --
                 HeapCorr_fwd_transfer_fwdhere_con does the whole construction. *)
              injection Hg1 as Hg1. subst y1. subst b.
              destruct (HeapCorr_fwd_transfer_fwdhere_con P G0 Gam HGam x0 y0 Hx0y0 Hgx0 Hb
                          brs0 c' zs ys body Gmid Gamy0 (BExpr (ECon c args))
                          Hforcey0 HIn Hlen Hbody) as [Gam'' [HNEfinal HHCtransfer]].
              exists Gam''. split.
              { exact HNEfinal. }
              { exact (HHCtransfer G1 (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0) HHCy0). }
           ++ (* CorrE_FwdAchievedCon: Gam x0 already achieved directly, to
                 c0/args0 -- ChainConsistent forces Gam y0 to the SAME
                 value, so y0's own forcing (Hforcey0) must be the trivial
                 NL_VarCons case, and x0's own case-body IS Hbody verbatim
                 (Gmid = Gam, no transport needed at all). *)
              injection Hg1 as Hg1. subst y1. subst b.
              assert (Hgamy0 : Gam y0 = Some (BExpr (ECon c0 args0)))
                by exact (HCC x0 y0 Hgx0 c0 args0 Hb).
              destruct (NEval_left_evar_shape P nil Gam y0 Gmid (BExpr (ECon c' zs)) Hforcey0) as
                [ [Hcase1 [HeqGmid _]]
                | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1' [Hz [Hne1 [_ [_ [_ HeqGmid]]]]]]]]] ] ].
              ** rewrite Hgamy0 in Hcase1. injection Hcase1 as Hcase1a Hcase1b.
                 assert (Hb' : Gam x0 = Some (BExpr (ECon c' zs))) by (rewrite <- Hcase1a, <- Hcase1b; exact Hb).
                 subst Gmid.
                 exists Gamy0. split.
                 { eapply NL_Select.
                   - apply NL_VarCons. exact Hb'.
                   - exact HIn.
                   - exact Hlen.
                   - exact Hbody. }
                 { exact HHCy0. }
              ** rewrite Hgamy0 in Hcase2. discriminate Hcase2.
              ** rewrite Hgamy0 in Hcase3. discriminate Hcase3.
              ** rewrite Hgamy0 in Hz. injection Hz as Hz. exfalso. exact (Hne1 c0 args0 (eq_sym Hz)).
        -- (* CorrE3 disjunct 2: Gam x0's witness is a VarChase-based
              skip-ahead certificate, not necessarily matching y0 directly.
              Use VarChase_first_step (an isolated, self-contained lemma)
              to extract b's own shape and how the chase used it, WITHOUT
              destructuring HVCd directly in this large context (fragile --
              see DEAD_ENDS.md). *)
           destruct (VarChase_first_step Gam x0 (BExpr (ECon cd argsd)) HVCd) as
             [b1 [Hb1 [Heqb1 | [w' [Heqb1 [Hnew'x0 Hrecw0]]]]]];
           rewrite Hb in Hb1; injection Hb1 as Hb1; subst b1; rewrite Heqb1 in Hb.
           ++ (* b = target directly: already achieved -- same construction
                 as the CorrE_FwdAchievedCon branch above, via ChainConsistent. *)
              assert (Hgamy0 : Gam y0 = Some (BExpr (ECon cd argsd)))
                by exact (HCC x0 y0 Hgx0 cd argsd Hb).
              destruct (NEval_left_evar_shape P nil Gam y0 Gmid (BExpr (ECon c' zs)) Hforcey0) as
                [ [Hcase1 [HeqGmid _]]
                | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e2 [G1' [Hz [Hne1 [_ [_ [_ HeqGmid]]]]]]]]] ] ].
              ** rewrite Hgamy0 in Hcase1. injection Hcase1 as Hcase1a Hcase1b.
                 assert (Hb' : Gam x0 = Some (BExpr (ECon c' zs))) by (rewrite <- Hcase1a, <- Hcase1b; exact Hb).
                 subst Gmid.
                 exists Gamy0. split.
                 { eapply NL_Select; [apply NL_VarCons; exact Hb' | exact HIn | exact Hlen | exact Hbody]. }
                 { exact HHCy0. }
              ** rewrite Hgamy0 in Hcase2. discriminate Hcase2.
              ** rewrite Hgamy0 in Hcase3. discriminate Hcase3.
              ** rewrite Hgamy0 in Hz. injection Hz as Hz. exfalso. exact (Hne1 cd argsd (eq_sym Hz)).
           ++ (* b = EVar w', w' <> x0: skip-ahead scenario. *)
              destruct (Nat.eq_dec w' y0) as [Heqwy0 | Hnewy0].
              ** (* w' = y0: b is EXACTLY EVar y0 -- same clean construction
                    as the CorrE_FwdHere branch above. *)
                 subst w'.
                 destruct (HeapCorr_fwd_transfer_fwdhere_con P G0 Gam HGam x0 y0 Hx0y0 Hgx0 Hb
                             brs0 c' zs ys body Gmid Gamy0 (BExpr (ECon c args))
                             Hforcey0 HIn Hlen Hbody) as [Gam'' [HNEfinal HHCtransfer]].
                 exists Gam''. split.
                 { exact HNEfinal. }
                 { exact (HHCtransfer G1 (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0) HHCy0). }
              ** assert (Hgamy0w' : Gam y0 = Some (BExpr (EVar w')))
                   by exact (HAC x0 y0 Hgx0 w' Hb Hnewy0).
                 (* Hcase2/Hcase3 are discharged via their OWN "v = EVar y0"
                    component (structurally impossible against our fixed,
                    Con-shaped target), NOT via Gam y0 -- since Hgamy0w' is
                    itself EVar-shaped, rewriting it into Hcase2's "Gam y0 =
                    EVar y0" component would NOT be discriminable (same
                    constructors, just w' vs y0). *)
                 destruct (NEval_left_evar_shape P nil Gam y0 Gmid (BExpr (ECon c' zs)) Hforcey0) as
                   [ [Hcase1 _]
                   | [ [_ [_ Heqv2]]
                     | [ [_ [_ Heqv3]]
                       | [_ [e2 [Gmid_inner [Hz [Hne1 [Hne2 [Hne3 [Hrecw HeqGmid]]]]]]]]] ] ];
                   try discriminate Heqv2; try discriminate Heqv3;
                   try (rewrite Hgamy0w' in Hcase1; discriminate Hcase1).
                 rewrite Hgamy0w' in Hz. injection Hz as Hz. subst e2.
                 subst Gmid.
                 assert (Hgmidy0 : hupd Gmid_inner y0 (BExpr (ECon c' zs)) y0 = Some (BExpr (ECon c' zs)))
                   by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
                 assert (Hgamy0y0 : Gamy0 y0 = Some (BExpr (ECon c' zs)))
                   by exact (NEval_left_con_persists P nil (hupd Gmid_inner y0 (BExpr (ECon c' zs)))
                               (rename_b (zipsubst ys zs) body) Gamy0 (BExpr (ECon c args)) Hbody y0 c' zs Hgmidy0).
                 destruct (skip_ahead_reconcile_test P x0 y0 w' c' zs Gam Gmid_inner
                             (BExpr (ECon c args)) Hx0y0 Hnewy0 Hnew'x0
                             Hb Hgamy0w' Hrecw (rename_b (zipsubst ys zs) body) Gamy0 Hbody)
                   as [Gam' [Hforcex0 [Gamx0 [Hbodyx0 [HeqGamx0 [Hgamx0x0 Hgamx0y0]]]]]].
                 exists Gamx0. split.
                 { eapply NL_Select; [exact Hforcex0 | exact HIn | exact Hlen | exact Hbodyx0]. }
                 { assert (Hgx0fwd_G1 : G1 x0 = Some (GFwd y0))
                     by exact (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0).
                   destruct (HeapCorr_con_to_contractloc G1 Gamy0 y0 c' zs HHCy0 Hgamy0y0) as [ytgt [Hcl Hz]].
                   assert (Hginw' : Gmid_inner w' = Some (BExpr (ECon c' zs)))
                     by exact (NEval_left_own_slot P (y0::nil) Gam w' Gmid_inner (BExpr (ECon c' zs)) Hrecw).
                   assert (Hrecw_nil' : NEval_left P nil Gam (BExpr (EVar w')) Gmid_inner (BExpr (ECon c' zs))).
                   { apply (NEval_left_guard_shrink P (y0::nil) nil (fun w0 H => False_ind _ H) Gam
                              (BExpr (EVar w')) Gmid_inner (BExpr (ECon c' zs)) Hrecw). }
                   assert (Hginx0' : Gmid_inner x0 = Some (BExpr (EVar w')))
                     by exact (NEval_left_alias_persists_through_force P x0 w' (not_eq_sym Hnew'x0)
                                 Gam Gmid_inner (BExpr (ECon c' zs)) Hrecw_nil' Hb).
                   assert (Hgmidx0 : hupd Gmid_inner y0 (BExpr (ECon c' zs)) x0 = Some (BExpr (EVar w')))
                     by (rewrite (hupd_neq Gmid_inner y0 (BExpr (ECon c' zs)) x0 Hx0y0); exact Hginx0').
                   assert (Hgmidw' : hupd Gmid_inner y0 (BExpr (ECon c' zs)) w' = Some (BExpr (ECon c' zs)))
                     by (rewrite (hupd_neq Gmid_inner y0 (BExpr (ECon c' zs)) w' Hnewy0); exact Hginw').
                   destruct (NEval_left_alias_or_con_persists P x0 w' c' zs (not_eq_sym Hnew'x0) nil
                               (hupd Gmid_inner y0 (BExpr (ECon c' zs))) (rename_b (zipsubst ys zs) body) Gamy0
                               (BExpr (ECon c args)) Hbody (or_introl Hgmidx0) Hgmidw')
                     as [Hgamy0x0_or Hgamy0w'con].
                   assert (Hchase_x0_y0 : VarChase Gamy0 x0 (BExpr (ECon c' zs))).
                   { destruct Hgamy0x0_or as [Heq1 | Heq1].
                     - eapply VChase_Hop; [exact Heq1 | exact Hnew'x0 | ].
                       apply VChase_Here; [exact Hgamy0w'con | intros ww Hcontra; discriminate Hcontra].
                     - apply VChase_Here; [exact Heq1 | intros ww Hcontra; discriminate Hcontra]. }
                   assert (HHCupdated : HeapCorr G1 (hupd Gamy0 x0 (BExpr (ECon c' zs))))
                     by exact (HeapCorr_update_achieved G1 Gamy0 x0 y0 ytgt c' zs HHCy0 Hgx0fwd_G1 Hcl Hz Hchase_x0_y0).
                   destruct Hgamx0y0 as [Hy0evar | Hy0con].
                   - (* y0's own slot ends up back at EVar w' (its ORIGINAL, pre-forcing
                        value) -- downgrade y0 within the x0-updated heap too, then match
                        Gamx0 pointwise EVERYWHERE against the doubly-updated heap. *)
                     assert (Hgamx0w' : Gamx0 w' = Some (BExpr (ECon c' zs)))
                       by (rewrite (HeqGamx0 w' Hnew'x0 Hnewy0); exact Hgamy0w'con).
                     assert (Hupdy0con : hupd Gamy0 x0 (BExpr (ECon c' zs)) y0 = Some (BExpr (ECon c' zs)))
                       by (rewrite (hupd_neq Gamy0 x0 (BExpr (ECon c' zs)) y0 (not_eq_sym Hx0y0)); exact Hgamy0y0).
                     assert (Hupdw'con : hupd Gamy0 x0 (BExpr (ECon c' zs)) w' = Some (BExpr (ECon c' zs)))
                       by (rewrite (hupd_neq Gamy0 x0 (BExpr (ECon c' zs)) w' Hnew'x0); exact Hgamy0w'con).
                     assert (Hdowny0 : (hupd (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w'))) y0
                                       = Some (BExpr (EVar w')))
                       by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
                     assert (Hdownw' : (hupd (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w'))) w'
                                       = Some (BExpr (ECon c' zs))).
                     { rewrite (hupd_neq (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w')) w' Hnewy0).
                       exact Hupdw'con. }
                     assert (HCEy0_v2 : CorrE3 G1 (hupd (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w')))
                                          y0 (BExpr (EVar w')))
                       by exact (HeapCorr_evar_witness_graph_persists G0 Gam HGam HNVT y0 w' (not_eq_sym Hnewy0) Hgamy0w'
                                   P (y0::nil) Gmid_inner c' zs Hrecw
                                   (BCase y0 brs0) G1 v1 Hrec
                                   (hupd (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w')))
                                   Hdowny0 Hdownw').
                     assert (HHCdown : HeapCorr G1 (hupd (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w'))))
                       by exact (HeapCorr_downgrade_evar G1 (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 w' c' zs
                                   HHCupdated Hupdy0con Hupdw'con Hnewy0 HCEy0_v2).
                     eapply HeapCorr_pointwise; [exact HHCdown | ].
                     intro q.
                     destruct (Nat.eq_dec q y0) as [Heqqy0 | Hneqqy0].
                     + subst q. rewrite Hy0evar. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
                     + destruct (Nat.eq_dec q x0) as [Heqqx0 | Hneqqx0].
                       * subst q. rewrite Hgamx0x0.
                         rewrite (hupd_neq (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w')) x0
                                    Hx0y0).
                         unfold hupd; rewrite Nat.eqb_refl; reflexivity.
                       * rewrite (HeqGamx0 q Hneqqx0 Hneqqy0).
                         rewrite (hupd_neq (hupd Gamy0 x0 (BExpr (ECon c' zs))) y0 (BExpr (EVar w')) q Hneqqy0).
                         rewrite (hupd_neq Gamy0 x0 (BExpr (ECon c' zs)) q Hneqqx0). reflexivity.
                   - (* y0's own slot ends up promoted to Con c' zs too -- Gamx0 matches
                        the single x0-update EVERYWHERE, including at y0 (same value). *)
                     eapply HeapCorr_pointwise; [exact HHCupdated | ].
                     intro q.
                     destruct (Nat.eq_dec q x0) as [Heqqx0 | Hneqqx0].
                     + subst q. rewrite Hgamx0x0. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
                     + destruct (Nat.eq_dec q y0) as [Heqqy0 | Hneqqy0].
                       * subst q. rewrite Hy0con.
                         rewrite (hupd_neq Gamy0 x0 (BExpr (ECon c' zs)) y0 (not_eq_sym Hx0y0)). exact (eq_sym Hgamy0y0).
                       * rewrite (HeqGamx0 q Hneqqx0 Hneqqy0).
                         rewrite (hupd_neq Gamy0 x0 (BExpr (ECon c' zs)) q Hneqqx0). reflexivity. }
      * (* NL_Guess shape: y0's own scrutinee-forcing reaches a free variable x',
           narrowed by Guess. Since forcing y0 lands on a FREE variable (not an
           achieved constructor), x0's own Nat-heap witness CANNOT be the
           VarChase-skip-ahead disjunct (that disjunct's own graph-level
           achieved chain would force Hforcey0 to land on that SAME achieved
           constructor via NEval_left_force_reaches_achieved -- contradiction);
           nor can it be any CorrE case other than FwdHere (all others need a
           non-GFwd graph shape at x0, contradicting Hgx0). So Gam x0 = EVar y0
           EXACTLY is the ONLY possibility here -- no case split needed at all. *)
        assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]].
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        -- destruct (CorrE_forced_shape G0 x0 b HCE) as
             [ [c0 [args0 [Hg1 Hb1]]]
             | [ [Hg1 Hb1]
               | [ [f1 [args1 [Hg1 Hb1]]]
                 | [ [y1 [y2 [Hg1 Hb1]]]
                   | [ [z1 [Hg1 Hb1]]
                     | [ [Hg1 Hb1]
                       | [ [y1 [Hg1 Hb1]]
                         | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
             rewrite Hgx0 in Hg1; try discriminate Hg1.
           ++ (* FwdHere: Gam x0 = EVar y0 exactly. *)
              injection Hg1 as Hg1. subst y1. subst b.
              assert (IH2 := proj2 (IH Gam HGam HNVT HNAL HWF HCC HAC)).
              assert (Hclx' : ContractLoc G1 y0 x') by exact (IH2 y0 brs0 eq_refl nil Gmid x' Hforcey0).
              destruct (HeapCorr_fwd_transfer_fwdhere_free P G0 Gam HGam x0 y0 Hgx0 Hx0y0 Hb
                          brs0 x' c1' ys1 body1 ws Gmid Gamy0 (BExpr (ECon c args))
                          Hforcey0 Hhd Hlenws HNDws Hfrws Hbodyguess) as [Gam'' [HNEfinal HHCtransfer]].
              exists Gam''. split.
              { exact HNEfinal. }
              { exact (HHCtransfer G1 (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0)
                         (fun _ => Hclx') HHCy0). }
           ++ (* FwdAchievedCon: IMPOSSIBLE -- Gam x0 already achieved directly
                 would force Hforcey0 (via ChainConsistent, matching y0's own
                 witness) to land on that SAME achieved value, contradicting
                 Hforcey0's own free-variable target. *)
              injection Hg1 as Hg1. subst y1. subst b.
              assert (Hgamy0 : Gam y0 = Some (BExpr (ECon c0 args0)))
                by exact (HCC x0 y0 Hgx0 c0 args0 Hb).
              destruct (NEval_left_evar_shape P nil Gam y0 Gmid (BExpr (EVar x')) Hforcey0) as
                [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1' [Hz [Hne1 _]]]]]]]].
              ** rewrite Hgamy0 in Hcase1. discriminate Hcase1.
              ** rewrite Hgamy0 in Hcase2. discriminate Hcase2.
              ** rewrite Hgamy0 in Hcase3. discriminate Hcase3.
              ** rewrite Hgamy0 in Hz. injection Hz as Hz. exfalso. exact (Hne1 c0 args0 (eq_sym Hz)).
        -- (* CorrE3 disjunct 2: IMPOSSIBLE -- x0's own skip-ahead witness
              forwards (via G0, functionally) to the SAME y0 as Hgx0, so its
              achieved chain is REALLY an achieved chain for y0 itself; combined
              with HeapCorr_achieved_to_VarChase (graph-achieved implies a
              STATIC VarChase) and NEval_left_force_matches_VarChase (a STATIC
              VarChase forces ANY dynamic forcing to compute that SAME value),
              this contradicts Hforcey0's own free-variable target directly --
              no need for a HeapCorr-based NEval_left_force_reaches_achieved
              port at all. *)
           exfalso.
           assert (Hydeq : yd = y0) by (rewrite Hgx0 in Hgxfwd; injection Hgxfwd as Hgxfwd; exact (eq_sym Hgxfwd)).
           subst yd.
           destruct (ContractLoc_to_N G0 y0 zd Hcld) as [n Hcln].
           assert (Hvcy0 : VarChase Gam y0 (BExpr (ECon cd argsd)))
             by exact (HeapCorr_achieved_to_VarChase G0 Gam HGam n y0 zd cd argsd Hcln Hzd).
           assert (Heqv := NEval_left_force_matches_VarChase Gam y0 (BExpr (ECon cd argsd)) Hvcy0 cd argsd eq_refl
                              P nil Gmid (BExpr (EVar x')) Hforcey0).
           discriminate Heqv.
    + intros x brs Heqxbrs. injection Heqxbrs as Heqx Heqbrs. subst x brs.
      intros F Gmid1 x' Hforce.
      destruct (NEval_left_evar_shape P F Gam x0 Gmid1 (BExpr (EVar x')) Hforce) as
        [ [Hcase1 [_ [c0 [args0 Heqv1]]]]
        | [ [Hcase2 _]
          | [ [Hcase3 _]
            | [HnInF [e0 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec1 HeqGmid1]]]]]]]]] ] ].
      * (* Hcase1: already achieved directly -- contradicts v = EVar x'. *)
        discriminate Heqv1.
      * (* Hcase2: Gam x0 = EVar x0 (self-loop) -- IMPOSSIBLE given G0 x0 = GFwd y0,
           since CorrE3's disjunct 2 can NEVER validate a self-loop witness
           (VarChase from a self-loop can use neither VChase_Here, which would
           need the self-loop's OWN content to already be Con-shaped, nor
           VChase_Hop, whose w' <> w precondition a self-loop directly
           violates) -- and disjunct 1's only self-loop-producing case,
           CorrE_Free, needs G0 x0 = EFree, contradicting Hgx0 directly. *)
        exfalso.
        assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]]. rewrite Hcase2 in Hb. injection Hb as Hb. subst b.
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        -- destruct (CorrE_forced_shape G0 x0 (BExpr (EVar x0)) HCE) as
             [ [c1 [args1 [Hg1 Hb1]]]
             | [ [Hg1 Hb1]
               | [ [f1 [args1 [Hg1 Hb1]]]
                 | [ [y1 [y2 [Hg1 Hb1]]]
                   | [ [z1 [Hg1 Hb1]]
                     | [ [Hg1 Hb1]
                       | [ [y1 [Hg1 Hb1]]
                         | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ]; try discriminate Hb1.
           ++ (* Free: Hb1 : EVar x0 = EVar x0 (trivially true, b was ALREADY fixed
                 to EVar x0) -- the real contradiction is Hg1 vs Hgx0 (EFree vs GFwd). *)
              congruence.
           ++ (* VarThunk: Hg1 : G0 x0 = GExpr(EVar z1), vs Hgx0 : G0 x0 = GFwd y0. *)
              congruence.
           ++ (* FwdHere: Hb1 : EVar x0 = EVar y1, Hg1 : G0 x0 = GFwd y1, vs Hgx0 : G0 x0 = GFwd y0. *)
              exact (Hx0y0 (ltac:(congruence))).
        -- destruct (VarChase_first_step Gam x0 (BExpr (ECon cd argsd)) HVCd) as
             [b1 [Hb1 [Heqb1 | [w' [Heqb1 [Hnew'x0 _]]]]]].
           ++ exfalso. congruence.
           ++ exact (Hnew'x0 (ltac:(congruence))).
      * (* Hcase3: Gam x0 = EFree -- IMPOSSIBLE, same pattern: disjunct 1's
           CorrE_Free needs G0 x0 = EFree (contradicts Hgx0), and disjunct 2's
           VarChase can use neither VChase_Here (EFree isn't Con-shaped) nor
           VChase_Hop (EFree isn't EVar-shaped). *)
        exfalso.
        assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]]. rewrite Hcase3 in Hb. injection Hb as Hb. subst b.
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        -- destruct (CorrE_forced_shape G0 x0 (BExpr EFree) HCE) as
             [ [c1 [args1 [Hg1 Hb1]]]
             | [ [Hg1 Hb1]
               | [ [f1 [args1 [Hg1 Hb1]]]
                 | [ [y1 [y2 [Hg1 Hb1]]]
                   | [ [z1 [Hg1 Hb1]]
                     | [ [Hg1 Hb1]
                       | [ [y1 [Hg1 Hb1]]
                         | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ]; discriminate Hb1.
        -- destruct (VarChase_first_step Gam x0 (BExpr (ECon cd argsd)) HVCd) as
             [b1 [Hb1 [Heqb1 | [w' [Heqb1 [Hnew'x0 _]]]]]]; congruence.
      * (* Hcase4: genuine recursion -- x0's own CorrE3 witness is either the
           "clean" FwdHere alias EVar y0 (use IH's own second conjunct,
           recursively, on y0's forcing) or a skip-ahead alias EVar w'
           (w' <> x0) whose OWN further chase is ALREADY known (via
           HeapCorr_achieved_to_VarChase, from the underlying achieved graph
           fact) to reach an achieved constructor -- contradicting Hrec1's
           own free-variable result via NEval_left_force_matches_VarChase, so
           this sub-case never actually happens. *)
        assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]]. rewrite Hz in Hb. injection Hb as Hb. subst b.
        destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
        -- destruct (CorrE_forced_shape G0 x0 e0 HCE) as
             [ [c1 [args1 [Hg1 Hb1]]]
             | [ [Hg1 Hb1]
               | [ [f1 [args1 [Hg1 Hb1]]]
                 | [ [y1 [y2 [Hg1 Hb1]]]
                   | [ [z1 [Hg1 Hb1]]
                     | [ [Hg1 Hb1]
                       | [ [y1 [Hg1 Hb1]]
                         | [y1 [z1 [c1 [args1 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ].
           ++ exfalso. exact (Hne1 c1 args1 Hb1).
           ++ exfalso. exact (Hne2 Hb1).
           ++ (* EFun: e0 = EFun f1 args1 -- Hg1 : G0 x0 = GExpr(EFun..), contradicts Hgx0 *)
              exfalso. congruence.
           ++ (* EChoice: contradicts Hgx0 *)
              exfalso. congruence.
           ++ (* VarThunk: contradicts Hgx0 *)
              exfalso. congruence.
           ++ (* Bot: contradicts Hgx0 *)
              exfalso. congruence.
           ++ (* FwdHere: e0 = EVar y1, and Hg1: G0 x0 = GFwd y1, combined w/ Hgx0: y1 = y0 *)
              assert (Heqy1 : y1 = y0) by congruence.
              subst y1.
              assert (IH2 := proj2 (IH Gam HGam HNVT HNAL HWF HCC HAC)).
              assert (Hrec1' : NEval_left P (x0 :: F) Gam (BExpr (EVar y0)) G1' (BExpr (EVar x')))
                by (rewrite <- Hb1; exact Hrec1).
              assert (Hclx' : ContractLoc G1 y0 x') by exact (IH2 y0 brs0 eq_refl (x0::F) G1' x' Hrec1').
              eapply CL_Fwd; [exact (GEval_fwd_permanent P G0 (BCase y0 brs0) G1 v1 Hrec x0 y0 Hgx0) | exact Hclx'].
           ++ (* FwdAchievedCon: e0 = Con c1 args1 -- contradicts Hne1 *)
              exfalso. exact (Hne1 c1 args1 Hb1).
        -- exfalso.
           destruct (VarChase_first_step Gam x0 (BExpr (ECon cd argsd)) HVCd) as
             [b1 [Hb1 [Heqb1 | [w' [Heqb1 [Hnew'x0 Hrecw0]]]]]].
           ++ exfalso. exact (Hne1 cd argsd (ltac:(congruence))).
           ++ assert (Heqe0w' : e0 = BExpr (EVar w')) by congruence.
              assert (Hrecw' : NEval_left P (x0 :: F) Gam (BExpr (EVar w')) G1' (BExpr (EVar x')))
                by (rewrite <- Heqe0w'; exact Hrec1).
              assert (Heqv := NEval_left_force_matches_VarChase Gam w' (BExpr (ECon cd argsd)) Hrecw0
                                 cd argsd eq_refl P (x0::F) G1' (BExpr (EVar x')) Hrecw').
              discriminate Heqv.
  - (* G_CaseFun *)
    split.
    + intros c args Hcorr.
      assert (Hgamx0 : Gam x0 = Some (BExpr (EFun f0 args0))).
      { assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
        destruct HGamx0 as [b [Hb HCE3]].
        destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgxfwd _]]]]]].
        - destruct (CorrE_forced_shape G0 x0 b HCE) as
            [ [c0 [args0' [Hg1 Hb1]]]
            | [ [Hg1 Hb1]
              | [ [f1 [args1 [Hg1 Hb1]]]
                | [ [y1 [y2 [Hg1 Hb1]]]
                  | [ [z1 [Hg1 Hb1]]
                    | [ [Hg1 Hb1]
                      | [ [y1 [Hg1 Hb1]]
                        | [y1 [z1 [c0 [args0' [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
            rewrite Hgx0 in Hg1; try discriminate Hg1.
          injection Hg1 as Hg1a Hg1b. subst f1 args1. rewrite Hb1 in Hb. exact Hb.
        - rewrite Hgx0 in Hgxfwd. discriminate Hgxfwd. }
      assert (Hxdom : G0 x0 <> None) by congruence.
      destruct (NEval_left_let_chain_to_value P HPWF G0 (BExpr (EFun f0 args0)) G1 vx Hrec1
                  Gam HGam HNVT I HWF HCC HAC x0 Hxdom)
        as [Hxeq [HNVT1 [HWF1 [Gam1 [HHC1 [HCC1 [HAC1 [Hgx1 Hplug]]]]]]]].
      assert (Hg1x0 : G1 x0 = Some (GExpr (EFun f0 args0))) by (rewrite Hxeq; exact Hgx0).
      destruct vx as [e0 | y0'].
      * (* vx = GExpr e0 *)
        destruct e0 as [ w | | | y1 z1 | f1 args1 | c1 args1 ].
        -- (* EVar: impossible, no GEval rule ever concludes GExpr(EVar _) *)
           exfalso. destruct (GEval_never_var_or_fun P G0 (BExpr (EFun f0 args0)) G1 (GExpr (EVar w)) Hrec1) as [Hnv _].
           exact (Hnv w eq_refl).
        -- (* EBot: Hrec2's own scrutinee is EBot, forcing v1 = EBot, contradicting Con *)
           exfalso.
           assert (Hxb : (hupd G1 x0 (GExpr EBot)) x0 = Some (GExpr EBot))
             by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
           assert (Hvb : v1 = GExpr EBot) by (eapply GEval_casebot_forces_bot; [exact Hrec2 | exact Hxb]).
           subst v1. inversion Hcorr.
        -- (* EFree: impossible for a program satisfying NoBareFreeOrChoiceProgWF --
              a bare, un-let-bound `free` can never be a function body's own tail. *)
           exfalso.
           destruct (GEval_result_not_free_or_choice P HNBFC G0 (BExpr (EFun f0 args0)) G1
                       (GExpr EFree) Hrec1 I) as [Hne _].
           exact (Hne eq_refl).
        -- (* EChoice: ditto -- a bare, un-cased choice can never be a function
              body's own tail either. *)
           exfalso.
           destruct (GEval_result_not_free_or_choice P HNBFC G0 (BExpr (EFun f0 args0)) G1
                       (GExpr (EChoice y1 z1)) Hrec1 I) as [_ Hne].
           exact (Hne y1 z1 eq_refl).
        -- (* EFun: impossible, G_Fun always further evaluates its own body *)
           exfalso. destruct (GEval_never_var_or_fun P G0 (BExpr (EFun f0 args0)) G1 (GExpr (EFun f1 args1)) Hrec1) as [_ Hnf].
           exact (Hnf f1 args1 eq_refl).
        -- (* ECon c1 args1: direct, via HeapCorr_update_from_fun + IH2 *)
           assert (Hgam1x0 : Gam1 x0 = Some (BExpr (EFun f0 args0))) by (rewrite Hgx1; exact Hgamx0).
           assert (HHCd : HeapCorr (hupd G1 x0 (GExpr (ECon c1 args1))) (hupd Gam1 x0 (BExpr (ECon c1 args1))))
             by exact (HeapCorr_update_from_fun G1 Gam1 x0 f0 args0 (GExpr (ECon c1 args1)) HHC1 Hg1x0).
           assert (HNVTd : NoVarThunk (hupd G1 x0 (GExpr (ECon c1 args1)))).
           { intros w z Heq. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
             - subst w. unfold hupd in Heq; rewrite Nat.eqb_refl in Heq. discriminate Heq.
             - rewrite (hupd_neq G1 x0 (GExpr (ECon c1 args1)) w Hnewx0) in Heq. exact (HNVT1 w z Heq). }
           assert (HWFd : WellFoundedFwd (hupd G1 x0 (GExpr (ECon c1 args1)))).
           { eapply WellFoundedFwd_update_from_fun; [exact HWF1 | exact Hg1x0 | ].
             intros y Hcontra; discriminate Hcontra. }
           assert (HCCd : ChainConsistent (hupd G1 x0 (GExpr (ECon c1 args1))) (hupd Gam1 x0 (BExpr (ECon c1 args1))))
             by exact (ChainConsistent_update_from_fun G1 Gam1 x0 f0 args0 (GExpr (ECon c1 args1)) HCC1 Hgam1x0).
           assert (HACd : AliasConsistent (hupd G1 x0 (GExpr (ECon c1 args1))) (hupd Gam1 x0 (BExpr (ECon c1 args1))))
             by exact (AliasConsistent_update_from_fun G1 Gam1 x0 f0 args0 (GExpr (ECon c1 args1)) HAC1 Hgam1x0).
           destruct (IH2 (hupd Gam1 x0 (BExpr (ECon c1 args1))) HHCd HNVTd HNAL HWFd HCCd HACd) as [IH2a _].
           destruct (IH2a c args Hcorr) as [Gam2 [HNE2 HHC2]].
           assert (HforceX0 : NEval_left P nil Gam (BExpr (EVar x0)) (hupd Gam1 x0 (BExpr (ECon c1 args1))) (BExpr (ECon c1 args1))).
           { eapply NL_VarExp.
             - intro Hin; destruct Hin.
             - exact Hgamx0.
             - intros cc argscc Hcontra; discriminate Hcontra.
             - intro Hcontra; discriminate Hcontra.
             - intro Hcontra; discriminate Hcontra.
             - exact (Hplug (x0 :: nil) Gam1 (BExpr (ECon c1 args1)) (NL_ValCon P (x0 :: nil) Gam1 c1 args1)). }
           assert (Hxeqc1 : (hupd Gam1 x0 (BExpr (ECon c1 args1))) x0 = Some (BExpr (ECon c1 args1)))
             by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
           destruct (NEval_left_bcase_shape P nil (hupd Gam1 x0 (BExpr (ECon c1 args1))) x0 brs0 Gam2
                       (BExpr (ECon c args)) HNE2) as
             [ [c' [zs [ys [body [Gmid [Hforce0 [HIn [Hlen Hbody0]]]]]]]]
             | [x' [Gmid [c1' [ys1 [body1 [ws [Hforce0 [Hhd [Hlenws [HNDws [Hfrws Hbodyguess]]]]]]]]]]] ].
           ++ destruct (NEval_left_evar_shape P nil (hupd Gam1 x0 (BExpr (ECon c1 args1))) x0 Gmid
                          (BExpr (ECon c' zs)) Hforce0) as
                [ [Hcase1 [HeqGmid _]]
                | [ [Hcase2 [_ Heqv]]
                  | [ [Hcase3 [_ Heqv]]
                    | [_ [e1 [G1x [Hz1 [Hne1 [_ [_ [_ HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
              ** rewrite Hxeqc1 in Hcase1. injection Hcase1 as Heqc' Heqzs. subst c' zs Gmid.
                 exists Gam2. split; [ | exact HHC2].
                 eapply NL_Select; [exact HforceX0 | exact HIn | exact Hlen | exact Hbody0].
              ** exfalso. rewrite Hxeqc1 in Hz1. injection Hz1 as Hz1. exact (Hne1 c1 args1 (eq_sym Hz1)).
           ++ exfalso.
              destruct (NEval_left_evar_shape P nil (hupd Gam1 x0 (BExpr (ECon c1 args1))) x0 Gmid
                          (BExpr (EVar x')) Hforce0) as
                [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1x [Hz1 [Hne1 _]]]]]]]].
              ** rewrite Hxeqc1 in Hcase1; discriminate Hcase1.
              ** rewrite Hxeqc1 in Hcase2; discriminate Hcase2.
              ** rewrite Hxeqc1 in Hcase3; discriminate Hcase3.
              ** rewrite Hxeqc1 in Hz1. injection Hz1 as Hz1. exact (Hne1 c1 args1 (eq_sym Hz1)).
      * (* vx = GFwd y0' : mirrors theorem2's own G_CaseChoice/NL_Select pattern,
           with Hplug's "replay from Gam1" standing in for NL_Or's own bias *)
        assert (Hx0y0' : x0 <> y0').
        { intro Heqxy; subst y0'.
          destruct (GEval_case_gives_ContractLoc P (hupd G1 x0 (GFwd x0)) x0 brs0 G2 v1 Hrec2) as [w Hcl].
          assert (Hself : (hupd G1 x0 (GFwd x0)) x0 = Some (GFwd x0))
            by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
          exact (ContractLoc_no_selfFwd (hupd G1 x0 (GFwd x0)) x0 w Hcl Hself). }
        assert (Hgam1x0 : Gam1 x0 = Some (BExpr (EFun f0 args0))) by (rewrite Hgx1; exact Hgamx0).
        assert (HHCd : HeapCorr (hupd G1 x0 (GFwd y0')) (hupd Gam1 x0 (BExpr (EVar y0'))))
          by exact (HeapCorr_update_from_fun G1 Gam1 x0 f0 args0 (GFwd y0') HHC1 Hg1x0).
        assert (HNVTd : NoVarThunk (hupd G1 x0 (GFwd y0'))).
        { intros w z Heq. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
          - subst w. unfold hupd in Heq; rewrite Nat.eqb_refl in Heq. discriminate Heq.
          - rewrite (hupd_neq G1 x0 (GFwd y0') w Hnewx0) in Heq. exact (HNVT1 w z Heq). }
        assert (HWFd : WellFoundedFwd (hupd G1 x0 (GFwd y0'))).
        { eapply WellFoundedFwd_update_from_fun; [exact HWF1 | exact Hg1x0 | ].
          intros y Heqy; injection Heqy as Heqy; subst y.
          assert (Hgfwd : (hupd G1 x0 (GFwd y0')) x0 = Some (GFwd y0'))
            by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
          inversion Hrec2; subst;
            try (match goal with
                 | Hx : hupd G1 x0 (GFwd y0') x0 = Some (GExpr _) |- _ =>
                     rewrite Hgfwd in Hx; discriminate Hx
                 end).
          rewrite Hgfwd in H2. injection H2 as H2. subst y.
          destruct (GEval_case_gives_ContractLoc P (hupd G1 x0 (GFwd y0')) y0' brs0 G2 v1 H5) as [ytgt Hclyt].
          exists ytgt. exact Hclyt. }
        assert (HCCd : ChainConsistent (hupd G1 x0 (GFwd y0')) (hupd Gam1 x0 (BExpr (EVar y0'))))
          by exact (ChainConsistent_update_from_fun G1 Gam1 x0 f0 args0 (GFwd y0') HCC1 Hgam1x0).
        assert (HACd : AliasConsistent (hupd G1 x0 (GFwd y0')) (hupd Gam1 x0 (BExpr (EVar y0'))))
          by exact (AliasConsistent_update_from_fun G1 Gam1 x0 f0 args0 (GFwd y0') HAC1 Hgam1x0).
        destruct (IH2 (hupd Gam1 x0 (BExpr (EVar y0'))) HHCd HNVTd HNAL HWFd HCCd HACd) as [IH2a _].
        destruct (IH2a c args Hcorr) as [Gam2 [HNE2 HHC2]].
        assert (Hgamx0eq : hupd Gam1 x0 (BExpr (EVar y0')) x0 = Some (BExpr (EVar y0')))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        destruct (NEval_left_bcase_shape P nil (hupd Gam1 x0 (BExpr (EVar y0'))) x0 brs0 Gam2
                    (BExpr (ECon c args)) HNE2) as
          [ [c' [zs [ys [body [Gmid [Hforce0 [HIn [Hlen Hbody0]]]]]]]]
          | [x' [Gmid [c1' [ys1 [body1 [ws [Hforce0 [Hhd [Hlenws [HNDws [Hfrws Hbodyguess]]]]]]]]]]] ].
        -- (* NL_Select shape: x0's OWN scrutinee-forcing (Hforce0) is NOT yet
              guarded, but x0's slot is EVar y0' (non-terminal), so it must be
              NL_VarExp -- inverting it directly hands back the guarded
              (x0::nil) recursive premise, which frame_guarded can use as-is
              (no separate widening step needed, unlike G_CaseChoice's own
              NL_Select branch, where the analogous fact came pre-guarded at
              nil and had to be widened instead of extracted). *)
           destruct (NEval_left_evar_shape P nil (hupd Gam1 x0 (BExpr (EVar y0'))) x0 Gmid
                       (BExpr (ECon c' zs)) Hforce0) as
             [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1x [Hz1 [Hne1 [Hne2 [Hne3 [Hrec2inner HeqGmid]]]]]]]]]]].
           ++ rewrite Hgamx0eq in Hcase1; discriminate Hcase1.
           ++ exfalso. rewrite Hgamx0eq in Hcase2. injection Hcase2 as Hcase2. exact (Hx0y0' (eq_sym Hcase2)).
           ++ rewrite Hgamx0eq in Hcase3; discriminate Hcase3.
           ++ rewrite Hgamx0eq in Hz1. injection Hz1 as Hz1. subst e1.
              assert (Hex1 : forall cc argscc, BExpr (EVar y0') <> BExpr (ECon cc argscc))
                by (intros cc argscc Hcontra; discriminate Hcontra).
              assert (Hex2 : BExpr (EVar y0') <> BExpr (EVar x0))
                by (intro Hcontra; injection Hcontra as Hcontra; exact (Hx0y0' (eq_sym Hcontra))).
              assert (Hex3 : BExpr (EVar y0') <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
              assert (Hey1 : forall cc argscc, BExpr (EFun f0 args0) <> BExpr (ECon cc argscc))
                by (intros cc argscc Hcontra; discriminate Hcontra).
              assert (Hey2 : BExpr (EFun f0 args0) <> BExpr (EVar x0)) by (intro Hcontra; discriminate Hcontra).
              assert (Hey3 : BExpr (EFun f0 args0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
              assert (HxF0 : In x0 (x0 :: nil)) by (left; reflexivity).
              destruct (NEval_left_frame_guarded x0 (BExpr (EVar y0')) Hex1 Hex2 Hex3
                          (BExpr (EFun f0 args0)) Hey1 Hey2 Hey3
                          P (x0 :: nil) (hupd Gam1 x0 (BExpr (EVar y0'))) (BExpr (EVar y0')) G1x
                          (BExpr (ECon c' zs)) Hrec2inner
                          HxF0 Hgamx0eq
                          Gam1 (fun w Hw => eq_sym (hupd_neq Gam1 x0 (BExpr (EVar y0')) w Hw)) Hgam1x0)
                as [Gam2' [Hforce0' Heqptw]].
              assert (HforceX0 : NEval_left P nil Gam (BExpr (EVar x0)) (hupd Gam2' x0 (BExpr (ECon c' zs)))
                                    (BExpr (ECon c' zs))).
              { eapply NL_VarExp.
                - intro Hin; destruct Hin.
                - exact Hgamx0.
                - intros cc argscc Hcontra; discriminate Hcontra.
                - intro Hcontra; discriminate Hcontra.
                - intro Hcontra; discriminate Hcontra.
                - exact (Hplug (x0 :: nil) Gam2' (BExpr (ECon c' zs)) Hforce0'). }
              (* Gmid ALREADY has x0 memoized to Con c' zs directly (Hforce0's own
                 scrutinee WAS x0 itself, unlike G_CaseChoice's analogous branch,
                 where the scrutinee was y0 and x0 remained a lazy alias needing a
                 separate shortcut_alias promotion) -- so no alias reconciliation
                 is needed at all here, just a plain pointwise-heap replay. *)
              assert (Heqheap : forall w, hupd Gam2' x0 (BExpr (ECon c' zs)) w = Gmid w).
              { intro w. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
                - subst w. unfold hupd; rewrite Nat.eqb_refl.
                  rewrite HeqGmid. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
                - rewrite (hupd_neq Gam2' x0 (BExpr (ECon c' zs)) w Hnewx0).
                  rewrite HeqGmid. rewrite (hupd_neq G1x x0 (BExpr (ECon c' zs)) w Hnewx0).
                  exact (Heqptw w Hnewx0). }
           destruct (NEval_left_pointwise_heap P nil Gmid
                       (rename_b (zipsubst ys zs) body) Gam2 (BExpr (ECon c args)) Hbody0
                       (hupd Gam2' x0 (BExpr (ECon c' zs))) Heqheap)
             as [Gam2''' [Hbodyfinal Heqfinal2]].
              exists Gam2'''. split.
              +++ eapply NL_Select; [exact HforceX0 | exact HIn | exact Hlen | exact Hbodyfinal].
              +++ eapply HeapCorr_pointwise; [exact HHC2 | exact Heqfinal2].
        -- (* NL_Guess shape: mirrors the NL_Select branch above EXACTLY (same
              inversion, same frame_guarded call, same Hplug bridge), just
              targeting a self-loop EVar x' instead of Con c' zs -- the full
              STEP1-4/two-location-VarChase machinery from
              HeapCorr_fwd_transfer_fwdhere_free's own x' <> y case is NOT
              needed here: that case had to reconcile TWO INDEPENDENTLY-
              chosen fresh guesses (one from forcing x directly, one from
              forcing y and continuing separately); here there is only ONE
              guess in play (Hbodyguess itself, already shared between the
              x0-scrutinee derivation and what Hplug needs), so a plain
              pointwise-heap replay suffices, same as the NL_Select branch. *)
           destruct (NEval_left_evar_shape P nil (hupd Gam1 x0 (BExpr (EVar y0'))) x0 Gmid
                       (BExpr (EVar x')) Hforce0) as
             [ [Hcase1 [_ [c'' [args'' Heqv]]]]
             | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1x [Hz1 [Hne1 [Hne2 [Hne3 [Hrec2inner HeqGmid]]]]]]]]]]].
           ++ discriminate Heqv.
           ++ exfalso. rewrite Hgamx0eq in Hcase2. injection Hcase2 as Hcase2. exact (Hx0y0' (eq_sym Hcase2)).
           ++ rewrite Hgamx0eq in Hcase3; discriminate Hcase3.
           ++ rewrite Hgamx0eq in Hz1. injection Hz1 as Hz1. subst e1.
              assert (Hex1 : forall cc argscc, BExpr (EVar y0') <> BExpr (ECon cc argscc))
                by (intros cc argscc Hcontra; discriminate Hcontra).
              assert (Hex2 : BExpr (EVar y0') <> BExpr (EVar x0))
                by (intro Hcontra; injection Hcontra as Hcontra; exact (Hx0y0' (eq_sym Hcontra))).
              assert (Hex3 : BExpr (EVar y0') <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
              assert (Hey1 : forall cc argscc, BExpr (EFun f0 args0) <> BExpr (ECon cc argscc))
                by (intros cc argscc Hcontra; discriminate Hcontra).
              assert (Hey2 : BExpr (EFun f0 args0) <> BExpr (EVar x0)) by (intro Hcontra; discriminate Hcontra).
              assert (Hey3 : BExpr (EFun f0 args0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
              assert (HxF0 : In x0 (x0 :: nil)) by (left; reflexivity).
              destruct (NEval_left_frame_guarded x0 (BExpr (EVar y0')) Hex1 Hex2 Hex3
                          (BExpr (EFun f0 args0)) Hey1 Hey2 Hey3
                          P (x0 :: nil) (hupd Gam1 x0 (BExpr (EVar y0'))) (BExpr (EVar y0')) G1x
                          (BExpr (EVar x')) Hrec2inner
                          HxF0 Hgamx0eq
                          Gam1 (fun w Hw => eq_sym (hupd_neq Gam1 x0 (BExpr (EVar y0')) w Hw)) Hgam1x0)
                as [Gam2' [Hforce0' Heqptw]].
              assert (HforceX0 : NEval_left P nil Gam (BExpr (EVar x0)) (hupd Gam2' x0 (BExpr (EVar x')))
                                    (BExpr (EVar x'))).
              { eapply NL_VarExp.
                - intro Hin; destruct Hin.
                - exact Hgamx0.
                - intros cc argscc Hcontra; discriminate Hcontra.
                - intro Hcontra; discriminate Hcontra.
                - intro Hcontra; discriminate Hcontra.
                - exact (Hplug (x0 :: nil) Gam2' (BExpr (EVar x')) Hforce0'). }
              assert (Heqheap : forall w, hupd Gam2' x0 (BExpr (EVar x')) w = Gmid w).
              { intro w. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
                - subst w. unfold hupd; rewrite Nat.eqb_refl.
                  rewrite HeqGmid. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
                - rewrite (hupd_neq Gam2' x0 (BExpr (EVar x')) w Hnewx0).
                  rewrite HeqGmid. rewrite (hupd_neq G1x x0 (BExpr (EVar x')) w Hnewx0).
                  exact (Heqptw w Hnewx0). }
              assert (Heqheap2 : forall w,
                  hupd_list (hupd (hupd Gam2' x0 (BExpr (EVar x'))) x' (BExpr (ECon c1' ws))) ws
                    (map (fun w0 => BExpr (EVar w0)) ws) w
                = hupd_list (hupd Gmid x' (BExpr (ECon c1' ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w).
              { apply hupd_list_pointwise. intro w. unfold hupd.
                destruct (Nat.eqb w x') eqn:E; [reflexivity | apply Heqheap]. }
              destruct (NEval_left_pointwise_heap P nil
                          (hupd_list (hupd Gmid x' (BExpr (ECon c1' ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                          (rename_b (zipsubst ys1 ws) body1) Gam2 (BExpr (ECon c args)) Hbodyguess
                          (hupd_list (hupd (hupd Gam2' x0 (BExpr (EVar x'))) x' (BExpr (ECon c1' ws))) ws
                             (map (fun w0 => BExpr (EVar w0)) ws))
                          Heqheap2)
                as [Gam2''' [Hbodyfinal Heqfinal2]].
              exists Gam2'''. split.
              +++ eapply NL_Guess; [exact HforceX0 | exact Hhd | exact Hlenws | exact HNDws | | exact Hbodyfinal].
                  intros w Hw. rewrite (Heqheap w). exact (Hfrws w Hw).
              +++ eapply HeapCorr_pointwise; [exact HHC2 | exact Heqfinal2].
    + (* Second conjunct (ContractLoc-matching): e IS BCase x0 brs0 here (theorem2's
         own "e" for the WHOLE G_CaseFun rule, not Hrec1's inner EFun), so this is
         NOT vacuous -- would need the analogous "force x0 reaches x0'" ->
         "ContractLoc G2 x0 x0'" argument G_CaseChoice's own second conjunct
         builds, threaded through the same Con/Fwd split as the first conjunct
         above; not yet attempted. *)
      admit.
  - (* G_CaseChoice *)
    assert (Hx0y0 : x0 <> y0).
    { intro Heqxy; subst y0.
      destruct (GEval_case_gives_ContractLoc P (hupd G0 x0 (GFwd x0)) x0 brs0 G1 v1 Hrec) as [w Hcl].
      assert (Hself : (hupd G0 x0 (GFwd x0)) x0 = Some (GFwd x0))
        by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
      exact (ContractLoc_no_selfFwd (hupd G0 x0 (GFwd x0)) x0 w Hcl Hself). }
    assert (Hgamx0 : Gam x0 = Some (BExpr (EChoice y0 z0))).
    { assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
      destruct HGamx0 as [b [Hb HCE3]].
      destruct HCE3 as [HCE | [y1 [z1 [c1 [args1 [Hgxfwd _]]]]]].
      - destruct (CorrE_forced_shape G0 x0 b HCE) as
          [ [c0 [args0 [Hg1 Hb1]]]
          | [ [Hg1 Hb1]
            | [ [f1 [args1 [Hg1 Hb1]]]
              | [ [y1' [y2' [Hg1 Hb1]]]
                | [ [z1' [Hg1 Hb1]]
                  | [ [Hg1 Hb1]
                    | [ [y1 [Hg1 Hb1]]
                      | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
          rewrite Hgx0 in Hg1; try discriminate Hg1.
        injection Hg1 as Hg1a Hg1b. subst y1' y2'. rewrite Hb1 in Hb. exact Hb.
      - rewrite Hgx0 in Hgxfwd. discriminate Hgxfwd. }
    destruct (GEval_case_gives_ContractLoc P (hupd G0 x0 (GFwd y0)) y0 brs0 G1 v1 Hrec) as [ytgt Hclyt].
    assert (HWF' : WellFoundedFwd (hupd G0 x0 (GFwd y0)))
      by exact (WellFoundedFwd_update_choice_to_fwd G0 x0 y0 z0 HWF Hgx0 (ex_intro _ ytgt Hclyt)).
    assert (HGam' : HeapCorr (hupd G0 x0 (GFwd y0)) (hupd Gam x0 (BExpr (EVar y0))))
      by exact (HeapCorr_update_choice_to_fwd G0 Gam x0 y0 z0 HGam Hgx0).
    assert (HNVT' : NoVarThunk (hupd G0 x0 (GFwd y0))).
    { intros w z Heq. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
      - subst w. unfold hupd in Heq; rewrite Nat.eqb_refl in Heq. discriminate Heq.
      - rewrite (hupd_neq G0 x0 (GFwd y0) w Hnewx0) in Heq. exact (HNVT w z Heq). }
    assert (HCC' : ChainConsistent (hupd G0 x0 (GFwd y0)) (hupd Gam x0 (BExpr (EVar y0))))
      by exact (ChainConsistent_update_to_fwd_lazy G0 Gam x0 y0 (BExpr (EChoice y0 z0)) HCC Hgamx0
                  (ltac:(intros cc argscc Heq; discriminate Heq))).
    assert (HAC' : AliasConsistent (hupd G0 x0 (GFwd y0)) (hupd Gam x0 (BExpr (EVar y0))))
      by exact (AliasConsistent_update_to_fwd_lazy G0 Gam x0 y0 (BExpr (EChoice y0 z0)) HAC Hgamx0
                  (ltac:(intros ww Heq; discriminate Heq))).
    destruct (IH (hupd Gam x0 (BExpr (EVar y0))) HGam' HNVT' HNAL HWF' HCC' HAC') as [IH1 IH2].
    split.
    + intros c args Hcorr.
      destruct (IH1 c args Hcorr) as [Gam1 [HNE HHC]].
      destruct (NEval_left_bcase_shape P nil (hupd Gam x0 (BExpr (EVar y0))) y0 brs0 Gam1 (BExpr (ECon c args)) HNE) as
        [ [c' [zs [ys [body [Gmid [Hforcey0 [HIn [Hlen Hbody]]]]]]]]
        | [x' [Gmid [c1' [ys1 [body1 [ws [Hforcey0 [Hhd [Hlenws [HNDws [Hfrws Hbodyguess]]]]]]]]]]] ].
      * (* NL_Select shape *)
        assert (Hex1 : forall cc argscc, BExpr (EVar y0) <> BExpr (ECon cc argscc))
          by (intros cc argscc Hcontra; discriminate Hcontra).
        assert (Hex2 : BExpr (EVar y0) <> BExpr (EVar x0))
          by (intro Hcontra; injection Hcontra as Hcontra; exact (Hx0y0 (eq_sym Hcontra))).
        assert (Hex3 : BExpr (EVar y0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
        assert (Hey1 : forall cc argscc, BExpr (EChoice y0 z0) <> BExpr (ECon cc argscc))
          by (intros cc argscc Hcontra; discriminate Hcontra).
        assert (Hey2 : BExpr (EChoice y0 z0) <> BExpr (EVar x0)) by (intro Hcontra; discriminate Hcontra).
        assert (Hey3 : BExpr (EChoice y0 z0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
        assert (HxF0 : In x0 (x0::nil)) by (left; reflexivity).
        assert (Hgamx0eq : hupd Gam x0 (BExpr (EVar y0)) x0 = Some (BExpr (EVar y0)))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        assert (Hforcey0_x0 : NEval_left P (x0::nil) (hupd Gam x0 (BExpr (EVar y0)))
                                 (BExpr (EVar y0)) Gmid (BExpr (ECon c' zs)))
          by exact (NEval_left_alias_weaken_force_y P x0 y0 Hx0y0 (hupd Gam x0 (BExpr (EVar y0)))
                      Gmid (BExpr (ECon c' zs)) Hforcey0 Hgamx0eq).
        destruct (NEval_left_frame_guarded x0 (BExpr (EVar y0)) Hex1 Hex2 Hex3
                    (BExpr (EChoice y0 z0)) Hey1 Hey2 Hey3
                    P (x0::nil) (hupd Gam x0 (BExpr (EVar y0))) (BExpr (EVar y0)) Gmid (BExpr (ECon c' zs)) Hforcey0_x0
                    HxF0 Hgamx0eq
                    Gam (fun w Hw => eq_sym (hupd_neq Gam x0 (BExpr (EVar y0)) w Hw)) Hgamx0)
          as [Gam2' [Hforcey0' Heqptw]].
        assert (HforceX0 : NEval_left P nil Gam (BExpr (EVar x0)) (hupd Gam2' x0 (BExpr (ECon c' zs))) (BExpr (ECon c' zs))).
        { eapply NL_VarExp.
          - intro Hin; destruct Hin.
          - exact Hgamx0.
          - intros cc argscc Hcontra; discriminate Hcontra.
          - intro Hcontra; discriminate Hcontra.
          - intro Hcontra; discriminate Hcontra.
          - apply NL_Or. exact Hforcey0'. }
        assert (Hgmidx0 : Gmid x0 = Some (BExpr (EVar y0)))
          by exact (NEval_left_alias_persists_through_force P x0 y0 Hx0y0
                      (hupd Gam x0 (BExpr (EVar y0))) Gmid (BExpr (ECon c' zs)) Hforcey0 Hgamx0eq).
        assert (Hgmidy0 : Gmid y0 = Some (BExpr (ECon c' zs)))
          by exact (NEval_left_own_slot P nil (hupd Gam x0 (BExpr (EVar y0))) y0 Gmid (BExpr (ECon c' zs)) Hforcey0).
        destruct (NEval_left_shortcut_alias P x0 y0 c' zs Hx0y0 nil Gmid
                    (rename_b (zipsubst ys zs) body) Gam1 (BExpr (ECon c args)) Hbody
                    (or_introl Hgmidx0) Hgmidy0)
          as [Gam1' [Hbody' Heqfinal]].
        assert (Heqheap : forall w, hupd Gam2' x0 (BExpr (ECon c' zs)) w = hupd Gmid x0 (BExpr (ECon c' zs)) w).
        { intro w. destruct (Nat.eq_dec w x0) as [Heqwx0 | Hnewx0].
          - subst w. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
          - rewrite (hupd_neq Gam2' x0 (BExpr (ECon c' zs)) w Hnewx0).
            rewrite (hupd_neq Gmid x0 (BExpr (ECon c' zs)) w Hnewx0).
            exact (Heqptw w Hnewx0). }
        destruct (NEval_left_pointwise_heap P nil (hupd Gmid x0 (BExpr (ECon c' zs)))
                    (rename_b (zipsubst ys zs) body) Gam1' (BExpr (ECon c args)) Hbody'
                    (hupd Gam2' x0 (BExpr (ECon c' zs))) Heqheap)
          as [Gam1'' [Hbodyfinal Heqfinal2]].
        exists Gam1''. split.
        -- eapply NL_Select; [exact HforceX0 | exact HIn | exact Hlen | exact Hbodyfinal].
        -- assert (Hgam1_persist := NEval_left_alias_or_con_persists P x0 y0 c' zs Hx0y0 nil Gmid
                                       (rename_b (zipsubst ys zs) body) Gam1 (BExpr (ECon c args)) Hbody
                                       (or_introl Hgmidx0) Hgmidy0).
           destruct Hgam1_persist as [Hgam1x0_disj Hgam1y0].
           assert (Hchase_x0 : VarChase Gam1 x0 (BExpr (ECon c' zs))).
           { destruct Hgam1x0_disj as [Heq1 | Heq1].
             - eapply VChase_Hop; [exact Heq1 | exact (not_eq_sym Hx0y0) | ].
               apply VChase_Here; [exact Hgam1y0 | intros ww Hcontra; discriminate Hcontra].
             - apply VChase_Here; [exact Heq1 | intros ww Hcontra; discriminate Hcontra]. }
           assert (Hg1x0fwd : G1 x0 = Some (GFwd y0)).
           { eapply GEval_fwd_permanent; [exact Hrec | ].
             unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
           destruct (HeapCorr_con_to_contractloc G1 Gam1 y0 c' zs HHC Hgam1y0) as [ytgt' [Hcl' Hz']].
           assert (HHCupdated : HeapCorr G1 (hupd Gam1 x0 (BExpr (ECon c' zs))))
             by exact (HeapCorr_update_achieved G1 Gam1 x0 y0 ytgt' c' zs HHC Hg1x0fwd Hcl' Hz' Hchase_x0).
           eapply HeapCorr_pointwise; [exact HHCupdated | ].
           intro w. rewrite (Heqfinal2 w). exact (Heqfinal w).
      * (* NL_Guess shape: closed via NEval_left_choice_as_alias_bcase, since
           x0's OWN Nat-heap slot is EChoice y0 z0, not a literal alias -- call
           HeapCorr_fwd_transfer_fwdhere_free (unmodified) against the
           ALIAS-shaped heap the IH already hands us (hupd Gam x0 (EVar y0)),
           then transport its result back across the EChoice/EVar swap at x0. *)
        assert (Hg0x0fwd : (hupd G0 x0 (GFwd y0)) x0 = Some (GFwd y0))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        assert (Hgamx0eq : hupd Gam x0 (BExpr (EVar y0)) x0 = Some (BExpr (EVar y0)))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        destruct (HeapCorr_fwd_transfer_fwdhere_free P (hupd G0 x0 (GFwd y0)) (hupd Gam x0 (BExpr (EVar y0)))
                    HGam' x0 y0 Hg0x0fwd Hx0y0 Hgamx0eq
                    brs0 x' c1' ys1 body1 ws Gmid Gam1 (BExpr (ECon c args))
                    Hforcey0 Hhd Hlenws HNDws Hfrws Hbodyguess)
          as [Gam'' [HNE'' HTransfer]].
        destruct (NEval_left_choice_as_alias_bcase P x0 y0 z0 Hx0y0 brs0
                    (hupd Gam x0 (BExpr (EVar y0))) Gam'' (BExpr (ECon c args)) HNE'' Hgamx0eq
                    Gam (fun w Hw => eq_sym (hupd_neq Gam x0 (BExpr (EVar y0)) w Hw)) Hgamx0)
          as [Gam''' [HNE''' Heqfull]].
        exists Gam'''. split.
        -- exact HNE'''.
        -- assert (Hg1x0fwd : G1 x0 = Some (GFwd y0)).
           { eapply GEval_fwd_permanent; [exact Hrec | ].
             unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
           assert (Hclx' : x' <> y0 -> ContractLoc G1 y0 x')
             by (intros _; exact (IH2 y0 brs0 eq_refl nil Gmid x' Hforcey0)).
           eapply HeapCorr_pointwise.
           ++ exact (HTransfer G1 Hg1x0fwd Hclx' HHC).
           ++ exact Heqfull.
    + intros x brs Heqxbrs. injection Heqxbrs as Heqx Heqbrs. subst x brs.
      intros F Gmid x' Hforce.
      destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hforce) as
        [ [Hcase1 _] | [ [Hcase2 _] | [ [Hcase3 _] | [_ [e1 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec2 _]]]]]]]]]]].
      * rewrite Hgamx0 in Hcase1; discriminate Hcase1.
      * rewrite Hgamx0 in Hcase2; discriminate Hcase2.
      * rewrite Hgamx0 in Hcase3; discriminate Hcase3.
      * rewrite Hgamx0 in Hz. injection Hz as Hz. subst e1.
        assert (Hrec3 := NEval_left_echoice_shape P (x0::F) Gam y0 z0 G1' (BExpr (EVar x')) Hrec2).
        assert (Hex1 : forall cc argscc, BExpr (EChoice y0 z0) <> BExpr (ECon cc argscc))
          by (intros cc argscc Hcontra; discriminate Hcontra).
        assert (Hex2 : BExpr (EChoice y0 z0) <> BExpr (EVar x0)) by (intro Hcontra; discriminate Hcontra).
        assert (Hex3 : BExpr (EChoice y0 z0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
        assert (Hex2_1 : forall cc argscc, BExpr (EVar y0) <> BExpr (ECon cc argscc))
          by (intros cc argscc Hcontra; discriminate Hcontra).
        assert (Hex2_2 : BExpr (EVar y0) <> BExpr (EVar x0))
          by (intro Hcontra; injection Hcontra as Hcontra; exact (Hx0y0 (eq_sym Hcontra))).
        assert (Hex2_3 : BExpr (EVar y0) <> BExpr EFree) by (intro Hcontra; discriminate Hcontra).
        assert (HxF : In x0 (x0::F)) by (left; reflexivity).
        assert (Hgamx0eq : hupd Gam x0 (BExpr (EVar y0)) x0 = Some (BExpr (EVar y0)))
          by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
        destruct (NEval_left_frame_guarded x0 (BExpr (EChoice y0 z0)) Hex1 Hex2 Hex3
                    (BExpr (EVar y0)) Hex2_1 Hex2_2 Hex2_3
                    P (x0::F) Gam (BExpr (EVar y0)) G1' (BExpr (EVar x')) Hrec3 HxF Hgamx0
                    (hupd Gam x0 (BExpr (EVar y0)))
                    (fun w Hw => hupd_neq Gam x0 (BExpr (EVar y0)) w Hw) Hgamx0eq)
          as [Gam2' [Hrec3' _]].
        assert (Hcl : ContractLoc G1 y0 x')
          by exact (IH2 y0 brs0 eq_refl (x0::F) Gam2' x' Hrec3').
        assert (Hxfwd : G1 x0 = Some (GFwd y0)).
        { eapply GEval_fwd_permanent; [exact Hrec | ].
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        eapply CL_Fwd; [exact Hxfwd | exact Hcl].
  - (* G_CaseCon *)
    split.
    + intros c' args' Hcorr.
      assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
      destruct HGamx0 as [b [Hb HCE3]].
      destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
      * destruct (CorrE_forced_shape G0 x0 b HCE) as
          [ [c0 [args0 [Hg1 Hb1]]]
          | [ [Hg1 Hb1]
            | [ [f1 [args1 [Hg1 Hb1]]]
              | [ [y1 [y2 [Hg1 Hb1]]]
                | [ [z1 [Hg1 Hb1]]
                  | [ [Hg1 Hb1]
                    | [ [y1 [Hg1 Hb1]]
                      | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
          rewrite Hgx0 in Hg1; try discriminate Hg1.
        injection Hg1 as Hg1a Hg1b. subst c0 args0. rewrite Hb1 in Hb.
        assert (HNALbody : NoAliasLetB (rename_b (zipsubst ys zs) body))
          by exact (NoAliasLetB_rename (zipsubst ys zs) body (NoAliasLetB_in brs0 c ys body HIn HNAL)).
        destruct (IH Gam HGam HNVT HNALbody HWF HCC HAC) as [IH1 _].
        destruct (IH1 c' args' Hcorr) as [Gam' [HNE HHC]].
        exists Gam'. split.
        -- eapply NL_Select; [apply NL_VarCons; exact Hb | exact HIn | exact Hlen | exact HNE].
        -- exact HHC.
      * exfalso. rewrite Hgx0 in Hgxfwd. discriminate Hgxfwd.
    + intros x brs Heqxbrs. injection Heqxbrs as Heqx Heqbrs. subst x brs.
      intros F Gmid x' Hforce.
      exfalso.
      assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
      destruct HGamx0 as [b [Hb HCE3]].
      destruct HCE3 as [HCE | [yd [zd [cd [argsd [Hgxfwd [Hcld [Hzd HVCd]]]]]]]].
      * destruct (CorrE_forced_shape G0 x0 b HCE) as
          [ [c0 [args0 [Hg1 Hb1]]]
          | [ [Hg1 Hb1]
            | [ [f1 [args1 [Hg1 Hb1]]]
              | [ [y1 [y2 [Hg1 Hb1]]]
                | [ [z1 [Hg1 Hb1]]
                  | [ [Hg1 Hb1]
                    | [ [y1 [Hg1 Hb1]]
                      | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
          rewrite Hgx0 in Hg1; try discriminate Hg1.
        injection Hg1 as Hg1a Hg1b. subst c0 args0. rewrite Hb1 in Hb.
        exact (NEval_left_evar_not_con P F Gam x0 Gmid x' Hforce c zs Hb).
      * exfalso. rewrite Hgx0 in Hgxfwd. discriminate Hgxfwd.
  - (* G_CaseConFree *)
    assert (Hbx : Gam x0 = Some (BExpr (EVar x0))).
    { assert (HGamx0 := HGam x0). rewrite Hgx0 in HGamx0.
      destruct HGamx0 as [b [Hb HCE3]].
      destruct HCE3 as [HCE | [y1 [z1 [c1' [args1 [Hgxfwd _]]]]]].
      - destruct (CorrE_forced_shape G0 x0 b HCE) as
          [ [c0 [args0 [Hg1 Hb1]]]
          | [ [Hg1 Hb1]
            | [ [f1 [args1 [Hg1 Hb1]]]
              | [ [y1 [y2 [Hg1 Hb1]]]
                | [ [z1 [Hg1 Hb1]]
                  | [ [Hg1 Hb1]
                    | [ [y1 [Hg1 Hb1]]
                      | [y1 [z1 [c0 [args0 [Hg1 [Hcl1 [Hz1 Hb1]]]]]]] ] ] ] ] ] ] ];
          rewrite Hgx0 in Hg1; try discriminate Hg1.
        subst b. exact Hb.
      - rewrite Hgx0 in Hgxfwd. discriminate Hgxfwd. }
    assert (Hxnotinws : ~ In x0 ws).
    { intro Hin. specialize (Hfresh x0 Hin). rewrite Hgx0 in Hfresh. discriminate Hfresh. }
    assert (HGam1 : HeapCorr (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws))))
      by exact (HeapCorr_update_free G0 Gam x0 c1 ws HGam Hgx0).
    assert (HNVT1 : NoVarThunk (hupd G0 x0 (GExpr (ECon c1 ws))))
      by exact (NoVarThunk_update_free G0 x0 c1 ws HNVT Hgx0).
    assert (HWF1 : WellFoundedFwd (hupd G0 x0 (GExpr (ECon c1 ws))))
      by exact (WellFoundedFwd_update_free G0 x0 c1 ws HWF Hgx0).
    assert (HCC1 : ChainConsistent (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws))))
      by exact (ChainConsistent_update_free G0 Gam x0 c1 ws HCC Hgx0 Hbx).
    assert (HAC1 : AliasConsistent (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws))))
      by exact (AliasConsistent_update_free G0 Gam x0 c1 ws HAC Hgx0 Hbx).
    assert (Hfresh' : forall w, In w ws -> (hupd G0 x0 (GExpr (ECon c1 ws))) w = None).
    { intros w Hin. rewrite (hupd_neq G0 x0 (GExpr (ECon c1 ws)) w).
      - exact (Hfresh w Hin).
      - intro Heq; subst w; exact (Hxnotinws Hin). }
    assert (HfreshGam : forall w, In w ws -> Gam w = None).
    { intros w Hin. assert (HGamw := HGam w). rewrite (Hfresh w Hin) in HGamw. exact HGamw. }
    assert (HGam2 : HeapCorr (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
                              (hupd_list (hupd Gam x0 (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)))
      by exact (HeapCorr_extend_free_list ws (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws)))
                  HGam1 HND Hfresh').
    assert (HNVT2 : NoVarThunk (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws)))
      by exact (NoVarThunk_extend_free_list ws (hupd G0 x0 (GExpr (ECon c1 ws))) HNVT1 HND Hfresh').
    assert (HWF2 : WellFoundedFwd (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws)))
      by exact (WellFoundedFwd_extend_free_list ws (hupd G0 x0 (GExpr (ECon c1 ws))) HWF1 HND Hfresh').
    assert (HCC2 : ChainConsistent (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
                                    (hupd_list (hupd Gam x0 (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)))
      by exact (ChainConsistent_extend_free_list ws (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws)))
                  HCC1 HWF1 HND Hfresh').
    assert (HAC2 : AliasConsistent (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
                                    (hupd_list (hupd Gam x0 (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws)))
      by exact (AliasConsistent_extend_free_list ws (hupd G0 x0 (GExpr (ECon c1 ws))) (hupd Gam x0 (BExpr (ECon c1 ws)))
                  HAC1 HWF1 HND Hfresh').
    assert (HInhd : In (c1, ys1, body1) brs0).
    { destruct brs0 as [| hd tl]; simpl in Hhd; [discriminate Hhd | ].
      injection Hhd as Hhd. subst hd. left. reflexivity. }
    assert (HNALbody : NoAliasLetB (rename_b (zipsubst ys1 ws) body1))
      by exact (NoAliasLetB_rename (zipsubst ys1 ws) body1 (NoAliasLetB_in brs0 c1 ys1 body1 HInhd HNAL)).
    split.
    + intros c args Hcorr.
      destruct (IH (hupd_list (hupd Gam x0 (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
                   HGam2 HNVT2 HNALbody HWF2 HCC2 HAC2) as [IH1 _].
      destruct (IH1 c args Hcorr) as [Gam1 [HNE HHC]].
      exists Gam1. split.
      * eapply NL_Guess.
        -- apply NL_VarSelf. exact Hbx.
        -- exact Hhd.
        -- exact Hlen.
        -- exact HND.
        -- exact HfreshGam.
        -- exact HNE.
      * exact HHC.
    + intros x brs Heqxbrs. injection Heqxbrs as Heqx Heqbrs. subst x brs.
      intros F Gmid x' Hforce.
      destruct (NEval_left_evar_shape P F Gam x0 Gmid (BExpr (EVar x')) Hforce) as
        [ [Hcase1 [_ [c0 [args0 Heqv1]]]]
        | [ [Hcase2 [_ Heqv2]]
          | [ [Hcase3 [_ Heqv3]]
            | [_ [e0 [G1' [Hz [Hne1 [Hne2 [Hne3 [Hrec1 HeqGmid]]]]]]]]] ] ].
      * discriminate Heqv1.
      * injection Heqv2 as Heqv2. subst x'.
        assert (Hg1x0 : (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws)) x0
                       = Some (GExpr (ECon c1 ws))).
        { rewrite hupd_list_notin; [ | exact Hxnotinws].
          unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
        assert (HG1x0 : G1 x0 = Some (GExpr (ECon c1 ws)))
          by exact (GEval_con_persists P
                      (hupd_list (hupd G0 x0 (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
                      (rename_b (zipsubst ys1 ws) body1) G1 v1 Hrec x0 c1 ws Hg1x0).
        eapply CL_Here. exact HG1x0.
      * exfalso. rewrite Hbx in Hcase3. discriminate Hcase3.
      * exfalso. rewrite Hbx in Hz. injection Hz as Hz. exact (Hne2 (eq_sym Hz)).
Admitted.
