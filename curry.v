(* ------------------------------------------------------------------ *)
(* Formalization of:                                                    *)
(*   (A) the "original" natural semantics for FlatCurry                 *)
(*       (Hanus et al., "A natural semantics for functional logic       *)
(*        programs", Fig. 2 of natural_semantics.pdf; also restated     *)
(*        as Fig. 2 / rules Nat-* of lsfa24.tex)                        *)
(*   (B) the graph-based execution model of lsfa24.tex, Figures 8 & 9   *)
(*       (the "basic" and "case" rules of the head-normal-form          *)
(*        relation G,S : e Down G',S' : v), restricted to the fragment  *)
(*        that Theorem 2 of the paper is actually stated for:           *)
(*        first-order, fully applied expressions (no `apply`/PART       *)
(*        nodes, no literals -- exactly the restriction the paper's own *)
(*        proof imposes: "we will assume all expressions are first      *)
(*        order and all applications are fully applied").               *)
(*                                                                        *)
(* Goal: state and attempt to prove Theorem 2 of lsfa24.tex:             *)
(*   If  G,S : e Down G',S' : v  (v a constructor)                       *)
(*   then there are heaps Gamma, Gamma' "corresponding" to G, G' such    *)
(*   that   Gamma : e Down_C Gamma' : v'                                 *)
(*        where v' is v with FWD-nodes contracted.                       *)
(* ------------------------------------------------------------------ *)

Require Import List Arith Lia.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(* 0. Basic vocabulary                                                  *)
(* ------------------------------------------------------------------ *)

Definition var   := nat.
Definition fname := nat.
Definition cname := nat.

(* ------------------------------------------------------------------ *)
(* 1. Shared syntax.                                                    *)
(*                                                                        *)
(* Restricted FlatCurry (Fig. "ref:restrict" of lsfa24.tex) is a         *)
(* syntactic *subset* of ordinary FlatCurry (Fig. "fig:flat"): all       *)
(* function/constructor/choice arguments are already variables, and     *)
(* every function body is a chain of lets followed by either a case     *)
(* or a plain expression.  We therefore use ONE grammar, `Blk`, and       *)
(* run BOTH semantics over it -- exactly what the paper's own            *)
(* Theorem 2 does (it writes "Gamma : e Down_C Gamma' : v'" for the      *)
(* very same e that the graph judgement was evaluating).                 *)
(*                                                                        *)
(* We drop literals and `apply`/PART nodes, matching the paper's own    *)
(* scoping of Theorem 2 to "first order ... fully applied" expressions. *)
(* We also drop the rigid `case` (only `fcase`-like narrowing case      *)
(* survives) because restricted FlatCurry only has one kind of case,    *)
(* and the informal text says explicitly that a free variable is a      *)
(* normal form that (the single) case can narrow.                      *)
(* ------------------------------------------------------------------ *)

Inductive Expr0 :=
| EVar   (x : var)
| EBot
| EFree
| EChoice (x y : var)
| EFun   (f : fname) (args : list var)
| ECon   (c : cname) (args : list var).

Inductive Blk :=
| BLet  (x : var) (e : Expr0) (k : Blk)
| BCase (x : var) (brs : list (cname * list var * Blk))
| BExpr (e : Expr0).

(* A program maps function names to (formal parameters, body). *)
Definition Prog := fname -> option (list var * Blk).

(* ------------------------------------------------------------------ *)
(* 2. Renaming (pure variable-for-variable substitution).               *)
(* ------------------------------------------------------------------ *)

Definition ren := var -> var.

Definition rename_e0 (s : ren) (e : Expr0) : Expr0 :=
  match e with
  | EVar x        => EVar (s x)
  | EBot           => EBot
  | EFree          => EFree
  | EChoice x y    => EChoice (s x) (s y)
  | EFun f args    => EFun f (map s args)
  | ECon c args    => ECon c (map s args)
  end.

Fixpoint rename_b (s : ren) (b : Blk) : Blk :=
  match b with
  | BLet x e k   => BLet (s x) (rename_e0 s e) (rename_b s k)
  | BCase x brs  => BCase (s x)
                      (map (fun p => match p with
                                     | (c, ps, bd) => (c, map s ps, rename_b s bd)
                                     end) brs)
  | BExpr e      => BExpr (rename_e0 s e)
  end.

(* Well-formedness: a bare, un-Case'd `EChoice` never has any GEval        *)
(* counterpart (Section 7c's NEval_realizes_GEval_is_false family) --      *)
(* Nat-Or always eagerly resolves it, while the graph semantics leaves an  *)
(* un-cased choice as-is.  The ONLY place a choice is legitimate is as a   *)
(* let-binding's RHS (`let z = (a ? b) in ...`), matching G_Let/N_Let's    *)
(* own treatment of it as an opaque, unforced heap value -- never as a     *)
(* function body, let-continuation, or case-branch body outright.  This   *)
(* recursively excludes it from every OTHER position a Blk can reach.      *)
Fixpoint NoBareChoiceB (b : Blk) : Prop :=
  match b with
  | BLet x e k => NoBareChoiceB k
  | BCase x brs =>
      fold_right (fun p acc => NoBareChoiceB (match p with (_, _, bd) => bd end) /\ acc) True brs
  | BExpr e => match e with EChoice _ _ => False | _ => True end
  end.

Lemma NoBareChoiceB_in :
  forall brs c ys bd, In (c, ys, bd) brs ->
  fold_right (fun (p : cname * list var * Blk) acc =>
                NoBareChoiceB (match p with (_, _, bd0) => bd0 end) /\ acc) True brs ->
  NoBareChoiceB bd.
Proof.
  induction brs as [| [[c0 ys0] bd0] brs' IH]; intros c ys bd Hin Hnbc.
  - destruct Hin.
  - destruct Hin as [Heq | Hin].
    + injection Heq as Heq1 Heq2 Heq3; subst c0 ys0 bd0. exact (proj1 Hnbc).
    + exact (IH c ys bd Hin (proj2 Hnbc)).
Qed.

Fixpoint blk_size (b : Blk) : nat :=
  match b with
  | BLet x e k => S (blk_size k)
  | BCase x brs =>
      S (fold_right (fun p acc => blk_size (match p with (_, _, bd) => bd end) + acc) 0 brs)
  | BExpr e => 0
  end.

Lemma blk_size_in_bound :
  forall x brs c ys bd, In (c, ys, bd) brs -> blk_size bd < blk_size (BCase x brs).
Proof.
  intros x brs c ys bd Hin. simpl.
  assert (H : blk_size bd <=
    fold_right (fun p acc => blk_size (match p with (_, _, bd0) => bd0 end) + acc) 0 brs).
  { induction brs as [| [[c0 ys0] bd0] brs' IH].
    - destruct Hin.
    - destruct Hin as [Heq | Hin].
      + injection Heq as Heq1 Heq2 Heq3; subst c0 ys0 bd0. simpl. lia.
      + simpl. specialize (IH Hin). lia. }
  lia.
Qed.

Lemma NoBareChoiceB_rename_bound :
  forall n b, blk_size b < n -> forall s, NoBareChoiceB b -> NoBareChoiceB (rename_b s b).
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

Lemma NoBareChoiceB_rename : forall s b, NoBareChoiceB b -> NoBareChoiceB (rename_b s b).
Proof.
  intros s b H.
  exact (NoBareChoiceB_rename_bound (S (blk_size b)) b (Nat.lt_succ_diag_r _) s H).
Qed.

(* A well-formed program's every function body is itself choice-free at   *)
(* its own top level (matching the "choices only ever arise as let-RHS"   *)
(* discipline) -- needed to let NoBareChoiceB propagate through Nat-Fun's *)
(* own unfolding, not just through the syntax of a single expression.     *)
Definition ProgWF (P : Prog) : Prop :=
  forall f ps body, P f = Some (ps, body) -> NoBareChoiceB body.

Definition injective (s : ren) := forall x y, s x = s y -> x = y.

(* A positional renaming built from two parallel lists (pattern       *)
(* variables ys, actual variables zs): maps the i-th element of ys to *)
(* the i-th element of zs, and is the identity elsewhere.             *)
Fixpoint zipsubst (ys zs : list var) : ren :=
  match ys, zs with
  | y :: ys', z :: zs' => fun w => if Nat.eqb w y then z else zipsubst ys' zs' w
  | _, _ => fun w => w
  end.

(* ------------------------------------------------------------------ *)
(* 3. Heaps                                                             *)
(* ------------------------------------------------------------------ *)

Definition heap (A : Type) := var -> option A.

Definition hupd {A} (h : heap A) (x : var) (v : A) : heap A :=
  fun y => if Nat.eqb y x then Some v else h y.

Fixpoint hupd_list {A} (h : heap A) (xs : list var) (vs : list A) : heap A :=
  match xs, vs with
  | x :: xs', v :: vs' => hupd (hupd_list h xs' vs') x v
  | _, _ => h
  end.

Definition hempty {A} : heap A := fun _ => None.

(* ------------------------------------------------------------------ *)
(* 4. The graph semantics (lsfa24.tex, Figures 8 & 9).                  *)
(* ------------------------------------------------------------------ *)

Inductive GNode :=
| GExpr (e : Expr0)
| GFwd  (x : var).

Definition Graph := heap GNode.

(* NOTE ON THE STACK.  Figures 8-9 thread a backtracking stack S        *)
(* through the head-normal-form judgement, but *only ever push* onto    *)
(* it (nothing in Fig. 8/9 inspects or pops S; only the separate        *)
(* backtracking relations of Fig. 7 do that).  Theorem 2's statement    *)
(* does not mention S at all, and the paper's own proof explicitly      *)
(* says: "We elide the stack in all of these mappings because it is     *)
(* not relevant to the proof."  We take the same, paper-licensed        *)
(* simplification and omit S from `GEval` below.                        *)

Section GraphSemantics.
Variable P : Prog.

Inductive GEval : Graph -> Blk -> Graph -> GNode -> Prop :=
| G_Bot : forall G,
    GEval G (BExpr EBot) G (GExpr EBot)
| G_Free : forall G,
    GEval G (BExpr EFree) G (GExpr EFree)
| G_Con : forall G c args,
    GEval G (BExpr (ECon c args)) G (GExpr (ECon c args))
| G_Choice : forall G x y,
    GEval G (BExpr (EChoice x y)) G (GExpr (EChoice x y))
| G_Var : forall G x,
    GEval G (BExpr (EVar x)) G (GFwd x)
| G_Fun : forall G G1 f args ps body v s,
    P f = Some (ps, body) ->
    length ps = length args ->
    injective s ->
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) ->
    (forall y, ~ In y ps -> G (s y) = None) ->
    GEval G (rename_b s body) G1 v ->
    GEval G (BExpr (EFun f args)) G1 v
(* NOTE: we add the side condition `G x = None`, i.e. x is fresh.       *)
(* The paper never states this explicitly for (Let), but relies on it   *)
(* implicitly (via "we assume all variables from function definitions   *)
(* are fresh", Fig. 8's caption) -- without it, a let could silently     *)
(* clobber a live binding.  See the discussion at the end of this file. *)
| G_Let : forall G G1 x e k v,
    G x = None ->
    GEval (hupd G x (GExpr e)) k G1 v ->
    GEval G (BLet x e k) G1 v
| G_CaseBot : forall G x brs,
    G x = Some (GExpr EBot) ->
    GEval G (BCase x brs) G (GExpr EBot)
| G_CaseFwd : forall G x y brs G1 v,
    G x = Some (GFwd y) ->
    GEval G (BCase y brs) G1 v ->
    GEval G (BCase x brs) G1 v
| G_CaseFun : forall G x f args brs G1 vx G2 v,
    G x = Some (GExpr (EFun f args)) ->
    GEval G (BExpr (EFun f args)) G1 vx ->
    GEval (hupd G1 x vx) (BCase x brs) G2 v ->
    GEval G (BCase x brs) G2 v
| G_CaseChoice : forall G x y z brs G1 v,
    G x = Some (GExpr (EChoice y z)) ->
    GEval (hupd G x (GFwd y)) (BCase y brs) G1 v ->
    GEval G (BCase x brs) G1 v
| G_CaseCon : forall G x c zs brs ys body G1 v,
    G x = Some (GExpr (ECon c zs)) ->
    List.In (c, ys, body) brs ->
    length ys = length zs ->
    GEval G (rename_b (zipsubst ys zs) body) G1 v ->
    GEval G (BCase x brs) G1 v
| G_CaseConFree : forall G x c1 ys1 body1 brs G1 v ws,
    G x = Some (GExpr EFree) ->
    hd_error brs = Some (c1, ys1, body1) ->
    length ws = length ys1 ->
    NoDup ws ->
    (forall w, In w ws -> G w = None) ->
    GEval (hupd_list (hupd G x (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
          (rename_b (zipsubst ys1 ws) body1)
          G1 v ->
    GEval G (BCase x brs) G1 v.

End GraphSemantics.

(* ------------------------------------------------------------------ *)
(* 5. The "original" natural semantics.                                 *)
(*                                                                        *)
(* This is Fig. 2 of natural_semantics.pdf (Hanus et al.), cross-checked *)
(* directly against the rendered PDF text, NOT the lsfa24.tex            *)
(* restatement (which, as documented at the bottom of this file, has     *)
(* two discrepancies against the true original).  We use the CORRECT    *)
(* original here, since that is literally "the original semantics" the   *)
(* task asks for; the discrepancies are discussed separately below.      *)
(*                                                                        *)
(* Free variables are not first-class syntax here (matching the true     *)
(* original): a `let y = free in k` binds y to the literal expression    *)
(* EFree, which is itself already a value; forcing a variable bound to   *)
(* EFree turns it into a self-loop `y = EVar y`, matching the paper's    *)
(* own description "free variables are represented as a variable that   *)
(* is mapped to itself in the heap".                                     *)
(*                                                                        *)
(* Case is always the "narrowing" (fcase-like) case, matching the fact   *)
(* that restricted FlatCurry (and lsfa's own Fig. 2 restatement, which    *)
(* only has Nat-Select/Nat-Guess for a single unified `case`) has only    *)
(* one kind of case, which narrows free variables.                       *)
(* ------------------------------------------------------------------ *)

Definition NHeap := heap Blk.

Definition let_content (x : var) (e : Expr0) : Blk :=
  match e with
  | EFree => BExpr (EVar x)
  | _ => BExpr e
  end.

Section NatSemantics.
Variable P : Prog.

(* BLACK-HOLE GUARD (added after `blackhole_counterexample`, Section     *)
(* 7b-i, exhibited a concrete Qed derivation where a heap location's      *)
(* thunk gets evaluated a SECOND, independent time while its FIRST        *)
(* evaluation is still in flight -- Nat-VarExp's memoization step was     *)
(* unconditional and never detected this).  `F : list var` is the set of *)
(* locations currently "under active force" on the current derivation's  *)
(* call stack.  Nat-VarExp is the only rule that forces a NAMED heap      *)
(* location, so it is the only rule that (a) checks the location it is   *)
(* about to force is not already in F, and (b) pushes it onto F for its  *)
(* own recursive premise.  Every other rule just threads F through        *)
(* unchanged.  Top-level judgments (theorem statements, the axioms below, *)
(* and anywhere else NEval is invoked "fresh") start with F = nil.        *)
Inductive NEval : list var -> NHeap -> Blk -> NHeap -> Blk -> Prop :=
| N_VarCons : forall F G x c args,
    G x = Some (BExpr (ECon c args)) ->
    NEval F G (BExpr (EVar x)) G (BExpr (ECon c args))
| N_VarSelf : forall F G x,
    G x = Some (BExpr (EVar x)) ->
    NEval F G (BExpr (EVar x)) G (BExpr (EVar x))
| N_VarFree : forall F G x,
    G x = Some (BExpr EFree) ->
    NEval F G (BExpr (EVar x)) (hupd G x (BExpr (EVar x))) (BExpr (EVar x))
| N_VarExp : forall F G x e G1 v,
    ~ In x F ->
    G x = Some e ->
    (forall c args, e <> BExpr (ECon c args)) ->
    e <> BExpr (EVar x) ->
    e <> BExpr EFree ->
    NEval (x :: F) G e G1 v ->
    NEval F G (BExpr (EVar x)) (hupd G1 x v) v
| N_ValFree : forall F G,
    NEval F G (BExpr EFree) G (BExpr EFree)
| N_ValCon : forall F G c args,
    NEval F G (BExpr (ECon c args)) G (BExpr (ECon c args))
(* MODELING NOTE (see bottom-of-file discussion "On alpha-renaming"):    *)
(* Fig. 2 of natural_semantics.pdf only mentions freshness for the       *)
(* variables bound directly by Let/Guess, not for a function's OTHER    *)
(* local (let-/pattern-)bound variables at unfold time; it is silent on *)
(* the exact mechanics, implicitly relying on a Barendregt-style        *)
(* "all bound variables are already suitably fresh" convention.  We     *)
(* resolve that silence by moving ALL freshening to function-unfold      *)
(* time, exactly mirroring (Fun)/Fig. 8's own freshening discipline      *)
(* ("we assume all variables from function definitions are fresh").      *)
(* This is an extensionally-equivalent way to realize the same           *)
(* convention (proving that equivalence in general would itself be a    *)
(* separate alpha-conversion meta-theorem); we did not have time to      *)
(* prove that separate equivalence, so this file's N_Fun is a            *)
(* deliberately-chosen, clearly-flagged strengthening of the literal     *)
(* Fig. 2 text, not a literal transcription of it.                       *)
| N_Fun : forall F G G1 f args ps body v s,
    P f = Some (ps, body) ->
    length ps = length args ->
    injective s ->
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) ->
    (forall y, ~ In y ps -> G (s y) = None) ->
    NEval F G (rename_b s body) G1 v ->
    NEval F G (BExpr (EFun f args)) G1 v
(* `let_content` mirrors the fact that a `free` right-hand side is       *)
(* ALREADY a self-referential free variable from the moment it is        *)
(* declared (the true original semantics has no separate "not yet        *)
(* forced free thunk" state; free variables are circular bindings from   *)
(* birth).                                                                *)
| N_Let : forall F G G1 x (e : Expr0) k v,
    G x = None ->
    NEval F (hupd G x (let_content x e)) k G1 v ->
    NEval F G (BLet x e k) G1 v
| N_Or : forall F G x y G1 v i,
    (i = x \/ i = y) ->
    NEval F G (BExpr (EVar i)) G1 v ->
    NEval F G (BExpr (EChoice x y)) G1 v
| N_Select : forall F G x c zs brs ys body G1 v G2,
    NEval F G (BExpr (EVar x)) G1 (BExpr (ECon c zs)) ->
    List.In (c, ys, body) brs ->
    length ys = length zs ->
    NEval F G1 (rename_b (zipsubst ys zs) body) G2 v ->
    NEval F G (BCase x brs) G2 v
| N_Guess : forall F G x G1 x' c1 ys1 body1 brs G2 v ws,
    NEval F G (BExpr (EVar x)) G1 (BExpr (EVar x')) ->
    hd_error brs = Some (c1, ys1, body1) ->
    length ws = length ys1 ->
    NoDup ws ->
    (forall w, In w ws -> G1 w = None) ->
    (* Fresh pattern variables are self-loops from birth, matching        *)
    (* N_Let's `let_content` treatment of `free` (see the "true          *)
    (* original" convention: free variables are circular bindings).       *)
    NEval F (hupd_list (hupd G1 x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
          (rename_b (zipsubst ys1 ws) body1)
          G2 v ->
    NEval F G (BCase x brs) G2 v.

End NatSemantics.

(* ------------------------------------------------------------------ *)
(* 6. Heap correspondence "Gamma corresponds to G".                     *)
(*                                                                        *)
(* The paper never defines this precisely -- it is exactly the kind of  *)
(* thing that needs to be pinned down to even STATE Theorem 2 formally,  *)
(* let alone prove it.  The construction below is the natural formal    *)
(* reading of the informal text: a graph location corresponds to a       *)
(* natural-semantics heap slot holding the SAME content, except that     *)
(* chains of FWD nodes on the graph side must be "contracted" (chased    *)
(* to their final non-FWD content) to obtain the corresponding content,  *)
(* and a location that is (after contraction) bound to `free` on the    *)
(* graph side corresponds to a *self-loop* `Gamma[x] = EVar x` on the    *)
(* natural-semantics side if x is itself the canonical (non-forwarded)   *)
(* location, or an *alias* `Gamma[x] = EVar y` if x forwards to a        *)
(* different free location y -- matching the paper's own description   *)
(* that free variables are represented by self-loops.                   *)
(* ------------------------------------------------------------------ *)

(* [ContractLoc G x y]: starting from location x, chase GFwd pointers    *)
(* until reaching a canonical, non-forwarded location y.                *)
Inductive ContractLoc (G : Graph) : var -> var -> Prop :=
| CL_Here : forall x e, G x = Some (GExpr e) -> ContractLoc G x x
| CL_Fwd  : forall x y z, G x = Some (GFwd y) -> ContractLoc G y z -> ContractLoc G x z.

(* [CorrVTerm G x b]: the FULLY FWD-contracted content that x resolves   *)
(* to -- used only for the theorem's *result* value, since the paper     *)
(* explicitly requires v' to be "v with forward nodes contracted".       *)
Inductive CorrVTerm (G : Graph) (x : var) : Blk -> Prop :=
| CVT_Con : forall y c args, ContractLoc G x y -> G y = Some (GExpr (ECon c args)) ->
              CorrVTerm G x (BExpr (ECon c args))
| CVT_Free : forall y, ContractLoc G x y -> G y = Some (GExpr EFree) ->
              CorrVTerm G x (BExpr (EVar y))
| CVT_Fun : forall y f args, ContractLoc G x y -> G y = Some (GExpr (EFun f args)) ->
              CorrVTerm G x (BExpr (EFun f args))
| CVT_Choice : forall y y1 y2, ContractLoc G x y -> G y = Some (GExpr (EChoice y1 y2)) ->
              CorrVTerm G x (BExpr (EChoice y1 y2))
| CVT_Var : forall y z, ContractLoc G x y -> G y = Some (GExpr (EVar z)) ->
              CorrVTerm G x (BExpr (EVar z))
| CVT_Bot : forall y, ContractLoc G x y -> G y = Some (GExpr EBot) ->
              CorrVTerm G x (BExpr EBot).

Inductive CorrV (G : Graph) : GNode -> Blk -> Prop :=
| CorrV_Direct : forall e, CorrV G (GExpr e) (BExpr e)
| CorrV_Fwd    : forall x b, CorrVTerm G x b -> CorrV G (GFwd x) b.

(* [CorrE G x b]: `b` is a VALID natural-semantics representation of     *)
(* graph location x: either x's own immediate content directly           *)
(* translated (with `free` becoming the self-loop `EVar x`), or, if x    *)
(* forwards to y, EITHER the lazy 1-hop alias `EVar y` OR an ACHIEVED    *)
(* value -- a genuine constructor, or a genuine free-variable self-loop  *)
(* -- reached by chasing (via ContractLoc) all the way to y's own        *)
(* canonical target.                                                     *)
(*                                                                        *)
(* This is DELIBERATELY multi-valued: several different `b`s can be      *)
(* valid for the same x.  It has to tolerate a natural-semantics heap    *)
(* that sits anywhere between "as lazy as the graph's own indirection"   *)
(* and "fully forced", because Nat-VarExp always eagerly memoizes to     *)
(* the fully-resolved value while the graph only mutates FWD nodes via   *)
(* explicit rules (Case-Fun, Case-Choice, ...).  A deterministic,        *)
(* always-fully-contracted CorrE (our first attempt) breaks as soon as   *)
(* one location's canonical content changes while another location      *)
(* still holds an as-yet-unrefreshed alias to it -- see "On sharing      *)
(* through forwarding nodes" at the end of this file.                    *)
(*                                                                        *)
(* REVISED (see the two HISTORICAL NOTEs below, in the sections that      *)
(* used to be HeapCorr_update_not_general and                             *)
(* NEval_confluence_unrestricted_is_false): the ORIGINAL version of this   *)
(* relation had a single fully general `CorrE_FwdChase : G x=GFwd y ->     *)
(* CorrE G y b -> CorrE G x b`, letting a forwarding location's witness    *)
(* be ANY valid representation of y -- including a raw, NON-terminal      *)
(* one (an unforced EFun/EChoice/EVar-thunk copied straight from wherever  *)
(* the chain led).  That is strictly more than the informal spec ever      *)
(* intended ("as lazy as the graph's own indirection" OR "fully forced")    *)
(* and, precisely because it let a forwarding location's Gam-witness be     *)
(* an operationally-INDEPENDENT copy of in-progress content (rather than     *)
(* either a lazy pointer or a genuinely-finished value), it admitted Gam's    *)
(* that could never arise from any real execution: stale copies that go       *)
(* wrong under an otherwise-ordinary graph mutation, and self-referential      *)
(* copies that never terminate at all.  The two constructors below replace     *)
(* it, restricting the "chase" to ONLY the two shapes Nat-VarExp can ever        *)
(* actually finish memoizing to.                                                 *)
Inductive CorrE (G : Graph) : var -> Blk -> Prop :=
| CorrE_Con : forall x c args, G x = Some (GExpr (ECon c args)) -> CorrE G x (BExpr (ECon c args))
| CorrE_Free : forall x, G x = Some (GExpr EFree) -> CorrE G x (BExpr (EVar x))
| CorrE_Fun : forall x f args, G x = Some (GExpr (EFun f args)) -> CorrE G x (BExpr (EFun f args))
| CorrE_Choice : forall x y z, G x = Some (GExpr (EChoice y z)) -> CorrE G x (BExpr (EChoice y z))
| CorrE_VarThunk : forall x z, G x = Some (GExpr (EVar z)) -> CorrE G x (BExpr (EVar z))
| CorrE_Bot : forall x, G x = Some (GExpr EBot) -> CorrE G x (BExpr EBot)
| CorrE_FwdHere : forall x y, G x = Some (GFwd y) -> CorrE G x (BExpr (EVar y))
| CorrE_FwdAchievedCon : forall x y z c args, G x = Some (GFwd y) -> ContractLoc G y z ->
    G z = Some (GExpr (ECon c args)) -> CorrE G x (BExpr (ECon c args)).
(* NOTE: there is deliberately NO "FwdAchievedFree" counterpart chasing to a
   genuine free-variable self-loop.  Con is a PERMANENT fact once achieved --
   no GEval rule ever mutates an already-Con-shaped location -- so a
   forwarding predecessor's "skip-ahead" Con witness can never go stale.
   Free is NOT permanent (G_CaseConFree narrows a free location to a
   constructor), so an analogous skip-ahead free-witness for a location
   MULTIPLE hops away would go stale exactly when that narrowing happens
   -- CorrE_update_free_other, below, is where this was actually discovered
   (as a failed proof obligation, not a hypothetical).  The only safe way
   to represent "eventually reaches a free variable" here is the literal,
   hop-by-hop 1-alias chain (CorrE_FwdHere, composed one hop at a time),
   never a shortcut through possibly-changing content.*)

Definition HeapCorr (G : Graph) (Gam : NHeap) : Prop :=
  forall x, match G x with
            | None => Gam x = None
            | Some _ => exists b, Gam x = Some b /\ CorrE G x b
            end.

Lemma ContractLoc_functional :
  forall G x y1 y2, ContractLoc G x y1 -> ContractLoc G x y2 -> y1 = y2.
Proof.
  intros G x y1 y2 H. revert y2.
  induction H; intros y2 H2; inversion H2; subst; try congruence.
  apply IHContractLoc. congruence.
Qed.

Lemma ContractLoc_dom : forall G x y, ContractLoc G x y -> G x <> None.
Proof. intros G x y H; inversion H; congruence. Qed.

Lemma ContractLoc_dom_tgt : forall G x y, ContractLoc G x y -> G y <> None.
Proof.
  intros G x y H; induction H.
  - congruence.
  - exact IHContractLoc.
Qed.

Lemma ContractLoc_nonfwd : forall G x y e, G x = Some (GExpr e) -> ContractLoc G x y -> y = x.
Proof. intros G x y e Hx H; inversion H; congruence. Qed.

Lemma ContractLoc_no_selfFwd : forall G x y, ContractLoc G x y -> G x <> Some (GFwd x).
Proof.
  intros G x y H. induction H as [x0 e0 H0 | x0 y0 z0 H0 Hrec IH]; intro Hself.
  - congruence.
  - assert (y0 = x0) by congruence. subst y0. exact (IH Hself).
Qed.

(* A nat-indexed mirror of ContractLoc, used purely so that we can do    *)
(* well-founded / strong induction on the chain length: ordinary Coq     *)
(* induction cannot recurse into an arbitrary intermediate point of a    *)
(* ContractLoc chain (it is not a structural subterm), but it CAN        *)
(* recurse on "the bound is smaller".                                    *)
Inductive ContractLocN (G : Graph) : nat -> var -> var -> Prop :=
| CLN_Here : forall x e, G x = Some (GExpr e) -> ContractLocN G 0 x x
| CLN_Fwd  : forall n x y z, G x = Some (GFwd y) -> ContractLocN G n y z -> ContractLocN G (S n) x z.

Lemma ContractLoc_to_N : forall G x y, ContractLoc G x y -> exists n, ContractLocN G n x y.
Proof.
  intros G x y H; induction H.
  - exists 0. eapply CLN_Here; eassumption.
  - destruct IHContractLoc as [n Hn]. exists (S n). eapply CLN_Fwd; eassumption.
Qed.

Lemma ContractLocN_to_ContractLoc : forall G n x y, ContractLocN G n x y -> ContractLoc G x y.
Proof.
  intros G n x y H; induction H as [x0 e0 H0 | n0 x0 y0 z0 H0 Hcln0 IH].
  - eapply CL_Here; exact H0.
  - eapply CL_Fwd; [exact H0 | exact IH].
Qed.

Lemma ContractLocN_nonfwd :
  forall G n x y e, G x = Some (GExpr e) -> ContractLocN G n x y -> n = 0 /\ y = x.
Proof.
  intros G n x y e Hx H. inversion H; subst.
  - split; reflexivity.
  - congruence.
Qed.

(* Given that x's canonical (fully contracted) target y holds a          *)
(* constructor, any VALID CorrE witness b for x is EITHER exactly that   *)
(* constructor, or a lazy alias `EVar y1` where y1 is STILL somewhere    *)
(* on x's own path to y (strictly closer to y than x is, per the bound). *)
Lemma CorrE_dom : forall G x b, CorrE G x b -> G x <> None.
Proof. intros G x b H; destruct H; congruence. Qed.

(* When G x is DIRECTLY (non-forwarded) content, CorrE is functional:    *)
(* only one constructor can possibly match, since they all pattern-match *)
(* on G x's own immediate shape.                                         *)
Lemma CorrE_from_con :
  forall G x c args, G x = Some (GExpr (ECon c args)) ->
  forall b, CorrE G x b -> b = BExpr (ECon c args).
Proof. intros G x c args Hx b H; destruct H; congruence. Qed.

(* Generalization: since CorrE at a NON-forwarded location is           *)
(* functional (any location that is directly GExpr-shaped can only be   *)
(* represented one way), its content is exactly `let_content`.          *)
Lemma CorrE_direct_unique :
  forall G x e, G x = Some (GExpr e) -> forall b, CorrE G x b -> b = let_content x e.
Proof.
  intros G x e Hx b H; destruct H;
    match goal with
    | [ H0 : G x = Some (GExpr ?e0) |- _ ] =>
        assert (e = e0) by congruence; subst e; simpl; congruence
    | [ H0 : G x = Some (GFwd _) |- _ ] => congruence
    end.
Qed.

Lemma Gam_from_con :
  forall G x c args, G x = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr G Gam -> Gam x = Some (BExpr (ECon c args)).
Proof.
  intros G x c args Hx Gam HGam.
  specialize (HGam x). rewrite Hx in HGam.
  destruct HGam as [b [Hb HCE]].
  assert (b = BExpr (ECon c args)) by (eapply CorrE_from_con; eauto).
  subst b. exact Hb.
Qed.

Lemma CorrE_con_progress_N :
  forall G x b, CorrE G x b ->
  forall n y c args, ContractLocN G n x y -> G y = Some (GExpr (ECon c args)) ->
  b = BExpr (ECon c args) \/
  exists m y1, m < n /\ b = BExpr (EVar y1) /\ ContractLocN G m y1 y.
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
  - (* Con: x0 itself canonical, holds ECon c0 args0 *)
    left.
    destruct (ContractLocN_nonfwd G n x0 y (ECon c0 args0) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - (* Free -- contradiction with target Con *)
    exfalso.
    destruct (ContractLocN_nonfwd G n x0 y EFree H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. discriminate.
  - (* Fun *) exfalso.
    destruct (ContractLocN_nonfwd G n x0 y (EFun f0 fargs0) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. discriminate.
  - (* Choice *) exfalso.
    destruct (ContractLocN_nonfwd G n x0 y (EChoice y1 z1) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. discriminate.
  - (* VarThunk *) exfalso.
    destruct (ContractLocN_nonfwd G n x0 y (EVar z1) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. discriminate.
  - (* Bot *) exfalso.
    destruct (ContractLocN_nonfwd G n x0 y EBot H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. discriminate.
  - (* FwdHere: b = EVar y0, x0 -fwd-> y0 *)
    right.
    inversion Hcln as [x1 e1 He1 | n1 x1 y1 z1 Hx1 Hcz1]; subst; [congruence | ].
    assert (y1 = y0) by congruence. subst y1.
    exists n1, y0. split; [lia | split; [reflexivity | exact Hcz1]].
  - (* FwdAchievedCon : G x0=GFwd y0, ContractLoc G y0 z0, G z0=Con c0' args0' --
       y0's canonical target is FUNCTIONAL, so z0 must be exactly the outer y,
       forcing this achieved constructor to BE the target constructor. *)
    inversion Hcln as [x1 e1 He1 | n1 x1 y1 z1 Hx1 Hcz1]; subst; [congruence | ].
    assert (y1 = y0) by congruence. subst y1.
    assert (Heqz : z0 = y)
      by (eapply ContractLoc_functional; [exact Hcl0 | exact (ContractLocN_to_ContractLoc G n1 y0 y Hcz1)]).
    subst z0.
    left. congruence.
Qed.

Lemma ContractLocN_functional :
  forall G n1 x y1, ContractLocN G n1 x y1 ->
  forall n2 y2, ContractLocN G n2 x y2 -> n1 = n2 /\ y1 = y2.
Proof.
  intros G n1 x y1 H. induction H as [x0 e0 H0 | n0 x0 y0 z0 H0 Hcln0 IH]; intros n2 y2 H2.
  - inversion H2 as [x1 e1 H1 | n3 x1 y3 z1 H1 Hcln3]; subst.
    + split; reflexivity.
    + congruence.
  - inversion H2 as [x1 e1 H1 | n3 x1 y3 z1 H1 Hcln3]; subst.
    + congruence.
    + assert (y0 = y3) by congruence. subst y3.
      destruct (IH n3 y2 Hcln3) as [Heqn Heqz].
      split; congruence.
Qed.

(* Needed for the black-hole guard: a ContractLocN chain's own endpoint  *)
(* is always non-forwarded (CLN_Here's own requirement, propagated       *)
(* through CLN_Fwd), and consequently a chain can only return to its own *)
(* starting point in zero steps -- a fwd chain never cycles.  This is    *)
(* exactly what lets force_var_N's alias-chase build up a "currently     *)
(* being forced" list with no risk of ever needing to re-push the same   *)
(* location (which the new Nat-VarExp side condition would reject).      *)
Lemma ContractLocN_endpoint_nonfwd :
  forall G n x y, ContractLocN G n x y -> exists e, G y = Some (GExpr e).
Proof.
  intros G n x y H.
  induction H as [x0 e0 H0 | n0 x0 y0 z0 H0 Hcln0 IH].
  - exists e0. exact H0.
  - exact IH.
Qed.

Lemma ContractLocN_self_only_zero :
  forall G i x, ContractLocN G i x x -> i = 0.
Proof.
  intros G i x H.
  destruct i as [| i'].
  - reflexivity.
  - exfalso.
    inversion H as [| n0 x0 y0 z0 H0 Hcln0]; subst.
    destruct (ContractLocN_endpoint_nonfwd G i' y0 x Hcln0) as [e He].
    congruence.
Qed.

(* Nothing reachable from x (at any chase length) can ever equal x       *)
(* itself, or (by prepending x's own first hop) anything reachable from  *)
(* the location x forwards to.  This is the "prepend one hop" step used  *)
(* to maintain force_var_N's own reachability-disjointness invariant.    *)
Lemma ContractLocN_not_reachable_from_self :
  forall G k x, ~ ContractLocN G (S k) x x.
Proof.
  intros G k x H.
  pose proof (ContractLocN_self_only_zero G (S k) x H) as Hc.
  discriminate Hc.
Qed.

Lemma ContractLocN_prepend :
  forall G x y0, G x = Some (GFwd y0) ->
  forall k z, ContractLocN G k y0 z -> ContractLocN G (S k) x z.
Proof.
  intros G x y0 Hx k z H.
  eapply CLN_Fwd; [exact Hx | exact H].
Qed.

(* The fully resolved (constructor) content is always a valid CorrE      *)
(* witness for every location on the path to it -- i.e. "prepending"     *)
(* forward hops onto an already-established CorrE fact stays valid.      *)
Lemma ContractLocN_to_CorrE :
  forall G n x y, ContractLocN G n x y ->
  forall c args, G y = Some (GExpr (ECon c args)) -> CorrE G x (BExpr (ECon c args)).
Proof.
  intros G n x y H; induction H as [x0 e0 H0 | n0 x0 y0 z0 H0 Hcln0 IH]; intros c args Hy.
  - rewrite H0 in Hy. inversion Hy; subst. apply CorrE_Con; exact H0.
  - eapply CorrE_FwdAchievedCon;
      [exact H0 | exact (ContractLocN_to_ContractLoc G n0 y0 z0 Hcln0) | exact Hy].
Qed.

Lemma ContractLocN_zero : forall G x y, ContractLocN G 0 x y -> y = x.
Proof. intros G x y H; inversion H; reflexivity. Qed.

Lemma ContractLocN_succ :
  forall G n0 x y, ContractLocN G (S n0) x y ->
  exists y0, G x = Some (GFwd y0) /\ ContractLocN G n0 y0 y.
Proof. intros G n0 x y H; inversion H as [| n1 x1 y1 z1 H1 Hcln1]; subst; eauto. Qed.


(* Threading the black-hole guard F through force_var_N: the alias-chase *)
(* it performs (via ContractLocN) never revisits a location, so it can    *)
(* correctly push each location it forces onto F as it goes, using        *)
(* ContractLocN_self_only_zero (a fwd chain never cycles) to justify      *)
(* that the invariant "nothing in F is reachable from the current start"  *)
(* survives each step (prepending the current hop via ContractLocN_prepend*)
(* / the direct CLN_Fwd argument below).                                  *)
Lemma force_var_N :
  forall P n G x y, ContractLocN G n x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr G Gam ->
  forall F, (forall z, In z F -> exists nz, ContractLocN G nz z y /\ n < nz) ->
  exists Gam', NEval P F Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr G Gam'.
Proof.
  intros P.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  intros G x y Hcln c args Hy Gam HGam F Hdisj.
  assert (HxF : ~ In x F).
  { intro Hin. destruct (Hdisj x Hin) as [nz [Hclnz Hgt]].
    destruct (ContractLocN_functional G n x y Hcln nz y Hclnz) as [Heqn _].
    lia. }
  destruct n as [| n0].
  - (* n=0 : x itself canonical *)
    assert (Hyx : y = x) by (eapply ContractLocN_zero; eauto). subst y.
    assert (Hb := Gam_from_con G x c args Hy Gam HGam).
    exists Gam. split.
    + apply N_VarCons. exact Hb.
    + exact HGam.
  - (* n = S n0 : x forwards to y0 *)
    destruct (ContractLocN_succ G n0 x y Hcln) as [y0 [Hxy0 Hcln0]].
    assert (HGamx := HGam x).
    assert (HGx : G x <> None) by congruence.
    destruct (G x) eqn:GX; [clear HGx | congruence].
    destruct HGamx as [b [Hb HCE]].
    assert (Hprog := CorrE_con_progress_N G x b HCE (S n0) y c args Hcln Hy).
    destruct Hprog as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
    + (* b already the target constructor *)
      subst b. exists Gam. split.
      * apply N_VarCons. exact Hb.
      * exact HGam.
    + (* b = EVar y1, y1 strictly closer to y (m < S n0) *)
      subst b.
      assert (Hy1x : y1 <> x).
      { intro Heq; subst y1.
        destruct (ContractLocN_functional G m x y Hcln1 (S n0) y Hcln) as [Hmn _].
        lia. }
      assert (Hdisj' : forall z, In z (x :: F) -> exists nz, ContractLocN G nz z y /\ m < nz).
      { intros z Hin.
        destruct Hin as [Heq | Hin].
        - subst z. exists (S n0). split; [exact Hcln | exact Hm].
        - destruct (Hdisj z Hin) as [nz [Hclnz Hgt]].
          exists nz. split; [exact Hclnz | lia]. }
      destruct (IHn m Hm G y1 y Hcln1 c args Hy Gam HGam (x :: F) Hdisj') as [Gam1 [HNE HHC]].
      exists (hupd Gam1 x (BExpr (ECon c args))).
      split.
      * eapply N_VarExp.
        -- exact HxF.
        -- exact Hb.
        -- intros c' args' Heq; discriminate.
        -- intro Heq; injection Heq as Heq'; congruence.
        -- intro Heq; discriminate.
        -- exact HNE.
      * intro z.
        destruct (Nat.eqb z x) eqn:Ezx.
        -- apply Nat.eqb_eq in Ezx; subst z.
           rewrite GX.
           eexists. split.
           ++ unfold hupd. rewrite Nat.eqb_refl. reflexivity.
           ++ eapply ContractLocN_to_CorrE; [exact Hcln | exact Hy].
        -- apply Nat.eqb_neq in Ezx.
           assert (Hhz : hupd Gam1 x (BExpr (ECon c args)) z = Gam1 z).
           { unfold hupd. destruct (Nat.eqb z x) eqn:E.
             - apply Nat.eqb_eq in E. congruence.
             - reflexivity. }
           rewrite Hhz.
           exact (HHC z).
Qed.
Lemma Gam_from_direct :
  forall G x yc, G x = Some (GExpr yc) ->
  forall Gam, HeapCorr G Gam -> Gam x = Some (let_content x yc).
Proof.
  intros G x yc Hx Gam HGam.
  specialize (HGam x). rewrite Hx in HGam.
  destruct HGam as [b [Hb HCE]].
  assert (b = let_content x yc) by (eapply CorrE_direct_unique; eauto).
  subst b. exact Hb.
Qed.

Lemma CorrE_progress_N :
  forall G x b, CorrE G x b ->
  forall n y yc, ContractLocN G n x y -> G y = Some (GExpr yc) ->
  b = let_content y yc \/
  exists m y1, m < n /\ b = BExpr (EVar y1) /\ ContractLocN G m y1 y.
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
  intros n y yc Hcln Hy.
  - left. destruct (ContractLocN_nonfwd G n x0 y (ECon c0 args0) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - left. destruct (ContractLocN_nonfwd G n x0 y EFree H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - left. destruct (ContractLocN_nonfwd G n x0 y (EFun f0 fargs0) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - left. destruct (ContractLocN_nonfwd G n x0 y (EChoice y1 z1) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - left. destruct (ContractLocN_nonfwd G n x0 y (EVar z1) H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - left. destruct (ContractLocN_nonfwd G n x0 y EBot H0 Hcln) as [_ Hyx0].
    subst y. rewrite H0 in Hy. inversion Hy; subst. reflexivity.
  - (* FwdHere: b = EVar y0, x0 -fwd-> y0 *)
    right.
    inversion Hcln as [x1 e1 He1 | n1 x1 y1 z1 Hx1 Hcz1]; subst; [congruence | ].
    assert (y1 = y0) by congruence. subst y1.
    exists n1, y0. split; [lia | split; [reflexivity | exact Hcz1]].
  - (* FwdAchievedCon : functionality forces z0 = y, so yc must literally BE
       this constructor, and let_content y yc is exactly BExpr(Con c0' args0') = b. *)
    inversion Hcln as [x1 e1 He1 | n1 x1 y1 z1 Hx1 Hcz1]; subst; [congruence | ].
    assert (y1 = y0) by congruence. subst y1.
    assert (Heqz : z0 = y)
      by (eapply ContractLoc_functional; [exact Hcl0 | exact (ContractLocN_to_ContractLoc G n1 y0 y Hcz1)]).
    subst z0.
    left. rewrite Hz0 in Hy. injection Hy as Hy. subst yc. reflexivity.
Qed.

(* REMOVED (unsound under the revised CorrE, and unused by theorem2 --      *)
(* only the Con-only force_var/force_var_N below are actually called):      *)
(* this file used to also have `ContractLocN_to_CorrE_gen`, `DirectAchievable`,*)
(* `force_var_gen_N`, and `force_var_gen`, generalizing force_var/force_var_N  *)
(* from "chases to a constructor" to "chases to EITHER a constructor OR a      *)
(* genuine free-variable self-loop", via a skip-ahead achieved-free witness     *)
(* exactly analogous to CorrE_FwdAchievedCon but for EFree.  That witness is      *)
(* UNSOUND for the same reason CorrE_FwdAchievedFree was removed above: Con is    *)
(* PERMANENT once achieved, but Free is NOT (G_CaseConFree narrows a free          *)
(* location to a constructor) -- so a location x that is MULTIPLE hops away        *)
(* from a free y, memoized skip-ahead to `EVar y`, would go stale (should now        *)
(* read the new constructor, not EVar y) the moment y gets narrowed, exactly like    *)
(* CorrE_update_free_other's own now-fixed proof obligation demonstrated concretely.  *)
(* Since nothing currently calls these (they were built ahead of the free-variable     *)
(* generalization of theorem2, which is not yet migrated into this file), they are      *)
(* simply dropped rather than weakened to the Con-only case, which would just             *)
(* duplicate force_var/force_var_N.  CorrE_progress_N and Gam_from_direct, above, remain  *)
(* -- CorrE_progress_N's own FwdHere case already produces the correct "closer alias"      *)
(* answer for a Free target with no achieved-chase reasoning needed at all.                 *)

Lemma force_var :
  forall P G x y, ContractLoc G x y ->
  forall c args, G y = Some (GExpr (ECon c args)) ->
  forall Gam, HeapCorr G Gam ->
  exists Gam', NEval P nil Gam (BExpr (EVar x)) Gam' (BExpr (ECon c args)) /\ HeapCorr G Gam'.
Proof.
  intros P G x y H c args Hy Gam HGam.
  destruct (ContractLoc_to_N G x y H) as [n Hn].
  eapply force_var_N; eauto.
  intros z Hin; destruct Hin.
Qed.

(* The one fragment of the missing "NEval soundness relative to G"       *)
(* lemma (see the G_CaseFwd discussion in Theorem 2's proof) that we DID *)
(* manage to isolate: if a location's CorrE witness happens to be        *)
(* Con-shaped, there is a genuine graph location realizing it directly.  *)
Lemma CorrE_con_to_contractloc :
  forall G x c args, CorrE G x (BExpr (ECon c args)) ->
  exists y, ContractLoc G x y /\ G y = Some (GExpr (ECon c args)).
Proof.
  intros G x c args H.
  remember (BExpr (ECon c args)) as target eqn:Ht.
  revert c args Ht.
  induction H as
    [ x0 c0 args0 H0
    | x0 H0
    | x0 f0 fargs0 H0
    | x0 y1 z1 H0
    | x0 z1 H0
    | x0 H0
    | x0 y0 H0
    | x0 y0 z0 c0' args0' H0 Hcl0 Hz0
    ]; intros c args Ht.
  - exists x0. split; [eapply CL_Here; eauto | ]. inversion Ht; subst. exact H0.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - (* FwdAchievedCon : ContractLoc G y0 z0, G z0 = Con c0' args0' directly *)
    injection Ht as Ht1 Ht2. subst c0' args0'.
    exists z0. split; [eapply CL_Fwd; [exact H0 | exact Hcl0] | exact Hz0].
Qed.

Lemma Gam_from_free :
  forall G x, G x = Some (GExpr EFree) ->
  forall Gam, HeapCorr G Gam -> Gam x = Some (BExpr (EVar x)).
Proof.
  intros G x Hx Gam HGam.
  specialize (HGam x). rewrite Hx in HGam.
  destruct HGam as [b [Hb HCE]].
  assert (b = BExpr (EVar x)) by (destruct HCE; congruence).
  subst b. exact Hb.
Qed.
Lemma hupd_neq : forall {A} (h : heap A) z g x, x <> z -> hupd h z g x = h x.
Proof.
  intros A h z g x Hxz. unfold hupd.
  destruct (Nat.eqb x z) eqn:E.
  - apply Nat.eqb_eq in E. congruence.
  - reflexivity.
Qed.

Lemma hupd_comm :
  forall {A} (h : heap A) a va b vb, a <> b ->
  forall w, hupd (hupd h a va) b vb w = hupd (hupd h b vb) a va w.
Proof.
  intros A h a va b vb Hab w. unfold hupd.
  destruct (Nat.eqb w b) eqn:Eb; destruct (Nat.eqb w a) eqn:Ea; try reflexivity.
  apply Nat.eqb_eq in Ea, Eb. exfalso. apply Hab. congruence.
Qed.

(* Moved up from its original spot (just before WellFoundedFwd_extend,     *)
(* further down) and generalized from `hupd G z (GExpr e0)` to an           *)
(* arbitrary fresh extension `hupd G z g` (g : GNode) -- the proof never      *)
(* actually inspected g's shape, only that z is fresh, so this was a free      *)
(* generalization.  Needed here (moved earlier) because CorrE_other, just      *)
(* below, now needs it for CorrE_FwdAchievedCon/FwdAchievedFree's own            *)
(* ContractLoc premises.                                                         *)
Lemma ContractLoc_extend :
  forall G z g, G z = None ->
  forall w target, ContractLoc G w target -> ContractLoc (hupd G z g) w target.
Proof.
  intros G z g Hz w target H.
  induction H as [x0 e1 H0 | x0 y0 z0 H0 Hcl0 IH].
  - eapply CL_Here.
    assert (Hx0z : x0 <> z) by (intro Heq; subst x0; congruence).
    unfold hupd. apply Nat.eqb_neq in Hx0z. rewrite Hx0z. exact H0.
  - eapply CL_Fwd.
    + assert (Hx0z : x0 <> z) by (intro Heq; subst x0; congruence).
      unfold hupd. apply Nat.eqb_neq in Hx0z. rewrite Hx0z. exact H0.
    + exact IH.
Qed.

(* Extending the graph at a fresh location z leaves every OTHER          *)
(* location's correspondence intact -- including locations that alias   *)
(* THROUGH a chain, since CorrE only ever follows z if some location's   *)
(* own content literally points at z, which cannot happen while z is     *)
(* still fresh (G z = None).                                             *)
Lemma CorrE_other :
  forall G x b, CorrE G x b -> forall z g, x <> z -> G z = None -> CorrE (hupd G z g) x b.
Proof.
  intros G x b H.
  induction H as
    [ x0 c args H0
    | x0 H0
    | x0 f args H0
    | x0 y0 w H0
    | x0 w H0
    | x0 H0
    | x0 y0 H0
    | x0 y0 z0 c0' args0' H0 Hcl0 Hz0
    ]; intros z g Hxz Hz.
  - eapply CorrE_Con. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_Free. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_Fun. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_Choice. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_VarThunk. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_Bot. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - eapply CorrE_FwdHere. rewrite (hupd_neq G z g x0 Hxz). exact H0.
  - (* FwdAchievedCon : z0 (the achieved target) is EXISTING (G z0=Con..),
       z is fresh (G z=None), so z0<>z; ContractLoc_extend carries the
       chase across, and hupd_neq carries the achieved fact across too. *)
    assert (Hz0z : z0 <> z) by (intro Heq; subst z0; congruence).
    eapply CorrE_FwdAchievedCon.
    + rewrite (hupd_neq G z g x0 Hxz). exact H0.
    + exact (ContractLoc_extend G z g Hz y0 z0 Hcl0).
    + rewrite (hupd_neq G z g z0 Hz0z). exact Hz0.
Qed.

(* Extending both heaps at a common fresh location with corresponding   *)
(* content preserves heap correspondence.                                *)
Lemma HeapCorr_extend :
  forall G Gam x e,
    HeapCorr G Gam -> G x = None ->
    HeapCorr (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
Proof.
  intros G Gam x e HGC Hx z.
  unfold hupd.
  destruct (Nat.eqb z x) eqn:Ezx.
  - apply Nat.eqb_eq in Ezx; subst z.
    eexists. split; [reflexivity | ].
    assert (Hself : (fun y => if Nat.eqb y x then Some (GExpr e) else G y) x = Some (GExpr e))
      by (rewrite Nat.eqb_refl; reflexivity).
    destruct e; simpl in Hself; simpl.
    + eapply CorrE_VarThunk; exact Hself.
    + eapply CorrE_Bot; exact Hself.
    + eapply CorrE_Free; exact Hself.
    + eapply CorrE_Choice; exact Hself.
    + eapply CorrE_Fun; exact Hself.
    + eapply CorrE_Con; exact Hself.
  - apply Nat.eqb_neq in Ezx.
    specialize (HGC z).
    destruct (G z) eqn:Gz.
    + destruct HGC as [b [Hb HCE]].
      exists b. split; [exact Hb | ].
      eapply CorrE_other; [exact HCE | exact Ezx | exact Hx].
    + exact HGC.
Qed.

(* Needed below for CorrE_FwdAchievedCon/FwdAchievedFree: a ContractLoc      *)
(* chain whose FINAL target is not the location being updated survives       *)
(* updating that (necessarily EXISTING, Free-shaped) location's content to    *)
(* a constructor.  x itself can never be an intermediate hop either -- Free    *)
(* is non-forwarding, so ContractLoc could only reach x as its OWN endpoint,    *)
(* which the hypothesis `ztarget <> x` already excludes.                        *)
Lemma ContractLoc_update_free_other :
  forall G y0 ztarget, ContractLoc G y0 ztarget ->
  forall x c args, G x = Some (GExpr EFree) -> ztarget <> x ->
  ContractLoc (hupd G x (GExpr (ECon c args))) y0 ztarget.
Proof.
  intros G y0 ztarget H.
  induction H as [x0 e0 H0 | x0 y1 z0 H0 Hcl0 IH]; intros x c args Hxfree Hzx.
  - eapply CL_Here. rewrite (hupd_neq G x (GExpr (ECon c args)) x0 Hzx). exact H0.
  - assert (Hx0x : x0 <> x).
    { intro Heq; subst x0. rewrite Hxfree in H0. discriminate H0. }
    eapply CL_Fwd.
    + rewrite (hupd_neq G x (GExpr (ECon c args)) x0 Hx0x). exact H0.
    + apply IH; [exact Hxfree | exact Hzx].
Qed.

(* Updating an EXISTING `free` location's content to a constructor       *)
(* preserves every OTHER location's correspondence.  This is exactly    *)
(* the situation the eager/deterministic CorrE broke on: something else *)
(* could already be aliased to x (via a FWD chain).  Under the          *)
(* multi-valued CorrE this is fine -- x is non-forwarded both before    *)
(* and after (EFree, then ECon), so nothing can ever chain THROUGH x    *)
(* (only terminate there), and the alias witness `EVar x` a chain would *)
(* use to stop at x never actually inspects x's content, so it survives *)
(* the update unchanged.                                                 *)
Lemma CorrE_update_free_other :
  forall G z b, CorrE G z b ->
  forall x c args, G x = Some (GExpr EFree) -> z <> x ->
  CorrE (hupd G x (GExpr (ECon c args))) z b.
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
  intros x c args Hxfree Hzx.
  - eapply CorrE_Con.    rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_Free.   rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_Fun.    rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_Choice. rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_VarThunk. rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_Bot.    rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - eapply CorrE_FwdHere. rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
  - (* FwdAchievedCon : the achieved target z1 (G z1=Con c1 args1) can't be x
       (x is Free), so both the chase and the achieved fact survive the update. *)
    assert (Hz1x : z1 <> x) by (intro Heq; subst z1; congruence).
    eapply CorrE_FwdAchievedCon.
    + rewrite (hupd_neq G x (GExpr (ECon c args)) z0 Hzx). exact H0.
    + exact (ContractLoc_update_free_other G y0 z1 Hcl0 x c args Hxfree Hz1x).
    + rewrite (hupd_neq G x (GExpr (ECon c args)) z1 Hz1x). exact Hz1.
Qed.


(* HISTORICAL NOTE (superseded -- kept for the write-up).                 *)
(*                                                                          *)
(* This file used to contain a theorem `HeapCorr_update_not_general`,       *)
(* proving HeapCorr is NOT preserved by an arbitrary graph mutation.  Its   *)
(* witness: z FWD-points at x; x currently holds Bot; z's own Gam-content   *)
(* is ALSO `EBot` -- a bare, literal COPY of x's raw (non-terminal, in the  *)
(* sense of "not Con/Free") content, justified via the OLD, fully general   *)
(* `CorrE_FwdChase : G x=GFwd y -> CorrE G y b -> CorrE G x b` (b arbitrary, *)
(* not restricted to an ACHIEVED shape).  Mutating x's content (Bot -> a    *)
(* constructor) left z's witness stale, breaking HeapCorr.  This was cited  *)
(* as the reason G_CaseFun's own step (updating an EFun-thunk location)     *)
(* was NOT the easy, purely-structural step it looked like.                 *)
(*                                                                          *)
(* THE FIX: CorrE_FwdChase has been replaced (see the CorrE definition      *)
(* above -- now CorrE_FwdAchievedCon / CorrE_FwdAchievedFree) so that a      *)
(* forwarding location's witness can ONLY be the direct 1-hop alias         *)
(* (`EVar y`, CorrE_FwdHere) or a value ALREADY ACHIEVED at the canonical    *)
(* (ContractLoc-reached) target -- a genuine constructor, or a genuine       *)
(* free-variable self-loop.  `Bot` is neither, so `Gam z = EBot` is no        *)
(* longer a valid witness for a forwarding z at all -- this exact             *)
(* counterexample's FIRST hypothesis (`HeapCorr G Gam`) can no longer even    *)
(* be established, so the theorem's witness does not exist anymore.          *)
(* Whether some OTHER witness still breaks a fully general "any GExpr to      *)
(* any GExpr" update is now open again under the tightened invariant --       *)
(* the theorem is removed rather than re-proved for a different witness,      *)
(* since the file's remaining use of this fact only ever needs the             *)
(* restricted "EFree source" case (HeapCorr_update_free, below), which          *)
(* still holds.                                                                *)

Lemma HeapCorr_update_free :
  forall G Gam x c args,
    HeapCorr G Gam -> G x = Some (GExpr EFree) ->
    HeapCorr (hupd G x (GExpr (ECon c args))) (hupd Gam x (BExpr (ECon c args))).
Proof.
  intros G Gam x c args HGC Hx z.
  destruct (Nat.eqb z x) eqn:Ezx.
  - apply Nat.eqb_eq in Ezx; subst z.
    assert (Hgself : hupd G x (GExpr (ECon c args)) x = Some (GExpr (ECon c args))).
    { unfold hupd. rewrite Nat.eqb_refl. reflexivity. }
    assert (Hgamself : hupd Gam x (BExpr (ECon c args)) x = Some (BExpr (ECon c args))).
    { unfold hupd. rewrite Nat.eqb_refl. reflexivity. }
    rewrite Hgself. eexists. split; [exact Hgamself | ].
    eapply CorrE_Con. exact Hgself.
  - apply Nat.eqb_neq in Ezx.
    rewrite (hupd_neq G x (GExpr (ECon c args)) z Ezx).
    specialize (HGC z).
    destruct (G z) eqn:Gz.
    + destruct HGC as [b [Hb HCE]].
      exists b. split.
      * rewrite (hupd_neq Gam x (BExpr (ECon c args)) z Ezx). exact Hb.
      * eapply CorrE_update_free_other; [exact HCE | exact Hx | exact Ezx].
    + rewrite (hupd_neq Gam x (BExpr (ECon c args)) z Ezx). exact HGC.
Qed.

Lemma hupd_list_notin :
  forall {A} (xs : list var) (vs : list A) (h : heap A) w, ~ In w xs -> hupd_list h xs vs w = h w.
Proof.
  induction xs as [| x xs' IHxs]; intros vs h w Hnin; destruct vs as [| v vs']; simpl; try reflexivity.
  rewrite hupd_neq.
  - apply IHxs. intro Hin; apply Hnin; right; exact Hin.
  - intro Heq; apply Hnin; left; congruence.
Qed.

(* Pulling a SINGLE update at a location outside the list `xs` out to      *)
(* either side of a `hupd_list` over `xs` gives the same heap.  Needed to  *)
(* re-order "install x's shortcut memo" against "narrow the fresh guess    *)
(* variables", which touch disjoint locations by freshness.                *)
Lemma hupd_list_hupd_swap :
  forall {A} (xs : list var) (vs : list A) (h : heap A) a va, ~ In a xs ->
  forall w, hupd_list (hupd h a va) xs vs w = hupd (hupd_list h xs vs) a va w.
Proof.
  induction xs as [| x xs' IHxs]; intros vs h a va Hnin w; destruct vs as [| v vs']; simpl; try reflexivity.
  assert (Hax : a <> x) by (intro Heq; apply Hnin; left; congruence).
  assert (Hnin' : ~ In a xs') by (intro Hin; apply Hnin; right; exact Hin).
  destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
  - subst w.
    unfold hupd at 1; rewrite Nat.eqb_refl.
    rewrite (hupd_neq (hupd (hupd_list h xs' vs') x v) a va x (not_eq_sym Hax)).
    unfold hupd; rewrite Nat.eqb_refl. reflexivity.
  - assert (Hlhs : hupd (hupd_list (hupd h a va) xs' vs') x v w = hupd_list (hupd h a va) xs' vs' w)
      by (apply hupd_neq; exact Hnewx).
    rewrite Hlhs, (IHxs vs' h a va Hnin' w).
    destruct (Nat.eq_dec w a) as [Heqwa | Hnewa].
    + subst w. unfold hupd; rewrite Nat.eqb_refl. reflexivity.
    + rewrite (hupd_neq (hupd_list h xs' vs') a va w Hnewa).
      symmetry. rewrite (hupd_neq (hupd (hupd_list h xs' vs') x v) a va w Hnewa).
      rewrite (hupd_neq (hupd_list h xs' vs') x v w Hnewx). reflexivity.
Qed.

(* Extending both heaps at a LIST of fresh, mutually distinct locations, *)
(* all freshly bound to `free` (self-loops on the natural-semantics      *)
(* side), preserves heap correspondence.  Used for narrowing a free      *)
(* variable to a constructor pattern (Case-ConFree / N_Guess), whose     *)
(* new pattern variables are exactly such a fresh list.                  *)
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

(* ------------------------------------------------------------------ *)
(* 6b. Confluence: NEval doesn't care WHICH valid representation of G   *)
(*     a heap uses -- any two heaps corresponding to the same graph     *)
(*     evaluate any expression to the same value.  This is exactly the  *)
(*     "evaluation is invariant under heap-representation changes"      *)
(*     property identified as the true root cause behind                *)
(*     NEval_fwd_transfer / NEval_choice_transfer / NEval_fun_transfer. *)
(* ------------------------------------------------------------------ *)

(* NEval_var_cycle_stuck itself is a general, CorrE-independent fact      *)
(* (kept below, unchanged): if Gam has a genuine 2-cycle of EVar aliases  *)
(* (a -> b -> a), forcing EITHER one never terminates -- no finite NEval  *)
(* derivation exists at all.  It used to feed a theorem                   *)
(* `NEval_confluence_unrestricted_is_false`, since removed; see the        *)
(* HISTORICAL NOTE just below it for why.                                 *)
Lemma NEval_var_cycle_stuck :
  forall P Gam a b, Gam a = Some (BExpr (EVar b)) -> Gam b = Some (BExpr (EVar a)) -> a <> b ->
  forall e, e = BExpr (EVar a) \/ e = BExpr (EVar b) ->
  forall F Gam' v', NEval P F Gam e Gam' v' -> False.
Proof.
  intros P Gam a b Ha Hb Hab e He F Gam' v' H. revert He.
  induction H; intro He; try (exfalso; destruct He as [He | He]; discriminate).
  - (* N_VarCons: e = BExpr (EVar x), Gam x = Some (BExpr (ECon c args)) *)
    destruct He as [He | He]; injection He as He; subst x; congruence.
  - (* N_VarSelf: Gam x = Some (BExpr (EVar x)) *)
    destruct He as [He | He]; injection He as He; subst x; congruence.
  - (* N_VarFree *)
    destruct He as [He | He]; injection He as He; subst x; congruence.
  - (* N_VarExp: recurse *)
    destruct He as [He | He]; injection He as He; subst x.
    + apply IHNEval; [exact Ha | exact Hb | right; congruence].
    + apply IHNEval; [exact Ha | exact Hb | left; congruence].
Qed.

(* HISTORICAL NOTE (superseded -- kept for the write-up).                 *)
(*                                                                          *)
(* This file used to contain a theorem                                     *)
(* `NEval_confluence_unrestricted_is_false`, disproving "any two Gam's       *)
(* validly corresponding to the same G give the same NEval termination       *)
(* behavior" (confluence with NO side condition).  Its witness: G x=GFwd y,   *)
(* and SEPARATELY (an entirely ordinary pattern) G y=GExpr(EVar x) -- y's      *)
(* own direct, non-forwarding content is literally the expression `EVar x`,    *)
(* i.e. an unforced `let y = x in ...`-style thunk-alias pointing BACK at x.    *)
(* The OLD, fully general `CorrE_FwdChase` could chase FROM x THROUGH y's own   *)
(* VarThunk content, giving x a SECOND valid witness `EVar x` (self-loop) in     *)
(* ADDITION to the direct alias `EVar y` (FwdHere) -- and a Gam choosing the      *)
(* first witness (`EVar x`) finishes immediately (Nat-VarSelf), while a Gam       *)
(* choosing `EVar y` recurses into forcing y, whose content is `EVar x`,           *)
(* landing back on the exact same judgment -- a genuine, non-terminating           *)
(* NEval derivation, formally witnessed via `NEval_var_cycle_stuck` above.           *)
(* Two heaps both validly corresponding to the same G could therefore have           *)
(* GENUINELY DIFFERENT TERMINATION BEHAVIOR on the same expression.                    *)
(*                                                                          *)
(* THE FIX: the same CorrE_FwdChase -> CorrE_FwdAchievedCon/FwdAchievedFree     *)
(* restriction described above (HeapCorr_update_not_general's historical note)   *)
(* also eliminates THIS counterexample's construction: chasing through a raw,    *)
(* non-achieved VarThunk (`EVar x`) is no longer permitted at all -- a forwarding *)
(* location's ONLY witnesses are now the direct 1-hop alias, or an ACHIEVED       *)
(* (Con / genuine free-self-loop) value reached via ContractLoc, and `EVar x`      *)
(* here is neither (x is itself a GFwd node, not Free).  So `HC1`'s own first       *)
(* hypothesis can no longer be established, and the theorem is removed rather       *)
(* than re-proved against a different witness.  (The two follow-up facts below,     *)
(* `GEval_case_chase_not_var_thunk` and                                             *)
(* `confluence_counterexample_graph_unreachable_by_case`, are independent of         *)
(* CorrE entirely -- they show this exact cyclic graph shape was already            *)
(* unreachable from any COMPLETE GEval derivation in the first place -- and are      *)
(* kept unchanged below.)                                                           *)

(* Is the counterexample graph above actually REACHABLE from a real,     *)
(* COMPLETE GEval derivation, or only from a stuck/non-existent proof     *)
(* search?  Answer: unreachable.  GEval's six BCase rules (CaseBot,       *)
(* CaseFwd, CaseFun, CaseChoice, CaseCon, CaseConFree) between them        *)
(* cover every content shape a scrutinee's *immediate* content may have   *)
(* EXCEPT `GExpr (EVar _)` -- there is no G_CaseVar rule at all.  So the  *)
(* moment a Case-forcing chain (following GFwd hops via CaseFwd) would    *)
(* land on a location whose content is a bare, unforced variable alias,   *)
(* the derivation has NO further rule to apply and simply does not        *)
(* exist as a Coq proof term.  This is exactly the shape of our           *)
(* counterexample graph (`G y = GExpr (EVar x)`, sitting behind a GFwd    *)
(* from x): it can only ever be encountered by an ATTEMPTED case-forcing  *)
(* chain that fails to complete, never by one that succeeds.  Since       *)
(* Theorem 2's proof always inducts on an already-COMPLETE GEval          *)
(* derivation, this is precisely the side condition confluence needs:     *)
(* restricted to graphs/locations a genuine BCase derivation actually     *)
(* reaches, the pathological alias-cycle this section's counterexample    *)
(* relies on cannot occur.                                                *)
Lemma GEval_case_chase_not_var_thunk :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v ->
  forall y, ContractLoc G x y -> forall z, G y <> Some (GExpr (EVar z)).
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H; intros x0 brs0 He; try discriminate He.
  - (* G_CaseBot: G x0 = Some (GExpr EBot) *)
    injection He as He1 He2; subst x0 brs0.
    intros y Hcl z Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hrec]; subst.
    + congruence.
    + congruence.
  - (* G_CaseFwd: G x0 = Some (GFwd y0), recurse on (BCase y0 brs0) *)
    injection He as He1 He2; subst x0 brs0.
    rename y into y0.
    intros y Hcl z Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hrec]; subst.
    + congruence.
    + assert (y1 = y0) by congruence; subst y1.
      exact (IHGEval y0 brs eq_refl y Hrec z Hz).
  - (* G_CaseFun: G x0 = Some (GExpr (EFun f args)) *)
    injection He as He1 He2; subst x0 brs0.
    intros w Hcl z Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hrec]; subst; congruence.
  - (* G_CaseChoice: G x0 = Some (GExpr (EChoice y z)) *)
    injection He as He1 He2; subst x0 brs0.
    intros w Hcl z0 Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1' z1' Hx1 Hrec]; subst; congruence.
  - (* G_CaseCon: G x0 = Some (GExpr (ECon c zs)) *)
    injection He as He1 He2; subst x0 brs0.
    intros w Hcl z Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hrec]; subst; congruence.
  - (* G_CaseConFree: G x0 = Some (GExpr EFree) *)
    injection He as He1 He2; subst x0 brs0.
    intros w Hcl z Hz.
    inversion Hcl as [x1 e1 Hx1 | x1 y1 z1 Hx1 Hrec]; subst; congruence.
Qed.

(* Concretely: the exact 2-node graph used above to disprove             *)
(* unrestricted confluence admits NO complete BCase derivation at x at    *)
(* all (let alone one exhibiting the bad heap-choice ambiguity) -- the    *)
(* chase gets stuck at y on its very first hop.                          *)
Theorem confluence_counterexample_graph_unreachable_by_case :
  forall P brs G' v,
  ~ GEval P (fun w : var => if Nat.eqb w 0 then Some (GFwd 1)
                             else if Nat.eqb w 1 then Some (GExpr (EVar 0))
                             else None)
           (BCase 0 brs) G' v.
Proof.
  intros P brs G' v.
  pose (x := 0). pose (y := 1).
  pose (G := fun w : var => if Nat.eqb w x then Some (GFwd y)
                             else if Nat.eqb w y then Some (GExpr (EVar x))
                             else None).
  intro Hbad.
  assert (HGy : G y = Some (GExpr (EVar x))) by (unfold G, x, y; reflexivity).
  assert (HGx : G x = Some (GFwd y)) by (unfold G, x, y; reflexivity).
  assert (Hcl : ContractLoc G x y) by (eapply CL_Fwd; [exact HGx | eapply CL_Here; exact HGy]).
  exact (GEval_case_chase_not_var_thunk P G x brs G' v Hbad y Hcl x HGy).
Qed.

(* A complete Case-forcing derivation always has SOME canonical target    *)
(* -- the GFwd chain it follows (via G_CaseFwd) can never cycle, since a  *)
(* GEval derivation is, by construction, a finite Coq proof term, and     *)
(* G_CaseFwd's own recursion strictly follows G's single, deterministic   *)
(* forward pointer at each step.                                          *)
Lemma GEval_case_gives_ContractLoc :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v ->
  exists y, ContractLoc G x y.
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H; intros x0 brs0 He; try discriminate He.
  - (* G_CaseBot *) injection He as He1 He2; subst x0 brs0.
    exists x. eapply CL_Here; exact H.
  - (* G_CaseFwd *) injection He as He1 He2; subst x0 brs0.
    destruct (IHGEval y brs eq_refl) as [y0 Hcl].
    exists y0. eapply CL_Fwd; [exact H | exact Hcl].
  - (* G_CaseFun *) injection He as He1 He2; subst x0 brs0.
    exists x. eapply CL_Here; exact H.
  - (* G_CaseChoice *) injection He as He1 He2; subst x0 brs0.
    exists x. eapply CL_Here; exact H.
  - (* G_CaseCon *) injection He as He1 He2; subst x0 brs0.
    exists x. eapply CL_Here; exact H.
  - (* G_CaseConFree *) injection He as He1 He2; subst x0 brs0.
    exists x. eapply CL_Here; exact H.
Qed.

(* THE SELF-LOOP REACHABILITY LEMMA (scoped last turn as the single       *)
(* most important thing to check before attempting the NEval-to-GEval     *)
(* converse theorem).  It asks: if a heap slot's CorrE witness happens    *)
(* to be a self-loop `EVar z`, and z is genuinely, completely             *)
(* Case-forced by GEval, must z be genuinely free -- or could the         *)
(* self-loop instead be an artifact of a CorrE_VarThunk/FwdChase content  *)
(* cycle (the same ambiguity that broke the first CorrE_selfvar_functional*)
(* attempt, and that powers NEval_confluence_unrestricted_is_false)?      *)
(*                                                                        *)
(* Answer: genuinely free.  ONCE a complete Case-forcing derivation for z *)
(* exists, GEval_case_chase_not_var_thunk rules out the content-cycle     *)
(* reading entirely (no GExpr(EVar _) content can lie along z's chase     *)
(* chain), and ContractLocN_functional rules out the OTHER way a self-    *)
(* referencing witness could arise (an intermediate alias "looping back"  *)
(* to z, which would require two DIFFERENT chase-depths to the same       *)
(* target, impossible since the chase is deterministic).  So the          *)
(* self-loop obstacle scoped last turn is NOT a real obstacle for the     *)
(* converse theorem, PROVIDED z is reached via a genuine, completed       *)
(* Case-forcing derivation -- exactly the situation NEval's own N_VarSelf *)
(* and N_Guess cases are in when this fact gets used.                     *)
Theorem CorrE_selfloop_means_free :
  forall P G z brs G' v, GEval P G (BCase z brs) G' v ->
  CorrE G z (BExpr (EVar z)) ->
  G z = Some (GExpr EFree).
Proof.
  intros P G z brs G' v HGE HCE.
  destruct (GEval_case_gives_ContractLoc P G z brs G' v HGE) as [y Hcl].
  destruct (ContractLoc_to_N G z y Hcl) as [n Hcln].
  assert (Hyc : exists yc, G y = Some (GExpr yc)).
  { clear Hcln HCE HGE. induction Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH].
    - exists e0; exact H0.
    - exact IH. }
  destruct Hyc as [yc Hy].
  destruct (CorrE_progress_N G z (BExpr (EVar z)) HCE n y yc Hcln Hy)
    as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
  - (* b = let_content y yc = BExpr (EVar z) *)
    destruct yc as [z0 | | | y0 w0 | f0 args0 | c0 args0];
      simpl in Heq; try discriminate Heq.
    + (* yc = EVar z0 : G y = GExpr (EVar z0), ruled out by the chase lemma *)
      injection Heq as Heq; subst z0.
      exfalso. exact (GEval_case_chase_not_var_thunk P G z brs G' v HGE y Hcl z Hy).
    + (* yc = EFree : let_content y EFree = BExpr (EVar y), so y = z *)
      injection Heq as Heq; subst y.
      exact Hy.
  - (* b = BExpr (EVar y1), m < n, ContractLocN G m y1 y -- forces y1 = z *)
    injection Heq as Heq; subst y1.
    exfalso.
    destruct (ContractLocN_functional G m z y Hcln1 n y Hcln) as [Hmn _].
    lia.
Qed.
(* natural, minimal restriction to add rather than a symptom of a deeper   *)
(* problem -- but it does need to be added explicitly, since HeapCorr's    *)
(* own definition is purely pointwise and has no way to rule it out.       *)
Definition WellFoundedFwd (G : Graph) : Prop :=
  forall w y, G w = Some (GFwd y) -> exists z, ContractLoc G w z.

Lemma CorrE_selfloop_to_CorrVTerm :
  forall G, WellFoundedFwd G ->
  forall z, CorrE G z (BExpr (EVar z)) -> CorrVTerm G z (BExpr (EVar z)).
Proof.
  intros G HWF z HCE.
  assert (Hcl : exists y, ContractLoc G z y).
  { destruct (G z) as [gc | ] eqn:EGz.
    - destruct gc as [e | y].
      + exists z. eapply CL_Here; exact EGz.
      + eapply HWF; exact EGz.
    - exfalso. exact (CorrE_dom G z (BExpr (EVar z)) HCE EGz). }
  destruct Hcl as [y Hcl].
  destruct (ContractLoc_to_N G z y Hcl) as [n Hcln].
  assert (Hyc : exists yc, G y = Some (GExpr yc)).
  { clear Hcln HCE. induction Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH].
    - exists e0; exact H0.
    - exact IH. }
  destruct Hyc as [yc Hy].
  destruct (CorrE_progress_N G z (BExpr (EVar z)) HCE n y yc Hcln Hy)
    as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
  - destruct yc as [z0 | | | y0 w0 | f0 args0 | c0 args0];
      simpl in Heq; try discriminate Heq.
    + (* yc = EVar z0 : G y = GExpr (EVar z), CVT_Var match *)
      injection Heq as Heq; subst z0.
      eapply CVT_Var; [exact Hcl | exact Hy].
    + (* yc = EFree : let_content y EFree = BExpr (EVar y), so y = z *)
      injection Heq as Heq; subst y.
      eapply CVT_Free; [exact Hcl | exact Hy].
  - injection Heq as Heq; subst y1.
    exfalso.
    destruct (ContractLocN_functional G m z y Hcln1 n y Hcln) as [Hmn _].
    lia.
Qed.

(* Two small facts needed for the converse theorem's N_Let/N_Guess cases: *)
(* a heap slot HeapCorr marks as free (None) on the natural-semantics      *)
(* side is free on the graph side too, and no HeapCorr'd heap ever holds   *)
(* a bare (non-self-looped) `EFree` -- CorrE has no constructor that       *)
(* produces that witness, at any depth of FwdChase.                       *)
Lemma HeapCorr_Gam_None_G_None :
  forall G Gam x, HeapCorr G Gam -> Gam x = None -> G x = None.
Proof.
  intros G Gam x HGC HGamx.
  specialize (HGC x). destruct (G x) as [gc | ] eqn:EG.
  - destruct HGC as [b [Hb _]]. congruence.
  - reflexivity.
Qed.

Lemma CorrE_never_bare_free : forall G x b, CorrE G x b -> b <> BExpr EFree.
Proof.
  intros G x b H. induction H; discriminate.
Qed.

(* Every CorrE witness is BExpr-shaped, even through arbitrarily many       *)
(* FwdChase hops -- CorrE never witnesses a BLet or BCase.  `inversion`     *)
(* alone cannot see this THROUGH FwdChase's own generic recursive premise   *)
(* (its witness "b" isn't syntactically constrained at that one step), so   *)
(* this needs the full induction.                                          *)
Lemma CorrE_witness_is_BExpr : forall G x b, CorrE G x b -> exists e, b = BExpr e.
Proof.
  intros G x b H. induction H;
    try (eexists; reflexivity); exact IHCorrE.
Qed.

(* Every CorrVTerm witness is exactly `let_content` of the canonical        *)
(* target's own direct content -- a clean characterization letting a       *)
(* CorrVTerm fact at one location be "replayed" at any location that        *)
(* shares the same canonical target (e.g. one location genuinely           *)
(* forwarding to another), without re-deriving it from scratch.             *)
Lemma CorrVTerm_inv :
  forall G x b, CorrVTerm G x b ->
  exists y yc, ContractLoc G x y /\ G y = Some (GExpr yc) /\ b = let_content y yc.
Proof.
  intros G x b H; destruct H.
  - exists y, (ECon c args); auto.
  - exists y, EFree; auto.
  - exists y, (EFun f args); auto.
  - exists y, (EChoice y1 y2); auto.
  - exists y, (EVar z); auto.
  - exists y, EBot; auto.
Qed.

(* REMOVED (unused elsewhere; no longer true in general): CorrVTerm_to_CorrE
   used to claim every CorrVTerm witness (which, unlike CorrE now, still
   allows contracting to Fun/Choice/VarThunk/Bot content) was also a valid
   CorrE witness.  That relied on the OLD, unrestricted CorrE_FwdChase and
   is exactly the same over-generalization the CorrE definition's own
   comment (and the two removed counterexample theorems above) documents --
   a forwarding location's CorrE witness can no longer be an arbitrary
   non-achieved copy.  It had no callers, so it is simply dropped rather
   than restricted. *)

(* Memoizing a location to a value that is ALREADY a valid CorrE witness    *)
(* for it preserves HeapCorr everywhere -- unlike HeapCorr_update_not_      *)
(* general's counterexample (Section 6), there is no staleness risk here,   *)
(* because we are not changing what the GRAPH says at all, only refining    *)
(* which of CorrE's own multiple valid representations this ONE slot uses.  *)
Lemma HeapCorr_update_consistent :
  forall G Gam z b, HeapCorr G Gam -> CorrE G z b -> HeapCorr G (hupd Gam z b).
Proof.
  intros G Gam z b HGC HCEz w.
  unfold hupd. destruct (Nat.eqb w z) eqn:Ew.
  - apply Nat.eqb_eq in Ew; subst w.
    specialize (HGC z). destruct (G z) as [gc | ] eqn:EGz.
    + exists b. split; [reflexivity | exact HCEz].
    + exfalso. exact (CorrE_dom G z b HCEz EGz).
  - exact (HGC w).
Qed.

(* Whenever an NEval derivation's OWN final result is a self-loop `EVar    *)
(* z'`, that location's slot in the RESULT heap holds exactly that self-   *)
(* loop -- true regardless of how deep the derivation is, since every rule *)
(* either passes the recursive result straight through (N_Fun/N_Let/N_Or/  *)
(* N_Select/N_Guess) or is itself the base case producing the self-loop     *)
(* directly (N_VarSelf/N_VarFree/N_VarExp).  Needed to know a Case-Guess's  *)
(* own freshly-narrowed location z' cannot coincide with any location that *)
(* already, separately, holds a genuine constructor.                       *)
Lemma NEval_selfloop_result_persists :
  forall P F G e G' z', NEval P F G e G' (BExpr (EVar z')) -> G' z' = Some (BExpr (EVar z')).
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
    | F0 G0 x1 y1 G1 v i Hi Hrec IH
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
(* A constructor-shaped location is TERMINAL FOREVER: no NEval rule ever    *)
(* rewrites a slot that already holds a constructor (N_VarExp's own side    *)
(* conditions explicitly exclude ECon-shaped content as something it        *)
(* recurses through; every OTHER rule either does not touch the heap at     *)
(* all, or only ever writes to a FRESH/currently-different slot).  This is  *)
(* the piece that lets a Con-shaped memo be threaded safely through a       *)
(* MULTI-step derivation (e.g. Nat-Select's own two premises) without       *)
(* needing to track it explicitly through every intermediate heap.          *)
Lemma NEval_con_persists :
  forall P F Gam e Gam' v, NEval P F Gam e Gam' v ->
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
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
      by exact (NEval_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
    assert (Hwz' : w <> z').
    { intro Heq; subst w. rewrite Hw1 in HG1z'. discriminate HG1z'. }
    assert (Hw2 : hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws
                    (map (fun w0 => BExpr (EVar w0)) ws) w = Some (BExpr (ECon c cargs))).
    { rewrite hupd_list_notin by exact Hwnotin.
      rewrite hupd_neq by exact Hwz'.
      exact Hw1. }
    exact (IH2 w c cargs Hw2).
Qed.
(* The invariant that makes the replay-style arguments' own two-premise   *)
(* (Nat-Select/Nat-Guess) cases tractable: "x is either still the lazy    *)
(* alias EVar y, or has ALREADY been promoted to the achieved constructor *)
(* -- and y itself is always the achieved constructor" is preserved by    *)
(* ANY NEval step.  The only place x's own slot can change AT ALL is via  *)
(* Nat-VarExp forcing x directly, which (since x's only possible content  *)
(* is the alias EVar y, and y is already terminal) can only ever memoize  *)
(* it to the SAME achieved constructor -- never anything else.            *)
Lemma NEval_alias_or_con_persists :
  forall P x y c args, x <> y ->
  forall F Gam e Gam' v, NEval P F Gam e Gam' v ->
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
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
      by exact (NEval_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
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
Lemma ContractLocN_ContractLoc_compose :
  forall G n z w, ContractLocN G n z w -> forall y, ContractLoc G w y -> ContractLoc G z y.
Proof.
  intros G n z w H.
  induction H as [x0 e0 H0 | n0 x0 y0 z0 H0 Hcln0 IH]; intros y Hcl.
  - exact Hcl.
  - eapply CL_Fwd; [exact H0 | apply IH; exact Hcl].
Qed.

(* If z and w share the same canonical target y (e.g. z genuinely           *)
(* forwards, through some number of GFwd hops, toward wherever w's own      *)
(* chase already ends up), ANY CorrVTerm fact already established at w      *)
(* transfers to z directly -- both are just different names for "chase to   *)
(* y, then read off y's own content."                                       *)
Lemma CorrVTerm_compose_same_target :
  forall G z w y, ContractLoc G z y -> ContractLoc G w y ->
  forall b, CorrVTerm G w b -> CorrVTerm G z b.
Proof.
  intros G z w y Hclz Hclw b Hcvt.
  destruct (CorrVTerm_inv G w b Hcvt) as [y0 [yc [Hcl0 [Hy0 Hb]]]].
  subst b.
  destruct (ContractLoc_to_N G w y0 Hcl0) as [n0 Hcln0].
  destruct (ContractLoc_to_N G w y Hclw) as [n1 Hcln1].
  destruct (ContractLocN_functional G n0 w y0 Hcln0 n1 y Hcln1) as [_ Heqy]; subst y0.
  destruct yc as [z0 | | | y1 z1 | f0 args0 | c0 args0]; simpl.
  - eapply CVT_Var; [exact Hclz | exact Hy0].
  - eapply CVT_Bot; [exact Hclz | exact Hy0].
  - eapply CVT_Free; [exact Hclz | exact Hy0].
  - eapply CVT_Choice; [exact Hclz | exact Hy0].
  - eapply CVT_Fun; [exact Hclz | exact Hy0].
  - eapply CVT_Con; [exact Hclz | exact Hy0].
Qed.

(* Splits an alias witness `CorrE G z (EVar w)` into the ONLY two ways it   *)
(* can arise: EITHER z and w share a canonical target (z genuinely, through *)
(* 0 or more GFwd hops, forwards toward the SAME place w's own chase ends   *)
(* up) -- in which case CorrVTerm_compose_same_target applies cleanly --    *)
(* OR z's own canonical target's DIRECT content is `EVar w` (an unforced,   *)
(* content-level thunk, CorrE_VarThunk) -- the genuinely irreducible case,  *)
(* see NEval_realizes_GEval_is_false_3.                                     *)
Lemma CorrE_alias_case_split :
  forall G, WellFoundedFwd G ->
  forall z w, CorrE G z (BExpr (EVar w)) ->
  (exists y, ContractLoc G z y /\ ContractLoc G w y) \/
  (exists y, ContractLoc G z y /\ G y = Some (GExpr (EVar w))).
Proof.
  intros G HWF z w HCE.
  assert (Hcl : exists y, ContractLoc G z y).
  { destruct (G z) as [gc | ] eqn:EGz.
    - destruct gc as [e | y].
      + exists z. eapply CL_Here; exact EGz.
      + eapply HWF; exact EGz.
    - exfalso. exact (CorrE_dom G z (BExpr (EVar w)) HCE EGz). }
  destruct Hcl as [y Hcl].
  destruct (ContractLoc_to_N G z y Hcl) as [n Hcln].
  assert (Hyc : exists yc, G y = Some (GExpr yc)).
  { clear Hcln HCE. induction Hcl as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH].
    - exists e0; exact H0.
    - exact IH. }
  destruct Hyc as [yc Hy].
  destruct (CorrE_progress_N G z (BExpr (EVar w)) HCE n y yc Hcln Hy)
    as [Heq | [m [y1 [Hm [Heq Hcln1]]]]].
  - destruct yc as [w0 | | | y0 z2 | f0 args0 | c0 args0]; simpl in Heq; try discriminate Heq.
    + injection Heq as Heq; subst w0.
      right. exists y. split; [exact Hcl | exact Hy].
    + injection Heq as Heq; subst y.
      left. exists w. split; [exact Hcl | eapply CL_Here; exact Hy].
  - injection Heq as Heq; subst y1.
    left. exists y. split; [exact Hcl | exact (ContractLocN_to_ContractLoc G m w y Hcln1)].
Qed.

Lemma HeapCorr_never_bare_free :
  forall G Gam x, HeapCorr G Gam -> Gam x <> Some (BExpr EFree).
Proof.
  intros G Gam x HGC Hcontra.
  specialize (HGC x). destruct (G x) as [gc | ] eqn:EG.
  - destruct HGC as [b [Hb HCE]]. rewrite Hb in Hcontra.
    injection Hcontra as Hcontra; subst b.
    exact (CorrE_never_bare_free G x (BExpr EFree) HCE eq_refl).
  - rewrite HGC in Hcontra. discriminate.
Qed.

Lemma HeapCorr_Gam_CorrE :
  forall G Gam z b, HeapCorr G Gam -> Gam z = Some b -> CorrE G z b.
Proof.
  intros G Gam z b HGam Hz.
  specialize (HGam z). destruct (G z) as [gc | ] eqn:EGz.
  - destruct HGam as [b' [Hb' HCE]]. rewrite Hz in Hb'. injection Hb' as Hb'; subst b'. exact HCE.
  - rewrite Hz in HGam. discriminate.
Qed.

(* WellFoundedFwd survives extending G at a FRESH location: a fresh,      *)
(* GExpr-shaped slot cannot be part of any EXISTING forward chain (it     *)
(* wasn't even defined before), so no existing chain's chase changes.     *)
Lemma WellFoundedFwd_extend :
  forall G z e0, WellFoundedFwd G -> G z = None -> WellFoundedFwd (hupd G z (GExpr e0)).
Proof.
  intros G z e0 HWF Hz w y Hwy.
  destruct (Nat.eq_dec w z) as [Heq | Hne].
  - subst w. unfold hupd in Hwy. rewrite Nat.eqb_refl in Hwy. discriminate Hwy.
  - assert (Hw : G w = Some (GFwd y)).
    { rewrite <- Hwy. unfold hupd. apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity. }
    destruct (HWF w y Hw) as [target Hcl].
    exists target. exact (ContractLoc_extend G z (GExpr e0) Hz w target Hcl).
Qed.

(* Toward a genuinely restricted confluence fact usable by                *)
(* NEval_fwd_transfer: the ONE piece that turned out tractable.  If x's   *)
(* content is the lazy alias `EVar y`, and y's OWN content is ALREADY     *)
(* terminal (a constructor, or a self-loop -- i.e. y needs no FURTHER     *)
(* forcing), then "pre-installing" the SAME memo at x that forcing x      *)
(* would lazily compute anyway changes nothing: ANY existing NEval        *)
(* derivation over the un-memoized heap replays, UNCHANGED in shape,      *)
(* over the memoized one, reaching the identical value.  This is much    *)
(* narrower than general confluence -- it is not about two independently  *)
(* CHOSEN CorrE witnesses, but about one heap and a strictly-more-eager    *)
(* version of the exact same heap -- and that narrowness is exactly what   *)
(* makes it provable where general confluence is not: this update can      *)
(* never uncover the FwdChase-into-a-cycle pathology, because y's content  *)
(* is required to ALREADY be terminal, not itself an unresolved alias.     *)
Lemma hupd_list_pointwise :
  forall {A} (xs : list var) (vs : list A) (h1 h2 : heap A),
    (forall w, h1 w = h2 w) ->
    forall w, hupd_list h1 xs vs w = hupd_list h2 xs vs w.
Proof.
  intros A xs.
  induction xs as [| x0 xs' IHxs]; intros vs h1 h2 Heq w.
  - simpl. apply Heq.
  - destruct vs as [| v0 vs'].
    + simpl. apply Heq.
    + simpl. unfold hupd. destruct (Nat.eqb w x0); [reflexivity | apply IHxs; exact Heq].
Qed.

(* NEval only ever inspects a heap through pointwise lookups (`G x = ...`   *)
(* premises) -- so a POINTWISE-equal heap (agreeing everywhere, without     *)
(* being the same Coq function) supports the identical derivation shape,   *)
(* landing on a pointwise-equal result heap.  This is the basic tool that   *)
(* lets the two different `hupd`-orderings below be reconciled without      *)
(* resorting to functional extensionality (which this file avoids, to      *)
(* keep every result reported by `Print Assumptions` axiom-free).           *)
Lemma NEval_pointwise_heap :
  forall P F Gam e Gam' v, NEval P F Gam e Gam' v ->
  forall Gam2, (forall w, Gam2 w = Gam w) ->
  exists Gam2', NEval P F Gam2 e Gam2' v /\ (forall w, Gam2' w = Gam' w).
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
    | F0 G z1 z2 G1 v i Hi Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Gam2 Heq.
  - exists Gam2. split; [apply N_VarCons; rewrite Heq; exact Hz | intro w; apply Heq].
  - exists Gam2. split; [apply N_VarSelf; rewrite Heq; exact Hz | intro w; apply Heq].
  - exists (hupd Gam2 z (BExpr (EVar z))). split.
    + apply N_VarFree; rewrite Heq; exact Hz.
    + intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists (hupd G2' z v0). split.
    + eapply N_VarExp;
        [exact HnF | rewrite Heq; exact Hz | exact Hne1 | exact Hne2 | exact Hne3 | exact HNE2].
    + intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq2].
  - exists Gam2. split; [apply N_ValFree | intro w; apply Heq].
  - exists Gam2. split; [apply N_ValCon | intro w; apply Heq].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE2].
    intros w Hw. rewrite Heq. exact (Hfresh w Hw).
  - assert (Heq' : forall w, hupd Gam2 z (let_content z e0) w = hupd G z (let_content z e0) w).
    { intro w; unfold hupd; destruct (Nat.eqb w z); [reflexivity | apply Heq]. }
    destruct (IH (hupd Gam2 z (let_content z e0)) Heq') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    apply N_Let; [rewrite Heq; exact HzFresh | exact HNE2].
  - destruct (IH Gam2 Heq) as [G2' [HNE2 Heq2]].
    exists G2'. split; [eapply N_Or; [exact Hi | exact HNE2] | exact Heq2].
  - destruct (IH1 Gam2 Heq) as [G1' [HNE1 Heq1]].
    assert (Heq1' : forall w, G1' w = G1 w) by exact Heq1.
    destruct (IH2 G1' Heq1') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply N_Select; [exact HNE1 | exact HIn | exact Hlen | exact HNE2].
  - destruct (IH1 Gam2 Heq) as [G1' [HNE1 Heq1]].
    assert (Heq'0 : forall w, hupd G1' z' (BExpr (ECon c1 ws)) w = hupd G1 z' (BExpr (ECon c1 ws)) w).
    { intro w; unfold hupd; destruct (Nat.eqb w z'); [reflexivity | apply Heq1]. }
    assert (Heq' : forall w,
      hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w =
      hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws) w)
      by (apply hupd_list_pointwise; exact Heq'0).
    destruct (IH2 _ Heq') as [G2' [HNE2 Heq2]].
    exists G2'. split; [ | exact Heq2].
    eapply N_Guess; [exact HNE1 | exact Hhd | exact Hlen | exact HND | | exact HNE2].
    intros w Hw. rewrite Heq1. exact (Hfr w Hw).
Qed.
(* The actual replay lemma this whole file was building toward: forcing x  *)
(* directly, when x is (or has already become) an achieved alias/promotion*)
(* of y (which itself holds an achieved constructor), can always REPLAY    *)
(* any NEval derivation that starts from x's heap -- landing on the same   *)
(* value, on a heap that differs from the original result only by having  *)
(* x pre-memoized to the constructor instead of left as a lazy alias.      *)
(* This is exactly the "short-circuit an alias chain changes nothing       *)
(* observable" fact; NEval_fwd_transfer below is the special case with     *)
(* e := BCase y brs.  F (the currently-forcing set) is carried through     *)
(* completely unchanged between the original and the replayed derivation: *)
(* the ONLY place x's own alias ever gets forced (the N_VarExp z=x case)   *)
(* now goes through N_VarCons directly instead in the replay (x is already *)
(* a constructor there), which needs no F side condition at all -- so the  *)
(* replay never needs to push anything onto F that the original didn't.    *)
Lemma NEval_shortcut_alias :
  forall P x y c args, x <> y ->
  forall F Gam e Gam1 v, NEval P F Gam e Gam1 v ->
  (Gam x = Some (BExpr (EVar y)) \/ Gam x = Some (BExpr (ECon c args))) ->
  Gam y = Some (BExpr (ECon c args)) ->
  exists Gam1', NEval P F (hupd Gam x (BExpr (ECon c args))) e Gam1' v /\
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros Hgx Hgy.
  - (* N_VarCons *)
    destruct (Nat.eq_dec z x) as [Heq | Hne].
    + subst z.
      assert (Heqcc : BExpr (ECon c0 args0) = BExpr (ECon c args)).
      { destruct Hgx as [Hgx' | Hgx']; rewrite Hz in Hgx'; [discriminate | congruence]. }
      exists (hupd G x (BExpr (ECon c args))). split.
      * apply N_VarCons. unfold hupd; rewrite Nat.eqb_refl. congruence.
      * intro w; reflexivity.
    + exists (hupd G x (BExpr (ECon c args))). split.
      * apply N_VarCons. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
      * intro w; reflexivity.
  - (* N_VarSelf *)
    destruct (Nat.eq_dec z x) as [Heq | Hne].
    + subst z. destruct Hgx as [Hgx' | Hgx'].
      * rewrite Hz in Hgx'. injection Hgx' as Hgx'. exfalso. apply Hxy. congruence.
      * rewrite Hz in Hgx'. discriminate.
    + exists (hupd G x (BExpr (ECon c args))). split.
      * apply N_VarSelf. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
      * intro w; reflexivity.
  - (* N_VarFree *)
    assert (Hne : z <> x).
    { intro Heq; subst z. destruct Hgx as [Hgx' | Hgx']; rewrite Hz in Hgx'; discriminate. }
    exists (hupd (hupd G x (BExpr (ECon c args))) z (BExpr (EVar z))). split.
    + apply N_VarFree. rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
    + intro w. exact (hupd_comm G x (BExpr (ECon c args)) z (BExpr (EVar z)) (not_eq_sym Hne) w).
  - (* N_VarExp *)
    destruct (Nat.eq_dec z x) as [Heq | Hne].
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
      * apply N_VarCons. unfold hupd; rewrite Nat.eqb_refl; reflexivity.
      * intro w; unfold hupd; destruct (Nat.eqb w x); reflexivity.
    + assert (Hyz : y <> z).
      { intro Heq'; subst y. rewrite Hgy in Hz. injection Hz as Hz; subst e0. exact (Hne1 c args eq_refl). }
      destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
      exists (hupd G1' z v0). split.
      * eapply N_VarExp.
        -- exact HzF.
        -- rewrite (hupd_neq G x (BExpr (ECon c args)) z Hne). exact Hz.
        -- exact Hne1.
        -- exact Hne2.
        -- exact Hne3.
        -- exact HNE'.
      * assert (Hcong : forall w, hupd G1' z v0 w = hupd (hupd G1 x (BExpr (ECon c args))) z v0 w).
        { intro w0; unfold hupd; rewrite (Heq' w0); reflexivity. }
        intro w. rewrite (Hcong w). exact (hupd_comm G1 x (BExpr (ECon c args)) z v0 (not_eq_sym Hne) w).
  - (* N_ValFree *)
    exists (hupd G x (BExpr (ECon c args))). split.
    + apply N_ValFree.
    + intro w; reflexivity.
  - (* N_ValCon *)
    exists (hupd G x (BExpr (ECon c args))). split.
    + apply N_ValCon.
    + intro w; reflexivity.
  - (* N_Fun *)
    destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
    exists G1'. split.
    + eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | | exact HNE'].
      intros y0 Hy0.
      assert (Hne : s y0 <> x).
      { intro Heq. specialize (Hfresh y0 Hy0). rewrite Heq in Hfresh.
        destruct Hgx as [Hgx' | Hgx']; rewrite Hgx' in Hfresh; discriminate. }
      rewrite (hupd_neq G x (BExpr (ECon c args)) (s y0) Hne). exact (Hfresh y0 Hy0).
    + exact Heq'.
  - (* N_Let *)
    assert (Hzx : z <> x).
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
    destruct (NEval_pointwise_heap P F0 (hupd (hupd G z (let_content z e0)) x (BExpr (ECon c args))) k G1' v HNE'
                (hupd (hupd G x (BExpr (ECon c args))) z (let_content z e0)) Hcong)
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + apply N_Let.
      * rewrite (hupd_neq G x (BExpr (ECon c args)) z Hzx). exact HzFresh.
      * exact HNE2''.
    + intro w. rewrite (Heq2'' w). exact (Heq' w).
  - (* N_Or *)
    destruct (IH Hgx Hgy) as [G1' [HNE' Heq']].
    exists G1'. split.
    + eapply N_Or; [exact Hi | exact HNE'].
    + exact Heq'.
  - (* N_Select *)
    destruct (IH1 Hgx Hgy) as [G1' [HNE1' Heq1']].
    destruct (NEval_alias_or_con_persists P x y c args Hxy F0 G (BExpr (EVar z)) G1 (BExpr (ECon c0 zs)) Hrec1 Hgx Hgy) as [Hgx2 Hgy2].
    destruct (IH2 Hgx2 Hgy2) as [G2' [HNE2' Heq2']].
    destruct (NEval_pointwise_heap P F0 (hupd G1 x (BExpr (ECon c args))) (rename_b (zipsubst ys zs) body) G2' v HNE2' G1' Heq1')
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + eapply N_Select; [exact HNE1' | exact HIn | exact Hlen | exact HNE2''].
    + intro w. rewrite (Heq2'' w). exact (Heq2' w).
  - (* N_Guess *)
    destruct (IH1 Hgx Hgy) as [G1' [HNE1' Heq1']].
    destruct (NEval_alias_or_con_persists P x y c args Hxy F0 G (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 Hgx Hgy) as [Hgx2 Hgy2].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
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
    destruct (NEval_pointwise_heap P F0
                (hupd (hupd_list (hupd G1 z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws)) x (BExpr (ECon c args)))
                (rename_b (zipsubst ys1 ws) body1) G2' v HNE2'
                (hupd_list (hupd G1' z' (BExpr (ECon c1 ws))) ws (map (fun w0 => BExpr (EVar w0)) ws))
                Hcong)
      as [G2'' [HNE2'' Heq2'']].
    exists G2''. split.
    + eapply N_Guess; [exact HNE1' | exact Hhd | exact Hlen | exact HND | | exact HNE2''].
      intros w Hw.
      destruct (Nat.eq_dec w x) as [Heqwx | Hnewx].
      * subst w. exfalso. exact (Hxnotin Hw).
      * rewrite (Heq1' w).
        assert (Hw1 := Hfr w Hw).
        rewrite (hupd_neq G1 x (BExpr (ECon c args)) w Hnewx). exact Hw1.
    + intro w. rewrite (Heq2'' w). exact (Heq2' w).
Qed.
Lemma GEval_case_chase_back :
  forall P G x y, ContractLoc G x y ->
  forall brs G' v, GEval P G (BCase y brs) G' v -> GEval P G (BCase x brs) G' v.
Proof.
  intros P G x y H.
  induction H as [x0 e0 H0 | x0 y0 z0 H0 Hcl0 IH]; intros brs G' v HGE.
  - exact HGE.
  - eapply G_CaseFwd; [exact H0 | apply IH; exact HGE].
Qed.

Lemma CorrVTerm_con_inv :
  forall G x c args, CorrVTerm G x (BExpr (ECon c args)) ->
  exists y, ContractLoc G x y /\ G y = Some (GExpr (ECon c args)).
Proof.
  intros G x c args H. inversion H; subst.
  eexists. split; eassumption.
Qed.

Lemma CorrVTerm_functional : forall G x b1 b2, CorrVTerm G x b1 -> CorrVTerm G x b2 -> b1 = b2.
Proof.
  intros G x b1 b2 H1 H2.
  destruct H1; destruct H2;
    match goal with
    | [ HA : ContractLoc G x ?ya, HB : ContractLoc G x ?yb |- _ ] =>
        assert (ya = yb) by (eapply ContractLoc_functional; eauto); subst
    end;
    congruence.
Qed.

Lemma CorrV_functional : forall G v b1 b2, CorrV G v b1 -> CorrV G v b2 -> b1 = b2.
Proof.
  intros G v b1 b2 H1 H2.
  destruct H1; inversion H2; subst; try reflexivity.
  eapply CorrVTerm_functional; eauto.
Qed.

Theorem theorem2 :
  forall P G e G' v,
    GEval P G e G' v ->
    forall c args, CorrV G' v (BExpr (ECon c args)) ->
    forall Gam, HeapCorr G Gam ->
    exists Gam', NEval P nil Gam e Gam' (BExpr (ECon c args)) /\ HeapCorr G' Gam'.
Proof.
  intros P G e G' v H.
  induction H as
    [ G
    | G
    | G c args
    | G x y
    | G x
    | G G1 f args ps body v s HPf Hlen Hinj Hmatch Hfresh HGEbody IH
    | G G1 x e k v HxFresh HGEk IH
    | G x brs HGx
    | G x y brs G1 v HGx HGEy IH
    | G x f args brs G1 vx G2 v HGx HGE1 IH1 HGE2 IH2
    | G x y z brs G1 v HGx HGEy IH
    | G x c zs brs ys body G1 v HGx HIn Hlen HGEbody IH
    | G x c1 ys1 body1 brs G1 v ws HGx Hhd Hlen HND Hfresh HGEbody IH
    ]; intros c0 args0 Hcorr Gam HGam.
  - (* G_Bot *) inversion Hcorr.
  - (* G_Free *) inversion Hcorr.
  - (* G_Con *)
    inversion Hcorr; subst.
    exists Gam. split.
    + apply N_ValCon.
    + exact HGam.
  - (* G_Choice *) inversion Hcorr.
  - (* G_Var *)
    inversion Hcorr as [ | x' b' HCT0 Heq1 Heq2 ]; subst.
    destruct (CorrVTerm_con_inv G x c0 args0 HCT0) as [y [Hcl Hy]].
    eapply force_var; eauto.
  - (* G_Fun *)
    destruct (IH c0 args0 Hcorr Gam HGam) as [Gam1 [HNE HHC]].
    assert (Hfresh' : forall y, ~ In y ps -> Gam (s y) = None).
    { intros y Hy. specialize (Hfresh y Hy). specialize (HGam (s y)).
      rewrite Hfresh in HGam. exact HGam. }
    exists Gam1. split.
    + eapply N_Fun; eauto.
    + exact HHC.
  - (* G_Let *)
    assert (HGamxFresh : Gam x = None).
    { specialize (HGam x). rewrite HxFresh in HGam. exact HGam. }
    assert (HGam' : HeapCorr (hupd G x (GExpr e)) (hupd Gam x (let_content x e))).
    { apply HeapCorr_extend; assumption. }
    destruct (IH c0 args0 Hcorr (hupd Gam x (let_content x e)) HGam') as [Gam1 [HNE HHC]].
    exists Gam1. split.
    + apply N_Let. exact HGamxFresh. exact HNE.
    + exact HHC.
  - (* G_CaseBot *) inversion Hcorr.
  - (* G_CaseFwd *)
    (* STUCK -- precise diagnosis (updated after building `force_var`):   *)
    (* applying IH gives a full NEval derivation forcing `BCase y brs`;   *)
    (* inverting it (Select/Guess) yields a concrete sub-derivation       *)
    (* `NEval Gam (BExpr(EVar y)) Gam0 hnf` forcing y to SOME hnf.  If    *)
    (* Gam[x]'s CorrE witness happens to be the 1-hop alias `EVar y`      *)
    (* (CorrE_FwdHere), we are DONE immediately: N_VarExp on x can        *)
    (* directly reuse that exact sub-derivation, no new lemma needed.     *)
    (* The problem is the OTHER branch: if Gam[x]'s witness came via a    *)
    (* deeper CorrE_FwdChase (Gam already holds something more resolved   *)
    (* than a bare alias to y), reusing `force_var` requires knowing a    *)
    (* GRAPH-level fact "G's canonical target for x/y is Con-shaped" --   *)
    (* and the only way we found to extract that fact from the NEval     *)
    (* derivation we DO have is a general soundness lemma of the shape    *)
    (* "NEval P Gam e Gam' v' + HeapCorr G Gam -> CorrE G (...) v' /\    *)
    (*  HeapCorr G Gam'", proved by induction on the GIVEN NEval          *)
    (* derivation.  That lemma is not just "more of the same": its own    *)
    (* Nat-Fun/Nat-Let/Nat-Or cases require exactly the same kind of      *)
    (* case-by-case correspondence work as Theorem 2 itself, just in the  *)
    (* opposite direction.  It is a separate, comparably-sized theorem    *)
    (* (roughly "Theorem 2, converse") that we did not have time to       *)
    (* build.  See CorrE_con_to_contractloc below for the one fragment of *)
    (* it (graph-level reconstruction from a Con-shaped CorrE fact) we    *)
    (* DID manage to isolate and prove, which is what makes the "already  *)
    (* aliased" branch work once that missing soundness fact is granted.  *)
    admit.
  - (* G_CaseFun *)
    (* STUCK -- same underlying gap as G_CaseFwd.  vx (the result of      *)
    (* evaluating `f args`) is not known in advance to be Con-shaped; it  *)
    (* could be Free, Fun-thunk-impossible, Choice, or Fwd.  Handling     *)
    (* each of those sub-shapes for the CONTINUATION `BCase x brs` under  *)
    (* `hupd G1 x vx` reduces, respectively, to: G_CaseCon's argument      *)
    (* (done), G_CaseConFree's argument (done), and exactly G_CaseChoice  *)
    (* / G_CaseFwd's argument (stuck, for the reason given there) -- plus *)
    (* a vacuous Bot sub-case.  So G_CaseFun does not need extra theory   *)
    (* beyond what G_CaseFwd/G_CaseChoice need; it is blocked by the same *)
    (* missing "NEval soundness relative to G" lemma, not a new one.      *)
    admit.
  - (* G_CaseChoice *)
    (* STUCK -- identical root cause to G_CaseFwd (x is set to FWD y      *)
    (* here too, then evaluation is redirected to `BCase y brs`); see the *)
    (* diagnosis there.                                                   *)
    admit.
  - (* G_CaseCon *)
    assert (Hbx : Gam x = Some (BExpr (ECon c zs))) by (eapply Gam_from_con; eauto).
    destruct (IH c0 args0 Hcorr Gam HGam) as [Gam1 [HNE HHC]].
    exists Gam1. split.
    + eapply N_Select.
      * apply N_VarCons. exact Hbx.
      * exact HIn.
      * exact Hlen.
      * exact HNE.
    + exact HHC.
  - (* G_CaseConFree *)
    assert (Hbx : Gam x = Some (BExpr (EVar x))) by (eapply Gam_from_free; eauto).
    assert (Hxnotinws : ~ In x ws).
    { intro Hin. specialize (Hfresh x Hin). congruence. }
    assert (HGam1 : HeapCorr (hupd G x (GExpr (ECon c1 ws))) (hupd Gam x (BExpr (ECon c1 ws)))).
    { apply HeapCorr_update_free; assumption. }
    assert (Hfresh' : forall w, In w ws -> (hupd G x (GExpr (ECon c1 ws))) w = None).
    { intros w Hin. rewrite (hupd_neq G x (GExpr (ECon c1 ws)) w).
      - apply Hfresh; exact Hin.
      - intro Heq; subst w; apply Hxnotinws; exact Hin. }
    assert (HfreshGam : forall w, In w ws -> Gam w = None).
    { intros w Hin. specialize (HGam w). rewrite (Hfresh w Hin) in HGam. exact HGam. }
    assert (HGam2 :
      HeapCorr (hupd_list (hupd G x (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
               (hupd_list (hupd Gam x (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))).
    { apply HeapCorr_extend_free_list; assumption. }
    destruct (IH c0 args0 Hcorr _ HGam2) as [Gam1 [HNE HHC]].
    exists Gam1. split.
    + eapply N_Guess.
      * apply N_VarSelf. exact Hbx.
      * exact Hhd.
      * exact Hlen.
      * exact HND.
      * exact HfreshGam.
      * exact HNE.
    + exact HHC.
Admitted.
(* The payoff of the black-hole guard: forcing y (with y already pushed   *)
(* onto F) can NEVER touch a location x that merely aliases y, because     *)
(* any rule that tried to would have to re-examine y itself (directly, or  *)
(* by chasing back through x's own alias) -- and y is already in F, so     *)
(* Nat-VarExp's guard rejects it outright.  This is the fact that failed   *)
(* to hold under the OLD, unguarded semantics (blackhole_counterexample    *)
(* is a direct witness of its negation there); with the guard in place it  *)
(* holds cleanly, by the same case-by-case technique as                    *)
(* NEval_alias_or_con_persists.                                            *)
(* The payoff of the black-hole guard: forcing y (with y already pushed   *)
(* onto F) can NEVER touch a location x that merely aliases y, because     *)
(* any rule that tried to would have to re-examine y itself (directly, or  *)
(* by chasing back through x's own alias) -- and y is already in F, so     *)
(* Nat-VarExp's guard rejects it outright.  This is the fact that failed   *)
(* to hold under the OLD, unguarded semantics (blackhole_counterexample    *)
(* is a direct witness of its negation there); with the guard in place it  *)
(* holds cleanly, by the same case-by-case technique as                    *)
(* NEval_alias_or_con_persists.                                            *)
Lemma NEval_evar_forced_shape :
  forall P F Gam y G' v, NEval P F Gam (BExpr (EVar y)) G' v ->
  (Gam y = Some v /\ G' = Gam /\ (exists c args, v = BExpr (ECon c args))) \/
  (Gam y = Some (BExpr (EVar y)) /\ G' = Gam /\ v = BExpr (EVar y)) \/
  (Gam y = Some (BExpr EFree) /\ G' = hupd Gam y (BExpr (EVar y)) /\ v = BExpr (EVar y)) \/
  (~ In y F /\ exists e0 G1,
     Gam y = Some e0 /\ (forall c args, e0 <> BExpr (ECon c args)) /\
     e0 <> BExpr (EVar y) /\ e0 <> BExpr EFree /\
     NEval P (y :: F) Gam e0 G1 v /\ G' = hupd G1 y v).
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
    | F0 G0 x1 y1 G1 v1 i Hi Hrec IH
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

Lemma NEval_alias_frozen :
  forall P x y, x <> y ->
  forall e0y, (forall c args, e0y <> BExpr (ECon c args)) -> e0y <> BExpr (EVar y) -> e0y <> BExpr EFree ->
  forall F Gam e Gam' v, NEval P F Gam e Gam' v ->
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HyF Hgx Hgy.
  - (* N_VarCons *)
    assert (Hzx : z <> x) by (intro Heq; subst z; rewrite Hz in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey1 c0 args0 eq_refl)).
    split; assumption.
  - (* N_VarSelf *)
    assert (Hzx : z <> x).
    { intro Heq; subst z. rewrite Hz in Hgx. injection Hgx as Hgx. exact (Hxy Hgx). }
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey2 eq_refl)).
    split; assumption.
  - (* N_VarFree *)
    assert (Hzx : z <> x) by (intro Heq; subst z; rewrite Hz in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite Hz in Hgy; injection Hgy as Hgy; subst e0y; exact (Hey3 eq_refl)).
    split.
    + rewrite (hupd_neq G z (BExpr (EVar z)) x (not_eq_sym Hzx)). exact Hgx.
    + rewrite (hupd_neq G z (BExpr (EVar z)) y (not_eq_sym Hzy)). exact Hgy.
  - (* N_VarExp *)
    destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + (* z = x : forces e1 = EVar y, then Hrec is "force y under (x::F0)" -- impossible *)
      subst z.
      assert (He1 : e1 = BExpr (EVar y)) by (rewrite Hz in Hgx; congruence).
      subst e1.
      assert (HyF' : In y (x :: F0)) by (right; exact HyF).
      exfalso.
      destruct (NEval_evar_forced_shape P (x :: F0) G y G1 v0 Hrec) as
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
    + (* z <> x : need also z <> y to apply IH cleanly *)
      destruct (Nat.eq_dec z y) as [Heqzy | Hnezy].
      * (* z = y : forcing y itself, contradicts HzF (~In y F0) vs HyF (In y F0) *)
        subst z. exfalso. exact (HzF HyF).
      * assert (HyF' : In y (z :: F0)) by (right; exact HyF).
        destruct (IH HyF' Hgx Hgy) as [IHx IHy].
        split.
        -- rewrite (hupd_neq G1 z v0 x (not_eq_sym Hnezx)). exact IHx.
        -- rewrite (hupd_neq G1 z v0 y (not_eq_sym Hnezy)). exact IHy.
  - (* N_ValFree *) split; assumption.
  - (* N_ValCon *) split; assumption.
  - (* N_Fun *) exact (IH HyF Hgx Hgy).
  - (* N_Let *)
    assert (Hzx : z <> x) by (intro Heq; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite HzFresh in Hgy; discriminate Hgy).
    assert (Hgx2 : hupd G z (let_content z e1) x = Some (BExpr (EVar y)))
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    assert (Hgy2 : hupd G z (let_content z e1) y = Some e0y)
      by (rewrite (hupd_neq G z (let_content z e1) y (not_eq_sym Hzy)); exact Hgy).
    exact (IH HyF Hgx2 Hgy2).
  - (* N_Or *) exact (IH HyF Hgx Hgy).
  - (* N_Select *)
    destruct (IH1 HyF Hgx Hgy) as [IH1x IH1y].
    exact (IH2 HyF IH1x IH1y).
  - (* N_Guess *)
    destruct (IH1 HyF Hgx Hgy) as [IH1x IH1y].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
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
(* NEval only ever inspects F through membership checks (~In _ F) --      *)
(* never its order or structure -- so replacing F with any list having    *)
(* the same members preserves validity.                                   *)
Lemma NEval_F_perm :
  forall P F1 F2, (forall w, In w F1 <-> In w F2) ->
  forall Gam e Gam' v, NEval P F1 Gam e Gam' v -> NEval P F2 Gam e Gam' v.
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros F2 Hperm.
  - apply N_VarCons. exact Hz.
  - apply N_VarSelf. exact Hz.
  - apply N_VarFree. exact Hz.
  - eapply N_VarExp.
    + intro Hin. apply HzF. apply (Hperm z). exact Hin.
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply IH. intro w; simpl; split.
      * intros [Heq | Hin]; [left; exact Heq | right; apply (Hperm w); exact Hin].
      * intros [Heq | Hin]; [left; exact Heq | right; apply (Hperm w); exact Hin].
  - apply N_ValFree.
  - apply N_ValCon.
  - eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | apply IH; exact Hperm].
  - apply N_Let; [exact HzFresh | apply IH; exact Hperm].
  - eapply N_Or; [exact Hi | apply IH; exact Hperm].
  - eapply N_Select; [apply IH1; exact Hperm | exact HIn | exact Hlen | apply IH2; exact Hperm].
  - eapply N_Guess; [apply IH1; exact Hperm | exact Hhd | exact Hlen | exact HND | exact Hfr | apply IH2; exact Hperm].
Qed.
(* Companion to NEval_alias_frozen: not just does x's alias survive       *)
(* unchanged while y is already in F, the WHOLE DERIVATION remains valid  *)
(* if x is ALSO added to F -- x is never the subject of any rule within   *)
(* it (the same case-by-case argument as NEval_alias_frozen), so adding   *)
(* it to the guard set changes nothing observable.                        *)
Lemma NEval_alias_weaken :
  forall P x y, x <> y ->
  forall e0y, (forall c args, e0y <> BExpr (ECon c args)) -> e0y <> BExpr (EVar y) -> e0y <> BExpr EFree ->
  forall F Gam e Gam' v, NEval P F Gam e Gam' v ->
  In y F ->
  Gam x = Some (BExpr (EVar y)) ->
  Gam y = Some e0y ->
  NEval P (x :: F) Gam e Gam' v.
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
    | F0 G z c0 zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros HyF Hgx Hgy.
  - (* N_VarCons *) apply N_VarCons. exact Hz.
  - (* N_VarSelf *) apply N_VarSelf. exact Hz.
  - (* N_VarFree *) apply N_VarFree. exact Hz.
  - (* N_VarExp *)
    destruct (Nat.eq_dec z x) as [Heqzx | Hnezx].
    + (* z = x : impossible, exactly as in NEval_alias_frozen *)
      subst z.
      assert (He1 : e1 = BExpr (EVar y)) by (rewrite Hz in Hgx; congruence).
      subst e1.
      assert (HyF' : In y (x :: F0)) by (right; exact HyF).
      exfalso.
      destruct (NEval_evar_forced_shape P (x :: F0) G y G1 v0 Hrec) as
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
        eapply N_VarExp.
        -- exact HzxF.
        -- exact Hz.
        -- exact Hne1.
        -- exact Hne2.
        -- exact Hne3.
        -- (* IH gives "NEval (x :: z :: F0) G e1 G1 v0"; we need
              "NEval (z :: x :: F0) G e1 G1 v0" -- same members, different
              order, reconciled via NEval_F_perm. *)
           apply (NEval_F_perm P (x :: z :: F0) (z :: x :: F0)).
           ++ intro w; simpl; tauto.
           ++ exact (IH HyF' Hgx Hgy).
  - (* N_ValFree *) apply N_ValFree.
  - (* N_ValCon *) apply N_ValCon.
  - (* N_Fun *)
    eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | ].
    exact (IH HyF Hgx Hgy).
  - (* N_Let *)
    assert (Hzx : z <> x) by (intro Heq; subst z; rewrite HzFresh in Hgx; discriminate Hgx).
    assert (Hzy : z <> y) by (intro Heq; subst z; rewrite HzFresh in Hgy; discriminate Hgy).
    assert (Hgx2 : hupd G z (let_content z e1) x = Some (BExpr (EVar y)))
      by (rewrite (hupd_neq G z (let_content z e1) x (not_eq_sym Hzx)); exact Hgx).
    assert (Hgy2 : hupd G z (let_content z e1) y = Some e0y)
      by (rewrite (hupd_neq G z (let_content z e1) y (not_eq_sym Hzy)); exact Hgy).
    apply N_Let; [exact HzFresh | exact (IH HyF Hgx2 Hgy2)].
  - (* N_Or *) eapply N_Or; [exact Hi | exact (IH HyF Hgx Hgy)].
  - (* N_Select *)
    destruct (NEval_alias_frozen P x y Hxy e0y Hey1 Hey2 Hey3 F0 G (BExpr (EVar z)) G1 (BExpr (ECon c0 zs)) Hrec1 HyF Hgx Hgy)
      as [IH1x IH1y].
    eapply N_Select; [exact (IH1 HyF Hgx Hgy) | exact HIn | exact Hlen | exact (IH2 HyF IH1x IH1y)].
  - (* N_Guess *)
    destruct (NEval_alias_frozen P x y Hxy e0y Hey1 Hey2 Hey3 F0 G (BExpr (EVar z)) G1 (BExpr (EVar z')) Hrec1 HyF Hgx Hgy)
      as [IH1x IH1y].
    assert (HG1z' : G1 z' = Some (BExpr (EVar z')))
      by exact (NEval_selfloop_result_persists P F0 G (BExpr (EVar z)) G1 z' Hrec1).
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
    eapply N_Guess; [exact (IH1 HyF Hgx Hgy) | exact Hhd | exact Hlen | exact HND | exact Hfr | exact (IH2 HyF Hgx3 Hgy3)].
Qed.
(* The top-level form actually needed by NEval_fwd_transfer: Hrec1 itself *)
(* starts at F=nil (y not yet pushed), so NEval_alias_weaken doesn't      *)
(* apply directly to it -- but the moment Hrec1 takes its own first step  *)
(* (forcing y's raw content), y gets pushed, and from there               *)
(* NEval_alias_weaken applies to the recursive sub-derivation.            *)
Lemma NEval_alias_weaken_force_y :
  forall P x y, x <> y ->
  forall Gam Gmid v, NEval P nil Gam (BExpr (EVar y)) Gmid v ->
  Gam x = Some (BExpr (EVar y)) ->
  NEval P (x :: nil) Gam (BExpr (EVar y)) Gmid v.
Proof.
  intros P x y Hxy Gam Gmid v H Hgx.
  destruct (NEval_evar_forced_shape P nil Gam y Gmid v H) as
    [ [Hcase1 [HeqG [c [args Heqv]]]]
    | [ [Hcase2 [HeqG Heqv]]
      | [ [Hcase3 [HeqG Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqG]]]]]]]] ] ] ].
  - subst Gmid v. apply N_VarCons. exact Hcase1.
  - subst Gmid v. apply N_VarSelf. exact Hcase2.
  - subst Gmid v. apply N_VarFree. exact Hcase3.
  - subst Gmid.
    eapply N_VarExp.
    + intro Hin. destruct Hin as [Heq | Hin]; [exact (Hxy Heq) | destruct Hin].
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply (NEval_F_perm P (x :: y :: nil) (y :: x :: nil)).
      * intro w; simpl; tauto.
      * apply (NEval_alias_weaken P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil) Gam e0 G1 v Hrec).
        -- left; reflexivity.
        -- exact Hgx.
        -- exact Hz.
Qed.
(* THE PAYOFF: with the black-hole guard in place, the persistence         *)
(* argument that failed under the OLD, unguarded semantics (see            *)
(* blackhole_counterexample) now goes through.  This proves the core case  *)
(* of NEval_fwd_transfer -- x's CorrE witness is the direct 1-hop alias    *)
(* `EVar y` (CorrE_FwdHere), and the given derivation resolves y to a      *)
(* constructor via Nat-Select -- in full, using nothing but the guard and  *)
(* the lemmas built around it (NEval_alias_weaken_force_y, NEval_alias_    *)
(* frozen, NEval_shortcut_alias, NEval_con_persists).  Completing          *)
(* NEval_fwd_transfer itself needs two more things this does not cover:    *)
(* (a) x's witness arising via the deeper CorrE_FwdChase (not just the     *)
(* direct alias), and (b) the Nat-Guess/free-variable-result case, which   *)
(* would need an analogous "shortcut" lemma for free-variable promotion    *)
(* (NEval_shortcut_alias is specifically about constructor promotion).     *)
Lemma NEval_fwd_transfer_fwdhere_con :
  forall P G Gam, HeapCorr G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Some (BExpr (EVar y)) ->
  forall brs c zs ys body Gmid Gam' v',
    NEval P nil Gam (BExpr (EVar y)) Gmid (BExpr (ECon c zs)) ->
    In (c, ys, body) brs ->
    length ys = length zs ->
    NEval P nil Gmid (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hb brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2.
  destruct (NEval_evar_forced_shape P nil Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
    [ [Hcase1 [HeqGmid _]]
    | [ [Hcase2 [_ Heqv]]
      | [ [Hcase3 [_ Heqv]]
        | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv.
  - (* Case A: y already Con-shaped, Gmid = Gam *)
    subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hcase1 in Hb. discriminate Hb. }
    assert (HforceX : NEval P nil Gam (BExpr (EVar x)) (hupd Gam x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply N_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - apply N_VarCons. exact Hcase1. }
    destruct (NEval_shortcut_alias P x y c zs Hxy nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hb) Hcase1) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply N_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1x HHC.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_con_persists P nil Gam (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hcase1). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact HHC | exact Hcy]).
      assert (HCEx : CorrE G1v x (BExpr (ECon c zs))).
      { destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
        eapply CorrE_FwdAchievedCon; [exact HG1x | exact Hcl1 | exact Hz1]. }
      assert (HHC' : HeapCorr G1v (hupd Gam' x (BExpr (ECon c zs))))
        by (eapply HeapCorr_update_consistent; [exact HHC | exact HCEx]).
      intro w. rewrite (Heq2' w). exact (HHC' w).
  - (* Case B: y forces via Nat-VarExp, e0 non-terminal *)
    subst Gmid.
    assert (Hxy : x <> y).
    { intro Heq; subst y. rewrite Hz in Hb. injection Hb as Hb. exact (Hne2 Hb). }
    assert (HforceY : NEval P (x :: nil) Gam (BExpr (EVar y)) (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { exact (NEval_alias_weaken_force_y P x y Hxy Gam (hupd G1 y (BExpr (ECon c zs))) (BExpr (ECon c zs)) Hrec1 Hb). }
    assert (HforceX : NEval P nil Gam (BExpr (EVar x))
               (hupd (hupd G1 y (BExpr (ECon c zs))) x (BExpr (ECon c zs))) (BExpr (ECon c zs))).
    { eapply N_VarExp.
      - intro Hin; destruct Hin.
      - exact Hb.
      - intros c' args' Heq; discriminate.
      - intro Heq; injection Heq as Heq; congruence.
      - intro Heq; discriminate.
      - exact HforceY. }
    assert (HG1xy : G1 x = Some (BExpr (EVar y)) /\ G1 y = Some e0).
    { exact (NEval_alias_frozen P x y Hxy e0 Hne1 Hne2 Hne3 (y :: nil) Gam e0 G1 (BExpr (ECon c zs)) Hrec
               (or_introl eq_refl) Hb Hz). }
    destruct HG1xy as [HG1x HG1y].
    assert (Hgmidx : hupd G1 y (BExpr (ECon c zs)) x = Some (BExpr (EVar y))).
    { rewrite (hupd_neq G1 y (BExpr (ECon c zs)) x Hxy). exact HG1x. }
    assert (Hgmidy : hupd G1 y (BExpr (ECon c zs)) y = Some (BExpr (ECon c zs))).
    { unfold hupd; rewrite Nat.eqb_refl; reflexivity. }
    destruct (NEval_shortcut_alias P x y c zs Hxy nil (hupd G1 y (BExpr (ECon c zs)))
                (rename_b (zipsubst ys zs) body) Gam' v' Hrec2
                (or_introl Hgmidx) Hgmidy) as [Gam1' [HNE2' Heq2']].
    exists Gam1'. split.
    + eapply N_Select; [exact HforceX | exact HIn | exact Hlen | exact HNE2'].
    + intros G1v HG1vx HHC.
      assert (Hcy : Gam' y = Some (BExpr (ECon c zs))).
      { exact (NEval_con_persists P nil (hupd G1 y (BExpr (ECon c zs)))
                 (rename_b (zipsubst ys zs) body) Gam' v' Hrec2 y c zs Hgmidy). }
      assert (HCEy : CorrE G1v y (BExpr (ECon c zs))) by (eapply HeapCorr_Gam_CorrE; [exact HHC | exact Hcy]).
      assert (HCEx : CorrE G1v x (BExpr (ECon c zs))).
      { destruct (CorrE_con_to_contractloc G1v y c zs HCEy) as [z1 [Hcl1 Hz1]].
        eapply CorrE_FwdAchievedCon; [exact HG1vx | exact Hcl1 | exact Hz1]. }
      assert (HHC' : HeapCorr G1v (hupd Gam' x (BExpr (ECon c zs))))
        by (eapply HeapCorr_update_consistent; [exact HHC | exact HCEx]).
      intro w. rewrite (Heq2' w). exact (HHC' w).
Qed.
(* The FwdChase counterpart to NEval_fwd_transfer_fwdhere_con above,       *)
(* scoped to the one sub-case that is both actually needed (per how        *)
(* HeapCorr_update_consistent, above, actually constructs FwdChase          *)
(* witnesses elsewhere in this file: always as a literal COPY of the        *)
(* target location's own current value, never an unrelated-but-still-       *)
(* CorrE-valid witness) and safe to prove outright: x's Gam-witness is NOT  *)
(* the lazy 1-hop alias `EVar y` (CorrE_FwdHere) but the SAME value Gam      *)
(* already holds for y (`Gam x = Gam y`), AND y has ALREADY been forced to  *)
(* a constructor.  This case is trivial -- since Gam x = Gam y = Con c zs   *)
(* directly, x is already that constructor too, so forcing x is a plain    *)
(* Nat-VarCons; no shortcut-alias heap surgery is needed at all.            *)
(*                                                                            *)
(* NOT covered here (left for future work): Gam x = Gam y where y's OWN      *)
(* content still needs further forcing (e0 non-terminal).  Replaying that    *)
(* shared content under x's guard `{x}` instead of y's `{y}` is not          *)
(* obviously safe -- unlike the FwdHere case (where x merely holds the       *)
(* INDIRECTION `EVar y`, so forcing x recurses into forcing y BY NAME, and    *)
(* NEval_alias_weaken_force_y/NEval_alias_frozen show x is never itself the  *)
(* subject of any rule inside y's own forcing), here x and y would each be    *)
(* independently evaluating the SAME raw content e0 from scratch, and         *)
(* nothing yet shows e0's evaluation is guard-agnostic between {x} and {y} -- *)
(* the exact shape of risk blackhole_counterexample (Section 7b-i) exploited. *)
Lemma NEval_fwd_transfer_fwdchase_con :
  forall P G Gam, HeapCorr G Gam ->
  forall x y, G x = Some (GFwd y) ->
  Gam x = Gam y ->
  forall brs c zs ys body Gam' v',
    Gam y = Some (BExpr (ECon c zs)) ->
    In (c, ys, body) brs ->
    length ys = length zs ->
    NEval P nil Gam (rename_b (zipsubst ys zs) body) Gam' v' ->
  exists Gam'', NEval P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx Hxy brs c zs ys body Gam' v' Hy HIn Hlen Hrec2.
  assert (Hx : Gam x = Some (BExpr (ECon c zs))) by (rewrite Hxy; exact Hy).
  exists Gam'. split.
  - eapply N_Select; [apply N_VarCons; exact Hx | exact HIn | exact Hlen | exact Hrec2].
  - intros G1 _ HHC. exact HHC.
Qed.

(* HISTORICAL NOTE (superseded -- kept for the write-up).                 *)
(*                                                                          *)
(* This file used to contain a substantial section here (roughly 650       *)
(* lines) building a concrete counterexample to the FULLY GENERAL           *)
(* "chase, y needs further forcing" extension of                            *)
(* NEval_fwd_transfer_fwdchase_con -- and, more importantly, to                *)
(* NEval_fwd_transfer ITSELF (the actual lemma theorem2's G_CaseFwd case         *)
(* needs).  Its witnesses:                                                       *)
(*                                                                                 *)
(*   fc_Gam0 : both x(0) and y(1) hold the IDENTICAL raw, non-terminal              *)
(*             content `f(x)` (a self-referential function call, via               *)
(*             `let x = f(x) in ...`-style sharing -- no aliasing at all,           *)
(*             just two DIFFERENT locations independently bound to the SAME         *)
(*             expression object).                                                    *)
(*   fc_G    : x forwards to y (G x = GFwd y), and y's OWN direct graph               *)
(*             content really is `EFun f (x::nil)` -- so `Gam x = Gam y` was          *)
(*             a valid CorrE_FwdChase witness under the OLD, unrestricted             *)
(*             `CorrE_FwdChase : G x=GFwd y -> CorrE G y b -> CorrE G x b`            *)
(*             (b arbitrary, here a non-terminal EFun call, not an achieved           *)
(*             value at all).                                                         *)
(*                                                                                    *)
(* The proof showed: forcing y CAN reach a constructor R (picking one Or-choice       *)
(* at the top level, escaping via a DIFFERENT Or-choice one level down, when x        *)
(* is momentarily unguarded); but forcing x DIRECTLY can ONLY ever reach a            *)
(* DIFFERENT constructor K, because the SAME escape route requires re-entering        *)
(* x while x is ALREADY in its own guard -- outright impossible.  Packaged as a       *)
(* full disproof (`NEval_fwd_transfer_is_false`), instantiating a `brs` with only     *)
(* an R-branch: y's forcing satisfies every hypothesis of the general lemma, yet      *)
(* x's forcing has no valid derivation through EITHER Nat-Select or Nat-Guess.        *)
(*                                                                                    *)
(* THE FIX: exactly the CorrE_FwdChase -> CorrE_FwdAchievedCon restriction            *)
(* described in the CorrE definition's own comment (and the two earlier               *)
(* HISTORICAL NOTEs, for HeapCorr_update_not_general and                              *)
(* NEval_confluence_unrestricted_is_false) ALSO eliminates this counterexample's      *)
(* construction: fc_Gam0's shared witness (a raw, non-terminal EFun call reached      *)
(* via forwarding) is no longer CorrE-valid at all -- fc_HeapCorr's own first proof   *)
(* obligation (`HeapCorr fc_G fc_Gam0`) can no longer be established, since only an   *)
(* alias (`EVar y`) or an ACHIEVED constructor is now a legal witness for a           *)
(* forwarding location.  The whole section -- fc_f_body/fc_g_body/fc_P/fc_Gam0/fc_G,  *)
(* the renaming/freshness helper lemmas, fc_force_y_reaches_R,                        *)
(* fc_force_x_reaches_only_K (and its fc_force_x_never_R/fc_force_x_never_selfloop    *)
(* corollaries), fc_HeapCorr, and the two packaged disproof theorems                  *)
(* (NEval_fwd_transfer_fwdchase_general_is_false, NEval_fwd_transfer_is_false) -- is  *)
(* removed rather than salvaged, since none of it typechecks against the revised      *)
(* CorrE and none of it would be reusable even if patched (the whole point was to     *)
(* exploit exactly the generality the fix removes).                                   *)
(*                                                                                    *)
(* NEval_fwd_transfer_fwdhere_con (fully proven, Con-achieving direction of the       *)
(* direct 1-hop alias case) and NEval_fwd_transfer_fwdchase_con (fully proven,        *)
(* just above -- Gam x = Gam y, y ALREADY resolved) both remain, unaffected --        *)
(* neither ever relied on the unrestricted FwdChase.  With the fix in place, a        *)
(* forwarding location's Gam-witness is now PROVABLY always either the direct         *)
(* alias or an already-achieved constructor (see CorrE's own definition) -- so        *)
(* the "harder half" these counterexamples were probing (a raw, non-terminal,         *)
(* shared-content witness) can no longer arise as a HeapCorr fact at all, and         *)
(* the FwdChase case of NEval_fwd_transfer should now be CLOSED by                    *)
(* NEval_fwd_transfer_fwdchase_con alone -- the next step is re-attempting            *)
(* NEval_fwd_transfer's proof directly against this strengthened invariant.           *)


(* Reliable case-split for CorrE, avoiding hand-counted `inversion ... as
   [...]` patterns (same technique as NEval_evar_forced_shape etc). *)
Lemma CorrE_forced_shape :
  forall G y b, CorrE G y b ->
  (exists c args, G y = Some (GExpr (ECon c args)) /\ b = BExpr (ECon c args)) \/
  (G y = Some (GExpr EFree) /\ b = BExpr (EVar y)) \/
  (exists f args, G y = Some (GExpr (EFun f args)) /\ b = BExpr (EFun f args)) \/
  (exists y1 y2, G y = Some (GExpr (EChoice y1 y2)) /\ b = BExpr (EChoice y1 y2)) \/
  (exists z, G y = Some (GExpr (EVar z)) /\ b = BExpr (EVar z)) \/
  (G y = Some (GExpr EBot) /\ b = BExpr EBot) \/
  (exists y0, G y = Some (GFwd y0) /\ b = BExpr (EVar y0)) \/
  (exists y0 z0 c0 args0, G y = Some (GFwd y0) /\ ContractLoc G y0 z0 /\
     G z0 = Some (GExpr (ECon c0 args0)) /\ b = BExpr (ECon c0 args0)).
Proof.
  intros G y b H.
  destruct H as
    [ x0 c0 args0 H0
    | x0 H0
    | x0 f0 args0 H0
    | x0 y1 y2 H0
    | x0 z0 H0
    | x0 H0
    | x0 y0 H0
    | x0 y0 z0 c0 args0 H0 Hcl0 Hz0
    ].
  - left. exists c0, args0. split; [exact H0 | reflexivity].
  - right; left. split; [exact H0 | reflexivity].
  - right; right; left. exists f0, args0. split; [exact H0 | reflexivity].
  - right; right; right; left. exists y1, y2. split; [exact H0 | reflexivity].
  - right; right; right; right; left. exists z0. split; [exact H0 | reflexivity].
  - right; right; right; right; right; left. split; [exact H0 | reflexivity].
  - right; right; right; right; right; right; left. exists y0. split; [exact H0 | reflexivity].
  - right; right; right; right; right; right; right.
    exists y0, z0, c0, args0. split; [exact H0 | split; [exact Hcl0 | split; [exact Hz0 | reflexivity]]].
Qed.

(* THE KEY MISSING PIECE: forcing y (however deep its own alias chain,
   under ANY guard F) always reaches whatever constructor x's achieved-Con
   witness (via ContractLoc from y) points to.  Given x's achieved witness,
   y's OWN raw content, whenever non-terminal, can ONLY be a further alias
   (never an independent Fun/Choice/VarThunk/Bot call): if y were
   non-forwarding with such content, ContractLoc uniqueness would force
   the achieved target to BE y itself, contradicting non-terminal content
   there.  So the alias chain is the only option, and it must be finite
   (F is a valid guard throughout a terminating derivation) -- induction
   on the given derivation walks it to completion. *)
Lemma NEval_force_reaches_achieved :
  forall P G Gam, HeapCorr G Gam ->
  forall F e Gam' v, NEval P F Gam e Gam' v ->
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
    | F0 G0 x1 y1 G1 v1 i Hi Hrec IH
    | F0 G0 z c zs brs ys body G1 v1 G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G0 z G1 z' c1' ys1 body1 brs G2 v1 ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros y Ht z1 c1 args1 Hcl1 Hz1; try discriminate Ht.
  - (* N_VarCons : Gam y = Con c args directly *)
    injection Ht as Ht; subst z.
    assert (HCEy : CorrE G y (BExpr (ECon c args))) by (eapply HeapCorr_Gam_CorrE; [exact HGam | exact Hz]).
    destruct (CorrE_con_to_contractloc G y c args HCEy) as [z2 [Hcl2 Hz2]].
    assert (Heqz : z1 = z2) by (eapply ContractLoc_functional; [exact Hcl1 | exact Hcl2]).
    subst z2. rewrite Hz1 in Hz2. injection Hz2 as Hz2. subst c1 args1. reflexivity.
  - (* N_VarSelf : Gam y = EVar y -- forces G y = EFree (CorrE_Free, since
       CorrE_forced_shape's only EVar-y-shaped case with x=y is Free or,
       impossibly, a self-forwarding FwdHere), contradicting achieved-Con. *)
    injection Ht as Ht; subst z.
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
    + (* Free : G y = EFree, non-forwarding, so ContractLoc forces z1 = y *)
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* VarThunk-shaped b = EVar z0 with z0 = y (from Hb) : same non-forwarding
         contradiction *)
      injection Hb as Hb. subst z0.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* FwdHere-shaped b = EVar y0 with y0 = y (from Hb) : G y = GFwd y,
         a forwarding self-loop, impossible *)
      injection Hb as Hb. subst y0.
      exact (ContractLoc_no_selfFwd G y z1 Hcl1 Hgy).
  - (* N_VarFree : Gam y = EFree directly -- G y = EFree (CorrE_Free unique),
       same contradiction: z1 = y, but G y = EFree not Con. *)
    injection Ht as Ht; subst z.
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
    (* only the Bot case gives b = BExpr EBot, not EFree; every other
       disjunct's own b-shape already discriminates against BExpr EFree,
       EXCEPT there is no constructor at all producing witness BExpr EFree
       itself -- CorrE_Free's OWN witness is BExpr (EVar x), not BExpr EFree.
       So actually every branch discriminates; nothing left to prove here. *)
  - (* N_VarExp : Gam y = e0, non-terminal *)
    injection Ht as Ht; subst z.
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
    + (* e0 = EFun f args : y non-forwarding, ContractLoc forces z1 = y *)
      exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* e0 = EChoice : same contradiction *)
      exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* e0 = EVar z0 (VarThunk, y non-forwarding) : same contradiction *)
      exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* e0 = EBot : same contradiction *)
      exfalso.
      assert (Hz1y : z1 = y) by (eapply ContractLoc_nonfwd; [exact Hgy | exact Hcl1]).
      subst z1. rewrite Hgy in Hz1. discriminate Hz1.
    + (* e0 = EVar y0 (FwdHere) : y forwards to y0 -- ContractLoc G y z1 must
         go through y0, giving ContractLoc G y0 z1; recurse via IH forcing y0. *)
      subst e0.
      assert (Hcl1' : ContractLoc G y0 z1).
      { inversion Hcl1 as [x0 e1 Hx0 | x0 y0' z0' Hx0 Hcl0']; subst.
        - rewrite Hgy in Hx0; discriminate Hx0.
        - rewrite Hgy in Hx0; injection Hx0 as Hx0; subst y0'; exact Hcl0'. }
      exact (IH HGam y0 eq_refl z1 c1 args1 Hcl1' Hz1).
    + (* e0 = Con c0 args0 (FwdAchievedCon) : excluded by Hne1 *)
      exfalso. subst e0. exact (Hne1 c0 args0 eq_refl).
Qed.

(* Re-added (was originally built to support the removed fc_* section, but
   is independently useful): a reliable inversion principle for BCase
   targets, splitting into the Nat-Select and Nat-Guess shapes. *)
Lemma NEval_bcase_forced_shape :
  forall P F Gam x brs G' v, NEval P F Gam (BCase x brs) G' v ->
  (exists c zs ys body G1,
     NEval P F Gam (BExpr (EVar x)) G1 (BExpr (ECon c zs)) /\
     In (c, ys, body) brs /\ length ys = length zs /\
     NEval P F G1 (rename_b (zipsubst ys zs) body) G' v)
  \/
  (exists x' G1 c1 ys1 body1 ws,
     NEval P F Gam (BExpr (EVar x)) G1 (BExpr (EVar x')) /\
     hd_error brs = Some (c1, ys1, body1) /\ length ws = length ys1 /\ NoDup ws /\
     (forall w, In w ws -> G1 w = None) /\
     NEval P F (hupd_list (hupd G1 x' (BExpr (ECon c1 ws))) ws (map (fun w => BExpr (EVar w)) ws))
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
    | F0 G0 x1 y1 G1 v1 i Hi Hrec IH
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

(* THE ASSEMBLY: NEval_fwd_transfer, the lemma theorem2's G_CaseFwd case
   needs.  Given HeapCorr, x's witness (via HeapCorr + CorrE_forced_shape,
   since G x = GFwd y) can only be FwdHere (b = EVar y) or FwdAchievedCon
   (b = Con c1 args1, achieved) -- every other CorrE shape requires x to be
   non-forwarding, contradicting G x = GFwd y directly.

   FwdHere is FULLY closed by NEval_fwd_transfer_fwdhere_con (both its own
   sub-cases: y already resolved, or y needs further forcing).

   FwdAchievedCon needs NEval_force_reaches_achieved first (confirming c1 =
   c, args1 = zs -- i.e. x's achieved value IS what y's own forcing
   reaches), then splits on HOW y resolves:
     - y already resolved in Gam directly (Nat-Select's own premise is
       N_VarCons) -- closed by NEval_fwd_transfer_fwdchase_con (Gam x =
       Gam y now holds, both being Con c zs).
     - y needs further forcing (Nat-VarExp fires) -- OPEN.  A second,
       independent attempt this session (a "reverse shortcut" lemma
       replaying the continuation from Gam instead of from y's
       post-forcing heap) confirmed this needs the same missing "NEval
       soundness relative to G" fact theorem2's own G_CaseFwd comment
       already names: relating the continuation's behavior over the two
       different starting heaps requires knowing y's own forcing never
       touches any location the continuation separately references, which
       is not derivable from HeapCorr alone.

   Nat-Guess (y resolves to a free-variable/self-loop result rather than a
   constructor) is ALSO OPEN -- neither fwdhere_con, fwdchase_con, nor
   NEval_force_reaches_achieved say anything about this shape; it needs an
   analogous "shortcut" lemma for free-variable promotion, flagged as
   missing before this session began. *)
Lemma NEval_fwd_transfer :
  forall P G Gam, HeapCorr G Gam ->
  forall x y, G x = Some (GFwd y) ->
  forall brs Gam' v', NEval P nil Gam (BCase y brs) Gam' v' ->
  exists Gam'', NEval P nil Gam (BCase x brs) Gam'' v' /\
                (forall G1, G1 x = Some (GFwd y) -> HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
Proof.
  intros P G Gam HGam x y HGx brs Gam' v' H.
  destruct (NEval_bcase_forced_shape P nil Gam y brs Gam' v' H) as
    [ [c [zs [ys [body [Gmid [Hrec1 [HIn [Hlen Hrec2]]]]]]]]
    | [x' [Gmid [c1' [ys1 [body1 [ws [Hrec1 [Hhd [Hlen [HND [Hfr Hrec2]]]]]]]]]]] ].
  - (* Nat-Select : y forces to a constructor Con c zs *)
    assert (HGamx := HGam x). rewrite HGx in HGamx.
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
    + (* FwdHere : b = EVar y0, and G x = GFwd y forces y0 = y *)
      rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      exact (NEval_fwd_transfer_fwdhere_con P G Gam HGam x y HGx Hb
               brs c zs ys body Gmid Gam' v' Hrec1 HIn Hlen Hrec2).
    + (* FwdAchievedCon : b = Con c0 args0, achieved via ContractLoc G y0 z0
         with y0 = y (from G x = GFwd y = GFwd y0) *)
      rewrite HGx in Hgx. injection Hgx as Hgx. subst y0. subst b.
      assert (Heqv : BExpr (ECon c zs) = BExpr (ECon c0 args0))
        by (eapply NEval_force_reaches_achieved; [exact HGam | exact Hrec1 | reflexivity | exact Hcl0 | exact Hz0]).
      injection Heqv as Heqc Heqargs. subst c0 args0.
      assert (Hx : Gam x = Some (BExpr (ECon c zs))) by exact Hb.
      destruct (NEval_evar_forced_shape P nil Gam y Gmid (BExpr (ECon c zs)) Hrec1) as
        [ [Hcase1 [HeqGmid _]]
        | [ [Hcase2 [_ Heqv2]]
          | [ [Hcase3 [_ Heqv2]]
            | [_ [e0 [G1 [Hz [Hne1 [Hne2 [Hne3 [Hrec HeqGmid]]]]]]]] ] ] ]; try discriminate Heqv2.
      * (* y already resolved directly : Gam y = Con c zs, Gmid = Gam --
           Gam x = Gam y now holds, closed by fwdchase_con *)
        subst Gmid.
        assert (Hxy : Gam x = Gam y) by (rewrite Hx; rewrite Hcase1; reflexivity).
        exact (NEval_fwd_transfer_fwdchase_con P G Gam HGam x y HGx Hxy
                 brs c zs ys body Gam' v' Hcase1 HIn Hlen Hrec2).
      * (* y needs further forcing : OPEN, see the discussion above this
           lemma -- needs the missing NEval-soundness-relative-to-G fact. *)
        admit.
  - (* Nat-Guess : y resolves to a self-loop / free variable -- OPEN, see
       the discussion above this lemma. *)
    admit.
Admitted.

(* Shrinking the guard is always safe: F only ever appears in N_VarExp's
   own `~In x F` side condition, so a SMALLER guard only makes that side
   condition EASIER to satisfy -- never harder. *)
Lemma NEval_F_shrink :
  forall P F1 F2, (forall w, In w F2 -> In w F1) ->
  forall Gam e Gam' v, NEval P F1 Gam e Gam' v -> NEval P F2 Gam e Gam' v.
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
    | F0 G x1 y1 G1 v i Hi Hrec IH
    | F0 G z c zs brs ys body G1 v G2 Hrec1 IH1 HIn Hlen Hrec2 IH2
    | F0 G z G1 z' c1 ys1 body1 brs G2 v ws Hrec1 IH1 Hhd Hlen HND Hfr Hrec2 IH2
    ]; intros F2 Hsub.
  - apply N_VarCons. exact Hz.
  - apply N_VarSelf. exact Hz.
  - apply N_VarFree. exact Hz.
  - eapply N_VarExp.
    + intro Hin. apply HzF. apply Hsub. exact Hin.
    + exact Hz.
    + exact Hne1.
    + exact Hne2.
    + exact Hne3.
    + apply IH. intros w Hin.
      destruct Hin as [Heq | Hin]; [left; exact Heq | right; apply Hsub; exact Hin].
  - apply N_ValFree.
  - apply N_ValCon.
  - eapply N_Fun; [exact HPf | exact Hlen | exact Hinj | exact Hmatch | exact Hfresh | apply IH; exact Hsub].
  - apply N_Let; [exact HzFresh | apply IH; exact Hsub].
  - eapply N_Or; [exact Hi | apply IH; exact Hsub].
  - eapply N_Select; [apply IH1; exact Hsub | exact HIn | exact Hlen | apply IH2; exact Hsub].
  - eapply N_Guess; [apply IH1; exact Hsub | exact Hhd | exact Hlen | exact HND | exact Hfr | apply IH2; exact Hsub].
Qed.
