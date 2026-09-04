# Theorem 2 Process Notes: Graph/Natural Semantics Correspondence in Rocq

## How to use this document

This is a **raw, comprehensive process record**, not a polished writeup. It exists to capture
everything that happened while trying to prove "Theorem 2" (the correspondence between graph
reduction and natural/heap semantics for FlatCurry) in Rocq/Coq, across `curry.v` and
`curry_test_leftmost.v`, in enough detail that it can later be condensed into something shorter
and more readable. It is also meant to double as a Rocq/Coq learning reference: Part 2 catalogs
every distinct tactic and proof idiom actually used, with real examples pulled from the files.

Nothing here is edited down for concision on purpose. Read Part 1 top to bottom for the story;
use Part 2 as a glossary when a tactic name shows up in Part 1 and you want the "why."

All file/line references are to `curry.v` and `curry_test_leftmost.v` in this directory, as of
the end of the session this document was written in. Line numbers will drift as the files change.

---

# Part 1: The Proof Process

## 1. The setup: why a correspondence theorem is needed at all

The project formalizes two different operational semantics for a restricted fragment of
FlatCurry (first-order, fully applied — no `apply`/PART nodes, no literals), following
`lsfa24.tex` and Hanus et al.'s "A natural semantics for functional logic programs":

- **The graph semantics (`GEval`)**, `curry.v` lines ~231-293, Figures 8 & 9 of `lsfa24.tex`.
  This is the "real compiler" model: a program state is a graph `Graph := heap GNode`, where
  each node is either a direct expression (`GExpr e`) or a forwarding pointer to another
  location (`GFwd x`). Evaluating an expression can *mutate* the graph in place — in
  particular, forcing a shared thunk once and having every other reference to it observe the
  same, now-resolved value via a forward pointer. This is what makes graph reduction efficient
  (no re-evaluation of shared work) and is the standard implementation technique for lazy
  functional languages.

- **The natural/heap semantics (`NEval`)**, `curry.v` lines ~328-420, Fig. 2 of
  `natural_semantics.pdf`. This is the more "textbook" substitution/heap semantics: a heap
  `NHeap := heap Blk` maps variables to (unevaluated or partially evaluated) expressions, and
  evaluation judgments look like `NEval F Gam e Gam' v` — "starting from heap `Gam`, with `F`
  the set of locations currently being forced (for cycle/black-hole detection), expression `e`
  evaluates to value `v`, producing heap `Gam'`."

Both operate over the exact same term grammar `Blk`/`Expr0` (this is deliberate — the paper's
own Theorem 2 statement uses the same `e` on both sides). The two models are meant to describe
*the same* language, so a correctness theorem connecting them — "if the graph machine reaches a
result, the natural-semantics machine reaches a corresponding result" — is exactly the kind of
soundness statement you need to trust that the (efficient, sharing-based) graph implementation
actually implements the (simple, substitution-based) specification semantics. That is
**Theorem 2** of `lsfa24.tex`, and it is the object of this whole file.

The shared syntax:

```coq
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
```

(Note the constructor order: `Blk` is `BLet | BCase | BExpr`, and `Expr0` is
`EVar | EBot | EFree | EChoice | EFun | ECon`. This matters a great deal for `destruct`/`induction`
patterns — see Part 2.)

### `GEval`

```coq
Inductive GEval : Graph -> Blk -> Graph -> GNode -> Prop :=
| G_Bot : forall G, GEval G (BExpr EBot) G (GExpr EBot)
| G_Free : forall G, GEval G (BExpr EFree) G (GExpr EFree)
| G_Con : forall G c args, GEval G (BExpr (ECon c args)) G (GExpr (ECon c args))
| G_Choice : forall G x y, GEval G (BExpr (EChoice x y)) G (GExpr (EChoice x y))
| G_Var : forall G x, GEval G (BExpr (EVar x)) G (GFwd x)
| G_Fun : forall G G1 f args ps body v s,
    P f = Some (ps, body) -> length ps = length args -> injective s ->
    (forall i x a, nth_error ps i = Some x -> nth_error args i = Some a -> s x = a) ->
    (forall y, ~ In y ps -> G (s y) = None) ->
    GEval G (rename_b s body) G1 v ->
    GEval G (BExpr (EFun f args)) G1 v
| G_Let : forall G G1 x e k v,
    G x = None ->
    GEval (hupd G x (GExpr e)) k G1 v ->
    GEval G (BLet x e k) G1 v
| G_CaseBot : forall G x brs, G x = Some (GExpr EBot) -> GEval G (BCase x brs) G (GExpr EBot)
| G_CaseFwd : forall G x y brs G1 v,
    G x = Some (GFwd y) -> GEval G (BCase y brs) G1 v -> GEval G (BCase x brs) G1 v
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
    G x = Some (GExpr (ECon c zs)) -> List.In (c, ys, body) brs -> length ys = length zs ->
    GEval G (rename_b (zipsubst ys zs) body) G1 v ->
    GEval G (BCase x brs) G1 v
| G_CaseConFree : forall G x c1 ys1 body1 brs G1 v ws,
    G x = Some (GExpr EFree) -> hd_error brs = Some (c1, ys1, body1) ->
    length ws = length ys1 -> NoDup ws -> (forall w, In w ws -> G w = None) ->
    GEval (hupd_list (hupd G x (GExpr (ECon c1 ws))) ws (map (fun _ => GExpr EFree) ws))
          (rename_b (zipsubst ys1 ws) body1) G1 v ->
    GEval G (BCase x brs) G1 v.
```

Key things to notice, because they drive everything downstream:

- `G_Var` and `G_Choice` evaluate a bare variable/choice expression to a `GFwd`/unresolved
  `GExpr` value **without touching the graph at all** — `G` is literally unchanged (`G1 = G`,
  syntactically the same variable in the conclusion). This "no-op" property turns out to be
  the single most useful fact discovered this session (§7 below).
- `G_CaseChoice` always forwards to the **first** operand `y` (never `z`) — the graph machine
  is deterministic here. This is the source of the whole `NEval_left` detour (§4).
- `G_CaseFun` is the one constructor where a case's scrutinee has genuinely unevaluated content
  (`EFun f args`) that must first be reduced (`vx`), and only *then* does evaluation continue by
  re-casing the *same* location `x`, now holding `vx`. This double-nested-evaluation shape is
  the hardest part of everything that follows.

### `NEval`

```coq
Inductive NEval : list var -> NHeap -> Blk -> NHeap -> Blk -> Prop :=
| N_VarCons : forall F G x c args,
    G x = Some (BExpr (ECon c args)) -> NEval F G (BExpr (EVar x)) G (BExpr (ECon c args))
| N_VarSelf : forall F G x,
    G x = Some (BExpr (EVar x)) -> NEval F G (BExpr (EVar x)) G (BExpr (EVar x))
| N_VarFree : forall F G x,
    G x = Some (BExpr EFree) -> NEval F G (BExpr (EVar x)) (hupd G x (BExpr (EVar x))) (BExpr (EVar x))
| N_VarExp : forall F G x e G1 v,
    ~ In x F -> G x = Some e ->
    (forall c args, e <> BExpr (ECon c args)) -> e <> BExpr (EVar x) -> e <> BExpr EFree ->
    NEval (x :: F) G e G1 v ->
    NEval F G (BExpr (EVar x)) (hupd G1 x v) v
| N_ValFree : forall F G, NEval F G (BExpr EFree) G (BExpr EFree)
| N_ValCon : forall F G c args, NEval F G (BExpr (ECon c args)) G (BExpr (ECon c args))
| N_Fun : forall F G G1 f args ps body v s, (* same shape as G_Fun *) ...
| N_Let : forall F G G1 x e k v,
    G x = None -> NEval F (hupd G x (let_content x e)) k G1 v -> NEval F G (BLet x e k) G1 v
| N_Or : forall F G x y G1 v i,
    (i = x \/ i = y) -> NEval F G (BExpr (EVar i)) G1 v -> NEval F G (BExpr (EChoice x y)) G1 v
| N_Select : forall F G x c zs brs ys body G1 v G2,
    NEval F G (BExpr (EVar x)) G1 (BExpr (ECon c zs)) -> List.In (c, ys, body) brs -> length ys = length zs ->
    NEval F G1 (rename_b (zipsubst ys zs) body) G2 v -> NEval F G (BCase x brs) G2 v
| N_Guess : forall F G x G1 x' c1 ys1 body1 brs G2 v ws, ...
```

Key things to notice:

- `F : list var` is the **black-hole guard**: the set of locations currently "under active
  force" on the current derivation's call stack. `N_VarExp` is the only rule that forces a
  *named* heap location by looking up its content; it's the only rule that (a) checks the
  location isn't already in `F` and (b) pushes it onto `F` for its own recursive premise. This
  guard was added *after* a concrete counterexample (`blackhole_counterexample`, §3.3 below)
  showed the unguarded semantics let a thunk be evaluated twice concurrently.
- `N_VarExp`'s memoization: once forcing `x` finishes with result `v`, it writes `v` directly
  into `x`'s own heap slot (`hupd G1 x v`) — **regardless of how many intermediate variable
  hops it took to get there.** This "skip-ahead" memoization is the root cause of the
  `HeapCorr2`/`HeapCorr3` split described in §5.
- `N_Or`'s nondeterminism: `i = x \/ i = y` — either choice operand may be picked. This is the
  source of everything in §4.
- `let_content` (used by `N_Let`): `let_content x EFree = BExpr (EVar x)`, else `BExpr e`. A
  `free` right-hand side becomes an immediate self-loop — "free variables are represented as a
  variable that is mapped to itself in the heap," matching the paper directly.

---

## 2. The correspondence relation: `CorrE`/`HeapCorr`, and its own history

To even *state* Theorem 2 you need a notion of "this natural-semantics heap `Gam` correctly
represents this graph `G`." That notion had its own non-trivial history, entirely within
`curry.v`, *before* `curry_test_leftmost.v` (and the `NEval_left` detour) even existed.

### `ContractLoc`: chasing forward pointers to a canonical value

```coq
Inductive ContractLoc (G : Graph) : var -> var -> Prop :=
| CL_Here : forall x e, G x = Some (GExpr e) -> ContractLoc G x x
| CL_Fwd  : forall x y z, G x = Some (GFwd y) -> ContractLoc G y z -> ContractLoc G x z.
```

`ContractLoc G x y` means: starting from `x`, following `GFwd` pointers, you eventually land on
`y`, and `y` itself holds a direct value (`GExpr`), not another forward pointer. This is "the
canonical, forward-contracted target" of `x`. `ContractLocN` (line ~566) is the same relation
indexed by hop-count, used when an explicit measure/induction on chain length is needed.

### `CorrE`: what counts as a valid natural-semantics representation of one location

```coq
Inductive CorrE (G : Graph) : var -> Blk -> Prop :=
| CorrE_Con : forall x c args, G x = Some (GExpr (ECon c args)) -> CorrE G x (BExpr (ECon c args))
| CorrE_Free : forall x, G x = Some (GExpr EFree) -> CorrE G x (BExpr (EVar x))
| CorrE_Fun : forall x f args, G x = Some (GExpr (EFun f args)) -> CorrE G x (BExpr (EFun f args))
| CorrE_Choice : forall x y z, G x = Some (GExpr (EChoice y z)) -> CorrE G x (BExpr (EChoice y z))
| CorrE_VarThunk : forall x z, G x = Some (GExpr (EVar z)) -> CorrE G x (BExpr (EVar z))
| CorrE_Bot : forall x, G x = Some (GExpr EBot) -> CorrE G x (BExpr EBot)
| CorrE_FwdHere : forall x y, G x = Some (GFwd y) -> CorrE G x (BExpr (EVar y))
| CorrE_FwdAchievedCon : forall x y z c args,
    G x = Some (GFwd y) -> ContractLoc G y z -> G z = Some (GExpr (ECon c args)) ->
    CorrE G x (BExpr (ECon c args)).
```

```coq
Definition HeapCorr (G : Graph) (Gam : NHeap) : Prop :=
  forall x, match G x with
            | None => Gam x = None
            | Some _ => exists b, Gam x = Some b /\ CorrE G x b
            end.
```

For a *direct* graph node (`G x = Some (GExpr e)`), `Gam`'s witness must be the literal
translation of `e`. For a *forwarding* node (`G x = Some (GFwd y)`), `Gam`'s witness can be
either:
- the lazy, one-hop alias `EVar y` (`CorrE_FwdHere`) — "`x`'s heap slot just says 'go look at
  `y`'", or
- (if `y`'s own canonical target, reached via `ContractLoc`, is already an achieved
  constructor) the constructor value directly (`CorrE_FwdAchievedCon`) — "`x`'s heap slot has
  already been memoized to the fully-resolved answer, skipping the pointer chase."

This is **deliberately multi-valued** — several different `b`s can be valid witnesses for the
same `x` — because `N_VarExp` always eagerly memoizes to the fully-resolved value the moment it
finishes forcing something, while the graph only mutates `GFwd` nodes via explicit rules
(`G_CaseFun`, `G_CaseChoice`, ...), so a natural-semantics heap can legitimately be anywhere on
the spectrum from "as lazy as the graph's own indirection" to "fully forced."

Note explicitly: `CorrE` has **no case for "witness is achieved via a multi-hop chase where the
intermediate hop is itself still lazy."** This restriction is deliberate and is the direct
cause of the entire `HeapCorr3` story in §5.

### 2.1 Three historical counterexamples that shaped `CorrE`'s current definition

`CorrE` did not start out this restricted. It originally had one fully general constructor:

```coq
(* the OLD, now-removed constructor *)
CorrE_FwdChase : G x = GFwd y -> CorrE G y b -> CorrE G x b   (* b arbitrary *)
```

— i.e., a forwarding location's witness could be **any** valid witness of its target, chased
transitively, with *no restriction on `b`'s shape at all* (not just achieved values, but raw,
in-progress content like an unevaluated `EFun` call or an unforced `EVar` alias). Three
concrete counterexamples, built and then removed from `curry.v` (their code is gone; their
full descriptions survive as "HISTORICAL NOTE" comments), showed this was unsound. All three
motivated the *same* fix.

**Counterexample A — `HeapCorr_update_not_general`** (comment at `curry.v` ~line 1148-1176).
Witness: `z` forward-points at `x` (`G z = GFwd x`); `x` currently holds `Bot`; `z`'s own
`Gam`-witness is *also* the literal `EBot` — a bare copy of `x`'s raw, non-terminal content,
justified by the old, fully general `CorrE_FwdChase`. Now mutate `x`'s content (e.g. `Bot`
resolving to a constructor, as `G_CaseFun`-style evaluation might do to some other location's
thunk): `z`'s witness is now stale, breaking `HeapCorr` at `z`. This showed `HeapCorr` is *not*
preserved by an arbitrary graph mutation — a real problem, because case rules like `G_CaseFun`
need to update an existing location's content mid-evaluation.

**Counterexample B — `NEval_confluence_unrestricted_is_false`** (comment at `curry.v`
~line 1295-1327). Witness: `G x = GFwd y`, and *separately* `G y = GExpr (EVar x)` — `y`'s own
direct content is literally the expression `EVar x`, an unforced `let y = x in ...`-style
alias pointing straight back at `x`. Under the old `CorrE_FwdChase`, `x` gets **two** valid
witnesses: the direct alias `EVar y` (`FwdHere`), *and* — by chasing through `y`'s raw
`VarThunk` content — the self-loop `EVar x`. A `Gam` that picks the self-loop witness for `x`
finishes immediately (`N_VarSelf`); a `Gam` that picks the alias witness recurses into forcing
`y`, whose content is `EVar x`, landing back on the exact same judgment — a genuinely
non-terminating `NEval` derivation (formally witnessed by `NEval_var_cycle_stuck`, `curry.v`
~line 1276). So two heaps that are *both* valid `HeapCorr` representations of the same graph
could have **different termination behavior** on the same expression — a much more serious
problem than staleness, since it breaks the very notion of "the heap represents the graph."

**Counterexample C — the `fc_*` section** (comment at `curry.v` ~line 2841-2887, ~650 lines of
now-removed Coq code). Witness: both `x` and `y` hold the *identical* raw, non-terminal content
`f(x)` (a self-referential function call, via `let x = f(x) in ...`-style sharing — genuinely
two different locations independently bound to the same expression object, not aliasing). `G`
has `x` forward to `y`, and `y`'s own direct content really is `EFun f (x :: nil)`, so
`Gam x = Gam y` was a valid `CorrE_FwdChase` witness. The proof showed: forcing `y` can reach a
constructor `R` (by picking one `Or`-choice at the top level, then escaping via a *different*
`Or`-choice one level down, while `x` is momentarily unguarded); but forcing `x` directly can
only ever reach a *different* constructor `K`, because the same escape route would require
re-entering `x` while `x` is already in its own guard — impossible. This is exactly
`NEval_fwd_transfer`'s fully general "chase, target needs further forcing" case being *false*.

**The fix, once, for all three.** `CorrE_FwdChase` was replaced by the two constructors shown
above: `CorrE_FwdHere` (direct one-hop alias only) and `CorrE_FwdAchievedCon` (skip-ahead
*only* to a value that's already achieved — a real constructor — reached via `ContractLoc`, not
to arbitrary raw content). In each of the three counterexamples, the very first hypothesis
(`HeapCorr G Gam`, using the *shared/stale/cyclic* witness) can no longer even be established
under the new `CorrE`, because a raw, non-terminal, or self-referential witness for a
forwarding location is no longer `CorrE`-valid at all. All three theorems and their supporting
apparatus were deleted rather than salvaged, since the entire point of each was to exploit
exactly the generality the fix removes.

Two follow-up facts about counterexample B's *graph shape specifically* were kept (they are
independent of `CorrE` and still hold): `GEval_case_chase_not_var_thunk` (`curry.v` ~1347) shows
that a *complete* `GEval` `BCase` derivation can never chase through a location whose content is
a bare, unforced `EVar` — there is no `G_CaseVar` rule, so the derivation simply wouldn't exist
as a Coq proof term if it tried — and `confluence_counterexample_graph_unreachable_by_case`
(~1391) confirms the exact 2-node graph from counterexample B is unreachable from any complete
`GEval` derivation in the first place. This mattered later for `CorrE_selfloop_means_free`
(~1458): once you know a location is reached via a genuine, *completed* case-forcing
derivation, a self-loop witness for it is guaranteed to mean the location is really free (not a
content-cycle artifact), because the content-cycle reading is exactly what
`GEval_case_chase_not_var_thunk` rules out.

### 2.2 `WellFoundedFwd`

```coq
Definition WellFoundedFwd (G : Graph) : Prop :=
  forall w y, G w = Some (GFwd y) -> exists z, ContractLoc G w z.
```

Every forward chain in the graph terminates at a real, non-`None` location. `HeapCorr`'s bare,
pointwise definition has no way to rule out a dangling forward pointer (`G p = GFwd x` while
`G x = None`) on its own; several later lemmas (e.g. `HeapCorr2_extend`, `curry_test_leftmost.v`
~380) need `WellFoundedFwd G` as an explicit side hypothesis specifically to exclude that case
when reasoning about a freshly-extended heap.

---

## 3. `theorem2`'s own proof attempt: exactly where it gets stuck

```coq
Theorem theorem2 :
  forall P G e G' v,
    GEval P G e G' v ->
    forall c args, CorrV G' v (BExpr (ECon c args)) ->
    forall Gam, HeapCorr G Gam ->
    exists Gam', NEval P nil Gam e Gam' (BExpr (ECon c args)) /\ HeapCorr G' Gam'.
Proof.
  intros P G e G' v H.
  induction H as [ ... ]; intros c0 args0 Hcorr Gam HGam.
  - (* G_Bot *) inversion Hcorr.
  - (* G_Free *) inversion Hcorr.
  - (* G_Con *) ... exists Gam. split; [apply N_ValCon | exact HGam].
  - (* G_Choice *) inversion Hcorr.
  - (* G_Var *) ... eapply force_var; eauto.
  - (* G_Fun *) destruct (IH c0 args0 Hcorr Gam HGam) as [Gam1 [HNE HHC]]. ...
  - (* G_Let *) ... apply HeapCorr_extend ... apply N_Let ...
  - (* G_CaseBot *) inversion Hcorr.
  - (* G_CaseFwd *) admit.  (* STUCK *)
  - (* G_CaseFun *) admit.  (* STUCK *)
  - (* G_CaseChoice *) admit.  (* STUCK *)
  - (* G_CaseCon *) ... eapply N_Select; [apply N_VarCons; exact Hbx | ...] ...
  - (* G_CaseConFree *) ... eapply N_Guess; [apply N_VarSelf; exact Hbx | ...] ...
Admitted.
```

**This is stated over a fully general `e` — not restricted to `BCase`-rooted expressions.** It
is proved by `induction H` on the `GEval` derivation directly (no `remember`/`revert` dance
needed here, because the induction target `e` is never constrained to a specific syntactic
shape at the top — every constructor is a live possibility for the top-level `e`). That gives an
automatic induction hypothesis `IH` for every recursive premise of every constructor, "for
free," matching the *same* general statement. This point matters enormously later (§8): it's
exactly what a narrower, `BCase`-only lemma *doesn't* get.

**What actually works, with no admits:** `G_Con`, `G_Var` (via `force_var`, using
`CorrVTerm_con_inv` to unpack the `CorrV` hypothesis into a concrete `ContractLoc` witness),
`G_Fun` (mechanical: apply `IH`, port the freshness side-condition, wrap in `N_Fun`), `G_Let`
(mechanical: extend `HeapCorr` via `HeapCorr_extend`, apply `IH`, wrap in `N_Let`), `G_CaseCon`
(direct: `Gam_from_con` gives the scrutinee's Nat-heap witness, `N_Select` + `N_VarCons`, apply
`IH`), `G_CaseConFree` (direct: `Gam_from_free`, extend the heap at the fresh guess-variables via
`HeapCorr_extend_free_list`, `N_Guess` + `N_VarSelf`, apply `IH`).

**What's vacuous, with no admits:** `G_Bot`, `G_Free`, `G_Choice`, `G_CaseBot` — in each case the
*given* `CorrV G' v (Con c args)` hypothesis is immediately contradictory (`inversion Hcorr`
closes the goal), because `CorrV`'s only constructors (`CorrV_Direct`, requiring
`GExpr e = GExpr (ECon c args)` syntactically, and `CorrV_Fwd`, requiring a `GFwd` node with a
matching `CorrVTerm`) simply cannot match a bare `Bot`/`Free`/`Choice` value.

**What's stuck, all three for the same reason:** `G_CaseFwd`, `G_CaseFun`, `G_CaseChoice`. The
in-file diagnosis, written directly into the proof as a comment (`curry.v` ~2283-2306), is
precise and important:

> Applying `IH` gives a full `NEval` derivation forcing `BCase y brs`; inverting it
> (Select/Guess) yields a concrete sub-derivation `NEval Gam (EVar y) Gam0 hnf` forcing `y` to
> *some* head-normal-form `hnf`. If `Gam[x]`'s `CorrE` witness happens to be the one-hop alias
> `EVar y` (`CorrE_FwdHere`), we're done immediately — `N_VarExp` on `x` directly reuses that
> exact sub-derivation. The problem is the *other* branch: if `Gam[x]`'s witness came via a
> deeper skip-ahead (`Gam` already holds something more resolved than a bare alias to `y`),
> reusing the fact requires a **graph-level** fact ("`G`'s canonical target for `x`/`y` is
> Con-shaped") that can only be extracted from the given `NEval` derivation via a **general
> soundness lemma of the shape "`NEval` forcing something `+ HeapCorr` implies a matching
> `CorrE`/`HeapCorr` fact,"** proved by induction on the *given* `NEval` derivation. That lemma
> is not "more of the same" — its own `N_Fun`/`N_Let`/`N_Or` cases require exactly the same kind
> of case-by-case correspondence work as Theorem 2 itself, just in the opposite direction. It's a
> separate, comparably-sized theorem ("Theorem 2, converse") that wasn't built.

`G_CaseFun` is explicitly diagnosed as reducing to the *same* gap (its continuation, after
resolving the function call's own result `vx`, dispatches into exactly `G_CaseCon`'s (done),
`G_CaseConFree`'s (done), or `G_CaseChoice`'s/`G_CaseFwd`'s (stuck) argument, depending on
`vx`'s shape), and `G_CaseChoice` is diagnosed as literally the same root cause as `G_CaseFwd`
(it also redirects to `BCase y brs` after setting `x := GFwd y`).

**This "Theorem 2, converse" gap — a partial, direction-reversed soundness fact needed
specifically to relate a Nat-heap forcing event back to the graph's own structure — is exactly
what all of the machinery in `curry_test_leftmost.v` (`ContractLoc`-based lemmas, `HeapCorr2`,
`HeapCorr3`, `NEval_left_force_free_sound`, the `theorem2_left` design in §8) has been trying to
build, one restricted piece at a time.** Everything from here on is, in one way or another, an
attempt to construct that missing converse fact (or enough of a substitute for it) without
having to prove it in full, unrestricted generality.

---

## 4. `NEval_left`: fixing the `EChoice` nondeterminism

Comment at the very top of `curry_test_leftmost.v` (lines 5-30):

> `GEval` is a **deterministic** execution model (a real compiler has to be): `G_CaseChoice`
> only ever forwards to the first operand of an `EChoice`, never the second — there is no
> companion rule. `NEval`'s own `N_Or` is genuinely nondeterministic (`i = x \/ i = y`). So
> "`GEval` reaches `v` implies `NEval` reaches `v`" (theorem2 as stated) cannot be strengthened,
> and worse: `theorem2` **as literally stated is provably not fully provable** in the direction
> that matters, because `NEval` can take the branch `GEval` structurally never can.
>
> `NEval_left` is `NEval` with that extra nondeterminism removed: `N_Or` is forced to `i = x`
> (the first operand), exactly matching `G_CaseChoice`'s own bias. Every `NEval_left` derivation
> is trivially also a valid `NEval` derivation (`NEval_left_to_NEval`), so proving
> `GEval P G e G' v -> exists Gam', NEval_left P nil Gam e Gam' v'` is strictly sufficient to
> reprove `theorem2` exactly as stated.
>
> The reason to go via `NEval_left` rather than trying to patch `NEval` directly: the
> obstruction blocking `curry.v`'s own `NEval_fwd_transfer` is an inability to relate two
> *independent* evaluations of "the same" sub-expression — and every historical counterexample
> that exploited this (`blackhole_counterexample`, the `fc_*` section) did so by having an
> `Or`-choice pick *different* branches on the two evaluations. Removing `Or`'s nondeterminism
> removes that entire attack surface.

The one-line diff:

```coq
(* NEval's N_Or *)
| N_Or : forall F G x y G1 v i, (i = x \/ i = y) -> NEval F G (BExpr (EVar i)) G1 v ->
    NEval F G (BExpr (EChoice x y)) G1 v

(* NEval_left's NL_Or -- always the LEFT operand *)
| NL_Or : forall F G x y G1 v,
    NEval_left F G (BExpr (EVar x)) G1 v -> NEval_left F G (BExpr (EChoice x y)) G1 v
```

Everything else in `NEval_left`'s inductive definition (`NL_VarCons`, `NL_VarSelf`,
`NL_VarFree`, `NL_VarExp`, `NL_ValFree`, `NL_ValCon`, `NL_Fun`, `NL_Let`, `NL_Select`,
`NL_Guess`) is a mechanical, structurally identical copy of `NEval`'s corresponding rule.
`NEval_left_to_NEval` (line 97) is a trivial induction showing any `NEval_left` derivation is
also an `NEval` derivation, picking `left; reflexivity` for the `NL_Or` case.

From this point on, the goal shifts to: **`GEval P G e G' v -> HeapCorr G Gam -> exists Gam',
NEval_left P nil Gam e Gam' v' /\ HeapCorr G' Gam'`** (with `HeapCorr` itself later strengthened
twice more — see §5).

---

## 5. Strengthening the correspondence: `HeapCorr2`, then `HeapCorr3`

### 5.1 `ChainConsistent` and `HeapCorr2` — a concrete, worked counterexample

Around line 298-365 of `curry_test_leftmost.v`, a concrete graph/heap pair is built and proven
to satisfy `HeapCorr` (bare) while exhibiting a pathology:

```coq
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
Proof. (* ~20 lines, one case per location, via CorrE_Con / CorrE_FwdHere / CorrE_FwdAchievedCon *) ... Qed.
```

The graph is a two-hop forward chain `2 -> 1 -> 0`, with `0` holding the achieved constructor.
`ex_Gam` gives location `1` the lazy, direct alias witness (`EVar 0`, valid via `CorrE_FwdHere`)
— but gives location `2` the **achieved constructor directly**, skipping `1` entirely (valid via
`CorrE_FwdAchievedCon`, since `ContractLoc` from `2` genuinely does chase to `0`). Both are
individually legal `CorrE` witnesses. But intuitively this is backwards: in any real execution,
memoizing `2`'s value would require first forcing through `1`, so `1`'s own witness should
*already* be promoted to the constructor by the time `2`'s is. `HeapCorr` — a purely pointwise
definition — has no way to see this, since `CorrE` only relates a location to the *graph*, never
to a sibling location's own witness.

```coq
Definition ChainConsistent (G : Graph) (Gam : NHeap) : Prop :=
  forall x y, G x = Some (GFwd y) ->
    forall c args, Gam x = Some (BExpr (ECon c args)) -> Gam y = Some (BExpr (ECon c args)).

Definition HeapCorr2 (G : Graph) (Gam : NHeap) : Prop := HeapCorr G Gam /\ ChainConsistent G Gam.

Lemma ex_x_ahead_of_y_not_chain_consistent : ~ ChainConsistent ex_G ex_Gam.
Proof. intro HCC. specialize (HCC 2 1 eq_refl 0 nil eq_refl). discriminate HCC. Qed.
```

`ChainConsistent` says: if `x` forwards to `y`, and `Gam` has *already* promoted `x`'s witness
to an achieved constructor, then `Gam` must have *already* promoted `y`'s witness too — no
"witness gets ahead of its own target" pathology. `ex_x_ahead_of_y_not_chain_consistent` confirms
this specific example genuinely violates it (`ex_Gam 2 = Con`, but `ex_Gam 1 = EVar 0`, not
`Con`), confirming the strengthening actually bites (rules out something `HeapCorr` alone
allowed). `HeapCorr2 = HeapCorr /\ ChainConsistent` is the strengthened invariant used pervasively
through the middle portion of the file (`HeapCorr2_extend`, `HeapCorr2_update_to_direct`,
`HeapCorr2_update_to_fwd_lazy`, `HeapCorr2_update_achieved`, and everything built on top).

### 5.2 `HeapCorr3` — accommodating genuine multi-hop memoization

Even with `ChainConsistent` added, `HeapCorr2` still inherits `CorrE`'s original limitation:
`CorrE_FwdAchievedCon`'s skip-ahead is **exactly one hop** — it requires `x`'s own immediate
forward target `y` to sit on a `ContractLoc` chase to the constructor, but says nothing about
`x`'s witness being validly skip-ahead if the achieved value is reached by chasing *through*
`y`'s own further forwarding, when `y` itself is *not yet* memoized past its own first hop.

This is not a corner case — it's what actually happens whenever `N_VarExp`'s recursive premise
itself bottoms out through **more than one** further layer of `N_VarExp` before finally
resolving. Concretely: suppose the natural semantics is asked to force `x`, and `Gam x = EVar y`
(one lazy Nat-heap hop). `N_VarExp` recurses into forcing `y`. Suppose `y` *itself* is not
directly a constructor but forces through several more variables before finally landing on a
constructor at some `z`. When this whole recursive force finishes, the **outer** call
(`x`'s own `N_VarExp`) memoizes `x`'s slot directly to the final constructor — it does not
bother rewriting `y`'s slot (or any of the intermediate slots) to reflect that they, too, are now
resolved; each of *those* forces already independently memoized their own slot when *their*
own `N_VarExp` calls returned, via the exact same mechanism, one layer at a time. So after a
chain of forces finishes, you get a chain of individually-memoized slots — which is fine and
`HeapCorr2`-representable. The genuinely awkward case is when, at the point a *fact about the
correspondence* needs to be established (mid-proof, not mid-execution), you are handed a
situation where `Gam`'s witness for some location `x` has *already* been promoted to the
achieved constructor while the *graph's own* forward chain from `x` to that constructor is
still more than one hop long — i.e., `x`'s own immediate graph-level target `y` is *not itself*
the constructor. `CorrE_FwdAchievedCon` structurally cannot witness this, because it requires
`G y = Some (GExpr (ECon c args))` directly, not "`y` eventually chases to a constructor."

This is documented precisely in the comment above `NEval_left_fwd_transfer_fwdhere_free`
(`curry_test_leftmost.v` ~2109-2134):

> Forcing `x` (via `NL_VarExp`) is forced to memoize `x` directly to `EVar x'` (skipping `y`) —
> this is sound (both `x` and `y` still chase, via pure Nat-heap aliasing, to whatever `x'`
> eventually achieves) but is **not a shape plain `CorrE`/`HeapCorr2` can certify** — so the
> conclusion here is `HeapCorr3`, not `HeapCorr2`. ... `y`'s own graph-level forward chain
> (however many `GFwd` hops — `G_CaseFun`/`G_CaseFwd` never re-compress an intermediate hop, so
> this is genuinely multi-hop in general, not a single edge) ...

The fix — `CorrE3`/`HeapCorr3` (lines 2060-2107):

```coq
Lemma ContractLoc_first_hop : ...   (* small helper *)
Lemma ContractLoc_trans : ...       (* ContractLoc composes across hops *)

Definition CorrE3 (G : Graph) (Gam : NHeap) (x : var) (b : Blk) : Prop :=
  CorrE G x b \/
  (exists y0 z c args, G x = Some (GFwd y0) /\ ContractLoc G y0 z /\
     G z = Some (GExpr (ECon c args)) /\ VarChase Gam x (BExpr (ECon c args))).

Definition HeapCorr3 (G : Graph) (Gam : NHeap) : Prop :=
  forall x, match G x with
            | None => Gam x = None
            | Some _ => exists b, Gam x = Some b /\ CorrE3 G Gam x b
            end.

Lemma HeapCorr_to_HeapCorr3 : forall G Gam, HeapCorr G Gam -> HeapCorr3 G Gam.
Lemma HeapCorr2_to_HeapCorr3 : forall G Gam, HeapCorr2 G Gam -> HeapCorr3 G Gam.
```

`CorrE3` adds a third option beyond plain `CorrE`'s cases: even when `x`'s witness doesn't
directly satisfy `CorrE`, it's accepted as long as (a) there is *some* graph-side forward chain
of *any length* from `x` reaching a location holding an achieved constructor (`G x = GFwd y0`,
`ContractLoc G y0 z`, `G z = Con c args` — arbitrary hop count, not just one), and (b) there's a
matching Nat-heap-side chase (`VarChase`, a purely Nat-heap alias-hop relation, not referencing
the graph at all) from `x` to a memoized witness for that same constructor. `ChainConsistent`'s
ordering discipline is dropped entirely — `HeapCorr3` does not require it. `HeapCorr2` implies
`HeapCorr3` (never the reverse); `HeapCorr3` is strictly weaker and easier to establish, at the
cost of being weaker as a foundation for further proof (see §8.3 for why this asymmetry became a
central design problem).

**Summary of the two strengthenings, side by side:**

| | What it adds over the previous notion | What it costs |
|---|---|---|
| `HeapCorr2 = HeapCorr /\ ChainConsistent` | Forbids a forwarding source's witness from being "ahead of" its own immediate target's witness | Nothing extra to establish beyond `HeapCorr` + the ordering discipline (still one-hop skip-ahead only) |
| `HeapCorr3` | Allows a witness to be validated via a graph-side chase of **arbitrary** hop length, matched by a pure Nat-heap alias-chase | Drops `ChainConsistent`'s ordering discipline entirely; genuinely weaker as an ambient invariant (see §8.3) |

---

## 6. The `NEval_left_fwd_transfer_*` lemma family

Once `NEval_left` and `HeapCorr2`/`HeapCorr3` exist, the natural next step is rebuilding
`curry.v`'s stuck `NEval_fwd_transfer` (the fact `theorem2`'s `G_CaseFwd` case needed) for
`NEval_left`. This turned out to split into several separately-provable pieces, matching the
four-way case split of `NEval_left_evar_shape` (which constructor of `NEval_left` actually
produced a given "force this variable" derivation — see Part 2 §T2):

- **`NEval_left_fwd_transfer_fwdhere_con`** (line 1833) — `x`'s witness is the direct one-hop
  alias `EVar y` (`CorrE_FwdHere`), and forcing `y` reaches a **constructor**. Fully proven,
  `Qed`. This is the analogue of the case `curry.v`'s own stuck proof said *would* work.
- **`NEval_left_fwd_transfer_fwdchase_con`** (line 2003) — `x`'s witness is a direct *copy* of
  `y`'s own already-achieved constructor witness (`Gam x = Gam y`, both already `Con`). Fully
  proven, `Qed` — genuinely trivial once stated this way, since `x` is already the constructor.
- **`NEval_left_fwd_transfer_fwdhere_free`** (line 2135) — the free-variable-result analogue of
  the `fwdhere_con` case: `x`'s witness is `EVar y`, and forcing `y` reaches a free variable
  `x'` rather than a constructor. Two sub-cases: `x' = y` (trivial, no promotion needed) and
  `x' <> y` (the multi-hop memoization case described in §5.2 — concludes `HeapCorr3`, and takes
  a `ContractLoc G1 y x'` fact as an extra hypothesis rather than deriving it, since deriving it
  needs the graph-side half of the very correspondence being built). Fully proven, `Qed`.
- **`NEval_left_fwd_transfer_fwdhere_con_F`**, **`_fwdchase_con_F`** (lines 2531, 2611) — guard-
  generalized (`F` arbitrary, not fixed to `nil`) versions of the two `_con` lemmas above, needed
  so they compose under an outer guard (e.g. when reached from inside `NEval_left_force_free_sound`'s
  own `x0 :: F` context).
- **`NEval_left_fwd_transfer_F`** (line 2630) — the guard-generalized assembly combining the
  pieces above. **Has 1 admit** — the free-variable-result, guard-general case remains open.
- **`NEval_left_fwd_transfer`** (line 2870) — the `nil`-guard top-level assembly, used directly
  by `theorem2_G_CaseFwd_case`.

---

## 7. `GEval_case_gives_ContractLoc_deep`

`curry.v` already has `GEval_case_gives_ContractLoc` (line 1415): given a complete `BCase x brs`
derivation *starting* at graph `G`, `x` has a well-defined `ContractLoc` chase in `G` (the
*starting* graph). This session needed the same fact but relative to the **final** graph `G'`
(after the whole case evaluation, including any mutation `G_CaseFun`/`G_CaseChoice`/etc. perform
along the way):

```coq
Lemma GEval_case_gives_ContractLoc_deep :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v -> exists w, ContractLoc G' x w.
```

Proven by the identical induction-on-`GEval` shape as the original (`curry_test_leftmost.v` line
3156), mirroring curry.v's own proof structure but stating the conclusion about `G'` instead of
`G`. Fully proven, `Qed`, purely graph-side (no `NEval_left`/`Gam` involved at all). This became
one of the building blocks for the "self-forward is impossible" arguments used repeatedly later
(see §7.1 below and the `EVar` sub-case in §9).

---

## 8. `NEval_left_force_free_sound`: the restricted "Theorem 2, converse"

### 8.1 Purpose and shape

The comment directly above the lemma (`curry_test_leftmost.v` ~3541-3559) explains its scope
precisely:

> EXPLORATORY, INCOMPLETE: the Nat-heap half of the "second theorem" curry.v's own Theorem 2
> flagged as missing — restricted to exactly the shape needed here (forcing a CASE SCRUTINEE
> reaches a genuinely free variable), which is what lets `G_CaseFwd`/`G_CaseChoice`/`G_CaseCon`/
> `G_CaseConFree` go through with nothing beyond `HeapCorr2` + `CorrE_forced_shape` + the graph's
> own permanence facts — exactly mirroring `GEval_case_gives_ContractLoc_deep`'s own induction,
> one layer at a time, using `HeapCorr2` to keep the Nat-heap side in lockstep. Generalizing over
> the guard `F` (rather than fixing `nil`) is what makes the `G_CaseFwd`/`G_CaseChoice`
> recursive step free.
>
> `G_CaseFun` is where this stops being free: `NL_Fun`'s recursive premise fully resolves the
> renamed function body in ONE Nat-heap step, whereas the graph's own `G_CaseFun` only shallowly
> resolves it (`vx`) before recursing at the CASE level for possibly many more steps. Relating
> "`NL_Fun` forces the body to `x'`" to "the graph's own `vx`, chased via the continuation,
> reaches `x'` too" needs its own argument.

The statement:

```coq
Lemma NEval_left_force_free_sound :
  forall P G x brs G' v, GEval P G (BCase x brs) G' v ->
  forall Gam, HeapCorr2 G Gam ->
  forall F Gmid x', NEval_left P F Gam (BExpr (EVar x)) Gmid (BExpr (EVar x')) ->
  ContractLoc G' x x'.
```

In words: given a complete graph-side evaluation of `BCase x brs`, and a `HeapCorr2`-related
Nat-heap `Gam`, and a natural-semantics forcing of `x` that lands on a *free variable* `x'`
(not a constructor), then in the final graph `G'`, `x` genuinely `ContractLoc`-chases to `x'`.

Proved by `induction H` on the `GEval` derivation (after `remember (BCase x brs) as e eqn:He;
revert x brs He`, since `x`/`brs` are non-variable indices of `H`'s type — see Part 2 §T1).
This gives 12 branches; 7 are eliminated immediately by `try discriminate He` (since their
conclusions aren't `BCase`-shaped), leaving exactly the 6 `BCase`-producing constructors:
`G_CaseBot`, `G_CaseFwd`, `G_CaseFun`, `G_CaseChoice`, `G_CaseCon`, `G_CaseConFree`.

### 8.2 Status of the six top-level cases

- **`G_CaseBot`** — `Qed`. Vacuous: `Gam`'s own witness for `x0` (extracted via
  `CorrE_forced_shape`) is forced (via `Hb : ... = EBot`) to contradict the given "forces to a
  free variable" hypothesis, via a chain of `discriminate`s.
- **`G_CaseFwd`** — `Qed`. First derives `x0 <> y0` (the forward target isn't the source
  itself) using exactly the "reconstruct a hypothetical self-forward, then
  `GEval_case_gives_ContractLoc` + `ContractLoc_no_selfFwd` gives a contradiction" pattern (see
  §7.1 below — this is the *first* place that pattern appears). Then two sub-cases from
  `CorrE_forced_shape`: the `FwdHere` witness (`b = EVar y0`, matches `y0` exactly) recurses via
  the induction's own `IH`; the `FwdAchievedCon` witness contradicts the "reaches a free
  variable" hypothesis directly via `NEval_left_evar_not_con`.
- **`G_CaseChoice`** — `Qed`. Derives `x0 <> y0` the same way. Then, since `x0`'s content
  transitions from `EChoice y0 z0` to `GFwd y0` on the graph side, needs to transport the
  *Nat-heap* forcing across the *matching* transition — this is where
  `HeapCorr2_update_to_fwd_lazy` (build the updated `HeapCorr2` for `hupd G0 x0 (GFwd y0)`
  paired with `hupd Gam x0 (EVar y0)`) and `NEval_left_frame_guarded` (replay a derivation across
  a guarded location's content change — see Part 2 §T-frame-guarded) are used together.
- **`G_CaseCon`** — `Qed`. Vacuous by the same "contradicts the free-variable-result hypothesis"
  pattern as `G_CaseBot`.
- **`G_CaseConFree`** — `Qed`. `x0` is itself the free self-loop; `x' = x0` follows almost
  immediately.
- **`G_CaseFun`** — the hard one, discussed in full in §9.

### 7.1 The recurring "self-forward is impossible" argument

Used first in `G_CaseFwd`, then again for `EVar` (§9) and attempted (unsuccessfully — see §9)
for `EChoice`:

```coq
assert (Hxy_neq : x0 <> y0).
{ intro Heqxy; subst y0.
  destruct (GEval_case_gives_ContractLoc P (hupd G0 x0 (GFwd x0)) x0 brs0 G1 v1
              (G_CaseFwd P G0 x0 x0 brs0 G1 v1 Hgx0 Hrec)) as [w Hcl].
  exact (ContractLoc_no_selfFwd G0 x0 w Hcl Hgx0). }
```

The trick: *assume* the target equals the source (a bare self-forward node), reconstruct a
hypothetical `GEval` derivation over that self-forward graph via the very constructor being
proven, extract a `ContractLoc` witness from `GEval_case_gives_ContractLoc`, then contradict it
with `ContractLoc_no_selfFwd` (`curry.v`'s own fact: a location that genuinely `ContractLoc`s
cannot itself be a bare `GFwd x` node pointing at itself — chasing a self-loop can never
terminate). This works cleanly whenever the "problem shape" is itself a `GFwd` self-loop. It
does **not** directly work when the problem shape is a bare `EChoice` value referencing itself
as an operand (`G x0 = EChoice x0 w`), because `ContractLoc` treats *any* direct `GExpr` node —
including a self-referential `EChoice` — as an immediate, valid, non-contradictory target via
`CL_Here`. This distinction mattered directly in the `EChoice` sub-case of `G_CaseFun` (§9.5).

---

## 9. `G_CaseFun`: the eight sub-shapes, one at a time

The hard case. Once `x0`'s content is known to be `EFun f0 args0` (the function call), and the
derivation is unpacked into "evaluate the call" (`Hrec1g`) then "continue casing `x0` with the
result" (`Hrec2g`), the strategy is to unpack the **Nat-heap side's own** forcing of `x0`
(`Hrec1`, the lemma's third top-level hypothesis) using `NEval_left_evar_shape`, then
`NEval_left_fun_shape`, arriving at `Hrec3 : NEval_left P (x0::F) Gam (rename_b s body) G1'
(BExpr (EVar x'))` for the function's *own body* under the natural semantics' renaming `s`. The
proof then does `destruct (rename_b s body) as [z e0 k | z brs2 | e0] eqn:Hbodyshape` — three
shapes (`BLet`/`BCase`/`BExpr`), and the `BExpr` shape further splits into `EVar | EBot | EFree |
EChoice | EFun | ECon` — eight total sub-cases.

### 9.1 The three vacuous `BExpr` shapes: `EBot`, `EFree`, `ECon`

Proven trivially via bare `inversion Hrec3.` — no `NEval_left` rule can conclude
`BExpr EBot`/`BExpr EFree`/`BExpr (ECon ...)` reaches `BExpr (EVar x')` (a free variable), so the
hypothesis `Hrec3` is immediately contradictory once its shape is fixed.

### 9.2 `EVar w0`: fully closed

The key realization: **`G_Var` makes zero heap change.** If the function body itself is just a
bare variable reference, forcing it on the graph side is a no-op (`G' = G`, `vx = GFwd w0`,
syntactically). This sidesteps the entire "does `HeapCorr2` survive the nested function-body
evaluation" problem, because there is no evaluation *to* survive.

The argument, in order:

1. **Rename-preimage.** A new small helper:

   ```coq
   Lemma rename_b_evar_preimage :
     forall s body w0, rename_b s body = BExpr (EVar w0) ->
     exists y1, body = BExpr (EVar y1) /\ s y1 = w0.
   ```

   proven by `destruct body` then `destruct e` and `injection` — since `rename_b`/`rename_e0`
   are simple shape-preserving homomorphisms (they can only ever produce `EVar (s y1)` from an
   input that was itself `EVar y1`), this recovers the *unrenamed* body shape from its renamed
   image.

2. **The forced variable must be a function parameter.** `Hfresh2 : forall y, ~ In y ps ->
   Gam (s y) = None` (from `NEval_left_fun_shape`'s own output — the natural semantics'
   freshness guarantee for the function's *non*-parameter bound variables). Since `Hrec3`
   successfully forces `w0` (so `Gam w0 <> None`, extracted via `NEval_left_evar_shape`), `w0`
   cannot be `s y1` for a non-parameter `y1` — contrapositive of `Hfresh2` — so `y1` must be a
   parameter: `In y1 ps`.

3. **`s` and the graph-side renaming `sG` agree on parameters.** Both `NL_Fun` (Nat-heap side,
   giving `s`) and `G_Fun` (graph side, giving `sG`, via a new `GEval_fun_shape` helper mirroring
   `NEval_left_fun_shape`) satisfy the *same* "matches `args0` positionally" condition against
   the *same* `args0` (since both start from the *same* `EFun f0 args0` content, as established
   earlier in the proof). For any parameter `y1` (`In y1 ps`), `List.In_nth_error` gives a
   position `i`; both `s y1` and `sG y1` are forced to equal `nth_error args0 i`, hence
   `s y1 = sG y1`.

4. **`G_Var` no-op, via a dedicated shape lemma:**

   ```coq
   Lemma GEval_var_shape :
     forall P G x G' v, GEval P G (BExpr (EVar x)) G' v -> G' = G /\ v = GFwd x.
   ```

   Applying this to the graph-side unfolding (after rewriting to show it's also
   `rename_b sG body = BExpr (EVar w0)`, using step 3) gives `G1 = G0` and `vx = GFwd w0`
   directly — no admitted "the call doesn't touch `x0`'s own location" hypothesis needed at all,
   because *nothing* changed.

5. **Self-forward exclusion.** `Hw0x0 : w0 <> x0`, via the §7.1 pattern (assuming `w0 = x0`
   forces `Hrec2g` into a self-forward graph, contradicted by `ContractLoc_no_selfFwd`).

6. **`HeapCorr2` update, via the *existing* lemma unchanged.** Since `vx = GFwd w0` and the
   "gold" (previous `x0` content, `EFun f0 args0`) qualifies (it's neither `GFwd` nor `ECon`),
   `HeapCorr2_update_to_fwd_lazy` applies directly, giving `HeapCorr2 (hupd G0 x0 (GFwd w0))
   (hupd Gam x0 (BExpr (EVar w0)))`.

7. **Replay the forcing of `w0` across the `x0`-slot update.** `Hrec3`'s own decomposition via
   `NEval_left_evar_shape` splits into four branches (self-loop, free, Con-impossible-here,
   general-recursive). The general-recursive branch needs `NEval_left_frame_guarded` to replay
   the original (guard `w0::x0::F`) derivation across the heap change at `x0` (which the
   original derivation never actually reads, since `x0` is already in its own guard). The other
   two live branches (self-loop, free) are handled directly with no replay needed (no recursion
   happened in the first place).

8. **Assemble and hand to `IH2`.** Wrap the replayed "force `w0`" derivation in an outer
   `NL_VarExp` step forcing `x0` itself, then apply the induction's own `IH2` (available for
   `Hrec2g`'s shape, matching `BCase x0 brs0` exactly) to conclude `ContractLoc G2 x0 x'`.

This sub-case is fully `Qed`, no admits, and was closed in this session.

### 9.3 Two bugs hit and fixed while closing `EVar` (worth recording precisely)

**Bug 1 — an ambiguous `subst`.** Inside the self-forward-exclusion step:

```coq
assert (Hw0x0 : w0 <> x0).
{ intro Heq; subst w0.   (* BUG: Heq : w0 = x0, but ALSO Hsy1 : s y1 = w0 is in context *)
  ...
```

`subst w0` silently eliminated `w0` using `Hsy1 : s y1 = w0` (also a valid elimination target,
since `w0` is a bare variable on its RHS) instead of the intended `Heq : w0 = x0` — because
`subst` doesn't care *which* hypothesis lets it eliminate a variable, it just needs *some*
equation, and it apparently preferred the earlier-established one. Every later hypothesis
mentioning `w0` (including `Heq` itself!) got silently rewritten to mention `s y1` instead,
producing a confusing, hard-to-read error much later in the proof (a type mismatch between
`hupd G0 x0 (GFwd (s y1))` and the expected `hupd G0 x0 (GFwd x0)`). **Fix:** replace
`intro Heq; subst w0` with `intro Heq; rewrite Heq in Hrec2g` — a *targeted* rewrite naming
exactly the one hypothesis that needs the substitution, never touching anything else. See Part 2
§T-subst-pitfall.

**Bug 2 — `subst` vs. targeted `rewrite` for a lemma's output equations.** After
`GEval_var_shape` gives `HG1eq : G1 = G0` and `Hvxeq : vx = GFwd w0`, the first instinct
(`subst G1 vx`) risks the same ambiguity if any *other* hypothesis in scope could also eliminate
`G1` or `vx`. The fix used instead: `rewrite HG1eq, Hvxeq in Hrec2g` — rewrite *only* the one
hypothesis (`Hrec2g`) that actually needs the substitution, leaving `G1`/`vx` themselves alone as
names. This is a slightly more verbose but much safer idiom whenever a proof has many
co-occurring equations that could plausibly all target the same variable.

### 9.4 `EChoice y1' y2'`: fully closed, but via a *different* argument than `EVar`

Initially assumed to be a near-verbatim copy of `EVar` (same "no heap change" trick, since
`G_Choice` is *also* a no-op — `GEval_echoice_shape`, mirroring `GEval_var_shape`, confirms
`G' = G /\ v = GExpr (EChoice x y)`). This mostly worked, but two things differed from `EVar`:

1. **The self-forward exclusion argument doesn't transfer.** As noted in §7.1, if the forced
   operand equals `x0` (`y1' = x0`), the graph node becomes `EChoice x0 w2` — a *direct* value
   that `ContractLoc` accepts immediately via `CL_Here`, not a contradiction. It turned out this
   didn't matter: rather than collapsing `x0`'s corresponding Nat-heap witness down to a bare
   `EVar`/`GFwd`-style alias (which is what made `y1' <> x0` necessary for `EVar`, to
   distinguish `EVar w0` from `EVar x0` when building an `NL_VarExp` step), the `EChoice` case
   keeps `x0`'s witness as a **direct `EChoice` value**, `hupd Gam x0 (BExpr (EChoice y1'
   (sG y2)))`. Every place `EVar` needed `w0 <> x0` (the `Hex2_2`-style distinctness conditions
   for `NEval_left_frame_guarded`/`NL_VarExp`) becomes trivially true for `EChoice` instead,
   because `EChoice ... <> EVar x0` **by constructor shape alone**, regardless of the operand
   values. So the harder self-forward argument was simply never needed.

2. **The second operand never needs to be related to anything.** `NL_Or` only ever forces the
   *first* `EChoice` operand; the second is carried along completely unread, on both the
   Nat-heap and graph sides. This meant the "`s` and `sG` agree on parameters" argument (step 3
   of §9.2) only had to be built for the *first* operand `y1`, not for `y2` as well — `sG y2`
   (the graph side's own, possibly *different*, choice of fresh name for `y2` if it's not a
   parameter) is simply carried through as an opaque value in both the graph's `EChoice y1'
   (sG y2)` and the corresponding Nat-heap witness, with no need to prove it equals anything on
   the Nat-heap side.

3. **`HeapCorr2_update_to_direct` (an already-existing, more general lemma) supplies the
   `HeapCorr2` update directly**, instead of `HeapCorr2_update_to_fwd_lazy`:

   ```coq
   Lemma HeapCorr2_update_to_direct :
     forall G Gam x gold e,
       HeapCorr2 G Gam -> G x = Some gold ->
       (forall w, gold <> GFwd w) -> (forall c args, gold <> GExpr (ECon c args)) ->
       HeapCorr2 (hupd G x (GExpr e)) (hupd Gam x (let_content x e)).
   ```

   This is already fully generic over *any* `Expr0` shape `e` (its own proof case-splits on `e`
   and produces the matching `CorrE` constructor for each — including `CorrE_Choice`). Applying
   it with `e := EChoice y1' (sG y2)` gives exactly what's needed, with `let_content x0 (EChoice
   ...)` reducing to `BExpr (EChoice ...)` by plain computation (`EChoice` isn't `EFree`, so
   `let_content` falls into its `_ => BExpr e` branch) — Coq accepts this via silent conversion,
   no explicit rewrite needed (see Part 2 §T-defeq).

Two new small helper lemmas were added, mirroring the `EVar` ones exactly:

```coq
Lemma rename_b_echoice_preimage :
  forall s body y1' y2', rename_b s body = BExpr (EChoice y1' y2') ->
  exists y1 y2, body = BExpr (EChoice y1 y2) /\ s y1 = y1' /\ s y2 = y2'.

Lemma GEval_echoice_shape :
  forall P G x y G' v, GEval P G (BExpr (EChoice x y)) G' v -> G' = G /\ v = GExpr (EChoice x y).
```

Fully `Qed`, no admits — the second sub-case closed this session.

### 9.5 The three remaining open sub-cases, and precisely why each is hard

**`BLet`.** `rename_b s body = BLet z e0 k`. `NL_Let` (Nat-heap side) picks its bound variable
`z` fresh with respect to `Gam` (via `s`); `G_Fun`'s own graph-side renaming `sG` picks its
fresh variables with respect to `G0` instead. Since these are two *independent* freshness
choices (over different ambient heaps), `s` and `sG` can genuinely choose *different* concrete
names for the function body's own internal bound variables. This is a genuine
alpha-renaming-invariance problem — not a missing-lemma or missing-IH problem — and it wasn't
attempted this session.

**`BCase z brs2`.** `NL_Select`/`NL_Guess` fire (Nat-heap side evaluates an embedded case). The
natural next move would be a *fresh, non-inductive* application of `NEval_left_force_free_sound`
itself to the embedded `GEval` derivation for `BCase (s y1) ...` found inside `Hrec1g` (matching
`z = s y1` via the same "agree on parameters" argument as `EVar`). But `NEval_left_force_free_sound`
is proved via `induction H` on the *outer, `BCase`-rooted* derivation; the embedded derivation is
obtained via a separate helper lemma (`GEval_fun_shape`), not literally a constructor's own
bound sub-term of `H`, so **it receives no automatic induction hypothesis** — Coq's `induction`
only auto-generates an IH for a recursive premise that is a literal argument of the matched
constructor, not for an arbitrary term produced by calling some other (even already-`Qed`'d)
lemma on that premise. Calling the lemma "by name" on this sub-derivation doesn't work either,
because the lemma's own identifier doesn't exist yet inside its own still-open proof. Genuinely
recursing here requires either well-founded recursion on an explicit size measure, or — as
discussed in §10 — restructuring the whole statement to be general enough that the *needed*
recursive fact becomes available as an ordinary constructor-bound IH again.

**`EFun f2 args2`.** `NL_Fun` fires *again*, one level deeper — the function body's own body is
itself another function call. `Hrec3` here is strictly smaller in a *structural* sense (as a
literal Nat-heap-side derivation), but the induction that's actually running (`induction H`) is
on the *graph*-side `GEval` derivation, not on `Hrec3` at all — so there's no IH available for
this either, for the same underlying reason as `BCase`. Would need a separate, nested
well-founded/structural induction set up specifically for iterating through Nat-heap-side
`NL_Fun` unfoldings, independent of the outer graph-side induction.

**Both `BCase` and `EFun`-recursion share the same root cause as each other** (missing IH access
under the graph-side-only induction), which is a different and, on reflection, *harder* root
cause than `BLet`'s (which is a genuine semantic alpha-equivalence gap, not an induction-access
gap).

---

## 10. `theorem2_G_CaseFwd_case`, `theorem2_G_CaseChoice_case`, `theorem2_G_CaseFun_case`

These three theorems assemble, one `GEval` constructor at a time, the actual "Theorem 2 with
`NEval_left`" statement for the case where the final result is a genuine constructor — the
piece `NEval_left_force_free_sound` itself deliberately does *not* try to establish (it's scoped
to the free-variable-result branch only).

```coq
Theorem theorem2_G_CaseFwd_case :
  forall P G x y brs G1 v,
  G x = Some (GFwd y) ->
  GEval P G (BCase y brs) G1 v ->
  (forall c args, CorrV G1 v (BExpr (ECon c args)) ->
    forall Gam, HeapCorr2 G Gam ->
    exists Gam', NEval_left P nil Gam (BCase y brs) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam') ->
  forall c args, CorrV G1 v (BExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam', NEval_left P nil Gam (BCase x brs) Gam' (BExpr (ECon c args)) /\ HeapCorr3 G1 Gam'.
```

Note the asymmetry: the hypothesis (the externally-supplied "IH" for the `y`-cased
sub-derivation) demands `HeapCorr2`, but **the conclusion only delivers `HeapCorr3`.** This
theorem is fully `Qed` — it composes `NEval_left_fwd_transfer` (§6) with
`NEval_left_force_free_sound` (§8) directly, no admits of its own. But it is transitively
`Admitted`, since it calls `NEval_left_force_free_sound`, which is itself `Admitted` (§9).

```coq
Theorem theorem2_G_CaseChoice_case :
  forall P G x y z brs G1 v,
  x <> y -> G x = Some (GExpr (EChoice y z)) ->
  GEval P (hupd G x (GFwd y)) (BCase y brs) G1 v ->
  (forall c args, CorrV G1 v (BExpr (ECon c args)) ->
    forall Gam_mid, HeapCorr2 (hupd G x (GFwd y)) Gam_mid ->
    exists Gam1, NEval_left P nil Gam_mid (BCase y brs) Gam1 (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam1) ->
  forall c args, CorrV G1 v (BExpr (ECon c args)) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam', NEval_left P nil Gam (BCase x brs) Gam' (BExpr (ECon c args)) /\ HeapCorr2 G1 Gam'.
```

Uniformly `HeapCorr2` in and out. **1 admit.**

```coq
Theorem theorem2_G_CaseFun_case :
  forall P G x f args brs G1 vx G2 v,
  G x = Some (GExpr (EFun f args)) ->
  GEval P G (BExpr (EFun f args)) G1 vx ->
  G1 x = G x ->            (* <- taken as a hypothesis, NOT derived; see below *)
  WellFoundedFwd G ->
  GEval P (hupd G1 x vx) (BCase x brs) G2 v ->
  (forall c args', CorrV G1 vx (BExpr (ECon c args')) -> forall Gam, HeapCorr2 G Gam ->
    exists Gam1, NEval_left P nil Gam (BExpr (EFun f args)) Gam1 (BExpr (ECon c args')) /\ HeapCorr2 G1 Gam1) ->
  (forall Gam1, HeapCorr2 (hupd G1 x vx) Gam1 -> forall c args', CorrV G2 v (BExpr (ECon c args')) ->
    exists Gam2, NEval_left P nil Gam1 (BCase x brs) Gam2 (BExpr (ECon c args')) /\ HeapCorr2 G2 Gam2) ->
  forall c args', CorrV G2 v (BExpr (ECon c args')) ->
  forall Gam, HeapCorr2 G Gam ->
  exists Gam2, NEval_left P nil Gam (BCase x brs) Gam2 (BExpr (ECon c args')) /\ HeapCorr2 G2 Gam2.
```

Note `G1 x = G x` is taken as a **raw, unproven hypothesis** — "the function call doesn't touch
its own scrutinee's location." This is *not* derived anywhere in the file; it's threaded through
as an assumption the caller must supply. **4 admits**, in the `vx` case split: the `EBot` case is
fully handled (contradiction via `GEval_casebot_forces_bot`); the `EFree` case (vx resolves to a
bare free thunk) is admitted, tagged "the same pre-existing gap `NEval_left_fwd_transfer` carries";
the `EChoice` case is admitted, tagged "ruled out for well-formed programs by `NoBareChoiceB`,
not assumed here" (i.e., it's provably impossible *given* well-formedness, but well-formedness
isn't a hypothesis of this theorem); the `GFwd y` case's own inner Nat-Guess sub-branch is
admitted (same free-variable gap as the `EFree` case). The `GFwd y`/Con-reaching sub-branch,
however, is a substantial (~100 line) fully-`Qed` construction using
`HeapCorr2_update_to_fwd_lazy`, `NEval_left_frame_guarded`, `NEval_left_pointwise_heap`, and
`HeapCorr2_update_achieved` together — this is the single largest fully-proven chunk of `NEval_left`-
side reasoning in the file, and is what the `EVar`/`EChoice` work in §9 drew its technique
vocabulary from.

---

## 11. `NEval_left_let_chain_to_fwd` / `NEval_left_let_chain_to_con`

```coq
Lemma NEval_left_let_chain_to_fwd :
  forall P G e G1 y, GEval P G e G1 (GFwd y) ->
  forall Gam, HeapCorr2 G Gam -> WellFoundedFwd G ->
  forall x, G x <> None -> G1 x = G x ->
  exists Gam1, HeapCorr2 G1 Gam1 /\ Gam1 x = Gam x /\
    forall F0 Gamk vk, NEval_left P F0 Gam1 (BExpr (EVar y)) Gamk vk -> NEval_left P F0 Gam e Gamk vk.
```

Purpose: given an arbitrary `GEval` derivation for some expression `e` that ends in a `GFwd y`
result, thread `HeapCorr2` forward from `G` to `G1` for a *bystander* location `x` (playing the
exact role `x0` plays in `theorem2_G_CaseFun_case` — the outer case's own scrutinee, untouched
*by assumption* during the nested call), and provide a "plug" property letting a derivation that
forces `y` from the new heap `Gam1` be replayed as a derivation of the *original* `e` from the
original `Gam`. This is exactly the generalized threading machinery `theorem2_G_CaseFun_case`
needs for its `GFwd`-result branch — and it takes `G1 x = G x` as a hypothesis for the *same*
reason `theorem2_G_CaseFun_case` does (it isn't derived here either).

Proved by `induction H` on the `GEval` derivation (13 constructors again). `G_Var`, `G_Fun`,
`G_Let` are fully handled — `G_Fun` and `G_Let` recurse via their own `IH`, threading the
freshness/extension facts through `HeapCorr2_extend`/`WellFoundedFwd_extend`. **5 admits**: the
five `BCase`-producing constructors (`G_CaseFwd`, `G_CaseFun`, `G_CaseChoice`, `G_CaseCon`,
`G_CaseConFree`) are all tagged "body cases on something before reaching `y` — not yet handled."

`NEval_left_let_chain_to_con` (line 2783) is the sibling lemma targeting a `Con`-shaped final
result directly (no continuation to splice in, so it's built guard-generic from the start,
sidestepping a separate "add an unused variable to the guard" lemma). **6 admit sites**, same
shape of gap.

---

## 12. Designing `theorem2_left`: the combined general statement

### 12.1 Motivation

Every one of the open gaps in §9.5, §10, and §11 traces back to the *same* structural problem:
whichever lemma is being worked on is scoped too narrowly (to `BCase x brs`-rooted derivations
only) to receive an automatic induction hypothesis for a *nested* sub-computation (a function
call's own body evaluation, in particular) that itself needs the *same kind* of reasoning
applied to it. `curry.v`'s own `theorem2` (§3) sidesteps this entirely by being stated over
**arbitrary `e`**, which is exactly why its `induction H` gives every recursive premise (`G_Fun`'s
body evaluation, both of `G_CaseFun`'s two sub-derivations, `G_Let`'s continuation) a matching
IH "for free." The fix considered is to do the same thing for the `NEval_left`/`HeapCorr2` world:
state one theorem over arbitrary `e`, proven by one `induction H` covering all 13 `GEval`
constructors, and fold `NEval_left_force_free_sound`'s free-variable-tracking role into it as a
second conjunct (since curry.v's own `theorem2` only tracks the constructor-reaching outcome).

### 12.2 The drafted statement

```coq
Theorem theorem2_left :
  forall P G e G' v, GEval P G e G' v ->
  forall Gam, HeapCorr2 G Gam ->
  (forall c args, CorrV G' v (BExpr (ECon c args)) ->
     exists Gam', NEval_left P nil Gam e Gam' (BExpr (ECon c args)) /\ HeapCorr2 G' Gam')
  /\
  (forall x brs, e = BCase x brs ->
     forall F Gmid x', NEval_left P F Gam (BExpr (EVar x)) Gmid (BExpr (EVar x')) ->
     ContractLoc G' x x').
```

The first conjunct is `curry.v`'s own `theorem2`, with `NEval`/`HeapCorr` replaced by
`NEval_left`/`HeapCorr2`. The second conjunct is `NEval_left_force_free_sound`, folded in as a
conjunct rather than kept as a separate lemma — vacuously true (via `discriminate` on
`e = BCase x brs`) whenever `e` isn't a `BCase`.

Proved via one `induction H` over all 13 `GEval` constructors, every recursive premise now
carries *this same conjunction* as its IH — including the `ContractLoc` half — so, e.g., the
`BCase`/`EFun`-recursion sub-cases of §9.5 become ordinary `(proj2 (IH1 ...)) ...` /
`(proj2 (IH2 ...)) ...` uses rather than self-calls.

### 12.3 Branch-by-branch mapping (as drafted, not yet attempted)

| Constructor | 1st conjunct (Con-reaching) | 2nd conjunct (`ContractLoc`) |
|---|---|---|
| `G_Bot`, `G_Free` | trivial/vacuous | vacuous (`e` not `BCase`) |
| `G_Con` | trivial (`NL_ValCon`) | vacuous |
| `G_Choice` | **vacuous** — `CorrV G (GExpr (EChoice x y)) (Con c args)` requires `EChoice = ECon` syntactically via `CorrV_Direct`, always false | vacuous |
| `G_Var` | should port from existing `force_var_left`/`force_var_N_left` | vacuous |
| `G_Fun` | mechanical port of curry.v's own case (`NL_Fun` ≡ `N_Fun`) | vacuous |
| `G_Let` | mechanical port (`NL_Let` ≡ `N_Let`) | vacuous |
| `G_CaseBot` | new, expected easy | ports from `force_free_sound`'s existing `Qed` case |
| `G_CaseFwd` | folds in `theorem2_G_CaseFwd_case`'s logic, using IH instead of an external hypothesis | ports from existing `Qed` case |
| `G_CaseChoice` | folds in `theorem2_G_CaseChoice_case`'s logic | ports from existing `Qed` case |
| `G_CaseCon`, `G_CaseConFree` | new, expected straightforward | port from existing `Qed` cases |
| `G_CaseFun` | folds in `theorem2_G_CaseFun_case`'s logic; its `NEval_left_let_chain_to_fwd`/`_to_con` calls likely become **unnecessary**, replaced by direct `IH1` use | `EVar`/`EChoice` port from §9.2/§9.4; `BCase`/`EFun`-recursion now have a real IH available; `BLet` alpha-renaming is untouched by this restructuring — a separate semantic gap |

### 12.4 The stopping-point realization: `HeapCorr2` cannot be the ambient invariant

Before attempting the rewrite, one open design question was raised: `theorem2_G_CaseFwd_case`
concludes `HeapCorr3` (not `HeapCorr2`), while its own hypothesis needs `HeapCorr2` — should
`theorem2_left` use `HeapCorr2` uniformly (attempt to strengthen the `G_CaseFwd` branch to
actually deliver `HeapCorr2`), or `HeapCorr3` uniformly, or the same asymmetric pattern?

This was resolved definitively, not as an open proof-difficulty question but as a **known
fact**: `HeapCorr2` genuinely cannot survive the general case, confirmed by recalling the
original motivation for `HeapCorr3`'s creation (§5.2) — `N_VarExp`/`NL_VarExp`'s memoization
skips past multi-hop alias chains as a matter of course, which only `HeapCorr3`'s arbitrary-hop
`CorrE3` disjunct can certify; `HeapCorr2`'s `CorrE_FwdAchievedCon` is fundamentally limited to
one hop.

Tracing the consequence through: within `theorem2_left`'s own drafted `G_CaseFun` branch, `IH1`
(covering the function-call sub-evaluation, `Hrec1g`) can only ever hand back `HeapCorr3` — for
the *same* reason `theorem2_G_CaseFwd_case` can only hand back `HeapCorr3` — whenever that
sub-evaluation involves a genuine multi-hop chase (which, unlike the `EVar`/`EChoice` sub-cases
of §9 that dodge this entirely via the "zero heap change" trick, is the *general* case for any
real function body). But `IH2` (covering the continuation, `Hrec2g`) needs `HeapCorr2` as its
*input*. So within a single induction step, `IH1`'s output cannot feed `IH2`'s hypothesis — this
mismatch is not confined to the `G_CaseFwd` branch alone; it recurs at every point where one
sub-derivation's result becomes the next sub-derivation's starting heap.

**Conclusion reached, and where the session stopped:** `theorem2_left` needs `HeapCorr3` as the
ambient invariant threaded throughout — hypothesis *and* conclusion both — not `HeapCorr2` going
in with a `HeapCorr3` downgrade coming out. This has a real, non-trivial cost: essentially all of
the `HeapCorr2`-specific update machinery built and relied on throughout this file and this
session — `HeapCorr2_update_to_fwd_lazy`, `HeapCorr2_update_to_direct`, `HeapCorr2_update_achieved`,
and by extension the `EVar`/`EChoice` proofs of §9.2/§9.4 and the existing `Qed`'d `G_CaseChoice`/
`G_CaseCon`/`G_CaseConFree` cases of `NEval_left_force_free_sound` — would need `HeapCorr3`
analogs before `theorem2_left` could be attempted with a self-consistent, uniformly-threaded
invariant. `HeapCorr2` was deliberately kept in the file (rather than working in `HeapCorr3` from
the start) specifically as a record of the development process, to allow reviewing how the
invariant evolved.

**This is where the session ended** — the `theorem2_left` combined statement is drafted and
reasoned through, but no Coq code implementing it (or the `HeapCorr3` analogs of the update
lemmas it would need) has been written yet.

---

## 13. Earlier explorations, now deleted

Three more files existed in the project directory that predate everything above and were never
part of the active `curry.v` / `curry_test_leftmost.v` dependency graph: `curry_pre_blackhole_refactor.v`
(4,228 lines, fully self-contained — its own `Graph`/`GEval`/`NEval`, no `Require Import curry.`),
`curry_test_remove_aliasing.v` (482 lines, `Require Import curry.`), and `curry_todo.v` (1,761
lines, no `Require Import` at all — a loose scratchpad that never compiled standalone). All three
have now been **deleted** from the repository. This section is the only remaining record of
their content.

### 13.1 `curry_pre_blackhole_refactor.v` and `curry_todo.v`: the pre-guard investigation

These two files' content substantially overlapped (`curry_todo.v` reads as a working extract of
`curry_pre_blackhole_refactor.v`'s later, most-active sections, pulled out without its imports as
a staging area for continued work — hence why it never compiled on its own). They're documented
together here as one investigation.

**What "pre-blackhole" means, confirmed by direct comparison.** `curry.v`'s current `NEval` carries
an explicit guard list as its first index:

```coq
Inductive NEval : list var -> NHeap -> Blk -> NHeap -> Blk -> Prop :=
| N_VarExp : forall F G x e G1 v,
    ~ In x F ->
    G x = Some e -> ... ->
    NEval (x :: F) G e G1 v ->
    NEval F G (BExpr (EVar x)) (hupd G1 x v) v
| ...
```

with a comment at `curry.v` line 331: *"BLACK-HOLE GUARD (added after `blackhole_counterexample`...
exhibited a concrete Qed derivation where a heap location's thunk gets evaluated a SECOND,
independent time while its FIRST evaluation is still in flight)."* `curry_pre_blackhole_refactor.v`'s
own `NEval` has **no such parameter** — `Inductive NEval : NHeap -> Blk -> NHeap -> Blk -> Prop`,
and `N_VarExp`'s premise is the bare `NEval G e G1 v`, with no re-entrancy check at all. This
confirms the file is genuinely the snapshot from *before* the guard mechanism (now inherited into
`NEval_left`) was added — not merely an older-looking variant.

**Counterexamples A and B, still alive here as working Coq, not just comments.** §2.1 above
documents three historical counterexamples that shaped `CorrE`'s current, restricted definition
(`CorrE_FwdHere`/`CorrE_FwdAchievedCon` in place of one fully general `CorrE_FwdChase`), noting
that their code is "gone" from `curry.v`, surviving only as HISTORICAL NOTE comments. This file
is exactly where that code still lives: `Theorem HeapCorr_update_not_general` (line 1119) and
`Theorem NEval_confluence_unrestricted_is_false` (line 1316) are both fully `Qed`'d here (confirmed:
`grep` for these names in current `curry.v` returns nothing — they are genuinely gone there).

**`blackhole_counterexample` (line 2632) — the actual motivating derivation.** The comment
directly above it: *"The whole point: a valid NEval derivation of 'force y' whose final heap has
x = Con K [] (a genuine constructor) while y = Con R [] — neither 'x still aliases y' nor 'x = y'
holds."* The witness program (`bh_P`/`bh_Gam0`) builds a function `y` whose body chooses (via
`EChoice`) between two branches: one that recurses into forcing `x`, where `x`'s own content is
itself a call back into (a fresh copy of) `y`'s own function — and *that* nested evaluation is free
to pick the *opposite* `EChoice` branch, landing on an unrelated constructor. The outer evaluation
of `y` ends up memoizing `x` to whatever that independent, nested evaluation happened to produce,
which has no fixed relationship to `y`'s own final value. This is a concrete, `Qed`, axiom-free Coq
term — not a hypothetical — exhibiting a genuine "black hole": a thunk re-entered and independently
re-evaluated while its first evaluation is still in flight, which unconditional `Nat-VarExp`
memoization does not detect or reject. The fix, confirmed by the comment immediately after
(line 2738): *"Closing NEval_fwd_transfer therefore genuinely needs an explicit re-entrancy guard
added to Nat-VarExp itself... not just a cleverer induction over the current rules"* — i.e.,
exactly the guard list `F` that `curry.v`'s `NEval` (and `NEval_left`) now carry.

**The "restricted soundness" precursor — direct ancestor of today's `theorem2_G_CaseXXX_case`
theorems.** Before the guard was added, this file already had the *same* per-constructor
architecture now embodied by `theorem2_G_CaseFwd_case`/`theorem2_G_CaseChoice_case`/
`theorem2_G_CaseFun_case` and `NEval_left_force_free_sound`:

```coq
Lemma NEval_fwd_transfer :
  forall P G Gam, HeapCorr G Gam -> forall x y, G x = Some (GFwd y) ->
  forall brs Gam' v', NEval P Gam (BCase y brs) Gam' v' ->
  exists Gam'', NEval P Gam (BCase x brs) Gam'' v' /\
                (forall G1, HeapCorr G1 Gam' -> HeapCorr G1 Gam'').
(* Admitted — needed by G_CaseFwd/G_CaseChoice *)

Lemma NEval_choice_transfer : ... (* Admitted — needed by G_CaseChoice *)
Lemma NEval_fun_transfer : ... (* Admitted — needed by G_CaseFun *)

Theorem NEval_sound_restricted :
  forall P G e G' v, GEval P G e G' v -> Achievable G' v ->
  forall Gam, HeapCorr G Gam -> ...
(* 10 of 13 GEval cases proved directly with NO admits; the remaining 3
   (G_CaseFwd, G_CaseChoice, G_CaseFun) each reduce to exactly one of the
   three axioms above, applied once. *)

Theorem theorem2_complete : ... (* Theorem 2 in full, modulo exactly the three axioms *)
```

`Achievable` here (a graph value is either a real constructor, or a `GFwd` chase reaching a genuine
free self-loop) is a direct precursor to today's use of `CorrV ... (BExpr (ECon c args))`. The
three admitted "transfer axioms" all say the same underlying thing: *"if x's content forwards to
/ thunks / calls something whose evaluation leads to an achievable value, a case on x can be
evaluated directly to a corresponding value on a corresponding heap."* Multiple decomposition
attempts (documented in the file's own "SUMMARY OF FINDINGS", reproduced below) all hit the same
wall: `NEval` eagerly memoizes, so completing a case on `x` by replaying `y`'s sub-derivation needs
"evaluation is invariant under varying a heap slot to another valid representation" — a genuine
confluence/determinism-up-to-representation theorem for `NEval` that was never built. This is
**a different concern from §5's `HeapCorr2`/`HeapCorr3` multi-hop-memoization gap** — this is about
whether replaying a derivation across an *updated* heap slot is even sound at all (a
confluence/re-entrancy question), not about whether a *memoized* Nat-heap witness can be
*represented* by the correspondence relation. The two gaps are related in spirit (both about how
much `NEval`'s eager memoization can be trusted to line up with the graph) but are formally
distinct, discovered independently, roughly a full development cycle apart.

**Two typos found in the source paper (lsfa24.tex Figure 2), confirmed against the compiled PDF:**
1. `(Nat-VarExp)`'s conclusion heap is written `Gamma[x -> v]`; it should be `Delta[x -> v]`
   (`Delta` = the heap resulting from evaluating `e`) — as written, the rule drops every other
   heap update performed while forcing `x`.
2. `(Nat-Let)`'s premise is written `Gamma[yk -> rho(ek)] : e`; it should be `... : rho(e)` (`rho`
   applied to the body too) — as written, the let's own bound variables are never substituted into
   the continuation.

Neither typo is exercised by the paper's own Figure 13 case-by-case mapping (`Nat-VarExp` is
elided as "trivial"; the `Nat-Let` mapping is stated abstractly enough not to expose the bug),
which is presumably why they survived to publication.

**The converse direction: `NEval_realizes_GEval`, scoped, attempted, and found genuinely,
irreducibly false in three independent ways.** This is a different theorem from `theorem2` itself
— not "`GEval` implies `NEval`" but "`NEval` implies `GEval`" — investigated as a way to understand
the transfer axioms' common core. Multiple rounds of work on it are recorded (as "UPDATE 1"
through "UPDATE 5" in the file's own running log), landing on:
- A completely general version is false for **three independent, distinct reasons**, each with its
  own machine-checked disproof: (a) `e` a bare top-level `EChoice` (`NEval_sound_is_false`'s
  instance — `Nat-Or` commits to a branch immediately for a bare choice, while `GEval`'s own rule
  for an un-cased choice returns the choice unresolved); (b) a self-forwarding graph node
  (`G z = GFwd z`, `HeapCorr`-valid and `NEval`-derivable via `Nat-VarSelf`, but with no possible
  `ContractLoc` target at all); (c) bare-`EVar` forcing of a location whose canonical content is a
  function call — the graph side (`G_Var`) never eagerly resolves a variable outside an active
  case, but `Nat-VarExp` always does, so no `GEval` derivation for a bare `EVar` can reflect that
  resolution (proved via the simplest instance: a nullary function returning a constant).
- After narrowing with `ProgWF` and a new recursive well-formedness predicate `NoBareChoiceB`
  (excluding `EChoice` from every `BExpr` leaf position except a let's RHS — the ancestor of
  `curry.v`'s current `NoBareChoiceB`), **9 of `NEval`'s 11 constructors were proved with zero
  admits**, and the remaining 2 (`N_VarExp`, `N_Guess`) were shown **provably impossible** as the
  theorem is scoped, each via its own rigorous disproof — not merely difficult.
- One genuinely useful positive result survived intact: `CorrE_selfloop_means_free` — if a location
  is reached via a *complete, real* `GEval` `BCase` derivation and its Nat-heap witness is a
  self-loop, the self-loop can only mean genuine freeness, never a content-level cycle. This
  (along with its supporting `GEval_case_gives_ContractLoc`) is exactly the ancestor of the
  `GEval_case_gives_ContractLoc`/`_deep` machinery §7 documents as still active today.
- Bottom-line assessment quoted directly from the file: *"A theorem that actually holds for the
  remaining two cases would need to be considerably narrower — most plausibly restricted to `e`
  ranging over `BCase`/`BLet`/top-level `EFun`-calls only (never a bare `EVar` as the outermost
  expression), which is precisely how theorem2/NEval_sound_restricted themselves are scoped, and
  is not an accident."* This is a direct, independently-discovered confirmation of why
  `NEval_left_force_free_sound` and the `theorem2_G_CaseXXX_case` theorems are scoped the way they
  are (always relative to a `BCase`'s own scrutinee, never a bare top-level `EVar`).

### 13.2 `curry_test_remove_aliasing.v`: two ideas for simplifying the heap semantics, both dead ends

A self-contained, five-part investigation into whether the heap/natural-semantics side could be
simplified in a way that would make progress on the transfer axioms above. Conclusion, stated
plainly in the file's own Part 5: **no** — neither idea supplies the actual missing ingredient,
which is orthogonal to both.

**Idea 2 (Part 1): forbid `let x = y in ...` (a bare-variable let-RHS) to prevent aliasing from
ever arising syntactically.** Shown **false**. Witness program:
```
idf(a) = a                    -- identity function
main   = let y = free in      -- y := location 0
         let x = idf(y) in    -- x := location 1, RHS is a CALL, not a bare var
         x
```
Forcing `x` unfolds `idf`, which forces `y` (a free self-loop) and returns `EVar y` as `idf`'s
result; `Nat-VarExp` memoizes location `x` to exactly that, `EVar 0` — an alias, even though the
source text never once wrote a bare-variable let. The reason: `N_Fun`'s parameter passing is
already "by reference" (formal parameters are renamed directly onto the caller's own locations),
and `Nat-VarExp` memoizes *whatever* value forcing produces, including another location's `EVar`.
Aliasing is dynamically re-created by the semantics themselves (the natural-semantics mirror of
the graph's own `G_Var`/`GFwd` construction), not merely a syntactic copy-propagation artifact a
compiler pass could pre-empt. The restriction was judged still reasonable as a *minor*
simplification (it does remove one class of redundant aliasing) but not as a load-bearing
assumption for `theorem2`.

**Idea 1 (Part 2): replace the guard-list mechanism with a Launchbury-style variable rule** —
instead of threading `F` through every rule, *remove* `x`'s own binding from the heap for the
duration of evaluating its content, reinstating it only once complete:
```coq
| N2_VarExp : forall G x e G1 v,
    G x = Some e -> ... ->
    NEval2 (hremove G x) e G1 v ->
    NEval2 G (BExpr (EVar x)) (hupd G1 x v) v
```
A re-entrant force of `x` now shows up as an ordinary lookup failure (`G x = None`) rather than a
side condition threaded through every rule. **Part 4 shows this is not actually more expressive**:
by a direct argument (a location currently guarded/removed keeps exactly its push-time,
non-terminal content the whole time — nothing can mutate it, and nothing else can re-force it,
under *either* mechanism, for the same underlying reason), the two are the *same* black-hole
policing mechanism in different clothes, modulo one care point about fresh-variable collisions
with a hidden (removed) location that would need a global-freshness invariant to fully bisimulate
(not formalized). **Part 3** confirms the graph-representation confluence counterexample (§2.1's
counterexample B) is equally stuck under the new rule too — forcing either of the two
mutually-aliased locations hits a `None` lookup after exactly 2 steps instead of an unbounded
regress, same conclusion, faster diagnosis, entirely orthogonal to which black-hole mechanism is
used.

**Part 5's conclusion, quoted directly**: the actually-missing ingredient for closing the transfer
axioms is a **graph-level acyclicity/non-interference fact** — "nothing reachable from `y`'s own
graph definition is, or forwards to, `x`" — needed to show that replaying `y`'s forcing derivation
under a heap where `x`'s slot has *also* been updated still reaches the same result. This is a
statement about `GEval`/`CorrE`'s aliasing structure, not about which black-hole bookkeeping
`NEval` happens to use, so *neither* idea 1 nor idea 2, alone or together, touches it. Both ideas
are reasonable, well-motivated simplifications on their own terms (idea 1 arguably more elegant,
and closer to Launchbury's original rule); neither unblocks `theorem2`.

## 14. Current status (as of 2026-08-15): two parallel `theorem2` attempts, and where each actually stands

This section exists because the two files drifted out of sync with these notes (this file was last
updated 2026-07-29; `DEAD_ENDS.md` was last updated 2026-08-11; real progress happened in
`curry_test_leftmost.v` after both). Both `curry.v` and `curry_test_leftmost.v` were confirmed to
`coqc` cleanly (no errors, only pre-existing string-in-comment warnings) as of this writing.

**`curry.v`'s `theorem2` (line 2229)** — the "official", `NEval`-stated version described in §3
above. Unchanged since §3/§10 were written: 8 of 11 induction cases are `Qed`-solid; 3 are `admit`
(`G_CaseFwd` line 2307, `G_CaseFun` line 2319, `G_CaseChoice` line 2324), all attributed in-comment
to the single missing `NEval_fwd_transfer` lemma (line 3134), which itself carries 2 further
`admit`s (lines 3182, 3185) for exactly the "y needs further forcing" and "Nat-Guess" sub-cases.
Root cause, per §9/§13 above: a "NEval soundness/confluence relative to G" fact for plain `NEval`
that was never built, and that three independent framings (§13 Part 5, `DEAD_ENDS.md` §S7-S9) show
is genuinely load-bearing, not an artifact of proof strategy.

**`curry_test_leftmost.v`'s `theorem2` (line 6918)** — the `NEval_left` restatement (§12's
`theorem2_left` direction, Or forced left to match `GEval`'s own bias, motivated by removing the
nondeterminism that was the real source of the confluence gap above). This is where the actual
progress since 07-29/08-11 lives:
- **`G_CaseFwd` (lines 7036-7408) is now fully `Qed`'d, zero `admit`s.** This is the exact case that
  was completely stuck in `curry.v` and in every dead-end logged in `DEAD_ENDS.md` — closed.
- **`G_CaseChoice` (lines 7411-7562) is almost done**: one remaining `admit` at line 7529, scoped
  to a single sub-shape (`NL_Guess`, i.e. the branch where the aliased-to location resolves via
  free-variable/self-loop promotion rather than being already-`Con`-shaped or forcing further
  through `NL_Select`). In-comment, this is flagged as needing "the FULL STEP1/STEP2/demote/
  re-promote machinery from `HeapCorr_fwd_transfer_fwdhere_free`'s own `x' <> y` case, ported here
  for `x0` aliasing `y0` via `EChoice`/`NL_Or` instead of directly" — i.e. an adaptation of
  already-proven machinery, not a new theory gap.
- **`G_CaseFun` (line 7409) is a bare, unstarted `admit.`** for the whole case. Per §10's original
  diagnosis (still expected to hold here), it should decompose into: the `G_CaseCon`/`G_CaseConFree`
  sub-shapes (already `Qed`'d elsewhere in this file) plus exactly the `G_CaseChoice`/`G_CaseFwd`
  sub-shapes — so no new lemma is expected, just the bookkeeping to write it out, likely surfacing
  the same `NL_Guess` gap as `G_CaseChoice` along the way.
- `G_CaseBot`, `G_CaseCon`, `G_CaseConFree` are all fully `Qed`'d in this version too.

**Net position:** the file you'd currently point to as "the proof of Theorem 2" (`curry.v`) still
has 3 open cases behind one unbuilt lemma. The up-to-date, closer-to-done attempt lives in
`curry_test_leftmost.v` and has *not* been folded back into `curry.v` as the new `theorem2` — doing
that migration is itself a to-do. Within `curry_test_leftmost.v`, the remaining work is: (a) one
narrow, already-diagnosed sub-case (`NL_Guess` promotion inside `G_CaseChoice`), and (b) writing out
`G_CaseFun`, which is expected to reduce to cases already closed elsewhere in the file plus (a)
again. This is a meaningfully smaller remaining surface than `curry.v`'s three-case, root-lemma-level
gap.

## 15. 2026-08-15 session: closed the `HeapCorr_fwd_transfer_fwdhere_free` two-hop admit; re-diagnosed the `G_CaseChoice`/`NL_Guess` gap as harder than its own comment claimed

**Closed, and now `Qed`-clean:** `HeapCorr_fwd_transfer_fwdhere_free`'s `x' <> y` branch had one
remaining `admit`, for the `w0 <> x, y` case of transporting `CorrE3 G1v Gam' w0 b` across to
`CorrE3 G1v Gam2raw w0 b` when `b`'s witness took the VarChase "skip-ahead" disjunct. The comment
called this a missing "genuine TWO-HOP generalization of `NEval_left_alias_or_con_persists`." It
turned out to need no new graph-level theory at all — only a **general two-location VarChase
transport lemma**, added as `VarChase_transport_two_locations` (plus a small converse helper,
`VarChase_transport_unshorten`, the missing other half of the existing `VarChase_transport_shorten`):
if two heaps agree everywhere except at `x`/`y`, and BOTH heaps independently already chase `x` and
`y` to the SAME `Con c args` (however each heap represents that — directly achieved, or still a lazy
alias one hop short), then VarChase transports between the two heaps freely for ANY starting
location. Proof: force both heaps up to a common "`x`,`y` both directly achieved" representative
(two `_shorten` steps each), cross via plain pointwise equality (`VarChase_pointwise`) once at that
representative, then peel the *target* heap's own forcing back off (two `_unshorten` steps) to land
on the real, possibly-still-lazy target heap. The needed "both heaps reach the same terminal"
hypothesis was the one non-obvious fact to establish at the call site: `ContractLoc_functional`
pins the achieved endpoint reachable from `y`'s (graph-level) forward chain to be UNIQUE, and that
endpoint was already shown (via `HeapCorr_con_to_contractloc` on `Gam' x' = Con c1 ws`) to BE
`wit`/`c1`/`ws` — so `Gam' x`'s own two possible CorrE3 shapes (`EVar y` or achieved) both provably
terminate at `c1`/`ws` too, via `CorrE_forced_shape` + that same functionality fact. No self-loop
side conditions were needed in the end (the `y`-side disjunct route through `Gmid`'s own `x'`-aliasing
fact, not through the graph-level `y0` intermediate, sidestepping that worry entirely). All of this
is now `Qed`, not `Admitted`, and the two new lemmas are file-general (not specific to this call site).

**Re-diagnosed, NOT closed:** attempted to then "port" this into `theorem2`'s own `G_CaseChoice`
`NL_Guess` sub-case (line ~7638), per that site's own comment ("would need the FULL
STEP1/STEP2/demote/re-promote machinery... ported here for `x0` aliasing `y0` via `EChoice`/`NL_Or`
instead of directly"). That comment undersells the gap. `HeapCorr_fwd_transfer_fwdhere_free`'s
STEP1-4 dance depends on `Gam x` ALREADY being a literal one-hop alias `EVar y` by the time the
"other side" (`Hrec2`) starts — which is what lets `NEval_left_shortcut_alias` treat `x` as
aliasing `y` and promote/demote it. In `G_CaseChoice`, `x0`'s Nat-heap slot is `EChoice y0 z0`, not
an alias at all, so that promotion step has no foothold. Worse: since `Gam x0` is non-terminal but
NOT one of `_shortcut_alias`'s two accepted shapes, the natural fallback — "`x0`'s slot is frame-
irrelevant to `Hrec2`'s own computation, so replay `Hrec2` over a heap with `x0` swapped to whatever
`HforceX0` produces" — needs `NEval_left_frame_guarded` (or `NEval_left_frozen_at`, which DOES give
`Gmid2 x0 = Gam x0` unchanged, cleanly, via the `[x0]`-guarded `Hforcey0'`). But `Hrec2`/`Hbodyguess`
itself runs with **guard `nil`, not `[x0]`** (it's the branch-body continuation from `theorem2`'s own
top-level nil-guard forcing) — so `x0` is NOT in Hrec2's own guard, and `_frame_guarded`'s whole proof
technique (which relies on the guard to rule out `x0` ever being re-entered) doesn't apply. Making
`x0`'s slot provably irrelevant to `Hrec2` without a guard would need an independent **freshness/
scoping fact** ("`x0`, a heap location from the enclosing computation, is never referenced by
`body1`/`ws`, the branch body being guessed") — exactly the kind of "global freshness invariant
`theorem2` doesn't currently have" that `DEAD_ENDS.md`'s §S9 already flagged and abandoned, in a
different guise. **Conclusion: the `G_CaseChoice`/`NL_Guess` gap is not a mechanical port of the now-
closed lemma — it needs either a new location-freshness invariant threaded through the whole theorem,
or a restructuring of how the guard is threaded through `NL_Guess`'s continuation, before the same
promote/demote technique (or some analogue of it) can even be attempted.** Not attempted further this
session; flagged here so the next session doesn't re-derive this from scratch.

## 16. Same session, continued: `G_CaseChoice`/`NL_Guess` actually closed (correcting §15's own conclusion); then a first pass at `G_CaseFun`

**§15's own "conclusion" above was wrong, and was overturned within the same session.** The user's
own suggestion broke the logjam: since `NL_Or` always forces its LEFT operand, a location holding
`EChoice y z` is operationally indistinguishable, for forcing purposes, from one holding the plain
alias `EVar y` — no freshness invariant needed at all, just a *bridge* between the two
representations. Built as two lemmas: `NEval_left_choice_as_alias_force` (peel `NL_VarExp`'s one
layer, transport the recursive premise — which genuinely IS guarded, `[x]` — via the *already-
existing* `NEval_left_frame_guarded`) and `NEval_left_choice_as_alias_bcase` (lift across a whole
`BCase`, since both `NL_Select`/`NL_Guess` force the scrutinee first). With that bridge, the
already-`Qed`'d `HeapCorr_fwd_transfer_fwdhere_free` (§15's closed lemma) could be called *unmodified*
against the alias-shaped heap the theorem's own IH already supplies, then carried back across the
`EChoice`/`EVar` swap. **`theorem2`'s `G_CaseChoice` case is now FULLY `Qed`'d, zero admits** — this
was the single remaining admit block in the file's active `theorem2` after §14/§15's work.

**Then a first, partial pass at `G_CaseFun`** (previously one blanket `admit.`, the last case in
`theorem2`). Diagnosis: `x0`'s slot is `EFun f0 args0`, an *unevaluated call* — the graph-level result
`vx` (`Hrec1`) can be `Bot`/`Free`/`Con`/`Fwd y`/`Choice y z`, and `theorem2`'s own automatic IH for
`Hrec1` (`IH1`) is Con-restricted and useless for the other four. The fix does NOT need the general
"theorem2, unrestricted" fact (`theorem2_left`) — it needs only a purely STRUCTURAL, evaluation-free
correspondence: `hupd G1 x0 vx`'s own `CorrE` requirement at `x0` has a trivial witness for every
shape (`EVar y` for `Fwd y`, the constructor itself for `Con`/`Choice`, `EVar x0` — the self-loop — for
`Free`), matching exactly what a genuinely OLDER, superseded `HeapCorr2`-based attempt in this same
file (`NEval_left_let_chain_to_fwd`/`_to_con`, `theorem2_G_CaseFun_case`, ~line 3696/5561) had already
worked out but never ported to the current `HeapCorr`/`CorrE3`. Ported and *generalized* into one
lemma, `NEval_left_let_chain_to_value` (unifying all five shapes via a `GNode_mirror` mapping, rather
than one lemma per shape), plus the graph-frame lemmas it needed at the assembly site
(`HeapCorr_update_from_fun`, `WellFoundedFwd_update_from_fun`, `ChainConsistent_update_from_fun`,
`AliasConsistent_update_from_fun`, `VarChase_avoids_fun_loc` — all proved by the same "`x0`'s old
content was `EFun`, never Fwd/achieving, so nothing could already have targeted it as a shortcut"
argument `HeapCorr_update_choice_to_fwd` already used for `EChoice`).

**What's now closed in `G_CaseFun`'s first conjunct:** `Bot` (vacuous), `EVar`/`EFun`-as-`vx`
(impossible, `GEval_never_var_or_fun`), `Con` (direct), `Fwd y` (mirrors `G_CaseChoice`'s own
`NL_Select` pattern, but note the scrutinee-forcing structure differs subtly from `G_CaseChoice`: here
`Hforce0`'s own scrutinee IS `x0` itself — since `G_CaseFun`, unlike `G_CaseChoice`, never redirects
the graph-level scrutinee — so the `[x0]`-guarded recursive premise needed by `_frame_guarded` comes
from INVERTING `Hforce0` via `NL_VarExp`'s own shape, not from widening an already-nil-guard fact via
`NEval_left_alias_weaken_force_y` the way `G_CaseChoice` does; and `Gmid` ends up with `x0` ALREADY
memoized to the achieved value, so no `_shortcut_alias` promotion step is needed at all, just a plain
`NEval_left_pointwise_heap` replay — noticeably SIMPLER than `G_CaseChoice`'s analogous branch once the
guard/scrutinee difference is accounted for).

**Four admits remain, all narrowly scoped:**
1. `vx = Free` — `x0` forces to the LITERAL token `EFree` (via `NL_ValFree` on a BARE, un-let-bound
   `free` tail), not a self-loop; `CorrE_Free`'s own witness needs `EVar x0` instead — an extra
   promotion step (something like: force once more, `NL_VarFree` this time, to actually reach the
   self-loop) that isn't built here.
2. `vx = Choice y z` — the function body's own tail being a bare, un-cased choice means `NL_Or`
   unfolds it EAGERLY inside `Hplug`'s own forcing (`GNode_mirror` correctly targets `BExpr(EChoice y
   z)` as the "what to force" value for `NEval_left_let_chain_to_value`'s own purposes, but *that's not
   the same problem* as needing `x0`'s achieved value post-force) — same family of gap as Free.
3. `NL_Guess` sub-shape within the `Fwd y` branch — `x0` forwards to `y0'` (an ordinary Fwd edge, not
   an `EChoice`), and `y0'` itself resolves to a free self-loop rather than a constructor. The exact
   same STEP1-4/two-location-`VarChase` machinery from `HeapCorr_fwd_transfer_fwdhere_free`'s `x' <> y`
   case (§14) would need adapting to this shape too — not yet attempted, though by analogy with how
   cleanly the `Con`/`Fwd`-`NL_Select` cases came together, this looks tractable, not another
   freshness-style wall.
4. **The whole SECOND conjunct** (`ContractLoc`-matching) for `G_CaseFun` — genuinely not started this
   session. Unlike the `EFun`-as-top-level-`e` sub-calls (where `theorem2`'s second conjunct is
   vacuous, `BExpr(EFun..) <> BCase _ _`), `theorem2`'s OWN "e" for the whole `G_CaseFun` rule instance
   IS `BCase x0 brs0` — so this conjunct is live and would need the analogous "force `x0` reaches
   `x0'`" → "`ContractLoc G2 x0 x0'`" argument `G_CaseChoice`'s own second conjunct already builds,
   threaded through the same `Con`/`Fwd` split as the first conjunct above.

`theorem2` now has exactly 4 admits total (all four above, all inside `G_CaseFun`) — down from one
blanket admit covering the entire case. File still compiles clean (`coqc`, zero errors).

## 17. Same session, continued again: `Free`/`Choice` closed via a new well-formedness hypothesis; `NL_Guess`-in-`Fwd` closed too — `theorem2` down to ONE admit

**The `Free` sub-case turned out to be a genuine gap in the theorem's own statement, not a missing
lemma — confirmed with the user before fixing it.** Forcing `x0` (whose slot is `EFun f0 args0`) when
the function body's tail is BARE `free` (not `let z = free in z`) is *deterministic*: `NL_VarExp →
NL_Fun → NL_ValFree` is the only possible derivation, and it produces the literal value `BExpr EFree`
— not a self-loop `EVar w`. But `BCase`'s only two Nat rules (`NL_Select`/`NL_Guess`) need the
scrutinee to reach `Con` or `EVar x'` specifically; bare `EFree` matches neither, so **no valid
`NEval_left` derivation of `BCase x0 brs0` exists in this scenario at all**, even though the graph
side succeeds fine via `G_CaseConFree`. None of `theorem2`'s hypotheses at the time ruled this out.
The user confirmed the underlying fact: real Curry source has no way to write a bare `free` (or bare
`?`) outside a `let` binding — matching a restriction the file already anticipated needing for
`Choice` alone (an older, superseded draft's own comment: "`EChoice`: ruled out for well-formed
programs by `NoBareChoiceB`, not assumed here" — that hypothesis was never actually added to the
active `theorem2`).

**Fix:** defined `NoBareFreeOrChoiceB` (mirrors curry.v's own `NoBareChoiceB` fixpoint exactly, just
also excluding bare `EFree` at every tail position — both shapes are legitimate ONLY as a
let-binding's own RHS) plus its rename/branch-lookup lemmas (literal copies of `NoBareChoiceB`'s own,
since the proof technique doesn't care which shapes are excluded), `NoBareFreeOrChoiceProgWF P` (a
program-wide fact, mirroring `NoAliasLetProgWF`), and the payoff lemma
`GEval_result_not_free_or_choice`: given this program-wide restriction, `GEval`'s own result can
NEVER be a bare Free or Choice node — provable by a **plain structural induction on `GEval` with NO
scope restriction at all** (unlike `NEval_left_let_chain_to_value`, this lemma only tracks a SHAPE
fact through the six case-tail `GEval` rules, not an actual Nat-heap construction, and
`NoBareFreeOrChoiceB` restricted to a `BCase` doesn't even depend on the scrutinee — so every
`BCase`-to-`BCase` step, e.g. `G_CaseFwd`/`G_CaseChoice`/`G_CaseFun`'s own second premise, reuses the
SAME hypothesis unchanged, no rewriting needed). Added `NoBareFreeOrChoiceProgWF P` as ONE new
top-level hypothesis to `theorem2` — since it's introduced once, before `induction H` runs (same
footing as the pre-existing `HPWF`), this did NOT require touching any of the other 12 already-`Qed`'d
cases at all. Both `Free` and `Choice` sub-cases of `G_CaseFun`'s first conjunct became flat
`exfalso` contradictions.

**Then closed the `NL_Guess`-within-`Fwd` admit too — turned out simpler than diagnosed in §16.**
The §16 comment guessed this needed `HeapCorr_fwd_transfer_fwdhere_free`'s full STEP1-4/
two-location-`VarChase` machinery (built for reconciling TWO INDEPENDENTLY-chosen fresh guesses — one
from forcing `x` directly, one from forcing `y` and continuing separately). That's not what's
happening here: there is only ONE guess in play (`Hbodyguess` is shared, already the same derivation
either way), so the fix mirrors the ALREADY-`Qed`'d `NL_Select` branch immediately above it in the
same case, line for line — invert `Hforce0` (x0's own scrutinee-forcing) via `NEval_left_evar_shape`
to extract the guarded `(x0::nil)` recursive premise, transport it via the existing
`NEval_left_frame_guarded`, feed it to `Hplug` to get `HforceX0` from the TRUE `Gam`, then a plain
`NEval_left_pointwise_heap` replay — just targeting a self-loop `EVar x'` instead of `Con c' zs`. Only
wrinkle: `NEval_left_evar_shape`'s own first disjunct (`VarCons`) is normally closed by `discriminate`
when the target is `Con`-shaped, but here the target IS `EVar x'`, so that disjunct's OWN impossibility
comes from its `exists c args, v = Con c args` sub-part instead — needed keeping that existential
in the destructuring pattern rather than discarding it.

**`theorem2` now has exactly ONE admit total** — the second conjunct (`ContractLoc`-matching) for
`G_CaseFun`. Diagnosis (from directly attempting it): unlike the first conjunct, the second conjunct's
own goal for the `Fwd` sub-case needs a **Nat-to-Graph** correspondence ("forcing the function call
reaches self-loop `x'`" implies "`ContractLoc` from the graph's own call-result to `x'`") for an
**arbitrary** expression (`EFun f0 args0`), not just a `BCase`-shaped one — `theorem2`'s own second
conjunct only covers `BCase`-shaped `e`. Attempting to invert the forcing derivation directly (via
`NEval_left_fun_shape`) to relate it back to `Hrec1`'s own `(ps, body, s)` decomposition risks needing
an independently-chosen renaming `s'` that may differ from `Hrec1`'s own `s` — exactly the
"alpha-renaming invariance" gap the older, superseded `theorem2_G_CaseFun_case` draft already flagged
as a SEPARATE blocker on top of its own main one. Not attempted further this session; flagged here so
the next session doesn't re-derive this diagnosis from scratch. File compiles clean (`coqc`, zero
errors) throughout.

## 18. Next session: pinned down exactly what the alpha-renaming gap is (and isn't), and why it can't
be fixed either by a new lemma kept local to `theorem2` or by a syntax restriction — the last admit
stays, now precisely characterized

**Half of the §17 worry dissolves once you actually look at what `ContractLoc` is checked against.**
The user's own framing was the key: the second conjunct's conclusion is about `G2`, the graph *after
both* `Hrec1` (evaluates the call) *and* `Hrec2` (re-evaluates `BCase x0 brs0` on the updated graph)
have run — and `Hrec2` is already one of `G_CaseFun`'s own two recursive premises, so it already has
its own `IH2` from `theorem2`'s own induction. `G_CaseChoice`'s already-`Qed`'d second conjunct
(`curry_test_leftmost.v:8526-8531`) is the exact template: get `ContractLoc G1 y0 x'` by calling `IH2`
*recursively on `Hrec`'s own next hop*, then close with one `CL_Fwd`. So "does the chase ever get stuck
behind an unevaluated call" is already answered — it can't, by the same induction, no new lemma needed.

**The genuine remainder: reconciling `Hforce`'s own internal fresh choice against `Hrec1`'s.** Before
`IH2` is even reachable, `Hforce` (arbitrary, caller-supplied) has to be unwound at `x0` itself, and
since `Gam x0 = EFun f0 args0` too, that unwinding fires `NL_VarExp → NL_Fun`, picking its own fresh
renaming `s'` — independent of `Hrec1`'s own `s`. Checked whether `HeapCorr`'s domain-matching
(`G x = None <-> Gam x = None`, `curry_test_leftmost.v:2417-2421`) already rules out disagreement: it
doesn't. It only guarantees `s` and `s'` avoid the *same* forbidden set — nothing pins them to make the
*same* choice among the (infinitely many) remaining fresh locations. Splitting on where the `Fwd`
target `y0'`/`x'` comes from inside the function body:
- **A parameter** — no ambiguity. Both `s` and `s'` are independently *forced* to map it to the same
  `args0[i]`, since that part of `NL_Fun`/`G_Fun`'s precondition isn't a free choice at all.
- **A body-internal `let`-bound variable** — genuinely ambiguous. `y0' = s(z)`, `x' = s'(z)`, and
  nothing ties them together. The concrete shape that lands here is a function whose body
  *manufactures a fresh free variable*, e.g. `f0(p) = let z = free in z` — i.e. exactly how
  `unknown`/anonymous free variables are idiomatically written in real Curry. So this isn't a corner
  case excludable the way bare-`free`-as-a-tail was in §17 (no surface syntax produces that one); this
  pattern is completely ordinary, so ruling it out would falsify the theorem's applicability to real
  programs.

**Checked all four already-`Qed`'d second-conjunct cases (`G_CaseFwd`, `G_CaseChoice`, `G_CaseCon`,
`G_CaseConFree`) for the same exposure — none of them have it.** None involves an existential
fresh-name pick whose *output identity* becomes the thing `ContractLoc`'s conclusion is checked
against: `G_CaseChoice`/`G_CaseFwd` just chase a pre-existing edge (`y`/`z` already fixed by the
graph, no renaming at all); `G_CaseConFree` narrows to a self-loop *at `x0` itself*
(`curry_test_leftmost.v:8654`, `injection Heqv2 as Heqv2; subst x'` — `x'` is forced equal to `x0`
directly, no freshness involved even though `G_CaseConFree` itself picks fresh `ws` for the new
constructor's arguments, because those `ws` never become the thing being matched against). `G_CaseFun`
is the only rule in the whole system where a genuinely fresh, existentially-chosen name can become the
`ContractLoc` target itself — confirming this really is new territory, not something the existing
proof technique already handles elsewhere in a form that generalizes.

**Considered weakening the conclusion to an existential (`ContractLoc G' x x' \/ exists y, ContractLoc
G' x y /\ G' y = Some (GExpr EFree)`), keeping it as a disjunction so the four already-`Qed`'d cases
could just take the `left` branch unchanged.** This looked local at first, but tracing *every* actual
consumer of the second conjunct — not just the four "second conjunct" bullets, but two more usages
buried inside `G_CaseFwd`'s and `G_CaseChoice`'s own *first*-conjunct proofs
(`curry_test_leftmost.v:7933-7941`, and the analogous spot near `:8494`) — found that one of them feeds
the result directly into `HeapCorr_fwd_transfer_fwdhere_free` (the two-hop `VarChase` lemma closed in
the prior session) as a hypothesis of the literal tied-`x'` shape. The weakening doesn't stay inside
`theorem2`; it forces a matching change to that lemma's own signature (and possibly further, unmapped
cascade beyond it). So this path is a real, larger refactor, not a local patch — flagged to the user
along with the original alpha-invariance-lemma option; **decision: stop here rather than take on either
one.**

**Current, final state of this investigation: `theorem2` has exactly ONE admit** — the second conjunct
(`ContractLoc`-matching) of `G_CaseFun`, `curry_test_leftmost.v:8356`. The first conjunct (Con-reaching
correspondence — the paper's actual Theorem 2 claim) is fully `Qed`'d for every case including
`G_CaseFun`. The remaining gap is precisely: relating two independently-fresh-chosen evaluations of the
same function call, specifically when that call manufactures a fresh free variable via an internal
`let`. Two viable ways forward for a future session, neither attempted: (a) prove a genuine
alpha-renaming-invariance lemma for `GEval`/`NEval_left` and keep `theorem2`'s statement exactly as is;
(b) weaken the second conjunct's conclusion to the disjunctive form above, and follow the cascade into
`HeapCorr_fwd_transfer_fwdhere_free` (and whatever it touches) to completion. File compiles clean
(`coqc`, zero errors) throughout; no `.v` changes were made this session — only this diagnosis.

## 19. Same session, continued: attempted path (b) first, hit the same wall §18 predicted; then started
path (a) for real, in a new standalone file `alpha_renaming_wip.v` — foundational piece done and
verified, three larger pieces still ahead

**Attempted (b) (the cascading disjunctive-conjunct refactor) concretely before giving up on it.** Read
`HeapCorr_fwd_transfer_fwdhere_free`'s full `x' <> y` sub-case (`curry_test_leftmost.v:6421-6650`ish,
the "STEP1-4 promote/demote" machinery) end to end. Confirmed the tied-`x'` hypothesis is genuinely
load-bearing, not superficial: `curry_test_leftmost.v:6564` (`Hcl_yx' : ContractLoc G1v y x'`) feeds
into `ContractLoc_first_hop`, `ContractLoc_trans`, and gets pinned against `wit` (the constructor target
`Gam'` independently reaches) via `ContractLoc_functional` — the whole promotion/demotion argument is
built around knowing exactly *which* location `x'` is. A decoupled "some free-standing location exists"
fact isn't sufficient to replay this; weakening it would mean redesigning roughly 200 lines of
already-`Qed`'d machinery, not patching a signature. No `.v` edits made (read-only investigation);
reverted to `close-choice-as-alias-gap` cleanly. Confirms §18's prediction was accurate, not
overcautious.

**Started (a) (the genuine alpha-renaming-invariance lemma) for real, on a new branch
`alpha-renaming-invariance`.** First design pass (before writing code) surfaced that the natural first
idea — "pick one bijection σ once, show any derivation relabeled by σ is still valid" — is NOT what's
needed: `Hforce` (the caller's derivation) picks its own fresh names completely independently, so
nothing lets a single upfront σ line up with it. What's actually required is a genuine **two-sided
bisimulation**: given two independently-derived evaluations of alpha-related expressions from
alpha-related heaps, show their results stay alpha-related, building the correspondence between the two
derivations' fresh-name choices *incrementally* — extending it by one swapped pair each time either
side's `NL_Fun`/`NL_Let`/`NL_Guess` picks a fresh name, using that both sides always have infinitely many
fresh names left to draw from.

Built and verified (`alpha_renaming_wip.v`, compiles clean) the foundational piece this rests on:
`transpose`, `mutual_inverse` (a bijection given as two mutually-inverse total functions
`sigma tau : ren`), and `mutual_inverse_extend` — extending a mutual-inverse pair by one fresh pair
`(a, b)` (both currently fixed points) while preserving mutual-inverse-ness everywhere else. This took
several iterations, including a genuine bug caught only by a concrete counterexample: the first cut at
`ext_sigma`/`ext_tau` only *redirected* `a ↦ b` without also redirecting `b` back, silently breaking
injectivity (`a=5, b=7, sigma=tau=identity` ⇒ `ext_tau(ext_sigma 7)` computed to `5`, not `7`). Fixed by
making the extension a genuine two-point *swap* rather than a one-sided redirect.

**Still fully unstarted, in order, before this closes the admit:**
1. `heap_rename` (pointwise: `heap_rename sigma tau G w := option_map (rename_b sigma) (G (tau w))`)
   plus its interaction with `rename_b`/`hupd`/`hupd_list` (composition/pushforward lemmas).
2. A "batch-extend by a finite list of pairs" lemma — `NL_Fun` and `NL_Guess` each introduce a *whole*
   renaming/list at once (not one variable at a time), so `mutual_inverse_extend` needs applying `N`
   times in a row, matched positionally against a computed `free_vars_b` of the function body / case
   branch (needs a `free_vars_b : Blk -> list var` fixpoint that doesn't exist yet either).
3. **The main piece**: the two-sided simultaneous induction over all 11 `NEval_left` rules. 8 of 11
   just thread the current `(sigma, tau)` through unchanged; `NL_Fun`/`NL_Let`/`NL_Guess` need the
   extension from (2). Given how much iteration the small piece in (this section) needed, this is the
   piece most likely to hide further surprises of the same kind.
4. Wiring the finished lemma into `theorem2`'s `G_CaseFun` second conjunct
   (`curry_test_leftmost.v:8350-8356`), replacing the `admit`.

**Decision (discussed with the user): stop here for this session.** `alpha_renaming_wip.v` is
deliberately a standalone file (not spliced into `curry_test_leftmost.v`), self-contained, and carries
its own header explaining status and the 4 remaining steps above — a documented starting point rather
than a false start, for whichever session picks this up next. `theorem2` itself is unchanged: still
exactly one admit, first conjunct fully `Qed`'d, `curry_test_leftmost.v` compiles clean.

## 20. Same session, continued again: piece 1 (`heap_rename`/composition) finished and verified; piece
2 (batch-extend by a finite list) revealed its own substantial sub-problem — a genuine
permutation/cycle-decomposition argument, not a quick iteration of piece 1

**Finished and verified piece 1.** Added to `alpha_renaming_wip.v`: `nheap_rename` (pointwise:
`nheap_rename sigma tau G w := option_map (rename_b sigma) (G (tau w))`) plus its `hupd`/`hupd_list`
commutation lemmas, and `rename_b`/`rename_e0` composition (`rename_b sigma1 (rename_b sigma2 b) =
rename_b (fun w => sigma1 (sigma2 w)) b`). The composition lemma needed strong induction on `blk_size`
rather than `Blk`'s own auto-generated induction principle — mirroring `curry.v`'s own
`NoBareChoiceB_rename_bound` pattern exactly, since `Blk`'s auto-generated IH doesn't give a usable
hypothesis for branch bodies nested inside `BCase`'s own `brs` list (a recurring theme in this file,
already flagged as **T15**/similar elsewhere). ~246 lines total so far, compiles clean.

**Piece 2 (batch-extend `mutual_inverse_extend` by a finite list of pairs, needed because `NL_Fun`
introduces a whole renaming at once) turned out to be its own substantial sub-problem, not a quick
iteration.** The root issue: `NL_Fun`'s renaming `s` (graph side / first derivation) and the target
`NL_Fun`'s renaming `s2` (second, independently-derived side) are chosen independently, and their
fresh-name *images can overlap with each other* — nothing rules this out, since each renaming is only
required to avoid the *original* heap's domain, not the other side's picks. So the pair `a_i = s(y_i)`
can coincide with an *earlier* pair's `b_j = s2(y_j)` for `j < i`.

Tried two approaches, both invalidated concretely (same discipline as piece 1's own counterexample):
- **Iterating `mutual_inverse_extend` pair-by-pair** fails outright — its own precondition ("both
  points are currently fixed points of the accumulated bijection") can already be false by the time
  pair `i` is reached, if `a_i` collided with an earlier `b_j`.
- **A "CONS a new pair onto the front, shadowing lookup" list-of-pairs construction** looked promising
  by hand-trace (the intuition: later entries shadow earlier ones for the same key, so collisions
  should "just work out"). Coded it up and checked it the same way piece 1's bug was caught — a concrete
  numeric trace with only a *single* pair (`a=5, b=7`, identity base) already reduces to the exact same
  bug as piece 1's very first (buggy) attempt: `tau(sigma(7))` comes out `5`, not `7`. The "shadowing"
  intuition doesn't actually address the base case at all — it was solving a problem (which entry wins
  when there's a naming conflict between pairs) that isn't the same problem as (which entry wins when a
  single pair's own two endpoints need simultaneous redirection).

**What's actually needed:** a genuine finite-permutation/cycle-decomposition argument — "any bijection
between two finite subsets `A, B` (given as parallel lists, matched positionally) extends to a
permutation of `A ∪ B`, identity outside it" — the standard fact behind why an arbitrary permutation of
a finite set decomposes into disjoint cycles. This is a real, self-contained combinatorial lemma, but a
separate one from anything built so far, not a two-line extension of `mutual_inverse_extend`. Not
attempted this session.

**Decision (discussed with the user): stop here again.** This is the third escalation in scope
discovered this session — first the cascading `HeapCorr_fwd_transfer_fwdhere_free` refactor (dead end),
then "closure under renaming" turning out to be the wrong shape entirely (needed a two-sided
bisimulation instead), now this permutation-extension sub-problem inside the bisimulation's own
foundational layer. Each discovery was concrete and load-bearing, not speculative — but the pattern
itself is informative: this gap keeps being deeper than the previous diagnosis suggested. `theorem2`
itself remains unchanged throughout all of this: still exactly one admit, first conjunct fully `Qed`'d,
`curry_test_leftmost.v` compiles clean. `alpha_renaming_wip.v`'s own header is kept current with exactly
this status for whoever (or whichever future session) picks it up next.

## 21. Next session: the permutation-extension gap from §20 turns out to split into a genuinely
clean "single component" piece and a harder "decompose into components" piece; the former is done
and verified, closing PIECE 2a

**Diagnosed why per-pair swapping is the wrong primitive at all, not just wrongly ordered.** §20 found
that iterating `mutual_inverse_extend` pair-by-pair fails when fresh images collide, and guessed the fix
was "apply the swaps in the right order" (a cycle-decomposition argument). Looking closer: even with a
correct order, a plain SWAP `(a,b)` is the wrong operation for an interior link of a chain `a -> b -> c`
in the first place — a swap forces `sigma(b) = a`, but a chain requires `sigma(b) = c`. The right
primitive is "rotate a whole connected chain, treated as one list, by one position" — a genuinely
different, and much more tractable, construction than a sequence of two-point swaps.

**Built and verified `cyc_extend` (`alpha_renaming_wip.v`, PIECE 2a — compiles clean).** Given a `NoDup`
list `l` all of whose points are CURRENTLY fixed points of `(sigma, tau)`, `cyc_sigma`/`cyc_tau` reindex
through `l` and `rotate1 l` (`rotate1 (x::l') = l' ++ [x]`, i.e. head-to-tail): `cyc_sigma l sigma w :=`
look up `w`'s position `i` in `l` (via a hand-rolled `list_index`, since this all has to be a *computable*
function, not just a relation) and return `l`'s rotation at that same position, falling back to the
ambient `sigma` for anything not in `l`. `cyc_extend` proves this is still `mutual_inverse`, and
`cyc_sigma_succ` confirms concretely what it's for: `cyc_sigma l sigma (l_i) = l_{i+1}` for consecutive
positions. No incremental per-pair induction was needed at all — the whole thing is a direct closed-form
definition plus a direct proof, sidestepping the swap-ordering question entirely. The one proof wrinkle:
`rewrite <-` on a goal like `w = sigma w` will happily rewrite *both* occurrences of `w` (including the
one hiding inside `sigma w`) unless pinned with `at 1` — cost two failed attempts before landing on the
right occurrence numbering; recorded as **T19** below (Part 2 glossary) since it's a recurring trap.

**What's still open (PIECE 2b, unstarted): decomposing an arbitrary pair of parallel lists `A, B` into
components ready to hand to `cyc_extend`.** `cyc_extend` handles ONE already-known chain/cycle; the real
application (`NL_Fun`'s two independent renamings `s`, `s2` applied to the same free-variable list `ys`,
giving `A := map s ys`, `B := map s2 ys`) needs the general two-list problem decomposed into however many
disjoint components the edge set `A_i -> B_i` actually has. Confirmed by direct construction that this
really does need genuine graph bookkeeping, not a shortcut: NoDup `A`/NoDup `B` gives out-degree/in-degree
`<= 1`, so the edges form disjoint simple paths and cycles; a closed cycle can go to `cyc_extend` as-is,
but an open path's dangling sink (an element of `B` not itself in `A`, so no required outgoing pair) has
to be wrapped back to its own path's start before `cyc_extend` applies — and finding "its own path's
start" means chasing backward through `B -> A` lookups, which needs its own explicit, provably-terminating
construction (bounded by `length A`, since a non-cyclic backward chase can't revisit a vertex). Not
attempted yet this session; `alpha_renaming_wip.v`'s header carries the precise remaining shape of this
so a future session doesn't have to re-derive it.

**Status: theorem2 itself still unchanged (one admit, as in §17-20).** This session's work is entirely
within the standalone `alpha_renaming_wip.v`; `curry_test_leftmost.v` was not touched and still compiles
clean.

## 22. PIECE 2b (decomposing the two-list permutation-extension problem into components) AND 2c (the
full batch-extend theorem) both built and fully verified in the same session, zero admits — the general
combinatorial gap from §20/§21 is closed completely

**Closed PIECE 2b in full.** Represented the "required pairs" as a single `ps : list (var*var)` (rather
than two parallel lists `A B`, to avoid ever having to argue they stay positionally aligned under
filtering) and built, in order:
- `fwd`/`fwd_in`/`fwd_complete`/`fwd_injective` — `fwd ps w` looks up `w`'s required target in `ps`;
  injective on its domain given `NoDup (map snd ps)` (two entries sharing a target force their sources
  equal, by a direct induction on `ps`, `pair_snd_nodup_fst_unique`).
- `is_chain`/`is_chain_snoc` — an index-based (`nth_error`) notion of "consecutive elements are `fwd`-
  linked", and a lemma for extending a chain by one more validated link.
- `chain_no_premature_repeat` — the combinatorial crux: within a NoDup chain, the ONLY vertex the chain's
  own last link can legally jump back to is the chain's own FIRST vertex (any other target would need two
  distinct predecessors mapping to the same value via `fwd`, contradicting injectivity + `NoDup_nth_error`
  positional uniqueness). This is what makes "rotate the whole component" well-defined at all — it rules
  out a chain silently re-merging into itself partway through.
- `chase`/`chase_invariant` — a fuel-bounded forward walk, proven (by induction on fuel) to never
  truncate a genuine chain early: the key device is a running pigeonhole bound `length ps <= fuel +
  length acc + 1` (elements already visited, all distinct and all genuine `ps`-sources, can't exceed
  `length ps` of them) that turns "fuel ran out mid-chain" into a direct numeric contradiction via
  `NoDup_incl_length`, so `chase` only ever stops at a real dead end (`fwd = None`) or by closing back to
  its own start (`fwd = Some start`) — never because it ran out of gas.
- `component`/`component_invariant`/`component_pair_realized` — the payoff: for ONE starting vertex `v0`,
  `component ps v0`'s whole connected chain gets captured, and EVERY required pair `(a,b) ∈ ps` with `a`
  landing in that component is realized by `cyc_sigma` — an interior link via `cyc_sigma_succ`, the
  component's own closing link via a new `cyc_sigma_wrap` (mirroring `cyc_sigma_succ` for the
  last-position-wraps-to-first case), using `chase_invariant`'s "never stops early" guarantee to know a
  closing link is always either absent or points back to `v0`, never to some other, wrong earlier vertex.

**Confirms directly why the two failed approaches from §20 don't come back to bite this construction.**
Both prior failures (naive pair-by-pair `mutual_inverse_extend` iteration, and the "shadowing lookup"
list-of-pairs idea) came from trying to build the bijection *incrementally*, one pair at a time, which
requires getting an ordering right that neither approach actually got right. `cyc_sigma`/`cyc_tau` are
never built incrementally at all — they're a single monolithic closed-form definition over the WHOLE
already-assembled component list (`list_index` into it and its `rotate1`), so there is no "pair `i`'s own
precondition can already be broken by pair `j`'s effect" failure mode to worry about; the entire
combinatorial difficulty is isolated inside `chase`/`chase_invariant` (correctly *assembling* the
component list once), not in applying it.

**PIECE 2c (the full batch-extend theorem): attempted immediately after 2b in the same session, and
turned out NOT to be pure bookkeeping — it needed one more real insight.** The naive plan ("pick `v0 :=
hd` of what's left, apply `cyc_extend`, filter out its component, recurse") is *unsound* as stated: picking
`v0` arbitrarily risks starting the chase partway down an open path, silently missing everything upstream
of it. Concretely, if some `p` (not reachable *forward* from `v0`) satisfies `fwd ps p = Some v0`, then
`component ps v0` never discovers `p` at all — `chase` only walks forward. Filtering `ps` by "source lands
in `component ps v0`" would then leave `(p, v0)` in the remainder, but `v0` itself is no longer a
`sigma`-fixed point after `cyc_extend` (it got rotated to the component's own second element) — breaking
the very invariant (`sigma` fixed on the remaining `ps`'s domain+range) the recursion depends on.

**The fix: `pick_source`.** Prefer, whenever one exists, a genuine PURE SOURCE — an element of `map fst ps`
that is *not itself* anyone's target (`~ In v0 (map snd ps)`), found via a single linear scan
(`find`/`has_pred`). A pure source is provably never a non-start element of any path, so chasing forward
from it can't miss an upstream predecessor. When NO pure source exists, a genuine NoDup/cardinality
argument (`pick_source_all_cycle_snd_subset_fst`, via `NoDup_length_incl`: `map fst ps ⊆ map snd ps` as
sets, both the same size by `NoDup`, forces equality) shows `ps`'s *entire* remaining structure has to be
pure closed cycles — so an arbitrary start is fine there, since every vertex in a closed cycle has both a
predecessor and a successor already inside it. Either way this delivers `component_backward_closed`: for
`(a,b) ∈ ps`, if `b` lands in the chosen `v0`'s component then so does `a` — exactly the fact needed to
filter `ps` safely (nothing consumed by this step can still be dangling as a stray target in what's left)
and to know the recursive result doesn't disturb pairs the current step already realized (via a matching
third conjunct threaded through `batch_extend`'s own statement: `sigma'` agrees with the input `sigma`
outside `ps`'s whole domain+range, needed to bridge sigma1's realized pairs across the recursive call).

**`batch_extend` itself is now the finished statement**: given `ps` (`NoDup` on both projections) and
`(sigma, tau)` already fixed on `ps`'s whole domain+range, produces `(sigma', tau')` that's still
mutual-inverse, realizes *every* pair in `ps`, and agrees with `sigma`/`tau` outside `ps`'s domain+range —
proved by `well_founded_induction lt_wf` on `length ps` (the same idiom piece 1's `rename_b_comp_bound`
already used), consuming at least one pair (`v0`'s own) each step.

**Practical fallout from actually writing all of this and getting it through `coqc`**: two recurring stdlib
traps cost most of the 2b iteration — `List.In`'s unfold direction (`elem = query`, not `query =
elem`) inverting `eq_sym` usage silently, and several extremely common list lemmas
(`nth_error_app1`/`app2`, `app_nth2`, `Permutation_cons_append`, `NoDup_cons`) marking a
looks-explicit index/list argument as actually implicit, so a positional call silently misaligns instead
of failing to typecheck at the call site. Recorded in detail as **T20** below. 2c surfaced a third, sharper
one — `destruct (compound_expr) eqn:H` doesn't just case-split the goal, it rewrites *every other
hypothesis* that happens to mention the exact same compound expression, silently changing their stated
types out from under later tactics — recorded as **T21**.

**Status: theorem2 itself still unchanged (one admit).** All of this session's work is again entirely
within the standalone `alpha_renaming_wip.v` (now 1151 lines, compiles clean end to end, `grep -c admit`
returns only comment references, zero actual admits); `curry_test_leftmost.v` was not touched. The
alpha-renaming-invariance lemma's whole foundational layer (pieces 1a/1b/2a/2b/2c) is now complete and
fully `Qed`'d — only PIECE 3 (the 11-rule simultaneous induction) and PIECE 4 (wiring the result into
`theorem2`) remain before the admit itself can close.

## 23. Next session: PIECE 3 started — all three of its prerequisites built and verified, the target
statement itself written down and typechecks, and a real scope reduction found along the way

**Checked batch_extend's interface against what PIECE 3's `NL_Fun` case would actually need (before
attempting PIECE 3 itself), and it holds up**, with one caveat traced through concretely: `NL_Fun`'s own
freshness premise (`G (s y) = None` for non-parameter `y`) is one-sided per derivation, so satisfying
`batch_extend`'s `Hfix` precondition needs PIECE 3 to carry a "sigma's support stays inside the two heaps'
current domains" invariant across its whole induction — which should come for free if PIECE 3's own
per-step correspondence is stated via piece 1's `nheap_rename` rather than a fresh domain-matching lemma
(confirmed this session — see below).

**Built and verified all three prerequisites that check surfaced, zero admits:**
- `vars_of_b`/`vars_of_e0` — every syntactic variable POSITION `rename_b`/`rename_e0` touch. Checking
  `rename_b`'s own definition confirmed it renames `BLet`/`BCase`'s *bound* variables too, not just free
  ones — so this needs no real binding/shadowing analysis, just a structural walk mirroring `rename_b`
  itself. Simpler than the `free_vars_b` placeholder from the piece-2 TODO list assumed.
- `rename_b_congr`/`rename_e0_congr` — pointwise agreement of two renamings on `vars_of_b b` implies
  `rename_b` agrees on the whole `b`. Same proof shape as `rename_b_comp` (strong induction on `blk_size`,
  `BCase`'s own auto-generated IH still not usable for nested branch bodies) — this is what turns
  `batch_extend`'s per-*pair* guarantee into the actual *term* equality PIECE 3's own IH will need.
- `NHeapAlpha` — the bisimulation invariant relating two `NHeap`s across a mutual-inverse pair, deliberately
  stated as pointwise equality to `nheap_rename` (`NHeapAlpha sigma tau Gam1 Gam2 := forall w, Gam2 w =
  nheap_rename sigma tau Gam1 w`) rather than inventing a fresh relation — this makes `NHeapAlpha_hupd`/
  `NHeapAlpha_hupd_list` nearly free (`nheap_rename_hupd`/`_hupd_list` were already `Qed`'d in piece 1b).
  `NHeapAlpha_domain` confirms the domain-matching fact the containment invariant needs falls straight out
  of `NHeapAlpha`'s own definition (`option_map`'s None-preserving behavior) — no separate lemma needed,
  exactly as hoped when the interface was first checked.

**Wrote PIECE 3's actual target statement, `NEval_left_self_confluence`, and it typechecks** (currently
`Admitted` — the file's one honest, deliberately-flagged gap, versus zero everywhere else):

```coq
Theorem NEval_left_self_confluence :
  forall P F Gam e Gam1 v1, NEval_left P F Gam e Gam1 v1 ->
  forall Gam2 v2, NEval_left P F Gam e Gam2 v2 ->
  exists sigma tau, mutual_inverse sigma tau /\ NHeapAlpha sigma tau Gam1 Gam2 /\ v2 = rename_b sigma v1.
```

**The scope reduction: this is deliberately narrower than section 19's original design, and that's
correct, not a shortcut.** Section 19 called for a full bisimulation over "alpha-related expressions from
alpha-related heaps." Re-checking exactly what `G_CaseFun`'s own admit needs, against section 18's own
diagnosis: the two derivations being reconciled there (`Hrec1` via `IH1`, and the arbitrary `Hforce`) force
the *same* expression (`BExpr (EVar x0)`) from the *same* heap `Gam` — not independently alpha-varied
expressions from independently-related heaps. `NEval_left_self_confluence` captures exactly that, no more:
same `P`, `F`, `Gam`, `e` on both sides, `Gam1`/`v1` vs. `Gam2`/`v2` as the two (possibly different)
outcomes. This is strictly easier to work with going forward — no expression-shape matching is needed at
each induction step, since `e` being identical on both sides already forces the *same* `NEval_left`
constructor to fire (which constructor applies is pinned by `G`'s own concrete value at each step) EXCEPT
at the two genuine nondeterminism sources, `NL_Fun`'s choice of `s` and `NL_Guess`'s choice of `ws` —
exactly the two cases `batch_extend` exists for. Confirmed the deterministic cases' own shape-matching
machinery (`NEval_left_evar_shape` and friends, `curry_test_leftmost.v`) already exists and is reusable,
not something PIECE 3 needs to build from scratch.

**Required pulling `curry_test_leftmost` into `alpha_renaming_wip.v`** (`NEval_left` lives there, not in
`curry.v`) — checked first for name collisions with everything already defined in this file; found none.
This is the first point the file stops being fully standalone, which is fine: piece 4 wires into
`curry_test_leftmost` anyway.

**One small new gap surfaced, not yet built**: `rename_b_id`/`rename_e0_id` (renaming by the identity
function is a no-op) — needed for the deterministic base cases (e.g. `NL_ValCon`, where both derivations
are forced identical) to instantiate `sigma := tau := id` and close via `mutual_inverse_id` (already built,
piece 1a). Likely a one-line induction, just not written yet.

**Not yet attempted: actually proving `NEval_left_self_confluence`** across all 11 `NEval_left`
constructors. That's still the real remaining work — this session got the statement pinned down precisely
and every prerequisite it needs built and verified, which is the natural place to stop before the
11-case induction itself, matching how pieces 2a/2b/2c were each staged.

**Status: theorem2 itself still unchanged (one admit).** `alpha_renaming_wip.v` is now 1354 lines,
compiles clean end to end, with exactly one `Admitted` (the target statement itself, deliberately) versus
zero everywhere else. `curry_test_leftmost.v` was not touched.

## 24. Same session, continued: found the statement itself needed two real corrections before the
11-case induction could even start, then closed 8 of the 11 cases

**Both corrections were found by tracing a case through on paper (specifically `NL_Fun` and `NL_VarExp`)
before writing any of the induction, not discovered mid-proof.** That discipline paid off directly — both
would have been much more expensive to unwind after several cases were already built on the broken
statement.

**Correction (a): `NEval_left_self_confluence` (last session's draft) is true, but can't be its own
induction hypothesis.** `NL_Fun`'s two continuations, `rename_b s1 body` and `rename_b s2 body`, are only
*related* by a renaming, not literally the same expression — so recursing into them can't reuse a
same-expression/same-heap statement about themselves. Worse: once expressions diverge, the two
derivations' own heaps diverge too (each side's `hupd` calls only ever touch its own output heap), so
"the same shared `Gam`" isn't even available past the first `NL_Fun`/`NL_Guess` step. Fixed by making the
real inductive statement, `NEval_left_confluence`, properly general: two heaps related by `NHeapAlpha`,
two expressions related by `rename_b sigma0` for an ambient `(sigma0, tau0)` — i.e. exactly the shape
section 19 originally called for. `NEval_left_self_confluence` comes back as a one-line corollary at
`sigma0 := tau0 := id`, needing two new small lemmas: `rename_b_id`/`rename_e0_id` (renaming by the
identity is a no-op — genuinely needed anyway, not just for this) and `NHeapAlpha_refl`.

**Correction (b): a single shared guard list `F` breaks at `NL_VarExp`.** `D1`'s recursive premise grows
its guard to `x :: F`; `D2`'s (via `NEval_left_evar_shape`) grows its own to `(sigma0 x) :: F`. These are
literally the same list only when `sigma0 x = x` — not guaranteed, since `sigma0` might already move `x`.
Fixed by tracking the two guard lists as *related* rather than shared: `F2 = map sigma0 F1`, threaded as
its own hypothesis rather than assumed equal. This also simplified the conclusion: instead of carrying a
separate "sigma0 fixes F" hypothesis/conclusion pair, the single "extends" conjunct
`sigma0 w <> w \/ Gam1 w <> None \/ Gam2 w <> None -> sigma w = sigma0 w` covers everything needed —
the third disjunct (location already in either heap's domain) is exactly what lets `NL_VarExp` conclude
`sigma x = sigma0 x` from the IH's own conclusion (since `x` is trivially in `Gam1`'s domain, having just
been looked up there), with no separate invariant to carry.

**Closed 8 of the 11 `NEval_left` constructors, all `Qed`'d**: `VarCons`, `VarSelf`, `VarFree`, `VarExp`
(deterministic cases via `NEval_left_evar_shape`'s existing shape-inversion, or hand-rolled
`remember`/`revert`/`destruct` for the ones without a ready-made shape lemma — `ValFree`, `ValCon`, `Or`);
`Let` turned out tractable too (needing one new lemma, `let_content_rename`: `let_content` commutes with
renaming, since `let_content` special-cases `EFree` to `EVar x` and both sides of the equation need that
same special-case to line up). Three small "`rename_b` preserves top-level shape" facts
(`rename_b_not_econ`/`_not_evar`/`_not_efree`) were needed for `NL_VarExp`, to know D2's own shape-
inversion is forced into the *same* constructor as D1's (not just *a* valid one).

**A genuinely new stdlib-adjacent trap surfaced while writing the hand-rolled shape-inversion cases**:
`destruct H eqn:Heq` where `H`'s type contains a *compound* index (here, `e2` after `subst`, or `F2` after
`subst`) needs that compound term abstracted via `remember` first — but `remember X as y eqn:Heq` only
rewrites occurrences that are already present when it runs; anything that becomes syntactically equal to
`X` only *later* (e.g. a different index position that the constructor match forces to the same value)
does **not** retroactively get the `y`-treatment, and shows up as a fresh, unrelated variable (`F1a`)
needing its own explicitly-reverted equation (`HF2eq`) to relate it back. Cost real iteration on `NL_Or`
before landing on: revert *every* hypothesis whose later use depends on the destructed index's own
identity, not just the one literal term being remembered.

**What's left**: `NL_Fun` and `NL_Guess` need `vars_of_b body` + `batch_extend` to reconcile the two
independently-chosen renamings/fresh lists, exactly per the plan already recorded in `alpha_renaming_wip.v`'s
own header. `NL_Select` turned out to be genuinely as hard as those two, not a quick win: `BCase`'s own
shape-inversion is a two-way disjunction (`NL_Guess` *also* concludes on `BCase x brs`), so ruling out D2
picking the `Guess` shape needs `IH1` (applied to the scrutinee-forcing sub-derivation) invoked *first*, to
show D2's own scrutinee-forcing is provably `ECon`-shaped too — a proper two-step argument, matching the
same level of intricacy as `curry_test_leftmost.v`'s own `G_CaseChoice`/`G_CaseFun` proofs.

**Status: theorem2 itself still unchanged (one admit).** `alpha_renaming_wip.v` is now 1688 lines,
compiles clean end to end. `NEval_left_confluence` carries exactly 3 admits (`NL_Fun`, `NL_Select`,
`NL_Guess`), each with a precise in-proof comment on what it needs; everything else in the file — all of
pieces 1a/1b/2a/2b/2c, plus the 8 closed `NEval_left_confluence` cases and every prerequisite lemma built
this session — is fully `Qed`'d. `curry_test_leftmost.v` was not touched.

## 25. Same session, continued again: a THIRD correction to the statement (found, same discipline, by
tracing NL_Fun through by hand before coding it) — fixed and re-threaded through all 8 cases; NL_Fun
itself traced all the way through except for one genuinely new, deeper gap

**Traced `NL_Fun`'s case by hand before writing any of it**, same discipline as corrections (a)/(b) last
session. Found immediately that `batch_extend`'s `Hfix` precondition (`sigma0` already fixes the pairs
list's domain+range) has no support: nothing about `mutual_inverse`/`NHeapAlpha` alone stops an
*adversarial* `sigma0` — satisfying every other hypothesis in the theorem — from happening to move one of
the two independently-fresh locations `s(y)`/`s2(y)`. This isn't a proof-technique gap; the theorem as
stated really would be false without some containment fact.

**Fixed with `Hcontain0`/`Hcontain`**: `sigma0`'s support must already avoid the region *both* heaps leave
undefined (`forall w, sigma0 w <> w -> Gam1 w <> None /\ Gam2 w <> None`), threaded as both hypothesis and
matching conclusion conjunct, same shape as the "extends" conjunct from correction (b). Re-proved all 8
already-closed cases — mostly mechanical (reuse `Hcontain0` directly when the heaps don't change, or lift
it through one `hupd` via a new `hupd_preserves_some` when they do). Two new reusable lemmas:
`NoDup_map_inj` (the image of a `NoDup` list under an injective function is `NoDup` — needed for
`batch_extend`'s own `NoDup` preconditions on the pairs list) and `Hcontain_None_fixed` (the
OR-contrapositive of `Hcontain0`: *either* heap being undefined at `w` already forces `sigma0 w = w` — used
once per side, since each fresh location is only known undefined in *its own* heap).

**With that fix in place, traced `NL_Fun`'s entire remaining argument through by hand, and it holds —
until the very last step.** Built: the batch pairs (`vars_of_b body`, filtered to exclude parameters `ps`
and deduplicated via `nodup`), `NoDup` of both projections (`NoDup_map_inj` + injectivity of `s`/`s2`), the
`Hfix` argument for non-parameters (`Hcontain_None_fixed` + each side's own freshness premise), and a
genuine, non-obvious 8-step argument that a *parameter's* image `s(x)` can never collide with some *other*
position's `s2(y)`: assuming `s(x) = s2(y)`, `D2`'s own freshness (`Gam2 (s2 y) = None`) plus
`Hcontain_None_fixed` gives `sigma0 (s2 y) = s2 y`; substituting the assumed equality gives
`sigma0 (s x) = s x`; combined with the *independently*-derived parameter-matching fact
`s2 x = sigma0 (s x)` (from `Hmatch`/`Hmatch2` + `map_nth_error`), that forces `s2 x = s(x) = s2 y`, and
`s2`'s own injectivity then forces `x = y` — contradicting `x ∈ ps`, `y ∉ ps`. All of that goes through
cleanly with `batch_extend`, `rename_b_comp`, and `rename_b_congr`.

**Where it stops: a genuine fourth gap, not yet fixed.** Applying the outer induction's own `IH` to
`body`'s continuation needs `map sigma F0 = map sigma0 F0` (`sigma` being `batch_extend`'s output) — i.e.
`sigma` must agree with `sigma0` on *every* element of the guard list `F0`. Via `batch_extend`'s own
"outside the pairs list" guarantee, this needs every `w ∈ F0` to satisfy both `w <> s(y)` (clean: `F0 ⊆
dom(Gam1)` by a "guard elements are already-forced locations" argument, and `s(y)` is fresh w.r.t. `Gam1` —
same heap, no issue) **and** `w <> s2(y)` (not clean: `w`'s membership in `dom(Gam1)` says nothing about
`dom(Gam2)`, and `s2(y)`'s freshness is a `dom(Gam2)` fact — nothing yet connects the two heaps' domains
*pointwise*, only via the `sigma0`-*shifted* `NHeapAlpha` correspondence, which relates `dom(Gam1)` to
`dom(Gam2)` only after applying `sigma0`, not before). Tried multiple routes to derive this from what's
already in scope (`NHeapAlpha`'s domain fact, `Hcontain0` itself); all blocked the same way — comparing
`sigma0(w)` against `s2(y)` (which the tools in hand can do) is a different claim from comparing `w`
against `s2(y)` (which is what's actually needed), and the two only coincide when `sigma0` happens to fix
`w`.

**The real fix, not yet built: a fourth hypothesis/conjunct pair** — "every element of `F1` is already
inside `Gam1`'s domain" (and the matching fact for `F2`/`Gam2`) — threaded through the whole induction
exactly like `Hcontain0`/`Hcontain` was this session. Unlike `Hcontain0`, this one is genuinely **not**
true of `NEval_left` in general: nothing in the relation's own rules stops an arbitrary top-level `F` from
containing locations unrelated to `G`'s domain (e.g. `NL_ValCon` holds for *any* `F` whatsoever, checking
nothing about it). It's only true because every actual *use* of `NEval_left` in this codebase starts `F` at
`nil` and grows it exclusively via `NL_VarExp`'s own `x :: F` (which does preserve "guard ⊆ domain", since
`x` is added exactly when `G x = Some e`). So it has to be an explicit hypothesis of the theorem, not
something derivable from what's already there — confirmed by trying, not just assumed.

**This matches the project's own recurring pattern** (see §20's "third escalation... this gap keeps being
deeper than the previous diagnosis suggested") almost exactly, one level down: each of the three
corrections found this session/continuation was concrete and load-bearing, not speculative, and each was
caught by tracing a case through by hand *before* writing any Rocq for it — not discovered mid-proof. That
discipline is exactly what made this a same-session finding rather than a wasted afternoon of retrofitting.

**Status: theorem2 itself still unchanged (one admit).** `alpha_renaming_wip.v` is now 1834 lines,
compiles clean end to end, zero unplanned admits (`NL_Fun`/`NL_Select`/`NL_Guess` remain, each precisely
diagnosed in its own in-proof comment — `NL_Fun`'s now documents the full argument up to exactly where the
fourth gap bites). `curry_test_leftmost.v` was not touched.

## 26. Next session: the fourth gap fixed and threaded through everything, NL_Fun's ENTIRE argument now
goes through in actual Rocq up to a fifth, narrower gap — and that one is genuinely deep

**Fixed the fourth gap from §25 in full.** Added `HFdom1`/`HFdom2` — "`F1`/`F2` are already inside
`Gam1`/`Gam2`'s own domain" — as a new hypothesis pair to `NEval_left_confluence` (no matching conclusion
conjunct needed, unlike `Hcontain0`/`Hcontain`: checking all 11 `NEval_left` constructors confirmed the
guard list `F` only ever *grows* at `NL_VarExp` — every other constructor either leaves `F` untouched or
only changes the *heap* — so `HFdom1`/`HFdom2` never need to flow back out through a conclusion, only get
locally extended at the one case that grows `F`). Re-threaded through all 8 already-closed cases: purely
mechanical — direct reuse where `F`/heap don't change, one `hupd_preserves_some` lift where the heap grows
(`NL_Let`), one real extension at `NL_VarExp` (`w = x` case discharged directly, `w ∈ F0` case via the
unchanged hypothesis). Also added the same hypothesis to the `NEval_left_self_confluence` corollary itself
(trivially satisfiable whenever the caller's own `F` is `nil`, which matches every actual call site in this
codebase).

**With `Hcontain0` (§25) and `HFdom1`/`HFdom2` (this session) both available, traced `NL_Fun`'s entire
argument through *in actual Rocq* — not just on paper — up through the exact fact flagged as blocking last
time: `sigma` (`batch_extend`'s output) agrees with `sigma0` on the whole guard list `F0`.** The insight
that unblocks it: combine the two hypotheses via a case split on whether `sigma0` fixes a given `w ∈ F0`,
rather than reaching for either alone (which is exactly what last session's diagnosis missed — it
considered `Hcontain0` and a domain fact separately, concluded neither sufficed alone, and stopped without
trying the combination). If `sigma0 w ≠ w`, `Hcontain0` directly gives `Gam2 w ≠ None`. If `sigma0 w = w`,
`HFdom2` (applied at `sigma0 w`, which is `w` in this case) gives it instead. Either way `w ∈ dom(Gam2)`,
which combined with `s2(y)`'s freshness (`Gam2 (s2 y) = None`) is exactly what's needed to rule out
`w = s2(y)`. This closed cleanly with only one small direction-of-equality fix needed (`Some (ps2,body2) =
Some (ps,body)` needed `symmetry` before `exact HPf2`) — the *entire* multi-step argument (batch pairs
construction, `NoDup` via injectivity, the 8-step parameter-collision argument from §25,
`rename_b_comp`/`rename_b_congr`, and now this F0-agreement argument) compiled essentially as planned.

**Stops at a fifth, narrower gap, and this one turned out deeper than it first looked.** Applying the
outer `IH` to `body`'s own continuation also needs `NHeapAlpha sigma tau G0 Gam2` (the *new* `sigma`/`tau`,
not the ambient `sigma0`/`tau0` — the heaps themselves don't change at `NL_Fun`, only the renaming pair
does) — and `batch_extend`'s own "agrees outside the pairs list" guarantee (`Houtside`) is stated only for
`sigma'`, never for `tau'`. The first guess — "just add a symmetric `tau'`-outside conjunct to
`batch_extend`" — doesn't actually dissolve the problem on its own: rewriting `NHeapAlpha` through
`mutual_inverse` into a form quantified over the *source* location instead of using `tau` to look one up
(`forall z, Gam2 (sigma z) = option_map (rename_b sigma) (G0 z)`) sidesteps needing anything about `tau'`
specifically, but for a source `z` outside the pairs list (where `sigma z = sigma0 z` follows from
`Houtside` alone, no `tau'` fact needed) it still needs `G0`'s own *stored value* at `z` to only mention
variables that are *also* outside the pairs list — i.e., needs the fresh locations `s(y)`/`s2(y)` to be
unreferenced not just as heap *keys* (`G0 (s y) = None` — the only freshness fact freshness premises give)
but as *values* stored somewhere else in the heap too. That's a fundamentally different kind of freshness
— a heap/value well-formedness invariant — that nothing in this file currently tracks, and it isn't obvious
it's even the most direct fix rather than a symptom pointing at a different one.

**Deliberately stopped here rather than guess further.** Three real gaps in a row (`c`/`d`/this one) were
each found by tracing a case through *before* coding it, and the first two went from "diagnosed" to "fully
`Qed`'d and re-threaded through 8 cases" within the same session they were found — a genuinely fast
turnaround, matching how corrections (a)/(b) went last time too. This fifth one doesn't have an equally
clean candidate fix yet, and forcing one through without being sure it's the *right* invariant (rather than
another layer masking a deeper issue) risks the kind of wasted-afternoon retrofitting the "trace before
coding" discipline exists to avoid. A good point for a fresh diagnosis pass, possibly by re-examining
whether `NEval_left`'s own well-formedness premises (`ProgWF`/`NoBareFreeOrChoiceProgWF`, used throughout
`curry_test_leftmost.v`'s `theorem2` but not yet threaded into this file at all) already rule out the
"stored value references a location outside its own domain-closure" scenario, rather than inventing a new
invariant from scratch.

**Status: theorem2 itself still unchanged (one admit).** `alpha_renaming_wip.v` is now 1940 lines,
compiles clean end to end, zero unplanned admits. `curry_test_leftmost.v` was not touched.

## 27. Same session, continued: the fifth gap sharpened from a described failure case into a named,
buildable invariant — checked, not guessed

**The user asked the natural next question about §26's fifth gap**: if a fresh location `s(y)` genuinely
can't be a heap *key* yet, how could some *other* cell's stored content possibly reference it as a value —
wouldn't that mean the heap already had a dangling pointer before the function call even started? Exactly
right semantically, and it's the key that turns "not even clear this is the right fix" into a concrete plan.

**Checked, rather than assumed, that nothing already covers this.** `ProgWF` (`curry.v`) only asserts
`NoBareChoiceB` on function bodies; `NoBareFreeOrChoiceProgWF` (`curry_test_leftmost.v`) only rules out bare
`free`/`choice` at a tail position. Neither says anything about *scoping* — i.e. neither says that every
variable a stored term mentions is itself already bound. Grepped the whole codebase for `closed`/`Scoped`/
`WellScoped` too: every hit is "proof closed" (an unrelated, purely textual sense), not a heap-scoping
notion. So the fact really is semantically true (well-scoped source + `NL_Let` being the only rule that
ever writes a fresh cell, always with content whose own free variables must already be bound by an
enclosing binder) but genuinely **not yet formalized anywhere** in this codebase — `NL_Let`'s own rule has
exactly one heap premise (`G x = None`, the *new* cell is fresh) and no premise at all constraining `e`'s
own free variables. That check is currently just *assumed* to hold externally, not proven.

**This reframes the fifth gap from "maybe the wrong fix entirely" into three concrete, standard pieces,
none built yet:**
1. A **"closed heap"** predicate — `forall z b, G z = Some b -> forall w, In w (vars_of_b b) -> G w <>
   None` (every stored value's own variable references are themselves already bound). `vars_of_b`
   (piece 3's own prerequisite, already built and `Qed`'d) is directly reusable here.
2. A **preservation lemma** — `NEval_left` maintains closedness (likely needs, for `NL_Fun`'s own case
   specifically, that the *source* function body is well-scoped relative to its own parameter list — a
   fact about `P` that doesn't currently have a name either, and would need its own hypothesis threaded
   through, matching how `Hcontain0`/`HFdom1`/`HFdom2` were each added this session).
3. Confirming the **actual call site** (wherever `theorem2`'s `G_CaseFun` case eventually invokes this
   corollary) starts from a closed heap — plausible almost by construction, but not yet checked.

This is a genuinely standard *kind* of invariant in operational-semantics formalizations (closedness/
scope-safety is usually one of the first lemmas proven about any heap-based semantics), which is
reassuring — but it's still real, unstarted work, and likely needs its own new well-scoping definition on
`P`/function bodies (nothing existing captures "every free variable in this body is a parameter or
introduced by an earlier binder") before the preservation lemma can even be stated.

**Status unchanged**: `alpha_renaming_wip.v`'s own comments (header + `NL_Fun`'s in-proof comment) updated
to match this sharper diagnosis; no code changes this pass. Still one admit in `theorem2`, still zero
unplanned admits in `alpha_renaming_wip.v`, `curry_test_leftmost.v` still untouched.

---

## 28. Same session, continued: actually building the ClosedHeap piece — 7 of 11 cases close outright,
the remaining 4 sharpen §27's plan further

**The user said "let's start there"** — building §27's piece (1)+(2) for real: the `ClosedHeap` predicate
and its preservation lemma, traced by hand before coding as usual.

**`ClosedHeap`**, defined exactly as sketched in §27:
```
Definition ClosedHeap (G : NHeap) : Prop :=
  forall z b, G z = Some b -> forall w, In w (vars_of_b b) -> G w <> None.
```

**The preservation attempt turned up a genuine simplification worth recording.** `NEval_left`'s 11
constructors split cleanly into two kinds:
- **"Heap-pointer-mediated"** (`VarCons`/`VarSelf`/`VarFree`/`VarExp` — every one with a `G x = Some e`
  premise): closedness of whatever the rule *finds* is derivable "for free" from `ClosedHeap G` applied at
  that premise — **no separate "is e closed" input hypothesis is needed at all**, because the very
  existence of the given `NEval_left` derivation already forces it (if `e` weren't already bound, no rule
  could have concluded anything about it in the first place). This is a strictly stronger/cleaner fact than
  what was originally guessed (an outer "e is closed" hypothesis threaded through everything) — the outer
  hypothesis turned out to be simply unnecessary for this half of the cases.
- **"Reveals brand-new syntax"** (`ValCon` at the leaf, and — the real content — `Let`/`Fun`/`Select`/
  `Guess`, each of which pulls a *whole new Blk term* in from the program or from `e`'s own immediate
  structure, never via a heap pointer): no such free lunch, and `vars_of_b` turns out to be **the wrong
  tool** for stating what would even be needed. `vars_of_b` conflates a term's genuinely free variables
  with ones a `BLet`/`BCase` *inside that very term* binds for itself — concretely, `vars_of_b (BLet z EFree
  (BExpr (EVar z))) = [z; z]`, yet that whole term is closed under the **empty** heap (`z` needs no
  pre-existing binding; it gets one from the let itself). Stating a correct hypothesis for these 4 cases
  needs an actual free-variable analysis (tracking a growing bound-set through `BLet`/`BCase` binders,
  something this file has never built), not just reusing `vars_of_b`.

**Result**: `NEval_left_closed_preserved` (`alpha_renaming_wip.v`, PIECE 5, right before
`NEval_left_confluence`) — 7 of the 11 cases (`VarCons`, `VarSelf`, `VarFree`, `VarExp`, `ValFree`,
`ValCon`, `Or`) are fully `Qed`-quality and **compiled clean on the first attempt**, confirming the by-hand
trace was right. The other 4 (`Let`, `Fun`, `Select`, `Guess`) are `admit`s with per-case comments pinpointing
exactly where each stalls; the theorem itself is `Admitted`.

**This sharpens §27's plan (2) rather than replacing it.** The preservation lemma can't even be *stated*
correctly for the binder-introducing cases without a real free-variable function first — so the next step
isn't "keep proving preservation," it's building that free-variable analysis (bound-set-aware, unlike
`vars_of_b`) plus, per §27's own point, a well-scopedness fact about `P`'s function/branch bodies stated in
terms of it. Only then can `Let`/`Fun`/`Select`/`Guess` be attempted.

**Status**: still one admit in `theorem2`, `curry_test_leftmost.v` still untouched. `alpha_renaming_wip.v`
still compiles clean with exactly the expected admits (4 new, in `NEval_left_closed_preserved`, plus the 3
pre-existing ones in `NEval_left_confluence`) — no unplanned admits or errors.

---

## 29. Same session, continued: `NEval_left_closed_preserved` fully closed — all 11 cases, zero admits

**The user said "let's start on that"** — go build §28's plan (the real `free_vars_b` plus
`FunBodyWellScoped`) and use it to close the 4 cases left open. Reordered `alpha_renaming_wip.v` so PIECE 6
(the free-variable machinery) sits *before* PIECE 5's theorem, since the restated theorem needs
`free_vars_b`/`FunBodyWellScoped` in scope — a mechanical `sed`-based block move, verified compile-clean
before writing a single line of new proof.

**PIECE 6 built cleanly, with one genuine finding worth recording.** `free_vars_b` (bound-set-aware,
correctly excluding `BLet`/`BCase`'s own bound variables) plus `free_vars_b_rename_subset` — the key lemma
needed for `NL_Fun`/`NL_Select`/`NL_Guess`, all of which apply a renaming/substitution to a term pulled in
from elsewhere. Initially expected this would need `s` injective (mirroring `rename_b_congr`'s own
injectivity-flavored uses elsewhere in this file), but tracing it by hand showed the **subset** direction
(a renamed term's free variables are always among the *images* of the original free variables — substitution
can only *lose* apparent free variables via variable capture, never *create* new ones) holds for **any** `s`,
injective or not. This mattered concretely: `zipsubst` (used by `NL_Select`/`NL_Guess`) is *not* generally
injective, so needing injectivity here would have blocked those two cases outright.

**`NEval_left_domain_mono`** (a simple standalone induction: `NEval_left` only ever *grows* a
heap via `hupd`/`hupd_list`, never shrinks it) turned out to be needed too, to carry a closedness fact
established against the *pre-scrutinee-forcing* heap (`G0`/`G1` before `NL_Select`/`NL_Guess`'s own
recursive premise 1) forward to the heap the branch body is actually evaluated against.

**Restating the theorem**: `free_vars_b` for `e`'s own closedness (the input hypothesis), but **`vars_of_b`**
kept for `v`'s (the conclusion) — since `v` is always one of the 3 terminal shapes (`ECon`/`EVar`/`Free`,
never `BLet`/`BCase`), the two coincide for `v` regardless, and `vars_of_b`'s *stronger* guarantee is
exactly what `NL_VarExp`'s own `hupd` step needs when it stores the just-computed `v` as a fresh cell's
content — using `free_vars_b` there instead would have needed an extra shape lemma for no benefit.

**Result**: `NEval_left_closed_preserved` is now fully `Qed`'d across all 11 constructors — `NL_Fun` needed
`FunBodyWellScoped` (the sole point a term is pulled in from *outside* `e`'s own structure); `NL_Let` needed
only `free_vars_b`'s own `remove`-based bound-set tracking, nothing external; `NL_Select`/`NL_Guess` needed
`free_vars_b_rename_subset` + `NEval_left_domain_mono` plus small connective lemmas
(`free_vars_b_bcase_branch`, `hd_error_in`, `zipsubst_in`/`zipsubst_notin`, and for `NL_Guess`'s extra
`hupd_list` layer, `hupd_list_map_self`/`hupd_list_notin`). Several small direction-of-equality slips along
the way (T20's "elem = query, not query = elem" pattern recurring twice more, an `in_or_app` nesting-order
mistake caught by the compiler rather than by hand), all fixed the same way as always: read the compiler's
own stated expected type, fix the one line.

**Status**: `theorem2` still has its one original admit, `curry_test_leftmost.v` still untouched.
`alpha_renaming_wip.v` (2482 lines) compiles clean end-to-end (`curry.v`, `curry_test_leftmost.v`,
`alpha_renaming_wip.v`, in that order) with exactly the 3 pre-existing admits, all in
`NEval_left_confluence`'s `NL_Fun`/`NL_Select`/`NL_Guess` cases — `NEval_left_closed_preserved` itself has
none. **Next step**: feed this back into `NL_Fun`'s own stalled fifth gap in `NEval_left_confluence` — the
`ClosedHeap G0` fact that gap needed is no longer something to merely assume, it's now provable by applying
`NEval_left_closed_preserved` along the *outer* derivation's own earlier steps.

---

## 30. Same session, continued: the fifth gap genuinely closed — and a sixth, more fundamental one found
immediately behind it

**The user said "let's continue"**, then "let's start on that" (the reorder), then "let's continue" again —
carrying straight through from §29's finish into feeding `NEval_left_closed_preserved` back into `NL_Fun`'s
own stalled fifth gap.

**Threading**: added `FunBodyWellScoped P`, `ClosedHeap Gam1`, and `(forall w, In w (free_vars_b e1) ->
Gam1 w <> None)` as three new hypotheses to `NEval_left_confluence` itself, right alongside `Hcontain0`/
`HFdom1`/`HFdom2`. Re-threading them through the 8 already-`Qed`'d cases turned out to be nearly free:
`VarCons`/`VarSelf`/`VarFree`/`ValFree`/`ValCon` are leaves (nothing to thread), and `VarExp`/`Or`/`Let`
each needed exactly the derivation `NEval_left_closed_preserved`'s *own* corresponding case had already
worked out — copy the technique, not re-derive it.

**The fifth gap, actually closed.** With `Hclosed1 : ClosedHeap G0` now directly available in `NL_Fun`'s own
case (it *is* the theorem's `Gam1`, unchanged, for that branch), building `NHeapAlpha sigma tau G0 Gam2`
needed one more piece beyond PIECE 5/6: for `z` a "pure sink" in `ps_pairs`'s range but not its domain (i.e.
`z = s2 y` for some `y`, where `s2 y` doesn't happen to equal any `s y'`), nothing in `batch_extend`'s
existing 3-conjunct interface pins down where `sigma` sends `z`. Traced by hand: `batch_extend`'s own
*construction* (cycle/component-based) always keeps `sigma` mapping the pairs-list's domain+range into
itself — true by construction, just not exposed. Added a 4th conjunct to `batch_extend`'s statement
(`sigma'` keeps `ps`'s domain+range closed under itself) and a new lemma `cyc_sigma_in` (`In w l -> In
(cyc_sigma l sigma w) l` — a rotation never leaves its own list, via `rotate1`'s permutation property) to
support it; re-proving `batch_extend`'s own induction to carry the new conjunct took two `change` fixes
(the by-now-familiar unreduced-`if`-under-a-closure trap, already documented at T-something) and one
`Permutation_in` argument-order fix (`x` is explicit and comes *before* the `Permutation` proof, not after).
With that in hand, `HNHAsigmatau` was built via the same "z-based" reformulation of `NHeapAlpha` planned
several sessions ago, and **it compiled clean on the first attempt** — real confirmation the diagnosis (G0's
own stored values never reference the fresh locations as *values*, because `ClosedHeap G0` plus both fresh
lists avoiding `G0`'s domain forces it) was exactly right.

**A sixth gap, found immediately behind the fifth.** Calling the outer `IH` on `Hrec` needs, among its
hypotheses, `Hcontain0` *for `sigma`* — `forall w, sigma w <> w -> G0 w <> None /\ Gam2 w <> None` — and
this is **false**, not merely unproven: `sigma` is *required* to move every `s(y)` to `s2(y)` (that's
`Hrealizes`/`Hnonparam`, load-bearing for `Hfinal` itself), yet `G0 (s y) = None` (`Hfresh`, directly) and
`Gam2 (s y) = None` (derivable the same way the fifth gap's own G0-side reasoning went). `sigma` is forced to
move *exactly* the locations both heaps leave undefined — the one thing `Hcontain0` (as phrased) forbids.
This is independent of everything about `ClosedHeap`/`free_vars_b` — it was always going to block `NL_Fun`'s
case, just hidden behind the fifth gap until now.

**Likely resolution** (not attempted): `Hcontain0`, added several sessions ago as "correction (c)", is
probably stronger than its actual job requires. Its only real purpose is to license `Hcontain_None_fixed` at
whichever *specific* fresh locations a deeper `NL_Fun`/`NL_Guess` call picks — not to hold unconditionally
for every `w`. Weakening it correctly — without re-breaking the 8 cases already threaded through the current
phrasing, a *fourth* re-verification pass — needs its own careful trace-first pass before touching any code.

**Status**: `alpha_renaming_wip.v` (2636 lines) compiles clean end-to-end. Still exactly 3 admits total, all
in `NEval_left_confluence` — `NL_Fun` now stops one genuine step later than before (at the sixth gap, not
the fifth), `NL_Select`/`NL_Guess` unchanged. `theorem2` still has its one original admit,
`curry_test_leftmost.v` still untouched.

---

## 31. Same session, continued: the sixth gap's natural fix works halfway, then exposes a deeper,
semantics-level question — a genuinely new kind of gap for this project

**The user said "let's trace the weakened form and see if it'll work"** — investigating §30's proposed fix
(weaken `Hcontain0` so it's satisfiable for `sigma`) by hand, before writing any code. No file edits this
entire session — purely investigative, and the investigation itself changed the plan twice.

**First finding: the naive weakening breaks what `Hcontain0` exists to support.** Changing its conclusion
from "both heaps defined" to "both heaps agree on definedness" (an IFF) makes it satisfiable for `sigma` at
`NL_Fun`'s own level, but it also makes "both undefined" *compatible* with `sigma0` moving `w` — which is
exactly what `Hcontain_None_fixed` needs to rule out to support `batch_extend`'s `Hfix` precondition at a
*deeper* level. The fix for the case we're stuck on breaks the case we already closed.

**Second finding: a structural fix — a growing "reserved region" `D`, threaded like the guard list `F1`/`F2`
already is — works for the straightforward part.** `Hcontain0` becomes `forall w, ~In w D -> sigma0 w<>w ->
...`; `D` grows by `ps_pairs`'s own domain+range exactly at `Fun`/`Guess` and is unchanged everywhere else;
the theorem's conclusion existentially produces its own `D' >= D` alongside `sigma`/`tau`. Traced by hand:
this correctly supports `Hfix` for a *deeper* level's own fresh pairs (they're outside `D` by heap
monotonicity + `Houtside`), and it elegantly resolves a *second*, previously-invisible issue found along the
way — a body-internal variable inside a case branch that's never actually taken during evaluation can have
its fresh location go permanently unbound, so the theorem's own "`sigma w<>w` implies both heaps defined"
output conjunct can't honestly promise anything about it. The existentially-chosen `D'` (⊇ `ps_pairs`) simply
exempts such locations — for free, as a side effect of the same mechanism.

**Third finding, the real blocker: establishing `Hfix` still needs "`s(y)` is outside `D`" as a starting
fact, and nothing gives it.** `s` comes from `NL_Fun`'s own rule in `curry_test_leftmost.v`, constrained only
by `injective s` and `Hfresh` (freshness relative to the *current* heap `G0`, checked independently at each
call). Nothing stops `s(y)` from numerically coinciding with an *ancestor* level's own fresh choice that also
never got bound — the identical dead-branch scenario, one nesting level up. **Checked, not guessed**:
`ProgWF` and `NoBareFreeOrChoiceProgWF` say nothing about variable-naming discipline; `var := nat` provides
an ordering, but `Hfresh` never uses it (no "beyond the max used so far" convention exists anywhere in this
codebase). The collision is concretely constructible: a case with an unreached branch containing a dead
let-bound variable, alongside a reached branch containing a nested `Fun` call — both levels' own `Hfresh`
premises check out completely independently, since `NEval_left` carries no cross-call memory of what's
already been chosen.

**The reassuring half**: this is very likely *not* a hole in the theorem itself. A dead branch never
contributes to the final evaluated value, so alpha-equivalence of the two derivations' results shouldn't
actually depend on how their respective throwaway fresh pairs get reconciled. What it breaks is *this proof
technique specifically*: `batch_extend`'s `Hfix` precondition demands `sigma0` already fix *every* one of
`vs`'s images unconditionally — dead ones included — and nothing forces that across nesting levels.

**Likely real fix, not attempted**: generalize `batch_extend` itself to *tolerate* a pre-existing `sigma0`
move landing inside `ps_pairs` — chaining through the existing move rather than requiring `Hfix` to hold
outright before starting. This is a genuine new combinatorial capability on top of PIECE 2 (component
decomposition, cycle extension), not a quick patch on top of the current interface, and materially bigger in
scope than the `D`-threading that motivated looking here.

**Why this is worth recording as its own category**: every prior "escalation" in this project (§20's third
escalation, the fourth/fifth/sixth gaps) was a gap *within the proof*, discoverable and fixable by adding
more structure to what's already being tracked. This one is different in kind — it's a question about
whether the underlying *semantics* (`NL_Fun`/`NL_Guess`'s freshness premises) provide enough global discipline
for a fully general confluence argument, surfaced only by pushing the proof far enough to need it. Worth
flagging explicitly for whoever picks this up next, rather than treating it as "just another gap to trace
through."

**Status unchanged**: no code edits this session (pure investigation, confirmed via the file's own
`coqc` compile before and after). `alpha_renaming_wip.v` still compiles clean with the same 3 admits;
`theorem2` still has its one original admit; `curry_test_leftmost.v` still untouched.

---

## 32. Same session, continued: the sixth gap's design fully worked out — nine new pieces, not yet built

**The user said "let's work on weakening the Hfix precondition and see if we can get that to work."** Three
things happened, each investigated by hand before any code: (1) confirmed generalizing `batch_extend`
directly is the wrong move; (2) designed and validated an alternative that avoids needing to; (3) found and
resolved one more dependency the alternative surfaced. No code changed anywhere in this arc — every
`coqc` check along the way showed the file exactly as `bef8254` left it.

**(1) `batch_extend` itself can't be casually weakened.** Read `cyc_extend`'s own proof directly:
the "`l` is currently fixed" precondition is used specifically to rule out something *outside* `l` mapping
*into* it (`cyc_tau_cyc_sigma`'s own case split on `sigma w ∈ l` for `w ∉ l`). Dropping it would mean
redoing `component`/`chase` over a *combined* graph (the new pairs plus wherever the incoming permutation
is already non-identity) — genuine new combinatorics, not a quick patch.

**(2) The alternative: never chain `batch_extend` outputs across levels.** Instead, thread four constants
fixed for the *entire* induction — `Gam1_TOP`, `Gam2_TOP`, `sigma0_TOP`, `tau0_TOP` — with monotonicity
hooks (`Gam1_TOP`'s domain ⊆ the current level's `Gam1`, via `NEval_left_domain_mono`) and a growing
`pa : list (var*var)` recording every `Fun`/`Guess` pair introduced anywhere so far. At every `Fun`/`Guess`
step, call `batch_extend` **fresh** — on `pa ++ this level's own new pairs`, starting from `sigma0_TOP`/
`tau0_TOP`, never from the incoming per-level `sigma0`. `Hfix` for the combined list then follows from the
*original*, never-re-examined `Hcontain0` plus monotonicity: anything fresh relative to a later heap is
provably fresh relative to `Gam1_TOP` too (the contrapositive of `NEval_left_domain_mono`, already built).
Verified this resolves the theorem's own "extends"/output-contain conjuncts too, by exempting them via
`~In w (map fst pa' ++ map snd pa')` where `pa'` is an existentially-produced superset of `pa` (needed
because a nested `Fun` two levels down can introduce further dead pairs a shallower exemption wouldn't
cover).

**(3) A new dependency surfaced, then resolved without needing a new semantic fact.** Applying this to
`NL_Fun`'s own `Hagree`/`Hfinal` (relating `s`/`s2` on parameter positions, via `Hparam`/`Hmatch`) needs
the *current* level's `sigma0` (used in `Hparam`) to agree with the *freshly recomputed* `sigma` at a
parameter that happens to be an ancestor's already-introduced pair — completely ordinary, e.g. a let-bound
local passed as an argument to a nested call, not a corner case. First worried this needed a genuinely new
fact — that a source variable's two independent renamed copies (D1's and D2's) must be live-or-dead in
lockstep — which would have been a different *kind* of gap (a question about the semantics, not the proof).
**It doesn't.** `batch_extend`'s `Hrealizes` conjunct is unconditional: `sigma'(a) = b` for *every* `(a,b)`
in its input list, regardless of what else that list contains or merges with. Maintaining
`Hrealize_accum : forall a b, In (a,b) pa -> sigma0 a = b` as an invariant (trivial at the top; free to
carry through every non-`Fun`/`Guess` case; free at `Fun`/`Guess` since `pa` is a subset of the fresh
call's own input list, so its own `Hrealizes` covers it) gives *exact* agreement on `pa`'s domain directly
— no liveness reasoning needed at all. Its mutual-inverse corollary gives the matching fact on the range
side via `tau` for free too.

**Net scope, not yet built**: roughly nine new pieces threaded through all 11 cases of
`NEval_left_confluence` — the four `_TOP` constants plus their own `mutual_inverse`/`Hcontain0`, two
monotonicity hooks, and `pa` with its own `NoDup`/`Hfix`/`Hrealize_accum` facts, mirrored by an
existential `pa'` in the conclusion. This sits on top of the four threading passes already done this
project (`Hcontain0`, `HFdom1`/`HFdom2`, `ClosedHeap`/`free_vars_b`/`FunBodyWellScoped`). **Deliberately
not attempted in this session** — a half-finished 11-case rewrite left mid-edit, if the remaining budget
ran out partway, would be strictly worse than a clean stop with a fully-validated design recorded. Full
design recorded in `alpha_renaming_wip.v`'s own header and `NL_Fun`'s in-proof comment.

**Status**: no code changes this session. `alpha_renaming_wip.v` compiles clean with the same 3 admits as
`bef8254`; `theorem2` still has its one original admit; `curry_test_leftmost.v` untouched. **Next step for
whoever picks this up**: implement the nine-piece design above — start with the statement, verify the 7
leaf/pass-through cases are near-trivial (as traced), then `NL_Fun`'s own case using `Hrealize_accum`
exactly as derived here.

---

## 33. Building the nine-piece design: 8 of 11 cases reproven, a seventh gap found in `NL_Fun`

**The user said "start the implementation."** Built it directly, checking `coqc` after each real chunk
(matching this project's own established discipline). Net result: real, verified progress, plus one new,
precisely-diagnosed obstruction — not a completed proof.

**What got built.** The theorem's `pa`-related facts (three named in Sec.32: NoDup on both projections,
`Hfix` relative to `sigma0_TOP`, `Hrealize_accum` relative to the *current* level's `sigma0`) turned out to
need a **fourth**, undocumented fact the moment `NL_Fun`'s own `Houtps` argument was actually redone:
`batch_extend`'s "outside" conjunct is now stated relative to `sigma0_TOP` (since the fresh call has to
start *from* `sigma0_TOP`, never the current `sigma0`) — so recovering "`sigma` agrees with the *current*
`sigma0`" for a parameter outside `pa`/`ps_pairs` needs a bridge fact, `Houtside_accum : forall w, ~In w
(fst pa) -> ~In w (snd pa) -> sigma0 w = sigma0_TOP w`, with nothing else to derive it from. Bundled all
four into one `Definition PaInv sigma0_TOP sigma0 pa` (plus a separate `PaSub pa pa'` for "pa' extends
pa") so every pass-through case could carry the invariant opaquely instead of re-destructuring four facts
at every call site — this collapsed what would have been a 12-conjunct existential back down to a
7-conjunct one, and made the mechanical threading through the 8 non-`Fun`/`Select`/`Guess` cases
(`VarCons`/`VarSelf`/`VarFree`/`ValFree`/`ValCon`/`VarExp`/`Let`/`Or`) genuinely mechanical, exactly as
Sec.32 predicted for the "leaf/pass-through" cases. All 8 are fully Qed'd, zero admits, confirmed via
`coqc`.

**`NL_Fun`: the first piece of the design confirmed correct, then a new wall.** `HfixBE_TOP` — establishing
that `sigma0_TOP` fixes this level's own `ps_pairs`, via `HGam1mono`/`HGam2mono`'s contrapositive (fresh
relative to the *current* heap implies fresh relative to `Gam1_TOP`/`Gam2_TOP`) plus the *original*,
never-re-examined `Hcontain0_TOP` — went through exactly as designed. The wall came right after, trying to
actually invoke `batch_extend` on the *combined* list `pa ++ ps_pairs` (required, since `Hfix` now only
holds relative to `sigma0_TOP`, and both `pa` and `ps_pairs` need to go in together for `Hrealize_accum`'s
own maintenance at the next level down): `batch_extend` needs `NoDup (map fst (pa++ps_pairs))`, which needs
`pa` and `ps_pairs` **disjoint**, not just individually `NoDup` — and this isn't provable from anything in
hand.

**The seventh gap.** `ps_pairs`'s elements are fresh relative to the *current* `G0`/`Gam2` (`Hfresh`/
`Hfresh2`). `pa`'s elements are only known *fixed by `sigma0_TOP`* (`HpaFix`) — nothing says they're in or
out of `G0`/`Gam2`'s domain. Concretely: if an ancestor level introduced a pair from its own body's **dead**
(never-taken) case branch — precisely gap 6's original scenario — that pair's locations stay outside every
heap's domain for the rest of the derivation, forever indistinguishable, from *this* level's `G0`, from an
ordinary never-yet-used fresh number. `NL_Fun`'s own rule constrains `s`/`s2` only by injectivity plus
freshness relative to the *current* heap — no cross-call memory rules out landing on that exact dead value.
Checked `FunBodyWellScoped` (confirms every element of `vs` is body-*internal*-bound, never a genuinely free
variable escaping outward) — this rules out the *ordinary* case (a let-bound variable later passed as an
argument to a nested call: that variable's fresh location gets bound in the heap the moment its own `Let`
is reached, so `Hfresh` at any later level directly excludes it) but does **not** rule out the dead-branch
case, where the location never gets bound at all. Re-checked `var := nat`'s own definition (no
reserved-region/monotone-counter convention `Hfresh` could lean on) — same conclusion as gap 6's own check.

**Why this is a genuinely different gap from #6, not the same one resurfacing.** Gap 6 blocked the
*output* "both heaps defined" conjunct — resolved by having `pa'`/`D'` exempt dead locations *after the
fact*. This one blocks `batch_extend`'s own *input* NoDup precondition, before `Hfinal` (the syntactic
renaming-agreement goal `Hrealize_accum` was built to reach) is even reachable — after-the-fact exemption
can't help a precondition the call itself needs to typecheck.

**Not yet resolved; two directions sketched, neither attempted.** (i) Restrict `pa` to *live* pairs only,
dropping a pair the instant its own branch is known not taken — but "not taken" is a fact about `Hrec`'s
own *dynamic* derivation, not something `vs`'s purely *structural* walk over `vars_of_b` can see before
`Hrec` is examined. (ii) Weaken `Hfinal` to not need to hold syntactically over `body`'s dead sub-terms at
all (relate `v1`/`v2` directly instead of the whole renamed `body`) — a bigger restructuring of the
theorem's own statement. Both are real design work, not attempted this session.

**Status**: `alpha_renaming_wip.v` compiles clean, still exactly 3 admits (`NL_Fun`'s new gap-7 stopping
point, `Select`, `Guess` — same count as `bef8254`, but the statement itself is substantially stronger and
8 of 11 cases are freshly reproven under it). `theorem2` still has its one original admit;
`curry_test_leftmost.v`/`curry.v` untouched. Full argument recorded in the file header and in `NL_Fun`'s
own in-proof comment (right where `HfixBE_TOP` ends and the new admit begins).

---

## 34. Choosing and building the gap-7 fix: `BlkAlpha`, a non-bijective correspondence relation

**The user asked which direction to pursue for gap 7, then said to start building it.** Three
candidates were on the table: (1) restrict `pa` to live pairs only, (2) weaken `Hfinal` so it doesn't
need to hold syntactically over dead sub-terms, (3) a Barendregt-style global freshness hypothesis.
The user picked (2). Traced it by hand before writing anything, per this project's own standing rule.

**Why the obvious cheap version of (2) fails.** The natural first idea: don't require the *whole*
term equation `e2 = rename_b sigma0 e1`, only require it to hold "on the live path." This doesn't
parse: `rename_b` is a plain structural substitution — it rewrites *every* variable occurrence,
dead branches included — so the equation is either exactly true at every syntactic position or
false. There is no partial-credit reading of a literal term equation. A second attempt — let the
hypothesis become "*some* witness renaming agreeing with `sigma0` on `e1`'s free variables, with
`e2 = rename_b sigma1 e1`" — also fails for a structural reason, not an incidental one: getting
`rename_b s2 body` out of `rename_b sigma1 (rename_b s body)` still forces `sigma1(s y) = s2(y)`
at *every* `y` in `body`, dead ones included, because that's what term equality at that position
means. Freedom to pick a fresh per-call witness doesn't remove the constraint; it only removes the
requirement that the witness be shared elsewhere — and the constraint itself is exactly gap 7's
own problem, relocated.

**The actual fix: don't require one global relation to explain e2's structure at all.** Built
`Expr0Alpha`/`BlkAlpha` (PIECE 7, `alpha_renaming_wip.v`, placed after `free_vars_b_bcase_branch`
since it needs it): an inductive correspondence relation, parameterized by an ambient `sigma`,
that only forces agreement with `sigma` at genuinely *live* positions (`Let`'s own RHS expression,
a `Case`'s own scrutinee) — anywhere a *binder* is crossed (`Let`'s bound name, a `Case` branch's
own pattern variables), the relation instead permits a **locally-overridden** correspondence
function, built via a plain function override (`ren_override2`: `fun w => if w = y1 then y2 else
sigma w`) rather than a bijection extension. This is the crux: a function override needs **no
NoDup/Hfix precondition at all** — overriding a function's value at a finite set of points can
never collide with anything, unlike extending a *bijection* (`batch_extend`'s whole reason for
being finicky). Two dead pairs from unrelated levels, under this relation, simply never have to
meet: each gets its own throwaway local override, never composed with anything else.

**The key lemma, `BlkAlpha_rename_scoped`** (this session's actual replacement for `Hfinal`):
given `injective s` and agreement between `sigma`/`s`/`s2` only on `body`'s own `free_vars_b`
(scope-aware — per `FunBodyWellScoped`, this is ⊆ `ps`, i.e. tiny), `BlkAlpha sigma (rename_b s
body) (rename_b s2 body)` holds. Proved by strong induction on `blk_size`, mirroring this file's
own established idiom (`well_founded_induction lt_wf`, same call convention as
`free_vars_b_subset_vars_of_b_bound`/`NEval_left_domain_mono`'s neighbors: `IHn (blk_size k + 1)
Hn k Hm ...`, not `IHn (blk_size k)` directly — got this wrong on the first pass and had to match
the existing pattern exactly). The `BLet` case needs no override at the head position at all when
the bound name coincides with something `H` already covers, but genuinely needs one
(`ren_override2`, pinning `s x ↦ s2 x` unconditionally) when it doesn't — that unconditional pin
is exactly what makes it always constructible, dead or live. The `BCase` case needed a genuinely
new pointwise lemma, `ren_override2_map_in` (injective `s` means `s w = s y` forces `w = y`, so
the override at `s w` always lands on the pair actually keyed by `w`, regardless of what else the
pattern-variable list contains — no `NoDup` needed, because `map s ys` and `map s2 ys` are always
images of the *same* source list `ys`, so a repeated name repeats consistently on both sides, never
conflicting).

**Debugging notes worth keeping** (real mistakes hit and fixed this session, not just the design):
constructor arguments for a *parameterized* `Inductive` (declared `Inductive X (sigma : ren) : ...`)
still take the parameter as an explicit leading argument at each constructor unless marked
implicit — `apply (BA_Let (s x) (s2 x) ...)` silently mis-slotted `s x` into `sigma`'s own position
and produced a confusing type-mismatch several arguments later, not an obvious arity error; fixed
by supplying `sigma` first. `List.In`'s `elem = query` unfold direction (T20) bit again in the
`BLet` case's own `in_in_remove` call. A `lia` failure reported as the unhelpful "Cannot find
witness" traced back to an over-eager `simpl in Hsize` that turned one instance of the *same*
opaque term (`blk_size (BCase x brs)`, appearing in both `Hsize` and a freshly-`assert`ed `Hlt`)
into two syntactically different ones — `lia` treats `blk_size (BCase x brs)` as an atom and can't
see through a `simpl` that only unfolded *one* of its two occurrences; removing the stray `simpl`
let the two inequalities compose by transitivity as intended.

**Status**: `Expr0Alpha`, `BlkAlpha`/`BrsAlpha`, `ren_override2` and its lemmas, and
`BlkAlpha_rename_scoped` are all fully Qed'd, zero admits — confirmed via a clean `coqc` (deleted
all `.vo`/`.glob` first). This is a **standalone foundation**, not yet wired into
`NEval_left_confluence` itself — the theorem still has its original 3 admits (`NL_Fun`'s gap-7 stop,
`Select`, `Guess`), unchanged by this session, since PIECE 7 doesn't touch the theorem yet. **Next
step**: restate `NEval_left_confluence` against `BlkAlpha sigma0 e1 e2` in place of the literal
`e2 = rename_b sigma0 e1` hypothesis, and redo all 11 cases against it — the 8 non-`Fun`/`Select`/
`Guess` cases should carry over close to mechanically (they only ever used the equation to invoke
shape-inversion at a *live* position, which `BlkAlpha`'s own leaf/`BA_Case`/`BA_Let`-live-part
cases still deliver directly); `NL_Fun`'s own case gets to use `BlkAlpha_rename_scoped` in place of
`Hfinal`, closing gap 7. `theorem2` still has its one original admit; `curry_test_leftmost.v`/
`curry.v` untouched.

## 35. A considered, deliberately-not-taken alternative to `BlkAlpha`: a genuine global-freshness
restriction on `NL_Fun`/`NL_Guess`, and why it was set aside in favor of finishing `BlkAlpha`'s wiring

**The user asked, before resuming `BlkAlpha`'s wiring: would requiring let-bound names to be
globally unique — decided at function-call entry, even for never-executed branches, the way an
old C compiler pre-allocates storage for every local regardless of which branch runs — fix gap
6/7 instead?**

**Half of this is already true of `NL_Fun` as written.** Its own rule (`curry_test_leftmost.v:61-
68`) already renames *every* non-parameter variable in the body via one injective `s`, chosen at
call entry, before any branch is known to be live — `rename_b s body` is a plain structural
substitution touching dead branches too. That much already matches the C-compiler analogy.

**What's actually missing is that the freshness check is heap-relative, not global.** `Hfresh :
forall y, ~ In y ps -> G (s y) = None` only rules out collision with what's *currently written* to
the heap. A dead branch's reserved name is never written (nothing ever `hupd`s it), so it's
invisible to every *other* call's own freshness check, forever — exactly gap 6/7's own mechanism.
Strengthening this to genuine cross-call uniqueness (a monotone, ever-growing reserved-name supply,
matching how real gensym-based implementations behave) would fix it, in principle — this is
candidate (3) from Sec.34 ("a Barendregt-style global freshness hypothesis"), which was on the
table there too.

**Why it wasn't taken.** Unlike the `Hcontain0`/`ClosedHeap`/`FunBodyWellScoped`-style hypotheses
threaded into `NEval_left_confluence` over the last dozen sessions — each naming something already
*true* of every `NEval_left` derivation, and thus addable as a plain extra hypothesis on the proof
— global freshness is **false** of `NEval_left` as currently defined; nothing in `NL_Fun`/`NL_Guess`
stops two unrelated firings from colliding. Making it true requires changing the *relation itself*:
threading a monotone reserved-set ghost parameter through all 11 constructors (not just the two that
introduce names, since it has to persist and grow through the others too), rechecking that
`theorem2`'s own first-conjunct existential witness construction still goes through under the
stronger premise, and auditing every existing `NL_Fun`/`NL_Guess` call site in the ~8666-line
`curry_test_leftmost.v` (several already `Qed`'d) against the new arity. That's a change with a
blast radius across the whole base semantics, not a self-contained lemma — a materially bigger and
riskier undertaking than finishing `BlkAlpha`'s wiring, whose foundation (`Expr0Alpha`/`BlkAlpha`/
`BlkAlpha_rename_scoped`) was already built and `Qed`'d as of `5eee8d0`.

**Decision: keep it as a recorded, validated fallback, not pursue it now.** If `BlkAlpha`'s wiring
into `NEval_left_confluence` hits a wall too, this is a real, understood second option, not
something to re-derive from scratch. Not attempted; no code changes from this discussion.

## 36. Wiring `BlkAlpha` into `NEval_left_confluence`: gap 7 genuinely closed, the whole nine-piece
`pa`/`PaInv`/`sigma0_TOP` apparatus dropped, three narrower admits remain

**The user said to proceed with `BlkAlpha`'s wiring.** Restated `NEval_left_confluence`'s
hypothesis from the literal `e2 = rename_b sigma0 e1` to `BlkAlpha sigma0 e1 e2`, and reproved the
11 cases against it. This is a **substantially bigger win than planned**: not only does `BlkAlpha`
fix the term-correspondence side of gap 7 (as designed), tracing it through concretely showed the
**heap-correspondence side doesn't need the nine-piece machinery either** — `pa`, `PaInv`, `PaSub`,
`sigma0_TOP`/`tau0_TOP`/`Gam1_TOP`/`Gam2_TOP` are all gone from the theorem's own signature now.

**Why the heap side turns out fine too, traced concretely before coding (per this project's own
standing discipline).** The nine-piece design existed because the *old*, literal-equality version
of `NL_Fun` needed one bijection to explain the *whole* renamed body, dead branches included,
forcing a monolithic construction that had to survive being merged across nesting levels (gap 7's
own NoDup-disjointness wall). Under `BlkAlpha`, `NL_Fun`'s own case needs **no sigma extension at
all**: `BlkAlpha_rename_scoped` only needs `sigma0` to agree with `s`/`s2` on `body`'s
`free_vars_b`, which `FunBodyWellScoped` already confines to `ps` — exactly `Hparam`'s own
conclusion (parameters always agree, no reconciliation needed), already available with zero new
work. Both heaps and the ambient `sigma0`/`tau0` pass into the recursive `IH` call completely
unchanged, since `NL_Fun` itself never touches the heap before recursing. Separately, the
*induction itself only ever visits live binders* — a dead case branch is never part of any
`NEval_left` derivation, so the induction can never reach one — meaning wherever a genuine renaming
extension *is* still needed (`NL_Let`'s one fresh pair, `NL_Guess`'s one fresh batch), it only ever
needs to be built **directly off the current `sigma0`/`tau0`**, one live pair/batch at a time, never
merged with anything an ancestor introduced. That removes gap 7's own disjointness question
entirely, not just for `NL_Fun`.

**Result:** `NL_Fun`'s own case is now fully `Qed`'d, zero admits, with no `batch_extend`/
`ps_pairs` at all — gap 7 is **closed**. 8 of 11 constructors are fully proven (`VarCons`,
`VarSelf`, `VarFree`, `VarExp`, `ValFree`, `ValCon`, `Fun`, `Or`); most of these needed only a
mechanical change (invert `BlkAlpha` to recover the same literal equation `subst e2` used to give,
via a new `BlkAlpha_bexpr_det` — provable because a bare `BExpr e` position is a leaf: none of
`Expr0Alpha`'s six constructors leave any freedom, so `BlkAlpha` and literal `rename_b` equality
coincide there). New foundational lemmas built along the way, all `Qed`'d: `Expr0Alpha_det`/
`Expr0Alpha_intro` (both directions of the leaf-determinism fact), `BlkAlpha_bexpr_det`,
`BlkAlpha_refl` (`BlkAlpha sigma b (rename_b sigma b)` for *any* `b`, a one-line corollary of
`BlkAlpha_rename_scoped` at `s := id` plus `rename_b_id` — needed at `NL_VarExp`, where the
recursive premise's own "found at `G x`" term isn't necessarily `BExpr`-shaped), and
`mutual_inverse_extend_gen` (generalizes `mutual_inverse_extend` to tolerate `a = b`, a genuine
no-op in that case — needed because `NL_Let`'s own two fresh picks aren't guaranteed distinct a
priori). Also built `NEval_left_blet_shape` (a `BLet` shape-inversion lemma mirroring
`NEval_left_evar_shape`/`_bcase_shape`, missing until now) and `BlkAlpha_change_sigma` (a
congruence lemma: a `BlkAlpha` derivation built under one ambient renaming transports to another
that merely *agrees on the term's own free variables* — needs no injectivity or `NoDup` anywhere,
unlike `rename_b_congr`, because `BlkAlpha`'s own binder-crossing machinery already tolerates a
local override at every binder).

**`NL_Let`: attempted, found a genuine new correction, left as a precisely-diagnosed admit rather
than force a fix.** Reconciling the two independently-fresh single locations `x`/`x2` via one
`mutual_inverse_extend`-style swap works for the *term* side (using `BlkAlpha_change_sigma` to
bridge the swap-based renaming against whatever local override `BlkAlpha`'s own inversion handed
back). But `Hcontain0`'s *output* conjunct — "wherever `sigma` moves something, both heaps have it
defined" — genuinely fails at exactly the two positions this step introduces: `Gam1' = hupd G0 x _`
defines `x` but not `x2`, and symmetrically `Gam2' = hupd Gam2 x2 _` defines `x2` but not `x`, so
neither position satisfies the *conjunction* (both heaps) the old-style claim demands. This is
**not** gap 6/7 resurfacing — no `batch_extend`, no cross-level merging, no disjointness question is
involved. It's a narrower, structural point: `Hcontain0` needs a *per-heap* exemption for the pair
each `Let`/`Guess` step introduces, threaded as a (much simpler than `pa`/`PaInv`) growing pair of
exemption lists, one per heap, each maintained as "always a subset of that heap's own domain" — true
by construction, since a position is only ever exempted the instant it's *written*, and heaps only
grow, so a later freshness check automatically avoids every earlier exemption. Concretely this needs
splitting `Hcontain0` into two per-heap facts rather than one conjoined one. Real, understood,
buildable — just not attempted this pass, so as not to risk leaving the (much higher-value) `NL_Fun`
case unverified partway through a bigger edit.

**`NL_Select`/`NL_Guess`: left admitted, matching the pre-existing diagnosis** (BCase's own shape
inversion is a two-way disjunction shared with `Guess`, needing `IH1` applied first to rule out D2
picking the other shape; `Guess` additionally needs a `batch_extend` call restricted to just `ws`
this level's own fresh batch, which the reasoning above suggests is safe under the new design but
wasn't attempted).

**Status:** `alpha_renaming_wip.v` compiles clean end to end (`coqc`), exactly 3 admits (`NL_Let`,
`NL_Select`, `NL_Guess`), zero elsewhere — confirmed by grepping the compiled file for `admit`/
`Admitted`. `curry_test_leftmost.v`/`curry.v` untouched. `theorem2` itself is unchanged (still its
one original admit) — the corollary `NEval_left_self_confluence` that admit needs requires
`NEval_left_confluence` fully `Qed`'d (not just `NL_Fun`'s own case), so PIECE 8's wiring into
`curry_test_leftmost.v` is still blocked on closing the remaining three. **Next step:** fix
`Hcontain0`'s per-heap-exemption gap at `NL_Let` (design above), then `NL_Guess` (same fix, plus a
`batch_extend` call on just its own `ws`), then `NL_Select` (the `IH1`-first argument), then wire
the finished theorem into `theorem2`'s own admit.

## 37. Correction to Sec.36's own conclusion: gap 7 is closed for `NL_Fun` specifically, not in
general — `NL_Let`'s per-heap exemption design has its own, deeper "gap 8," structurally the same
collision as gap 6/7 but for a *live* pair, not a dead one. Diagnosed by hand, not yet fixed.

**The user said to continue — picked up exactly where Sec.36 left off: build the per-heap-exemption
fix for `NL_Let`.** Traced it through by hand before coding (no `.v` edits this session). Found the
design *itself* has a hole, one level down from where it first looks fine.

**The naive design (Sec.36's own sketch): bundle "`D` ⊆ that heap's own domain" with the exemption,
per heap.** `HeapExempt sigma0 D Gam := (forall w, In w D -> Gam w <> None) /\ (forall w, sigma0 w
<> w -> ~In w D -> Gam w <> None)`, one instance for `Gam1`, one for `Gam2`. At `NL_Let`, exempt
`x2` from the `Gam1`-side instance (since `hupd G0 x _` never defines `x2`) and `x` from the
`Gam2`-side instance (since `hupd Gam2 x2 _` never defines `x`). **This breaks immediately, by
direct construction**: the very definition requires `In w D -> Gam w <> None` — but `x2` is being
added to the `Gam1`-side `D` *precisely because* `Gam1` does **not** define it. The "domain" half
and the "exemption" half of one bundled invariant are in direct tension the moment either heap's
own exemption list contains the *other* heap's own fresh pick.

**Splitting the two purposes apart doesn't dissolve the problem — it relocates it exactly where gap
7 already found it.** Drop the "`D` ⊆ domain" requirement from the exemption fact itself; keep it
only where it's actually used, to justify "fresh relative to a heap implies not in `D`" at the
*next* level down. Trace what a **deeper**, nested `NL_Let` (inside `k`, evaluated against
`Gam1' = hupd G0 x _` and its own descendants) needs: given its own fresh pick `x_deep` satisfies
`G_deep x_deep = None`, it needs `sigma_ancestor(x_deep) = x_deep` to run `mutual_inverse_extend` at
its own level. Via the (correctly) gated `Hcontain1`, this only follows if `x_deep` is *not* in the
inherited exemption list — and `x2` (this level's own exemption) *is* in that list. **Nothing rules
out `x_deep = x2`.** Concretely constructed, not just asserted: two derivations of
`BLet x1 EFree (BLet x2 EFree (BExpr (EVar x2)))` from the same (empty) heap — D1 picks `x1 := 100`
then, for its own *second* let, is free to pick `x2 := 101` (fresh only relative to
`hupd Gam 100 _`, which says nothing about 101); D2 independently picks `x1' := 101` for its own
*first* let (fresh relative to the same empty heap — 101 is available to it too, by sheer
coincidence of D2's own free choice). Reconciling D1's first `Let` against D2's forces the swap
`sigma_ancestor := ext_sigma id 100 101`, i.e. `sigma_ancestor(101) = 100`. D1's own *second* `Let`
(picking `x2 = 101`) now needs `sigma_ancestor(101) = 101` to swap it against whatever D2 does at
its own second position — but `sigma_ancestor(101) = 100`, not `101`. Both derivations are
completely ordinary, well-typed `NEval_left` proofs; nothing about either is contrived.

**Why none of the three already-built extension primitives absorb this.** `mutual_inverse_extend`,
`cyc_extend`, and `batch_extend` (Sec.20-22's own machinery) all share one precondition shape:
every point being incorporated must *already be a fixed point* of the ambient bijection. None of
the three has any notion of "redirect a point the bijection already moves elsewhere, chaining
through the existing target" — which is exactly what reconciling `x2` against D2's own second pick
would require here (`sigma`'s value at 101 needs to become D2's own second choice, while whatever
101 *used* to map to, `100`, needs to land somewhere sensible too — a genuine chain-extension, not a
fresh pair). This is a different combinatorial primitive from anything built so far, not a small
patch to an existing one.

**This is structurally the same phenomenon as gap 6/7 (an ancestor's "invisible-on-this-side"
position colliding with a descendant's own fresh pick), just for a different reason.** Gap 6/7's
dead-branch positions were invisible because they're never evaluated at all. `NL_Let`'s `x2` is
invisible to `G0`'s own lineage for a different reason — it's `x2` genuinely *is* live, but only on
`Gam2`'s side, and `NEval_left`'s own freshness premises never check anything about the *other*
derivation's heap. Both failure modes reduce to the same root cause identified back in Sec.31/§35's
own discussion: `var := nat` carries no global, cross-derivation uniqueness discipline, so nothing
stops two independently-fresh choices from numerically coinciding, whether across dead/live
branches of the *same* derivation or across the *two* derivations being reconciled.

**Correction to last session's own conclusion.** Sec.36 said "gap 7 is closed... no more
disjointness worries." That's accurate for `NL_Fun` specifically — `BlkAlpha_rename_scoped` never
needs a sigma extension there at all, so the whole question doesn't arise, and `NL_Fun`'s own case
is genuinely, unconditionally `Qed`'d, unaffected by this section. It does **not** generalize to
`NL_Let`/`NL_Guess`, both of which still need a genuine heap-level bijection extension (for
`NHeapAlpha`, not for the term relation — confirmed by tracing the `NL_Let` case concretely:
`NHeapAlpha` at `w := x2` genuinely requires `sigma(x) = x2`, it isn't an artifact of a clumsy
construction), and that extension is exactly where this new collision lives.

**Not attempted: the actual fix.** Likely needs a genuine "extend a bijection at a point it already
moves, by chaining" primitive — a real generalization of `cyc_extend` (which already knows how to
rotate an existing chain by one position; what's missing is *inserting a new link* into a chain
whose other end is already fixed elsewhere). This is real, scoped, buildable work, comparable in
size to Sec.21-22's own original development of `cyc_extend`/`batch_extend` — not attempted this
session so as not to leave a partial, unverified construction in place. No `.v` files changed this
session; `alpha_renaming_wip.v` is exactly as `HEAD` left it (`NL_Fun` `Qed`'d, `NL_Let`/`NL_Select`/
`NL_Guess` admitted), `theorem2` still has its one original admit.

## 38. Building the chain-redirect primitive: gap 8 itself genuinely closed, but wiring it into
`NL_Let` exposes a third, separate bookkeeping problem, not yet resolved — reverted rather than
leave a half-verified construction in place

**The user said to build the chain-redirect.** Worked out the construction on paper first (per the
project's own standing discipline), validated the combinatorial core in a scratch file before
touching the real proof, then integrated it.

**The primitive: `splice_sigma`/`splice_tau`.** Given `mutual_inverse sigma tau` and two points `a`,
`d` (neither required to be a fixed point), insert the edge `a -> d` by *reconnecting* whatever `a`
used to map to (`a' := sigma a`) with whatever used to map to `d` (`d' := tau d`): `d'` now maps to
`a'`, closing the gap the redirect leaves behind.

```coq
Definition splice_sigma (sigma tau : ren) (a d : var) : ren :=
  fun w => if Nat.eq_dec w a then d else if Nat.eq_dec w (tau d) then sigma a else sigma w.
Definition splice_tau (sigma tau : ren) (a d : var) : ren :=
  fun w => if Nat.eq_dec w d then a else if Nat.eq_dec w (sigma a) then tau d else tau w.
```

`splice_mutual_inverse : mutual_inverse sigma tau -> forall a d, mutual_inverse (splice_sigma sigma
tau a d) (splice_tau sigma tau a d)` needs **no precondition on `a`/`d` at all** — a strict
generalization of `ext_sigma`/`mutual_inverse_extend`'s own swap, which is exactly the special case
`a' = a`, `d' = d` (both already fixed). Verified directly (`splice_is_swap_when_fixed`) and against
the process notes' own gap-8 counterexample by hand-computation before being trusted. `NHeapAlpha_
splice` is the matching heap-level lemma: given `NHeapAlpha sigma tau Gam1 Gam2`, `ClosedHeap Gam1`,
and only the two *ordinary* freshness facts (`Gam1 x = None`, `Gam2 x2 = None` — no fixed-point
facts needed), `NHeapAlpha` survives extending by `splice_sigma`/`splice_tau x x2`. Both lemmas
compile clean, zero admits, fully standalone — genuine, reusable progress regardless of what
happened next.

**Wiring into `NL_Let`: gap 8 itself is resolved, but a third bookkeeping problem surfaces
immediately behind it.** With `splice_sigma` available, `NL_Let`'s own construction no longer needs
`Hxfixed`/`Hx2fixed` (fixed-point facts) at all — the swap goes through regardless of whether an
ancestor already moved `x`. But the theorem's own **"extends" conjunct** (`sigma` agrees with
`sigma0` wherever `sigma0` already moved something, or either heap already defines it) still needs
`Hcontain0` to be *re-derivable* at every level — and `Hcontain0`'s own AND-shaped output ("both
heaps defined wherever `sigma` moves something") genuinely fails at exactly the two positions
`NL_Let`'s own splice touches (`x` defined only on `Gam1`'s side, `x2` only on `Gam2`'s) — the same
shape of failure gap 6 first found, now for a *live* pair rather than a dead one. Unlike gap 8
itself, this doesn't block on a missing combinatorial primitive (splice handles the construction
fine either way) — it blocks on getting an **exemption-list design** right.

**Tried, live, and found genuinely unresolved — reverted rather than leave it half-verified.**
Attempted gating both `Hcontain0` and the "extends" conjunct by a single, growing, unstructured
exemption list `D` (threaded like gap 6's own `pa`, but as a plain list, needing no `NoDup`/merging
since `splice_sigma` never consumes `D` for its own construction). This runs into a genuine problem
at `NL_VarExp`'s own case: its "extends" step needs `sigma x = sigma0 x` for `x` a value already
*present* in `Gam1`'s domain (`Hgx0`) — which requires knowing `x` itself was never exempted, i.e.
`~In x D'`. Establishing that needs a *third* invariant beyond `D`'s own growth — "every element of
`D` is a position where *at least one* of the two input heaps was undefined at the moment it was
added" — which is true by construction at `NL_Let` but wasn't threaded, and a single OR-shaped
membership fact turned out to under-determine what's needed once `Hgx0` only rules out *one* of the
two heaps (`Gam1`), leaving `Gam2`'s own state at `x` genuinely unconstrained. Considered leaving
"extends" ungated (only gating `Hcontain0`'s own output) — traced through and found this breaks the
*next* level down instead, for the same underlying reason (a deeper level's own "extends" argument
needs exactly the fact the shallower level's gating was withholding). Each fix considered relocates
the problem rather than closing it; a working design most likely needs **two separate, per-heap**
exemption lists (`D1 ⊆` complement of `Gam1`'s domain, `D2 ⊆` complement of `Gam2`'s), not one
combined list — genuine further design work, not attempted.

**Decision: revert the theorem-level wiring, keep the validated primitive.** Restored
`NEval_left_confluence`'s signature, all 8 already-`Qed`'d cases, and the corollary to the clean,
compiling checkpoint from this session's earlier point (no `Hcontain0`/`D` threading at all — the 8
cases never needed it in the first place, since none of them ever actually changes `sigma`).
`splice_sigma`/`splice_tau`/`splice_mutual_inverse`/`NHeapAlpha_splice` stay in the file, `Qed`'d,
ready for whoever next attempts `NL_Let` with the two-list design sketched above already in hand.

**Status:** `alpha_renaming_wip.v` compiles clean end to end, exactly 3 admits (`NL_Let`, `NL_Select`,
`NL_Guess`), zero elsewhere. `NL_Fun`'s own closure (gap 7) is completely unaffected — it never needs
any sigma extension, so none of this arises there. `theorem2` unchanged, still its one original
admit. **Next step:** design the two-separate-exemption-list version of `Hcontain0`/"extends"
(`D1`/`D2`, each maintained as "subset of that heap's own domain's complement"), re-verify it doesn't
break `NL_VarExp`'s own use before touching `NL_Let` again, then finish `NL_Let` with `splice_sigma`
already in hand.

## 39. The two-list design, attempted — and a simpler fix found instead: `Hcontain0` was never
actually needed at all. `NL_Let` fully closed, zero admits

**The user said to try the two-list design.** Before writing Coq, re-derived what `D1`/`D2` would
each need to satisfy, tracking the *direction* of every use carefully (the exact discipline that was
missing last time) — and that tracing dissolved the problem rather than confirming the design.

**Re-deriving `Hcontain0`'s two roles separately.** Its *input* role (deriving `sigma0 w = w` from
`Gam1 w = None`, used once, at `NL_VarExp`'s own `sigma x = sigma0 x` step) turns out to need nothing
about `D` at all: `NL_VarExp`'s own `Gam1 x <> None` fact (`Hgx0`) is a *positive* fact, and a `D`
containing only positions where some heap is *undefined* can never contain `x` in the first place —
checked directly against a `D_ok : In w D -> Gam1 w = None \/ Gam2 w = None` invariant, `Gam1 x <>
None` alone doesn't rule out the *other* disjunct (`Gam2 w = None`), reproducing the exact
under-determination gap 8's own write-up already flagged. Splitting into `D1`/`D2` (one per heap) and
gating `Hcontain0` per-side looked promising — until re-deriving *why* `Hcontain0` was needed at all
found the actual answer: it was needed to prove `NL_Let`'s own `x`/`x2` are fixed points of `sigma0`,
*specifically* so `mutual_inverse_extend`'s swap could apply. **`splice_sigma` doesn't have that
precondition.** Once that's the only thing `Hcontain0` was for, and it's gone, `Hcontain0` itself has
no remaining job — confirmed by grep: across all 8 already-`Qed`'d cases, `Hcontain0` was never
*applied*, only threaded through untouched (since none of them ever change `sigma` at all).

**Simplifying "extends" the same way.** The "extends" conjunct's own three disjuncts
(`sigma0 w<>w`, `Gam1 w<>None`, `Gam2 w<>None`) were inherited from the pre-`BlkAlpha` design without
re-checking which are actually *exercised*. Grepping every real application again: only `NL_VarExp`'s
own `Gam1 w<>None` disjunct is ever used, anywhere. Dropped the statement to
`forall w, Gam1 w <> None -> sigma w = sigma0 w` — the single conjunct that's actually load-bearing.
Reverified this doesn't weaken anything needed downstream: since `Gam1` in the *conclusion* always
means the *input* heap to the current call (not the post-write output), `NL_Let`'s own two special
positions (`x`, and `tau0 x2` — the two positions `splice_sigma` touches) are *both* directly
`Gam1`-undefined (`Hxfresh` for `x`; derived from `Halpha0` + `Hx2fresh` for `tau0 x2`, exactly as
before) — meaning the simplified "extends" claim is **automatically vacuous at both**, with no
exemption tracking, no `D`, no gating of any kind needed.

**Result: `NL_Let` is fully `Qed`'d, zero admits.** The construction is now short and direct:
`splice_sigma`/`splice_tau x x2` build the extended bijection unconditionally; `NHeapAlpha_splice`
carries `NHeapAlpha` through it; `BlkAlpha_change_sigma` bridges the term relation using the same
"`x`/`tau0 x2` are `Gam1`-undefined, hence excluded from any position `e`/`k` can actually reference"
argument that closes `Herename`/`Hagreek`; the recursive `IH` call needs no new machinery beyond
what's already built. No case-split on whether `x = x2` is needed anywhere (`splice_mutual_inverse`
holds unconditionally, so the degenerate case that forced awkward branching in the old
`mutual_inverse_extend_gen`-based attempt simply never arises).

**Status:** `alpha_renaming_wip.v` compiles clean end to end, exactly **2 admits** (`NL_Select`,
`NL_Guess`), zero elsewhere — down from 3. 9 of 11 constructors are `Qed`'d: `VarCons`, `VarSelf`,
`VarFree`, `VarExp`, `ValFree`, `ValCon`, `Fun`, `Or`, and now `Let`. `theorem2` itself is unchanged
(still its one original admit) — the corollary it needs requires all 11 cases closed. **Next step:**
`NL_Select` (the `IH1`-first argument plus a `BrsAlpha`-lookup lemma, mechanism already understood,
not yet written) and `NL_Guess` (the same `BrsAlpha`-lookup, plus a *batch* version of `splice_sigma`
for its own `ws` list — plausibly straightforward now that a single splice needs no fixed-point
precondition, but not yet attempted).

---

## 40. Next session: built `BrsAlpha_lookup`, started `NL_Select`, found (and partly fixed) a genuinely
new required hypothesis — unique branch-constructor labels — then hit a second, deeper gap in `BlkAlpha`
itself

**Built `BrsAlpha_lookup`** (via a position-based `BrsAlpha_nth_error` helper, so it needs no assumption
about duplicate constructor labels — an `In`-based lookup would have been ambiguous exactly where the
next finding bites). Cost two misdiagnosed `injection`/`induction` errors before landing on the real
cause: `BrsAlpha` is declared via `with` alongside `BlkAlpha`, so plain `induction` does **not** treat its
own `sigma` parameter as uniform — it comes back as a 9th, per-case-varying leading binder, silently
shifting every subsequent name in an `as [...]` pattern by one versus what the surface `Inductive`
declaration's `forall` list suggests. Only found by `Show`ing the raw goal instead of re-guessing the
order a third time — worth remembering if this file's `induction`-on-`BrsAlpha` pattern ever needs
re-deriving (T15/T21 are the same *lesson*, one level up: here it's an inductive's own parameter turning
into a hidden index, not a constructor-argument-order mixup).

**Used it to start `NL_Select`, and found the real blocker was sharper than the placeholder comment
said.** `IH1` cleanly rules out the `NL_Guess` disjunct of `NEval_left_bcase_shape` (forcing `sigma0 x` in
`Gam2` must come back `ECon`-shaped, since `IH1` transports `Hrec1`'s `ECon` result forward, contradicting
`Guess`'s `EVar`-shaped result — closed by `discriminate`). For the surviving `Select` disjunct,
`NEval_left_bcase_shape` on `H2` hands back *some* branch `(c', ys', body')` in `brs2` matching the forced
constructor; separately, `BrsAlpha_lookup` hands back the branch that's *actually* the `BrsAlpha`-image of
D1's own chosen branch. **Nothing forced these to be the same entry** if `brs2` has two branches sharing a
constructor with different bodies — not a missing tactic, a missing hypothesis: the theorem (and the
underlying semantics generally) implicitly assumes case branches are well-formed, same as real
pattern-match compilation, but nothing said so anywhere in the Rocq encoding.

**Fixed it, mirroring how `FunBodyWellScoped`/`ClosedHeap` were added for the analogous NL_Fun-era gaps.**
Added `BrsUniqB` — a `NoBareChoiceB`-shaped recursive predicate over `Blk` requiring `NoDup` on each
`BCase`'s own constructor-label list, recursing through `BLet`'s continuation and every branch's own body
— plus `BrsUniqHeap` (heap-content analogue, mirroring `ClosedHeap`) and `ProgBrsUniqWF` (program-level
analogue, mirroring `FunBodyWellScoped`). Backed by a full `NEval_left_BrsUniqHeap_preserved` theorem,
mirroring `NEval_left_closed_preserved`'s own 11-case structure but substantially *simpler*: `BrsUniqB`
carries no per-variable payload at all (it's a bare structural fact about a `Blk`'s own shape), so none of
`ClosedHeap`'s free-var bookkeeping (`zipsubst_in`/`zipsubst_notin`/`NEval_left_domain_mono`) was needed —
only `ProgBrsUniqWF`, for `NL_Fun`'s own body-unfolding, plays the role `FunBodyWellScoped` played there.
Two more small lemmas close the actual ambiguity: `BrsAlpha_labels_eq` (`BrsAlpha` always keeps the *same*
constructor name at each position on both lists, since `BrsA_cons`'s own conclusion uses one `c` for both
sides — so a `NoDup` fact about `brs1`'s labels transfers to `brs2`'s `verbatim`, not just up to some
correspondence) and `brs_label_unique` (two same-label entries in a `NoDup`-labeled list are the same
entry). All three new hypotheses (`ProgBrsUniqWF P`, `BrsUniqHeap Gam1`, `BrsUniqB e1`) threaded through
the theorem's statement and all 9 already-`Qed`'d cases' own recursive `IH` calls (mechanical but
necessary — every case needed at least a pass-through, `Fun`/`Let`/`VarExp` needed a real derivation), plus
the `NEval_left_self_confluence` corollary. File re-verified compiling clean throughout with zero
unplanned admits after every edit.

**Then `NL_Select` reached a second, deeper gap this session did *not* fix.** With the branch identified
as the *literal same entry*, closing the case needs a `BlkAlpha` relating `rename_b (zipsubst ys zs) body`
(D1's substituted branch) to `rename_b (zipsubst ys2 zs') body2` (D2's) — composing the branch's own
`BlkAlpha sigma' body body2` (from `BrsAlpha_lookup`) with the two *separate* `zipsubst` renamings layered
on top. Tracing what this composition actually needs: for `w` free in `body` outside `ys`, `sigma0 w`
(via the theorem's own "extends" fact) must **not** collide with `ys2` — otherwise `zipsubst ys2 zs'`
would wrongly intercept a genuinely-outer reference on D2's side. Nothing currently guarantees that.
This is *not* the same shape as gap 8's fix (`NL_Let`'s own `x2`): `x2`'s freshness came for free from
D2's own **operational** premise (`NL_Let` itself requires `G x = None`), but `ys`/`ys2` never touch a
heap at all — `zipsubst` is a plain pre-evaluation substitution, so there is no operational freshness fact
to reach for here. This looks like a genuine gap in `BlkAlpha`'s own definition: `BA_Case`/`BrsA_cons`
currently let `ys2` be *any* names at all, with zero disjointness from anything — not something a smarter
tactic at the `NL_Select` call site can patch around, since it's a fact about the *given*, already-fixed
`e2`/`brs2`, not something the proof constructs. Deliberately **not fixed yet**: touching `BlkAlpha`'s own
definition risks needing to redo pieces of all 9 already-`Qed`'d cases, which build on its current
(unconstrained) shape — flagged for discussion rather than decided unilaterally.

**Status:** `alpha_renaming_wip.v` compiles clean end to end, still exactly **2 admits** (`NL_Select`,
`NL_Guess`) — but `NL_Select`'s own admit is now genuinely closer, with the branch-uniqueness gap fully
resolved and the remaining blocker sharpened to one precise, well-understood question about `BlkAlpha`'s
own definition. **Next step:** decide how to add a freshness/disjointness guarantee for a `BCase`
branch's own bound pattern names (most likely: strengthen `BA_Case`/`BrsA_cons` itself, or add a
program-wide "bound names are drawn from a globally-fresh pool" invariant analogous to `FunBodyWellScoped`)
before finishing `NL_Select`; `NL_Guess` needs the identical fix plus its own already-scoped batch-splice
work on top.

## 41. Same session, continued: the user asked for a counterexample before committing to changing
`BlkAlpha` — built one, and it's real

**The question.** Before agreeing to touch `BlkAlpha` (load-bearing for all 9 already-`Qed`'d cases), the
user asked the right question: is §40's capture gap an actual inconsistency of `NEval_left_confluence`'s
*statement*, or just a proof-technique shortfall that a cleverer tactic might route around? The honest
answer requires a concrete counterexample, not more paper reasoning — this file has already been burned
before by "obviously right" hand-arguments that didn't survive contact with `Show` (§40 itself, T15/T19-T21
throughout the glossary).

**Built one, fully machine-checked.** `NEval_left_confluence_stmt_is_false` (end of `alpha_renaming_wip.v`)
takes the theorem's own statement as a hypothesis and derives `False` from it, using a fully concrete
instance — `sigma0 := tau0 := id`; `e1 := BCase 0 [(0, [2], BExpr (EVar 1))]`, forcing `x=0` (stored as
`Con 0 [3]`) to select the branch, substituting its pattern var `2` (unused in the body) for `3`, then
forcing the body's own free var `1` (stored as nullary `Con 100`) — giving `v1 = Con 100 []`. `e2 := BCase
0 [(0, [1], BExpr (EVar 1))]` is a **perfectly valid `BlkAlpha` id-witness** for `e1` under the current,
unconstrained `BA_Case`/`BrsA_cons` (only the pattern-var renaming `2↦1` and off-`ys` agreement are
required, both satisfied), but branch2's own pattern var (`1`) happens to equal exactly the free variable
its body alpha-corresponds to. Running `e2` on the *same* heap: forcing `x=0` selects the branch again,
but now substituting *its* pattern var `1` for `3` captures the body's own `EVar 1` — rewriting it to `EVar
3` before evaluation, so D2 forces position `3` (stored as nullary `Con 200`) instead of position `1`.
`v2 = Con 200 []`, which cannot equal `rename_b sigma v1` (`= Con 100 []` for every `sigma`, since `v1` has
no free variables) for *any* `sigma` — the conclusion is unsatisfiable even though every hypothesis
(`mutual_inverse`, `NHeapAlpha`, `ClosedHeap`, `BrsUniqHeap`, `BrsUniqB e1`, `ProgBrsUniqWF`,
`FunBodyWellScoped`, `e1`'s own free-var closedness) holds outright for this instance.

**`Print Assumptions NEval_left_confluence_stmt_is_false.` reports "Closed under the global context"** —
zero axioms, nothing `Admitted` anywhere in its dependency chain. This is as rigorous as it gets: the
theorem's statement, exactly as currently written, can **never** be proven, independent of proof technique.
§40's diagnosis was correct, and `BlkAlpha`'s own definition (or the theorem's hypothesis list) genuinely
needs to change before `NL_Select`/`NL_Guess` can close.

**Process note, since this cost several failed `coqc` attempts before `Qed`:** building a *disproof* this
way (assume the target theorem's statement, derive `False` from a concrete instance) hits the same
tactic-precision issues as any other proof in this file — got tripped up by an un-beta-reduced local
`sigma'` closure blocking `destruct (Nat.eqb w 2) eqn:E` from finding its target (fixed with a `simpl`
first, same lesson as T5/T19), a `rewrite`-based `Expr0Alpha_intro` application fighting itself when the
`replace` target used the wrong (identity, not the local override) function, `reflexivity` misused on a
`<>` goal instead of `discriminate`, `in_app_or`/`in_remove` reached for out of habit when `free_vars_b`'s
own `BCase` case (`x :: fold_right ...`, no top-level `++`) didn't have that shape at all, and `(fun w H =>
H)` for two now-vacuous `In w nil -> ...` premises needing `False_rect _ H` instead (since `In w nil`
reduces to `False`, not to the goal type itself). None of these were conceptual — each was caught
immediately by the next `coqc` error and fixed in one step once actually looked at.

**Status:** `alpha_renaming_wip.v` still compiles clean, still exactly 2 admits (`NL_Select`, `NL_Guess`),
plus one new, fully-`Qed`'d, zero-axiom disproof documenting exactly why they can't close under the
current `BlkAlpha`. **Next step:** design the `BlkAlpha` fix (most likely a freshness/disjointness side
condition on `BA_Case`/`BrsA_cons`'s own `ys2`, or an equivalent program-wide fresh-bound-names invariant)
and re-verify it doesn't disturb any of the 9 already-`Qed`'d cases before resuming `NL_Select`.

## 42. Same session, continued: designed and built the `BlkAlpha` fix, re-verified all 9 cases, found it
closes TWO bugs at once, then hit a third, different (not a `BlkAlpha` defect) subtlety finishing `NL_Select`

**The fix.** `BrsA_cons` gained one new premise: `sigma'` must be injective on `ys1 ++ free_vars_b b1`
(everything this branch actually names — its own pattern vars, plus `b1`'s own free vars). Tracing through
exactly what breaks without it found this single condition closes not one but **two** distinct soundness
bugs:
1. **Capture** (§41's counterexample): `w` free in `b1` outside `ys1`, with `sigma w` landing in `ys2` —
   follows directly from the new premise + `Forall2`: if `sigma w` were `ys2`'s `i`-th entry, then
   `sigma w = sigma' w = sigma' ys1[i]`, forcing `w = ys1[i]` by injectivity — contradicting `w` outside
   `ys1`.
2. **Conflation**, found only while finishing `NL_Select` with the narrower, capture-only premise this
   session started with: two *distinct* pattern names `y ≠ y'` in `ys1` mapping to the *same* `sigma' y =
   sigma' y'`. Nothing in the capture-only premise ruled this out, and it breaks `zipsubst` directly — if
   `ys2` has this identification too (forced by `Forall2`), `zipsubst ys2 zs2` can only ever resolve to
   *one* of the two intended target positions, silently losing the other. Caught by actually trying to
   prove the `zipsubst`-commutation fact `NL_Select` needs (see below) and hitting an unprovable step, not
   by more paper reasoning — confirms verifying against the actual downstream use, not just the
   counterexample that motivated the first cut, is what surfaced the second bug.

**Blast radius: exactly two construction sites**, found by grepping for `BrsA_cons`/`BA_Case` applications
rather than assuming every `BlkAlpha`-touching lemma needed rework: `BlkAlpha_rename_scoped` (needed a new
`injective s2` hypothesis — available at both real call sites, `BlkAlpha_refl` with `s2 := sigma0` via
`mutual_inverse_injective_l`, and `NL_Fun` with `s2` via `Hinj2`, already extracted from
`NEval_left_fun_shape` but previously unused) and `BlkAlpha_change_sigma_bound` (needed no new hypothesis
at all — the old witness's own local-injectivity fact transports unchanged across an ambient-`sigma`
swap, since the swap only touches positions the local override already shields). Everything else (`BlkAlpha
_refl`'s callers, all 9 already-`Qed`'d `NL_*` cases) just needed the *new argument* threaded through, not
new reasoning — `BlkAlpha_refl` picked up its own `injective sigma` hypothesis as a consequence.

**Verifying the fix actually works, not just compiles.** Re-attempting `NEval_left_confluence_stmt_is_false`
(§41's disproof) under the live, fixed `BlkAlpha` fails exactly where it should — the `HBA` construction's
own `apply (BrsA_cons ...)` now demands the new injectivity obligation, which is genuinely false for that
instance (`sigma(1)=1 ∈ ys2=[1]`), so the bad witness is no longer constructible. Relocated the disproof to
`failed_attempts.v` (Sec.6) with a frozen, locally-renamed copy of the *old* `BlkAlpha`/`BrsAlpha`
(`BlkAlphaOld`/`BrsAlphaOld`) so it keeps compiling independently of the live (now-fixed) definitions —
`Print Assumptions` on it there still reports "Closed under the global context," confirming the relocation
didn't change what it proves.

**Built the per-position fact `NL_Select` actually needs.** `zipsubst_compose_in`/`zipsubst_compose_out`
(near `zipsubst_in`, both fully `Qed`'d) give `sigma (zipsubst ys zs w) = zipsubst ys2 zs2 (sigma' w)` for
`w` in `ys` (via the new local-injectivity premise, restricted to `ys`) and for `w` free in the branch body
outside `ys` (via the capture half plus a new small generic helper, `Forall2_in_r`: `In` on a `Forall2`'s
second list traces back to a related first-list element — standard, wasn't in this codebase under this
name yet).

**Then a THIRD subtlety, this time genuinely not a `BlkAlpha` defect.** Lifting the per-position fact
above into a full `BlkAlpha` relating the two *substituted* branch bodies (`rename_b (zipsubst ys zs)
body` vs `rename_b (zipsubst ys2 zs2) body2`) needs a new composition lemma mirroring
`BlkAlpha_rename_scoped`'s own well-founded recursion into `body`'s structure — and at a NESTED binder
inside `body` (say a `BLet z e k` buried inside the matched branch), the same "does the renaming conflate
two distinct names" question resurfaces, this time asking: can `zipsubst ys zs` (a value-substitution, not
a bijection — `zs` are literal stored heap values with no injectivity guarantee, unlike `NL_Fun`'s own `s`,
which the semantics itself requires injective) send some field value `z ∈ zs` to the *same* name as some
other bound variable already inside `body`? Nothing in the semantics rules this out — `ECon`'s own
argument list carries no such guarantee, and `NL_Select` doesn't add one. This is a genuinely different
kind of question from Sec.42's fix (a scoping/freshness question about substituted-in *values*, in the same
family as `NL_Fun`'s own `Hfresh` or `NL_Guess`'s own `HND`/freshness premises, not a repeat of the
capture/conflation bug in `BlkAlpha`'s own definition) — flagged in `NL_Select`'s own comment, deliberately
not resolved this session.

**Status:** `alpha_renaming_wip.v` compiles clean end to end, still exactly **2 admits** (`NL_Select`,
`NL_Guess`) — but the `BlkAlpha` question the user asked about is now closed: confirmed genuine via a
machine-checked disproof, fixed with a single premise that resolves two distinct bugs, and the fix is
re-verified against all 9 previously-`Qed`'d cases plus the self-confluence corollary. **Next step:** decide
how to state/discharge the new "substituted heap values don't collide with body-internal bound names"
scoping fact (likely a fresh hypothesis in the `Hfresh`/`ClosedHeap` family), then build
`BlkAlpha_compose_rename` to finish `NL_Select`; `NL_Guess` needs the identical piece plus its own
already-scoped batch-splice work.

---

## 43. Next session: `BlkAlpha_compose_rename` built and Qed'd (zero admits, zero axioms) — the
mechanical half of the gap is closed; the freshness question is isolated but still open

**The lemma.** Generalizes two existing well-founded-recursion lemmas at once: `BlkAlpha_rename_scoped`
(pushes two renamings `s`/`s2` through the *same* body) and `BlkAlpha_change_sigma_bound` (walks an
*existing* `BlkAlpha` witness without touching its structure). Given `BlkAlpha rho body body2` (exactly
`BrsAlpha_lookup`'s own output — `body`/`body2` possibly different terms, related via `rho`) plus two
*further* renamings `theta1`/`theta2` (`zipsubst ys zs` / `zipsubst ys2 zs2` at the real call site), it
concludes `BlkAlpha sigma (rename_b theta1 body) (rename_b theta2 body2)`.

**The key design choice: local, not global, injectivity.** `BlkAlpha_rename_scoped`'s `Hinj`/`Hinj2` were
*global* (`injective s`, unrestricted domain) — fine there, since `s`/`s2` were genuine bijection-shaped
renamings. `zipsubst ys zs` manifestly is **not** globally injective (it's the identity off `ys`), so
`BlkAlpha_compose_rename` instead requires `theta1` injective only on `vars_of_b body` (everywhere
`rename_b` actually touches — bound names too, not just `free_vars_b`, unlike `BlkAlpha_rename_scoped`,
since nested binders here don't get a free per-level choice of `theta1`/`theta2` the way they get a free
per-level choice of the *ambient sigma*), and `theta2` injective on a deliberately widened domain:
`vars_of_b body2 \/ map rho (vars_of_b body)`. The first disjunct covers positions arising from `body2`'s
own structure (a nested branch's `ys2`); the second covers positions reached via the ambient `rho`'s
offset behavior (any name off the local `ys`, at any depth). Working through the proof (particularly the
`BCase` case's own recursive step and its `BrsA_cons` local-injectivity obligation) showed this exact
two-part domain is *sufficient* to close every sub-goal using only facts already in hand at each level
(`HF2`, `Hoff2`, `HinHead`/`HinHead2`, `Forall2_eq_map`) — with **no separate "`BlkAlpha` preserves
free-variable-ness" transport lemma needed**. That's a real relief: such a lemma would likely be *false*
for an arbitrary `BlkAlpha` witness satisfying only the bare inductive definition (nothing in `BA_Let`
forces its own local override injective), so avoiding the need for it sidesteps a dead end rather than
papering over one.

**New standalone helpers built alongside it** (all fully `Qed`'d, none specific to this file's own
relations): `vars_of_e0_rename` (computational: `vars_of_e0 (rename_e0 rho e) = map rho (vars_of_e0 e)`),
`Expr0Alpha_compose_rename` (the `Expr0`-level analogue, composing an existing `Expr0Alpha rho e e2`
with two further renamings), `vars_of_b_bcase_branch` (the `vars_of_b` analogue of the already-existing
`free_vars_b_bcase_branch`, needed because injectivity here is stated over *all* of `vars_of_b`, not just
`free_vars_b`), `ren_override2_map_in_local` (a local-injectivity version of the existing
`ren_override2_map_in`, needing `s` injective only on `ys`, not globally — exactly what a zipsubst-shaped
`theta` can actually offer), and three small generic `Forall2` facts stdlib's own `Forall2_impl` doesn't
quite give (`Forall2_impl_in_l`, with an `In`-refinement on the premise; `Forall2_eq_map`; `Forall2_map_both`).

**Verification.** `coqc alpha_renaming_wip.v` compiles with zero errors; `Print Assumptions
BlkAlpha_compose_rename` reports "Closed under the global context" (checked directly, then the check line
removed again — not left in the file). `alpha_renaming_wip.v` still has exactly its same **2 admits**
(`NL_Select`, `NL_Guess`) — this session added a fully-`Qed`'d building block, not yet wired into either.

**What's still open, precisely.** `BlkAlpha_compose_rename` is a general lemma with `Hinj1`/`Hinj2` as
*explicit hypotheses* — building it did not require (and does not resolve) the question of how to
*discharge* those hypotheses at `NL_Select`'s own call site. That reduces, as §42 already anticipated, to
exactly: "no `zs`/`zs2` value collides with any *other* name (bound or free, at any depth) inside the
matched branch body" — a genuine freshness fact about the *dynamic* heap values `zs`, in the same family
as `Hfresh`/`HND` elsewhere in this file, not a repeat of §42's `BlkAlpha` bug (already fixed, and
confirmed by this session's proof to not be what's blocking things now). **Next step:** decide how to
state and obtain that freshness fact — most likely a new hypothesis on `NEval_left_confluence` itself
(mirroring `FunBodyWellScoped`/`ClosedHeap`/`BrsUniqHeap`'s own precedent), then actually wire
`BrsAlpha_lookup` + `zipsubst_compose_in`/`zipsubst_compose_out` + `BlkAlpha_compose_rename` together into
`NL_Select`'s tactic script (currently still a bare `admit`); `NL_Guess` needs the identical piece plus its
own already-scoped batch-splice work for `ws`.

---

## 44. Same session, continued: dug into the freshness fact and found §43's `Hinj1`/`Hinj2` are actually
too strong — chasing the fix hits a genuine, unresolved recursive-injectivity gap, not just more casework

**The starting question.** §43 left "no `zs` value collides with any other name inside `body`" as the
freshness fact to discharge `BlkAlpha_compose_rename`'s `Hinj1`/`Hinj2`. This session traced through
exactly *why* each is needed, one invocation at a time, rather than assuming the blanket statement was
right.

**Finding 1: full injectivity is unsound, not just strong — it rejects legitimate sharing.** `theta1 =
zipsubst ys zs` conflating two *distinct* elements of `ys` (`ys[i] ≠ ys[j]` with `zs[i] = zs[j]`) is
**not** a bug to exclude — it's ordinary graph-semantics aliasing (`f x = C x x` is a normal program,
matching a runtime value with two fields sharing one heap cell; nothing anywhere in this codebase's
`ClosedHeap`/`BrsUniqHeap`/`GEval`'s own `ECon` rule requires argument lists to be duplicate-free, and
requiring it would be wrong). Worse: with full injectivity, `Hinj2` becomes **unsatisfiable** whenever
sharing is present (`zs2 = map sigma zs` inherits the same duplicate, so `theta2` necessarily conflates
the two corresponding — genuinely distinct — names in `ys2` too) — meaning `BlkAlpha_compose_rename`, as
built in §43, could never actually be invoked for a branch matching an aliased constructor at all.

**Finding 2: the correct weakening needs a "consistency" fact, not just an exemption.** Tracing every
`Hinj1`/`Hinj2` invocation in the §43 proof found the sharing case bites in exactly **one** spot: the
`BrsA_cons` local-injectivity obligation in the `BCase` recursion, comparing two positions that both trace
back to the branch's own pattern list `ys`, through the nested local override `rho'''`. Everywhere else,
at least one compared position is *provably* not a pattern-list element (a `Let`'s own fresh bound name, a
different nested branch's own pattern list — disjoint from `ys` under the standard no-shadowing
convention), so injectivity genuinely holds there and only needs the freshness fact (`zs`/`zs2` vs. every
*other* name in `body`/`body2`) to be provable, exactly as §43 anticipated. The one hard spot needs: (a) a
biconditional `Hcons` — "`theta1` conflates two `ys` elements iff `theta2` conflates the two corresponding
`ys2` elements" (genuinely true given `zs2 = map sigma zs` plus injective `sigma`, no new hypothesis
needed for *this* half) — and (b) recovering "these two positions came from `ys`" from "their images landed
in `theta2`'s exempted set", which needs **`rho` injective on `ys ∪ free_vars_b body`** (call it
`Hrhoinj`) — exactly `BrsAlpha_lookup`'s own `Hcap1`, already available for free at the outermost call.

**Finding 3 (the actual wall): `Hrhoinj` doesn't survive being threaded through the recursion.**
`Hrhoinj` is a hypothesis of the *general* lemma, so it must be re-proved fresh at *every* recursive call,
not just the outermost one. At `BLet`'s own recursive step (proving it for the nested local override
`rho''`, restricted to the continuation `k`), the second-side binder `x2` is an *arbitrary* witness pulled
from whatever built the incoming `BlkAlpha` derivation — with **no established relationship to `rho`'s
image** over anything. Nothing in scope lets you rule out `x2` coinciding with `rho`'s image of some free
name in `k`. This is not "more of the same casework" — it's a missing piece of infrastructure (freshness
of every constructed local-override witness relative to the ambient `rho`'s image) that doesn't currently
exist anywhere in this file and would need its own design work, most likely tied to how `x2`-style fresh
choices get constructed at real call sites (`splice_sigma` and friends), not something derivable from
`BlkAlpha`'s bare inductive definition.

**Decision (with the user): stop and record, rather than push through or narrow the approach yet.**
`BlkAlpha_compose_rename` is left exactly as §43 built it (full injectivity, still `Qed`'d, zero admits,
zero axioms) — not risking an in-progress rewrite. One small, standalone, harmless addition survives from
this session's exploration: `bound_vars_b` (a new fixpoint, the dual of `free_vars_b` — the set of names
introduced as a *binder* anywhere in a `Blk`, deliberately **not** the same as `vars_of_b` minus
`free_vars_b`, since a name bound by a `Let` that's *also* free in that same `Let`'s own right-hand side —
e.g. `let x = x + 1 in ...` — must still count as bound there) plus `bound_vars_b_bcase_branch` (the
`bound_vars_b` analogue of `vars_of_b_bcase_branch`/`free_vars_b_bcase_branch`). Both fully `Qed`'d,
unused so far, but likely-needed groundwork: a genuine "no shadowing of the branch's own pattern names by
a nested binder" hypothesis (needed regardless of how the `Hrhoinj` gap gets resolved) is naturally stated
against `bound_vars_b`, not `vars_of_b`/`free_vars_b` (working this out mid-session is what surfaced the
distinction from `vars_of_b \ free_vars_b` in the first place).

**Status:** `alpha_renaming_wip.v` compiles clean, unchanged admit count (2: `NL_Select`, `NL_Guess`).
**Next step, next session:** resolve the `Hrhoinj` recursive-injectivity gap. Two candidate directions,
neither attempted yet: (a) stop trying to state `BlkAlpha_compose_rename` for fully arbitrary
`theta1`/`theta2`/`rho`, and instead build a narrower version specialized to the real
`zipsubst`/`mutual_inverse`-shaped instantiation directly, where the needed facts about fresh witnesses may
already be derivable from `splice_sigma`'s own construction; or (b) design and thread through the missing
"freshly-constructed local-override witnesses never collide with the ambient renaming's image" fact as its
own explicit hypothesis, mirroring how `Hfresh` plays this role for `NL_Fun`.

## 45. Next session: built and `Qed`'d a hygiene invariant (`NoShadowB`) as directed by the user; designing
its use inside `BlkAlpha_compose_rename` found it resolves §44's aliasing gap cleanly but exposed a second,
entangled freshness question underneath it

**The direction, chosen with the user.** Presented with §44's three candidate directions, the user picked
option (a)-adjacent: build the Barendregt no-shadowing invariant and see how far it goes, rather than
specialize `BlkAlpha_compose_rename` to the concrete call site or touch `BlkAlpha`'s definition a third
time.

**Built and `Qed`'d, zero admits.** `NoShadowB b := NoDup (bound_vars_b b)` (using §44's own, previously
unused `bound_vars_b`), plus: `NoDup_app_disjoint` (a small standalone list fact `NoDup (l1++l2) -> In a l1
-> ~In a l2`, not previously in this file under any name); `NoShadowB_let_k`/`NoShadowB_bcase_branch`
(pulling a branch's own `NoDup ys`, its body's own `NoShadowB`, and — the fact this was built for — `ys`
disjoint from anything the body binds at ANY depth, out of the parent's single `NoShadowB` fact, via
`NoDup_app_remove_l`/`_r` on `bound_vars_b`'s own concatenation structure); `bound_vars_b_rename` (the
`bound_vars_b` analogue of §43's `vars_of_e0_rename`, same well-founded-on-`blk_size` shape as
`BrsUniqB_rename_bound` since `Blk`'s auto-generated induction principle has no usable IH for branch
bodies); `NoShadowB_rename` (preserved under an injective renaming, composing the above with the
already-existing `NoDup_map_inj`); `ProgNoShadowWF` (program-level lift, mirroring
`FunBodyWellScoped`/`ProgBrsUniqWF`'s own precedent: `NoDup (ps ++ bound_vars_b body)` packages both
"parameters duplicate-free" and "parameters disjoint from the body's own binders" in one condition, the
same style `BrsA_cons`'s own local-injectivity premise already uses). `coqc` confirms zero errors after
this addition, independent of everything below.

**Working out `NoShadowB`'s actual USE inside `BlkAlpha_compose_rename` (not yet applied to the file — this
was design/validation work, done by hand-tracing the proof obligations, not yet committed as an edit).**
The plan: add an explicit `ys0` parameter (the outer branch's own, FIXED pattern list — fixed because
`theta1`/`theta2`/`sigma` themselves never change across the lemma's own recursive `IHn` calls, confirmed by
rereading Sec.43's proof: only `rho`/`sigma`'s *local overrides* change per level, never `theta1`/`theta2`),
weaken `Hinj1`/`Hinj2`'s conclusions from `w1 = w2` to `w1 = w2 \/ (In w1 ys0 /\ In w2 ys0)`, and add two
hygiene hypotheses (`Hhyg1 : forall y, In y ys0 -> ~ In y (bound_vars_b body)`, and its D2-side mirror
`Hhyg2` using `map rho ys0`/`bound_vars_b body2`).

**Where this lands cleanly.** Tracing every existing `Hinj1`/`Hinj2` call site in Sec.43's proof found each
one splits into: (a) *domain-restriction* uses (threading the hypothesis down to a recursive `IHn` call) —
these need **no change at all**, since the weakened conclusion has the exact same shape the recursive
call's own hypothesis expects, so `apply Hinj1`/`apply Hinj2` unify straight through; or (b)
*equality-deriving* uses (actually decomposing an application to get `w1 = w2`) — every one of these
already has **at least one side that is a bound name at the relevant level** (`BLet`'s own `x` vs. an
arbitrary free `w`; `BrsA_cons`'s own local-injectivity obligation comparing two positions both traceable
into `ys`/`ys'` at *some* nesting level) — and for those, the exemption disjunct is directly refutable:
whichever side is bound is, by `NoShadowB_bcase_branch`/`NoShadowB_let_k`, provably **not** in `ys0` (D1
side) or `map rho ys0` (D2 side, since that side's bound name sits in `bound_vars_b body2`, and `Hhyg2` says
`map rho ys0` avoids exactly that) — so the exemption branch contradicts itself immediately, leaving the
original, unconditional `w1 = w2` argument completely intact underneath. This is exactly why the fix
targets a **fixed, top-level** `ys0` rather than re-deriving "`rho` injective on `ys`" recursively (§44's
own wall): the exemption's *impossibility* proof only ever needs a static fact about `bound_vars_b`, never
a fact about what `rho`/its local overrides happen to do.

**Where it does NOT yet land cleanly — a second, previously-unnoticed gap.** The one case that resists this
treatment is `BrsA_cons`'s own local-injectivity obligation when **both** compared positions are genuinely
free (in `free_vars_b bd`, in neither branch's own pattern list) — nothing there is bound, so the
hygiene-based impossibility argument has no foothold, and this sub-case needs an entirely different route:
composing the branch's own `Hagree`-style fact at both positions and cancelling gives an equation of the
shape `sigma (theta1 y1) = sigma (theta1 y2)`, needing **`sigma` injective on that pair** to finish. Tracing
whether *that* threads through the recursion hits a **direct re-run of §44's own wall, one level down**: at
`BLet`'s own step, deciding whether a free-at-this-level position might actually be the *enclosing* binder's
own name (referenced again deeper in) requires knowing the constructed second-side witness (`x2`) doesn't
collide with the ambient renaming's image elsewhere — the exact "freshness of constructed local-override
witnesses" gap §44 already named and left unresolved, just now cornered into a narrower spot (only the
genuinely-free/genuinely-free pairing, not the `ys`-vs-`ys` aliasing case, which the hygiene fix *does*
fully resolve). Tried and confirmed NOT to route around this: (a) widening `Hagree`'s own domain from
`free_vars_b body` to `vars_of_b body` looked promising at first (bound-name instances of this fact DO come
for free from `BA_Let`/`BrsA_cons`'s own definitional binder-pairing, e.g. `Hxeq`, no injectivity needed)
but the free-free case still bottoms out needing `sigma`-injectivity on a domain that itself must survive
`BLet`'s own local override, i.e. the same wall; (b) reformulating the needed fact as "`rho` injective on
`ys0 ∪ free_vars_b body`, relative to a FIXED top-level `rho`" (mirroring how `ys0` itself is held fixed)
looked like a closer analogue of `BrsAlpha_lookup`'s own `Hcap1`, and unlike `Hagree` it does NOT need
special handling for bound names (a bound name is never in `free_vars_b body`, by definition, so this
fact's domain skips them entirely) — but re-deriving it at `BLet`'s own step for a newly-free `x` (a name
free at the child level precisely because it references the just-introduced, arbitrary `x2`) hits the
identical wall from the opposite direction: nothing rules out `x2` coinciding with the fixed-top `rho`'s
image of some unrelated name.

**Status:** `alpha_renaming_wip.v` compiles clean, still exactly 2 admits (`NL_Select`, `NL_Guess`) —
`BlkAlpha_compose_rename` itself was deliberately left as §43 built it (full injectivity, still `Qed`'d),
not risking an in-progress rewrite of a lemma nothing else in the file yet calls. This session's concrete,
committed addition is the `NoShadowB` infrastructure above (real, `Qed`'d, and confirmed to fully resolve
the `ys`-vs-`ys` aliasing half of §44's problem) plus a validated (by hand, not yet Rocq-checked as an
edit) design showing exactly where a second, harder question sits underneath: the "freshness of
constructed local-override witnesses relative to the ambient renaming's image" gap §44 first named is now
confirmed to be the genuine remaining blocker, narrowed to exactly the free-free sub-case, and demonstrably
NOT dissolved by the hygiene invariant alone — it needs its own, separate resolution (§44's option (b)) no
matter which domain the surrounding argument is phrased over. **Next step, flagged for discussion rather
than decided unilaterally:** design that missing freshness fact directly (most likely tied to how `x2`/`ys2`
-style fresh witnesses actually get constructed at real call sites — `splice_sigma`, `BlkAlpha_refl`,
`NL_Fun`'s own `Hfresh` — rather than something derivable from `BlkAlpha`'s bare inductive definition), since
that now looks like the one piece both `BlkAlpha_compose_rename`'s general form and any narrower,
call-site-specific version would equally need.

## 46. Same session, continued: the user's own correction to a §45 counterexample redirects the whole
approach — the "freshness" gap dissolves operationally, not via any `BlkAlpha` change, and two new lemmas
close it

**The correction.** §45 ended by proposing to strengthen `BA_Let`/`BrsA_cons` so a constructed local-override
witness (`x2`) can't collide with the ambient renaming's image — and, to justify it, offered a standalone
`BlkAlpha` witness relating `let 1 = Con0 in EVar 2` to `let 2 = Con0 in EVar 2`. The user caught the actual
problem immediately: those two terms aren't alpha-equivalent at all — `EVar 2` is a free reference in the
first and refers to the let's own bound variable in the second — so the "counterexample" was really just
exposing that `BA_Let`'s definition is too permissive in the abstract, not evidence that anything about the
*confluence theorem* needs fixing.

**Chasing why this matters reframed the whole approach.** `BLet` only ever evaluates via `NL_Let`, whose own
`Hxfresh` premise (`G x = None`) has to hold before the rule can fire *at all*. In the counterexample, `Gam2`
already had something stored at position `2` — so `NL_Let` simply can't apply to `e2` under that heap; there
is no `D2` derivation to hand the confluence theorem, and the "bad" instance is vacuous. That matches
exactly what `NL_Let`'s own (already-`Qed`'d) case already relies on ("x2's freshness came for free from
D2's own operational premise" — recorded back in the notes covering that case). The real lesson: a purely
syntactic, pre-evaluation `BlkAlpha` fact can never see this kind of protection; only interleaving with the
actual operational derivation can.

**Tried twice to build a machine-checked disproof of a sharper variant — both attempts failed instructively.**
Rather than trust that reframing on its own (this file has been burned by hand-arguments before), built two
successive attempts at a Sec.41-style disproof, aiming at the specific scenario `BlkAlpha_compose_rename`'s
own "both genuinely free" sub-case was stuck on: a nested `BLet`'s freshly-chosen bound name made to collide
with a *substituted* scrutinee value, not a heap-occupied one.
- **Attempt 1** (colliding value drawn from a *pre-existing* heap position): failed to even get off the
  ground. Making the two scrutinee arguments "line up" under `sigma0` forces `sigma0` to relate the
  colliding positions directly, and `NHeapAlpha`'s own global correspondence then forces the *other* side's
  heap to already have something at exactly the position the nested `Let` needs empty — so `Hxfresh` can
  never hold there in the first place.
- **Attempt 2** (colliding value drawn from a position created *mid-evaluation*, inside the scrutinee's own
  forcing, so it isn't in the original heap `sigma0`'s "extends" clause pins down): also failed, for a
  deeper reason — `IH1`'s own conclusion (applied to the scrutinee-forcing sub-derivation) gives
  `NHeapAlpha sigma1 tau1 G1 Gam2'` *unconditionally*, for the whole *updated* heap, not just an "extends"
  restriction to positions already present at the start. So even a position born partway through forcing
  the scrutinee has its image forced to be heap-defined on the other side too.

**The general fact underneath both failures, proved directly.** Combining `ClosedHeap` (whatever ends up in
a forced constructor's own argument list must already be heap-defined — nothing referenced by a stored value
can be dangling), `NHeapAlpha`'s full correspondence (not just its "extends" half), and
`NEval_left_domain_mono` (already in this file — the heap only ever grows, never loses entries) gives: once
a position lands in the scrutinee's forced arguments, its image on the *other* side stays heap-defined
through *everything* evaluated afterward, at any depth. Since `NL_Let`'s own freshness check needs its bound
name *undefined* at the moment it fires, this makes it impossible — not by convention, not by a new
invariant, but as a direct consequence of machinery already `Qed`'d in this file.

**Built and `Qed`'d, zero admits, zero axioms (`Print Assumptions` checked and removed again).**
`NEval_left_forced_args_defined` — a three-line corollary of `NEval_left_closed_preserved`'s own second
conjunct (specialized to `e := BExpr (EVar z)`, `v := BExpr (ECon c zs)`, so `free_vars_b e = [z]` and
`vars_of_b v = zs` exactly) — gives the scrutinee's own forced arguments are heap-defined the instant forcing
finishes. `NEval_left_forced_args_stay_defined` composes that with `nheap_rename_at` (crossing to the other
side via `NHeapAlpha`) and `NEval_left_domain_mono` (propagating forward through *any* later evaluation `e2`
on that side) to give the actual payoff: for every `w` in the scrutinee's forced `zs`, `sigma`'s image of `w`
stays heap-defined through whatever the other side evaluates afterward — exactly the fact needed to
discharge, at `NL_Select`'s real call site, the "no zs/zs2 value collides with any other name inside the
matched branch body" obligation Sec.43's own comment on `BlkAlpha_compose_rename` flagged as separate and
unresolved. Both lemmas placed directly after `NEval_left_closed_preserved` in `alpha_renaming_wip.v`.

**Status:** `alpha_renaming_wip.v` compiles clean, still exactly 2 admits (`NL_Select`, `NL_Guess`) — this
session's committed addition is the two lemmas above (real, `Qed`'d, verified zero-axiom), closing the
*freshness* half of what `BlkAlpha_compose_rename` needed, operationally rather than via any `BlkAlpha`
change (so the "third touch to `BlkAlpha`'s definition" §45 was steering toward is no longer needed at all).
The *aliasing* half (§45's `NoShadowB`-based weakening of `Hinj1`/`Hinj2`) is still designed but not yet
applied to the live `BlkAlpha_compose_rename`. **Next step:** decide whether to (a) finish wiring the §45
hygiene design plus these two new freshness lemmas into an actual rebuild of `BlkAlpha_compose_rename`, or
(b) skip the standalone lemma entirely and structure `NL_Select`'s own case to call `IH2` directly against
the branch body's evaluation the way `NL_Fun`/`NL_Let` already do, letting each nested level's own freshness
come from these two lemmas as it's reached rather than proving one large fact up front — §46's own findings
(that a syntax-only, pre-evaluation composition lemma structurally can't see the protection that's actually
doing the work) lean toward (b), but this hasn't been tried yet.

## 47. Same session, continued: went with option (a) after all — re-derived the "both free" sub-case by
hand, found the real wall was narrower than §44 thought, and fully rebuilt `BlkAlpha_compose_rename`
(zero admits, zero axioms)

**Re-deriving the "both free" gap.** Picking back up on §45's stuck point (the `BrsA_cons` local-injectivity
obligation when neither compared position is a pattern name, at any level), traced it through by hand one
more time rather than assuming §44's diagnosis of the wall was the final word. Two things §44 hadn't
separated: (1) `rho`'s own nested overrides (`rho''`/`rho'''`) DO stay consistent with a fixed top-level
`rho0` for a position that's free at the current level, via straightforward `Hoff`/`Hoff2` chaining — no
constructed witness's arbitrariness ever enters that chain, since a genuinely free position is by
definition never one of the witnesses. (2) The place a constructed witness's arbitrariness *does* bite
(`Hagree`'s own bundled fact, or `Hrhoinj0`'s domain) is exactly bounded by whether the position is bound
*anywhere* in the whole term, not just at the current level — and *that* question doesn't need chasing an
arbitrary witness's relationship to anything: a constructed binder (`x2` from `BA_Let`, or an element of
`ys2` from `BrsA_cons`) is by construction always a member of `bound_vars_b` of whatever body contains it,
transitively, regardless of what value it happens to be. So a FIXED, monotonically-threaded superset of
`bound_vars_b body`/`body2` (call them `bv1`/`bv2`, distinct from `ysX`'s own hygiene check) lets "at least
one compared position is bound somewhere" be decided uniformly at any depth, closing that half without ever
touching a witness's own arbitrariness — and the remaining half (both positions genuinely free, potentially
aliased through the top branch's own pattern list) is exactly where the `rho0`/`Hrhoinj0`/`Hconsistent`
chain from §45's design applies cleanly, since genuinely-free positions never touch a constructed witness at
all.

**The full final design, all fixed/threaded relative to the top invocation, none needing recursive
re-derivation against an arbitrary witness:**
- `ysX` (renamed from §45's `ys0` to avoid a real shadowing collision with an existing local binder of that
  name elsewhere in the proof) — the exemption set, and `Hinj1`/`Hinj2` weakened exactly as §45 designed.
- `bv1`/`bv2` — fixed supersets of `body`/`body2`'s own `bound_vars_b`, threaded via plain monotonicity
  (`bound_vars_b k ⊆ bound_vars_b (BLet x e k) ⊆ bv1`, and symmetrically for a `BCase` branch's own body).
  `Hhyg1`/`Hhyg2` restated against these (not the per-level `bound_vars_b`, which would miss an ancestor's
  own binder once recursion has moved past it — the bug an earlier draft of this design hit and had to
  correct before it worked).
- `rho0`/`fv1`/`Hrhoinj0` — the fixed top-level `rho` and its own injectivity on `ysX ∪ fv1` (exactly
  `BrsAlpha_lookup`'s own `Hcap1`), used only for genuinely-free positions.
- `Hconsistent` — `theta2` conflates two `rho0`-images of `ysX` elements iff `theta1` conflates the
  elements themselves; §44's own Finding 2a, free at the real call site.
- `Hagree`, widened to a bundle: the usual `sigma (theta1 w) = theta2 (rho w)` unconditionally, plus (only
  when `w` isn't bound anywhere) `In w fv1 /\ rho w = rho0 w` — threaded the same way the original `Hagree`
  already was, with the new half simply vacuous whenever `w` happens to be an ancestor's own bound name
  referenced freely at a deeper level (its premise `~ In w bv1` is false there, so nothing needs proving).

**Built and verified in a scratch file first** (`BlkAlpha_compose_rename2`, mirroring this file's own
practice of validating a hard case in isolation before committing it live), debugged against `coqc` through
a sequence of concrete, small mismatches (a `free_vars_b_bcase_branch` premise that's actually
`remove_all ys (free_vars_b bd)`, not `free_vars_b bd`, missed twice; `Hbt`'s own domain accidentally stated
over `vars_of_b` instead of `free_vars_b`; two omitted `Hhyg1'`/`Hhyg2'` obligations in a recursive `IHn`
call; one argument-order swap) — none of them conceptual, each caught immediately by the next `coqc` error,
consistent with this file's whole history of tactic-precision issues being distinct from genuine gaps.
`Print Assumptions` confirmed "Closed under the global context" before transplanting into the live file
under the original name (`BlkAlpha_compose_rename`), replacing the Sec.43 full-injectivity version — nothing
else in the file called it yet, so the replacement needed no other call-site updates.

**Status:** `alpha_renaming_wip.v` compiles clean, still exactly 2 admits (`NL_Select`, `NL_Guess`) —
`BlkAlpha_compose_rename` itself is now **fully closed**: zero admits, zero axioms, handling the aliasing
case (§45), the freshness case (§46, not directly used inside this lemma but validating why the design is
sound), and this session's own "both free" case, all as one coherent lemma. **Next step:** actually wire this
finished lemma into `NL_Select`'s own proof (still a bare `admit`) — via `BrsAlpha_lookup` for `rho`/`ysX`
(`Hcap1` gives `Hrhoinj0` directly), `zipsubst_compose_in`/`zipsubst_compose_out` for the top-level `Hagree`
fact, `NEval_left_forced_args_stay_defined` (§46) for whatever freshness `Hhyg2`/`Hconsistent` still need at
the real call site, and `NoShadowB`/`ProgNoShadowWF` (§45) threaded onto the confluence theorem itself to
supply `bv1`/`bv2`/`Hhyg1`/`Hhyg2` — then the identical piece for `NL_Guess`, which needs nothing new beyond
its own already-scoped batch-splice work for `ws`.

## 48. Same session, continued: `Hbt` turned out to need a genuinely new hygiene fact — found by trying to
prove a first attempt at it and discovering it was actually FALSE, then landing on a much simpler fix than
the false attempt's own recursive shape suggested

**The false start.** Tried to discharge `BlkAlpha_compose_rename`'s own `Hbt` hypothesis (needed at
`NL_Select`'s real call site) via a general, standalone, recursively-proved lemma: "any name bound
somewhere in a term has its `rho`-image bound somewhere in the alpha-related term too." Attempting to prove
it surfaced a genuine counterexample to the STATEMENT itself, not a proof-technique gap: `let x = x + 1 in
...`. `BA_Let`'s own definition uses the *ambient* `sigma` (not a local override) for the RHS's own
`Expr0Alpha` — so the `x` referenced there is, by the formalization's own semantics, a different, *outer*
`x`, distinct from this same `let`'s own binder, even though they're numerically identical. That position is
simultaneously "bound" (trivially, it's this `let`'s own head) and "free" (via the RHS reference) — and
nothing forces the *outer* `x`'s own image to be bound anywhere at all. `NoShadowB` (bound-vs-bound
distinctness) doesn't touch this; it's a bound-vs-free question.

**The fix, once framed correctly, turned out to be much simpler than the false start's own recursive shape
suggested.** The key realization: `Hbt`, as `BlkAlpha_compose_rename`'s own already-`Qed`'d proof actually
*uses* it, is only ever supplied ONCE, at the very top invocation — every deeper level's own version is
already *derived*, inside that already-finished proof, via `Hoff`/`Hoff2`-chaining from that single
top-level fact. So the standalone lemma needed at the real call site never has to be recursive or general
at all: it only has to hold for `body` (D1's own selected branch) directly, using `body`'s own,
directly-computed `bound_vars_b`/`free_vars_b` — not some inductively-threaded version.

That single-level fact — call it `NoCaptureB b := forall y, In y (bound_vars_b b) -> ~ In y (free_vars_b
b)` — is a NEW, standalone hygiene invariant, distinct from `NoShadowB`, and deliberately does NOT exclude
a branch legitimately referencing an outer pattern var: that reference is *properly bound* (not free) once
`free_vars_b` is computed over the WHOLE enclosing term (`e1`), and only reads as free when the branch's own
body is examined in isolation — exactly the distinction that makes `Hbt`'s exemption set (`ysX`, handled
separately via `Hrhoinj0`) safe while the `let x = x + 1` pattern isn't. Built two small transport lemmas
(`NoCaptureB_let_k`, `NoCaptureB_bcase_branch`, mirroring `NoShadowB_bcase_branch`'s own shape closely,
using it directly for one of the two sub-cases each needs) giving `NoCaptureB` of a `BLet`'s continuation or
a `BCase` branch's own body from `NoCaptureB` + `NoShadowB` of the *containing* term — meaning `NoCaptureB
body` (exactly what `Hbt` needs at the real call site) follows in one step from `NoCaptureB e1` +
`NoShadowB e1`, both `Qed`'d, zero admits. With `NoCaptureB body` in hand, `Hbt`'s own two premises (`In y
bv1`, `In y (free_vars_b body)`, with `bv1 := bound_vars_b body` at the top) are directly contradictory, so
`Hbt` discharges by `exfalso` alone — no recursion, no rho reasoning, nothing about `body2` needed at all.

**Status:** `alpha_renaming_wip.v` compiles clean, still exactly 2 admits (`NL_Select`, `NL_Guess`). Added
`NoCaptureB` alongside `NoShadowB`/`ProgNoShadowWF`, both new lemmas `Qed`'d zero-admit. **Next step:**
`NL_Select` itself still needs `NoShadowB e1`, `NoShadowB e2`, and `NoCaptureB e1` threaded onto
`NEval_left_confluence` as new hypotheses (mechanical pass-through for the 9 already-`Qed`'d cases, real
derivation for `NL_Fun`'s body-unfolding via program-level `ProgNoShadowWF`/an analogous `ProgNoCaptureWF`,
and `NL_Let`'s own recursion) before the lemma built across §43-§48 can actually be invoked.

## 49. Same session, continued: threaded all seven new hygiene hypotheses through `NEval_left_confluence`'s
full 11-case induction — mechanical, but real, work touching every already-`Qed`'d case, done in one pass

**The threading.** Added `ProgNoShadowWF P`, `ProgNoCaptureWF P`, `NoShadowHeap Gam1`, `NoCaptureHeap Gam1`,
`NoShadowB e1`, `NoShadowB e2`, `NoCaptureB e1` to `NEval_left_confluence`'s own statement (mirroring exactly
how `FunBodyWellScoped`/`ProgBrsUniqWF`/`ClosedHeap`/`BrsUniqHeap`/`BrsUniqB e1` were added in earlier
sessions — same style, same precedent), then went through all 11 cases. Built two small heap-level
invariants first (`NoShadowHeap`/`NoCaptureHeap`, mirroring `BrsUniqHeap`, giving every heap-stored value its
own `NoShadowB`/`NoCaptureB`) plus `NoCaptureB_rename` (mirroring `NoShadowB_rename`, composing the already-
existing `bound_vars_b_rename` equality with `free_vars_b_rename_subset`'s subset direction — sufficient
since injectivity is what turns a subset argument into the needed contradiction) — both `Qed`'d, zero
axioms, before touching the theorem's own cases.

**Where real (not just mechanical) derivation was needed, matching exactly where `BrsUniqB`/`ClosedHeap`
needed it before:**
- `NL_VarExp` (unfolds `G0 x`'s own stored expression `e`): `NoShadowB e`/`NoCaptureB e` come from the new
  `NoShadowHeap`/`NoCaptureHeap Gam1` hypotheses directly (mirroring how `He0BrsUniq` already came from
  `HBrsUniqHeap1`); the D2-side fact (`NoShadowB (rename_b sigma0 e)`) comes from `NoShadowB_rename`.
- `NL_Fun` (unfolds the called function's own body): both sides' facts come from `NoShadowB_rename`/
  `NoCaptureB_rename` applied to `ProgNoShadowWF`/`ProgNoCaptureWF`'s own output for that function, using
  `Hinj`/`Hinj2` (the two sides' own argument-matching injectivity, already extracted, already used by
  `BrsUniqB_rename` right beside it) — `ProgNoShadowWF` hands back `NoDup (ps ++ bound_vars_b body)`, one
  `NoDup_app_remove_l` away from the `NoShadowB body` actually needed.
- `NL_Let` (recurses into the continuation `k`, and updates the heap via `hupd`): `NoShadowB k`/`NoCaptureB
  k` come from `NoShadowB_let_k`/`NoCaptureB_let_k` applied to `e1`'s own (already-`Qed`'d, §48) hygiene
  facts, mirroring exactly how `HkBrsUniq` already reduces to `He1BrsUniq` for free; the D2-side fact needed
  the same extraction applied to `e2` (after `destruct He2`'s own unification retargets `He2NoShadow` onto
  the destructured `BLet x2n e2n k2n` shape automatically, the same way `body2` got unified for free inside
  `BlkAlpha_compose_rename` itself). The updated heap's own `NoShadowHeap`/`NoCaptureHeap` facts are
  immediate — every value `NL_Let`/`NL_VarFree` ever write is `let_content`-shaped, hence `BExpr`-shaped,
  hence trivially satisfies both (`bound_vars_b (BExpr _) = nil` makes `NoShadowB` a bare `NoDup nil` and
  `NoCaptureB` vacuous) — no analogue of `let_content_BrsUniq` needed at all.
- `NL_Or` (the `EChoice` case): both new `BExpr`-shaped facts are the same `NoShadowB_bexpr`/`NoCaptureB_
  bexpr` triviality already used for `He1BrsUniq` there (passed as bare `I`).
- The other 7 cases (`VarCons`/`VarSelf`/`VarFree`/`ValFree`/`ValCon`, plus the two still-`admit`'d
  `Select`/`Guess`) needed only mechanical pass-through — no new reasoning.
- `NEval_left_self_confluence` (the self-confluence corollary right after the theorem) needed the identical
  seven hypotheses added to its own statement and threaded into its call to the main theorem, since `e1` and
  `e2` coincide there (`NoShadowB e` supplied for both slots at once).

**Status:** `alpha_renaming_wip.v` compiles clean, zero errors, still exactly 2 admits (`NL_Select`,
`NL_Guess`) — this session's own §43-§49 work has now built and threaded *everything* `BlkAlpha_compose_
rename` needs; nothing new remains to design. **Next step (turned out to be optimistic, see §50):**
`NL_Select`'s own admit looked like a pure wiring task — build the case's actual proof body: `BrsAlpha_
lookup` for `rho`/`ysX` (`Hcap1` gives `Hrhoinj0` directly), `zipsubst_compose_in`/`zipsubst_compose_out`
for the top-level `Hagree` fact, `NEval_left_forced_args_stay_defined` for the freshness half `Hinj2`/
`Hconsistent` need, `Hbt` now trivial via `NoCaptureB`, and finally `BlkAlpha_compose_rename` itself to
close the case.

## 50. Same session, continued: hand-tracing the actual wiring found one more genuine gap — `Hinj1` needs a
freshness fact that isn't covered by anything built so far, and isn't just a mechanical detail

**The wiring plan itself checked out.** Worked out, by hand, the full structure for `NL_Select`'s proof
body: destructure `He2` to get `e2 = BCase (sigma0 x) brs2`; apply `NEval_left_bcase_shape` to `H2` to get
D2's own two-way case split; apply `IH1` to `Hrec1` (the scrutinee's own confluence) uniformly across both
branches, closing the Guess branch by `discriminate` (an `ECon`-shaped result can't equal an `EVar`-shaped
one) exactly as the case's own long-standing comment already described; then, in the surviving Select
branch, use `BrsAlpha_lookup` + `BrsAlpha_labels_eq` + `brs_label_unique` to pin D2's own `NEval_left_bcase_
shape` witness down to the *literal same* branch entry `BrsAlpha_lookup` itself finds (this part really was
exactly what the existing comment already claimed was done). All of that traces through cleanly using
pieces already `Qed`'d.

**Where it stopped: `Hinj1`, one of `BlkAlpha_compose_rename`'s own nine hypotheses, needs `theta1 :=
zipsubst ys zs` to be injective except within `ys` — and checking that concretely at the real instantiation
surfaced a case none of this session's earlier freshness work actually covers.** Splitting `theta1 w1 =
theta1 w2` (for `w1, w2 ∈ vars_of_b body`) three ways: both in `ys` (exempted, fine), both outside `ys`
(identity, `w1 = w2` directly, fine), and the mixed case — one of `w1`/`w2` in `ys` (so its image is some
`zs`-value), the other a name **bound** somewhere inside `body` but not in `ys`. That mixed case needs `zs`'s
own values to never coincide with *any* syntactic bound name anywhere in `body` — including inside branches
`body`'s own evaluation never actually takes, since `BlkAlpha_compose_rename`'s recursion walks every branch
of every nested `BCase`, not just the one path `Hrec2` follows.

`NEval_left_forced_args_stay_defined` (§46) doesn't reach this: it protects a *specific*, operationally-
reached binder — the moment some nested `NL_Let` in the path `Hrec2` actually takes tries to bind a name
equal to a `zs`-value, its own `Hxfresh` (needing *undefined*) fails, because `zs`'s image stays *defined*.
That's a real fact about the execution path Hrec2 follows, but `Hinj1` is a purely syntactic premise, needed
*before* any of `body`'s own evaluation is examined, and it has to hold for every syntactic bound name in
`body` — including ones in branches that are never executed at all, which have no `NL_Let` step ever firing
to make their freshness an operational fact in the first place.

**This looks like the same kind of gap Sec.44's own notes anticipated but didn't yet need** — "a program-
wide 'bound names are drawn from a globally-fresh pool' invariant" — genuinely new design work, not a
mechanical detail to patch in passing. Checked whether anything already threaded (`NoShadowB e1`, `NoCaptureB
e1`, `He1closed`) covers it: `NoShadowB`/`NoCaptureB` are about bound-vs-bound and bound-vs-free *within*
`body` itself, not about `body`'s bound names versus `zs` (external, dynamic heap values); `He1closed` only
covers `e1`'s own *free* variables, never its bound ones.

**Status:** `alpha_renaming_wip.v` unchanged since §49 (this section's work was all hand-tracing, not yet
committed to the file) — still compiles clean, still exactly 2 admits. **Next step, flagged for discussion
rather than decided unilaterally, matching how every other genuine fork this session hit was handled:**
design that freshness invariant (most likely a new hypothesis on the confluence theorem itself, giving every
constructor argument value drawn from the heap immunity from colliding with any bound name anywhere in the
term being matched against it, with its own preservation argument through the induction) before finishing
`NL_Select`'s proof body.

## 51. Next session: diagnosed §50's gap down to a concrete example (a case scrutinee forcing to `Con c
[7]` colliding with a `let 7 = ...` bound inside an unreached branch of the matched body), then — on the
user's explicit direction, after a checkpoint commit/push as a fallback — strengthened `NL_Let`/`NL_Fun`/
`NL_Guess` themselves rather than building the smaller, contained "derivation-indexed predicate" alternative

**The diagnosis.** `N_Select`'s `zs` (and `N_Fun`'s `s`, `N_Let`'s `x`, `N_Guess`'s `ws`) were only ever
required fresh against the *current heap* (`G x = None`-style side conditions) — never against the finite
set of names the *program itself* binds, statically, in its own source text. Nothing in the operational
semantics stops a runtime-chosen name from coinciding with an unrelated bound name written elsewhere in the
program, including inside branches never executed. This is a real gap in the formalization, not a proof-
technique shortfall: a real implementation gets this for free because compiled-away source names and
malloc'd addresses are disjoint namespaces, but this development types both as the same `var`.

**The two candidate fixes, and the choice.** (a) A *derivation-indexed* predicate (`Fixpoint` over an
`NEval_left` proof term, recursing into each sub-derivation, asserting the needed fact only at `NL_Let`/
`NL_Fun`/`NL_Guess`) — contained entirely to `alpha_renaming_wip.v`, zero changes to `NEval_left` or its
~50 other call sites, but less reusable/elegant. (b) Strengthen `NL_Let`/`NL_Fun`/`NL_Guess`'s own premises
directly with a new `ProgBoundName` side condition — the "textbook correct" fix (a real, reusable
`GlobalFreshHeap`-style invariant), but changes the base relation's constructor arities, which a `grep`
before starting showed touches roughly 50 pattern-match sites across `curry_test_leftmost.v` (8,666 lines)
and `alpha_renaming_wip.v`, plus (found only once inside it) 14 *construction* sites needing real new proof
content, not just mechanical pattern updates. The user chose (b) explicitly, after being shown the real
scope, and asked for a checkpoint commit+push first as a fallback — done (`a5052fd`) before any surgery.

**The apparatus, built in `curry_test_leftmost.v` ahead of `NEval_left`'s own definition** (Coq requires
every identifier fully defined before use, so `bound_vars_b` — previously living deep inside
`alpha_renaming_wip.v` — was relocated here too):
```
Fixpoint bound_vars_b (b : Blk) : list var := ...  (* moved, unchanged *)
Definition ProgBoundName (P : Prog) (x : var) : Prop :=
  exists f ps body, P f = Some (ps, body) /\ (In x ps \/ In x (bound_vars_b body)).
```
`NL_Let`/`NL_Fun`/`NL_Guess` each gained one new premise, inserted right after their existing heap-freshness
condition: `~ ProgBoundName P x` (`NL_Let`), `forall y, ~ In y ps -> ~ ProgBoundName P (s y)` (`NL_Fun`),
`forall w, In w ws -> ~ ProgBoundName P w` (`NL_Guess`). `NEval_left_to_NEval` (the embedding into plain,
unstrengthened `NEval`) needed only its pattern updated — the new fact is simply dropped, since `NEval`'s
own rules don't need it.

**The sweep, done compile-error-driven rather than by pre-reading every site** (Coq's own arity-mismatch
errors are a complete, precise checklist of every site touching the changed constructors): a blanket `sed`
first inserted a new bound name (`Hnb`) into every `induction ... as [...]` pattern whose `NL_Fun`/`NL_Let`/
`NL_Guess` arm used the file's own extremely consistent naming convention (`Hfresh Hrec IH`, `HzFresh Hrec
IH`, `HND Hfr Hrec2 IH2`) — catching the vast majority of the ~50 sites in three commands. **This first
sed pass had a real bug**, caught by the very next compile: `GEval`'s *own*, completely unrelated `G_Fun`/
`G_CaseConFree` constructors (unchanged, in `curry.v`) happen to use the *identical* variable-naming
convention at their own `induction`/`destruct` sites, so the blanket substitution corrupted ~22 `GEval`-
shaped patterns that were never supposed to change — caught immediately (every corrupted line was
distinguishable by lacking `NEval_left`'s own leading `F0` guard-set argument) and reverted by exact line
number before continuing. Lesson for next time: a naming-convention-based blanket `sed` across a large file
needs an explicit structural discriminator (here, "does the pattern start with F0") checked *before* trusting
its results, not just a post-hoc compile check — the compile check caught it here only because the *count*
of `GEval` inductions was large enough to hit early, not because the corruption was self-evidently visible.

**The remaining sites needed real content, handled case by case as the compiler surfaced each one:**
- Two shape-inversion lemmas needed the new fact threaded into their own *conclusions*, since callers
  destructure them to get at `NL_Guess`'s witnesses: `NEval_left_bcase_shape` (10 call sites) and (found
  transitively) `NEval_left_fwd_transfer_fwdhere_free`/`HeapCorr_fwd_transfer_fwdhere_free`'s own signatures.
  Each of the ~15 downstream call sites got the mechanical "add one more binder to the destructuring
  pattern" treatment, plus (where the branch's own proof actually consumed the freshness fact to construct
  a further `NL_Guess`) a real `exact Hnb`/`exact Hnbws` substitution — never a new obligation, since in
  every case the witness being reused (`s`, `x`, `ws`) was *the same* witness the fact already existed for.
- **The one genuinely new, unavoidable class of gap:** sites bridging `GEval` (the graph semantics, in
  `curry.v`, deliberately left untouched) into `NEval_left` construction — `GEval`'s `G_Fun`/`G_Let`/
  `G_CaseConFree` carry no `ProgBoundName` fact about their own witnesses at all (mirroring the exact same
  gap on the graph side), so nothing exists to discharge the new `NEval_left` premise from. Checked, before
  admitting any of these, whether the *enclosing* lemma was already fully `Qed`'d or already `Admitted` in
  the pre-surgery checkpoint (`git show a5052fd:... | awk ...`) — every single one (`NEval_left_let_chain_
  to_fwd`, `NEval_left_let_chain_to_con`, `NEval_left_let_chain_to_value`, and `curry_test_leftmost.v`'s own
  restatement of `theorem2` itself) was *already* `Admitted` before this session touched anything, so a new
  `admit` there adds a new, clearly-`(* NEW GAP *)`-commented gap to an already-incomplete result, not a
  regression of a previously-closed one. **Verified, not just argued:** `Admitted.`-terminator count in
  `curry_test_leftmost.v` is unchanged (9 before, 9 after) despite 10 new `admit`s being added, and every
  one of the ~6 lemmas fixed with *real* content (`NEval_left_frame_guarded`, `NEval_left_choice_as_alias_
  bcase`, `NEval_left_fwd_transfer`, `NEval_left_fwd_transfer_fwdhere_free`, `HeapCorr_fwd_transfer_
  fwdhere_free`, `NEval_left_bcase_shape`) still ends in `Qed.` with no `admit` inside it.

**Crucial point for the actual project this session serves:** `curry.v`'s own `theorem2` (the result the
very first commit calls "the main theorem") uses the *original*, unmodified `NEval` — completely untouched
by any of this. `curry_test_leftmost.v`'s *separate* restatement of `theorem2` via `NEval_left` (built later,
as a stepping stone toward the leftmost-bias confluence work this session actually cares about) was already
`Admitted` before this session started, so gaining a few more precisely-scoped, clearly-commented admits
inside it is not a regression of anything the project considers "done."

**Status:** both `curry_test_leftmost.v` and `alpha_renaming_wip.v` compile clean, zero errors.
`curry_test_leftmost.v`: 9 `Admitted.` (unchanged from before this session), `admit` count 29 → 39 (10 new,
all inside already-`Admitted` lemmas, each `(* NEW GAP *)`-commented). `alpha_renaming_wip.v`: still exactly
**2 admits** (`NL_Select`, `NL_Guess`) — unchanged, zero regressions; the whole point of the surgery (a real,
program-wide `ProgBoundName`/`GlobalFreshHeap`-style fact usable at `NL_Select`'s own call site) is now
available but **not yet used** — `Hinj1` itself has not yet been attempted against it. **Next step:** build
`GlobalFreshHeap`/an initial-heap hypothesis on `NEval_left_confluence`, prove it preserved through all 11
cases (mechanical pass mirroring §49, with real derivation needed only at `NL_Let`/`NL_Fun`/`NL_Guess`,
now trivial since those rules directly hand back the needed fact), then use it to close `Hinj1` and finish
`NL_Select`'s (and, mirroring it, `NL_Guess`'s) actual proof body.

## 52. Same session, continued: built `GlobalFreshHeap`/`NoCaptureProgB`/`NoCaptureProgHeap` and their joint
preservation theorem, then threaded all three through `NEval_left_confluence` and `NEval_left_self_
confluence` — zero admits added, `NL_Select`/`NL_Guess` still the only two remaining

**The apparatus** (alpha_renaming_wip.v, right after `let_content_NoCapture`, ahead of everything that
needs `bound_vars_b_rename`/`NoDup_app_disjoint`): `GlobalFreshHeap P G := forall x, ProgBoundName P x -> G
x = None` (heap keys avoid the program's own static names); `NoCaptureProgB P b := forall x, In x
(bound_vars_b b) -> ~ ProgBoundName P x` (a TERM's own bound names avoid them — deliberately NOT required
of the term's free/unrenamed static occurrences, mirroring `NoCaptureB`'s own asymmetry); `NoCaptureProgHeap
P G := forall z b, G z = Some b -> NoCaptureProgB P b` (every heap-STORED value satisfies it too — needed
for the same reason `NoShadowHeap`/`NoCaptureHeap`/`BrsUniqHeap` were needed: `NL_VarExp` pulls a term IN
from the heap, not from `e`'s own structure, so nothing about `e` implies anything about it).

**`NEval_left_globalfresh_preserved`** mirrors `NEval_left_closed_preserved` case for case (identical
`ClosedHeap`/free-closedness bookkeeping, duplicated rather than invoked, since every case's own recursive
IH call needs the new facts threaded ALONGSIDE the old ones, not instead of them) — `VarCons`/`VarSelf`/
`ValFree`/`ValCon` immediate, `VarFree`/`VarExp` via a `hupd`-at-an-already-defined-key contrapositive
argument (if `ProgBoundName P x` held, `GlobalFreshHeap` would already force `G x = None`, contradicting the
rule's own precondition that `x` is already heap-resident — so the newly-written key can never itself be a
static name), `Fun` via `bound_vars_b_rename` (`bound_vars_b (rename_b s body) = map s (bound_vars_b
body)`, general, no injectivity needed) composed with `ProgNoShadowWF`'s own `NoDup (ps ++ bound_vars_b
body)` (pins down that `body`'s own bound names are never among `ps`) and NL_Fun's OWN new premise (`Hnb`)
applied there, `Let` via `Hnb` directly (the new key literally IS what `Hnb` exempts), `Select` via `zipsubst_
in` + `NEval_left_closed_preserved`'s own already-established `zs`-defined-in-`G1` fact, contrapositived
against `GlobalFreshHeap G1`, `Guess` via `Hnb` directly again (simpler than Select — `ws`'s own freshness
against `ProgBoundName` is a DIRECT hypothesis here, no indirection through heap-definedness needed).
**Compiled clean on the first attempt, zero admits, `Print Assumptions` confirms "Closed under the global
context."**

**Threading into `NEval_left_confluence`/`NEval_left_self_confluence`:** added `GlobalFreshHeap P Gam1`,
`NoCaptureProgHeap P Gam1`, `NoCaptureProgB P e1` as three new top-level hypotheses (mirroring exactly where
`ClosedHeap`/`NoShadowHeap`/`NoCaptureHeap`/`NoCaptureB e1` already sit), then touched every `IH`/`IH1`/`IH2`
call site that recurses into an UNCHANGED heap (`VarExp`, `Fun`, `Or`) with a straight pass-through (or, for
`VarExp`, extracting the heap-stored value's own `NoCaptureProgB` fact from `NoCaptureProgHeap` — mirroring
`He0BrsUniq`'s own precedent exactly) and the one case that grows the heap in a way this proof's own
recursion still needs (`Let`) with the same `HnewGF`/`HnewNCHeap` construction already written inside
`NEval_left_globalfresh_preserved` itself, copied in (not invoked — confluence's own induction needs its OWN
copy of the bookkeeping, since its `IH` is a fact about ITSELF, not about the standalone preservation
theorem). **`Select`/`Guess` themselves were NOT touched** — both remain a bare `admit.`; the new hypotheses
just sit unused in their local context for now, available for the next step. One purely mechanical surprise
along the way: two bare `destruct H2 as [...]` shape-inversion sites (not `induction`, so the earlier
sed pass's naming convention didn't match them) needed the same one-more-binder fix by hand, caught
immediately by the compiler.

**Status:** both files still compile clean, zero errors, zero new admits anywhere — `alpha_renaming_wip.v`
still exactly 2 admits (`NL_Select`, `NL_Guess`), `curry_test_leftmost.v` unchanged from §51. **Next step:**
actually write `NL_Select`'s proof body — branch-identification via `BrsAlpha_lookup`/`brs_label_unique`
(already built, per the case's own long-standing comment), `zipsubst_compose_in`/`zipsubst_compose_out` for
`Hagree`, `NEval_left_forced_args_stay_defined` for the zs-freshness half of `Hinj2`/`Hconsistent`, `Hbt` via
`NoCaptureB`, `Hinj1` NOW via `NEval_left_globalfresh_preserved` (called on `Hrec1` to get `GlobalFreshHeap P
G1`, then the same `zipsubst_in`-plus-contrapositive argument already proven inside that theorem's own
Select case), and finally `BlkAlpha_compose_rename` itself to close the case — genuinely the first time
every single piece it needs has existed, Qed'd, before starting; `NL_Guess` mirrors it afterward.

## 53. Same session, continued: started writing `NL_Select`'s actual proof body, found `Hinj1` — even with
`GlobalFreshHeap` in hand — fails for a SECOND, structurally different collision (a substituted constructor
field vs. an unrelated already-live free variable, not a bound one); confirmed both halves with a
machine-checked disproof + companion derivation before doing anything about it

**The new collision, found by hand-tracing `Hinj1`'s literal requirement.** `Hinj1` quantifies over ALL of
`vars_of_b body` (not just its bound names), requiring: for `w1, w2 ∈ vars_of_b body` with `zipsubst ys zs w1
= zipsubst ys zs w2`, either `w1 = w2` or both are pattern variables (`ysX = ys`). `GlobalFreshHeap` protects
the "both bound-vs-pattern" collision (§50-52's own motivating case). It does NOT protect this one: take a
branch `case x of C w1 -> let dummy = w2 in w1`, where `w2` is an ordinary, already-live FREE variable of the
branch (nothing to do with the match), and suppose forcing `x` yields `Con C [w2]` — i.e. the constructor's
OWN field happens to literally be `w2`, the SAME already-existing variable the branch also references
directly. Nothing rules this out: a forced constructor's fields are just whatever pre-existing bindings the
program put there, with no reason to avoid every OTHER free variable the matched branch happens to also
mention (this is ordinary sharing, exactly the kind of aliasing this graph-reduction semantics exists to
support). After substitution (`theta1 := zipsubst [w1] [w2]`), BOTH the pattern-var occurrence (now `w2`) AND
the pre-existing free occurrence of `w2` read as the bare name `w2` — `theta1` sends two DISTINCT names to
the same value, `w2` is not a pattern variable, and `w1 ≠ w2` — neither `Hinj1` disjunct is available.

**Confirmed with a machine-checked disproof before designing anything** (user's explicit direction, mirroring
this project's own established practice — `NEval_left_confluence_stmt_is_false`'s precedent) — TWO separate
checks, both in `failed_attempts.v` §7, both `Print Assumptions`-clean (zero axioms):
1. `Hinj1_fails_concretely`: a fully concrete instance (`ys := [1]`, `zs := [2]`, `body := let 3 = 2 in 1`,
   so `vars_of_b body = [3;2;1]`) where `zipsubst [1] [2]` sends both `1` and `2` to `2`, with neither
   disjunct available — a bare five-line computation, no `NEval_left`/`GEval` machinery needed at all.
2. **The crucial companion check, to determine severity**: does `NEval_left_confluence`'s own CONCLUSION
   still hold in a full, concrete instance of exactly this scenario, or is the theorem itself now suspect?
   Built two complete, literal `NEval_left` derivations (`Hinj1_D1_ex`/`Hinj1_D2_ex`) from the identical heap
   — `D1` over a branch with pattern var `1`, `D2` over the alpha-variant with pattern var `4` (`sigma0 :=
   id`, the branch's own local override sending `1 ↦ 4`) — and both reach the literal SAME final value
   (`BExpr (ECon 5 [])`), alpha-related by plain `id`. **This settles the question**: `NEval_left_confluence`
   itself is NOT threatened by this scenario — this is a proof-TECHNIQUE gap in `BlkAlpha_compose_rename`'s
   current design (its `Hinj1` hypothesis is strictly stronger than the theorem actually needs), not a
   soundness bug in the theorem's statement, unlike §41/45's own disproof (which WAS a genuine inconsistency
   of the statement as it then stood).

**Status:** `failed_attempts.v` gains four new lemmas (§7), all `Print Assumptions`-clean; `alpha_renaming_wip.v`
and `curry_test_leftmost.v` both unchanged, still compiling clean, still exactly 2 admits. **Next step,
flagged for discussion rather than decided unilaterally, matching how every other genuine fork this session
hit was handled:** design a fix. Two directions sketched but not yet attempted: (a) widen `BlkAlpha_compose_
rename`'s own exemption structure — e.g. a third `Hinj1` disjunct covering "both `theta1`-images already
agree with what `Hagree`/`Hconsistent` independently pin down," letting the "collides with an already-
consistent free variable" case through soundly; or (b) a different overall proof strategy for `NL_Select`
that doesn't route through `BlkAlpha_compose_rename`'s current shape at all. (a) keeps the substantial
existing investment in that lemma but requires re-deriving its own internal induction against a weaker
hypothesis (real risk of hitting the same kind of "at least one side bound somewhere" case-split work §44-47
already went through once); (b) risks discarding a large, fully-`Qed`'d piece of machinery for an unknown
replacement. Neither has been attempted.

---

# Part 2: Rocq/Coq Tactics and Idioms Glossary

This part catalogs, with real examples, every distinct tactic/pattern used repeatedly across
this work. It's organized roughly from "structural, load-bearing idioms" to "small mechanical
helpers."

## T1. `remember ... as ... eqn:` + `revert` + `induction`/`destruct` — generalizing an index before inducting

**The problem it solves.** Coq's `induction`/`destruct` on a hypothesis `H : Ind a1 ... an`
requires each index `ai` to be a bare variable, not a compound term, if you want the resulting
motive to properly track how each constructor constrains that index. If `H : GEval P G
(BCase x brs) G' v` and you `induction H` directly, Coq either complains or (worse) silently
loses information relating `BCase x brs` to each constructor's own conclusion, because
`BCase x brs` is a *compound* term, not a variable, occupying that index position.

**The fix.** Introduce a fresh variable standing for the compound term, remember the equation
relating them, generalize (`revert`) anything that depends on the pieces you'll need to recover
later, then induct/destruct on the *now-uniform* hypothesis. Real example
(`NEval_left_force_free_sound`, `curry_test_leftmost.v` ~3603-3612):

```coq
Proof.
  intros P G x brs G' v H.
  remember (BCase x brs) as e eqn:He.
  revert x brs He.
  induction H as [ ... ]; intros x1 brs1 He; try discriminate He;
    injection He as He1 He2; subst x1 brs1; ...
```

`remember (BCase x brs) as e eqn:He` replaces the compound term with a fresh `e`, and records
`He : e = BCase x brs` (well, actually the direction is `He : BCase x brs = e` becomes visible
via how it's used — check via `discriminate`/`injection` which direction the tool leaves it in;
in practice it doesn't matter much because both directions destructure the same way). `revert x
brs He` pushes `x`, `brs`, and the remembered equation back into the goal so that `induction H`'s
automatically-generated motive quantifies over them too (otherwise the induction would fail to
typecheck, or would silently generalize them itself in a way you don't control). Then, in each of
the 13 branches, `intros x1 brs1 He` reintroduces them (now under fresh names per-branch, since
each branch has its own bound variables), `try discriminate He` throws out every branch whose
conclusion isn't syntactically `BCase _ _` (so `He : BExpr (EFun f args) = BCase x1 brs1` is a
manifestly absurd equation between different `Blk` constructors — `discriminate` closes it
instantly), and the survivors get `injection He as He1 He2; subst x1 brs1` to recover
`x1 = x0`/`brs1 = brs0` and substitute them away, leaving the goal phrased in terms of the
constructor's own bound names.

This exact skeleton is used, near-verbatim, in essentially every "shape inversion" lemma in the
file (see T2) and in the main inductions (`NEval_left_force_free_sound`,
`NEval_left_let_chain_to_fwd`/`_to_con`, `NEval_left_frame_guarded`, etc.).

## T2. The "shape inversion" idiom: extracting "only constructor `C` could have produced this"

A specialized, very common use of T1: given a hypothesis whose *conclusion* has a fixed,
concrete shape (e.g. `GEval P G (BExpr (EVar x)) G' v`), prove that only one constructor of the
inductive relation could possibly have that shape, and extract exactly the facts that
constructor's premises give you. General template:

```coq
Lemma <name>_shape :
  forall <args>, <Relation> <args'> (<concrete pattern>) <result vars> ->
  <conjunction/existential of facts that the ONE matching constructor's premises provide>.
Proof.
  intros <args> H.
  remember (<concrete pattern>) as e eqn:He.
  destruct H as [ <one pattern per constructor> ]; try discriminate He.
  <for the survivor(s): injection He as ...; subst ...; exact/split the extracted facts>
Qed.
```

Real, complete example (`GEval_var_shape`, `curry_test_leftmost.v` ~3488):

```coq
Lemma GEval_var_shape :
  forall P G x G' v, GEval P G (BExpr (EVar x)) G' v -> G' = G /\ v = GFwd x.
Proof.
  intros P G x G' v H.
  remember (BExpr (EVar x)) as e eqn:He.
  destruct H as
    [ G0 | G0 | G0 c0 args0 | G0 x0 y0 | G0 x0
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
```

Only the `G_Var` branch (5th pattern, `G0 x0`) survives `try discriminate He`, because every
other constructor's conclusion has a *syntactically different* second argument (`BExpr EBot`,
`BExpr EFree`, `BExpr (ECon c args)`, `BExpr (EChoice x y)`, `rename_b s body`, `BLet ...`,
`BCase ...` — none of which unify with the fixed pattern `BExpr (EVar x)` except the one that
*is* `BExpr (EVar x0)`). This pattern was used repeatedly this session and throughout the file
for: `GEval_var_shape`, `GEval_echoice_shape`, `GEval_fun_shape`, `NEval_left_evar_shape`,
`NEval_left_fun_shape`, `NEval_left_echoice_shape`, `NEval_left_bcase_shape`, and more. It is the
single most repeated non-trivial idiom in the file.

**A variant using `induction` instead of `destruct`**, when the shape lemma itself needs to
recurse (e.g. because the relation being shaped is on the *outside* of another induction, or the
lemma proves something about an arbitrarily deep chase) — see `GEval_case_gives_ContractLoc`,
`GEval_case_gives_ContractLoc_deep`, `NEval_left_force_free_sound` itself, all of which use
`induction H as [...]` in place of `destruct H as [...]` in the T1/T2 skeleton, because they need
an IH for constructors whose conclusion *does* match (e.g. `G_CaseFwd`'s recursive premise).

## T3. `injection ... as ...` vs. `discriminate` vs. `inversion` — differences and pitfalls

- **`discriminate H`**: closes the goal when `H` is an equation between two *manifestly
  different* constructors of the same inductive type (e.g. `H : BExpr e = BLet x e' k`, or
  `H : Some a = None`). Produces `False` from thin air, since such an equation can never hold.
  Also works when `H`'s type reduces (via `simpl`/computation) to such an equation — Coq will
  attempt the reduction automatically. Cannot be used on an equation between two applications of
  the *same* constructor (e.g. `Some a = Some b`) — for that, use `injection`.

- **`injection H as name1 name2 ...`**: given `H : C a1 a2 = C b1 b2` (same constructor `C`
  applied to different arguments), produces the componentwise equations `a1 = b1`, `a2 = b2` as
  new, separately-named hypotheses, and clears `H`. **Pitfall hit this session**: if one of the
  resulting equations has a *bare variable* on both/either side with nothing further to
  decompose (e.g. `H : Some (BExpr (EVar y)) = Some (BExpr (EVar y))` after everything else is
  already forced equal, or more commonly a leftover equation like `b = <concrete term>` where
  `b` is already a bare variable and there's genuinely nothing left to "inject" out of it),
  `injection H as H` can fail with **"Nothing to inject."** The fix used repeatedly: replace
  `injection Hbeq as Hbeq. subst b.` with plain `subst b.` (or, if `b` isn't a bare variable on
  one side, just `rewrite` directly) — i.e., recognize when the equation is already "atomic"
  enough that `subst`/`rewrite` alone suffices, without going through `injection` first.

- **`inversion H`**: the most general of the three. Given `H : Relation a1 ... an`, it examines
  *every* constructor of `Relation`, discards the ones whose conclusion cannot unify with
  `a1 ... an`, and for each survivor, introduces its premises as new hypotheses/goals, plus the
  equations forced by unifying the conclusion's indices against `a1 ... an` (left as separate
  hypotheses, *not* auto-substituted — that's `inversion ...; subst`'s job). `inversion` is more
  powerful than a hand-written `destruct ... as [...]; try discriminate` (T2) because it doesn't
  require you to enumerate every constructor pattern by hand and doesn't require a prior
  `remember` — but it's also less controllable: it can produce hypothesis names you didn't
  choose, and (crucially, see T-subst-pitfall below) `inversion H; subst` risks the *same* kind
  of "wrong equation chosen" bug that bare `subst` can hit anywhere else. In this codebase, the
  explicit `remember`+`destruct`+`discriminate` idiom (T1/T2) was consistently preferred over
  bare `inversion` for shape-extraction lemmas specifically *because* it gives full control over
  binder names and avoids `inversion`'s own implicit substitution behavior — see the discussion
  in §9.3.

## T4. The `subst` pitfall: ambiguous variable elimination

`subst x` (or bare `subst`, which tries to eliminate every eligible variable it can find) looks
through *all* hypotheses in context for an equation that lets it eliminate `x` — `x = t` or
`t = x` for some term `t` not containing `x`. **If more than one such hypothesis exists, `subst`
picks one, and there's no guarantee it's the one you meant.** This session hit exactly this bug
(§9.3, Bug 1): inside a sub-proof establishing `w0 <> x0`, `intro Heq; subst w0` was written
expecting `subst` to use the just-introduced `Heq : w0 = x0` — but an *earlier*, still-in-scope
hypothesis `Hsy1 : s y1 = w0` was *also* a valid elimination target for `w0` (since `w0` sits
bare on its right-hand side), and `subst` silently chose *that* one instead, rewriting `w0` to
`s y1` **everywhere in the context, including inside `Heq` itself** (turning it into the much
less useful `Heq : s y1 = x0`). The resulting error surfaced many lines later, far from the
actual cause, as an opaque type mismatch.

**The fix, used consistently after this was diagnosed**: whenever more than one hypothesis in
scope could plausibly eliminate the same variable, don't use `subst` at all — use a **targeted
`rewrite H in H'`** naming exactly the one hypothesis you want changed and exactly the equation
you want to apply:

```coq
(* risky: *)
intro Heq; subst w0.

(* safe: *)
intro Heq; rewrite Heq in Hrec2g.
```

Similarly, after a shape lemma produces two output equations (e.g. `GEval_var_shape` giving
`HG1eq : G1 = G0` and `Hvxeq : vx = GFwd w0`), prefer `rewrite HG1eq, Hvxeq in Hrec2g` (rewriting
only the one hypothesis that actually needs updating) over `subst G1 vx` (which touches every
hypothesis mentioning either variable, and — while the multi-name form of `subst` is generally
safer than bare `subst` since it's scoped to the named variables — is still worth avoiding when
you specifically want to control the blast radius).

## T5. `destruct t as [...] eqn:H` auto-substitutes `t` everywhere, not just the goal

When `t` is a *compound* term (not a bare variable) and you write `destruct t as [pat1 | pat2 |
...] eqn:H`, Coq doesn't just case-split the goal — it **generalizes `t` and substitutes each
case's reconstructed pattern for `t` in every hypothesis that mentions it too**, not only in the
goal. This is usually exactly what you want, but it produces a specific, easy-to-hit error if
you then try to *manually* rewrite using the `eqn:` equation afterward: since the substitution
already happened everywhere, `rewrite H in SomeOtherHyp` (where `SomeOtherHyp` used to mention
`t`) fails with **"Found no subterm matching `t` in `SomeOtherHyp`"**, because `t` isn't there
anymore — it's already been replaced. This was hit and fixed this session (an earlier occurrence
in the `G_CaseFun`/body-shape case split): the fix was simply to delete the now-redundant
`rewrite ... in Hrec3;` prefix and use the hypothesis directly, since `destruct (rename_b s body)
as [...] eqn:Hbodyshape` had already updated `Hrec3`'s type for you.

## T6. Bullet structuring (`-`, `+`, `*`, `--`, `++`, ...) for nested case proofs

Coq's bullet system lets you mark, and have the type-checker *enforce*, which sub-goal a given
block of tactics is meant to address, at each level of case-nesting. The convention used
throughout this file: `-` for the outermost level (e.g. one bullet per `GEval` constructor after
an `induction`), `+` for the next level in (e.g. one bullet per disjunct of a `CorrE_forced_shape`
destructuring), `*` for the level after that, then `--`, `++`, and so on, doubling up the symbol
once the single-character levels are exhausted. This matters for more than style: **if a bullet's
tactics don't fully close its sub-goal (or accidentally leave stray goals from a sibling), Coq
raises an error immediately at the point of the mismatched bullet**, rather than silently letting
the proof script wander into the wrong goal — which is exactly the kind of silent-drift bug you
want caught early in a 4000+-line file with many deeply nested case splits. Real example (the
`G_CaseFun` case's `BExpr e0` sub-split, `curry_test_leftmost.v` ~3661 onward):

```coq
      * (* rename_b s body = BExpr e0 *)
        destruct e0 as [ w0 | | | y1' y2' | f2 args2 | c1 args2 ].
        -- (* EVar w0: ... *)
           ...
        -- (* EBot: ... vacuous. *)
           inversion Hrec3.
        -- (* EFree: ... vacuous. *)
           inversion Hrec3.
        -- (* EChoice y1' y2': ... *)
           ...
        -- (* EFun f2 args2: ... *)
           admit.
        -- (* ECon c1 args2: ... vacuous. *)
           inversion Hrec3.
```

## T7. `eapply` vs. `apply`

`apply lemma` requires Coq to be able to fully unify the *entire* conclusion of `lemma` against
the current goal in one step, including inferring every one of `lemma`'s earlier arguments from
that unification; if some argument can't be inferred that way (because it doesn't appear in the
conclusion, or the conclusion alone underdetermines it), plain `apply` fails outright. `eapply
lemma` is the same, but instead of failing when an argument can't be inferred, it leaves it as a
fresh, unresolved metavariable — which either gets pinned down by unifying a *later* explicit
argument you supply, or is left as a **separate goal to discharge afterward**, typically one per
missing argument, addressed in order with subsequent bullets. This codebase uses `eapply`
pervasively for exactly this reason — most of the relation constructors (`NL_VarExp`, `N_Select`,
`CorrE_FwdAchievedCon`, etc.) have several premises that aren't determined by the conclusion
alone, so `eapply Constructor; [ tac1 | tac2 | ... ]` (or the bulleted `eapply Constructor.
- tac1. - tac2. ...` form) is the standard way to instantiate them one at a time. Plain `apply` is
reserved for cases where full, immediate unification is expected to just work (e.g. applying an
already-fully-instantiated hypothesis directly).

## T8. `exists`/`eexists` and nested-existential/conjunction unpacking

Providing a witness for `exists x, P x` is `exists w` (or, if the witness itself should be left
to unification/a later tactic, `eexists`, deferring the choice as a metavariable). Consuming a
hypothesis of nested existentials/conjunctions is done via nested `destruct ... as [...]`
patterns whose bracket-nesting must exactly mirror the statement's own right-associated nesting.
A concrete, representative (and easy to get subtly wrong) example — unpacking
`NEval_left_fun_shape`'s five-part conjunction wrapped inside two existentials:

```coq
destruct (NEval_left_fun_shape P (x0::F) Gam f0 args0 G1' (BExpr (EVar x')) Hrec2)
  as [ps [body [s [HPf [Hlen [Hinj [Hmatch [Hfresh2 Hrec3]]]]]]]].
```

The lemma's conclusion is `exists ps body s, P /\ Q /\ R /\ S /\ T /\ U` — which Coq parses as
`exists ps, (exists body, (exists s, (P /\ (Q /\ (R /\ (S /\ (T /\ U)))))))` (existentials and
right-associated conjunction, nested nine levels deep by the time you count both). The
`destruct ... as [...]` pattern must match that nesting *exactly*, bracket for bracket, in
order — this is the single most common source of "this pattern has N bindings but the term has
M" errors in a large proof, especially after editing a lemma's statement (adding/removing a
conjunct) without also updating every call site's unpacking pattern. There is no shortcut other
than counting parentheses carefully or letting Coq's own error message ("Unused introduction
patterns" / "not enough" / disjunctive-pattern mismatches) guide a fix.

## T9. `assert (H : T) by tac` vs. `assert (H : T). { tac. }`

Both introduce a new hypothesis `H : T`, proved by `tac`, into the current goal. `by tac` is
strictly for when `tac` is expected to close the sub-goal *completely* in one shot (a single
tactic, or a short `;`-chained sequence) — it's a compact, single-line idiom, e.g.:

```coq
assert (Hself : (hupd G0 x0 (GFwd x0)) x0 = Some (GFwd x0))
  by (unfold hupd; rewrite Nat.eqb_refl; reflexivity).
```

The `{ tac. }` (curly-brace focus) form is used when the sub-proof needs *multiple* tactics
across multiple lines, its own internal case-splitting/bullets, or is simply long enough that
inlining it into a `by (...)` would hurt readability:

```coq
assert (HGamw0 : Gam w0 <> None).
{ destruct (NEval_left_evar_shape P (x0::F) Gam w0 G1' (BExpr (EVar x')) Hrec3) as
    [ [Hc1 _] | [ [Hc2 _] | [ [Hc3 _] | [_ [e1 [G1'' [Hz1 _]]]]]]];
  [ rewrite Hc1 | rewrite Hc2 | rewrite Hc3 | rewrite Hz1 ]; discriminate. }
```

Both are used throughout this file; the choice is purely about sub-proof length/complexity, not
semantics.

## T10. `unfold hupd; rewrite Nat.eqb_refl` and `hupd_neq` — reasoning about heap update

The heap-update function is defined as (`curry.v` ~201):

```coq
Definition hupd {A} (h : heap A) (x : var) (v : A) : heap A :=
  fun y => if Nat.eqb y x then Some v else h y.
```

To prove `(hupd h x v) x = Some v` (reading back the just-written location), the idiom is
`unfold hupd; rewrite Nat.eqb_refl; reflexivity` — unfold the definition to expose the `if`,
rewrite `Nat.eqb x x` to `true` via `Nat.eqb_refl`, then the `if` reduces definitionally and
`reflexivity` closes it. To prove `(hupd h x v) y = h y` for `y <> x` (reading back an
*untouched* location), the codebase instead uses the already-proven helper lemma `hupd_neq`:

```coq
Lemma hupd_neq : forall {A} (h : heap A) z g x, x <> z -> hupd h z g x = h x.
```

so `rewrite (hupd_neq h x v y Hyx)` (given `Hyx : y <> x`) rewrites `(hupd h x v) y` down to
plain `h y` in one step, rather than re-deriving the `Nat.eqb`/`if` reasoning by hand every time.
Both idioms appear dozens of times throughout the file; `hupd_neq` in particular is the
single most-invoked auxiliary lemma outside the main relations.

## T11. `congruence` vs. `discriminate` vs. `injection` for equational reasoning

`congruence` is a decision procedure for equality reasoning that's strictly more automatic than
either `discriminate` or `injection` for straightforward goals: given a set of hypotheses that
are equations (possibly involving constructor applications) and a goal that's either an equation
or `False`, `congruence` will chain substitutions, apply constructor-injectivity, and apply
constructor-disjointness all on its own, closing many goals that would otherwise need an explicit
`injection`-then-`discriminate`-or-`rewrite` sequence spelled out by hand. It's used throughout
this file as a one-word closer whenever a goal is "obviously" implied by combining a couple of
equational hypotheses, e.g. `assert (Hbeq : b = BExpr (ECon c' args')) by congruence.` — letting
Coq find the chain of substitutions itself rather than spelling out `rewrite Hb in Hxxx; injection
... ` by hand. `discriminate`/`injection` remain preferable when you want a *specific*, readable,
single-purpose step (or when `congruence`'s automation is overkill/slower for a trivial case).

## T12. `Nat.eq_dec` / `in_dec` for decidable case splits

`Nat.eq_dec : forall x y : nat, {x = y} + {x <> y}` and (for list membership)
`in_dec : forall (A : Type), (forall x y : A, {x = y} + {x <> y}) -> forall (a : A) (l : list A),
{In a l} + {~ In a l}` provide the *decision procedure* needed to `destruct` a case split on
whether two variables are equal, or whether some variable is a member of a list, producing
exactly two goals with the corresponding hypothesis (`Heq : x = y` or `Hneq : x <> y`) already in
hand. Standard idiom: `destruct (Nat.eq_dec p x) as [Heqpx | Hnepx]` or
`destruct (in_dec Nat.eq_dec y1 ps) as [Hin | Hnin]`. Used constantly anywhere a proof needs to
distinguish "the location I'm updating" from "every other location."

## T13. Definitional/computational equality applied silently (no explicit rewrite needed)

Coq will accept a term of type `T` where type `T'` is expected as long as `T` and `T'` are
*convertible* (equal by computation/reduction), with no explicit tactic needed to bridge them —
this is one of the most powerful and most easily-missed features of the type theory. Concrete
example from this session: `let_content` is defined as
`let_content x e = match e with EFree => BExpr (EVar x) | _ => BExpr e end`. A lemma
(`HeapCorr2_update_to_direct`) is *stated* with `let_content x e` in its conclusion, but when
applied with a concrete, non-`EFree` constructor like `e := EChoice y1' w2`, Coq's unifier will
happily reduce `let_content x0 (EChoice y1' w2)` down to `BExpr (EChoice y1' w2)` *during
unification itself* — so a goal literally stated as
`HeapCorr2 (...) (hupd Gam x0 (BExpr (EChoice y1' w2)))` unifies directly against the lemma's
conclusion `HeapCorr2 (...) (hupd Gam x0 (let_content x0 (EChoice y1' w2)))` with **no `simpl`,
`unfold`, or explicit rewrite needed at all** — `eapply HeapCorr2_update_to_direct` just works.
This is a recurring theme: whenever a mismatch *looks* like it should need a rewrite, first check
whether it's actually already true by computation.

## T14. Section variables (`Variable P : Prog`) and implicit threading

`GraphSemantics`/`NatSemantics` (in `curry.v`) and the corresponding sections in
`curry_test_leftmost.v` are wrapped in `Section ... Variable P : Prog. ... End ...`. Inside the
section, every definition (`GEval`, `NEval`, `NEval_left`, and every lemma about them) can refer
to `P` as an ordinary in-scope name, with no need to abstract over it explicitly. Once the
section closes, Coq automatically re-generalizes every one of those definitions/lemmas to take
`P` as their **first explicit argument** — which is why, outside the section (i.e., everywhere
this file actually calls these lemmas), you see `GEval P G e G' v`, `NEval_left P F Gam e Gam' v`,
`NEval_left_evar_shape P F Gam y G' v ...`, with `P` spelled out explicitly every time, even
though it was never mentioned inside the section's own lemma statements. This is purely a
readability/ergonomics device for the file's *authors* (no need to thread `P` through every
internal statement by hand while writing the section) that becomes invisible plumbing for the
file's *callers* (who must supply `P` like any other argument).

## T15. Constructor order matters for `destruct ... as [pat | pat | ...]`, and getting it wrong is a real, recurring bug class

`destruct`/`induction ... as [pattern list]` binds each bracketed pattern to the constructors of
the relevant inductive type **in the exact order they were declared**, not by name or by some
canonical/alphabetical order. Two concrete bugs this project hit from assuming the wrong order:

- `Blk` is declared `BLet | BCase | BExpr` (`curry.v` line 62-65) — **not**
  `BExpr | BCase | BLet` as might be guessed by "expression-first" intuition. A pattern written
  as `destruct (rename_b s body) as [z e0 k | z brs2 | e0] eqn:Hbodyshape` is correct (matching
  `BLet`'s three fields, then `BCase`'s two, then `BExpr`'s one, in that order) — writing it with
  `BExpr`'s single-field pattern first produces either an outright arity-mismatch error ("Expects
  a disjunctive pattern with N branches") or, worse, a proof that silently type-checks against
  the *wrong* constructor's fields if the arities happen to coincide.
- `Expr0` is declared `EVar | EBot | EFree | EChoice | EFun | ECon` (`curry.v` line 54-60) — used
  correctly this session as `destruct e0 as [ w0 | | | y1' y2' | f2 args2 | c1 args2 ]` (note the
  three bare `|`s for `EBot`/`EFree`, which bind no variables at all).

**The general lesson**: before writing any `destruct`/`induction ... as [...]` pattern against an
inductive type you haven't just looked at, re-`grep`/re-read its actual `Inductive ...` declaration
first — never guess the order from intuition or from how it "reads naturally," since both bugs
above compiled far enough to produce a *confusing*, not an *obvious*, error (a warning about
unused introduction patterns, or an arity mismatch several tokens in) rather than an immediate,
easy-to-diagnose one.

## T16. Coq's top-to-bottom definition ordering, and physically relocating code

Coq requires every identifier to be *fully defined* (its `Proof ... Qed`/`Defined` block closed,
or its `Definition`/`Inductive` block finished) strictly *before* any later part of the file may
refer to it — there is no forward-declaration or mutual-recursion-across-arbitrary-distance
mechanism for ordinary `Lemma`/`Definition`s (mutual recursion needs `with`, declared together,
not this). This mattered concretely this session: when a new block of lemmas
(`NEval_left_echoice_shape` through `NEval_left_force_free_sound`, and later
`theorem2_G_CaseFwd_case`) was written and needed to call a *helper* (`NEval_left_frame_guarded`,
`NEval_left_force_free_sound` itself) that happened to be defined *later* in the file, `coqc`
failed with "The variable `X` was not found in the current environment." The fix in both cases
was not a code change at all, but a **physical relocation**: extracting the whole new block (as
literal file text, ~30-265 lines depending on the case) and re-inserting it bodily *after* the
dependency's own `Qed.`, using a short inline Python script to slice and splice the file text
(since the blocks were too large to move reliably by hand-editing). This is a genuinely different
kind of "fix" from anything else in this glossary — not a tactic change, a structural
reorganization of the file driven purely by Coq's linear processing order.

## T17. `induction H` (auto-IH per matching recursive premise) vs. calling an already-proven lemma on a derived sub-term (no auto-IH) — the crux of the well-founded-recursion discussion

This is less a single tactic and more the single most important *structural* fact about Coq
proofs that this session's later half turned on, so it's worth stating precisely as its own
glossary entry.

When you write `induction H as [pat1 | pat2 | ...]` for `H : R a1 ... an` (an inductive
relation), Coq builds, for *each* constructor `C` of `R`, a case whose available hypotheses
include not just `C`'s own premises, but — for every premise of `C` that is *itself* an instance
of the *same* relation `R` (matching the goal's own current motive) — an **automatically
generated induction hypothesis** for that premise, asserting the goal's own statement (with the
premise's own indices substituted in) already holds for it. This is what lets, e.g.,
`NEval_left_force_free_sound`'s `G_CaseFwd` case call `IH y0 brs0 eq_refl Gam HGam2 (x0::F) G1' x'
Hrec2` "for free" — `Hrec2`(really: the constructor's own recursive premise, here matching the
motive) is a literal, syntactic sub-term of the constructor being destructured, and Coq generates
its IH automatically as part of the `induction` tactic's own machinery.

This automatic-IH generation is **strictly tied to the recursive premise being a literal
constructor argument of the thing you're inducting on.** If, instead, you obtain a "smaller"
derivation *indirectly* — by calling some other, already-`Qed`'d lemma (e.g. `GEval_fun_shape`)
on a premise, which internally does its own `destruct`/pattern-match and *returns* an embedded
sub-derivation as part of its output — that returned sub-derivation is, from the *induction
tactic's* point of view, just some arbitrary term of the right type; it receives **no**
automatic induction hypothesis, no matter how "obviously smaller" it is semantically (and even if,
after full reduction, it would literally *compute to* the exact same sub-term the direct pattern
match would have given you). This is precisely why the `BCase`/`EFun`-recursion sub-cases of §9.5
are hard in a way `EVar`/`EChoice` (§9.2/§9.4) are not: those two sub-cases needed *no* IH at all
(the "`G_Var`/`G_Choice` make zero heap change" trick made the relevant fact provable outright,
with no recursion), while `BCase`/`EFun`-recursion genuinely need to apply "the same kind of
reasoning, one level deeper" to a derivation obtained via a helper lemma, for which no IH exists
under the current, narrowly-`BCase`-scoped induction.

Two ways to fix this, both discussed in §10/§12: (a) **well-founded recursion on an explicit size
measure** — define a `nat`-valued measure over `GEval` derivations, do strong induction on that
measure instead of structural `induction H`, and manually supply "this measure strictly
decreases" proofs at each recursive call site (rejected as disproportionately large for what it
would buy, and still needing separate "measure decreases across a helper-lemma call" lemmas for
every shape-extraction helper used); or (b) **generalize the theorem's own statement** to be
proved over arbitrary `e` (not just `BCase`-rooted `e`), so that the *previously-indirect* call
becomes, once again, a literal constructor-bound recursive premise of a *single*, larger
induction — recovering automatic IH generation "for free," which is the direction §12
(`theorem2_left`) pursues.

## T18. Miscellaneous smaller lemmas/tactics used as building blocks

- **`List.In_nth_error : forall (A : Type) (l : list A) (x : A), In x l -> exists n, nth_error l
  n = Some x`** — converts a `List.In` membership fact into a concrete index, needed whenever a
  proof has `In y1 ps` (a parameter is *some* member of the parameter list) but needs to relate
  it, positionally, to the matching argument at the *same* index in a parallel list (`args0`) via
  a `nth_error`-indexed hypothesis like `Hmatch : forall i x a, nth_error ps i = Some x ->
  nth_error args0 i = Some a -> s x = a`.
- **`nth_error_Some : nth_error l n <> None <-> n < length l`** and
  **`nth_error_None : nth_error l n = None <-> length l <= n`** (both from the standard `List`
  library) — used together to derive a contradiction when a proof needs to rule out
  `nth_error args0 i = None` given `nth_error ps i = Some y1` and `length ps = length args0`
  (i.e., `i` is in-bounds for `ps`, so by the length equality it must also be in-bounds for
  `args0`, so `nth_error args0 i` cannot be `None`).
- **`lia`** — the linear integer arithmetic decision procedure; used to close small numeric side
  goals (e.g. `i < length ps` combined with `length ps = length args0` implies `i < length
  args0`) that would otherwise need manual `Nat.lt_le_trans`-style lemma chaining.
- **`simpl`** — unfolds/reduces definitions (`Fixpoint`s, pattern matches on already-known
  constructors) one or more steps, used throughout to expose the underlying `if`/`match` so that
  a subsequent `rewrite`/`reflexivity`/`discriminate` has something concrete to work with (e.g.
  after `destruct e0 as [...]`, `simpl in H` on a hypothesis mentioning `rename_e0 s e0` reduces
  it down to the constructor-specific case).
- **`intros` (bare, and with explicit names)** — universally used to move hypotheses/quantifiers
  from the goal into the context; the file consistently uses fully explicit names
  (`intros P G x brs G' v H`) rather than the anonymous `intros.` form, for readability in a
  proof this size, and because many later tactics need to refer back to specific hypotheses by
  name.
- **`clear H`** — occasionally used to discard a hypothesis that's become stale/misleading (e.g.
  after rewriting `Hrec2g` to a more specific type, the original, now-redundant intermediate
  equation is sometimes cleared to keep the context legible for the remaining proof).

## T19. `rewrite <- H` rewrites EVERY matching occurrence, including ones hiding inside a larger
subterm — pin down which one with `at n`

**The problem it causes.** Given `Heq : f (f w) = f w` and a goal `w = f w`, the instinct is `rewrite
<- (Hst w)` (where `Hst w : tau (f w) = w`) to turn the goal into something `Heq`-shaped. But `rewrite <-`
finds *every* syntactic occurrence of the rewrite's target pattern in the current goal, not just the one
you had in mind — and `f w` (or here, bare `w`) often occurs more than once, including nested inside
another occurrence of itself (e.g. the `w` sitting inside `f w` on the other side of the equation). The
rewrite fires on all of them at once, producing a goal that no longer matches what the next line expects
— a `Found no subterm matching ... while it is expected to have type ...` error whose printed types look
close enough to right that the actual problem (which occurrence got rewritten) is easy to misdiagnose as
a different lemma-name/argument-order mistake instead.

**The fix.** Use `rewrite <- H at n` to target exactly the `n`-th occurrence (counted left-to-right in
the current goal), leaving the others alone. Concretely (`alpha_renaming_wip.v`,
`cyc_tau_cyc_sigma`/`cyc_sigma_cyc_tau`): to turn goal `w = sigma w` into `tau (sigma w) = sigma w`
(matching `Hst (sigma w)` after a further `Heq`-rewrite), `rewrite <- (Hst w) at 1` targets only the bare
`w` standing alone on the goal's left, not the `w` hiding inside `sigma w` on the right. Getting the
occurrence number wrong on the first attempt (and then chasing the resulting type-mismatch error as if it
were something else) cost two failed compile attempts in a row before landing on this — worth checking
`at n` immediately whenever a `rewrite <-` target could plausibly appear more than once in the goal,
rather than only reaching for it after a confusing error.

## T20. `List.In`'s definitional unfold order is `elem = query`, not `query = elem` — and stdlib
lemmas frequently mark the "obvious" positional argument implicit

**The `In` direction trap.** `In` is defined as `Fixpoint In a l := match l with nil => False | b::m =>
b = a \/ In a m end` — the EXISTING list element `b` is on the LEFT of the equation, the thing you searched
for (`a`) is on the RIGHT. So `simpl`-ing (or `destruct`-ing) a hypothesis `Hin : In start (nxt :: nil)`
produces `nxt = start \/ False`, not `start = nxt \/ False` — backwards from what the variable names'
left-to-right order in `In start [nxt]` suggests. Writing `eq_sym` reflexively (because "obviously" the
query should come first) silently flips a hypothesis that was ALREADY in the right shape, so
`Hne : nxt <> start` applied to an `eq_sym`'d version fails with a "term has type X while expected Y"
error that reads like an unrelated lemma-argument mistake, not a direction bug — cost real iteration in
`alpha_renaming_wip.v`'s `chase_invariant`/`component_invariant` (PIECE 2b) before being caught by just
reading the exact printed type of the hypothesis in the error rather than assuming the "natural" direction.
**The fix**: when a `False`-goal proof involving `In`-derived equalities won't typecheck, print/read the
actual hypothesis type first (`Set Printing All` if needed) rather than guessing which side `eq_sym`
belongs on.

**The implicit-index trap.** Several extremely common `List` lemmas mark what LOOKS like a positional,
obviously-explicit argument as implicit: `nth_error_app1`/`nth_error_app2` (`n`), `app_nth2` (`n`),
`Permutation_cons_append` (neither, but its arg ORDER is `l x`, i.e. list first — easy to guess backwards
as `x l`), `NoDup_cons` (`l`). `Check`ing one of these prints a clean-looking `forall (l l' : list A) (n :
nat), ...` that gives no visual hint of which binders are secretly `[bracketed]`/implicit — passing all of
them positionally (e.g. `nth_error_app1 l [v] i Hi`) then fails with a confusing "term has type nat while
it is expected to have type `?n < length l`"-style error (the tactic engine tried to unify your extra
explicit argument against the *proof* slot). **The fix**: use `About lemma_name` instead of `Check
lemma_name` before writing an explicit positional application — `About` prints the `Arguments ...`
line with real `[bracket]` annotations, or just `apply`/`rewrite` the bare lemma name and let unification
supply everything instead of guessing the positional call.

## T21. `destruct (compound_expr) eqn:H` rewrites *every* hypothesis mentioning that exact expression,
not just the goal — including a `forall`-quantified hypothesis whose STATEMENT contains it

**The problem it causes.** `destruct t eqn:H` on a bare variable `t` only ever affects the goal (and
whatever the goal depends on). But when `t` is a *compound* expression — e.g. `nth_error (component ps v0)
(length (component ps v0) - 1)` — and some OTHER hypothesis already in context happens to mention that
exact same expression (say `Hterm : forall x, nth_error (component ps v0) (length (component ps v0) - 1) =
Some x -> P x`, straight out of `component_invariant`'s own conclusion), the `destruct` rewrites that
occurrence too, turning `Hterm` into `forall x, Some xl = Some x -> P x` (`xl` being the freshly-introduced
witness) — silently, with no warning. Two concrete symptoms this produced (`alpha_renaming_wip.v`,
`component_backward_closed`, PIECE 2c): first, trying to route the extracted witness through a nested
`assert (Hex : exists xl, <the same compound expression> = Some xl) { destruct ... eqn:E; ... }` fails
*inside the assert itself*, because the assert's own stated goal contains that same compound expression,
which also gets rewritten to `Some xl = Some xl0` under the hood — `exact E` no longer matches. Second,
applying the (now-rewritten) `Hterm xl Hxl` fails with a "term has type X while expected Y" error that
looks like a completely unrelated argument-order mistake, because `Hxl`'s ordinary equation no longer
matches `Hterm`'s silently-mutated premise type.

**The fix.** Don't fight it — use it. Once you know `destruct ... eqn:` will rewrite a same-shaped
hypothesis's premise down to `Some xl = Some xl` (or `None = None`, in the other branch), that premise
becomes trivially dischargeable by `eq_refl` (or `reflexivity`) instead of the original named equation:
`destruct (Hterm xl eq_refl)` rather than `destruct (Hterm xl Hxl)`. Concretely: `destruct (nth_error l i)
as [xl | ] eqn:Hxl; [ | exfalso; apply Hnex; reflexivity]` — the `None` branch's `Hnex : nth_error l i <>
None` gets rewritten to `None <> None` by the very same mechanism, so `reflexivity` (not a fact about
`nth_error`) closes it. Avoid routing the extraction through a separate `assert`/`exists` wrapper whose own
stated goal repeats the exact compound expression — that just relocates the same rewrite collision one
level down, with a more confusing error site.
