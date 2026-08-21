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
