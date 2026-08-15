# Dead Ends — consult before retrying an approach

This file catalogs approaches that were tried (or seriously investigated) and rejected,
across the whole `theorem2` effort, so we don't re-walk them. Two sources: (1) the project's
own history, recorded in `curry.v` comments, `failed_attempts.v`, and
`THEOREM2_PROCESS_NOTES.md`; (2) this session's own investigation (2026-08-03) into
`theorem2`'s `G_CaseFwd` case.

Convention: each entry says what was tried, why it fails, and where to look for the full
detail.

---

## Historical dead ends (pre-dating this session)

### H1. `CorrE_FwdChase` — a single, fully general "chase through a Fwd edge" constructor

```coq
(* the OLD, now-removed constructor *)
CorrE_FwdChase : G x = GFwd y -> CorrE G y b -> CorrE G x b   (* b arbitrary *)
```

Let a forwarding location's Nat-heap witness be *any* valid witness of its target, chased
transitively, with no restriction on `b`'s shape (raw in-progress content included, not just
achieved values). **Unsound**, via three independent counterexamples (all deleted from
`curry.v`, described in HISTORICAL NOTE comments there; live, `Qed`'d copies of two of them
survive in `curry_pre_blackhole_refactor.v`):

- **Counterexample A** (`HeapCorr_update_not_general`, `curry.v` ~1148-1176): a stale-copy
  witness breaks the moment the copied location's content later gets mutated (e.g. by
  `G_CaseFun`). Shows `HeapCorr` isn't preserved by an arbitrary graph mutation under this rule.
- **Counterexample B** (`NEval_confluence_unrestricted_is_false` / `blackhole_counterexample`,
  `curry.v` ~1295-1327, ~2632): `G x = GFwd y`, `G y = GExpr (EVar x)` (a raw, unforced
  self-referential alias). Two different `HeapCorr`-valid `Gam`s for the *same* graph have
  *different termination behavior* forcing `x` — one terminates immediately (self-loop), one
  diverges. This is what motivated the guard list `F` threaded through `NEval`/`NEval_left`
  (`N_VarExp`/`NL_VarExp`'s `~In z F` check) — the guard didn't exist before this counterexample.
- **Counterexample C** (the `fc_*` section, `curry.v` ~2841-2887, ~650 lines, deleted): genuine
  self-referential sharing (`let x = f(x) in ...`). Forcing `y` (which shares `x`'s raw content)
  can reach a different constructor than forcing `x` directly, because an escape route via one
  `Or`-choice requires re-entering `x` while `x` is already guarded. This is
  `NEval_fwd_transfer`'s fully general "chase, target needs further forcing" case being false.

**The fix** (still active): replace `CorrE_FwdChase` with two restricted constructors —
`CorrE_FwdHere` (direct one-hop alias only) and `CorrE_FwdAchievedCon` (skip-ahead only to an
*already-achieved* constructor, reached via `ContractLoc`, never to raw in-progress content).
See `THEOREM2_PROCESS_NOTES.md` §2.1 for the full writeup.

### H2. `ChainConsistent` / `HeapCorr2` — require an achieved witness to imply its Fwd target is also achieved

```coq
Definition ChainConsistent (G : Graph) (Gam : NHeap) : Prop :=
  forall x y, G x = Some (GFwd y) ->
    forall c args, Gam x = Some (BExpr (ECon c args)) -> Gam y = Some (BExpr (ECon c args)).
```

Built to rule out "`x`'s Nat-heap witness already achieved, `y`'s (x's immediate Fwd target)
still a lazy alias" — a combination that bare `HeapCorr`/`CorrE` allows declaratively (see
`failed_attempts.v` §3, `ex_x_ahead_of_y_reachable`, `Qed`'d concrete witness) but that "no real
execution would ever produce exactly this by forcing `x` itself" (quoting the file). Adding
`ChainConsistent` excludes it by definition.

**Superseded**: `ChainConsistent` turned out too strong. It can't represent *ordinary* multi-hop
memoization (discovered while proving `NEval_left_fwd_transfer_fwdhere_free`): ordinary
`Nat-VarExp` path-compression, forcing `x` through a genuine multi-hop chain `x -> y -> z`,
memoizes `x` directly to the achieved value at `z` — but per `ChainConsistent`, that would also
require `y` to already show the same achieved constructor, which the underlying `CorrE`
witnesses have no way to certify for a 2-or-more-hop skip. `HeapCorr2 = HeapCorr /\
ChainConsistent` was therefore judged too strong to survive as the *ambient* invariant of a
general induction over `GEval` (most branches go through a real multi-hop chase and can only
hand back the weaker `HeapCorr3`/`HeapCorr`, never `HeapCorr2`). See `failed_attempts.v` §4-5.

**IMPORTANT NUANCE (found this session, 2026-08-03, not fully resolved — see "Open question"
below):** it's not actually clear the "ordinary multi-hop path-compression" scenario that
motivated dropping `ChainConsistent` is itself *operationally reachable* either — see the
"this session" entries below.

### H3. `HeapCorr3`/`CorrE3` (current, active) — the replacement

```coq
Definition CorrE3 (G : Graph) (Gam : NHeap) (x : var) (b : Blk) : Prop :=
  CorrE G x b \/
  (exists y0 z c args, G x = Some (GFwd y0) /\ ContractLoc G y0 z /\
     G z = Some (GExpr (ECon c args)) /\ VarChase Gam x (BExpr (ECon c args))).
```

Not itself a dead end — this is the live, current definition (`HeapCorr` in
`curry_test_leftmost.v`, renamed from `HeapCorr3`). Drops `ChainConsistent`'s ordering
requirement entirely; accepts a Nat-heap witness `x` that's achieved via an *arbitrary-length*
graph-side `ContractLoc` chase, backed by a Nat-heap-side `VarChase` alias-hop-chain to the same
value. See its own comment block in `curry_test_leftmost.v` (~2177) for the corrected rationale
— **and note its comment explicitly documents H3a below**.

### H3a. Requiring the immediate Fwd target to *also* `VarChase`-agree (a stronger `CorrE3`)

An earlier version of `CorrE3`'s disjunct required the Fwd target `y0`'s *own* Nat-heap value to
*also* chase to the same terminal constructor (not just `x`'s). Documented directly in the
comment above `CorrE3`'s current definition (`curry_test_leftmost.v` ~2182-2186) as
**"unnecessary, and wrong whenever the graph-level chain from that immediate target is itself
more than one hop... a real multi-hop chain is completely ordinary, not a corner case."**

**This session (2026-08-03) independently re-derived and re-proposed this exact strengthening**
while trying to close `theorem2`'s `G_CaseFwd` case, before finding this pre-existing comment.
Do not propose it again without addressing the objection above head-on (see "Open question").

### H4. Generalizing `force_var`/`force_var_N` from "chases to a constructor" to "chases to a
constructor OR a genuine free-variable self-loop"

Would have added a `CorrE_FwdAchievedFree`-style skip-ahead constructor/lemma family
(`ContractLocN_to_CorrE_gen`, `DirectAchievable`, `force_var_gen_N`, `force_var_gen` — all
deleted from `curry.v`, see the comment at ~904-922). **Unsound**: `Con` is permanent once
written to the graph, but `Free` is *not* — `G_CaseConFree` narrows a free location to a
constructor later. A location multiple hops from a free `y`, memoized skip-ahead to `EVar y`,
would go stale the moment `y` gets narrowed to a constructor. (`CorrE_FwdAchievedFree` itself was
removed for the identical reason, per the comment just above `CorrE`'s definition.)

### H5. `force_var2_left` — chasing through a raw, un-mutated `EChoice` node with `G` held fixed

Discovered while trying to build this on top of `ContractLoc2N`/`CorrE_con_progress_N2`
(`curry_test_leftmost.v` ~4868-4884, kept as "honest, self-contained... graph theory" but marked
explicitly non-useful). **Unsound relative to `HeapCorr2`** (and the same reasoning applies to
`HeapCorr`/`CorrE3`): unlike a Fwd-to-Con chase, `Con` is a terminal/permanent graph shape, but a
raw `EChoice` node is *not* — it only becomes "resolved" via an explicit `G_CaseChoice` mutation
(turning it into a `GFwd`), a graph-level event. `NL_Or`'s eager Nat-heap resolution of a choice
can't be retroactively justified against a graph that never performed that mutation.

### H6. "Forbid `let x = y in ...` (bare-variable let-RHS)" as a way to prevent *all* Nat-heap
aliasing / simplify away `CorrE3`'s multi-valued complexity entirely

Investigated in `curry_test_remove_aliasing.v` (file since deleted; findings preserved in
`THEOREM2_PROCESS_NOTES.md` §13.2, "Idea 2", Part 1). **Shown false** by a concrete witness
program:

```
idf(a) = a
main   = let y = free in
         let x = idf(y) in
         x
```

Forcing `x` unfolds `idf` (parameter passing is "by reference" — `a` is renamed directly onto
`y`'s own location), which forces `y` (a free self-loop) and returns `EVar y`; `Nat-VarExp`
memoizes `x` to `EVar 0` — a genuine Nat-heap *alias*, even though the source text never wrote a
bare-variable let anywhere. Aliasing is dynamically re-created by the semantics themselves
(the Nat-heap mirror of the graph's own `G_Var`/`GFwd` construction), not merely a syntactic
copy-propagation artifact a compiler pass could pre-empt.

**IMPORTANT — this is NOT the same claim as this session's `NoAliasLetB`/`NoVarThunk` work.**
`NoAliasLetB` only claims the *graph* never holds a bare `GExpr (EVar z)` node ("var-thunk") —
it does NOT claim, and was never used to claim, that the *Nat-heap* (`Gam`) never holds an
alias `EVar y`. Nat-heap aliasing (`Gam x = EVar y`, matching a real `GFwd` edge) is completely
normal and is exactly what `CorrE_FwdHere`/`CorrE3` are built to represent. In the `idf(y)`
example above, `x`'s *graph* content after being cased is `GFwd y` (via `G_Var`'s always-`GFwd`
semantics + `G_CaseFun`'s memoization) — never `GExpr (EVar y)` — so `NoVarThunk` is not violated
by this example. These are genuinely different invariants; do not conflate the two if this
comes up again.

### H7. Launchbury-style heap-removal ("black hole via `None`") vs. the guard-list mechanism

Investigated in the same `curry_test_remove_aliasing.v` (§13.2, "Idea 1", Parts 2-4): replace
threading a guard list `F` through every rule with *removing* `x`'s binding from the heap while
evaluating its content (re-entrant force shows up as `G x = None` instead of a guard-list
check). **Not a genuine simplification**: proved equivalent in expressiveness to the guard-list
mechanism (same black-hole policing, different bookkeeping), modulo one unformalized
global-freshness care point. Section 3 confirms the graph-representation confluence
counterexample (H1's Counterexample B) is equally stuck under this rule too. Neither this nor H6
supplies the actual missing ingredient (see H8).

### H8. General `NEval`/`NEval_left` confluence ("replaying a derivation over a heap where
someone else's slot has *also* been independently updated reaches the same result")

`THEOREM2_PROCESS_NOTES.md` §13.2 Part 5's own conclusion: the actually-missing ingredient for
closing the `NEval_fwd_transfer`-style transfer axioms is a **graph-level
acyclicity/non-interference fact** — "nothing reachable from `y`'s own graph definition is, or
forwards to, `x`" — needed to show replaying `y`'s forcing derivation under a heap where `x`'s
slot has *also* been updated still reaches the same result. This is a statement about
`GEval`/`CorrE`'s aliasing structure, not about Nat-heap bookkeeping, so neither H6 nor H7
touches it.

A **narrow, provable special case** of this does exist and is actively used:
`NEval_left_shortcut_alias`/`_relax` (`curry_test_leftmost.v` ~1259, ~1456) — pre-installing (or
removing) a memo for a variable `x` whose *entire* remaining behavior is "read once, return a
value" (not itself needing further recursive forcing) is safe, because it doesn't touch the
acyclicity issue at all. See `curry.v` ~1904-1917 for the exact scope note: *"this update can
never uncover the FwdChase-into-a-cycle pathology, because y's content is required to ALREADY be
terminal, not itself an unresolved alias."* **General confluence beyond this narrow case remains
open** — see this session's entries below, which hit exactly this wall from a different angle.

---

## This session's dead ends (2026-08-03, investigating `theorem2`'s `G_CaseFwd` case)

Context: `theorem2`'s `G_CaseFwd` branch (`G0 x0 = GFwd y0`) needs to turn IH's result for `y0`
(a full `BCase y0 brs0` derivation reaching `Con c args`) into one for `x0`. This hits a case
where `x0`'s Nat-heap witness is *already* achieved to a constructor via `CorrE3`'s skip-ahead
disjunct while `y0` (x0's immediate Fwd target) has not itself been forced/memoized — see the
"Where we are" note below for the full writeup of this specific gap.

### S1. Re-deriving H3a independently (see above)

Proposed strengthening `CorrE3`'s skip-ahead disjunct to also require
`VarChase Gam y0 (Con c args)` for the immediate Fwd target `y0`. Re-discovered the exact
objection already recorded in the code comment (H3a) *after* proposing it: this breaks ordinary
multi-hop path-compression the same way `ChainConsistent` did. **Do not retry without first
resolving the "Open question" below** (specifically: is the "ordinary path-compression" scenario
this exclusion would break actually operationally reachable, or is *it* also a dead end in the
same way `ex_x_ahead_of_y_reachable`, H2, was?).

### S2. `NEval_left` determinism / "memoization transparency" lemma

Attempted to sidestep S1 by proving: if a case-body derivation reads `y0`'s memoized value (from
IH's own construction, which forced `y0` fully), the *same* case body should be independently
re-derivable from the original, unmemoized `Gam`, reaching the same result — relying on
`NEval_left` being deterministic. This requires **guard-weakening**: the sub-derivation for
`y0`'s own content was proven under one specific guard (e.g. `y0::nil`), but the splice point
inside the case body's own recursive unfolding is under a *different* (possibly larger) guard,
and there's no general "guard doesn't matter" lemma for `NEval_left` — the guard exists
specifically to block self-referential re-forcing (see H1 Counterexample B / the guard's own
origin), so weakening it arbitrarily risks reintroducing exactly the loop it prevents. Would
need an additional **independence argument** (the two computations never force the same
variable) not currently available. This is the *same* wall as H8 (general confluence beyond the
narrow already-terminal case is genuinely open), approached from a different direction —
confirms H8's "remains open" status rather than resolving it.

### S3. "x ahead of y" reachability (RESOLVED — confirmed operationally unreachable)

Built a toy Curry-level example (`x0 -> GFwd y0 -> GFwd y1 -> Con "C"`, case body literally
`EVar y0`) to test whether "`x0` achieved, `y0` dangling" is reachable. In every operational
trace attempted, forcing `x0` through `NL_VarExp` recursively *also* memoizes `y0` (and every
other intermediate hop) as a byproduct of the very same recursive step — `NL_VarExp`'s own
memoization fires at *every* level of its own recursion, not just the outermost. Could not
construct a real forcing trace where an intermediate hop is skipped.

**Resolution (from the user):** every `GFwd` edge is created by a case-forcing step
(`G_CaseFun`/`G_CaseChoice`/`G_CaseConFree`), which is *itself* triggered only by `NL_Select`/
`NL_Guess` forcing the cased variable first — so the moment `G x` becomes `GFwd y`, `Gam x`
becomes `EVar y` in lockstep. The *only* way `Gam x` can later diverge from `EVar y` is by
forcing `EVar x` again, which (via `NL_VarExp`'s recursive structure) necessarily forces `y` too,
all the way down the chain. So "x ahead of y" — the scenario `ChainConsistent` was built to
exclude — genuinely cannot arise from a real execution. `ChainConsistent`'s rejection (H2) was
therefore a **proof-engineering setback** (couldn't show it was preserved through the old
induction, likely for want of `NoVarThunk`/`NoAliasLetB`, which didn't exist yet), not a
soundness problem with the invariant itself. **Action taken:** revived `ChainConsistent` as a
second invariant threaded through `theorem2` (`ChainConsistent_extend` added for `G_Let`,
mirroring the old `HeapCorr2_extend`'s own use of `WellFoundedFwd`). This compiles cleanly
through `G_Bot`..`G_Let`.

### S4. `HeapCorr_fwd_dichotomy` — NOT a dead end after all; the lemma as stated is simply FALSE (corrected 2026-08-04)

Attempted: "given `G0 x0 = GFwd y0`, `Gam x0` is either `EVar y0` exactly or already achieved to
*some* constructor" — as a single, standalone lemma, to let `G_CaseFwd`'s construction pick
between a `fwdhere_con`-style port (alias case) and a `ChainConsistent`-based argument (achieved
case). **Failed to compile.**

**Original (WRONG) diagnosis:** attributed the failure to a proof-engineering gap — "nothing ties
the skip-ahead witness's alias target to `y0`" — and treated it as a wall requiring either a
`CorrE3` change or abandoning the approach.

**Corrected diagnosis (2026-08-04, prompted by direct user pushback on this framing):** the lemma
is **semantically false**, not merely hard to prove. There is a genuine third case for `Gam x0`
beyond "alias to `y0` exactly" or "achieved directly": `Gam x0 = EVar w` for `w <> y0`. Concrete
mechanism: `y0`'s own chain forwards further to a currently-*free* location `w` (not yet narrowed
to a constructor); forcing `x0` at that point recurses all the way through `y0` to `w` and
memoizes `x0` **directly** to `EVar w`, skipping `y0` (ordinary multi-hop path compression, same
phenomenon already accepted for constructors, just landing on a free self-loop instead of a `Con`).
If `w` is *later*, independently, narrowed by a `Guess` elsewhere in the program, the graph now
shows `y0`'s chain reaching an achieved constructor while `Gam x0` still shows the stale `EVar w`
— exactly `CorrE3`'s disjunct 2's shape, with `b = EVar w` (not `Con`). **This is not hypothetical
— it is exactly the shape already used, `b = EVar x'`, in the existing `Qed`'d proof of
`NEval_left_fwd_transfer_fwdhere_free`** (`curry_test_leftmost.v` ~3134-3145, `right. exists y,
wit, c1, ws. ...`). Since `theorem2` quantifies over an *arbitrary* `Gam` satisfying `HeapCorr`,
this third case must be handled, not excluded — so the two-way dichotomy was wrong to attempt.
**Lemma correctly removed from the file** (it should never be re-added in this form).

**Good news:** S6's plan (below) never actually needed this dichotomy — it calls `force_var`
directly on `x0`, which already handles *any* shape `Gam x0` has (including this third case) via
its existing disjunct-2 dispatch. So S6 survives this correction untouched.

### S5. Investigating whether `CorrE3`'s skip-ahead disjunct (disjunct 2) is needed at all — CORRECTED, it IS needed

**Original finding (WRONG in its conclusion):** traced `force_var_N`'s own proof and observed
`HeapCorr_update_achieved` only ever *writes* an achieved witness via disjunct 1
(`CorrE_FwdAchievedCon`), never disjunct 2, and speculated disjunct 2 might be operationally dead.

**Corrected (2026-08-04):** this observation is true as far as it goes (nothing in *this file*
ever *writes* a Gam using disjunct 2's own certificate directly) but the conclusion drawn from it
was wrong. Disjunct 2 is genuinely load-bearing — it is exactly what's needed to justify a Gam
witness of the shape `b = EVar w` (an alias, not an achieved value) whenever `w` is NOT x's own
immediate graph-level Fwd target. S4's corrected entry (above) gives the concrete mechanism (a
free variable reached via multi-hop compression, later independently narrowed elsewhere), and
`NEval_left_fwd_transfer_fwdhere_free` (`curry_test_leftmost.v` ~2768-3158, `Qed`'d) is a REAL,
already-proven case that constructs exactly this shape via disjunct 2 (see lines 3134-3145: `right.
exists y, wit, c1, ws. ...`, with `b = EVar x'` — an alias, not an achieved constructor). So
disjunct 2 is not "operationally redundant, formally load-bearing only for exhaustiveness" as
previously claimed — it does real, necessary work, specifically for the free-variable/`NL_Guess`
pathway. **Do not propose removing `CorrE3`'s disjunct 2 or collapsing `HeapCorr` back to
`HeapCorr2`** — this was tried in spirit before (`ChainConsistent`/`HeapCorr2`, H2) and separately
reconsidered and rejected again here; both times for the same underlying reason (multi-hop
compression producing states plain `CorrE` cannot represent), just discovered via different
routes (H2 via the direct-achievement case, this entry via the free-then-narrowed case).

### S6. Cleaner `G_CaseFwd` construction plan — still valid after S4/S5's correction

Call `force_var` directly on `x0` (it already internally handles whichever `CorrE3` disjunct
justifies `Gam x0`, via the same machinery used in `force_var_N`'s disjunct-2 branch) to get
`Gam_fx0` with `x0` forced. Then, instead of trying to relate `Gam_fx0` back to `HNEy`'s own
(independently-built, over the *original* `Gam`) heap, **re-apply `theorem2`'s own IH a second
time, directly to `Gam_fx0`**, with the *same* `Hcorr` (a fact about `G1`/`v1` only, independent
of any `Gam`). This produces a *fresh* `HNEy'` over `Gam_fx0` rather than reusing the original
`HNEy`. If `ChainConsistent G0 Gam_fx0` holds (`Gam_fx0 x0` is achieved by construction, so
`ChainConsistent` applied at `(x0, y0)` gives `Gam_fx0 y0` the same achieved value directly),
`HNEy'`'s own internal "force `y0`" step is forced to be the trivial `NL_VarCons` case (no
alias-chasing needed), meaning its heap is unchanged — so `HNEy'`'s case-body sub-derivation
*already* runs from `Gam_fx0` exactly, which is *exactly* the heap `force_var`'s own forcing of
`x0` produces. `NL_Select` then assembles directly: `force_var`'s own result as the
scrutinee-forcing premise, `HNEy'`'s extracted branch-match and case-body sub-derivation as the
rest. No transplant lemma needed at all. **This plan does NOT depend on S4's false dichotomy at
all** — it works regardless of which of the (now three known) shapes `Gam x0` originally had,
because `force_var` already dispatches all of them correctly before this plan's own reasoning
even starts.

**Prerequisite:** `force_var`/`force_var_N` (and their dependencies `HeapCorr_update_achieved`,
`VarChaseN_to_NEval_left`) need to be extended to *also* establish `ChainConsistent G0 Gam_fx0`
in their output, not just `HeapCorr`.

### S7. Extending `ChainConsistent` through `force_var_N`'s machinery — disjunct 1 done, disjunct 2 in progress

**`ChainConsistent_update_achieved` (new lemma, `Qed`, added next to `HeapCorr_update_achieved`):**
promoting `x` from its lazy alias `EVar y0` to the achieved constructor preserves
`ChainConsistent`, *provided* `y0` is already achieved to the *same* value first (`Gam y0 = Con c
args`, established before the call) *and* `x`'s own prior witness was exactly `EVar y0` (not yet
`Con`-shaped — this is what rules out the one dangerous case, some other already-achieved `p`
forwarding into `x`: original `ChainConsistent` would already force `p`'s target to be `Con`-shaped
too, contradicting `Gam x = EVar y0`). This slots cleanly into `force_var_N`'s existing **disjunct
1** branch: both extra hypotheses (`Gam x = EVar y0`, `Gam y0 = Con c args`) are already
established there (`Hb`, and `Hgamy0` via `NEval_left_own_slot`) for unrelated reasons. **Disjunct
1 is fully extended and compiles.**

**Disjunct 2 (hand-off to `VarChaseN_to_NEval_left`) is a genuinely different, harder problem —
NOT the same wall as S4 (S4 was a false lemma; this is a real, open proof obligation).**
`VarChaseN_to_NEval_left`'s own chase is purely Nat-heap-based (`VarChaseN`'s hop case only ever
requires `Gam w = EVar w'`, no graph fact at all) — so at an intermediate hop, there may be NO
graph edge `G w = GFwd w'` matching the alias at all (this is precisely disjunct 2's whole point,
confirmed load-bearing by S5's correction). `ChainConsistent_update_achieved` cannot be invoked at
such a hop because its own hypothesis requires a real `G x = GFwd y0` matching the alias target.
**Establishing `ChainConsistent` for `VarChaseN_to_NEval_left`'s output therefore needs a
different argument than the one that worked for disjunct 1** — likely checking `ChainConsistent`
directly against `VarChaseN_to_NEval_left`'s own final output pointwise (for every `p` with `G p =
GFwd q`, if the update touches `p`, does its target `q` correctly show `Con` too), rather than
trying to reuse `ChainConsistent_update_achieved` at each intermediate hop.

### S8. "Fold reconciliation into `theorem2`'s own induction" (third conjunct) — investigated, rejected

Idea: add a third conjunct to `theorem2`'s statement — "for any `q` reaching `e`'s scrutinee via a
`GFwd`-chain (not just directly), the `BCase q brs` conclusion also holds" — proven together with
the other two conjuncts by the same induction, so `G_CaseFwd`'s own case could invoke `IH`'s third
conjunct directly instead of needing external reconciliation machinery.

**Works cleanly for `G_CaseFwd` itself** — composing one more `GFwd` hop onto whatever chain the
goal already carries, then handing off to `IH`'s own third conjunct, needs no reconciliation at
all (this was the case that motivated the idea).

**Does NOT work for the other five `G_CaseXXX` cases** (`CaseFun`, `CaseChoice`, `CaseCon`,
`CaseConFree`, trivially `CaseBot`). Their recursive premises aren't themselves `BCase`-evaluations
of the same scrutinee (they evaluate a function call, a renamed branch body, etc.), so the third
conjunct has no recursive premise to compose onto — it needs to force `q` itself and reconcile that
with `x`'s own sub-computation, which is *exactly* the same "does `q`'s Nat-heap alias structure
mirror the graph" reconciliation problem from `G_CaseFwd`, just relocated to five more cases. Not
avoidable by scoping the conjunct to only `G_CaseFwd`-shaped `e`, either: a `G_CaseFwd` chain can
legitimately terminate in any of the other five cases, so the third conjunct must hold for those
`e`-shapes too. **Net effect: makes the problem bigger (six cases needing reconciliation instead of
one), not smaller.** Do not retry this framing.

### S9. General `NEval_left` confluence/transport lemma — investigated, hits the SAME wall as S7/S8, in a new guise

**Historical context (important — checked directly, not assumed):** a confluence-style tool for
`NEval` (not `NEval_left`) was attempted in `curry.v`, predating `NEval_left`'s creation, and hit a
genuine wall — three `Admitted` "transfer axioms" (`NEval_fwd_transfer`, `NEval_choice_transfer`,
`NEval_fun_transfer`) all reduced to *"`NEval` eagerly memoizes, so completing a case on `x` by
replaying `y`'s sub-derivation needs 'evaluation is invariant under varying a heap slot to another
valid representation' — a genuine confluence/determinism-up-to-representation theorem for `NEval`
that was never built"* (`THEOREM2_PROCESS_NOTES.md`). `NEval_left` itself was created specifically
in response to this, and `curry_test_leftmost.v`'s own opening comment states the hope explicitly:
*"Removing Or's nondeterminism should remove that entire attack surface... turning the missing
'NEval soundness relative to G' non-interference fact into an ordinary confluence-under-replay
argument."* **That hope was never followed through** — no standalone `NEval_left` confluence lemma
exists anywhere in the file. The project instead pivoted to `NEval_left_force_free_sound` (built by
structural induction on `GEval` directly, sidestepping general confluence for most cases via
"generalize the guard `F`"), but its own comment admits its `G_CaseFun` case for a structurally
identical reason: `NL_Fun`'s recursive premise "fully resolves the renamed function body in ONE
Nat-heap step, whereas the graph's own `G_CaseFun` only shallowly resolves it... before recursing
at the CASE level for possibly many more steps" — marked "not yet built" there too.

**This session's attempt (2026-08-11):** defined
```coq
Definition GamCompatible (Gam1 Gam2 : NHeap) : Prop :=
  forall p, Gam1 p = Gam2 p \/
    (exists c args, VarChase Gam1 p (BExpr (ECon c args)) /\ VarChase Gam2 p (BExpr (ECon c args))).
```
(two Nat-heaps are compatible pointwise if they agree outright, or both `VarChase` to the same
achieved value — i.e. "two different amounts of alias-compression of the same underlying graph
state"), and attempted:
```coq
Lemma NEval_left_transport :
  forall P G0, NoVarThunk G0 ->
  forall F Gam1 e Gam1' v, NEval_left P F Gam1 e Gam1' v ->
  forall Gam2, HeapCorr G0 Gam1 -> HeapCorr G0 Gam2 -> GamCompatible Gam1 Gam2 ->
  (forall p, In p F -> Gam1 p = Gam2 p) ->
  exists Gam2', NEval_left P F Gam2 e Gam2' v /\ HeapCorr G0 Gam2' /\ GamCompatible Gam1' Gam2'.
```
proven by induction directly on the given `NEval_left` derivation (not on two independently-built
derivations — this sidesteps the alpha-renaming worry from S2/earlier: `NL_Fun`'s freshness
requirement `Gam (s y) = None` transfers automatically whenever `Gam1 (s y) = None`, since
`GamCompatible`'s second disjunct requires `Gam1 p = Some _` as `VarChase`'s own base case, so
`Gam1 p = None` forces the FIRST disjunct, `Gam2 p = None` too — no fresh re-choice of `s` is ever
needed, since we're transporting the SAME, already-built derivation, not comparing two new ones).
`NL_VarCons`'s "agree" branch closed cleanly.

**Where it broke: `NL_VarCons`'s (and `NL_VarExp`'s) "disagree, `VarChase`-reconciled" branch.**
Splicing in a fresh reconstruction (via `VarChaseN_to_NEval_left`) for the disagreeing location
needs that lemma's own guard-disjointness hypothesis (`forall p, In p F -> exists nz, VarChaseN
Gam2 nz p (Con c args) /\ n < nz`) to hold for the CURRENT guard `F`. The simple invariant `forall
p, In p F -> Gam1 p = Gam2 p` does NOT imply this: an `F`-member `p` could itself be a live alias
(`Gam1 p = Gam2 p = EVar q`) whose OWN further chase (through `q`) diverges between `Gam1`/`Gam2`
even though `p` itself agrees — and nothing rules out `q` coinciding with the very location being
spliced for. Tried strengthening the invariant twice (a) "F-members never `VarChase` to anything
achieved via `Gam2`" — fails immediately, since exactly the location being pushed onto the guard
(`z` itself, mid-`NL_VarExp`) is allowed to be `VarChase`-achieved via `Gam2` in the scenario we
care about, so the invariant can't even survive the step that creates it; (b) tried to argue the
required disjointness follows from program-level scoping/freshness — this would need a global
freshness invariant `theorem2` doesn't currently have (`var = nat` is a flat, unrestricted
namespace shared between "source variables" and "runtime-chosen locations").

**Conclusion: this is the SAME wall as S7 (force_var_N's own disjunct-2 guard tracking) and S8
(the abandoned third-conjunct idea), now hit a third time, from the "general confluence" angle.**
Three independent framings (extend `ChainConsistent` through `VarChaseN_to_NEval_left`; fold
reconciliation into `theorem2`'s own induction; build a general `NEval_left` transport/confluence
lemma) all bottom out at needing the SAME missing ingredient: a guard/freshness-disjointness fact
relating an externally-introduced location's alias chain to whatever guard is already in scope at
the point it gets spliced in. This strongly suggests the missing ingredient is real and load-bearing
— not an artifact of any one proof strategy — and future attempts should expect to need it too,
however the reconciliation is framed. **Scaffolding for this attempt was reverted (not kept in the
file — it was all `admit`, no genuine partial progress beyond the first case).**
