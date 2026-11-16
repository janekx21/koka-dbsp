// aggregate.kk -- non-linear incremental operators: distinct and aggregates.
//
// A non-linear operator cannot map an input delta straight to an output delta. Each one
// keeps per-key state (the integral of its input, or an accumulator) and, for every key
// the delta touches, computes the output before and after and emits the difference.
// Keys the delta does not touch cost nothing.
//
// All of these are pure step functions: (state, delta) -> (new state, output delta).
// Rows with weight <= 0 count as absent for distinct, min/max and the group-existence
// rules of count/sum (see each operator).
module aggregate

import zset
import izset
import tmap

// ---------------------------------------------------------------------------
// distinct
// ---------------------------------------------------------------------------

// State: the integral of the input, as row -> weight (zero weights are removed).
// A row is present while its integral weight is > 0, and distinct emits +1 / -1 when
// that changes, so a weight moving between positive values emits nothing.
fun present(w : int) : int
  if w > 0 then 1 else 0

fun distinct-go( items : list<(a,int)>, t : tmap<a,int>, acc : list<(a,int)>
               , cmp : (a,a) -> order ) : (tmap<a,int>, list<(a,int)>)
  match items
    Nil -> (t, acc)
    Cons((row, dw), rest) ->
      val w0 = match tmap/lookup(t, row, cmp)
                 Nothing -> 0
                 Just(w) -> w
      val w1 = w0 + dw
      val t' = if w1 == 0 then tmap/delete(t, row, cmp) else tmap/insert(t, row, w1, cmp)
      val d  = present(w1) - present(w0)
      distinct-go(rest, t', (if d == 0 then acc else Cons((row, d), acc)), cmp)

pub fun distinct-step(st : tmap<a,int>, d : zset<a>, ?cmp : (a,a) -> order) : (tmap<a,int>, zset<a>)
  val (t, out) = distinct-go(d.items, st, Nil, cmp)
  (t, Zset(out.reverse))                 // rows come from a sorted delta, so already sorted

// ---------------------------------------------------------------------------
// The shared per-key update
// ---------------------------------------------------------------------------

// For every key in the delta (ascending): look up its old state, let `upd` compute the
// new state and the output rows that changed, and write the state back (Nothing removes
// the key). Returns the new state and the (unnormalised) output rows.
pub fun update-keys( st : tmap<k,s>, dix : izset<k,a>
                   , upd : (k, maybe<s>, zset<a>) -> (maybe<s>, list<(c,int)>)
                   , kcmp : (k,k) -> order ) : (tmap<k,s>, list<(c,int)>)
  fun visit(acc, key, dg)
    val (t, outs) = acc
    val (next, o) = upd(key, tmap/lookup(t, key, kcmp), dg)
    val t' = match next
               Nothing -> tmap/delete(t, key, kcmp)
               Just(s1) -> tmap/insert(t, key, s1, kcmp)
    (t', o ++ outs)
  tmap/fold(dix.by-key, (st, Nil), visit)

// Output rows that change when a group's aggregate goes from `before` to `after`:
// retract the old row, insert the new one, and emit nothing if the row is unchanged.
fun changes( k : k, before : maybe<v>, after : maybe<v>, out : (k,v) -> c
           , ccmp : (c,c) -> order ) : list<(c,int)>
  match before
    Nothing -> match after
      Nothing -> Nil
      Just(v) -> [(out(k, v), 1)]
    Just(v0) -> match after
      Nothing -> [(out(k, v0), -1)]
      Just(v1) ->
        val r0 = out(k, v0)
        val r1 = out(k, v1)
        if ccmp(r0, r1) == Eq then Nil else [(r0, -1), (r1, 1)]

// ---------------------------------------------------------------------------
// Accumulator aggregates (count, sum, ...): O(1) per row, no group storage
// ---------------------------------------------------------------------------

// An aggregate whose state can absorb a row with a weight, including a negative one
// (a retraction must exactly undo an insertion).
//   init    state of an empty group
//   add     absorb a row with its weight
//   finish  the group's value, or Nothing if the group is absent (emits no row)
//   zero    True when the state equals `init` in effect, so the key can be forgotten.
//           Do NOT report zero merely because the group is absent: a group with a negative
//           count still has to be remembered until its insertions arrive.
pub struct agg<a,s,v>(init : s, add : (s,a,int) -> s, finish : s -> maybe<v>, zero : s -> bool)

// Number of rows (sum of weights). The group exists while its count is > 0.
pub fun agg-count() : agg<a,int,int>
  Agg(0, fn(n, _row, w) n + w, fn(n) if n > 0 then Just(n) else Nothing, fn(n) n == 0)

// Sum of f(row) weighted by row weight. State is (count, total); the group exists
// while its count is > 0.
pub fun agg-sum(f : a -> int) : agg<a,(int,int),int>
  Agg((0, 0),
      fn(s, row, w) (s.fst + w, s.snd + w * f(row)),
      fn(s) if s.fst > 0 then Just(s.snd) else Nothing,
      fn(s) s.fst == 0 && s.snd == 0)

fun absorb(ag : agg<a,s,v>, s0 : s, items : list<(a,int)>) : s
  match items
    Nil -> s0
    Cons((row, w), rest) -> absorb(ag, (ag.add)(s0, row, w), rest)

// State: key -> accumulator. `out` builds the output row from a key and its value.
pub fun aggregate-step( st : tmap<k,s>, d : zset<a>, key : a -> k, ag : agg<a,s,v>
                      , out : (k,v) -> c, kcmp : (k,k) -> order, ccmp : (c,c) -> order )
                      : (tmap<k,s>, zset<c>)
  fun upd(k, old, dg)
    val s0 = match old
               Nothing -> ag.init
               Just(s) -> s
    val s1 = absorb(ag, s0, dg.items)
    val next = if (ag.zero)(s1) then Nothing else Just(s1)
    (next, changes(k, (ag.finish)(s0), (ag.finish)(s1), out, ccmp))
  val (st', outs) = update-keys(st, index-by(d, key, kcmp), upd, kcmp)
  (st', zset/from-list(outs, ccmp))

// ---------------------------------------------------------------------------
// Whole-group aggregates (min, max, anything of the entire group)
// ---------------------------------------------------------------------------

// The extreme row (by `rcmp`) among rows with positive weight; `want` is Lt for the
// minimum and Gt for the maximum.
fun extreme-pick(best : maybe<a>, p : (a,int), rcmp : (a,a) -> order, want : order) : maybe<a>
  if p.snd <= 0 then best
  else match best
    Nothing -> Just(p.fst)
    Just(b) -> if rcmp(p.fst, b) == want then Just(p.fst) else best

fun extreme(g : zset<a>, rcmp : (a,a) -> order, want : order) : maybe<a>
  g.items.foldl(Nothing, fn(best, p) extreme-pick(best, p, rcmp, want))

pub fun min-row(g : zset<a>, rcmp : (a,a) -> order) : maybe<a>
  extreme(g, rcmp, Lt)

pub fun max-row(g : zset<a>, rcmp : (a,a) -> order) : maybe<a>
  extreme(g, rcmp, Gt)

// State: the integral of the input, indexed by key. `f` computes the group's value from
// the group's whole Z-set (weights included), or Nothing if the group is absent.
// Cost per touched key is the size of that group.
pub fun aggregate-group-step( st : izset<k,a>, d : zset<a>, key : a -> k, f : zset<a> -> maybe<v>
                            , out : (k,v) -> c, acmp : (a,a) -> order
                            , kcmp : (k,k) -> order, ccmp : (c,c) -> order )
                            : (izset<k,a>, zset<c>)
  val dix = index-by(d, key, kcmp)
  fun visit(acc, k, dg)
    val g0 = izset/lookup(st, k, kcmp)
    val g1 = zset/plus(g0, dg, acmp)
    changes(k, f(g0), f(g1), out, ccmp) ++ acc
  val outs = tmap/fold(dix.by-key, Nil, visit)
  (add-delta(st, dix, acmp, kcmp), zset/from-list(outs, ccmp))


// What topk is
//
// It keeps the k best rows of each group under an ordering you choose, for example the 3 highest-scoring players per game, or the 10 most recent events per user. It’s SQL’s ORDER BY … LIMIT k applied per group, kept up to date incrementally.
//
// The output delta for a touched group is the difference between its old and new top-k: rows that entered the top-k get +1, and rows that dropped out get −1. Inserting a row that doesn’t make the cut produces no output. Deleting a top-k row promotes the next best row from outside the set, which is why the operator has to remember more than k rows per group.
//
// Why min/max don’t cover it
//
// aggregate-group-by can only emit one row per group (its function returns a single maybe<v>). min and max are the k = 1 case. For k > 1 the output is a set of rows, so it needs its own step function. topk could be written by hand on top of izset, but it’s tedious to get right with ties and weights, which is why I proposed building it once.
//
// Do you need it?
//
// It isn’t needed for the rest of the plan. Step 4 (a debug/inspection layer, if you want it) and step 5 (feedback loops and recursion, e.g. transitive closure) depend on distinct and join, which are done. topk is a convenience for ranking and “latest N” queries.
//
// My suggestion is to skip it for now and go to step 5, which is the part that makes this a real DBSP rather than a incremental-SQL engine. topk can be added later without touching anything else, since it only needs izset and the update-keys pattern already in place. Say if you’d rather have it first.
