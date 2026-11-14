// circuit.kk -- incremental circuits over Z-sets.
//
// Two layers:
//
//  1. Pure step functions:   (state, input delta) -> (new state, output delta)
//     These are the mathematics of incremental computation. No heap, no effects;
//     they can be tested directly.
//
//  2. A circuit: a list of nodes that each wrap one step function together with
//     its state (kept in a heap reference). A node reads the output slots of its
//     input streams and writes its own output slot. Nodes are appended in
//     creation order, and a node can only refer to streams that already exist,
//     so creation order is a valid topological order. The scheduler is therefore
//     just "run every node once, in order" per step.
module circuit

import std/core/undiv
import zset

// ---------------------------------------------------------------------------
// Layer 1: pure step functions
// ---------------------------------------------------------------------------

// I: running total of the input deltas. State and output are the same value.
pub fun integrate-step(acc : zset<a>, d : zset<a>, ?cmp : (a,a) -> order) : (zset<a>, zset<a>)
  val next = zset/plus(acc, d, cmp)
  (next, next)

// D: turn a stream of snapshots into a stream of changes. State is the previous snapshot.
pub fun differentiate-step(prev : zset<a>, cur : zset<a>, ?cmp : (a,a) -> order) : (zset<a>, zset<a>)
  (cur, zset/minus(cur, prev, cmp))

// Join is bilinear, so with ia, ib = integrals of everything seen so far:
//   d(a join b) = da join ib  +  ia join db  +  da join db
pub struct join-state<a,b>(ia : zset<a>, ib : zset<b>)

pub fun join-state()
  Join-state(zset/empty(), zset/empty())

pub fun join-step( st : join-state<a,b>, da : zset<a>, db : zset<b>
                 , ka : a -> k, kb : b -> k, f : (a,b) -> c
                 , acmp : (a,a) -> order, bcmp : (b,b) -> order
                 , kcmp : (k,k) -> order, ccmp : (c,c) -> order )
                 : (join-state<a,b>, zset<c>)
  val j = fn(x, y) zset/join(x, y, ka, kb, kcmp, f, ccmp)
  val out = zset/plus(zset/plus(j(da, st.ib), j(st.ia, db), ccmp), j(da, db), ccmp)
  (Join-state(zset/plus(st.ia, da, acmp), zset/plus(st.ib, db, bcmp)), out)

// ---------------------------------------------------------------------------
// Layer 2: circuits
// ---------------------------------------------------------------------------

// All mutable state lives in heap `h`, so a circuit cannot escape `run`.
pub struct circuit<h>
  nodes : ref<h, list<() -> st<h> ()>>      // newest first

// A stream is the output slot of a node: the delta produced during the current step.
pub struct stream<h,a>
  circ : circuit<h>
  out  : ref<h, zset<a>>

// Where the outside world pushes deltas for the next step.
pub struct input-handle<h,a>
  pending : ref<h, zset<a>>

pub fun circuit() : alloc<h> circuit<h>
  Circuit(ref(Nil))

// Heap read with `div` discharged. Koka adds `div` to any read of a reference whose
// contents might mention the same heap (it could hold a self-referential closure).
// The only closures this module stores in the heap are the nodes below, and none of
// them refer to themselves, so reads are safe.
fun get(r : ref<h,a>) : read<h> a
  pretend-no-div(fn() !r)

fun add-node(c : circuit<h>, node : () -> st<h> ()) : st<h> ()
  val ns = c.nodes
  ns := Cons(node, get(ns))

// -- inputs and outputs ------------------------------------------------------

pub fun input(c : circuit<h>) : st<h> (stream<h,a>, input-handle<h,a>)
  val pending = ref(zset/empty())
  val out     = ref(zset/empty())
  fun node()
    out := get(pending)
    pending := zset/empty()
  c.add-node(node)
  (Stream(c, out), Input-handle(pending))

// Several pushes before the next step are added together.
pub fun push(h : input-handle<h,a>, delta : zset<a>, ?cmp : (a,a) -> order) : st<h> ()
  val p = h.pending
  p := zset/plus(get(p), delta, cmp)

// The delta this stream carried in the most recent step.
pub fun read(s : stream<h,a>) : read<h> zset<a>
  get(s.out)

// -- generic node constructors -----------------------------------------------

fun add-unary( s : stream<h,a>, init : t, step : (t, zset<a>) -> (t, zset<b>) ) : st<h> stream<h,b>
  val state = ref(init)
  val slot  = ref(zset/empty())
  fun node()
    val (state', o) = step(get(state), get(s.out))
    state := state'
    slot := o
  s.circ.add-node(node)
  Stream(s.circ, slot)

fun add-binary( l : stream<h,a>, r : stream<h,b>, init : t
              , step : (t, zset<a>, zset<b>) -> (t, zset<c>) ) : st<h> stream<h,c>
  val state = ref(init)
  val slot  = ref(zset/empty())
  fun node()
    val (state', o) = step(get(state), get(l.out), get(r.out))
    state := state'
    slot := o
  l.circ.add-node(node)
  Stream(l.circ, slot)

// -- operators ---------------------------------------------------------------
// Linear operators are stateless: applying them to a delta gives the output delta.

pub fun map(s : stream<h,a>, f : a -> b, ?cmp : (b,b) -> order) : st<h> stream<h,b>
  s.add-unary((), fn(u, d) (u, zset/map(d, f, cmp)))

pub fun filter(s : stream<h,a>, pred : a -> bool) : st<h> stream<h,a>
  s.add-unary((), fn(u, d) (u, zset/filter(d, pred)))

pub fun plus(l : stream<h,a>, r : stream<h,a>, ?cmp : (a,a) -> order) : st<h> stream<h,a>
  l.add-binary(r, (), fn(u, dl, dr) (u, zset/plus(dl, dr, cmp)))

pub fun minus(l : stream<h,a>, r : stream<h,a>, ?cmp : (a,a) -> order) : st<h> stream<h,a>
  l.add-binary(r, (), fn(u, dl, dr) (u, zset/minus(dl, dr, cmp)))

pub fun integrate(s : stream<h,a>, ?cmp : (a,a) -> order) : st<h> stream<h,a>
  s.add-unary(zset/empty(), fn(acc, d) integrate-step(acc, d, cmp))

pub fun differentiate(s : stream<h,a>, ?cmp : (a,a) -> order) : st<h> stream<h,a>
  s.add-unary(zset/empty(), fn(prev, cur) differentiate-step(prev, cur, cmp))

// Join takes four orderings: the two input element types (for the integrals kept
// as state), the key, and the output row.
pub fun join( l : stream<h,a>, r : stream<h,b>
            , ka : a -> k, kb : b -> k, f : (a,b) -> c
            , acmp : (a,a) -> order, bcmp : (b,b) -> order
            , kcmp : (k,k) -> order, ccmp : (c,c) -> order ) : st<h> stream<h,c>
  l.add-binary(r, join-state(),
    fn(st0, da, db) join-step(st0, da, db, ka, kb, f, acmp, bcmp, kcmp, ccmp))

// -- scheduler ---------------------------------------------------------------

// One step: run every node once, in creation order.
pub fun step(c : circuit<h>) : st<h> ()
  get(c.nodes).reverse.foreach(fn(n) n())
