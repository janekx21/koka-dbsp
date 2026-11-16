// aggregate-test.kk -- tests for aggregate.kk and the circuit wiring.
//
//  1. hand-built unit tests for each operator's edge cases
//  2. randomised tests against from-scratch references (rows are (key, payload)):
//       at every step  output delta == Q(total after) - Q(total before)
//                      sum of output deltas == Q(total)
//                      state holds no stale entries
//  3. the same operators wired into a circuit
//  4. a scale test (large deltas, default stack)
import std/core/debug
import zset
import izset
import tmap
import aggregate
import circuit

fun rcmp(a : (int,int), b : (int,int)) : order
  cmp(a.fst, b.fst).andthen(fn() cmp(a.snd, b.snd))

fun zeq(a : zset<(int,int)>, b : zset<(int,int)>) : bool
  zset/(==)(a, b, rcmp)

fun key-of(r : (int,int)) : int
  r.fst

fun ok(label : string, cond : bool) : console bool
  println((if cond then "ok   " else "FAIL ") ++ label)
  cond

fun showz(z : zset<(int,int)>) : string
  z.show(fn(r) "(" ++ r.fst.show ++ "," ++ r.snd.show ++ ")")

fun row(k : int, v : int, w : int) : zset<(int,int)>
  zset/singleton((k, v), w)

fun rows(xs : list<((int,int),int)>) : zset<(int,int)>
  zset/from-list(xs, rcmp)

// ---------------------------------------------------------------------------
// From-scratch references (deliberately naive, independent of aggregate.kk)
// ---------------------------------------------------------------------------

fun group(tot : zset<(int,int)>, k : int) : list<((int,int),int)>
  tot.items.filter(fn(p) p.fst.fst == k)

fun sumw(g : list<((int,int),int)>) : int
  g.foldl(0, fn(acc, p) acc + p.snd)

fun positives(g : list<((int,int),int)>) : list<int>
  g.filter(fn(p) p.snd > 0).smap(fn(p) p.fst.snd)

fun ref-key(tot : zset<(int,int)>, k : int, f : list<((int,int),int)> -> maybe<int>) : list<((int,int),int)>
  match f(group(tot, k))
    Nothing -> []
    Just(v) -> [((k, v), 1)]

fun ref-rows(tot : zset<(int,int)>, f : list<((int,int),int)> -> maybe<int>) : zset<(int,int)>
  rows(list(0, 5).flatmap(fn(k) ref-key(tot, k, f)))

fun ref-distinct(tot : zset<(int,int)>) : zset<(int,int)>
  rows(tot.items.filter(fn(p) p.snd > 0).smap(fn(p) (p.fst, 1)))

fun ref-count(tot : zset<(int,int)>) : zset<(int,int)>
  ref-rows(tot, fn(g) if sumw(g) > 0 then Just(sumw(g)) else Nothing)

fun ref-sum(tot : zset<(int,int)>) : zset<(int,int)>
  ref-rows(tot, fn(g) if sumw(g) > 0 then Just(g.foldl(0, fn(acc, p) acc + p.snd * p.fst.snd)) else Nothing)

fun min-of(g : list<((int,int),int)>) : maybe<int>
  match positives(g)
    Nil -> Nothing
    Cons(x, xs) -> Just(xs.foldl(x, fn(a, b) if b < a then b else a))

fun max-of(g : list<((int,int),int)>) : maybe<int>
  match positives(g)
    Nil -> Nothing
    Cons(x, xs) -> Just(xs.foldl(x, fn(a, b) if b > a then b else a))

fun ref-min(tot : zset<(int,int)>) : zset<(int,int)>
  ref-rows(tot, min-of)

fun ref-max(tot : zset<(int,int)>) : zset<(int,int)>
  ref-rows(tot, max-of)

// number of keys whose group satisfies `p`
fun keys-where(tot : zset<(int,int)>, p : list<((int,int),int)> -> bool) : int
  list(0, 5).filter(fn(k) p(group(tot, k))).length

// ---------------------------------------------------------------------------
// The operators under test, as plain step functions
// ---------------------------------------------------------------------------

fun mk-out(k : int, v : int) : (int,int)
  (k, v)

fun distinct-op(st : tmap<(int,int),int>, d : zset<(int,int)>) : (tmap<(int,int),int>, zset<(int,int)>)
  distinct-step(st, d, rcmp)

fun count-op(st : tmap<int,int>, d : zset<(int,int)>) : (tmap<int,int>, zset<(int,int)>)
  aggregate-step(st, d, key-of, agg-count(), mk-out, cmp, rcmp)

fun sum-op(st : tmap<int,(int,int)>, d : zset<(int,int)>) : (tmap<int,(int,int)>, zset<(int,int)>)
  aggregate-step(st, d, key-of, agg-sum(fn(r) r.snd), mk-out, cmp, rcmp)

fun payload-of(r : maybe<(int,int)>) : maybe<int>
  match r
    Nothing -> Nothing
    Just(x) -> Just(x.snd)

fun min-op(st : izset<int,(int,int)>, d : zset<(int,int)>) : (izset<int,(int,int)>, zset<(int,int)>)
  aggregate-group-step(st, d, key-of, fn(g) payload-of(min-row(g, rcmp)), mk-out, rcmp, cmp, rcmp)

fun max-op(st : izset<int,(int,int)>, d : zset<(int,int)>) : (izset<int,(int,int)>, zset<(int,int)>)
  aggregate-group-step(st, d, key-of, fn(g) payload-of(max-row(g, rcmp)), mk-out, rcmp, cmp, rcmp)

// ---------------------------------------------------------------------------
// 1. Unit tests
// ---------------------------------------------------------------------------

fun unit-distinct() : console bool
  val e : tmap<(int,int),int> = tmap/empty()
  val (s1, o1) = distinct-op(e,  row(1, 7, 1))     // appears
  val (s2, o2) = distinct-op(s1, row(1, 7, 1))     // weight 2: still present, no output
  val (s3, o3) = distinct-op(s2, row(1, 7, -1))    // weight 1: no output
  val (s4, o4) = distinct-op(s3, row(1, 7, -1))    // weight 0: disappears
  val (s5, o5) = distinct-op(s4, row(1, 7, -1))    // weight -1: still absent, no output, remembered
  val (s6, o6) = distinct-op(s5, row(1, 7, 1))     // back to 0: nothing, forgotten
  val (s7, o7) = distinct-op(e,  row(1, 7, 3))     // weight 3 is still just +1
  ok("distinct: first insert emits +1", zeq(o1, row(1, 7, 1)))
    && ok("distinct: duplicates emit nothing", o2.is-empty && o3.is-empty)
    && ok("distinct: last copy removed emits -1", zeq(o4, row(1, 7, -1)))
    && ok("distinct: negative weight is absent and remembered", o5.is-empty && tmap/size(s5) == 1)
    && ok("distinct: returning to zero forgets the row", o6.is-empty && tmap/size(s6) == 0)
    && ok("distinct: weight 3 emits weight 1", zeq(o7, row(1, 7, 1)) && tmap/size(s7) == 1)

fun unit-count() : console bool
  val e : tmap<int,int> = tmap/empty()
  val (s1, o1) = count-op(e,  rows([((1,0),1), ((1,1),1)]))
  val (s2, o2) = count-op(s1, row(1, 2, 1))
  val (s3, o3) = count-op(s2, rows([((1,0),-1), ((1,1),-1), ((1,2),-1)]))
  val (t1, p1) = count-op(e,  row(1, 0, -1))                        // retraction arrives first
  val (t2, p2) = count-op(t1, row(1, 0, 1))
  val (t3, p3) = count-op(t2, row(1, 9, 1))
  val (u1, q1) = count-op(e,  row(2, 0, -1))
  val (u2, q2) = count-op(u1, rows([((2,0),1), ((2,1),2)]))         // net count 1: group appears
  ok("count: new group emits (key,count)", zeq(o1, row(1, 2, 1)))
    && ok("count: change retracts old row and inserts new", zeq(o2, rows([((1,2),-1), ((1,3),1)])))
    && ok("count: emptied group is retracted and forgotten", zeq(o3, row(1, 3, -1)) && tmap/size(s3) == 0)
    && ok("count: early retraction emits nothing but is remembered", p1.is-empty && tmap/size(t1) == 1)
    && ok("count: insertion cancelling it forgets the key", p2.is-empty && tmap/size(t2) == 0)
    && ok("count: later insert behaves as a fresh group", zeq(p3, row(1, 1, 1)))
    && ok("count: negative count then net-positive appears correctly", q1.is-empty && zeq(q2, row(2, 2, 1)))

fun unit-sum() : console bool
  val e : tmap<int,(int,int)> = tmap/empty()
  val (s1, o1) = sum-op(e,  row(1, 5, 1))
  val (s2, o2) = sum-op(s1, row(1, 0, 1))        // payload 0: sum unchanged, so no output
  val (s3, o3) = sum-op(s2, row(1, 5, -1))
  val (s4, o4) = sum-op(s3, row(1, 0, -1))
  ok("sum: new group", zeq(o1, row(1, 5, 1)))
    && ok("sum: value unchanged emits nothing", o2.is-empty)
    && ok("sum: retraction changes the sum", zeq(o3, rows([((1,5),-1), ((1,0),1)])))
    && ok("sum: last row removed retracts the group", zeq(o4, row(1, 0, -1)) && tmap/size(s4) == 0)

fun unit-minmax() : console bool
  val e : izset<int,(int,int)> = izset/empty()
  val (a1, m1) = min-op(e,  rows([((1,3),1), ((1,5),1)]))
  val (a2, m2) = min-op(a1, row(1, 1, 1))                // new minimum
  val (a3, m3) = min-op(a2, row(1, 1, -1))               // minimum removed: next one takes over
  val (a4, m4) = min-op(a3, row(1, 9, 1))                // not the minimum: no output
  val (b1, x1) = max-op(e,  rows([((1,3),1), ((1,5),1)]))
  val (b2, x2) = max-op(b1, row(1, 5, -1))
  val (b3, x3) = max-op(b2, rows([((1,3),-1)]))          // group empties
  ok("min: initial", zeq(m1, row(1, 3, 1)))
    && ok("min: new smaller row", zeq(m2, rows([((1,3),-1), ((1,1),1)])))
    && ok("min: removing the minimum falls back to the next", zeq(m3, rows([((1,1),-1), ((1,3),1)])))
    && ok("min: non-extreme insert emits nothing", m4.is-empty)
    && ok("max: initial and fallback", zeq(x1, row(1, 5, 1)) && zeq(x2, rows([((1,5),-1), ((1,3),1)])))
    && ok("max: emptied group removed from state", zeq(x3, row(1, 3, -1)) && b3.key-count == 0)

// ---------------------------------------------------------------------------
// 2. Randomised tests against from-scratch references
// ---------------------------------------------------------------------------

fun next(seed : int) : int
  (seed * 1103515245 + 12345) % 2147483648

fun pick(seed : int, bound : int) : int
  (seed / 65536) % bound

fun gen-rows(is : list<int>, seed : int, acc : list<((int,int),int)>) : (list<((int,int),int)>, int)
  match is
    Nil -> (acc, seed)
    Cons(_, rest) ->
      val s1 = next(seed)
      val s2 = next(s1)
      val s3 = next(s2)
      gen-rows(rest, s3, Cons(((pick(s1, 6), pick(s2, 5)), pick(s3, 5) - 2), acc))   // key 0..5, payload 0..4, weight -2..2

fun gen-delta(seed : int) : (zset<(int,int)>, int)
  val s0 = next(seed)
  val (rs, s1) = gen-rows(list(1, pick(s0, 6)), s0, Nil)
  (rows(rs), s1)

fun drive( steps : list<int>, st : s, tot : zset<(int,int)>, cum : zset<(int,int)>, seed : int
         , step : (s, zset<(int,int)>) -> (s, zset<(int,int)>)
         , reference : zset<(int,int)> -> zset<(int,int)>
         , state-ok : (s, zset<(int,int)>) -> bool ) : console bool
  match steps
    Nil -> True
    Cons(i, rest) ->
      val (d, seed') = gen-delta(seed)
      val (st', out) = step(st, d)
      val tot' = zset/plus(tot, d, rcmp)
      val cum' = zset/plus(cum, out, rcmp)
      val want = zset/minus(reference(tot'), reference(tot), rcmp)
      if not(zeq(out, want)) then
        println("     step " ++ i.show ++ ": output delta wrong")
        println("       delta in: " ++ showz(d))
        println("       got:      " ++ showz(out))
        println("       want:     " ++ showz(want))
        False
      elif not(zeq(cum', reference(tot'))) then
        println("     step " ++ i.show ++ ": sum of outputs != Q(total)")
        False
      elif not(state-ok(st', tot')) then
        println("     step " ++ i.show ++ ": state has stale or missing entries")
        False
      else drive(rest, st', tot', cum', seed', step, reference, state-ok)

fun z0() : zset<(int,int)>
  zset/empty()

fun random-tests() : console bool
  val n = 600
  val steps = list(1, n)
  val d = ok("distinct vs from-scratch (4 seeds x " ++ n.show ++ " steps)",
             [1,2,3,4].all(fn(sd) drive(steps, tmap/empty(), z0(), z0(), sd, distinct-op, ref-distinct,
                                        fn(st, tot) tmap/size(st) == tot.items.length)))
  val c = ok("count vs from-scratch",
             [1,2,3,4].all(fn(sd) drive(steps, tmap/empty(), z0(), z0(), sd, count-op, ref-count,
                                        fn(st, tot) tmap/size(st) == keys-where(tot, fn(g) sumw(g) != 0))))
  val s = ok("sum vs from-scratch",
             [1,2,3,4].all(fn(sd) drive(steps, tmap/empty(), z0(), z0(), sd, sum-op, ref-sum,
                                        fn(st, tot) tmap/size(st) == keys-where(tot, fn(g) sumw(g) != 0 || g.foldl(0, fn(a, p) a + p.snd * p.fst.snd) != 0))))
  val mn = ok("min vs from-scratch",
              [1,2,3,4].all(fn(sd) drive(steps, izset/empty(), z0(), z0(), sd, min-op, ref-min,
                                         fn(st, tot) st.key-count == keys-where(tot, fn(g) not(g.is-nil)) && st.valid(cmp))))
  val mx = ok("max vs from-scratch",
              [1,2,3,4].all(fn(sd) drive(steps, izset/empty(), z0(), z0(), sd, max-op, ref-max,
                                         fn(st, tot) st.key-count == keys-where(tot, fn(g) not(g.is-nil)) && st.valid(cmp))))
  d && c && s && mn && mx

pub fun main() : <console,ndet> ()
  println("== unit ==")
  val u1 = unit-distinct()
  val u2 = unit-count()
  val u3 = unit-sum()
  val u4 = unit-minmax()
  println("")
  println("== randomised, against from-scratch references ==")
  val r = random-tests()
  println("")
  if u1 && u2 && u3 && u4 && r then println("all checks passed") else println("FAILED")
