// aggregate-scale.kk -- large deltas must not overflow the stack, and a single-row step
// against a large state must stay cheap. Run with the DEFAULT stack:
//   koka -O2 -o aggregate-scale aggregate-scale.kk && ./aggregate-scale
import std/core/debug
import std/time/timer
import std/time/duration
import std/num/float64
import zset
import izset
import tmap
import aggregate

fun rcmp(a : (int,int), b : (int,int)) : order
  cmp(a.fst, b.fst).andthen(fn() cmp(a.snd, b.snd))
fun key-of(r : (int,int)) : int
  r.fst
fun mk-out(k : int, v : int) : (int,int)
  (k, v)
fun max-payload(g : zset<(int,int)>) : maybe<int>
  match max-row(g, rcmp)
    Nothing -> Nothing
    Just(x) -> Just(x.snd)

fun one-row(i : int) : zset<(int,int)>
  zset/singleton(((i * 7919) % 200000, 1000000 + i), 1)

fun steps-distinct(is : list<int>, st : tmap<(int,int),int>) : int
  match is
    Nil -> 0
    Cons(i, rest) ->
      val (st', out) = distinct-step(st, one-row(i), rcmp)
      out.items.length + steps-distinct(rest, st')

fun steps-count(is : list<int>, st : tmap<int,int>) : int
  match is
    Nil -> 0
    Cons(i, rest) ->
      val (st', out) = aggregate-step(st, one-row(i), key-of, agg-count(), mk-out, cmp, rcmp)
      out.items.length + steps-count(rest, st')

fun steps-max(is : list<int>, st : izset<int,(int,int)>) : int
  match is
    Nil -> 0
    Cons(i, rest) ->
      val (st', out) = aggregate-group-step(st, one-row(i), key-of, max-payload, mk-out, rcmp, cmp, rcmp)
      out.items.length + steps-max(rest, st')

pub fun main() : <console,ndet> ()
  val n = 400000
  val k = n / 2
  val big = zset/from-list(list(0, n - 1).smap(fn(i) (((i % k, i), 1))), rcmp)
  trace("input: " ++ big.items.length.show ++ " rows, " ++ k.show ++ " keys")

  val e1 : tmap<(int,int),int> = tmap/empty()
  val (s1, o1) = distinct-step(e1, big, rcmp)
  trace("distinct:        " ++ o1.items.length.show ++ " rows out, state " ++ tmap/size(s1).show)

  val e2 : tmap<int,int> = tmap/empty()
  val (s2, o2) = aggregate-step(e2, big, key-of, agg-count(), mk-out, cmp, rcmp)
  trace("count by key:    " ++ o2.items.length.show ++ " rows out, state " ++ tmap/size(s2).show)

  val e3 : tmap<int,(int,int)> = tmap/empty()
  val (s3, o3) = aggregate-step(e3, big, key-of, agg-sum(fn(r) r.snd), mk-out, cmp, rcmp)
  trace("sum by key:      " ++ o3.items.length.show ++ " rows out, state " ++ tmap/size(s3).show)

  val e4 : izset<int,(int,int)> = izset/empty()
  val (s4, o4) = aggregate-group-step(e4, big, key-of, max-payload, mk-out, rcmp, cmp, rcmp)
  trace("max by key:      " ++ o4.items.length.show ++ " rows out, state " ++ s4.key-count.show)

  // 200 sequential one-row steps against the loaded state; report the average per step
  val (t1, a) = elapsed(fn() steps-distinct(list(1, 200), s1))
  val (t2, b) = elapsed(fn() steps-count(list(1, 200), s2))
  val (t3, c) = elapsed(fn() steps-max(list(1, 200), s4))
  println("avg single-row step vs " ++ n.show ++ "-row state:  distinct " ++ (t1.milli-seconds.float64 / 200.0).show-fixed(3) ++ " ms,  count " ++ (t2.milli-seconds.float64 / 200.0).show-fixed(3) ++ " ms,  max " ++ (t3.milli-seconds.float64 / 200.0).show-fixed(3) ++ " ms   (outputs " ++ a.show ++ "/" ++ b.show ++ "/" ++ c.show ++ ")")
