// bench.kk -- cost of a single-row step as the join state grows.
// Load N rows on each side, then apply STEPS single-row deltas to the left side.
import zset
import izset
import circuit

val n = 80_000
val steps = 200
val use-new = True

fun rcmp(a : (int,int), b : (int,int)) : order
  cmp(a.fst, b.fst).andthen(fn() cmp(a.snd, b.snd))

fun key-of(r : (int,int)) : int
  r.fst

fun combine(x : (int,int), y : (int,int)) : (int,int)
  (x.fst, x.snd + y.snd)

fun next(seed : int) : int
  (seed * 1103515245 + 12345) % 2147483648

fun load(k : int) : zset<(int,int)>
  zset/from-list(list(0, n - 1).map(fn(i) ((i % k, i), 1)), rcmp)

// old: flat state, regrouped every step
fun ojoin(x : zset<(int,int)>, y : zset<(int,int)>) : zset<(int,int)>
  zset/join(x, y, key-of, key-of, combine, cmp, rcmp)

fun old-steps(is : list<int>, ia : zset<(int,int)>, ib : zset<(int,int)>, k : int, seed : int, total : int) : int
  match is
    Nil -> total
    Cons(i, rest) ->
      val s  = next(seed)
      val da = zset/singleton(((s / 65536) % k, 1000000 + i), 1)
      val out = ojoin(da, ib)                                   // db is empty: only da join ib matters
      old-steps(rest, zset/plus(ia, da, rcmp), ib, k, s, total + out.items.length)

// new: indexed state
fun new-steps(is : list<int>, st : join-state<int,(int,int),(int,int)>, k : int, seed : int, total : int) : int
  match is
    Nil -> total
    Cons(i, rest) ->
      val s  = next(seed)
      val da = zset/singleton(((s / 65536) % k, 1000000 + i), 1)
      val (st', out) = join-step(st, da, zset/empty(), key-of, key-of, combine, rcmp, rcmp, cmp, rcmp)
      new-steps(rest, st', k, s, total + out.items.length)

pub fun main() : console ()
  val k  = max(n / 2, 1)
  val la = load(k)
  val lb = load(k)
  val total =
    if use-new then
      val (st, _) = join-step(join-state(), la, lb, key-of, key-of, combine, rcmp, rcmp, cmp, rcmp)
      new-steps(list(1, steps), st, k, 7, 0)
    else
      old-steps(list(1, steps), la, lb, k, 7, 0)
  println("n=" ++ n.show ++ " steps=" ++ steps.show ++ " new=" ++ use-new.show ++ " output rows over all steps=" ++ total.show)
