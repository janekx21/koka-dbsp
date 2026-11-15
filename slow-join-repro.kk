// slow-join-repro.kk -- minimal reproducer for a performance anomaly (cause not identified).
//
// The same join (a 1-row Z-set against an 8000-row Z-set, 2 output rows) is run two ways:
// identical code, except that in `with-opaque-keys` the key-extractor functions arrive
// as parameters instead of being named at the call site.
//   known keys  : a few ms
//   opaque keys : > 1 second, and ~4x slower per doubling of n (superlinear)
// Opaque comparators, opaque combine functions, and opaque keys in `groups` alone are all fast.
// Build: koka -O2 -o repro slow-join-repro.kk && ./repro
import zset
import std/time/timer
import std/time/duration

fun rcmp(a : (int,int), b : (int,int)) : order
  cmp(a.fst, b.fst).andthen(fn() cmp(a.snd, b.snd))
fun key-of(^r : (int,int)) : int
  r.fst
fun combine(x : (int,int), y : (int,int)) : (int,int)
  (x.fst, x.snd + y.snd)

// copy of zset.kk's join-groups
fun jg( gl : list<(k,list<(a,int)>)>, gr : list<(k,list<(b,int)>)>, kcmp : (k,k) -> order, f : (a,b) -> e c ) : e list<(c,int)>
  match gl
    Nil -> Nil
    Cons((kl,ls), gl') -> match gr
      Nil -> Nil
      Cons((kr,rs), gr') -> match kcmp(kl,kr)
        Lt -> jg(gl', gr, kcmp, f)
        Gt -> jg(gl, gr', kcmp, f)
        Eq -> ls.flatmap(fn(l) rs.map(fn(r) (f(l.fst, r.fst), l.snd * r.snd))) ++ jg(gl', gr', kcmp, f)

fun with-known-keys(a : zset<(int,int)>, b : zset<(int,int)>) : zset<(int,int)>
  from-list(jg(groups(a, key-of, cmp), groups(b, key-of, cmp), cmp, combine), rcmp)

fun with-opaque-keys(a : zset<(int,int)>, b : zset<(int,int)>, ka : ((int,int)) -> int, kb : ((int,int)) -> int) : zset<(int,int)>
  from-list(jg(groups(a, ka, cmp), groups(b, kb, cmp), cmp, combine), rcmp)

pub fun main() : <console,ndet> ()
  val n = 8000
  val k = n / 2
  val big = from-list(list(0, n - 1).map(fn(i) (((i % k, i), 1))), rcmp)
  val one = singleton((3, 999999), 1)
  val (d1, _) = elapsed(fn() with-known-keys(one, big).items.length)
  val (d2, _) = elapsed(fn() with-opaque-keys(one, big, key-of, key-of).items.length)
  println("known keys: " ++ d1.milli-seconds.show ++ " ms    opaque keys: " ++ d2.milli-seconds.show ++ " ms") // $ known keys: 2 ms    opaque keys: 645 ms 
