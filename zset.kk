module zset
import std/core/undiv



// Stack-safe list map.
// std/core/list's `map` is declared `fip` and, in Koka v3.2.9, overflows the stack on
// long lists (about 80,000 elements with the default 8 MB stack). The same definition
// written as an ordinary function gets tail-recursion-modulo-constructor and runs in
// constant stack, so everything in this library that maps over a list of unbounded
// length uses this instead.
pub fun smap(xs : list<a>, f : a -> e b) : e list<b>
  match xs
    Nil -> Nil
    Cons(x, xx) -> Cons(f(x), smap(xx, f))


// ---------------------------------------------------------------------------
// Type and basic constructors
// ---------------------------------------------------------------------------

pub struct zset<k>(items : list<(k, int)>)

pub fun zset/show(zset: zset<k>, ?show: (k) -> string) : total string
  val sign  = fn(w : int) if w > 0 then "+" else ""
  val parts = zset.items.smap(fn(p) show(p.fst) ++ " -> " ++ sign(p.snd) ++ p.snd.show)
  "{" ++ parts.join(", ") ++ "}"

pub fun empty()
  Zset(Nil)  
pub fun zset/is-empty(z : zset<k>) : bool
  z.items.is-nil

pub fun singleton(key : k, weight : int) : zset<k>
  if weight == 0 then Zset(Nil) else Zset([(key,weight)])


// ---------------------------------------------------------------------------
// Stable merge sort (used to normalise arbitrary lists of weighted keys)
// ---------------------------------------------------------------------------

// `le(x,y)` = "x may come before y"; taking the left element on ties keeps it stable.
fun msort-merge(xs : list<a>, ys : list<a>, le : (a,a) -> bool) : list<a>
  match xs
    Nil -> ys
    Cons(x, xs') -> match ys
      Nil -> xs
      Cons(y, ys') ->
        if le(x,y) then Cons(x, msort-merge(xs', ys, le))
                   else Cons(y, msort-merge(xs, ys', le))

// Recursion on a size counter is not structural, so Koka infers `div` here.
// It does terminate (n strictly halves), so we discharge `div` in `msort`.
fun msort-n(xs : list<a>, n : int, le : (a,a) -> bool) : div list<a>
  if n <= 1 then xs else
    val h = n / 2
    msort-merge(msort-n(xs.take(h), h, le), msort-n(xs.drop(h), n - h, le), le)

pub fun msort(xs : list<a>, le : (a,a) -> bool) : list<a>
  pretend-no-div(fn() msort-n(xs, xs.length, le))

// ---------------------------------------------------------------------------
// Normalisation: sort, add weights of equal keys, drop zeros
// ---------------------------------------------------------------------------

// Walk a key-sorted list, adding up runs of equal keys and dropping zero totals.
// Structural recursion on `xs`, carrying the current run (k, w).
fun consolidate-run(k : k, w : int, xs : list<(k,int)>, ?cmp : (k,k) -> order) : list<(k,int)>
  match xs
    Nil -> if w == 0 then Nil else [(k,w)]
    Cons((k2,w2), rest) ->
      if cmp(k,k2) == Eq then consolidate-run(k, w + w2, rest, cmp)
      elif w == 0 then consolidate-run(k2, w2, rest, cmp)
      else Cons((k,w), consolidate-run(k2, w2, rest, cmp))

fun consolidate(xs : list<(k,int)>, ?cmp : (k,k) -> order) : list<(k,int)>
  match xs
    Nil -> Nil
    Cons((k,w), rest) -> consolidate-run(k, w, rest, cmp)

pub fun from-list(xs : list<(k,int)>, ?cmp : (k,k) -> order) : zset<k>
  val sorted = xs.msort(fn(p,q) cmp(p.fst, q.fst) != Gt)
  Zset(consolidate(sorted, cmp))

// Convenience: every key gets weight +1 (a plain set of insertions).
pub fun of-keys(xs : list<k>, ?cmp : (k,k) -> order) : zset<k>
  from-list(xs.smap(fn(x) (x,1)), cmp)

pub fun to-list(z : zset<k>) : list<(k,int)>
  z.items



// ---------------------------------------------------------------------------
// The abelian group structure: plus, neg, minus
// ---------------------------------------------------------------------------

fun merge-items(xs : list<(k,int)>, ys : list<(k,int)>, ?cmp : (k,k) -> order) : list<(k,int)>
  match xs
    Nil -> ys
    Cons((kx,wx), xs') -> match ys
      Nil -> xs
      Cons((ky,wy), ys') -> match cmp(kx,ky)
        Lt -> Cons((kx,wx), merge-items(xs', ys, cmp))
        Gt -> Cons((ky,wy), merge-items(xs, ys', cmp))
        Eq ->
          val w = wx + wy
          if w == 0 then merge-items(xs', ys', cmp)
                    else Cons((kx,w), merge-items(xs', ys', cmp))

// TODO this could be (+)

pub fun plus(a : zset<k>, b : zset<k>, ?cmp : (k,k) -> order) : zset<k>
  Zset(merge-items(a.items, b.items, cmp))

pub fun neg(a : zset<k>) : zset<k>
  Zset(a.items.smap(fn(p) (p.fst, 0 - p.snd)))

// TODO this could be (-)
 
pub fun minus(a : zset<k>, b : zset<k>, ?cmp : (k,k) -> order) : zset<k>
  plus(a, neg(b), cmp)

// 
// ---------------------------------------------------------------------------
// Linear operators
// ---------------------------------------------------------------------------

// Selection preserves order and weights, so no re-sorting is needed.
pub fun filter(a : zset<k>, pred : k -> e bool) : e zset<k>
  Zset(a.items.filter(fn(p) pred(p.fst)))

// Map can send distinct keys to the same key (weights add, possibly cancelling)
// and can reorder keys, so the result is re-normalised.
pub fun map(a : zset<k>, f : k -> e j, ?cmp : (j,j) -> order) : e zset<j>
  from-list(a.items.smap(fn(p) (f(p.fst), p.snd)), cmp)

// ---------------------------------------------------------------------------
// Join with explicit key extractors (sort-merge)
// ---------------------------------------------------------------------------

// Group weighted items by key: ascending keys, each with its (item,weight) run.
fun group-run(k : k, acc : list<v>, xs : list<(k,v)>, ?cmp : (k,k) -> order) : list<(k,list<v>)>
  match xs
    Nil -> [(k, acc.reverse)]
    Cons((k2,v2), rest) ->
      if cmp(k,k2) == Eq then group-run(k, Cons(v2,acc), rest, cmp)
      else Cons((k, acc.reverse), group-run(k2, [v2], rest, cmp))

fun group-runs(xs : list<(k,v)>, ?cmp : (k,k) -> order) : list<(k,list<v>)>
  match xs
    Nil -> Nil
    Cons((k,v), rest) -> group-run(k, [v], rest, cmp)

pub fun groups(z : zset<a>, key : a -> k, cmp : (k,k) -> order) : list<(k,list<(a,int)>)>
  val keyed  = z.items.smap(fn(p) (key(p.fst), p))
  val sorted = keyed.msort(fn(p,q) cmp(p.fst, q.fst) != Gt)
  group-runs(sorted, cmp)

fun join-groups( gl : list<(k,list<(a,int)>)>, gr : list<(k,list<(b,int)>)>
               , f : (a,b) -> e c
               , ?cmp : (k,k) -> order ) : e list<(c,int)>
  match gl
    Nil -> Nil
    Cons((kl,ls), gl') -> match gr
      Nil -> Nil
      Cons((kr,rs), gr') -> match cmp(kl,kr)
        Lt -> join-groups(gl', gr, f)
        Gt -> join-groups(gl, gr', f)
        Eq ->
          // within a matching key, every left row pairs with every right row;
          // weights multiply
          val here = ls.flatmap(fn(l) rs.smap(fn(r) (f(l.fst, r.fst), l.snd * r.snd)))
          here ++ join-groups(gl', gr', f)

// join(a, b, ka, kb, kcmp, f, ccmp): for every pair (x,y) with ka(x) == kb(y),
// emit f(x,y) with weight w(x) * w(y).
pub fun join( a : zset<a>, b : zset<b>
            , ka : a -> k, kb : b -> k, f : (a,b) -> c
            , ?k/cmp : (k,k) -> order, ?c/cmp : (c,c) -> order ) : zset<c>
  val pairs = join-groups(groups(a, ka, k/cmp), groups(b, kb, k/cmp), f)
  from-list(pairs, c/cmp)

// ---------------------------------------------------------------------------
// Inspection helpers
// ---------------------------------------------------------------------------

// Sum of all weights (the multiset cardinality).
pub fun weighted-count(z : zset<k>) : int
  z.items.foldl(0, fn(acc,p) acc + p.snd)

fun items-equal(xs : list<(k,int)>, ys : list<(k,int)>, ?cmp : (k,k) -> order) : bool
  match xs
    Nil -> ys.is-nil
    Cons((kx,wx), xs') -> match ys
      Nil -> False
      Cons((ky,wy), ys') -> wx == wy && cmp(kx,ky) == Eq && items-equal(xs', ys', cmp)

pub fun zset/(==)(a : zset<k>, b : zset<k>, ?cmp : (k,k) -> order) : bool
  items-equal(a.items, b.items, cmp)

// ---------------------------------------------------------------------------
// Ordering helpers for building `cmp` functions
// ---------------------------------------------------------------------------

// Lexicographic combination: `cmp(a.x, b.x).andthen(fn() cmp(a.y, b.y))`
pub fun andthen(o : order, next : () -> order) : order
  match o
    Eq -> next()
    _  -> o

pub fun pair-cmp(ca : (a,a) -> order, cb : (b,b) -> order) : (((a,b),(a,b)) -> order)
  fn(p, q)
    val (a1, b1) = p
    val (a2, b2) = q
    ca(a1, a2).andthen(fn() cb(b1, b2))
