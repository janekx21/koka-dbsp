// tmap.kk -- persistent ordered map as a weight-balanced tree.
//
// Every node stores the size of its subtree, and the balance invariant is a ratio
// between the sizes of siblings: if a node has more than one entry below it, neither
// child may be more than `delta` times as large as the other. The parameters
// (delta = 3, ratio = 2) are the ones proved correct by Hirai & Yamamoto,
// "Balancing weight-balanced trees" (JFP 2011), and used by Haskell's Data.Map.
//
// All operations take an explicit ordering as an implicit parameter `?cmp`, in the
// same style as zset.kk. Updates are persistent: they return a new tree and share
// everything off the changed path with the old one.
module tmap

// Do not build `Bin` nodes by hand: the size field and the balance invariant
// are maintained by the functions below. `valid` checks both.
pub type tmap<k,v>
  Tip
  Bin(sz : int, key : k, value : v, left : tmap<k,v>, right : tmap<k,v>)

val delta = 3
val ratio = 2

// ---------------------------------------------------------------------------
// Construction and inspection
// ---------------------------------------------------------------------------

pub fun empty() : tmap<k,v>
  Tip

pub fun size(t : tmap<k,v>) : int
  match t
    Tip -> 0
    Bin(n, _, _, _, _) -> n

pub fun is-empty(t : tmap<k,v>) : bool
  match t
    Tip -> True
    _   -> False

pub fun singleton(key : k, value : v) : tmap<k,v>
  Bin(1, key, value, Tip, Tip)

pub fun lookup(t : tmap<k,v>, key : k, ?cmp : (k,k) -> order) : maybe<v>
  match t
    Tip -> Nothing
    Bin(_, kx, x, l, r) -> match cmp(key, kx)
      Lt -> lookup(l, key, cmp)
      Gt -> lookup(r, key, cmp)
      Eq -> Just(x)

pub fun member(t : tmap<k,v>, key : k, ?cmp : (k,k) -> order) : bool
  match lookup(t, key, cmp)
    Nothing -> False
    Just(_) -> True

pub fun min-entry(t : tmap<k,v>) : maybe<(k,v)>
  match t
    Tip -> Nothing
    Bin(_, k, x, Tip, _) -> Just((k,x))
    Bin(_, _, _, l, _) -> min-entry(l)

pub fun max-entry(t : tmap<k,v>) : maybe<(k,v)>
  match t
    Tip -> Nothing
    Bin(_, k, x, _, Tip) -> Just((k,x))
    Bin(_, _, _, _, r) -> max-entry(r)

// ---------------------------------------------------------------------------
// Balancing
// ---------------------------------------------------------------------------

// A node whose size is computed from its children.
fun bin(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : tmap<k,v>
  Bin(size(l) + size(r) + 1, k, x, l, r)

fun single-l(k1 : k, x1 : v, t1 : tmap<k,v>, t : tmap<k,v>) : tmap<k,v>
  match t
    Bin(_, k2, x2, t2, t3) -> bin(k2, x2, bin(k1, x1, t1, t2), t3)
    Tip -> bin(k1, x1, t1, Tip)                       // unreachable

fun single-r(k1 : k, x1 : v, t : tmap<k,v>, t3 : tmap<k,v>) : tmap<k,v>
  match t
    Bin(_, k2, x2, t1, t2) -> bin(k2, x2, t1, bin(k1, x1, t2, t3))
    Tip -> bin(k1, x1, Tip, t3)                       // unreachable

fun double-l(k1 : k, x1 : v, t1 : tmap<k,v>, t : tmap<k,v>) : tmap<k,v>
  match t
    Bin(_, k2, x2, Bin(_, k3, x3, t2, t3), t4) ->
      bin(k3, x3, bin(k1, x1, t1, t2), bin(k2, x2, t3, t4))
    _ -> single-l(k1, x1, t1, t)                      // unreachable

fun double-r(k1 : k, x1 : v, t : tmap<k,v>, t4 : tmap<k,v>) : tmap<k,v>
  match t
    Bin(_, k2, x2, t1, Bin(_, k3, x3, t2, t3)) ->
      bin(k3, x3, bin(k2, x2, t1, t2), bin(k1, x1, t3, t4))
    _ -> single-r(k1, x1, t, t4)                      // unreachable

fun rotate-l(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : tmap<k,v>
  match r
    Bin(_, _, _, ly, ry) ->
      if size(ly) < ratio * size(ry) then single-l(k, x, l, r) else double-l(k, x, l, r)
    Tip -> bin(k, x, l, r)                            // unreachable

fun rotate-r(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : tmap<k,v>
  match l
    Bin(_, _, _, ly, ry) ->
      if size(ry) < ratio * size(ly) then single-r(k, x, l, r) else double-r(k, x, l, r)
    Tip -> bin(k, x, l, r)                            // unreachable

// Rebuild a node after one of its subtrees changed size by at most one entry.
fun balance(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : tmap<k,v>
  val sl = size(l)
  val sr = size(r)
  if sl + sr <= 1 then Bin(sl + sr + 1, k, x, l, r)
  elif sr > delta * sl then rotate-l(k, x, l, r)
  elif sl > delta * sr then rotate-r(k, x, l, r)
  else Bin(sl + sr + 1, k, x, l, r)

// ---------------------------------------------------------------------------
// Insert, delete, alter
// ---------------------------------------------------------------------------

pub fun insert(t : tmap<k,v>, key : k, value : v, ?cmp : (k,k) -> order) : tmap<k,v>
  match t
    Tip -> Bin(1, key, value, Tip, Tip)
    Bin(n, kx, x, l, r) -> match cmp(key, kx)
      Lt -> balance(kx, x, insert(l, key, value, cmp), r)
      Gt -> balance(kx, x, l, insert(r, key, value, cmp))
      Eq -> Bin(n, key, value, l, r)

// Remove the smallest / largest entry of the non-empty tree with these parts.
fun delete-min-bin(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : ((k,v), tmap<k,v>)
  match l
    Tip -> ((k,x), r)
    Bin(_, lk, lx, ll, lr) ->
      val (m, l') = delete-min-bin(lk, lx, ll, lr)
      (m, balance(k, x, l', r))

fun delete-max-bin(k : k, x : v, l : tmap<k,v>, r : tmap<k,v>) : ((k,v), tmap<k,v>)
  match r
    Tip -> ((k,x), l)
    Bin(_, rk, rx, rl, rr) ->
      val (m, r') = delete-max-bin(rk, rx, rl, rr)
      (m, balance(k, x, l, r'))

// Join two trees whose keys are already ordered (all of l < all of r) and whose
// sizes were balanced against each other before one entry was removed.
fun glue(l : tmap<k,v>, r : tmap<k,v>) : tmap<k,v>
  match l
    Tip -> r
    Bin(_, lk, lx, ll, lr) -> match r
      Tip -> l
      Bin(_, rk, rx, rl, rr) ->
        if size(l) > size(r) then
          val ((mk, mx), l') = delete-max-bin(lk, lx, ll, lr)
          balance(mk, mx, l', r)
        else
          val ((mk, mx), r') = delete-min-bin(rk, rx, rl, rr)
          balance(mk, mx, l, r')

pub fun delete(t : tmap<k,v>, key : k, ?cmp : (k,k) -> order) : tmap<k,v>
  match t
    Tip -> Tip
    Bin(_, kx, x, l, r) -> match cmp(key, kx)
      Lt -> balance(kx, x, delete(l, key, cmp), r)
      Gt -> balance(kx, x, l, delete(r, key, cmp))
      Eq -> glue(l, r)

// The general update: `f` sees the current value (if any) and says what to store.
// Returning Nothing deletes the key (or leaves it absent).
pub fun alter(t : tmap<k,v>, key : k, f : maybe<v> -> e maybe<v>, ?cmp : (k,k) -> order) : e tmap<k,v>
  match t
    Tip -> match f(Nothing)
      Nothing -> Tip
      Just(x) -> Bin(1, key, x, Tip, Tip)
    Bin(n, kx, x, l, r) -> match cmp(key, kx)
      Lt -> balance(kx, x, alter(l, key, f, cmp), r)
      Gt -> balance(kx, x, l, alter(r, key, f, cmp))
      Eq -> match f(Just(x))
        Nothing -> glue(l, r)
        Just(x') -> Bin(n, kx, x', l, r)

// ---------------------------------------------------------------------------
// Traversal and conversion
// ---------------------------------------------------------------------------

// In-order (ascending key) fold.
pub fun fold(t : tmap<k,v>, init : b, f : (b,k,v) -> e b) : e b
  match t
    Tip -> init
    Bin(_, k, x, l, r) ->
      val acc  = fold(l, init, f)
      val acc' = f(acc, k, x)
      fold(r, acc', f)

fun to-list-acc(t : tmap<k,v>, acc : list<(k,v)>) : list<(k,v)>
  match t
    Tip -> acc
    Bin(_, k, x, l, r) -> to-list-acc(l, Cons((k,x), to-list-acc(r, acc)))

// Entries in ascending key order.
pub fun to-list(t : tmap<k,v>) : list<(k,v)>
  to-list-acc(t, Nil)

// Later entries for the same key replace earlier ones.
pub fun from-list(xs : list<(k,v)>, ?cmp : (k,k) -> order) : tmap<k,v>
  xs.foldl(Tip, fn(t, p) insert(t, p.fst, p.snd, cmp))

// ---------------------------------------------------------------------------
// Invariant checking (for tests)
// ---------------------------------------------------------------------------

pub fun height(t : tmap<k,v>) : int
  match t
    Tip -> 0
    Bin(_, _, _, l, r) -> 1 + max(height(l), height(r))

// Just(size) when every stored size is correct and every node is weight-balanced.
fun balanced(t : tmap<k,v>) : maybe<int>
  match t
    Tip -> Just(0)
    Bin(n, _, _, l, r) -> match balanced(l)
      Nothing -> Nothing
      Just(sl) -> match balanced(r)
        Nothing -> Nothing
        Just(sr) ->
          if n == sl + sr + 1 && (sl + sr <= 1 || (sl <= delta * sr && sr <= delta * sl))
            then Just(n) else Nothing

fun ascending-from(prev : k, xs : list<(k,v)>, ?cmp : (k,k) -> order) : bool
  match xs
    Nil -> True
    Cons((k,_), rest) -> cmp(prev, k) == Lt && ascending-from(k, rest, cmp)

// Keys strictly ascending in order, stored sizes correct, and weight balance holds.
pub fun valid(t : tmap<k,v>, ?cmp : (k,k) -> order) : bool
  match balanced(t)
    Nothing -> False
    Just(_) -> match to-list(t)
      Nil -> True
      Cons((k,_), rest) -> ascending-from(k, rest, cmp)
