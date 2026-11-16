// tmap-test.kk -- tests for tmap.kk
//
//  1. unit tests for each operation
//  2. sequential workloads (ascending / descending), which are the classic way to
//     unbalance a tree: validity and a height bound are checked
//  3. random operation sequences checked against a naive sorted-list model, with the
//     tree invariants verified after EVERY operation
import tmap

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fun ok(label : string, cond : bool) : console bool
  println((if cond then "ok   " else "FAIL ") ++ label)
  cond

fun entries-equal(xs : list<(int,int)>, ys : list<(int,int)>) : bool
  match xs
    Nil -> ys.is-nil
    Cons((k1,v1), xs') -> match ys
      Nil -> False
      Cons((k2,v2), ys') -> k1 == k2 && v1 == v2 && entries-equal(xs', ys')

fun maybe-eq(a : maybe<int>, b : maybe<int>) : bool
  match a
    Nothing -> b.is-nothing
    Just(x) -> match b
      Nothing -> False
      Just(y) -> x == y

fun render(xs : list<(int,int)>) : string
  "[" ++ xs.smap(fn(p) p.fst.show ++ ":" ++ p.snd.show).join(", ") ++ "]"

// ---------------------------------------------------------------------------
// The reference model: a sorted association list
// ---------------------------------------------------------------------------

fun model-lookup(m : list<(int,int)>, key : int) : maybe<int>
  match m
    Nil -> Nothing
    Cons((k,v), rest) -> if k == key then Just(v) elif k > key then Nothing else model-lookup(rest, key)

fun model-insert(m : list<(int,int)>, key : int, value : int) : list<(int,int)>
  match m
    Nil -> [(key,value)]
    Cons((k,v), rest) ->
      if key < k then Cons((key,value), m)
      elif key == k then Cons((key,value), rest)
      else Cons((k,v), model-insert(rest, key, value))

fun model-delete(m : list<(int,int)>, key : int) : list<(int,int)>
  match m
    Nil -> Nil
    Cons((k,v), rest) ->
      if key == k then rest
      elif key < k then m
      else Cons((k,v), model-delete(rest, key))

fun model-alter(m : list<(int,int)>, key : int, f : maybe<int> -> maybe<int>) : list<(int,int)>
  match f(model-lookup(m, key))
    Nothing -> model-delete(m, key)
    Just(y) -> model-insert(m, key, y)

// An update that sometimes inserts, sometimes changes, and sometimes deletes.
fun bump(m : maybe<int>) : maybe<int>
  match m
    Nothing -> Just(1)
    Just(x) -> if x >= 3 then Nothing else Just(x + 1)

// ---------------------------------------------------------------------------
// 1. Unit tests
// ---------------------------------------------------------------------------

fun unit-tests() : console list<bool>
  val e : tmap<int,string> = empty()
  val t1 = e.insert(2, "b").insert(1, "a").insert(3, "c")
  val t2 = t1.insert(2, "B")                      // overwrite
  val t3 = t1.delete(2)
  val t4 = t1.delete(99)                          // absent
  val ta = e.alter(5, fn(m) match m { Nothing -> Just("new"); Just(x) -> Just(x) })
  val tb = t1.alter(2, fn(m) match m { Just(x) -> Just(x ++ "!"); Nothing -> Nothing })
  val tc = t1.alter(2, fn(_) Nothing)             // delete via alter
  val td = t1.alter(77, fn(_) Nothing)            // absent stays absent
  val strs = fn(t : tmap<int,string>) t.to-list.smap(fn(p) p.fst.show ++ p.snd).join(",")
  val sorted = from-list([(5,"e"),(1,"a"),(4,"d"),(2,"b"),(3,"c")])
  val dups   = from-list([(1,"x"),(2,"y"),(1,"z")])
  val keys-in-order = t1.fold([], fn(acc, k, _) Cons(k, acc)).reverse
  [ ok("empty: size 0, no lookup, valid",
       e.size == 0 && e.is-empty && e.lookup(1).is-nothing && e.valid)
  , ok("insert/lookup", t1.lookup(1) == Just("a") && t1.lookup(3) == Just("c") && t1.lookup(9).is-nothing)
  , ok("size after inserts", t1.size == 3 && t1.valid)
  , ok("overwrite keeps size and replaces value", t2.size == 3 && t2.lookup(2) == Just("B") && t2.valid)
  , ok("member", t1.member(2) && not(t1.member(4)))
  , ok("delete present", t3.size == 2 && t3.lookup(2).is-nothing && t3.valid && strs(t3) == "1a,3c")
  , ok("delete absent is a no-op", strs(t4) == strs(t1) && t4.valid)
  , ok("delete does not modify the original (persistence)", strs(t1) == "1a,2b,3c")
  , ok("alter inserts when absent", ta.lookup(5) == Just("new") && ta.size == 1 && ta.valid)
  , ok("alter updates when present", strs(tb) == "1a,2b!,3c" && tb.valid)
  , ok("alter can delete", strs(tc) == "1a,3c" && tc.valid)
  , ok("alter Nothing on absent key is a no-op", strs(td) == strs(t1))
  , ok("min and max", sorted.min-entry == Just((1,"a")) && sorted.max-entry == Just((5,"e")) && e.min-entry.is-nothing)
  , ok("to-list is sorted", strs(sorted) == "1a,2b,3c,4d,5e")
  , ok("fold visits keys in ascending order", keys-in-order == [1,2,3])
  , ok("from-list: later entry wins", strs(dups) == "1z,2y" && dups.size == 2)
  ]

// ---------------------------------------------------------------------------
// 2. Sequential workloads
// ---------------------------------------------------------------------------

// Apply `step` for every key, checking validity after each one.
fun seq-insert(ks : list<int>, t : tmap<int,int>) : bool
  match ks
    Nil -> True
    Cons(k, rest) ->
      val t' = t.insert(k, k * 10)
      if t'.valid then seq-insert(rest, t') else False

fun seq-delete(ks : list<int>, t : tmap<int,int>) : bool
  match ks
    Nil -> t.is-empty
    Cons(k, rest) ->
      val t' = t.delete(k)
      if t'.valid then seq-delete(rest, t') else False

fun build(ks : list<int>) : tmap<int,int>
  ks.foldl(empty(), fn(t, k) t.insert(k, k * 10))

fun sequential-tests() : console list<bool>
  val n = 500
  val asc  = list(1, n)
  val desc = list(1, n).reverse
  val big  = build(list(1, 5000))
  val bigd = build(list(1, 5000).reverse)
  println("  (heights: 500 ascending = " ++ build(asc).height.show ++
          ", 5000 ascending = " ++ big.height.show ++
          ", 5000 descending = " ++ bigd.height.show ++ ")")
  // A weight-balanced tree with delta = 3 has height at most ~2.41 * log2(n).
  // n = 500 -> log2 ~ 9, n = 5000 -> log2 ~ 12.3
  [ ok("insert 1..500 ascending, valid after every insert", seq-insert(asc, empty()))
  , ok("insert 500..1 descending, valid after every insert", seq-insert(desc, empty()))
  , ok("delete 1..500 ascending from a full tree, valid after every delete", seq-delete(asc, build(asc)))
  , ok("delete 500..1 descending from a full tree, valid after every delete", seq-delete(desc, build(asc)))
  , ok("delete in interleaved order (odds then evens)",
       seq-delete(list(1, n).filter(fn(k) k % 2 == 1) ++ list(1, n).filter(fn(k) k % 2 == 0), build(asc)))
  , ok("5000 ascending inserts: size, valid, height bound",
       big.size == 5000 && big.valid && big.height <= 30)
  , ok("5000 descending inserts: size, valid, height bound",
       bigd.size == 5000 && bigd.valid && bigd.height <= 30)
  , ok("lookup after 5000 inserts", big.lookup(1) == Just(10) && big.lookup(5000) == Just(50000) && big.lookup(5001).is-nothing)
  ]

// ---------------------------------------------------------------------------
// 3. Randomised model-based tests
// ---------------------------------------------------------------------------

fun next(seed : int) : int
  (seed * 1103515245 + 12345) % 2147483648

fun pick(seed : int, bound : int) : int
  (seed / 65536) % bound

fun lookups-agree(ks : list<int>, t : tmap<int,int>, model : list<(int,int)>) : bool
  match ks
    Nil -> True
    Cons(k, rest) -> maybe-eq(t.lookup(k), model-lookup(model, k)) && lookups-agree(rest, t, model)

// Run `steps` random operations (insert / delete / alter) on a tree and the model in
// lock step; after each one the tree must be valid and equal to the model.
fun run-ops(steps : list<int>, t : tmap<int,int>, model : list<(int,int)>, seed : int, range : int) : console bool
  match steps
    Nil -> lookups-agree(list(0, range - 1), t, model)
    Cons(i, rest) ->
      val s1   = next(seed)
      val s2   = next(s1)
      val key  = pick(s1, range)
      val kind = pick(s2, 3)
      val (t', model', name) =
        if kind == 0 then (t.insert(key, i), model-insert(model, key, i), "insert")
        elif kind == 1 then (t.delete(key), model-delete(model, key), "delete")
        else (t.alter(key, bump), model-alter(model, key, bump), "alter")
      if t'.valid then
        if entries-equal(t'.to-list, model') then run-ops(rest, t', model', next(s2), range)
        else
          println("     contents differ from model at step " ++ i.show ++ " (" ++ name ++ " " ++ key.show ++ ")")
          println("     tree:  " ++ render(t'.to-list))
          println("     model: " ++ render(model'))
          False
      else
        println("     invariant broken at step " ++ i.show ++ " (" ++ name ++ " " ++ key.show ++ ")")
        False

fun random-tests() : console list<bool>
  [ ok("random ops, 16 keys (constant collisions and deletes), 3000 steps",
       run-ops(list(1, 3000), empty(), Nil, 1, 16))
  , ok("random ops, 64 keys, 3000 steps",
       run-ops(list(1, 3000), empty(), Nil, 7, 64))
  , ok("random ops, 1000 keys (tree grows large), 3000 steps",
       run-ops(list(1, 3000), empty(), Nil, 42, 1000))
  , ok("random ops, 5 keys (tree keeps emptying), 2000 steps",
       run-ops(list(1, 2000), empty(), Nil, 99, 5))
  ]

// ---------------------------------------------------------------------------

pub fun main() : console ()
  println("== unit ==")
  val a = unit-tests()
  println("")
  println("== sequential ==")
  val b = sequential-tests()
  println("")
  println("== randomised, against a sorted-list model ==")
  val c = random-tests()
  println("")
  val all = a ++ b ++ c
  val failed = all.filter(fn(x) not(x)).length
  if failed == 0 then println("all " ++ all.length.show ++ " checks passed")
  else println(failed.show ++ " of " ++ all.length.show ++ " checks FAILED")
