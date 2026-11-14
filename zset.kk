module zset
import std/core/undiv


// ---------------------------------------------------------------------------
// Type and basic constructors
// ---------------------------------------------------------------------------

struct zset<k>(items : list<(k, int)>)

fun zset/show(zset: zset<k>, ?show: (k) -> string) : total string
  "[" ++ zset.items.map(fn((i, _)) show(i)).join(", ") ++ "]"

fun empty()
  Zset(Nil)  
fun zset/is-empty(z : zset<k>) : bool
  z.items.is-nil

fun singleton(key : k, weight : int) : zset<k>
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
  from-list(xs.map(fn(x) (x,1)), cmp)

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

pub fun plus(a : zset<k>, b : zset<k>, ?cmp : (k,k) -> order) : zset<k>
  Zset(merge-items(a.items, b.items, cmp))

pub fun neg(a : zset<k>) : zset<k>
  Zset(a.items.map(fn(p) (p.fst, 0 - p.snd)))

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
pub fun map(a : zset<k>, f : k -> e j, jcmp : (j,j) -> order) : e zset<j>
  from-list(a.items.map(fn(p) (f(p.fst), p.snd)), jcmp)

// ---------------------------------------------------------------------------
// Join with explicit key extractors (sort-merge)
// ---------------------------------------------------------------------------

// Group weighted items by key: ascending keys, each with its (item,weight) run.
fun group-run(k : k, acc : list<v>, xs : list<(k,v)>, kcmp : (k,k) -> order) : list<(k,list<v>)>
  match xs
    Nil -> [(k, acc.reverse)]
    Cons((k2,v2), rest) ->
      if kcmp(k,k2) == Eq then group-run(k, Cons(v2,acc), rest, kcmp)
      else Cons((k, acc.reverse), group-run(k2, [v2], rest, kcmp))

fun group-runs(xs : list<(k,v)>, kcmp : (k,k) -> order) : list<(k,list<v>)>
  match xs
    Nil -> Nil
    Cons((k,v), rest) -> group-run(k, [v], rest, kcmp)

fun groups(z : zset<a>, key : a -> e k, kcmp : (k,k) -> order) : e list<(k,list<(a,int)>)>
  val keyed  = z.items.map(fn(p) (key(p.fst), p))
  val sorted = keyed.msort(fn(p,q) kcmp(p.fst, q.fst) != Gt)
  group-runs(sorted, kcmp)

fun join-groups( gl : list<(k,list<(a,int)>)>, gr : list<(k,list<(b,int)>)>
               , kcmp : (k,k) -> order
               , f : (a,b) -> e c ) : e list<(c,int)>
  match gl
    Nil -> Nil
    Cons((kl,ls), gl') -> match gr
      Nil -> Nil
      Cons((kr,rs), gr') -> match kcmp(kl,kr)
        Lt -> join-groups(gl', gr, kcmp, f)
        Gt -> join-groups(gl, gr', kcmp, f)
        Eq ->
          // within a matching key, every left row pairs with every right row;
          // weights multiply
          val here = ls.flatmap(fn(l) rs.map(fn(r) (f(l.fst, r.fst), l.snd * r.snd)))
          here ++ join-groups(gl', gr', kcmp, f)

// join(a, b, ka, kb, kcmp, f, ccmp): for every pair (x,y) with ka(x) == kb(y),
// emit f(x,y) with weight w(x) * w(y).
pub fun join( a : zset<a>, b : zset<b>
            , ka : a -> e k, kb : b -> e k, kcmp : (k,k) -> order
            , f : (a,b) -> e c, ccmp : (c,c) -> order ) : e zset<c>
  val pairs = join-groups(groups(a, ka, kcmp), groups(b, kb, kcmp), kcmp, f)
  from-list(pairs, ccmp)

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

pub fun equal(a : zset<k>, b : zset<k>, ?cmp : (k,k) -> order) : bool
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


// Main for testing
//



struct emp(emp-id : int, name : string, dept : int)
struct dept(dept-id : int, dept-name : string)
struct row(name : string, dept-name : string)


fun emp-cmp(a : emp, b : emp) : order
  cmp(a.emp-id, b.emp-id).andthen(fn() cmp(a.name, b.name)).andthen(fn() cmp(a.dept, b.dept))

fun cmp(a : emp, b : emp) : order
  emp-cmp(a,b)


fun dept/cmp(a : dept, b : dept) : order
  cmp(a.dept-id, b.dept-id).andthen(fn() cmp(a.dept-name, b.dept-name))

fun row-cmp(a : row, b : row) : order
  cmp(a.name, b.name).andthen(fn() cmp(a.dept-name, b.dept-name))

fun row/show(r : row) : string
  "(" ++ r.name ++ ", " ++ r.dept-name ++ ")"

fun emp/show(e : emp) : string
  "emp(" ++ e.emp-id.show ++ ", " ++ e.name ++ ", " ++ e.dept.show ++ ")"

fun check(label : string, ok : bool) : console ()
  println((if ok then "ok   " else "FAIL ") ++ label)

// emp ⋈ dept on dept id; output is a plain struct built by the caller
fun emp-dept(es : zset<emp>, ds : zset<dept>) : zset<row>
  join(es, ds, fn(e) e.dept, fn(d) d.dept-id, cmp,
       fn(e,d) Row(e.name, d.dept-name), row-cmp)


pub fun main() : console ()
  val e1 = Emp(1, "ann", 10)
  val e2 = Emp(2, "bob", 10)
  val e3 = Emp(3, "cat", 20)
  val e4 = Emp(4, "dan", 30)   // dept 30 does not exist yet
  val d10 = Dept(10, "eng")
  val d20 = Dept(20, "ops")
  val d30 = Dept(30, "hr")

  val es = of-keys([e1,e2,e3])
  val ds = of-keys([d10,d20])

  println("emps:   " ++ es.show())
  println("joined: " ++ emp-dept(es, ds).show())
  println("")

  // --- group laws -----------------------------------------------------------
  check("a + (-a) = 0", plus(es, neg(es), emp-cmp).is-empty)
  check("plus commutes",
        equal(plus(es, of-keys([e4], emp-cmp), emp-cmp),
              plus(of-keys([e4], emp-cmp), es, emp-cmp), emp-cmp))
  check("duplicate keys add weights",
        of-keys([e1,e1], emp-cmp).weighted-count == 2)
  check("insert then delete cancels",
        from-list([(e1,1),(e1,-1)], emp-cmp).is-empty)

  // --- linear operators -----------------------------------------------------
  val a = of-keys([e1,e2], emp-cmp)
  val b = of-keys([e3,e4], emp-cmp)
  val pname = fn(e : emp) e.dept
  check("filter is linear",
        equal(filter(plus(a,b,emp-cmp), fn(e) e.dept < 30),
              plus(filter(a, fn(e) e.dept < 30), filter(b, fn(e) e.dept < 30), emp-cmp), emp-cmp))
  check("map is linear",
        equal(map(plus(a,b,emp-cmp), pname, cmp),
              plus(map(a, pname, cmp), map(b, pname, cmp), cmp), cmp))
  val depts-of = map(es, pname, cmp)
  println("dept ids of emps (map merges duplicates): " ++ depts-of.show(show))

  // --- join is bilinear: this identity is what incrementalisation uses ------
  //   (a+da) ⋈ (b+db)  -  a ⋈ b  =  da ⋈ b  +  a ⋈ db  +  da ⋈ db
  val da = of-keys([e4])                  // new employee
  val db = of-keys([d30])                // new department
  val full  = emp-dept(plus(es,da,emp-cmp), plus(ds,db))
  val delta-direct = minus(full, emp-dept(es,ds), row-cmp)
  val delta-incr   = plus(plus(emp-dept(da,ds), emp-dept(es,db), row-cmp),
                          emp-dept(da,db), row-cmp)
  println("")
  println("delta (recomputed): " ++ delta-direct.show())
  println("delta (incremental): " ++ delta-incr.show())
  check("bilinear delta identity", equal(delta-direct, delta-incr, row-cmp))

  // --- retraction -----------------------------------------------------------
  val gone = emp-dept(neg(of-keys([e1], emp-cmp)), ds)
  println("deleting ann gives: " ++ gone.show())
  check("join with negative weights retracts", gone.weighted-count == -1)

// fun main()
//   val persons = Zset([("Janek", 1)])
//   println(persons.show())
