// demo.kk -- an incremental emp ⋈ dept view, driven step by step
import zset
import circuit

struct emp(emp-id : int, name : string, dept : int)
struct dept(dept-id : int, dept-name : string)
struct row(name : string, dept-name : string)

fun emp/cmp(a : emp, b : emp) : order
  cmp(a.emp-id, b.emp-id).andthen(fn() cmp(a.name, b.name)).andthen(fn() cmp(a.dept, b.dept))

fun dept/cmp(a : dept, b : dept) : order
  cmp(a.dept-id, b.dept-id).andthen(fn() cmp(a.dept-name, b.dept-name))

fun row/cmp(a : row, b : row) : order
  cmp(a.name, b.name).andthen(fn() cmp(a.dept-name, b.dept-name))

fun row/show(r : row) : string
  "(" ++ r.name ++ ", " ++ r.dept-name ++ ")"

fun check(label : string, ok : bool) : console ()
  println((if ok then "ok   " else "FAIL ") ++ label)

// The from-scratch reference query, used to check the incremental circuit.
fun emp-dept(es : zset<emp>, ds : zset<dept>) : zset<row>
  zset/join(es, ds, fn(e) e.dept, fn(d) d.dept-id, 
            fn(e,d) Row(e.name, d.dept-name))

// --- pure step functions: no circuit, no heap -------------------------------

fun snapshots(ds : list<zset<int>>, acc : zset<int>) : list<zset<int>>
  match ds
    Nil -> Nil
    Cons(d, rest) ->
      val (acc', snap) = integrate-step(acc, d)
      Cons(snap, snapshots(rest, acc'))

fun changes(ss : list<zset<int>>, prev : zset<int>) : list<zset<int>>
  match ss
    Nil -> Nil
    Cons(s, rest) ->
      val (prev', d) = differentiate-step(prev, s)
      Cons(d, changes(rest, prev'))

fun render(zs : list<zset<int>>) : string
  zs.map(fn(z) z.show()).join(" ; ")

pub fun main() : console ()
  println("== pure step functions ==")
  val deltas = [of-keys([1,2]), singleton(1, -1), of-keys([3])]
  val snaps  = snapshots(deltas, zset/empty())
  println("deltas:    " ++ render(deltas))
  println("snapshots: " ++ render(snaps))
  check("D(I(deltas)) = deltas", render(changes(snaps, zset/empty())) == render(deltas))
  println("")

  println("== circuit ==")
  val e1  = Emp(1, "ann", 10)
  val e2  = Emp(2, "bob", 10)
  val e3  = Emp(3, "cat", 20)
  val e4  = Emp(4, "dan", 30)
  val d10 = Dept(10, "eng")
  val d10b = Dept(10, "engineering")
  val d20 = Dept(20, "ops")
  val d30 = Dept(30, "hr")

  with run
  val c = circuit()
  val (emps, emps-in)   = c.input()
  val (depts, depts-in) = c.input()
  val view    = emps.join(depts, fn(e) e.dept, fn(d) d.dept-id,
                          fn(e,d) Row(e.name, d.dept-name),
                          emp/cmp, dept/cmp, cmp, row/cmp)
  val mat     = view.integrate()                         // the materialised view
  val only-hr = view.filter(fn(r) r.dept-name == "hr")  // second consumer of `view`

  // totals of everything pushed so far, for the from-scratch reference
  val tot-e = ref(zset/empty())
  val tot-d = ref(zset/empty())
  val prev  = ref(zset/empty())

  fun tick(label : string, de : zset<emp>, dd : zset<dept>)
    emps-in.push(de)
    depts-in.push(dd)
    c.step()
    tot-e := zset/plus(!tot-e, de)
    tot-d := zset/plus(!tot-d, dd)
    val now = emp-dept(!tot-e, !tot-d)
    val delta = view.read()
    println(label)
    println("  delta out: " ++ delta.show())
    println("  hr only:   " ++ only-hr.read().show())
    println("  view now:  " ++ mat.read().show())
    check("  delta = recompute(now) - recompute(before)", delta == zset/minus(now, !prev))
    check("  integrated view = recompute(now)", mat.read() == now)
    prev := now
    println("")

  tick("step 1: initial load", of-keys([e1,e2,e3]), of-keys([d10,d20]))
  tick("step 2: dan joins dept 30, which does not exist yet", of-keys([e4]), zset/empty())
  tick("step 3: dept 30 appears", zset/empty(), of-keys([d30]))
  tick("step 4: ann leaves; dept 10 is renamed", neg(of-keys([e1])), from-list([(d10,-1),(d10b,1)]))
