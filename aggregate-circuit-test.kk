// aggregate-circuit-test.kk -- the aggregate operators wired into a circuit, plus a scale test.
import std/core/debug
import zset
import izset
import tmap
import aggregate
import circuit

fun rcmp(a : (int,int), b : (int,int)) : order
  cmp(a.fst, b.fst).andthen(fn() cmp(a.snd, b.snd))

fun key-of(r : (int,int)) : int
  r.fst

fun mk-out(k : int, v : int) : (int,int)
  (k, v)

fun payload-of(r : maybe<(int,int)>) : maybe<int>
  match r
    Nothing -> Nothing
    Just(x) -> Just(x.snd)

fun max-payload(g : zset<(int,int)>) : maybe<int>
  payload-of(max-row(g, rcmp))

fun showz(z : zset<(int,int)>) : string
  z.show(fn(r) "(" ++ r.fst.show ++ "," ++ r.snd.show ++ ")")

fun rows(xs : list<((int,int),int)>) : zset<(int,int)>
  zset/from-list(xs, rcmp)

pub fun main() : <console,ndet> ()
  println("== circuit: input -> distinct, count-by-key, max-by-key ==")
  with run
  val c = circuit()
  val (src, src-in) = c.input()
  val dist  = src.distinct(rcmp)
  val cnt   = src.aggregate-by(key-of, agg-count(), mk-out, cmp, rcmp)
  val mx    = src.aggregate-group-by(key-of, max-payload, mk-out, rcmp, cmp, rcmp)
  val cnt-v = cnt.integrate(rcmp)                       // materialised views
  val mx-v  = mx.integrate(rcmp)
  fun tick(label : string, d : zset<(int,int)>)
    src-in.push(d, rcmp)
    c.step()
    println(label)
    println("  distinct delta: " ++ showz(dist.read()))
    println("  count delta:    " ++ showz(cnt.read()) ++ "   count view: " ++ showz(cnt-v.read()))
    println("  max delta:      " ++ showz(mx.read()) ++ "   max view:   " ++ showz(mx-v.read()))
  tick("step 1: dept 1 gets payloads 3,5; dept 2 gets 4",   rows([((1,3),1), ((1,5),1), ((2,4),1)]))
  tick("step 2: duplicate of (1,5), new max in dept 2",     rows([((1,5),1), ((2,9),1)]))
  tick("step 3: remove one copy of (1,5) and the max of dept 2", rows([((1,5),-1), ((2,9),-1)]))
  tick("step 4: dept 2 emptied",                            rows([((2,4),-1)]))
