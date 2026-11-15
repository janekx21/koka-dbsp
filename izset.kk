module izset

import std/core/undiv
import zset
import tmap

// ---------------------------------------------------------------------------
// Type and basic constructors
// ---------------------------------------------------------------------------

struct izset<k,a>(groups : tmap<k, zset<a>>)   // invariant: no empty groups

pub fun izset/show(izset: izset<k, a>, ?k/show: (k) -> string, ?a/show: (zset<a>) -> string) : total string
  val parts = izset.groups.to-list.map(fn((k, a)) k/show(k) ++ ": " ++ a/show(a))
  "<" ++ parts.join(", ") ++ ">"



pub fun empty()
  Izset(tmap/empty())  

pub fun izset/is-empty(z : izset<k,a>) : bool
  z.groups.is-empty

// // ------------------------
// // Operations
// // ------------------------

pub fun index-by(z : zset<a>, key: (a) -> k, ?k/cmp: (k,k) -> order, ?a/cmp: (a,a) -> order) : e izset<k,a>
  val gs = z.groups(key,k/cmp).map(fn((k, g)) (k,zset/from-list(g, a/cmp)))
  val t =  tmap/from-list(gs)
  Izset(t)

pub fun add(state: izset<k,a>, delta: izset<k, a>, ?a/cmp: (a,a) -> order, ?k/cmp: (k,k) -> order) : e izset<k,a>
  val merge = fn(m, n, cmp)
    match m
      Just(z) -> Just(z.plus(n, cmp))
      Nothing -> Just(n)

  val dgs = delta.groups
  val gs = dgs.fold(state.groups, fn(t,k,v) t.alter(k, fn (m) merge(m, v, a/cmp) ,k/cmp))
  Izset(gs)


pub fun lookup(ix: izset<k,a>, key: k, ?cmp: (k,k) -> order) : zset<a>
  match ix.groups.lookup(key)
    Just(z) -> z
    Nothing -> zset/empty()
  
  

fun ok(label : string, cond : bool) : console bool
  println((if cond then "ok   " else "FAIL ") ++ label)
  cond

fun main()
  println("== unit ==")
  val deltas = zset/of-keys([1,2,3,4,5])
  val ix = deltas.index-by(fn(i) i%3)
  ok("lookup: valid key", ix.lookup(0) == zset/of-keys([3]))
  ok("lookup: invalid key is empty", ix.lookup(99) == zset/of-keys([]))

  val deltas2 = zset/of-keys([6,7,8])
  val ix2 = deltas2.index-by(fn(i) i%3)
  ok("add: linear", ix.add(ix2).groups.to-list == (deltas.plus(deltas2)).index-by(fn(i) i%3).groups.to-list)
  
