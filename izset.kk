// izset.kk -- Z-sets indexed by key, for incremental join state.
//
// An indexed Z-set is an ordered map from key to the Z-set of rows with that key.
// Invariant: no group is empty (a group that cancels to nothing is removed).
//
// Compared with the flat zset, this lets a join step touch only the keys that
// appear in the delta: group the delta (small), then look each key up in the
// state (O(log n)) instead of regrouping the whole state.
module izset

import zset
import tmap

pub struct izset<k,a>(by-key : tmap<k, zset<a>>)

pub fun empty() : izset<k,a>
  Izset(tmap/empty())

pub fun is-empty(ix : izset<k,a>) : bool
  tmap/is-empty(ix.by-key)

// Number of distinct keys.
pub fun key-count(ix : izset<k,a>) : int
  tmap/size(ix.by-key)

// The rows with this key (empty if none).
pub fun lookup(ix : izset<k,a>, key : k, ?k/cmp : (k,k) -> order) : zset<a>
  match tmap/lookup(ix.by-key, key, k/cmp)
    Nothing -> zset/empty()
    Just(g) -> g

// Index a (small) Z-set by key. `groups` sorts by key with a stable sort, so each
// group's rows stay in the zset's own order and need no re-sorting.
pub fun index-by(z : zset<a>, key : a -> k, ?k/cmp : (k,k) -> order) : izset<k,a>
  val gs = zset/groups(z, key, k/cmp)
  Izset(gs.foldl(tmap/empty(), fn(t, g) tmap/insert(t, g.fst, Zset(g.snd), k/cmp)))

// state + delta: one O(log n) update per key in the delta. A group that sums to
// empty is deleted from the map.
pub fun add-delta(state : izset<k,a>, delta : izset<k,a>, ?a/cmp : (a,a) -> order, ?k/cmp : (k,k) -> order) : izset<k,a>
  fun merge-group(old, dg)
    match old
      Nothing -> Just(dg)
      Just(g) ->
        val merged = zset/plus(g, dg, a/cmp)
        if zset/is-empty(merged) then Nothing else Just(merged)
  Izset(tmap/fold(delta.by-key, state.by-key,
    fn(t, key, dg) tmap/alter(t, key, fn(old) merge-group(old, dg), k/cmp)))

// Pair every row of `small` with the rows of `big` that share its key, using f.
// Cost: one lookup in `big` per key of `small`, plus the matches produced.
// Weights multiply. The result is an unsorted list (the caller normalises it).
pub fun probe( small : izset<k,a>, big : izset<k,b>, f : (a,b) -> c
             , ?k/cmp : (k,k) -> order ) : list<(c,int)>
  fun visit(acc, key, ga)
    match tmap/lookup(big.by-key, key, k/cmp)
      Nothing -> acc
      Just(gb) -> ga.items.flatmap(fn(l) gb.items.smap(fn(r) (f(l.fst, r.fst), l.snd * r.snd))) ++ acc
  tmap/fold(small.by-key, Nil, visit)

// ---- inspection (tests, debugging) -----------------------------------------

// Forget the index: all rows as one Z-set.
pub fun to-zset(ix : izset<k,a>, ?a/cmp : (a,a) -> order) : zset<a>
  zset/from-list(tmap/fold(ix.by-key, Nil, fn(acc, _k, g) g.items ++ acc), a/cmp)

// Tree invariants hold and no group is empty.
pub fun valid(ix : izset<k,a>, ?k/cmp : (k,k) -> order) : bool
  tmap/valid(ix.by-key, k/cmp) &&
    tmap/fold(ix.by-key, True, fn(ok, _k, g) ok && not(zset/is-empty(g)))
