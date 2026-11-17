import zset
import circuit
import aggregate

struct user(username : string)
struct message
  message-id : int
  creator    : string
  parent-id  : maybe<int>
  content    : string

struct friend(a-username : string, b-username : string)


fun user/cmp(a : user, b : user) : order
  cmp(a.username, b.username)

fun message/cmp(a : message, b : message) : order
  cmp(a.message-id, b.message-id).andthen(fn() cmp(a.creator, b.creator)).andthen(fn() cmp(a.parent-id, b.parent-id)).andthen(fn() cmp(a.content, b.content))


fun friend/cmp(a : friend, b : friend) : order
  cmp(a.a-username, b.a-username)
  .andthen(fn() cmp(a.b-username, b.b-username))

fun user/show(u : user) : string
  "User(" ++ u.username ++ ")"

fun message/show(m : message) : string
  "Message(" ++ m.message-id.show ++ ", " ++ m.creator ++ ": " ++ m.content ++ ")"



// fun row/show(r : row) : string
//   "(" ++ r.name ++ ", " ++ r.dept-name ++ ")"

fun check(label : string, ok : bool) : console ()
  println((if ok then "ok   " else "FAIL ") ++ label)

// The from-scratch reference query, used to check the incremental circuit.
// fun emp-dept(es : zset<emp>, ds : zset<dept>) : zset<row>
//   zset/join(es, ds, fn(e) e.dept, fn(d) d.dept-id, 
//             fn(e,d) Row(e.name, d.dept-name))

// --- pure step functions: no circuit, no heap -------------------------------

// fun snapshots(ds : list<zset<int>>, acc : zset<int>) : list<zset<int>>
//   match ds
//     Nil -> Nil
//     Cons(d, rest) ->
//       val (acc', snap) = integrate-step(acc, d)
//       Cons(snap, snapshots(rest, acc'))

// fun changes(ss : list<zset<int>>, prev : zset<int>) : list<zset<int>>
//   match ss
//     Nil -> Nil
//     Cons(s, rest) ->
//       val (prev', d) = differentiate-step(prev, s)
//       Cons(d, changes(rest, prev'))

// fun render(zs : list<zset<int>>) : string
//   zs.smap(fn(z) z.show()).join(" ; ")


// struct user-friend(username: string,)

pub fun main() : console ()
  // println("== pure step functions ==")

  // val deltas = [of-keys([1,2]), singleton(1, -1), of-keys([3])]
  // val snaps  = snapshots(deltas, zset/empty())
  // println("deltas:    " ++ render(deltas))
  // println("snapshots: " ++ render(snaps))
  // check("D(I(deltas)) = deltas", render(changes(snaps, zset/empty())) == render(deltas))
  // println("")

  println("== circuit ==")
  
  // val e2  = Emp(2, "bob", 10)
  // val e3  = Emp(3, "cat", 20)
  // val e4  = Emp(4, "dan", 30)
  // val d10 = Dept(10, "eng")
  // val d10b = Dept(10, "engineering")
  // val d20 = Dept(20, "ops")
  // val d30 = Dept(30, "hr")

  with run
  val c = circuit()
  val (users, users-in) = c.input()
  val (friends, friends-in) = c.input()
  val (message, message-in) = c.input()

  val user-view = users.integrate(user/cmp)
  val message-view = message.integrate(message/cmp)


  val friends-message-view = users
    .join(friends, username, a-username, fn (u, f)  (u,f))
    .join(message, fn((_,f)) f.b-username, fn(m) m.creator, fn ((u,_),m) (u,m))
    .integrate()
  // val (depts, depts-in) = c.input()
  // val view    = emps.join(depts, fn(e) e.dept, fn(d) d.dept-id,
  //                         fn(e,d) Row(e.name, d.dept-name),
  //                         emp/cmp, dept/cmp, cmp, row/cmp)
  // val mat     = view.integrate()                         // the materialised view
  // val only-hr = view.filter(fn(r) r.dept-name == "hr")  // second consumer of `view`

  // // totals of everything pushed so far, for the from-scratch reference
  // val tot-e = ref(zset/empty())
  // val tot-d = ref(zset/empty())
  // val prev  = ref(zset/empty())
  //
  val next-message-id = message.aggregate-by(fn (_) 0, agg-count, fn (k,v) v).integrate()

  val send-message = fn(creator, content)
    val next-id = next-message-id.read.to-list.map(fst).head(99)
    println(next-message-id.read.show)
    message-in.push(of-keys([Message(next-id, creator, Nothing, content)]))
    c.step()
    
  val print-all = fn()
    println("  users: " ++ user-view.read.to-list.map(fst).show())
    println("  messages: " ++ message-view.read.to-list.map(fst).show())
    println("  friend-messages: " ++ friends-message-view.read.to-list.map(fst).show())
    println("")



  users-in.push(of-keys([User("Janek"), User("Lara")]))
  c.step()
  print-all()

  message-in.push(of-keys([Message(0, "Janek", Nothing, "Hallo Welt")]))
  message-in.push(of-keys([Message(1, "Lara", Nothing, "Wie gehts Leute?")]))
  friends-in.push(of-keys([Friend("Lara", "Janek")]))
  c.step()
  print-all()

  // Use case: As a user I want to see all messages from my friends
  
  val print-user-messages = fn(username': string)
    val x = friends-message-view.read.filter(fn (fm) fm.fst.username == username').to-list.map(fst)
    //      ^^^^^^^^^^^^^^^^^^^^      ^^^^
    //                  mat view      Adhoc query

    println("  " ++ username' ++ "s messages:")
    x.foreach fn((_,m))
      println("   " ++ m.creator ++ ": " ++ m.content)
    println("")
  print-user-messages("Janek")
  print-user-messages("Lara")

  
  message-in.push(of-keys([Message(2, "Janek", Nothing, "Was geht ab welt?")]))
  friends-in.push(of-keys([Friend("Janek", "Lara")]))
  c.step()


  print-user-messages("Janek")
  print-user-messages("Lara")


  send-message("Janek", "hi lara :)")
  send-message("Lara", "hi janek :>")

  print-user-messages("Janek")
  print-user-messages("Lara")

  print-all()
  // tick("step 2: dan joins dept 30, which does not exist yet", of-keys([e4]), zset/empty())
  // tick("step 3: dept 30 appears", zset/empty(), of-keys([d30]))
  // tick("step 4: ann leaves; dept 10 is renamed", neg(of-keys([e1])), from-list([(d10,-1),(d10b,1)]))
