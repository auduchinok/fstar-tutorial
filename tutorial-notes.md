# F* tutorial notes

F* syntax is based closely on the OCaml syntax and the non-light syntax of F#.
F* program consists of modules. Each module has body that contains definitions.
Main definition is optional.

```fsharp
module FileName
  type filename = string // type synonym

module ACLs
  open FileName // filename instead of FileName.filename

  let canWrite (f : filename) =
    match f with
    | "demo/tempfile" -> true
    | _ -> false

  let canRead (f : filename) =
    canWrite f || f = "demo/README"

```

### Refinement types

We can define interfaces for external functions.
F* can call .Net, OCaml methods.

```fsharp
module FileIO
  open ACLs
  open FileName
  assume val read  : f:filename{canRead f} -> string
  assume val write : f:filename{canWrite f} -> string -> unit
```

`assume val` declares values without definition.
Module `FileIO` declares `read` and `write` functions.

`x:{phi(x)}` defines a type that is a subset of `x` which elements satisfy predicate.

F* allows to use value if it's type is checked at runtime.

```fsharp
 exception InvalidRead

 val checkedRead : filename -> string
  let checkedRead f =
    if canRead f then read f else raise InvalidRead
```

### Inferred types and effects

In addition to inferring types of expressions F* infers side effects.

`t1 -> t2 -> ... -> tn -> E t` General function form.
`t1`, ..., `tn` are types of arguments, `E` is an effect type.

```fsharp
val canRead : filename -> bool (* ML type inference *)
val canRead : filename -> Tot bool (* F* type inference *)
```

`a' -> bool` is a shortcut for `a' -> ML bool`

Effect types:

* `Tot` is pure total, i.e. has no side effects
* `Dv`, effect may diverge
* `ST` may use heap
* `Exn` may throw exceptions
* `ML` may loop forever, do IO, etc.

```fsharp
val isPositive : int -> Tot bool
let isPositive n = n > 0

val max : int -> int -> Tot int
let max a b = if a > b then a else b

assume val read : filename -> ML string
```
Function arguments cannot have any side effect, thus only function result has an effect type.

Default effect type for non-`Tot` is `ML`.

```fsharp
let rec loop i = i + loop (i - 1) (* will be inferred to (int -> ML int) or just (int -> int) *)
(* We can explicitly set type to (int -> Dv int) *)
```

```fsharp
val : int -> ML (unit -> ML int) (* int -> (unit -> int) *)
let newCounter init =
  let c = ref init in
  fun () -> c := !c + 1; !c
```

```fsharp
val fact : x:int{x >= 0} -> Tot int (* Tot on non-negative ints *)
let rec fact n =
  if n = 0 then 1 else n * fact (n - 1)
```

### Assertions

F* tries to prove assertions statically by translating them to **Z3** theorem prover.

```fsharp
let a = assert (max 0 1 = 1)

let b = assert (forall x y. max x y >= x
                  && max x y >= y
                  && (max x y = x || max x y = y))
```

### Lemmas

A lemma is a *ghost total function*, which always return `unit`. The result of ghost function however carries useful info.

```fsharp
val factIsPositive : x:nat -> GTot (u:unit{fact x > 0})
let rec factIsPositive n =
  match n with
  | 0 -> ()
  | _ -> factIsPositive (n - 1)
```
Lemma has a *dependent function type* because the type of its result depends on the value of the parameter.

The type of the result of `factIsPositive 0`, `GTot (u:unit{fact 0 > 0})`, is different from the result of `factIsPositive 1`.

```fsharp
(* More general function definition *)
x1:t1 -> x2:t2 -> ... -> xn:tn[x1 ... xn-1] -> E t[x1 ... xn]
```

Each function parameter `xi` can freely appear in its scope after the first arrow following `xi`. `t[x1 .. xn]` shows that in definition.

### Syntax sugar for refinement types and lemmas

```fsharp
(* full type *)
val factIsIncreasing : x:(y:nat{y > 2}) -> GTot (u:unit{fact x > x})

(* simplify parameter *)
val factIsIncreasing : x:nat{x > 2} -> GTot (u:unit{fact x > x})

(* use lemma keyword *)
val factIsIncreasion : x:nat{x > 2} -> Lemma (fact x > x)

(* use pre- & post- conditions, less types cluttering *)
val factIsIncreasing : x:nat -> Lemma (requires (x > 2)) (ensures (fact x > x))

let rec factIsIncreasing n =
  match n with
  | 3 -> ()
  | _ -> factIsIncreasing (n - 1)
```

F* ensures internally that recursive calls in Tot function will terminate:

```fsharp
let factIsIncreasing : n:nat{2 < n && n < x} -> Lemma (fact n > n)
```

Another inductional prove example:

```fsharp
type nat = x:int{x >= 0}
type pos = x:nat{x >= 1}

val fib : nat -> Tot pos
let rec fib n =
  if n <= 1 then 1 else fib (n - 1) + fib (n - 2)

val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibIsIncreasing n =
  match n with
  | 2 -> ()
  | _ -> fibIsIncreasing (n - 1)

  (* induction step simplified, using admit() *)
  val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibIsIncreasing n =
  match n with
  | 2 -> ()
  | _ -> admit()

  (* or even automatically, experimental *)
    val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
  let rec fibIsIncreasing n = by_induction_on n fibIsIncreasing
```

### `bool` vs `Type`

Refinement types have form of `x:t{phi(x)}` where `phi` is a type, a *predicate on the value* `x:t`. When using boolean value as a predicate it automatically being coerced.

```fsharp
b2t (b:bool) : Type = (b == true)
```

`==` is a type constructor for equality predicate, it's not equal to `=`. `==` is heterogeneous, while `=` is homogeneous.

Boolean functions: `&&`, `||`, `not`.

The propositional connectives: `/\`, `\/`, `~`, `==>`, `<==>`.

Quantifiers: `forall`, `exists`.

```fsharp
canRead e /\ forall x. canWrite x ==> canRead x

(* full form *)
b2t(canRead e) /\ forall x. b2t(canWrite x) ==> b2t(canRead x)
```

### Simple inductive types

Constructors names capitalized. Default constructor effect type if Tot.

```fsharp
type myList 'a =
  | Nil  : myList 'a
  | Cons : hd: 'a -> tl: myList 'a -> myList 'a
```

`list` is defined in standard prelude (`FStar.List`), has same syntax-suggar as in F#.

```fsharp
type nat = x:int{x>=0}

val length : list 'a -> Tot nat
let rec length l =
  match l with
    | [] -> 0
    | hd :: tl -> 1 + length tl

val append: l1:list 'a -> l2:list 'a -> res:list 'a{length res = length l1 + length l2}
val append: list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 =
  match l1 with
    | [] -> l2
    | hd :: tl -> hd :: append tl l2

val appendLength: l1: list 'a -> l2: list 'a -> GTot (u:unit{length (append l1 l2) = length l1 + length l2})
val appendLength: l1: list 'a -> l2: list 'a -> Lemma (length (append l1 l2) = length l1 + length l2)
let rec appendLength l1 l2 =
  match l1 with
    | [] -> ()
    | hd :: tl -> appendLength tl l2

val mem: 'a -> list 'a -> Tot bool
let rec mem a l =
  match l with
    | [] -> false
    | hd :: tl -> hd = a || mem a tl

val appendMem: l1: list 'a -> l2: list 'a -> a: 'a -> Lemma (mem a (append l1 l2) <==> mem a l1 || mem a l2)
let rec appendMem l1 l2 a =
  match l1 with
    | hd :: tl -> appendMem tl l2 a
    | [] ->
        match l2 with
          | [] -> ()
          | hd :: tl -> appendMem [] tl a

(* given solution, why it is enough? *)
val appendMemGiven: l1: list 'a -> l2: list 'a -> a: 'a -> Lemma (mem a (append l1 l2) <==> mem a l1 || mem a l2)
let rec appendMemGiven l1 l2 a =
  match l1 with
    | [] -> ()
    | hd :: tl -> appendMemGiven tl l2 a
```

### *intrinsic* and *extrinsic* constraints

* *intrinsic* proving uses types refiniments
* *extrinsic* proving uses lemmas

It's not always possible to prove properties using *intrinsic* constraints. Example property is that double-reversing a list is the identity function.

### Higher-order functions on lists

```fsharp
let rec map f l =
    match l with
        | [] -> []
        | hd :: tl -> f hd :: map f tl
```

The type of `map` is

```fsharp
    val map: ('a -> 'b) -> list 'a -> list 'b
```

which, more explicitly, is

```fsharp
    val map: ('a -> ML 'b) -> Tot (list 'a -> ML (list 'b))
```

It is possible to specify *different* type:
```fsharp
val map: ('a -> Tot 'b) -> list 'a -> Tot (list 'b)
```
which is not same at all.

**Not solved `4f`.**
