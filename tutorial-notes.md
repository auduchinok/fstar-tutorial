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

### Infered types and effects

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
Function arguments cannot have any side effect, thus only function result has it.

Default effect type for non-Tot is ML.

```fsharp
let rec loop i = i + loop (i - 1) (* will be infered to (int -> ML int) or just (int -> int) *)
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
val factIsPositive : x:nat -> (u:unit{fact x > 0})
let rec factIsPositive n =
  match n with
  | 0 -> ()
  | _ -> factIsPositive (n - 1)
```
Lemma has a *dependent function type* because the type of its result depends on the value of the parameter.

The type of the result of `factIsPositive 0`, `Tot (u:unit{fact 0 > 0})`, is different from the result of `factIsPositive 1`.

```fsharp
(* More general function definition *)
x1:t1 -> x2:t2 -> ... -> xn:tn[x1 ... xn-1] -> E t[x1 ... xn]
```

Each function parameter `xi` can freely appear in its scope after the first arrow following `xi`. `t[x1 .. xn]` shows that in definition.

### Syntax sugar for refinement types and lemmas

```fsharp
(* full type *)
val factIsIncreasing : x:(y:nat{x > 2}) -> GTot (u:unit{fact x > x})

(* simplify parameter *)
val factIsIncreasing : x:nat{x > 2} -> GTot (u:unit{fact x > x})

(* use lemma keyword *)
val factIsIncreasion : x:nat{x > 2} -> Lemma (fact x > x)

(* use pre- & post- conditions *)
val factIsIncreasing : x:nat -> Lemma (requires (x > 2)) (ensures (fact x > x))

let rec factIsIncreasing n =
  match n with
  | 3 -> ()
  | _ -> factIsIncreasing (n - 1)
```

F* ensures that recursive calls in Tot function will terminate:

```fsharp
let factIsIncreasing : n:nat{2 < n && n < x} -> Lemma (fact n > n)
```

Another inductional prove example:

```fsharp
val fib : nat -> Tot pos
let rec fib n =
  if n <= 1 then 1 else fib (n - 1) + fib (n - 2)
  
val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibIsIncreasing n =
  match n with
  | 2 -> ()
  | _ -> fibIsIncreasing (n - 1)
  
  (* induction step simplified *)
  val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibIsIncreasing n =
  match n with
  | 2 -> ()
  | _ -> admit()
  
  (* or even automatically, experimental *)
    val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
  let rec fibIsIncreasing n = by_induction_on n fibIsIncreasing
```
