module Factorial

type nat = x:int{x >= 0}
type pos = x:nat{x >= 1}

val fact : nat -> Tot pos
let rec fact n =
  if n = 0 then 1 else n * fact (n - 1)
  
val factIsPositive : x:nat -> GTot (u:unit{fact x > 0})
let rec factIsPositive n =
  match n with
  | 0 -> ()
  | _ -> factIsPositive (n - 1)
  
val factIsIncreasing : x:(y:nat{y > 2}) -> GTot (u:unit{fact x > x})
val factIsIncreasing : x:nat{x > 2} -> GTot (u:unit{fact x > x})
val factIsIncreasing : x:nat{x > 2} -> Lemma (fact x > x)
let rec factIsIncreasing n =
  match n with
  | 3 -> ()
  | _ -> factIsIncreasing (n - 1)
  
val fib : nat -> Tot pos
let rec fib n =
  if n <= 1 then 1 else fib (n - 1) + fib (n - 2)
  
val fibIsIncreasing : n:nat{n >= 2} -> Lemma (fib n >= n)
let rec fibIsIncreasing n =
  match n with
  | 2 -> ()
  | _ -> fibIsIncreasing (n - 1)
