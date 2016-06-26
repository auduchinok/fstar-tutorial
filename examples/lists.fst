module Lists

open FStar.List

type nat = x:int{x>=0}


(* Example list type definition *)
type myList 'a =
  | Nil  : myList 'a
  | Cons : hd: 'a -> tl: myList 'a -> myList 'a


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
    | [] -> match l2 with
              | [] -> ()
              | hd :: tl -> appendMem [] tl a


(* given solution, why is it enough? *)
val appendMemGiven: l1: list 'a -> l2: list 'a -> a: 'a -> Lemma (mem a (append l1 l2) <==> mem a l1 || mem a l2)
let rec appendMemGiven l1 l2 a =
  match l1 with
    | [] -> ()
    | hd :: tl -> appendMemGiven tl l2 a


val reverse: l: list 'a -> Tot (list 'a)
let rec reverse = function
  | [] -> []
  | hd :: tl -> append (reverse tl) [hd]


let snoc l h = append l [h]

