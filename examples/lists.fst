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

val snocCons: l:list 'a -> h: 'a -> Lemma (reverse (snoc l h) = h::reverse l)
let rec snocCons l h =
  match l with
    | [] -> ()
    | hd :: tl -> snocCons tl h

val revInvolutive: l: list 'a -> Lemma (reverse (reverse l) = l)
let rec revInvolutive l =
  match l with
    | [] -> ()
    | hd :: tl -> revInvolutive tl; snocCons (reverse tl) hd

(* val revInjective: l1: list 'a -> l2: list 'a ->
  Lemma
  (requires (reverse l1 = reverse l2))
  (ensures (l1 = l2))
let rec revInjective l1 l2 = revInvolutive l1; revInvolutive l2 *)


val find: f: ('a -> Tot bool) -> list 'a -> Tot (option (x: 'a{f x}))
let rec find f l =
  match l with
    | [] -> None
    | hd :: tl -> if f hd then Some hd else find f tl


val find' : f:('a -> Tot bool) -> list 'a -> Tot (option 'a)
let rec find' f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find' f tl


val findPredicate: f: ('a -> Tot bool) -> l: list 'a -> x: 'a ->
  Lemma (requires (find' f l = Some x)) (ensures (f x))
let rec findPredicate f l x =
  match l with
    | [] -> ()
    | hd :: tl -> if f hd then () else findPredicate f tl x


val foldl: ('a -> 'b -> 'b) -> list 'a -> 'b -> 'b
let rec foldl f l acc =
  match l with
    | [] -> acc
    | hd :: tl -> foldl f tl (f hd acc)


val foldlConsIsReverse: l: list 'a -> l': list 'a ->
  Lemma (foldl Cons l l' = append (reverse l) l')
let rec foldlConsIsReverse l l' =
  match l with
    | [] -> ()
    | hd :: tl -> foldlConsIsReverse tl l'