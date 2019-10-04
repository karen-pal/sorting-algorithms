(*
Made by: Karen A. Palacio, 2019.
*)
module SelectionSort
open FStar.List.Tot
open SelSort

(*The minimum of a list*)
val minimum : l1 : list int{length l1 >= 1} -> Pure int (requires True) (ensures (fun r ->(forall x. (mem x l1) ==> r<=x) /\ mem r l1))
(decreases (length l1))
let rec minimum l1 = match l1 with
                  | [x] -> x
                  | x::y::xs -> if x<y then minimum (x::xs)
                              else minimum (y::xs)

(*Erase an element of a list.
Since erase will be called with the minimum of a given list as i, i will always belong to l1 and the length of the resulting list will be strictly less than the length of the original.
Also it will not be called with l1 = [] *)

val erase : i:int -> l1: list int -> Pure (list int)
 (requires mem i l1)
 (ensures (fun r -> permutation l1 (i::r)))
let rec erase m l = match l with
                 |[x] -> []
                 |x::xs ->
                   if m=x then xs
                   else x::erase m xs

val memcountLemma: y:int -> xs: list int -> 
  Lemma (ensures mem y xs <==> count y xs > 0)
        [SMTPat (mem y xs); SMTPat (count y xs) ]

let rec memcountLemma y xs =
  match xs with
    | [] -> ()
    | x::xs' -> memcountLemma y xs'

(*The selection sort algorithm*)
val selsort : l:list int -> Pure (list int) (requires True) 
            (ensures (fun r -> sorted r /\ permutation l r)) (decreases (length l))

let rec selsort l = match l with
    |[] -> []
    |x::xs -> let list = x::xs in
      let min = minimum list in
      let rest = erase min list in
      min::selsort rest
