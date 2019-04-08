(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Ex06a
//partition



val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val length: list 'a -> Tot nat
let rec length = function
  | [] -> 0
  | _::tl -> 1 + length tl


(* Exercise: Write the partition function and prove it total.  *)
val partition: ('a -> Tot bool) -> l:(list 'a) ->
         (Tot (res:(list 'a * list 'a){length (fst res) <= length l && length (snd res) <= length l}))
let rec partition f l = match l with
  | [] -> ([],[])
  | x::xs -> let (l1,l2) = partition f xs in if f x then (x::l1,l2) else (l,x::l2)


val sort : l:(list int) -> Tot (list int) (decreases (length l))
let rec sort l = match l with
  | [] -> []
  | pivot :: tl ->
    let hi, lo  = partition (fun x -> pivot <= x) tl in
    append (sort lo) (pivot :: sort hi)
