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
module Ex04f
//fold-left

val fold_left: f:('b -> 'a -> Tot 'a) -> l:list 'b -> 'a -> Tot 'a
let rec fold_left f l i = match l with
  | [] -> i
  | x :: xs -> fold_left f xs (f x i)
//implement fold_left

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse = function
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

//val list_assoc: l1:list 'a -> l2:list 'a -> l3:list 'a ->
//                Lemma (append (append l1 l2) l3 == append l1 (append l2 l3))
//list_assoc l2 l3 l3 =

val list_assoc_elem: l1:list 'a -> b:'a -> l2:list 'a ->
                Lemma (append l1 (Cons b l2) == append (append l1 [b]) l2)
let rec list_assoc_elem l1 b l2 = match l1 with
  | [] -> ()
  | x :: xs -> list_assoc_elem xs b l2

val fold_left_cons_is_reverse:
       l:list 'a
    -> l':list 'a
    -> Lemma (fold_left Cons l l' == append (reverse l) l')
let rec fold_left_cons_is_reverse l l' = match l with
  | [] -> ()
  | x :: xs -> fold_left_cons_is_reverse xs (Cons x l'); list_assoc_elem (reverse xs) x l'

// fold_left Cons l l'
// fold_left Cons xs (Cons x l')
// append (reverse xs) (Cons x l')
// append (append (reverse xs) [x]) l'
// append (reverse (x::xs)) l'
// append (reverse l) l'
