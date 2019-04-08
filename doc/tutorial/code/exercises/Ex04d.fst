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
module Ex04d
//reverse

val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2

val reverse: list 'a -> Tot (list 'a)
let rec reverse l =
  match l with
  | [] -> []
  | hd::tl -> append (reverse tl) [hd]
let snoc l h = append l [h]

val snoc_cons: l:list 'a -> h:'a -> Lemma (reverse (snoc l h) == h::reverse l)
let rec snoc_cons l h = match l with
  | [] -> ()
  | hd::tl -> snoc_cons tl h


val rev_involutive: l:list 'a -> Lemma (reverse (reverse l) == l)
let rec rev_involutive l = match l with
  | [] -> ()
  | hd::tl -> rev_involutive tl; snoc_cons (reverse tl) hd


//val last: l: list 'a -> 'a
//last
//
//val hlp: l1:list 'a -> l2:list 'a
//                -> Lemma (requires (reverse l1 == reverse l2 /\ ))
//                         (ensures (last l1 == last l2))
//let rec hlp l h = match l with
//  | [] -> ()
//  | hd::tl -> snoc_cons tl h


// BEGIN: RevInjective
val rev_injective : l1:list 'a -> l2:list 'a
                -> Lemma (requires (reverse l1 == reverse l2))
                         (ensures  (l1 == l2))
let rec rev_injective l1 l2 = match (l1,l2) with
  | ([],[]) -> ()
  | (x :: xs, y :: ys) ->
    snoc_cons (reverse xs) x;
    snoc_cons (reverse ys) y;
    rev_involutive xs;
    rev_involutive ys;
    rev_injective xs ys

// END: RevInjective

// l1 = x :: xs = x :: rev (rev xs) = x :: rev (rev ys) = {???} = y :: rev (rev ys) = y :: ys = l2
