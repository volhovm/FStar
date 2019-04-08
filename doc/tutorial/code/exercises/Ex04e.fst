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
module Ex04e
//find

open FStar.Exn
open FStar.All

type option 'a =
   | None : option 'a
   | Some : v:'a -> option 'a

val satisfies: ('a -> bool) -> option 'a -> bool
let satisfies f x = match x with
  | None -> true
  | Some y -> f y

val find: f:('a -> bool) -> list 'a -> res:(option 'a){satisfies f res }
let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

val isSome : option 'a -> bool
let isSome x = match x with
  | None -> false
  | Some _ -> true

exception FromSomeException
val fromSome : option 'a -> ML 'a
let fromSome x = match x with
  | None -> raise FromSomeException
  | Some x -> x


val find_satisfies : #a:eqtype -> b:a -> f:(a -> bool) -> l:(list a) ->
                     Lemma (requires (find f l = Some b))
                           (ensures (f b))
let find_satisfies #a b f l = ()

val find_satisfies2 : #a:eqtype -> f:(a -> bool) -> l:(list a) ->
                     Lemma (match find f l with
                              | None -> true
                              | Some x -> f x)
let find_satisfies2 #a f l = ()
