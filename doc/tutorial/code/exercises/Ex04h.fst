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
module Ex04h
//nth

(* Write a function that returns the `n`th element of a list. Give a
   type that ensures it is total. *)

val len: list 'a -> nat
let rec len l = match l with
  | [] -> 0
  | x::xs -> 1 + len xs

val list_at : l:list 'a -> x:nat{x < len l} -> Tot 'a
let rec list_at l i = match (l,i) with
  | (x::_, 0) -> x
  | (_::xs,_) -> list_at xs (i-1)
