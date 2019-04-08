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
module Ex03a
//factorial-types

open FStar.Mul

(* What are some other types you can give to factorial?
   Try writing them and see if F* agrees with you. *)

// BEGIN: FactorialTypes
val factorial: x:nat -> nat
let rec factorial n =
  match n with
    | 0 -> 1
    | _ -> n * (factorial (n - 1))
// END: FactorialTypes


// BEGIN: FactorialTypes
val factorial2: x:int{x>=5} -> Tot int
let rec factorial2 n =
  if n = 5 then factorial 5 else n * (factorial2 (n - 1))
// END: FactorialTypes


val factorial_is_greater_than_arg3: x:nat{x > 2} -> GTot (u:unit{factorial x > x})
let rec factorial_is_greater_than_arg3 x =
  match x with
    | 3 -> ()
    | _ -> factorial_is_greater_than_arg3 (x-1)

val factorial_is_greater_than_arg4: x:nat{x > 0} -> Lemma (factorial x > x)
