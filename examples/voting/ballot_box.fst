(*
   Copyright 2015 Chantal Keller, Microsoft Research and Inria

   Based on work by V. Cortier, F. Eigner, S. Kremer, M. Maffei and C.
   Wiedling <https://sps.cs.uni-saarland.de/voting>.

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


module Ballot_box
open Bytes
open Crypto_interface
open Assumptions

(* -------------- Ballot Box Implementation -------------- *)
let ballotBox pkBB skBB ca cb co e =
  let ba = check_val pkBB ca in
  match ba with
    | false -> e
    | true ->
       let bb = check_val pkBB cb in
       match bb with
	 | false -> e
	 | true ->
	    let bo = check_val pkBB co in
	(* Note: If the intruder send an homo encryption of ca and ca then, bo = false and protocol still typechecks *)
	    match bo with
	      | false -> e
	      | true ->
	         if (co = ca) then e else
	           if (co = cb) then e else
	             let cab = hom_add pkBB ca cb in
	             let cfinal = hom_add pkBB cab co in
	             match dec skBB cfinal with
	               | None -> e
	               | Some mfinal -> mfinal
