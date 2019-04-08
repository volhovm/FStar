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
(* to be used with Ex12.MAC.fst and Ex12a.ACLs.fst *)

module Ex12a1.Cap (* capabilities *)

open FStar.ST
open FStar.All
open FStar.Bytes


module ACLs = Ex12a.ACLs
module MAC = Ex12.MAC

// BEGIN: UTF8Inj
assume val utf8: s:string  -> Tot bytes

assume UTF8_inj:
  forall s0 s1.{:pattern (utf8 s0); (utf8 s1)}
     b2t (equalBytes (utf8 s0) (utf8 s1)) ==> s0==s1
// END: UTF8Inj

type capRead (msg:bytes) = (forall f. msg = utf8 f ==> ACLs.canRead f)
type capWrite (msg:bytes) = (forall f. msg = utf8 f ==> ACLs.canWrite f)

let k = MAC.keygen capRead

// BEGIN: CapType
val issueR: f:string{ ACLs.canRead f } -> ML MAC.tag
let issueR f = assert(MAC.key_prop k (utf8 f)); MAC.mac k (utf8 f)

val redeemR: f:string -> m:MAC.tag -> ML (u:unit{ ACLs.canRead f })
let redeemR f m = match MAC.verify k (utf8 f) m with
  | true -> ()
  | false -> failwith "bad capability"
// END: CapType

val k': MAC.pkey capWrite
let k' = MAC.keygen capWrite

val issueW: f:string{ ACLs.canWrite f } -> ML MAC.tag
let issueW f = assert(MAC.key_prop k' (utf8 f)); MAC.mac k' (utf8 f)

val redeemW: f:string -> m:MAC.tag -> ML (u:unit{ ACLs.canWrite f })
let redeemW f m = match MAC.verify k' (utf8 f) m with
  | true -> assert(ACLs.canWrite f)
  | false -> failwith "bad capability"

let test =
  let t1 = issueR "file1" in
  redeemR "file1" t1
