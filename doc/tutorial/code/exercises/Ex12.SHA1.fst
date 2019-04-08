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
module Ex12.SHA1

open FStar.All
open FStar.Seq
open FStar.Bytes
open CoreCrypto

module U8 =  FStar.UInt8
module U32 =  FStar.UInt32

type text  = bytes    (* a type abbreviation, for clarity *)


(* we rely on some external crypto library implementing HMAC-SHA1 *)

let keysize = 16
let blocksize = keysize
let macsize = 20

type key = lbytes keysize
type tag = bytes //lbytes macsize

val sample: n:nat -> ML (lbytes n)
let sample n = random n

val sha1 : bytes -> Tot (h:bytes{length h = 20})
let sha1 b = hash SHA1 b

val hmac_sha1: key -> t:text{length t < keysize} -> Tot tag
let hmac_sha1 k t =
  let x5c = U8.uint_to_t 92 in
  let x36= U8.uint_to_t 54 in
  let opad = create (U32.uint_to_t blocksize) x5c in
  let ipad = create (U32.uint_to_t blocksize) x36 in
  let (xor_key_opad: lbytes keysize) = xor (U32.uint_to_t keysize) k opad in
  let (xor_key_ipad: lbytes keysize) = xor (U32.uint_to_t keysize) k ipad in
  sha1 ( xor_key_opad @|
                (sha1 (xor_key_ipad @| t))
       )
