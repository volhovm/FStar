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
module Ex05b
//fibonacci-is-ok


open FStar.Math.Lemmas
open FStar.Mul
open FStar.Squash
open FStar.SquashProperties
open FStar.Classical


// fib 1 1 0 = 1
// fib 1 1 1 = fib 1 2 0 = 1
// fib 1 1 2 = fib 1 2 1 = fib 2 3 0 = 2
// fib 1 1 3 = fib 1 2 2 = fib 2 3 1 = fib 3 5 0 = 3

// fib a b 1 = fib b (a+b) 0 = b
// fib a b 2 = fib b (a+b) 1 = fib (a+b) (a+b+b) 0 = a+b
// fib a b 3 = fib b (a+b) 2 = fib (a+b) (a+b+b) 1 = fib (a+b+b) (a+b+a+b+b) 0 = a+b+b
// fib a b 4 = fib b (a+b) 3 = fib (a+b) (a+b+b) 2 = fib (a+b+b) (a+b+a+b+b) 1 = fib (a+b+a+b+b) (a+b+b+a+b+a+b+b) 0 = (a+b+a+b+b)
// fib a b 5 = fib b (a+b) 4 = fib (a+b) (a+b+b) 3 = fib (a+b+b) (a+b+a+b+b) 2 = fib (a+b+a+b+b) (a+b+b+a+b+a+b+b) 1 = .. = (a+b+b+a+b+a+b+b)
// fib a b 6 = fib b (a+b) 5 = ... = (a+b+b+a+b+a+b+b) + (a+b+a+b+b)

// fib a b n = k1*a + k2*b
// fib a b (n+1) = fib b (a+b) n = k1*b + k2*(a+b)
// (k1 = fib (n-2), k2 = fib (n-1))

// ?
// fib a b 3 = a+b+b
// fib a (a+b) 3 = b+a+b+a+a = a+b+b + 2*a

// ??
// fib a b 4 = 2a + 3b
// fib b (a+b) 4 = 3a + 5b
// fib a (a+b) 4 = 5a + 3b = fib a b 4 + 3b

// ???
// fib a b 5 = 3a + 5b
// fib a (a+b) 5 = 3a + 5b + 5a

// ????
// fib a b 6 = 5a + 8b
// fib b (b+a) 6 = 5a + 8b + 5b
// fib a (a+b) 6 = 8a + 5b + 5a



val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fib : a:nat -> b:nat -> n:nat -> (Tot (r:nat)) (decreases n)
let rec fib a b n =
  match n with
  | 0 -> a
  | _ -> fib b (a+b) (n-1)




type fks = tuple2 nat nat

val isfibks : fks -> nat -> nat -> nat -> bool
let isfibks (k1,k2) a b n =
    fib a b n = k1 * a + k2 * b

val fibks: a:nat -> b:nat -> n:nat -> Tot (ks:fks{isfibks ks a b n}) (decreases n)
let rec fibks a b n = match n with
  | 0 -> (1,0)
  | 1 -> (0,1)
  | 2 -> (1,1)
  | _ -> let (l1,l2) = fibks b (a+b) (n-1) in
         let (k1,k2) = (l2,l1+l2) in
         assert (fib a b n = l1 * b + l2 * (a + b));
         distributivity_add_right l2 a b;
         assert (fib a b n = l1 * b + l2 * a + l2 * b);
         assert (fib a b n = l2 * a + (l1 + l2) * b);
         (k1,k2)

val nextks : fks -> fks
let nextks (k1,k2) = (k2,k1+k2)

val prevks : ks:fks{snd ks >= fst ks} -> fks
let prevks (k1,k2) = (k2-k1,k1)

val k2isfact: a:nat -> b:nat -> n:nat{n>=1} -> ks:fks{ks = fibks a b n} ->
              Lemma (ensures (snd ks = fibonacci (n-1))) (decreases n)
let rec k2isfact a b n (k1,k2) = match n with
  | 1 -> assert (k2 = 1)
  | 2 -> assert (k2 = 1)
  | _ -> assert (n > 1);
         k2isfact b (a+b) (n-1) (prevks (k1,k2));
         assert (k1 = fibonacci (n-2));
         k2isfact (a+b) (a+b+b) (n-2) (prevks (prevks (k1,k2)));
         assert (k2-k1 = fibonacci (n-3));
         assert (k2 = fibonacci (n-1))

val k1isfact: a:nat -> b:nat -> n:nat{n>=2} -> ks:fks{ks = fibks a b n} ->
              Lemma (ensures (fst ks = fibonacci (n-2))) (decreases n)
let rec k1isfact a b n (k1,k2) = match n with
  | 1 -> assert (k1 = 1)
  | 2 -> assert (k1 = 1)
  | _ -> k2isfact b (a+b) (n-1) (prevks (k1,k2));
         k2isfact (a+b) (a+b+b) (n-2) (prevks (prevks (k1,k2)))

val k1plusk2isfact: a:nat -> b:nat -> n:nat{n>=2} -> ks:fks{ks = fibks a b n} ->
              Lemma (ensures (fst ks + snd ks = fibonacci n))
let k1plusk2isfact a b n ks = k1isfact a b n ks; k2isfact a b n ks


val fib_is_ok : n:nat -> Lemma (fib 1 1 n = fibonacci n)
let rec fib_is_ok n = match n with
  | 0 -> ()
  | 1 -> ()
  | _ -> k1plusk2isfact 1 1 n (fibks 1 1 n)
