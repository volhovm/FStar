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
module Ex06b
//quick-sort-poly

open FStar.Option
open FStar.Classical

//////////////// Comparisons

type total_order (a:eqtype) (f: (a -> a -> Tot bool)) =
   (forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2)  (* anti-symmetry *)
 /\ (forall a1 a2 a3. f a1 a2 /\ f a2 a3 ==> f a1 a3)   (* transitivity  *)
 /\ (forall a1 a2. f a1 a2 \/ f a2 a1)                 (* totality      *)

type cmp (a:eqtype) = f:(a -> a -> Tot bool){total_order a f}

val order_rev: #a:eqtype -> c:(cmp a) -> x:a -> y:a ->
  Lemma (ensures (not (c x y) ==> c y x))
let order_rev #a c x y = ()


/////////////////////


val mem: #t:eqtype -> t -> list t -> Tot bool
let rec mem #t a l = match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl

val numocc: #a:eqtype -> a -> list a -> nat
let rec numocc #a e l = match l with
  | [] -> 0
  | x::xs -> (if x = e then 1 else 0) + numocc #a e xs

val numocc_to_mem: #a:eqtype -> e:a -> l:list a -> m:bool{(numocc #a e l > 0) = m /\ mem e l = m}
let rec numocc_to_mem #a e l = match l with
  | [] -> false
  | x::xs -> x = e || numocc_to_mem #a e xs

val numocc_is_mem: #a:eqtype -> e:a -> l:list a ->
  Lemma (numocc #a e l > 0 = mem e l)
let numocc_is_mem #a e l =
  let m = numocc_to_mem #a e l in
  assert((numocc #a e l > 0) = m /\ mem e l = m)

val numocc_is_mem1: #a:eqtype -> e:a -> l1:list a -> l2:list a ->
  GTot (u:unit{numocc e l1 = numocc e l2 ==> mem e l1 = mem e l2})
let rec numocc_is_mem1 #a e l1 l2 = numocc_is_mem #a e l1; numocc_is_mem #a e l2


val numocc_is_mem2: #a:eqtype -> l1:list a -> l2:list a ->
  Lemma (ensures (forall e. numocc e l1 = numocc e l2 ==> mem e l1 = mem e l2))
  [SMTPat (forall e. numocc e l1 = numocc e l2)]
let numocc_is_mem2 #a l1 l2 =
  forall_intro_gtot (fun e -> numocc_is_mem1 e l1 l2)



val append : list 'a -> list 'a -> Tot (list 'a)
let rec append l1 l2 = match l1 with
  | [] -> l2
  | hd :: tl -> hd :: append tl l2


val append_numocc:
       #t:eqtype
    -> l1:list t
    -> l2:list t
    -> Lemma (requires True)
             (ensures (forall a. numocc a (append l1 l2) = (numocc a l1 + numocc a l2)))
             [SMTPat (append l1 l2)]
let rec append_numocc #t l1 l2 = match l1 with
  | [] -> ()
  | hd::tl -> append_numocc tl l2


val length: list 'a -> Tot nat
let rec length l = match l with
  | [] -> 0
  | _ :: tl -> 1 + length tl


val sorted0: list int -> Tot bool
let rec sorted0 l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> x <= y && sorted0 (y::xs)


val sorted: #a:eqtype -> cmp a -> list a -> Tot bool
let rec sorted #a c l = match l with
    | [] -> true
    | [x] -> true
    | x::y::xs -> c x y && sorted #a c (y::xs)


val partition: ('a -> Tot bool) -> list 'a -> Tot (list 'a * list 'a)
let rec partition f = function
  | [] -> [], []
  | hd::tl ->
     let l1, l2 = partition f tl in
     if f hd
     then hd::l1, l2
     else l1, hd::l2


val partition_lemma: #t:eqtype -> f:(t -> Tot bool)
   -> l:list t
   -> Lemma (requires True)
            (ensures ((length (fst (partition f l))
                     + length (snd (partition f l)) = length l
                  /\ (forall x. mem x (fst (partition f l)) ==> f x)
                  /\ (forall x. mem x (snd (partition f l)) ==> not (f x))
                  /\ (forall x. numocc x l =
                                numocc x (fst (partition f l)) +
                                numocc x (snd (partition f l))))))
            [SMTPat (partition f l)]
let rec partition_lemma #t f l = match l with
    | [] -> ()
    | hd::tl -> partition_lemma f tl


val sorted_concat_lemma0:
       l1:list int{sorted0 l1}
    -> l2:list int{sorted0 l2}
    -> pivot:int
    -> Lemma (requires ((forall y. mem y l1 ==> not (pivot <= y))
                     /\ (forall y. mem y l2 ==> pivot <= y)))
             (ensures (sorted0 (append l1 (pivot::l2))))
             [SMTPat (sorted0 (append l1 (pivot::l2)))]
let rec sorted_concat_lemma0 l1 l2 pivot = match l1 with
    | [] -> ()
    | hd::hd2::tl -> sorted_concat_lemma0 tl l2 pivot; assert (hd <= hd2)
    | hd::tl -> sorted_concat_lemma0 tl l2 pivot; assert (hd <= pivot)

val sorted_concat_lemma:
       #a:eqtype
    -> c:(cmp a)
    -> l1:list a{sorted c l1}
    -> l2:list a{sorted c l2}
    -> pivot:a
    -> Lemma (requires ((forall y. mem y l1 ==> not (c pivot y))
                     /\ (forall y. mem y l2 ==> c pivot y)))
             (ensures (sorted c (append l1 (pivot::l2))))
             [SMTPat (sorted c (append l1 (pivot::l2)))]
let rec sorted_concat_lemma #a c l1 l2 pivot = match l1 with
    | [] -> ()
    | [hd] -> sorted_concat_lemma #a c [] l2 pivot;
              order_rev #a c pivot hd
    | hd::hd'::tl' -> sorted_concat_lemma #a c (hd'::tl') l2 pivot

#set-options "--z3rlimit 90 --initial_fuel 5 --max_fuel 5 --initial_ifuel 2 --max_ifuel 2"

val sort: #a:eqtype -> c:(cmp a) -> l:list a ->
          Tot ( m:list a{ sorted c m /\
                          (forall i. numocc i l = numocc i m) })
              (decreases (length l))
let rec sort #a c l = match l with
  | [] -> []
  | pivot::tl ->
    let hi, lo = partition (fun j -> c pivot j) tl in
    let los = sort #a c lo in
    let his = sort #a c hi in
    let m = append los (pivot::his) in

    numocc_is_mem2 los lo;
    numocc_is_mem2 his hi;
    assert(forall i. mem i los = mem i lo);
    assert(forall i. mem i his = mem i hi);

    sorted_concat_lemma #a c los his pivot;
    assert (sorted c m);


    // Numocc
    assert (forall i. numocc i los = numocc i lo);
    assert (forall i. numocc i his = numocc i hi);
    assert (forall i. numocc i l = numocc i lo + numocc i [pivot] + numocc i hi);
    assert (forall i. numocc i m = numocc i los + numocc i (pivot::his));
    assert (forall i. numocc i m = numocc i lo + numocc i [pivot] + numocc i hi);
    assert (forall i. numocc i m = numocc i l);
    assert (forall i. numocc i l = numocc i m);


    assert (sorted c m /\ (forall i. numocc i l = numocc i m));


    m
