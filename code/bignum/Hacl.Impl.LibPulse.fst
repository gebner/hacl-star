module Hacl.Impl.LibPulse
#lang-pulse
open Pulse

open FStar.Mul

open Lib.IntTypes

module LSeq = Lib.Sequence
module Loops = Lib.LoopCombinators

module S = Hacl.Spec.Lib

module AP = Pulse.Lib.ArrayPtr

inline_for_extraction
let fill_elems_impl_ty
  (#t:Type0)
  (#a:Type0)
  (n:size_t)
  (output:AP.ptr t) //lbuffer t n
  (spec: erased (i:size_nat{i < v n} -> a -> a & t))
  (refl: (i:size_nat{i <= v n} -> a -> slprop)) =
  (i:size_t{v i < v n} -> #vr: erased a -> #vo: erased (Seq.seq t) { Seq.length vo == v n } -> stt unit
      (requires refl (v i) vr ** pts_to output vo)
      (ensures fun _ ->
        refl (v i + 1) (fst (reveal spec (v i) vr)) **
        pts_to output (Seq.upd vo (v i) (snd (reveal spec (v i) vr)))))

inline_for_extraction noextract
let fill_elems_st =
  #t:Type0
  -> #a:Type0
  -> n:size_t
  -> output:AP.ptr t //lbuffer t n
  -> refl: (i:size_nat{i <= v n} -> a -> slprop)
  -> spec: erased (i:size_nat{i < v n} -> a -> a & t)
  -> impl: fill_elems_impl_ty n output spec refl ->
  #vr: a ->
  stt unit
    (requires refl 0 vr ** (exists* vo. pts_to output vo ** pure (Seq.length vo == v n)))
    (ensures fun _ ->
      refl (v n) (fst (S.generate_elems (v n) (v n) spec vr)) **
      pts_to output (snd (S.generate_elems (v n) (v n) spec vr)))

inline_for_extraction noextract
fn fill_elems' () : fill_elems_st = #t #a n output refl spec impl #vr {
  let mut i = (uint 0 <: size_t);
  S.eq_generate_elems0 (v n) 0 spec vr;
  rewrite refl 0 vr as 
    refl (v (mk_int 0 <: size_t)) (S.generate_elems (v n) (v (mk_int 0 <: size_t)) spec vr)._1;

  while (let vi = !i; (lt vi n))
    invariant b. exists* (vi: size_t { v vi <= v n })
        (voutput: Seq.seq t { Seq.length voutput == v n }) vr'.
      pts_to i vi ** pts_to output voutput **
      refl (v vi) vr' **
      pure (vr' == (S.generate_elems (v n) (v vi) spec vr)._1) **
      pure (forall (j: nat { j < v vi }).
        Seq.index voutput j ==
          Seq.index (snd (S.generate_elems (v n) (v vi) spec vr)) j) **
      pure (b == (lt vi n))
  {
    let vi = !i;
    with vi'. assert pts_to i vi'; rewrite each vi' as vi;
    S.generate_elems_unfold (v n) (v n) spec vr (v vi);
    with voutput. assert pts_to output voutput;
    with vr'. assert refl (v vi) vr';
    let x = impl vi;
    with vr''. rewrite refl (v vi + 1) vr'' as refl (v (add vi (mk_int 1))) vr'';
    i := add vi (uint 1);
  };
  with vi. assert pts_to i vi;
  with voutput. assert pts_to output voutput ** pure (voutput `Seq.equal` snd (S.generate_elems (v n) (v n) spec vr));
  with vr'. rewrite refl (v vi) vr' as
    refl (v n) (fst (S.generate_elems (v n) (v n) spec vr));
}

inline_for_extraction noextract
let fill_elems : fill_elems_st = fill_elems' ()

inline_for_extraction
let fill_elems4 = fill_elems

(*

inline_for_extraction noextract
val fill_blocks4:
    #t:Type0
  -> #a:Type0
  -> h0:mem
  -> n4:size_t{4 * v n4 <= max_size_t}
  -> output:lbuffer t (4ul *! n4)
  -> refl:(mem -> i:size_nat{i <= 4 * v n4} -> GTot a)
  -> footprint:(i:size_nat{i <= 4 * v n4} -> GTot
      (l:B.loc{B.loc_disjoint l (loc output) /\ B.address_liveness_insensitive_locs `B.loc_includes` l}))
  -> spec:(mem -> GTot (i:size_nat{i < 4 * v n4} -> a -> a & t))
  -> impl:(i:size_t{v i < 4 * v n4} -> Stack unit
      (requires fun h ->
	modifies (footprint (v i) |+| loc (gsub output 0ul i)) h0 h)
      (ensures  fun h1 _ h2 ->
	(let block1 = gsub output i 1ul in
	 let c, e = spec h0 (v i) (refl h1 (v i)) in
	 refl h2 (v i + 1) == c /\ LSeq.index (as_seq h2 block1) 0 == e /\
	 footprint (v i + 1) `B.loc_includes` footprint (v i) /\
	 modifies (footprint (v i + 1) |+| (loc block1)) h1 h2))) ->
  Stack unit
    (requires fun h -> h0 == h /\ live h output)
    (ensures  fun _ _ h1 -> modifies (footprint (4 * v n4) |+| loc output) h0 h1 /\
     (let s, o = LSeq.generate_blocks 4 (v n4) (v n4) (Loops.fixed_a a)
       (S.generate_blocks4_f #t #a (v n4) (spec h0)) (refl h0 0) in
      refl h1 (4 * v n4) == s /\ as_seq #_ #t h1 output == o))

let fill_blocks4 #t #a h0 n4 output refl footprint spec impl =
  fill_blocks h0 4ul n4 output (Loops.fixed_a a)
  (fun h i -> refl h (4 * i))
  (fun i -> footprint (4 * i))
  (fun h0 -> S.generate_blocks4_f #t #a (v n4) (spec h0))
  (fun i ->
    let h1 = ST.get () in
    impl (4ul *! i);
    impl (4ul *! i +! 1ul);
    impl (4ul *! i +! 2ul);
    impl (4ul *! i +! 3ul);
    let h2 = ST.get () in
    assert (
      let c0, e0 = spec h0 (4 * v i) (refl h1 (4 * v i)) in
      let c1, e1 = spec h0 (4 * v i + 1) c0 in
      let c2, e2 = spec h0 (4 * v i + 2) c1 in
      let c3, e3 = spec h0 (4 * v i + 3) c2 in
      let res = LSeq.create4 e0 e1 e2 e3 in
      LSeq.create4_lemma e0 e1 e2 e3;
      let res1 = LSeq.sub (as_seq h2 output) (4 * v i) 4 in
      refl h2 (4 * v i + 4) == c3 /\
      (LSeq.eq_intro res res1; res1 `LSeq.equal` res))
  )


inline_for_extraction noextract
val fill_elems4: fill_elems_st
let fill_elems4 #t #a h0 n output refl footprint spec impl =
  [@inline_let] let k = n /. 4ul in
  let tmp = sub output 0ul (4ul *! k) in
  fill_blocks4 #t #a h0 k tmp refl footprint spec (fun i -> impl i);
  let h1 = ST.get () in
  assert (4 * v k + v (n -! 4ul *! k) = v n);
  B.modifies_buffer_elim (B.gsub #t output (4ul *! k) (n -! 4ul *! k)) (footprint (4 * v k) |+| loc tmp) h0 h1;
  assert (modifies (footprint (4 * v k) |+| loc (gsub output 0ul (4ul *! k))) h0 h1);

  let inv (h:mem) (i:nat{4 * v k <= i /\ i <= v n}) =
    modifies (footprint i |+| loc (gsub output 0ul (size i))) h0 h /\
   (let (c, res) = Loops.repeat_right (v n / 4 * 4) i (S.generate_elem_a t a (v n))
      (S.generate_elem_f (v n) (spec h0)) (refl h1 (4 * v k), as_seq h1 (gsub output 0ul (4ul *! k))) in
    refl h i == c /\ as_seq h (gsub output 0ul (size i)) == res) in

  Loops.eq_repeat_right (v n / 4 * 4) (v n) (S.generate_elem_a t a (v n))
    (S.generate_elem_f (v n) (spec h0)) (refl h1 (4 * v k), as_seq h1 (gsub output 0ul (4ul *! k)));

  Lib.Loops.for (k *! 4ul) n inv
  (fun i ->
    impl i;
    let h = ST.get () in
    assert (v (i +! 1ul) = v i + 1);
    FStar.Seq.lemma_split (as_seq h (gsub output 0ul (i +! 1ul))) (v i);
    Loops.unfold_repeat_right (v n / 4 * 4) (v n) (S.generate_elem_a t a (v n))
      (S.generate_elem_f (v n) (spec h0)) (refl h1 (4 * v k), as_seq h1 (gsub output 0ul (4ul *! k))) (v i)
    );

  S.lemma_generate_elems4 (v n) (v n) (spec h0) (refl h0 0)


inline_for_extraction noextract
val lemma_eq_disjoint:
    #a1:Type
  -> #a2:Type
  -> #a3:Type
  -> clen1:size_t
  -> clen2:size_t
  -> clen3:size_t
  -> b1:lbuffer a1 clen1
  -> b2:lbuffer a2 clen2
  -> b3:lbuffer a3 clen3
  -> n:size_t{v n < v clen2 /\ v n < v clen1}
  -> h0:mem
  -> h1:mem -> Lemma
  (requires
    live h0 b1 /\ live h0 b2 /\ live h0 b3 /\
    eq_or_disjoint b1 b2 /\ disjoint b1 b3 /\ disjoint b2 b3 /\
    modifies (loc (gsub b1 0ul n) |+| loc b3) h0 h1)
  (ensures
    (let b2s = gsub b2 n (clen2 -! n) in
    as_seq h0 b2s == as_seq h1 b2s /\
    Seq.index (as_seq h0 b2) (v n) == Seq.index (as_seq h1 b2) (v n)))

let lemma_eq_disjoint #a1 #a2 #a3 clen1 clen2 clen3 b1 b2 b3 n h0 h1 =
  let b1s = gsub b1 0ul n in
  let b2s = gsub b2 0ul n in
  assert (modifies (loc b1s |+| loc b3) h0 h1);
  assert (disjoint b1 b2 ==> Seq.equal (as_seq h0 b2) (as_seq h1 b2));
  assert (disjoint b1 b2 ==> Seq.equal (as_seq h0 b2s) (as_seq h1 b2s));
  assert (Seq.index (as_seq h1 b2) (v n) == Seq.index (as_seq h1 (gsub b2 n (clen2 -! n))) 0)


inline_for_extraction noextract
val update_sub_f_carry:
    #a:Type
  -> #b:Type
  -> #len:size_t
  -> h0:mem
  -> buf:lbuffer a len
  -> start:size_t
  -> n:size_t{v start + v n <= v len}
  -> spec:(mem -> GTot (b & Seq.lseq a (v n)))
  -> f:(unit -> Stack b
      (requires fun h -> h0 == h)
      (ensures  fun _ r h1 ->
       (let b = gsub buf start n in modifies (loc b) h0 h1 /\
       (let (c, res) = spec h0 in r == c /\ as_seq h1 b == res)))) ->
  Stack b
    (requires fun h -> h0 == h /\ live h buf)
    (ensures  fun h0 r h1 -> modifies (loc buf) h0 h1 /\
     (let (c, res) = spec h0 in r == c /\
     as_seq h1 buf == LSeq.update_sub #a #(v len) (as_seq h0 buf) (v start) (v n) res))

let update_sub_f_carry #a #b #len h0 buf start n spec f =
  let tmp = sub buf start n in
  let h0 = ST.get () in
  let r = f () in
  let h1 = ST.get () in
  assert (v (len -! (start +! n)) == v len - v (start +! n));
  B.modifies_buffer_elim (B.gsub #a buf 0ul start) (loc tmp) h0 h1;
  B.modifies_buffer_elim (B.gsub #a buf (start +! n) (len -! (start +! n))) (loc tmp) h0 h1;
  LSeq.lemma_update_sub (as_seq h0 buf) (v start) (v n) (snd (spec h0)) (as_seq h1 buf);
  r

*)