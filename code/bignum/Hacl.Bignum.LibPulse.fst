module Hacl.Bignum.LibPulse
#lang-pulse
open Pulse

open Lib.IntTypes

open Hacl.Bignum.BasePulse
open Hacl.Bignum.DefinitionsPulse

module S = Hacl.Spec.Bignum.Lib
module SD = Hacl.Spec.Bignum.Definitions
module SL = Hacl.Spec.Lib
module LSeq = Lib.Sequence
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse
module Loops = Lib.LoopCombinators

inline_for_extraction let sizet_of_size_t (x: size_t) : y:SizeT.t { v x == SizeT.v y } =
  assume SizeT.fits_u32;
  SizeT.uint32_to_sizet x

///
///  Get and set i-th bit of a bignum
///

inline_for_extraction noextract
fn bn_get_ith_bit
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t{v i / bits t < v len})
  (#b0: erased (SD.lbignum t (v len))) #prb
  requires pts_to b #prb b0
  returns r:limb t
  ensures pts_to b #prb b0
  ensures pure (r == S.bn_get_ith_bit (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  let j = i %. pbits;
  let tmp = AP.(b.(sizet_of_size_t i_ind));
  ((tmp >>. j) &. (uint #t 1))
}

inline_for_extraction noextract
fn bn_set_ith_bit
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t{v i / bits t < v len})
  (#b0: erased (SD.lbignum t (v len)))
  requires pts_to b (b0)
  ensures pts_to b (S.bn_set_ith_bit (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  assert pure (v i_ind < v len); // Z3 fails nondeterministically without this
  let j = i %. pbits;
  let b_i_ind = AP.(b.(sizet_of_size_t i_ind));
  AP.(b.(sizet_of_size_t i_ind) <- b_i_ind |. (uint #t 1 <<. j));
}

inline_for_extraction noextract
fn cswap2_st
  (#t:limb_t)
  (len:size_t)
  (bit:limb t)
  (b1:lbignum t len)
  (b2:lbignum t len)
  (#b1_0: erased (SD.lbignum t (v len)))
  (#b2_0: erased (SD.lbignum t (v len)))
  requires pts_to b1 (b1_0) ** pts_to b2 (b2_0)
  ensures pts_to b1 (fst (S.cswap2 bit b1_0 b2_0)) ** pts_to b2 (snd (S.cswap2 bit b1_0 b2_0))
{
  let mask = (uint #t 0) -. bit;
  let mut i = 0ul;
  Loops.eq_repeati0 0 (S.cswap2_f mask) (reveal b1_0, reveal b2_0);
  while (let vi = !i; lt vi len)
    invariant b. exists* vi vb1 vb2.
      pts_to b1 vb1 ** pts_to b2 vb2 ** pts_to i vi **
      pure (b == lt vi len) **
      pure (v vi <= v len /\
        (vb1, vb2) == Loops.repeati (v vi) (S.cswap2_f mask) (reveal b1_0, reveal b2_0))
  {
    let vi = !i;
    let b1_i = AP.(b1.(sizet_of_size_t vi));
    let b2_i = AP.(b2.(sizet_of_size_t vi));
    let dummy = mask &. (b1_i ^. b2_i);
    AP.(b1.(sizet_of_size_t vi) <- b1_i ^. dummy);
    AP.(b2.(sizet_of_size_t vi) <- b2_i ^. dummy);
    Loops.unfold_repeati (v len) (S.cswap2_f mask) (reveal b1_0, reveal b2_0) (v vi);
    i := add vi 1ul;
  };
}

inline_for_extraction noextract
let bn_get_top_index_st (t:limb_t) (len:size_t{0 < v len}) =
  b:lbignum t len -> #b0: erased (SD.lbignum t (v len)) -> #prb: perm ->
  stt (limb t) (requires pts_to b #prb b0)
    fun r -> pts_to b #prb b0 **
      pure (v r == S.bn_get_top_index b0)

inline_for_extraction noextract
fn mk_bn_get_top_index (#t: limb_t) (len: size_t { 0 < v len }) :
    bn_get_top_index_st t len = b #b0 #prb {
  let mut r = (uint 0 <: limb t);
  with vr0. assert pts_to r vr0;

  with spec. assert pure (spec == S.bn_get_top_index_f b0);
  Loops.eq_repeat_gen0 (v len) (S.bn_get_top_index_t (v len)) spec (v vr0);
  let mut i = 0ul;
  while (let vi = !i; lt vi len)
    invariant cond. exists* vi vr.
      pts_to i vi ** pts_to r vr ** pts_to b #prb b0 **
      pure (cond == lt vi len) **
      pure (v vi <= v len /\
        v vr == Loops.repeat_gen (v vi) (S.bn_get_top_index_t (v len)) spec (v vr0))
  {
    let vi = !i;
    Loops.unfold_repeat_gen (v len) (S.bn_get_top_index_t (v len)) spec (v vr0) (v vi);
    let b_i = AP.(b.(sizet_of_size_t vi));
    let mask = eq_mask b_i (zeros t SEC);
    let vr = !r;
    r := mask_select mask vr (size_to_limb vi);
    mask_select_lemma mask vr (size_to_limb vi);
    i := add vi 1ul;
  };

  !r
}

let bn_get_top_index_u32 len: bn_get_top_index_st U32 len = mk_bn_get_top_index #U32 len
let bn_get_top_index_u64 len: bn_get_top_index_st U64 len = mk_bn_get_top_index #U64 len


inline_for_extraction noextract
val bn_get_top_index: #t:_ -> len:_ -> bn_get_top_index_st t len
let bn_get_top_index #t =
  match t with
  | U32 -> bn_get_top_index_u32
  | U64 -> bn_get_top_index_u64


inline_for_extraction noextract
fn bn_get_bits_limb
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t{v i / bits t < v len})
  (#b0: erased (SD.lbignum t (v len))) #prb
  requires pts_to b #prb b0
  returns r:limb t
  ensures pts_to b #prb b0
  ensures pure (r == S.bn_get_bits_limb (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  let j = i %. pbits;
  let b_i_ind = AP.(b.(sizet_of_size_t i_ind));
  let p1 = b_i_ind >>. j;
  if (i_ind +! 1ul <. len && 0ul <. j) {
    let b_ind_1 = AP.(b.(sizet_of_size_t (i_ind +! 1ul)));
    (p1 |. (b_ind_1 <<. (pbits -! j)))
  } else {
    p1
  }
}

inline_for_extraction noextract
fn bn_get_bits
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t)
  (l:size_t{v l < bits t /\ v i / bits t < v len})
  (#b0: erased (SD.lbignum t (v len))) #prb
  requires pts_to b #prb b0
  returns r:limb t
  ensures pts_to b #prb b0
  ensures pure (r == S.bn_get_bits (b0) (v i) (v l))
{
  let mask_l: limb t = (uint #t 1 <<. l) -. (uint #t 1);
  let r = bn_get_bits_limb len b i;
  (r &. mask_l)
}
