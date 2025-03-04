module Hacl.Bignum.LibPulse
#lang-pulse
open Pulse

open Lib.IntTypes

open Hacl.Bignum.BasePulse
open Hacl.Bignum.DefinitionsPulse

module S = Hacl.Spec.Bignum.Lib
module SL = Hacl.Spec.Lib
module LSeq = Lib.Sequence
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse

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
  requires pts_to b (b0)
  returns r:limb t
  ensures pts_to b (b0)
  ensures pure (r == S.bn_get_ith_bit (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  let j = i %. pbits;
  let tmp = AP.(b.(sizet_of_size_t i_ind));
  (tmp >>. j) &. (uint #t 1)
}

inline_for_extraction noextract
fn bn_set_ith_bit
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t{v i / bits t < v len})
  requires pts_to b (b0)
  returns ()
  ensures pts_to b (S.bn_set_ith_bit (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  let j = i %. pbits;
  AP.(b.(sizet_of_size_t i_ind)) <- AP.(b.(sizet_of_size_t i_ind)) |. (uint #t 1 <<. j)
}

inline_for_extraction noextract
fn cswap2_st
  (#t:limb_t)
  (len:size_t)
  (bit:limb t)
  (b1:lbignum t len)
  (b2:lbignum t len)
  requires pts_to b1 (b1_0) ** pts_to b2 (b2_0)
  returns ()
  ensures pts_to b1 (fst (S.cswap2 bit b1_0 b2_0)) ** pts_to b2 (snd (S.cswap2 bit b1_0 b2_0))
{
  let mask = (uint #t 0) -. bit;
  let mut i = 0ul;
  let len_sizet = sizet_of_size_t len;
  let body_ty = 
    fun i x1 x2 -> pts_to b1 x1 ** pts_to b2 x2;
  let body () = i #x1 #x2 {
    let dummy = mask &. (AP.(b1.(sizet_of_size_t i)) ^. AP.(b2.(sizet_of_size_t i)));
    AP.(b1.(sizet_of_size_t i)) <- AP.(b1.(sizet_of_size_t i)) ^. dummy;
    AP.(b2.(sizet_of_size_t i)) <- AP.(b2.(sizet_of_size_t i)) ^. dummy;
  };
  fill_elems4 body_ty len_sizet (body ());
}

inline_for_extraction noextract
fn bn_get_top_index
  (#t:limb_t)
  (len:size_t{0 < v len})
  (b:lbignum t len)
  requires pts_to b (b0)
  returns r:limb t
  ensures pts_to b (b0)
  ensures pure (r == S.bn_get_top_index (b0))
{
  let mut r = 0ul;
  let len_sizet = sizet_of_size_t len;
  let body_ty = fun i x0 -> pts_to b x0;
  let body () = i #x0 {
    let mask = eq_mask (AP.(b.(sizet_of_size_t i))) (zeros t SEC);
    r <- mask_select mask r (size_to_limb i);
  };
  fill_elems4 body_ty len_sizet (body ());
  r
}


inline_for_extraction noextract
fn bn_get_bits_limb
  (#t:limb_t)
  (len:size_t)
  (b:lbignum t len)
  (i:size_t{v i / bits t < v len})
  requires pts_to b (b0)
  returns r:limb t
  ensures pts_to b (b0)
  ensures pure (r == S.bn_get_bits_limb (b0) (v i))
{
  let pbits = size (bits t);
  let i_ind = i /. pbits;
  let j = i %. pbits;
  let p1 = AP.(b.(sizet_of_size_t i_ind)) >>. j;
  if (i_ind +! 1ul <. len && 0ul <. j) {
    p1 |. (AP.(b.(sizet_of_size_t (i_ind +! 1ul))) <<. (pbits -! j))
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
  requires pts_to b (b0)
  returns r:limb t
  ensures pts_to b (b0)
  ensures pure (r == S.bn_get_bits (b0) (v i) (v l))
{
  let mask_l = (uint #t 1 <<. l) -. (uint #t 1);
  bn_get_bits_limb len b i &. mask_l
}
