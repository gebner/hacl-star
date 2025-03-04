module Hacl.Bignum.MultiplicationPulse
#lang-pulse
open Pulse

open Lib.IntTypes

open Hacl.Bignum.DefinitionsPulse
open Hacl.Bignum.BasePulse
open Hacl.Impl.LibPulse

module LSeq = Lib.Sequence
module S = Hacl.Spec.Bignum.Multiplication
module SS = Hacl.Spec.Bignum.Squaring
module SL = Hacl.Spec.Lib
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse

inline_for_extraction let sizet_of_size_t (x: size_t) : y:SizeT.t { v x == SizeT.v y } =
  assume SizeT.fits_u32;
  SizeT.uint32_to_sizet x

inline_for_extraction noextract
fn bn_mul1
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (l:limb t)
  (res:lbignum t aLen)
  (#va: (SD.lbignum t (v aLen)))
  requires pts_to a (va)
  requires exists* res0. pts_to res res0
  returns c_out: limb t
  ensures pts_to res (snd (S.bn_mul1 va l))
  ensures pts_to a (va)
  ensures pure (c_out == fst (S.bn_mul1 va l))
{
  let mut c = (uint #t 0 <: limb t);

  with body_ty. assert pure (body_ty ==
    fill_elems_impl_ty aLen res (S.bn_mul1_f va l)
      fun i x -> pts_to c x ** pts_to a va);
  fn body () : body_ty = i #vr #vo {
    let a_i = AP.(a.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c0 = !c;
    assert pure (c0 == vr);
    let c0' = mul_wide_add_st a_i l c0 res_i;
    c := c0';
    AR.from_array_ptr_return res_i;
  };

  fill_elems4 aLen res _ _ (body ());
  !c
}

inline_for_extraction noextract
fn bn_mul1_add_in_place
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (l:limb t)
  (res:lbignum t aLen)
  #va
  requires pts_to a va
  requires exists* vres. pts_to res vres
  returns c_out: limb t
  ensures pts_to a va
  ensures pts_to res (snd (S.bn_mul1_add_in_place va l vres))
  ensures pure (c_out == fst (S.bn_mul1_add_in_place va l vres))
{
  let mut c = (uint #t 0 <: limb t);

  with body_ty. assert pure (body_ty ==
    fill_elems_impl_ty aLen res (S.bn_mul1_add_in_place_f va l vres)
      fun i x -> pts_to c x ** pts_to a va);
  fn body () : body_ty = i #vr #vo {
    let a_i = AP.(a.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c0 = !c;
    assert pure (c0 == vr);
    let c0' = mul_wide_add2_st a_i l c0 res_i;
    c := c0';
    AR.from_array_ptr_return res_i;
  };

  fill_elems4 aLen res _ _ (body ());
  !c
}

inline_for_extraction noextract
fn bn_mul1_lshift_add
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (b_j:limb t)
  (resLen:size_t)
  (j:size_t{v j + v aLen <= v resLen})
  (res:lbignum t resLen)
  #va
  #vres
  requires pts_to a va
  requires exists* res_vres. pts_to res res_vres
  returns c_out: limb t
  ensures pts_to a va
  ensures pts_to res (snd (S.bn_mul1_lshift_add va b_j (v j) res_vres))
  ensures pure (c_out == fst (S.bn_mul1_lshift_add va b_j (v j) res_vres))
{
  let res_j = AP.split res (sizet_of_size_t j);
  let res0: lbignum t aLen = coerce_eq () res_j; rewrite each res_j as res0;
  let c_out = bn_mul1_add_in_place aLen a b_j res0;
  AP.join res_j res; rewrite each res_j as res;
  c_out
}

inline_for_extraction noextract
let bn_mul_st (t:limb_t) =
    aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum t bLen
  -> res:lbignum t (aLen +! bLen)
  -> #va: _
  -> #vb: _
  -> #vres: _
  -> stt unit
  (requires pts_to a va ** pts_to b vb ** pts_to res vres)
  (ensures fun _ -> pts_to a va ** pts_to b vb ** pts_to res (S.bn_mul va vb))

inline_for_extraction noextract
fn bn_mul (#t:limb_t) : bn_mul_st t = aLen a bLen b res #va #vb #vres {
  memset res (uint #t 0) (aLen +! bLen);
  let h0 = ST.get () in
  fill_elems4 bLen res _ _ 
  (fun j ->
    let bj = AP.(b.(sizet_of_size_t j));
    let c0 = bn_mul1_lshift_add aLen a bj (aLen +! bLen) j res;
    c0
  )
}

[@CInline]
let bn_mul_u32 : bn_mul_st U32 = bn_mul
[@CInline]
let bn_mul_u64 : bn_mul_st U64 = bn_mul

inline_for_extraction noextract
let bn_mul_u (#t:limb_t) : bn_mul_st t =
  match t with
  | U32 -> bn_mul_u32
  | U64 -> bn_mul_u64

inline_for_extraction noextract
fn bn_sqr_diag
  (#t:limb_t)
  (aLen:size_t{v aLen + v aLen <= max_size_t})
  (a:lbignum t aLen)
  (res:lbignum t (aLen +! aLen))
  #va
  #vres
  requires pts_to a va
  requires pts_to res vres
  ensures pts_to res (SS.bn_sqr_diag va)
  ensures pts_to a va
{
  let h0 = ST.get () in
  fill_elems4 aLen res _ _ 
  (fun i ->
    let (hi, lo) = mul_wide (AP.(a.(sizet_of_size_t i))) (AP.(a.(sizet_of_size_t i)));
    AR.to_array_ptr res (2ul *! i) lo;
    AR.to_array_ptr res ((2ul *! i) +! 1ul) hi;
  )
}

inline_for_extraction noextract
let bn_sqr_st (t:limb_t) =
    aLen:size_t{0 < v aLen /\ v aLen + v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> res:lbignum t (aLen +! aLen)
  -> #va: _
  -> #vres: _
  -> stt unit
  (requires pts_to a va ** pts_to res vres)
  (ensures fun _ -> pts_to a va ** pts_to res (SS.bn_sqr va))

inline_for_extraction noextract
fn bn_sqr (#t:limb_t) : bn_sqr_st t = aLen a res #va #vres {
  memset res (uint #t 0) (aLen +! aLen);
  
  fill_elems4 aLen res _ _ 
  (fun j ->
    let ab = AP.split a (sizet_of_size_t j);
    let a_j = AP.(a.(sizet_of_size_t j));
    let c0 = bn_mul1_lshift_add j ab a_j (aLen +! aLen) j res;
    let res_v = SS.bn_sqr_diag va in
    res_v
  );

  let tmp = create (aLen +! aLen) (uint #t 0) in
  bn_sqr_diag aLen a tmp;
  let c1 = Hacl.Bignum.AdditionPulse.bn_add_eq_len (aLen +! aLen) res tmp res in
  ignore c1;
  ()
}

[@CInline]
let bn_sqr_u32 : bn_sqr_st U32 = bn_sqr
[@CInline]
let bn_sqr_u64 : bn_sqr_st U64 = bn_sqr

inline_for_extraction noextract
let bn_sqr_u (#t:limb_t) : bn_sqr_st t =
  match t with
  | U32 -> bn_sqr_u32
  | U64 -> bn_sqr_u64