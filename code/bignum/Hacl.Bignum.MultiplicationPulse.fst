module Hacl.Bignum.MultiplicationPulse
#lang-pulse
open Pulse

open Lib.IntTypes

open Hacl.Bignum.DefinitionsPulse
open Hacl.Bignum.BasePulse
open Hacl.Impl.LibPulse

module LSeq = Lib.Sequence
module S = Hacl.Spec.Bignum.Multiplication
module SD = Hacl.Spec.Bignum.Definitions
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
  (#va: erased (SD.lbignum t (v aLen)))
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
  (#va: erased (SD.lbignum t (v aLen)))
  (#vres: erased (SD.lbignum t (v aLen)))
  requires pts_to a va
  requires pts_to res vres
  returns c_out: limb t
  ensures pts_to a va
  ensures pts_to res (snd (S.bn_mul1_add_in_place va l vres))
  ensures pure (c_out == fst (S.bn_mul1_add_in_place va l vres))
{
  let mut c = (uint #t 0 <: limb t);

  with body_ty. assert pure (body_ty ==
    fill_elems_impl_ty aLen res #(fun j x -> x == Seq.index vres j)
      (S.bn_mul1_add_in_place_f va l vres)
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
  (#va: erased (SD.lbignum t (v aLen)))
  (#vres: erased (SD.lbignum t (v resLen)))
  requires pts_to a va
  requires pts_to res vres
  returns c_out: limb t
  ensures pts_to a va
  ensures pts_to res (snd (S.bn_mul1_lshift_add va b_j (v j) vres))
  ensures pure (c_out == fst (S.bn_mul1_lshift_add va b_j (v j) vres))
{
  let res_j = AP.split res (sizet_of_size_t j);
  let res_rest = AP.ghost_split res_j (sizet_of_size_t aLen);
  with vres_j. assert AP.pts_to res_j vres_j;
  let c_out = bn_mul1_add_in_place aLen a b_j res_j;
  AP.join res_j res_rest;
  AP.join res res_j;
  with vres'. assert pts_to res vres';
  LSeq.lemma_update_sub' #(limb t) #(v resLen) vres (v j) (v aLen)
    (snd (S.bn_mul1_add_in_place va b_j vres_j)) vres';
  c_out
}

inline_for_extraction noextract
let bn_mul_st (t:limb_t) =
    aLen:size_t
  -> a:lbignum t aLen
  -> bLen:size_t{v aLen + v bLen <= max_size_t}
  -> b:lbignum t bLen
  -> res:lbignum t (aLen +! bLen)
  -> #va: erased (SD.lbignum t (v aLen))
  -> #vb: erased (SD.lbignum t (v bLen))
  -> #vres: erased (SD.lbignum t (v (aLen +! bLen)))
  -> stt unit
  (requires pts_to a va ** pts_to b vb ** pts_to res vres)
  (ensures fun _ -> pts_to a va ** pts_to b vb ** lbignum_pts_to res (S.bn_mul va vb))

inline_for_extraction noextract
fn bn_mul (#t:limb_t) : bn_mul_st t = aLen a bLen b res #va #vb #vres {
  arrayptr_memset res (uint #t 0) (sizet_of_size_t (aLen +! bLen));
  with vres0. assert pts_to res vres0;
  let mut j = 0ul;
  Lib.LoopCombinators.eq_repeati0 0 (S.bn_mul_ va vb) vres0;
  while (let vj = !j; lt vj bLen)
    invariant cond. exists* vj (vres : SD.lbignum t (v (aLen +! bLen))).
      pts_to j vj ** pts_to res vres ** pts_to b vb ** pts_to a va **
      pure (cond == lt vj bLen) **
      pure (v vj <= v bLen /\
        vres == Lib.LoopCombinators.repeati (v vj) (S.bn_mul_ va vb) vres0)
  {
    let vj = !j;
    j := add vj 1ul;
    let bj = AP.(b.(sizet_of_size_t vj));
    let c0 = bn_mul1_lshift_add aLen a bj (aLen +! bLen) vj res;
    Lib.LoopCombinators.unfold_repeati (v vj + 1) (S.bn_mul_ va vb) vres0 (v vj);
    AP.(res.(sizet_of_size_t (aLen +! vj)) <- c0);
  }
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
  (#va: erased (SD.lbignum t (v aLen)))
  requires pts_to a va
  requires lbignum_pts_to res (Seq.create #(limb t) (v aLen + v aLen) (uint #t 0))
  ensures pts_to res (SS.bn_sqr_diag va <: SD.lbignum t (v (aLen +! aLen)))
  ensures pts_to a va
{
  with vres0. assert pts_to res vres0;
  let mut j = 0ul;
  Lib.LoopCombinators.eq_repeati0 0 (SS.bn_sqr_diag_f va) vres0;
  while (let vj = !j; lt vj aLen)
    invariant cond. exists* vj (vres : SD.lbignum t (v (aLen +! aLen))).
      pts_to j vj ** pts_to res vres ** pts_to a va **
      pure (cond == lt vj aLen) **
      pure (v vj <= v aLen /\
        vres == Lib.LoopCombinators.repeati (v vj) (SS.bn_sqr_diag_f va) vres0)
  {
    let vj = !j;
    let a_j = AP.(a.(sizet_of_size_t vj));
    let (hi, lo) = mul_wide a_j a_j;
    AP.(res.(sizet_of_size_t (2ul *! vj)) <- lo);
    AP.(res.(sizet_of_size_t (2ul *! vj +! 1ul)) <- hi);
    Lib.LoopCombinators.unfold_repeati (v vj + 1) (SS.bn_sqr_diag_f va) vres0 (v vj);
    j := add vj 1ul;
  }
}

inline_for_extraction noextract
let bn_sqr_st (t:limb_t) =
    aLen:size_t{0 < v aLen /\ v aLen + v aLen <= max_size_t}
  -> a:lbignum t aLen
  -> res:lbignum t (aLen +! aLen)
  -> #va: erased (SD.lbignum t (v aLen))
  -> #vres: erased (SD.lbignum t (v (aLen +! aLen)))
  -> stt unit
  (requires pts_to a va ** pts_to res vres)
  (ensures fun _ -> pts_to a va ** pts_to res (SS.bn_sqr va <: SD.lbignum t (v (aLen +! aLen))))

inline_for_extraction noextract
fn bn_sqr (#t:limb_t) : bn_sqr_st t = aLen a res #va #vres {
  with resLen. assert (pure (resLen == aLen +! aLen));
  arrayptr_memset res (uint #t 0) (sizet_of_size_t resLen);
  with vres0. assert pts_to res vres0;

  let mut j = 0ul;
  with spec. assert pure (spec == SS.bn_sqr_f va);
  Lib.LoopCombinators.eq_repeati0 0 spec vres0;
  while (let vj = !j; lt vj aLen)
    invariant cond. exists* vj (vres : SD.lbignum t (v (aLen +! aLen))).
      pts_to j vj ** pts_to res vres ** pts_to a va **
      pure (cond == lt vj aLen) **
      pure (v vj <= v aLen /\
        vres == Lib.LoopCombinators.repeati (v vj) spec vres0)
  {
    let vj = !j;
    let a_j = AP.(a.(sizet_of_size_t vj));
    let a_rest = AP.ghost_split a (sizet_of_size_t vj);
    let ab: lbignum t vj = coerce_eq () a; rewrite each a as ab;
    let res_v = bn_mul1_lshift_add vj ab a_j resLen vj res;
    AP.join ab a_rest; rewrite each ab as a; with va'. assert pts_to a va' ** pure (Seq.equal va' va);
    Lib.LoopCombinators.unfold_repeati (v vj + 1) spec vres0 (v vj);
    AP.(res.(sizet_of_size_t (vj +! vj)) <- res_v);
    j := add vj 1ul;
  };

  let _ = Hacl.Bignum.AdditionPulse.bn_dbl resLen res;

  let mut tmp_arr = [| (uint #t 0 <: limb t); sizet_of_size_t (aLen +! aLen) |];
  let tmp = AP.from_array tmp_arr;
  bn_sqr_diag aLen a tmp;
  with vtmp. assert AP.pts_to tmp vtmp;

  let _ = Hacl.Bignum.AdditionPulse.bn_add_eq_len_inplace (aLen +! aLen) tmp res;

  AP.to_array tmp _ #_ #vtmp;
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