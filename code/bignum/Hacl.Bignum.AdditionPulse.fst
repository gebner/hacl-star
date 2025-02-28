module Hacl.Bignum.AdditionPulse
#lang-pulse
open Pulse

open FStar.Mul

open Hacl.Bignum.DefinitionsPulse
open Hacl.Bignum.BasePulse
open Hacl.Impl.LibPulse

open Lib.IntTypes

module S = Hacl.Spec.Bignum.Addition
module SD = Hacl.Spec.Bignum.Definitions
module LSeq = Lib.Sequence
module SL = Hacl.Spec.Lib
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse

inline_for_extraction let sizet_of_size_t (x: size_t) : y:SizeT.t { v x == SizeT.v y } =
  assume SizeT.fits_u32;
  SizeT.uint32_to_sizet x

[@@pulse_unfold]
let bn_sub_carry_refl
  #t
  (aLen:size_t)
  (a:lbignum t aLen)
  (pra: perm)
  (a0: (SD.lbignum t (v aLen)))
  (c: ref (carry t))
  (i: size_nat{i <= v aLen}) (x: carry t)
  : slprop =
  pts_to c x ** pts_to a #pra a0

inline_for_extraction noextract
fn bn_sub_carry
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (#pra: perm)
  (c_in:carry t)
  (res:lbignum t aLen)
  (#a0: (SD.lbignum t (v aLen)))
  // FIXME: eq_or_disjoint
  requires pts_to a #pra a0 ** (exists* res0. pts_to res res0)
  returns c_out : carry t
  ensures
    pts_to res (snd (S.bn_sub_carry a0 c_in)) **
    pts_to a #pra a0 **
    pure (c_out == fst (S.bn_sub_carry a0 c_in))
{
  let mut c = c_in;

  let spec = S.bn_sub_carry_f a0;
  fn body () : fill_elems_impl_ty #(limb t) #(carry t) aLen res (bn_sub_carry_refl aLen a pra a0 c) spec = i #vr #vo {
    let t1 = AP.(a.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c0 = !c;
    assert pure (c0 == vr);
    let c0' = subborrow_st c0 t1 (uint #t 0) res_i;
    c := c0';
    AR.from_array_ptr_return res_i;
  };

  fill_elems4 aLen res _ spec (body ());
  !c;
}


inline_for_extraction noextract
let bn_sub_eq_len_st (t:limb_t) (aLen:size_t) =
    a:lbignum t aLen
  -> b:lbignum t aLen
  -> res:lbignum t aLen
  -> #va: (SD.lbignum t (v aLen))
  -> #vb: (SD.lbignum t (v aLen))
  -> #pra: perm
  -> #prb: perm
  -> stt (carry t)
  (requires exists* vres. pts_to a #pra va ** pts_to b #prb vb ** pts_to res vres)
  (ensures fun c_out ->
    pts_to a #pra va ** pts_to b #prb vb **
    pure (c_out == fst (SL.generate_elems (v aLen) (v aLen) (S.bn_sub_f va vb) (uint #t 0))) **
    lbignum_pts_to res (snd (SL.generate_elems (v aLen) (v aLen) (S.bn_sub_f va vb) (uint #t 0))))

[@@pulse_unfold]
let bn_sub_eq_len_refl (t:limb_t) (aLen:size_t)
  (a: lbignum t aLen)
  (b: lbignum t aLen)
  (va: (SD.lbignum t (v aLen)))
  (vb: (SD.lbignum t (v aLen)))
  (pra prb: perm)
  (c: ref (carry t))
  (i: size_nat{i <= v aLen}) (x: carry t)
  : slprop =
  pts_to c x ** pts_to a #pra va ** pts_to b #prb vb

inline_for_extraction noextract
fn bn_sub_eq_len #t aLen : bn_sub_eq_len_st t aLen = a b res #va #vb #pra #prb {
  let mut c = (uint #t 0 <: carry t);

  let spec = S.bn_sub_f va vb;
  fn body () : fill_elems_impl_ty #(limb t) #(carry t) aLen res (bn_sub_eq_len_refl t aLen a b va vb pra prb c) spec = i #vr #vo {
    let t1 = AP.(a.(sizet_of_size_t i));
    let t2 = AP.(b.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c' = !c;
    let c' = subborrow_st c' t1 t2 res_i;
    c := c';
    AR.from_array_ptr_return res_i;
  };

  fill_elems4 aLen res _ spec (body ());
  !c
}

let bn_sub_eq_len_u32 (aLen:size_t) : bn_sub_eq_len_st U32 aLen = bn_sub_eq_len aLen
let bn_sub_eq_len_u64 (aLen:size_t) : bn_sub_eq_len_st U64 aLen = bn_sub_eq_len aLen

inline_for_extraction noextract
let bn_sub_eq_len_u (#t:limb_t) (aLen:size_t) : bn_sub_eq_len_st t aLen =
  match t with
  | U32 -> bn_sub_eq_len_u32 aLen
  | U64 -> bn_sub_eq_len_u64 aLen


inline_for_extraction noextract
fn bn_sub
    (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (bLen:size_t{v bLen <= v aLen})
  (b:lbignum t bLen)
  (res:lbignum t aLen)
  #va #vb #pra #prb
  requires pts_to a #pra va
  requires pts_to b #prb vb
  requires exists* vres. pts_to res vres
  returns c_out:(carry t)
  ensures pts_to a #pra va
  ensures pts_to b #prb vb
  ensures pure (c_out == fst (S.bn_sub va vb))
  ensures pts_to res (snd (S.bn_sub va vb))
{
  let a1 = AP.split a (sizet_of_size_t bLen);
  let a0: lbignum t bLen = coerce_eq () a; rewrite each a as a0;
  let res1 = AP.split res (sizet_of_size_t bLen);
  let res0: lbignum t bLen = coerce_eq () res; rewrite each res as res0;
  let c0 = bn_sub_eq_len bLen a0 b res0;
  if (bLen <. aLen) {
    let rLen = aLen -! bLen;
    let c1 = bn_sub_carry rLen a1 c0 res1;
    AP.join a0 a1; rewrite each a0 as a;
    with va'. assert pts_to a #pra va' ** pure (Seq.equal va va');
    AP.join res0 res1; rewrite each res0 as res;
    c1
  } else {
    AP.join a0 a1; rewrite each a0 as a;
    with va'. assert pts_to a #pra va' ** pure (Seq.equal va va');
    AP.join res0 res1; rewrite each res0 as res;
    with vres. assert pts_to res vres ** pure (Seq.equal vres (snd (S.bn_sub va vb)));
    c0
  }
}

inline_for_extraction noextract
fn bn_sub1
  (#t:limb_t)
  (aLen:size_t{0 < v aLen})
  (a:lbignum t aLen)
  (b1:limb t)
  (res:lbignum t aLen)
  #va #pra
  requires pts_to a #pra va
  requires exists* vres. pts_to res vres
  returns c_out: carry t
  ensures pts_to a #pra va
  ensures pts_to res (snd (S.bn_sub1 va b1))
  ensures pure (c_out == fst (S.bn_sub1 va b1))
{
  let a0 = AP.(a.(0sz));
  let res0 = AR.from_array_ptr res 0sz;
  let c0 = subborrow_st (uint #t 0) a0 b1 res0;
  AR.from_array_ptr_return res0;

  if (1ul <. aLen) {
    let rLen = aLen -! 1ul;
    let a1 = AP.split a 1sz;
    let res1 = AP.split res 1sz;
    let c1 = bn_sub_carry rLen a1 c0 res1;
    AP.join a a1;
    AP.join res res1;
    with vres'. assert pts_to res vres' ** pure (vres' `Seq.equal` snd (S.bn_sub1 va b1));
    with va'. assert pts_to a #pra va' ** pure (va' `Seq.equal` va);
    c1
  } else {
    with vres'. assert pts_to res vres' ** pure (vres' `Seq.equal` snd (S.bn_sub1 va b1));
    c0
  }
}

[@@pulse_unfold]
let bn_add_carry_refl
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  va pra
  (c: ref (carry t))
  (i: size_nat{i <= v aLen}) (x: carry t)
  : slprop =
  pts_to c x ** pts_to a #pra va

inline_for_extraction noextract
fn bn_add_carry
    (#t:limb_t)
    (aLen:size_t)
    (a:lbignum t aLen)
    (c_in:carry t)
    (res:lbignum t aLen)
    #va #pra
  requires pts_to a #pra va
  requires exists* vres. pts_to res vres
  returns c_out: carry t
  ensures pts_to a #pra va
  ensures pts_to res (snd (S.bn_add_carry va c_in))
  ensures pure (c_out == fst (S.bn_add_carry va c_in))
{
  let mut c = c_in;

  let spec = S.bn_add_carry_f va;
  fn body () : fill_elems_impl_ty #(limb t) #(carry t) aLen res (bn_add_carry_refl aLen a va pra c) spec = i #vr #vo {
    let t1 = AP.(a.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c' = !c;
    let c' = addcarry_st c' t1 (uint #t 0) res_i;
    c := c';
    AR.from_array_ptr_return res_i;
  };
  
  fill_elems4 aLen res _ spec (body ());
  !c
}


inline_for_extraction noextract
let bn_add_eq_len_st (t:limb_t) (aLen:size_t) =
    a:lbignum t aLen
  -> b:lbignum t aLen
  -> res:lbignum t aLen
  -> #va: _
  -> #vb: _
  -> #pra: perm
  -> #prb: perm
  -> stt (carry t)
    (requires pts_to a #pra va ** pts_to b #prb vb ** (exists* vres. pts_to res vres))
    (ensures fun c_out ->
      let s = SL.generate_elems (v aLen) (v aLen) (S.bn_add_f va vb) (uint #t 0) in
      pts_to a #pra va ** pts_to b #prb vb **
      pure (c_out == fst s) ** pts_to res (snd s))


[@@pulse_unfold]
let bn_add_eq_len_refl
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (b:lbignum t aLen)
  (res:lbignum t aLen)
  va pra
  vb prb
  (c: ref (carry t))
  (i: size_nat{i <= v aLen}) (x: carry t)
  : slprop =
  pts_to c x ** pts_to a #pra va ** pts_to b #prb vb

inline_for_extraction noextract
fn bn_add_eq_len (#t:limb_t) (aLen:size_t) : bn_add_eq_len_st t aLen = a b res #va #vb #pra #prb {
  let mut c: carry t = uint #t 0;

  let spec = S.bn_add_f va vb;
  fn body () : fill_elems_impl_ty #(limb t) #(carry t) aLen res (bn_add_eq_len_refl aLen a b res va pra vb prb c) spec = i #vr #vo {
    let t1 = AP.(a.(sizet_of_size_t i));
    let t2 = AP.(b.(sizet_of_size_t i));
    let res_i = AR.from_array_ptr res (sizet_of_size_t i);
    let c' = !c;
    let c' = addcarry_st c' t1 t2 res_i;
    c := c';
    AR.from_array_ptr_return res_i;
  };

  fill_elems4 aLen res _ spec (body ());
  !c
}


let bn_add_eq_len_u32 (aLen:size_t) : bn_add_eq_len_st U32 aLen = bn_add_eq_len aLen
let bn_add_eq_len_u64 (aLen:size_t) : bn_add_eq_len_st U64 aLen = bn_add_eq_len aLen

inline_for_extraction noextract
let bn_add_eq_len_u (#t:limb_t) (aLen:size_t) : bn_add_eq_len_st t aLen =
  match t with
  | U32 -> bn_add_eq_len_u32 aLen
  | U64 -> bn_add_eq_len_u64 aLen


inline_for_extraction noextract
fn bn_add
  (#t:limb_t)
  (aLen:size_t)
  (a:lbignum t aLen)
  (bLen:size_t{v bLen <= v aLen})
  (b:lbignum t bLen)
  (res:lbignum t aLen)
  #va #vb
  #pra #prb
  requires pts_to a #pra va
  requires pts_to b #prb vb
  requires exists* vres. pts_to res vres
  returns c_out: carry t
  ensures pts_to a #pra va
  ensures pts_to b #prb vb
  ensures
    (let s = S.bn_add va vb in
    pure (c_out == fst s) ** pts_to res (snd s))
{
  let a1 = AP.split a (sizet_of_size_t bLen);
  let a0: lbignum t bLen = coerce_eq () a; rewrite each a as a0;
  let res1 = AP.split res (sizet_of_size_t bLen);
  let res0: lbignum t bLen = coerce_eq () res; rewrite each res as res0;
  let c0 = bn_add_eq_len bLen a0 b res0;
  if (bLen <. aLen) {
    let rLen = aLen -! bLen;
    let c1 = bn_add_carry rLen a1 c0 res1;
    AP.join a0 a1; rewrite each a0 as a;
    with va'. assert pts_to a #pra va' ** pure (Seq.equal va va');
    AP.join res0 res1; rewrite each res0 as res;
    c1
  } else {
    AP.join a0 a1; rewrite each a0 as a;
    with va'. assert pts_to a #pra va' ** pure (Seq.equal va va');
    AP.join res0 res1; rewrite each res0 as res;
    with vres. assert pts_to res vres ** pure (Seq.equal vres (snd (S.bn_add va vb)));
    c0
  }
}


inline_for_extraction noextract
fn bn_add1
  (#t:limb_t)
  (aLen:size_t{0 < v aLen})
  (a:lbignum t aLen)
  (b1:limb t)
  (res:lbignum t aLen)
  #va #pra
  requires pts_to a #pra va
  requires exists* vres. pts_to res vres
  returns c_out: carry t
  ensures pts_to a #pra va
  ensures pure (c_out == fst (S.bn_add1 va b1))
  ensures pts_to res (snd (S.bn_add1 va b1))
{
  let a0 = AP.(a.(0sz));
  let res0 = AR.from_array_ptr res 0sz;
  let c0 = addcarry_st (uint #t 0) a0 b1 res0;
  AR.from_array_ptr_return res0;

  if (1ul <. aLen) {
    let rLen = aLen -! 1ul;
    let a1 = AP.split a 1sz;
    let res1 = AP.split res 1sz;
    let c1 = bn_add_carry rLen a1 c0 res1;
    AP.join a a1; with va'. assert pts_to a #pra va' ** pure (Seq.equal va' va);
    AP.join res res1; with vres. assert pts_to res vres ** pure (vres `Seq.equal` snd (S.bn_add1 va b1));
    c1
  } else {
    with vres. assert pts_to res vres ** pure (vres `Seq.equal` snd (S.bn_add1 va b1));
    c0
  }
}