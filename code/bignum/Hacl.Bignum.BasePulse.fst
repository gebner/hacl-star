module Hacl.Bignum.BasePulse
#lang-pulse

open Pulse
module AR = Lib.ArrayRefPulse
open FStar.Mul

open Lib.IntTypes
open Hacl.Bignum.DefinitionsPulse

include Hacl.Spec.Bignum.Base

module LSeq = Lib.Sequence

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"


(**
unsigned char _addcarry_u64 (unsigned char c_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 64-bit integers a and b with unsigned 8-bit carry-in c_in (carry flag),
and store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

inline_for_extraction noextract
fn addcarry_st (#t:limb_t) (c_in:carry t) (a:limb t) (b:limb t) (out:AR.ref (limb t))
  requires exists* s. pts_to out s
  returns c_out : carry t
  ensures exists* c0. pts_to out c0 ** pure ((c_out, c0) == addcarry c_in a b)
{
  let r = Lib.IntTypes.IntrinsicsPulse.add_carry #t c_in a b out;
  r
}

(**
unsigned char _subborrow_u64 (unsigned char b_in, unsigned __int64 a, unsigned __int64 b, unsigned __int64 * out)

Description
Add unsigned 8-bit borrow b_in (carry flag) to unsigned 64-bit integer b, and subtract the result from
unsigned 64-bit integer a. Store the unsigned 64-bit result in out, and the carry-out in dst (carry or overflow flag).
*)

inline_for_extraction noextract
fn subborrow_st (#t:limb_t) (c_in:carry t) (a:limb t) (b:limb t) (out:AR.ref (limb t))
  requires exists* s. pts_to out s
  returns c_out: carry t
  ensures exists* c0. pts_to out c0 ** pure ((c_out, c0) == subborrow c_in a b)
{
  let c_out = Lib.IntTypes.IntrinsicsPulse.sub_borrow #t c_in a b out;
  c_out
}


inline_for_extraction noextract
let mul_wide_add_t (t:limb_t) =
    a:limb t
  -> b:limb t
  -> c_in:limb t
  -> out:AR.ref (limb t) ->
  stt (limb t)
  (requires exists* s. pts_to out s)
  (ensures fun c_out -> exists* c0. pts_to out c0 ** pure ((c_out, c0) == mul_wide_add a b c_in))


[@CInline]
fn mul_wide_add_u32 () : mul_wide_add_t U32 = a b c_in out {
  lemma_mul_wide_add a b c_in (u32 0);
  let res = to_u64 a *! to_u64 b +! to_u64 c_in;
  AR.(out := to_u32 res);
  to_u32 (res >>. 32ul)
}

[@CInline]
fn mul_wide_add_u64 () : mul_wide_add_t U64 = a b c_in out {
  lemma_mul_wide_add a b c_in (u64 0);
  let res = mul64_wide a b +! to_u128 c_in;
  AR.(out := to_u64 res);
  to_u64 (res >>. 64ul)
}


inline_for_extraction noextract
val mul_wide_add_st: #t:limb_t -> mul_wide_add_t t
let mul_wide_add_st #t =
  match t with
  | U32 -> mul_wide_add_u32 ()
  | U64 -> mul_wide_add_u64 ()


inline_for_extraction noextract
let mul_wide_add2_t (t:limb_t) =
    a:limb t
  -> b:limb t
  -> c_in:limb t
  -> out:AR.ref (limb t) ->
  #c0: erased (limb t) ->
  stt (limb t)
  (requires pts_to out c0)
  (ensures fun c_out -> exists* c1. pts_to out c1 **
    pure ((c_out, c1) == mul_wide_add2 a b c_in c0))


[@CInline]
fn mul_wide_add2_u32 () : mul_wide_add2_t U32 = a b c_in out #c0 {
  let out0 = AR.(!out);
  lemma_mul_wide_add a b c_in out0;
  let res = to_u64 a *! to_u64 b +! to_u64 c_in +! to_u64 out0;
  AR.(out := to_u32 res);
  to_u32 (res >>. 32ul)
}


[@CInline]
fn mul_wide_add2_u64 () : mul_wide_add2_t U64 = a b c_in out #c0 {
  let out0 = AR.(!out);
  lemma_mul_wide_add a b c_in out0;
  let res = mul64_wide a b +! to_u128 c_in +! to_u128 out0;
  AR.(out := to_u64 res);
  to_u64 (res >>. 64ul)
}


inline_for_extraction noextract
val mul_wide_add2_st: #t:limb_t -> mul_wide_add2_t t
let mul_wide_add2_st #t =
  match t with
  | U32 -> mul_wide_add2_u32 ()
  | U64 -> mul_wide_add2_u64 ()
