module Lib.IntTypes.IntrinsicsPulse
#lang-pulse

open Pulse
module AR = Lib.ArrayRefPulse

open Lib.IntTypes

open FStar.Mul

#set-options "--z3rlimit 50 --ifuel 0 --fuel 0"

inline_for_extraction
let add_carry_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:AR.ref (uint_t t SEC) ->
  stt (uint_t t SEC)
  (exists* s. pts_to r s ** pure (v cin <= 1))
  (fun c ->
    exists* vr.
    pure (v c <= 1) **
    pts_to r vr **
    pure (v vr + v c * pow2 (bits t) == v x + v y + v cin))


val add_carry_u32: add_carry_st U32

val add_carry_u64: add_carry_st U64


inline_for_extraction
let add_carry (#t:inttype{t = U32 \/ t = U64}) : add_carry_st t =
  match t with
  | U32 -> add_carry_u32
  | U64 -> add_carry_u64


inline_for_extraction
let sub_borrow_st (t:inttype{t = U32 \/ t = U64}) =
    cin:uint_t t SEC
  -> x:uint_t t SEC
  -> y:uint_t t SEC
  -> r:AR.ref (uint_t t SEC) ->
  stt (uint_t t SEC)
  (requires exists* s. pts_to r s ** pure (v cin <= 1))
  (ensures fun c ->
    exists* vr.
    pure (v c <= 1) **
    pts_to r vr **
    pure (v vr - v c * pow2 (bits t) == v x - v y - v cin))


val sub_borrow_u32: sub_borrow_st U32

val sub_borrow_u64: sub_borrow_st U64


inline_for_extraction
let sub_borrow (#t:inttype{t = U32 \/ t = U64}) : sub_borrow_st t =
  match t with
  | U32 -> sub_borrow_u32
  | U64 -> sub_borrow_u64
