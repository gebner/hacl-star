module Hacl.Bignum.DefinitionsPulse
#lang-pulse
open Pulse

open FStar.Mul

open Lib.IntTypes

module S = Hacl.Spec.Bignum.Definitions
module AP = Pulse.Lib.ArrayPtr

#reset-options "--z3rlimit 50 --fuel 0 --ifuel 0"

inline_for_extraction noextract
val blocks: x:size_t{v x > 0} -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks (v x) (v m)}
let blocks x m = (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
val blocks0: x:size_t -> m:size_t{v m > 0} -> r:size_t{v r == S.blocks0 (v x) (v m)}
let blocks0 x m = if x =. 0ul then 1ul else (x -. 1ul) /. m +. 1ul

inline_for_extraction noextract
let limb_t = S.limb_t

inline_for_extraction noextract
let limb (t:limb_t) = S.limb t

inline_for_extraction noextract
let lbignum (t:limb_t) (len: size_t) = AP.ptr (limb t)

[@@pulse_unfold]
let lbignum_pts_to #t #len (x: lbignum t len) (#[full_default()] f : perm) (v: S.lbignum t (v len)) =
  AP.pts_to x #f v

[@@pulse_unfold]
instance lbignum_pts_to_inst #t #len : has_pts_to (lbignum t len) (S.lbignum t (v len)) =
  { pts_to = lbignum_pts_to }