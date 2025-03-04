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

// TODO move to pulse
fn arrayptr_memset (#t: Type0) (r: AP.ptr t) (x: t) (sz: SizeT.t)
  requires exists* vr. pts_to r vr ** pure (Seq.length vr == SizeT.v sz)
  ensures pts_to r (Seq.create (SizeT.v sz) x)
{
  let mut i = 0sz;
  while (let vi = !i; SizeT.lt vi sz)
    invariant b. exists* vi vr.
      pts_to i vi ** pts_to r vr **
      pure (SizeT.v vi <= SizeT.v sz /\ Seq.length vr == SizeT.v sz /\
        (forall (j: nat). j < SizeT.v vi ==> Seq.index vr j == x)) **
      pure (b == (SizeT.lt vi sz))
  {
    let vi = !i;
    AP.(r.(vi) <- x);
    i := SizeT.add vi 1sz;
  };
  with vr. assert pts_to r vr ** pure (vr `Seq.equal` Seq.create (SizeT.v sz) x);
}