module Lib.ArrayRefPulse
#lang-pulse

open Pulse

module AP = Pulse.Lib.ArrayPtr

let ref t = AP.ptr t

[@@pulse_unfold]
let pts_to_ #t (r: ref t) (pr: perm) (v: t) : slprop =
  pts_to (r <: AP.ptr t) #pr seq![v]

let pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a) = ()

ghost fn share #t (r: ref t) (#pr: perm) #v
  requires pts_to r #pr v
  ensures pts_to r #(pr /. 2.0R) v ** pts_to r #(pr /. 2.0R) v
{
  AP.share r
}

ghost fn gather #t (r: ref t) (#pr1 #pr2: perm) #v1 #v2
  requires pts_to r #pr1 v1 ** pts_to r #pr2 v2
  ensures pts_to r #(pr1 +. pr2) v1 ** pure (v1 == v2)
{
  AP.gather r;
  assert pure (Seq.index seq![v1] 0 == v1);
  assert pure (Seq.index seq![v2] 0 == v2)
}

inline_for_extraction
fn op_Bang #a (b: ref a) (#v: erased a) #p
  requires pts_to b #p v
  returns x : a
  ensures pts_to b #p v ** pure (reveal v == x)
{
  AP.(b.(0sz))
}

inline_for_extraction
fn op_Colon_Equals #a (b: ref a) (x: a) (#v:erased a)
  requires pts_to b v
  ensures pts_to b x
{
  AP.(b.(0sz) <- x);
  assert pure (Seq.upd seq![reveal v] 0 x `Seq.equal` seq![x])
}