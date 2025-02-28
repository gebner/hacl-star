module Lib.ArrayRefPulse
module AP = Pulse.Lib.ArrayPtr
#lang-pulse

let pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a) = ()

ghost fn share #t (r: ref t) (#pr: perm) #v
  requires pts_to r #pr v
  ensures pts_to r #(pr /. 2.0R) v ** pts_to r #(pr /. 2.0R) v
{
  unfold pts_to r #pr v;
  AP.share #t r;
  fold pts_to r #(pr /. 2.0R) v;
  fold pts_to r #(pr /. 2.0R) v;
}

ghost fn gather #t (r: ref t) (#pr1 #pr2: perm) #v1 #v2
  requires pts_to r #pr1 v1 ** pts_to r #pr2 v2
  ensures pts_to r #(pr1 +. pr2) v1 ** pure (v1 == v2)
{
  unfold pts_to r #pr1 v1;
  unfold pts_to r #pr2 v2;
  AP.gather r;
  assert pure (Seq.index seq![v1] 0 == v1);
  assert pure (Seq.index seq![v2] 0 == v2);
  fold pts_to r #(pr1 +. pr2);
}

inline_for_extraction
fn op_Bang #a (b: ref a) (#v: erased a) #p
  requires pts_to b #p v
  returns x : a
  ensures pts_to b #p v ** pure (reveal v == x)
{
  unfold pts_to b #p v;
  let x = AP.(b.(0sz));
  fold pts_to b #p v;
  x
}

inline_for_extraction
fn op_Colon_Equals #a (b: ref a) (x: a) (#v:erased a)
  requires pts_to b v
  ensures pts_to b x
{
  unfold pts_to b v;
  AP.(b.(0sz) <- x);
  assert pure (Seq.upd seq![reveal v] 0 x `Seq.equal` seq![x]);
  fold pts_to b x;
}

inline_for_extraction
fn from_array_ptr (#t: Type0) (r: AP.ptr t) (#pr: perm) (#v: erased (Seq.seq t)) (i: SizeT.t)
  requires AP.pts_to r #pr v ** pure (SizeT.v i < Seq.length v)
  returns x: ref t
  ensures (exists* (h: squash (SizeT.v i < Seq.length v)). pure (eq2 #unit h ()) **
      pts_to x #pr (Seq.index v (SizeT.v i)) ** from_array_ptr_rest r #pr v (SizeT.v i) x)
{
  let x = AP.split r i;
  with vr. assert AP.pts_to r #pr vr;
  let y = AP.ghost_split x 1sz;
  with vx. assert AP.pts_to x #pr vx;
  with vy. assert AP.pts_to y #pr vy;
  assert pure (Seq.equal vx seq![Seq.index v (SizeT.v i)]);
  rewrite AP.pts_to x #pr vx as AP.pts_to x #pr seq![Seq.index v (SizeT.v i)];
  assert pure (Seq.equal vy (Seq.slice v (SizeT.v i + 1) (Seq.length v)));
  rewrite AP.pts_to y #pr vy as AP.pts_to y #pr (Seq.slice v (SizeT.v i + 1) (Seq.length v));
  fold from_array_ptr_rest r #pr v (SizeT.v i) x;
  fold pts_to x #pr (Seq.index v (SizeT.v i));
  x
}

ghost fn from_array_ptr_return (#t: Type0) (#r: AP.ptr t) (#[full_default()] pr:perm)
    (#v: (Seq.seq t)) (#i: nat) (x: ref t) (#w: erased t)
  requires from_array_ptr_rest r #pr v i x ** pts_to x #pr w
  ensures exists* (h: squash (i < Seq.length v)). pure (eq2 #unit h ()) **
      AP.pts_to r #pr (Seq.upd v i w)
{
  unfold from_array_ptr_rest r #pr v i x;
  unfold pts_to x #pr w;
  AP.join r x;
  AP.join r _;
  with v'. assert AP.pts_to r #pr v' ** pure (v' `Seq.equal` Seq.upd v i w);
}