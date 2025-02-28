module Lib.ArrayRefPulse
open Pulse
module AP = Pulse.Lib.ArrayPtr

let ref (t: Type0) : Type0 = AP.ptr t

let pts_to #t ([@@@mkey] r: ref t) (#[full_default()] pr: perm) (v: t) : slprop =
  pts_to (r <: AP.ptr t) #pr seq![v]

[@@pulse_unfold] instance ref_has_pts_to #t : has_pts_to (ref t) t = { pts_to = pts_to }

val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

val share #t (r: ref t) (#pr: perm) #v : stt_ghost unit [] (pts_to r #pr v) (fun _ -> pts_to r #(pr /. 2.0R) v ** pts_to r #(pr /. 2.0R) v)
val gather #t (r: ref t) (#pr1 #pr2: perm) #v1 #v2 : stt_ghost unit [] (pts_to r #pr1 v1 ** pts_to r #pr2 v2) (fun  _ -> pts_to r #(pr1 +. pr2) v1 ** pure (v1 == v2))

inline_for_extraction val (!) #a (b: ref a) (#v: erased a) #p : stt a (pts_to b #p v) (fun x -> pts_to b #p v ** pure (reveal v == x))
inline_for_extraction val (:=) #a (b: ref a) (x: a) (#v:erased a) : stt unit (pts_to b v) (fun _ -> pts_to b x)

let from_array_ptr_rest #t (r: AP.ptr t) (#[full_default()] pr:perm)
    (v: (Seq.seq t)) (i: nat) ([@@@mkey] x: ref t) =
  exists* (h: squash (i < Seq.length v)).
  pure (h == ()) **
  AP.pts_to r #pr (Seq.slice v 0 i) **
  pure (AP.adjacent r i x) **
  exists* (y: AP.ptr t).
  AP.pts_to y #pr (Seq.slice v (i+1) (Seq.length v)) **
  pure (AP.adjacent x 1 y)

inline_for_extraction
val from_array_ptr (#t: Type0) (r: AP.ptr t) #pr (#v: erased (Seq.seq t)) (i: SizeT.t) :
  stt (ref t) (requires AP.pts_to r #pr v ** pure (SizeT.v i < Seq.length v))
    (ensures fun x -> exists* (h: squash (SizeT.v i < Seq.length v)). pure (eq2 #unit h ()) **
      pts_to x #pr (Seq.index v (SizeT.v i)) ** from_array_ptr_rest r #pr v (SizeT.v i) x)
val from_array_ptr_return (#t: Type0) (#r: AP.ptr t) (#[full_default()] pr:perm)
    (#v: (Seq.seq t)) (#i: nat) (x: ref t) (#w: erased t) :
  stt_ghost unit [] (requires from_array_ptr_rest r #pr v i x ** pts_to x #pr w)
    (ensures fun _ -> exists* (h: squash (i < Seq.length v)). pure (eq2 #unit h ()) **
      AP.pts_to r #pr (Seq.upd v i w))