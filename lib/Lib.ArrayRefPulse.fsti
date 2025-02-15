module Lib.ArrayRefPulse
#lang-pulse

open Pulse

val ref (t: Type0) : Type0

val pts_to_ #t (r: ref t) (pr: perm) (v: t) : slprop
[@@pulse_unfold] instance ref_has_pts_to #t : has_pts_to (ref t) t = { pts_to = fun r #pr v -> pts_to_ r pr v }

val pts_to_timeless (#a:Type) (r:ref a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

val share #t (r: ref t) (#pr: perm) #v : stt_ghost unit [] (pts_to r #pr v) (fun _ -> pts_to r #(pr /. 2.0R) v ** pts_to r #(pr /. 2.0R) v)
val gather #t (r: ref t) (#pr1 #pr2: perm) #v1 #v2 : stt_ghost unit [] (pts_to r #pr1 v1 ** pts_to r #pr2 v2) (fun  _ -> pts_to r #(pr1 +. pr2) v1 ** pure (v1 == v2))

inline_for_extraction val (!) #a (b: ref a) (#v: erased a) #p : stt a (pts_to b #p v) (fun x -> pts_to b #p v ** pure (reveal v == x))
inline_for_extraction val (:=) #a (b: ref a) (x: a) (#v:erased a) : stt unit (pts_to b v) (fun _ -> pts_to b x)