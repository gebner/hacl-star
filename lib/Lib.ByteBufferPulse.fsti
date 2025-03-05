module Lib.ByteBufferPulse
#lang-pulse

open Pulse

open Lib.IntTypes

module BS = Lib.ByteSequence
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse

/// Host to {little,big}-endian conversions
/// TODO: missing specifications

inline_for_extraction
val uint_to_be: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_to_le: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_from_be: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

inline_for_extraction
val uint_from_le: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level -> uint_t t l -> uint_t t l

(** Constructs the equality mask for two buffers of secret integers in constant-time *)
inline_for_extraction
fn buf_eq_mask
    (#t:inttype{~(S128? t)})
    (#len1:size_t)
    (#len2:size_t)
    (b1:AP.ptr (int_t t SEC))
    (b2:AP.ptr (int_t t SEC))
    (len:size_t{v len <= v len1 /\ v len <= v len2})
    (res:AR.ref (int_t t SEC))
    (#vb1: erased (Seq.lseq (int_t t SEC) (v len1)))
    (#vb2: erased (Seq.lseq (int_t t SEC) (v len2)))
    (#pra: perm)
    (#prb: perm)
    requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 ** pts_to res (ones t SEC)
    returns z: int_t t SEC
    ensures AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 ** pts_to res z
    ensures pure (z == BS.seq_eq_mask #t #(v len1) #(v len2) vb1 vb2 (v len))

(** Compares two buffers of secret bytes of equal length in constant-time,
    declassifying the result *)
inline_for_extraction
fn lbytes_eq
    (#len:size_t)
    (b1:AP.ptr uint8)
    (b2:AP.ptr uint8)
    (#vb1: erased (Seq.lseq uint8 (v len)))
    (#vb2: erased (Seq.lseq uint8 (v len)))
    (#pra: perm)
    (#prb: perm)
    requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2
    returns r:bool
    ensures AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
            pure (r == BS.lbytes_eq #(v len) vb1 vb2)

inline_for_extraction
fn buf_mask_select
    (#t:inttype{~(S128? t)})
    (#len:size_t)
    (b1:AP.ptr (int_t t SEC))
    (b2:AP.ptr (int_t t SEC))
    (mask:int_t t SEC{v mask = 0 \/ v mask = v (ones t SEC)})
    (res:AP.ptr (int_t t SEC))
    (#vb1: erased (Seq.lseq (int_t t SEC) (v len)))
    (#vb2: erased (Seq.lseq (int_t t SEC) (v len)))
    (#pra: perm)
    (#prb: perm)
    requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 ** (exists* (vres : Seq.lseq (int_t t SEC) (v len)). AP.pts_to res vres)
    ensures AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
            AP.pts_to res (BS.seq_mask_select #_ #(v len) vb1 vb2 mask)

inline_for_extraction
fn uint_from_bytes_le
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (i:AP.ptr (uint_t U8 l))
    (#i_0: erased (Seq.lseq (uint_t U8 l) (numbytes t)))
    (#pri: perm)
    requires AP.pts_to i #pri i_0
    returns o:uint_t t l
    ensures AP.pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_le (i_0))

inline_for_extraction
fn uint_from_bytes_be
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (i:AP.ptr (uint_t U8 l))
    (#i_0: erased (Seq.lseq (uint_t U8 l) (numbytes t)))
    (#pri: perm)
    requires AP.pts_to i #pri i_0
    returns o:uint_t t l
    ensures AP.pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_be #t (i_0))


inline_for_extraction
fn uint_to_bytes_le
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (o:AP.ptr (uint_t U8 l))
    (i:uint_t t l)
    (#pri: perm)
    requires exists* (vo: Seq.lseq _ (numbytes t)). AP.pts_to o vo
    ensures AP.pts_to o (BS.uint_to_bytes_le #t i)

inline_for_extraction
fn uint_to_bytes_be
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (o:AP.ptr (uint_t U8 l))
    (i:uint_t t l)
    requires exists* (vo: Seq.lseq _ (numbytes t)). AP.pts_to o vo
    ensures AP.pts_to o (BS.uint_to_bytes_be #t i)

inline_for_extraction
fn uints_from_bytes_le
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (o:AP.ptr (uint_t t l))
    (i:AP.ptr (uint_t U8 l))
    #pri (#vi: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t)))))
  requires exists* (vo: Seq.lseq _ (v len)). AP.pts_to o vo
  requires AP.pts_to i #pri vi
  ensures AP.pts_to i #pri vi 
  ensures AP.pts_to o (BS.uints_from_bytes_le #t #l #(v len) vi)

inline_for_extraction
fn uints_from_bytes_be
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (o:AP.ptr (uint_t t l))
    (i:AP.ptr (uint_t U8 l))
    #pri (#vi: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t)))))
  requires exists* (vo: Seq.lseq _ (v len)). AP.pts_to o vo
  requires AP.pts_to i #pri vi
  ensures AP.pts_to i #pri vi 
  ensures AP.pts_to o (BS.uints_from_bytes_be #t #l #(v len) vi)

inline_for_extraction
fn uints_to_bytes_le
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (len:size_t{v len * numbytes t <= max_size_t})
    (o:AP.ptr (uint_t U8 l))
    (i:AP.ptr (uint_t t l))
    #pri (#vi: erased (Seq.lseq (uint_t t l) (v len)))
  requires AP.pts_to i #pri vi
  requires exists* (vo: Seq.lseq _ (v (len *! size (numbytes t)))).  AP.pts_to o vo
  ensures AP.pts_to i #pri vi
  ensures AP.pts_to o (BS.uints_to_bytes_le #t #l #(v len) vi)

inline_for_extraction
fn uints_to_bytes_be
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (len:size_t{v len * numbytes t <= max_size_t})
    (o:AP.ptr (uint_t U8 l))
    (i:AP.ptr (uint_t t l))
    #pri (#vi: erased (Seq.lseq (uint_t t l) (v len)))
  requires AP.pts_to i #pri vi
  requires exists* (vo: Seq.lseq _ (v (len *! size (numbytes t)))).  AP.pts_to o vo
  ensures AP.pts_to i #pri vi
  ensures AP.pts_to o (BS.uints_to_bytes_be #t #l #(v len) vi)

inline_for_extraction
let uint32s_to_bytes_le len = uints_to_bytes_le #U32 #SEC len

inline_for_extraction
let uint32s_from_bytes_le #len = uints_from_bytes_le #U32 #SEC #len

inline_for_extraction
fn uint_at_index_le
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (i:AP.ptr (uint_t U8 l))
    (idx:size_t{v idx < v len})
    (#i_0: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t)))))
    (#pri: perm)
    requires AP.pts_to i #pri i_0
    returns r:uint_t t l
    ensures AP.pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_le #t #l #(v len) i_0 (v idx))

inline_for_extraction
fn uint_at_index_be
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (i:AP.ptr (uint_t U8 l))
    (idx:size_t{v idx < v len})
    (#i_0: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t)))))
    (#pri: perm)
    requires AP.pts_to i #pri i_0
    returns r:uint_t t l
    ensures AP.pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_be #t #l #(v len) i_0 (v idx))
