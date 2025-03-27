module Lib.ByteBufferPulse

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
let buf_eq_mask_t =
    (#t:inttype{~(S128? t)}) ->
    (#len1:size_t) ->
    (#len2:size_t) ->
    (b1:AP.ptr (int_t t SEC)) ->
    (b2:AP.ptr (int_t t SEC)) ->
    (len:size_t{v len <= v len1 /\ v len <= v len2}) ->
    (#vb1: erased (Seq.lseq (int_t t SEC) (v len1))) ->
    (#vb2: erased (Seq.lseq (int_t t SEC) (v len2))) ->
    (#pra: perm) ->
    (#prb: perm) ->
    stt (int_t t SEC)
      (requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2)
      (ensures fun z ->
        AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
        pure (z == BS.seq_eq_mask #t #(v len1) #(v len2) vb1 vb2 (v len)))
inline_for_extraction
val buf_eq_mask : buf_eq_mask_t

(** Compares two buffers of secret bytes of equal length in constant-time,
    declassifying the result *)
inline_for_extraction
let lbytes_eq_t =
    (#len:size_t) ->
    (b1:AP.ptr uint8) ->
    (b2:AP.ptr uint8) ->
    (#vb1: erased (Seq.lseq uint8 (v len))) ->
    (#vb2: erased (Seq.lseq uint8 (v len))) ->
    (#pra: perm) ->
    (#prb: perm) ->
    stt bool (requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2)
      (ensures fun r -> AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
            pure (r == BS.lbytes_eq #(v len) vb1 vb2))
inline_for_extraction
val lbytes_eq : lbytes_eq_t

inline_for_extraction
let buf_mask_select_t =
    (#t:inttype{~(S128? t)}) ->
    (#len:size_t) ->
    (b1:AP.ptr (int_t t SEC)) ->
    (b2:AP.ptr (int_t t SEC)) ->
    (mask:int_t t SEC{v mask = 0 \/ v mask = v (ones t SEC)}) ->
    (res:AP.ptr (int_t t SEC)) ->
    (#vb1: erased (Seq.lseq (int_t t SEC) (v len))) ->
    (#vb2: erased (Seq.lseq (int_t t SEC) (v len))) ->
    (#pra: perm) ->
    (#prb: perm) ->
    stt unit (requires AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 ** (exists* (vres : Seq.lseq (int_t t SEC) (v len)). AP.pts_to res vres))
      (ensures fun _ -> AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
            AP.pts_to res (BS.seq_mask_select #_ #(v len) vb1 vb2 mask))
inline_for_extraction
val buf_mask_select : buf_mask_select_t

inline_for_extraction
let uint_from_bytes_le_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (i:AP.ptr (uint_t U8 l)) ->
    (#i_0: erased (Seq.lseq (uint_t U8 l) (numbytes t))) ->
    (#pri: perm) ->
    stt (uint_t t l) (requires AP.pts_to i #pri i_0)
      (ensures fun o -> AP.pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_le (i_0)))
inline_for_extraction
val uint_from_bytes_le : uint_from_bytes_le_t

inline_for_extraction
let uint_from_bytes_be_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (i:AP.ptr (uint_t U8 l)) ->
    (#i_0: erased (Seq.lseq (uint_t U8 l) (numbytes t))) ->
    (#pri: perm) ->
    stt (uint_t t l) (requires AP.pts_to i #pri i_0)
      (ensures fun o -> AP.pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_be (i_0)))
inline_for_extraction
val uint_from_bytes_be : uint_from_bytes_be_t

inline_for_extraction
let uint_to_bytes_le_t =
    (#t:inttype{unsigned t}) ->
    (#l:secrecy_level) ->
    (o:AP.ptr (uint_t U8 l)) ->
    (i:uint_t t l) ->
    (#pri: perm) ->
    stt unit (requires exists* (vo: Seq.lseq _ (numbytes t)). AP.pts_to o vo)
      (ensures fun _ -> AP.pts_to o (BS.uint_to_bytes_le #t i))
inline_for_extraction
val uint_to_bytes_le : uint_to_bytes_le_t

inline_for_extraction
let uint_to_bytes_be_t =
    (#t:inttype{unsigned t}) ->
    (#l:secrecy_level) ->
    (o:AP.ptr (uint_t U8 l)) ->
    (i:uint_t t l) ->
    (#pri: perm) ->
    stt unit (requires exists* (vo: Seq.lseq _ (numbytes t)). AP.pts_to o vo)
      (ensures fun _ -> AP.pts_to o (BS.uint_to_bytes_be #t i))
inline_for_extraction
val uint_to_bytes_be : uint_to_bytes_be_t

inline_for_extraction
let uints_from_bytes_le_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (#len:size_t{v len * numbytes t <= max_size_t}) ->
    (o:AP.ptr (uint_t t l)) ->
    (i:AP.ptr (uint_t U8 l)) ->
    #pri:_ -> (#vi: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t))))) ->
  stt unit (requires (exists* (vo: Seq.lseq _ (v len)). AP.pts_to o vo) ** AP.pts_to i #pri vi)
    (ensures fun _ -> AP.pts_to i #pri vi ** AP.pts_to o (BS.uints_from_bytes_le #t #l #(v len) vi))
inline_for_extraction
val uints_from_bytes_le : uints_from_bytes_le_t

inline_for_extraction
let uints_from_bytes_be_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (#len:size_t{v len * numbytes t <= max_size_t}) ->
    (o:AP.ptr (uint_t t l)) ->
    (i:AP.ptr (uint_t U8 l)) ->
    #pri:_ -> (#vi: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t))))) ->
  stt unit (requires (exists* (vo: Seq.lseq _ (v len)). AP.pts_to o vo) ** AP.pts_to i #pri vi)
    (ensures fun _ -> AP.pts_to i #pri vi ** AP.pts_to o (BS.uints_from_bytes_be #t #l #(v len) vi))
inline_for_extraction
val uints_from_bytes_be : uints_from_bytes_be_t

inline_for_extraction
let uints_to_bytes_le_t =
    (#t:inttype{unsigned t}) ->
    (#l:secrecy_level) ->
    (len:size_t{v len * numbytes t <= max_size_t}) ->
    (o:AP.ptr (uint_t U8 l)) ->
    (i:AP.ptr (uint_t t l)) ->
    #pri:_ -> (#vi: erased (Seq.lseq (uint_t t l) (v len))) ->
  stt unit (requires AP.pts_to i #pri vi ** (exists* (vo: Seq.lseq _ (v (len *! size (numbytes t)))).  AP.pts_to o vo))
    (ensures fun _ -> AP.pts_to i #pri vi ** AP.pts_to o (BS.uints_to_bytes_le #t #l #(v len) vi))
inline_for_extraction
val uints_to_bytes_le : uints_to_bytes_le_t

inline_for_extraction
let uints_to_bytes_be_t =
    (#t:inttype{unsigned t}) ->
    (#l:secrecy_level) ->
    (len:size_t{v len * numbytes t <= max_size_t}) ->
    (o:AP.ptr (uint_t U8 l)) ->
    (i:AP.ptr (uint_t t l)) ->
    #pri:_ -> (#vi: erased (Seq.lseq (uint_t t l) (v len))) ->
  stt unit (requires AP.pts_to i #pri vi ** (exists* (vo: Seq.lseq _ (v (len *! size (numbytes t)))).  AP.pts_to o vo))
    (ensures fun _ -> AP.pts_to i #pri vi ** AP.pts_to o (BS.uints_to_bytes_be #t #l #(v len) vi))
inline_for_extraction
val uints_to_bytes_be : uints_to_bytes_be_t

inline_for_extraction
let uint32s_to_bytes_le len = uints_to_bytes_le #U32 #SEC len

inline_for_extraction
let uint32s_from_bytes_le #len = uints_from_bytes_le #U32 #SEC #len

inline_for_extraction
let uint_at_index_le_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (#len:size_t{v len * numbytes t <= max_size_t}) ->
    (i:AP.ptr (uint_t U8 l)) ->
    (idx:size_t{v idx < v len}) ->
    (#i_0: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t))))) ->
    (#pri: perm) ->
    stt (uint_t t l) (requires AP.pts_to i #pri i_0)
      (ensures fun r -> AP.pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_le #t #l #(v len) i_0 (v idx)))
inline_for_extraction
val uint_at_index_le : uint_at_index_le_t

inline_for_extraction
let uint_at_index_be_t =
    (#t:inttype{unsigned t /\ ~(U1? t)}) ->
    (#l:secrecy_level) ->
    (#len:size_t{v len * numbytes t <= max_size_t}) ->
    (i:AP.ptr (uint_t U8 l)) ->
    (idx:size_t{v idx < v len}) ->
    (#i_0: erased (Seq.lseq (uint_t U8 l) (v (len *! size (numbytes t))))) ->
    (#pri: perm) ->
    stt (uint_t t l) (requires AP.pts_to i #pri i_0)
      (ensures fun r -> AP.pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_be #t #l #(v len) i_0 (v idx)))
inline_for_extraction
val uint_at_index_be : uint_at_index_be_t
