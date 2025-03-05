module Lib.ByteBufferPulse

open Pulse

open Lib.IntTypes
open Lib.Buffer
open Hacl.Bignum.BasePulse

module BS = Lib.ByteSequencePulse
module AP = Pulse.Lib.ArrayPtr
module AR = Lib.ArrayRefPulse

#set-options "--z3rlimit 30 --fuel 0 --ifuel 0"

/// Host to {little,big}-endian conversions
/// TODO: missing specifications

inline_for_extraction
let uint_to_be #t #l (x:uint_t t l) = uint_of_be #t x

inline_for_extraction
let uint_to_le #t #l (x:uint_t t l) = uint_of_le #t x

inline_for_extraction
let uint_from_be #t #l (x:uint_t t l) = uint_to_be #t x

inline_for_extraction
let uint_from_le #t #l (x:uint_t t l) = uint_to_le #t x

(** Constructs the equality mask for two buffers of secret integers in constant-time *)
inline_for_extraction
fn buf_eq_mask
    (#t:inttype{~(S128? t)})
    (#len1:size_t)
    (#len2:size_t)
    (b1:lbuffer (int_t t SEC) len1)
    (b2:lbuffer (int_t t SEC) len2)
    (len:size_t{v len <= v len1 /\ v len <= v len2})
    (res:lbuffer (int_t t SEC) (size 1))
    (#b0: erased (SD.lbignum (uint_t t) (v len1)))
    (#b1: erased (SD.lbignum (uint_t t) (v len2)))
    #(pra: perm)
    #(prb: perm)
    requires pts_to b1 #pra b0 ** pts_to b2 #prb b1 ** pts_to res (ones t SEC)
    returns z: int_t t SEC
    ensures pts_to b1 #pra b0 ** pts_to b2 #prb b1 ** pts_to res z
    ensures pure (z == BS.seq_eq_mask (as_seq b0) (as_seq b1) (v len))
{
  let rec_eq = 0ul;
  let mut i = 0ul;
  while (lt (!i) len)
    invariant inv. 
      exists* vi v1 v2.
        pts_to b1 v1 ** pts_to b2 v2 ** pts_to i vi ** pts_to res rec_eq **
        pure (inv == lt vi len) ** pure (rec_eq == z)
  {
    let b1_i = AP.(b1.(size_to_limb !i));
    let b2_i = AP.(b2.(size_to_limb !i));
    rec_eq <- (rec_eq |. ((b1_i ^. b2_i) ^. ((b1_i ^. b2_i) -. 1ul)));
    i := add !i 1ul;
  };
  rec_eq
}

(** Compares two buffers of secret bytes of equal length in constant-time,
    declassifying the result *)
inline_for_extraction
fn lbytes_eq
    (#len:size_t)
    (b1:lbuffer uint8 len)
    (b2:lbuffer uint8 len)
    (#b0: erased (SD.lbignum uint8 (v len)))
    #(pra: perm)
    #(prb: perm)
    requires pts_to b1 #pra b0 ** pts_to b2 #prb b0
    returns r:bool
    ensures pts_to b1 #pra b0 ** pts_to b2 #prb b0 **
            pure (r == BS.lbytes_eq (as_seq b0) (as_seq b0))
{
  let mask = buf_eq_mask b1 b2 len (AR.from_array_ptr_uint 0sz);
  bool_of_eq_mask mask
}

inline_for_extraction
fn buf_mask_select
    (#t:inttype{~(S128? t)})
    (#len:size_t)
    (b1:lbuffer (int_t t SEC) len)
    (b2:lbuffer (int_t t SEC) len)
    (mask:int_t t SEC{v mask = 0 \/ v mask = v (ones t SEC)})
    (res:lbuffer (int_t t SEC) len)
    (#b1_0: erased (SD.lbignum (int_t t SEC) (v len)))
    #(pra: perm)
    #(prb: perm)
    requires pts_to b1 #pra b1_0 ** pts_to b2 #prb b1_0 ** exists* vres. pts_to res vres
    returns _
    ensures pts_to b1 #pra b1_0 ** pts_to b2 #prb b1_0 **
            pts_to res (S.buf_mask_select (as_seq b1_0) (as_seq b1_0) mask)
{
  mstore_unchecked_int res (mask_select mask (mload_int b1) (mload_int b2));
}

inline_for_extraction
fn uint_from_bytes_le
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (i:lbuffer (uint_t U8 l) (size (numbytes t)))
    (#i_0: erased (uintlist_t U8 l (size (numbytes t))))
    #(pri: perm)
    requires pts_to i #pri i_0
    returns o:uint_t t l
    ensures pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_le (as_seq i_0))
{
  uint_from_bytes_le #t #l (mload_int i)
}

inline_for_extraction
fn uint_from_bytes_be
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (i:lbuffer (uint_t U8 l) (size (numbytes t)))
    (#i_0: erased (uintlist_t U8 l (size (numbytes t))))
    #(pri: perm)
    requires pts_to i #pri i_0
    returns o:uint_t t l
    ensures pts_to i #pri i_0 **
            pure (o == BS.uint_from_bytes_be #t (as_seq i_0))
{
  uint_from_bytes_be #t #l (mload_int i)
}

inline_for_extraction
fn uint_to_bytes_le
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (o:lbuffer (uint_t U8 l) (size (numbytes t)))
    (i:uint_t t l)
    #(pri: perm)
    requires pts_to o #pri (uint_to_bytes_le #t i)
    returns _
    ensures pts_to o #pri (BS.uint_to_bytes_le #t i)
{
  mstore_unchecked_int o (uint_to_bytes_le #t (uint_of_i #t i));
}

inline_for_extraction
fn uint_to_bytes_be
    (#t:inttype{unsigned t})
    (#l:secrecy_level)
    (o:lbuffer (uint_t U8 l) (size (numbytes t)))
    (i:uint_t t l)
    #(pri: perm)
    requires pts_to o #pri (uint_to_bytes_be #t i)
    returns _
    ensures pts_to o #pri (BS.uint_to_bytes_be #t i)
{
  mstore_unchecked_int o (uint_to_bytes_be #t (uint_of_i #t i));
}

inline_for_extraction
let uint32s_to_bytes_le len = uints_to_bytes_le #U32 #SEC len

inline_for_extraction
let uint32s_from_bytes_le #len = uints_from_bytes_le #U32 #SEC #len

inline_for_extraction
fn uint_at_index_le
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (i:lbuffer (uint_t U8 l) (len *! size (numbytes t)))
    (idx:size_t{v idx < v len})
    (#i_0: erased (uintlist_t U8 l (len *! size (numbytes t))))
    #(pri: perm)
    requires pts_to i #pri i_0
    returns r:uint_t t l
    ensures pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_le #t #l #(v len) (as_seq i_0) (v idx))
{
  let off = idx * numbytes t;
  uint_from_bytes_le #t #l (slice i off (len *! size (numbytes t)) (numbytes t) pri)
}

inline_for_extraction
fn uint_at_index_be
    (#t:inttype{unsigned t /\ ~(U1? t)})
    (#l:secrecy_level)
    (#len:size_t{v len * numbytes t <= max_size_t})
    (i:lbuffer (uint_t U8 l) (len *! size (numbytes t)))
    (idx:size_t{v idx < v len})
    (#i_0: erased (uintlist_t U8 l (len *! size (numbytes t))))
    #(pri: perm)
    requires pts_to i #pri i_0
    returns r:uint_t t l
    ensures pts_to i #pri i_0 **
            pure (r == BS.uint_at_index_be #t #l #(v len) (as_seq i_0) (v idx))
{
  let off = idx * numbytes t;
  uint_from_bytes_be #t #l (slice i off (len *! size (numbytes t)) (numbytes t) pri)
}
```
