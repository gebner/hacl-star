module Lib.EndiannessPulse

/// Stateful operations between machine integers and buffers of uint8s. Most of
/// these operations are implemented natively using the target's system endianness
/// headers, relying on macros or static inline declarations.
///
/// .. note::
///
///    This module supersedes ``C.Endianness``.

open FStar.Endianness

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

open Pulse
module AP = Pulse.Lib.ArrayPtr

inline_for_extraction
type u8 = U8.t
inline_for_extraction
type u16 = U16.t
inline_for_extraction
type u32 = U32.t
inline_for_extraction
type u64 = U64.t
inline_for_extraction
type u128 = U128.t

/// Byte-swapping operations
/// ------------------------
///
/// TODO these are totally unspecified

val htole16: u16 -> u16
val le16toh: u16 -> u16

val htole32: u32 -> u32
val le32toh: u32 -> u32

val htole64: u64 -> u64
val le64toh: u64 -> u64

val htobe16: u16 -> u16
val be16toh: u16 -> u16

val htobe32: u32 -> u32
val be32toh: u32 -> u32

val htobe64: u64 -> u64
val be64toh: u64 -> u64

/// Loads and stores
/// ----------------
///
/// These are primitive

inline_for_extraction
let store_t #t (bs: nat) (to_n: bytes -> nat) (v: t -> nat) =
  (x: AP.ptr u8) -> (z: t) ->
  stt unit (requires exists* vx. pts_to x vx ** pure (Seq.length vx == bs))
    (ensures fun _ -> exists* vx. pts_to x vx ** pure (to_n vx == v z))

inline_for_extraction
let load_t #t (bs: nat) (to_n: bytes -> nat) (v: t -> nat) =
  (x: AP.ptr u8) -> (#vx: erased (Seq.lseq u8 bs)) -> (#pr: perm) ->
  stt t (requires AP.pts_to x #pr vx)
    (ensures fun z -> AP.pts_to x #pr vx ** pure (to_n vx == v z))

val store16_le  : store_t  2 le_to_n U16.v
val store32_le  : store_t  4 le_to_n U32.v
val store64_le  : store_t  8 le_to_n U64.v
val store128_le : store_t 16 le_to_n U128.v

val store16_be  : store_t  2 be_to_n U16.v
val store32_be  : store_t  4 be_to_n U32.v
val store64_be  : store_t  8 be_to_n U64.v
val store128_be : store_t 16 be_to_n U128.v

val load16_le  : load_t  2 le_to_n U16.v
val load32_le  : load_t  4 le_to_n U32.v
val load64_le  : load_t  8 le_to_n U64.v
val load128_le : load_t 16 le_to_n U128.v

val load16_be  : load_t  2 be_to_n U16.v
val load32_be  : load_t  4 be_to_n U32.v
val load64_be  : load_t  8 be_to_n U64.v
val load128_be : load_t 16 be_to_n U128.v
