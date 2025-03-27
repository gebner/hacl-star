module Lib.ByteBufferPulse
#lang-pulse

open Lib.IntTypes

module Loops = Lib.LoopCombinators
module Raw = Lib.RawIntTypes

friend Lib.ByteSequence
friend Lib.IntTypes
friend FStar.Endianness

module E = Lib.EndiannessPulse

(*
 * Despite befriending IntTypes this module enforces secrecy. The only exception,
 * for backwards compatibility, is `lbytes_eq`, which declassifies its result.
 *
 * We befriend IntTypes (or use RawIntTypes) to call into E library
 * for endianness conversions, which uses public machine integers.
 * E.g. `uint_to_bytes_le` loads a secret integer into a buffer of secret bytes by
 * internally casting the integer to a public machine integer, calling into LowStar,
 * and converting the result back to secret bytes.
 *
 * We use RawIntTypes when possible and only when this would be inconvenient
 * rely on opening the definitions in IntTypes. Specifically, only
 * `uint_from_bytes_le`, uint_from_bytes_be`, `uint_to_bytes_le`, and `uint_to_bytes_be`
 * rely on definitions in IntTypes. Alternatively, RawIntTypes could be used to cast
 * sequences and buffers of secret integers to sequences and buffers of machine integers,
 * but this would be too cumbersome.
*)

let uint_to_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> E.htobe16 u
  | U16, SEC -> Raw.u16_from_UInt16 (E.htobe16 (Raw.u16_to_UInt16 u))
  | U32, PUB -> E.htobe32 u
  | U32, SEC -> Raw.u32_from_UInt32 (E.htobe32 (Raw.u32_to_UInt32 u))
  | U64, PUB -> E.htobe64 u
  | U64, SEC -> Raw.u64_from_UInt64 (E.htobe64 (Raw.u64_to_UInt64 u))

let uint_to_le #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> E.htole16 u
  | U16, SEC -> Raw.u16_from_UInt16 (E.htole16 (Raw.u16_to_UInt16 u))
  | U32, PUB -> E.htole32 u
  | U32, SEC -> Raw.u32_from_UInt32 (E.htole32 (Raw.u32_to_UInt32 u))
  | U64, PUB -> E.htole64 u
  | U64, SEC -> Raw.u64_from_UInt64 (E.htole64 (Raw.u64_to_UInt64 u))

let uint_from_be #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> E.be16toh u
  | U16, SEC -> Raw.u16_from_UInt16 (E.be16toh (Raw.u16_to_UInt16 u))
  | U32, PUB -> E.be32toh u
  | U32, SEC -> Raw.u32_from_UInt32 (E.be32toh (Raw.u32_to_UInt32 u))
  | U64, PUB -> E.be64toh u
  | U64, SEC -> Raw.u64_from_UInt64 (E.be64toh (Raw.u64_to_UInt64 u))

let uint_from_le #t #l u =
  match t, l with
  | U1, _ -> u
  | U8, _ -> u
  | U16, PUB -> E.le16toh u
  | U16, SEC -> Raw.u16_from_UInt16 (E.le16toh (Raw.u16_to_UInt16 u))
  | U32, PUB -> E.le32toh u
  | U32, SEC -> Raw.u32_from_UInt32 (E.le32toh (Raw.u32_to_UInt32 u))
  | U64, PUB -> E.le64toh u
  | U64, SEC -> Raw.u64_from_UInt64 (E.le64toh (Raw.u64_to_UInt64 u))

inline_for_extraction let sizet_of_size_t (x: size_t) : y:SizeT.t { v x == SizeT.v y } =
  assume SizeT.fits_u32;
  SizeT.uint32_to_sizet x

inline_for_extraction
fn buf_eq_mask' () : buf_eq_mask_t = #t #len1 #len2 b1 b2 len #vb1 #vb2 #pra #prb {
  let mut i = 0ul;
  let mut res = (ones t SEC <: int_t t SEC);
  while (let vi = !i; lt vi len)
    invariant cond. exists* vi vres.
      AP.pts_to b1 #pra vb1 ** AP.pts_to b2 #prb vb2 **
      pts_to res vres ** pts_to i vi **
      pure (cond == (lt vi len)) **
      pure (v vi <= v len /\
        v vres == v (BS.seq_eq_mask #t #(v len1) #(v len2) vb1 vb2 (v vi)))
  {
    let vi = !i;
    let z0 = !res;
    let b1_i = AP.(b1.(sizet_of_size_t vi));
    let b2_i = AP.(b2.(sizet_of_size_t vi));
    res := eq_mask b1_i b2_i &. z0;
    with z. assert pts_to res z;
    assert pure (z == BS.seq_eq_mask_inner #t #(v len1) #(v len2) vb1 vb2 (v len) (v vi) z0);
    i := add vi 1ul;
  };
  with vi. assert pts_to i vi ** pure (v vi == v len);
  !res;
}
inline_for_extraction let buf_eq_mask = buf_eq_mask' ()

#push-options "--debug SMTFail"
inline_for_extraction
fn lbytes_eq' () : lbytes_eq_t = #len b1 b2 #vb1 #vb2 #pra #prb {
  let z = buf_eq_mask #_ #len #len b1 b2 len;
  UInt8.eq (Raw.u8_to_UInt8 z) 255uy
}
inline_for_extraction let lbytes_eq = lbytes_eq' ()

inline_for_extraction
fn map2T (#a1 #a2 #b:Type0) (clen:size_t)
  (o:AP.ptr b) (f:(a1 -> a2 -> Tot b))
  (i1:AP.ptr a1) (i2:AP.ptr a2)
  (#vi1: erased (Seq.lseq a1 (v clen)))
  (#vi2: erased (Seq.lseq a2 (v clen)))
  #pr1 #pr2
  requires AP.pts_to i1 #pr1 vi1
  requires AP.pts_to i2 #pr2 vi2
  requires exists* (vo: Seq.lseq b (v clen)). AP.pts_to o vo
  ensures AP.pts_to i1 #pr1 vi1
  ensures AP.pts_to i2 #pr2 vi2
  ensures AP.pts_to o (Lib.Sequence.map2 #_ #_ #_ #(v clen) f vi1 vi2)
{
  let mut i = 0ul;
  while (let vi = !i; lt vi clen)
    invariant cond. exists* vo vi.
      pts_to i vi ** pts_to o vo **
      AP.pts_to i1 #pr1 vi1 ** AP.pts_to i2 #pr2 vi2 **
      pure (cond == lt vi clen) **
      pure (v vi <= v clen /\ Seq.length vo == v clen /\
        (forall (j: nat). j < v vi ==> Seq.index vo j == f (Seq.index vi1 j) (Seq.index vi2 j)))
  {
    let vi = !i;
    let i1_i = AP.(i1.(sizet_of_size_t vi));
    let i2_i = AP.(i2.(sizet_of_size_t vi));
    AP.(o.(sizet_of_size_t vi) <- f i1_i i2_i);
    i := add vi 1ul;
  };
  with vo. assert AP.pts_to o vo;
  assert pure (squash (Lib.Sequence.equal vo (Lib.Sequence.map2 #_ #_ #_ #(v clen) f vi1 vi2)));
}

inline_for_extraction
fn bug_mask_select' () : buf_mask_select_t = #t #len b1 b2 mask res #vb1 #vb2 #pra #prb {
  map2T len res (BS.mask_select mask) b1 b2
}
inline_for_extraction let buf_mask_select = bug_mask_select' ()

// #set-options "--max_fuel 1 --max_ifuel 1"

/// BEGIN using friend Lib.IntTypes

val nat_from_bytes_le_to_n: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_le #l b == FStar.Endianness.le_to_n b))
  (decreases (Seq.length b))
let rec nat_from_bytes_le_to_n l b =
  if Seq.length b = 0 then ()
  else nat_from_bytes_le_to_n l (Seq.tail b)

val nat_from_bytes_be_to_n: l:secrecy_level -> b:Seq.seq UInt8.t ->
  Lemma (ensures (BS.nat_from_bytes_be #l b == FStar.Endianness.be_to_n b))
  (decreases (Seq.length b))
let rec nat_from_bytes_be_to_n l b =
  if Seq.length b = 0 then ()
  else nat_from_bytes_be_to_n l (Seq.slice b 0 (Seq.length b - 1))

inline_for_extraction
fn uint_from_bytes_le' () : uint_from_bytes_le_t = #t #l i #i_0 #pri {
  nat_from_bytes_le_to_n l i_0;
  match t {
    U8 -> { AP.(i.(0sz)) }
    U16 -> { E.load16_le i }
    U32 -> { E.load32_le i }
    U64 -> { E.load64_le i }
    U128 -> { admit (); E.load128_le i }
  }
}
inline_for_extraction let uint_from_bytes_le = uint_from_bytes_le' ()

inline_for_extraction
fn uint_from_bytes_be' () : uint_from_bytes_be_t = #t #l i #i_0 #pri {
  nat_from_bytes_be_to_n l i_0;
  match t {
    U8 -> { AP.(i.(0sz)) }
    U16 -> { E.load16_be i }
    U32 -> { E.load32_be i }
    U64 -> { E.load64_be i }
    U128 -> { admit (); E.load128_be i }
  }
}
inline_for_extraction let uint_from_bytes_be = uint_from_bytes_be' ()

val nat_to_bytes_n_to_le: len:size_nat -> l:secrecy_level -> n:nat{n < pow2 (8 * len)} ->
  Lemma (ensures Seq.equal (FStar.Endianness.n_to_le len n)
                           (BS.nat_to_bytes_le #l len n))
  (decreases len)
let rec nat_to_bytes_n_to_le len l n =
  if len = 0 then () else
    begin
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (len - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (len - 1));
    nat_to_bytes_n_to_le (len - 1) l (n / 256)
    end

val nat_to_bytes_n_to_be: len:size_nat -> l:secrecy_level -> n:nat{n < pow2 (8 * len)} ->
  Lemma (ensures (Seq.equal (FStar.Endianness.n_to_be len n)
                            (BS.nat_to_bytes_be #l len n)))
  (decreases len)
let rec nat_to_bytes_n_to_be len l n =
  if len = 0 then () else
    begin
    Math.Lemmas.division_multiplication_lemma n (pow2 8) (pow2 (8 * (len - 1)));
    Math.Lemmas.pow2_plus 8 (8 * (len - 1));
    nat_to_bytes_n_to_be (len - 1) l (n / 256)
    end

let uint_to_bytes_le_to_n (t:inttype {unsigned t}) (l:secrecy_level) (n:uint_t t l) :
  Lemma (ensures Seq.equal (FStar.Endianness.n_to_le (numbytes t) (v n))
                           (BS.uint_to_bytes_le n)) =
  nat_to_bytes_n_to_le (numbytes t) l (v n)

fn uint_to_bytes_le' () : uint_to_bytes_le_t = #t #l o i #pri {
  nat_to_bytes_n_to_le (numbytes t) l (v i);
  match t {
    U1 -> {
      let i: uint_t U1 l = i;
      AP.(o.(0sz) <- i);
      with vo. assert AP.pts_to o vo;
      assert pure (Seq.equal vo (BS.nat_to_intseq_le_ #U8 #l (numbytes t) (Raw.uint_to_nat i)));
    }
    U8 -> {
      let i: uint_t U8 l = i;
      AP.(o.(0sz) <- i);
      with vo. assert AP.pts_to o vo;
      assert pure (Seq.equal vo (BS.nat_to_intseq_le_ #U8 #l (numbytes t) (Raw.uint_to_nat i)));
    }
    U16 -> {
      let i: uint_t U16 l = i;
      let i: uint_t U16 PUB = coerce_eq () i;
      E.store16_le o i;
      // uint_to_bytes_n_to_le _ _ i;
      nat_to_bytes_n_to_le (numbytes U16) PUB (v i);
      with vo. assert AP.pts_to o vo;
      assert pure (Seq.equal vo (BS.uint_to_bytes_le #t i));
    }
    _ -> { admit() }
  }
}

let uint_to_bytes_le #t #l o i =
  match t with
  | U1 | U8 ->
    o.(0ul) <- i;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 o) (BS.nat_to_intseq_le_ #U8 #l (numbytes t) (Raw.uint_to_nat i)))
  | U16 ->
    E.store16_le o (Raw.u16_to_UInt16 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U32 ->
    E.store32_le o (Raw.u32_to_UInt32 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U64 ->
    E.store64_le o (Raw.u64_to_UInt64 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)
  | U128 ->
    E.store128_le o (Raw.u128_to_UInt128 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_le (numbytes t) l (v i)

let uint_to_bytes_be #t #l o i =
  match t with
  | U1 | U8 ->
    o.(0ul) <- i;
    let h1 = ST.get () in
    assert (Seq.equal (as_seq h1 o) (BS.nat_to_intseq_be_ #U8 #l (numbytes t) (Raw.uint_to_nat i)))
  | U16 ->
    E.store16_be o (Raw.u16_to_UInt16 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U32 ->
    E.store32_be o (Raw.u32_to_UInt32 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U64 ->
    E.store64_be o (Raw.u64_to_UInt64 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)
  | U128 ->
    E.store128_be o (Raw.u128_to_UInt128 i);
    let h1 = ST.get () in
    nat_to_bytes_n_to_be (numbytes t) l (v i)

/// END using friend Lib.IntTypes

module Seq = Lib.Sequence

let uints_from_bytes_le #t #l #len o i =
  let h0 = ST.get() in
  [@ inline_let]
  let spec (h:mem) : GTot (j:size_nat{j < v len} -> uint_t t l) =
    let i0 = as_seq h i in
    fun j -> BS.uint_from_bytes_le (Seq.sub i0 (j * numbytes t) (numbytes t))
  in
  fill h0 len o spec (fun j ->
    let h = ST.get() in
    let bj = sub i (j *! (size (numbytes t))) (size (numbytes t)) in
    let r = uint_from_bytes_le bj in
    as_seq_gsub h i (j *! size (numbytes t)) (size (numbytes t));
    r);
  let h1 = ST.get() in
  assert (Seq.equal (as_seq h1 o) (BS.uints_from_bytes_le (as_seq h0 i)))

let uints_from_bytes_be #t #l #len o i =
  let h0 = ST.get() in
  [@ inline_let]
  let spec (h:mem) : GTot (j:size_nat{j < v len} -> uint_t t l) =
    let i0 = as_seq h i in
    fun j -> BS.uint_from_bytes_be (Seq.sub i0 (j * numbytes t) (numbytes t))
  in
  fill h0 len o spec (fun j ->
    let h = ST.get() in
    let bj = sub i (j *! (size (numbytes t))) (size (numbytes t)) in
    let r = uint_from_bytes_be bj in
    as_seq_gsub h i (j *! size (numbytes t)) (size (numbytes t));
    r);
  let h1 = ST.get() in
  assert (Seq.equal (as_seq h1 o) (BS.uints_from_bytes_be (as_seq h0 i)))

#push-options "--z3rlimit 300" // This proof is pretty flaky
let uints_to_bytes_le #t #l len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = BS.uints_to_bytes_le_inner (as_seq h i) in
  fill_blocks h0 (size (numbytes t)) len o a_spec (fun _ _ -> ()) (fun _ -> loc_none) spec
    (fun j -> uint_to_bytes_le (sub o (mul_mod j (size (numbytes t))) (size (numbytes t))) i.(j));
  norm_spec [delta_only [`%BS.uints_to_bytes_le]] (BS.uints_to_bytes_le (as_seq h0 i))

let uints_to_bytes_be #t #l len o i =
  let h0 = ST.get () in
  [@ inline_let]
  let a_spec (i:nat{i <= v len}) = unit in
  [@ inline_let]
  let spec (h:mem) = BS.uints_to_bytes_be_inner (as_seq h i) in
  fill_blocks h0 (size (numbytes t)) len o a_spec (fun _ _ -> ()) (fun _ -> loc_none) spec
    (fun j -> uint_to_bytes_be (sub o (mul_mod j (size (numbytes t))) (size (numbytes t))) i.(j));
  norm_spec [delta_only [`%BS.uints_to_bytes_be]] (BS.uints_to_bytes_be (as_seq h0 i))
#pop-options

let uint_at_index_le #t #l #len i idx =
  let b = sub i (idx *! (size (numbytes t))) (size (numbytes t)) in
  uint_from_bytes_le b

let uint_at_index_be #t #l #len i idx =
  let b = sub i (idx *! (size (numbytes t))) (size (numbytes t)) in
  uint_from_bytes_be b
