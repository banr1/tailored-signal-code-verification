/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderRepr
public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Hooks4K
public import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveExt
import LibsignalBinary.Proofs.SpqrV1.Top.EncodeVarint.Proof
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<spqr::v1::chunked::states::Message>::serialize`

Binary memory layout, separation-logic specification, and correctness proof for
`<spqr::v1::chunked::states::Message>::serialize` against `Message.serialize`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L35MessageSerialize
open Lean Elab Command ProofLib.ProgramReflection CryptoVerification.CodeLayout in
elab "gen_fn_decodes_n " tree:ident pfx:ident sym:str cnt:num : command => do
  let e ← liftTermElabM <| ProofLib.CodeLookup.lookupOff `CryptoVerification.libsignalSessionCode sym.getString
  let lo := Syntax.mkNumLit (toString e.val); let hi := Syntax.mkNumLit (toString (e.val + 4 * cnt.getNat))
  let r ← `(decodeRange| $lo:num → $hi:num); elabCommand (← `(command| gen_decodes $tree $pfx [$r:decodeRange]))
end CryptoVerification.SpqrV1.Layout.L35MessageSerialize

namespace CryptoVerification.SpqrV1.Top.MessageSerialize

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Top.EncodeVarint CryptoVerification.SpqrV1.Alloc
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L35MessageSerialize

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

gen_fn_decodes_n libsignalSessionCode_tree msgSerializeBin
  "<spqr::v1::chunked::states::Message>::serialize" 110

open Lean Elab Tactic in
/-- Fetch instructions in `[kStart, kEnd)` using decode lemmas in
    `CryptoVerification.SpqrV1.Top.MessageSerialize`. -/
elab "msgSerialize_fetches_range " b:term:max H:term:max hfn:ident
    kStart:num kEnd:num : tactic => do
  let e ← ProofLib.CodeLookup.lookupOff `CryptoVerification.libsignalSessionCode
    "<spqr::v1::chunked::states::Message>::serialize"
  let off := e.val
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hex := String.ofList (Nat.toDigits 16 (off + k))
    let dec := mkIdent (`CryptoVerification.SpqrV1.Top.MessageSerialize |>.str
      ("msgSerializeBin_decode_0" ++ "x" ++ hex))
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

/-!
## 1. Binary Layout of `spqr::v1::chunked::states::Message` (`48` bytes, align `8`)

* `+0x00..+0x08` (`8`B): `epoch : u64` (`Epoch = BitVec 64`).
* `+0x08..+0x09` (`1`B): `payload` discriminant (`0#8..6#8` = `MessageType.toU8`):
  - `0#8` (`.none`): `+0x09..+0x30` (`39`B) padding;
  - `4#8` (`.ct1Ack b`): `+0x09..+0x0a` (`1`B) `bool` (`if b then 1#8 else 0#8`), `+0x0a..+0x30` (`38`B) padding;
  - `1#8, 2#8, 3#8, 5#8, 6#8` (`.hdr c`, `.ek c`, `.ekCt1Ack c`, `.ct1 c`, `.ct2 c`):
    `+0x09..+0x0a` (`1`B) padding, `+0x0a..+0x2c` (`34`B) `chunkAt (a + 0x0a#64) c`
    (`data : [u8; 32]` at `+0x0a..+0x2a`, `index : u16` at `+0x2a..+0x2c`),
    `+0x2c..+0x30` (`4`B) tail padding.
-/

abbrev messageSize : Nat := 48

/-- Memory representation of `MessagePayload P` at `a + 0x08#64` (`40` bytes). -/
def messagePayloadAt (P : PolyApi) (a : BitVec 64) (p : MessagePayload P) : SepProp :=
  let toC := fun c : P.Chunk => ({ index := P.chunkIndex c, data := P.chunkData c } : Chunk)
  match p with
  | .none =>
      ((a + 0x08#64) ↦₈ 0#8) ∗ memRegion (a + 0x09#64) 39
  | .hdr c =>
      ((a + 0x08#64) ↦₈ 1#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ek c =>
      ((a + 0x08#64) ↦₈ 2#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ekCt1Ack c =>
      ((a + 0x08#64) ↦₈ 3#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ct1Ack b =>
      ((a + 0x08#64) ↦₈ 4#8) ∗ ((a + 0x09#64) ↦₈ (if b then 1#8 else 0#8)) ∗
        memRegion (a + 0x0a#64) 38
  | .ct1 c =>
      ((a + 0x08#64) ↦₈ 5#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4
  | .ct2 c =>
      ((a + 0x08#64) ↦₈ 6#8) ∗ memRegion (a + 0x09#64) 1 ∗
        chunkAt (a + 0x0a#64) (toC c) ∗ memRegion (a + 0x2c#64) 4

/-- Memory representation of `spqr::v1::chunked::states::Message` (`48` bytes at `a`). -/
def messageAt (P : PolyApi) (a : BitVec 64) (m : Message P) : SepProp :=
  (a ↦₆₄ m.epoch) ∗ messagePayloadAt P a m.payload

/-! ## 2. Symbol Name, Stack Budget, and Specification of `<Message>::serialize` -/

abbrev messageSerializeName : String :=
  "<spqr::v1::chunked::states::Message>::serialize"

/-- Stack budget for `<Message>::serialize`:
    * own frame `0x50 = 80` bytes (`+0x000: sub sp, sp, #0x50`);
    * calls `spqr::encode_varint` (`spqrEncodeVarintStackX = 0x50 + extHookStack = 16464`) and
    `do_reserve_and_handle [local#7]` (`doReserveStack = 4208 ≤ spqrEncodeVarintStackX`). -/
abbrev messageSerializeStackX : Nat := 0x50 + spqrEncodeVarintStackX

/-- Ghost state for `<Message>::serialize`: `(msgA, index, ret, msg)`. -/
structure MessageSerializeGhost (P : PolyApi) where
  msgA : BitVec 64
  index : BitVec 32
  ret : BitVec 64
  msg : Message P

/-- Specification of `<spqr::v1::chunked::states::Message>::serialize` against `Message.serialize`:
    * `x0 = x.msgA` (`&Message`), `w1 = x.index` (`u32`), `x8 = x.ret` (`*mut Vec<u8>`).
    * Preserves `messageAt P x.msgA x.msg` and writes `vecU8 A x.ret (x.msg.serialize x.index)`.
    * Panics only on OOM (`allocFailedIn`). -/
def messageSerializeSpecX (P : PolyApi) (A : RustAlloc) : Spec (MessageSerializeGhost P) where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.msgA ∧ (s.readReg64 .x1).setWidth 32 = x.index ∧
      s.readReg64 .x8 = x.ret⌝ ∗
      messageAt P x.msgA x.msg ∗ memRegion x.ret 24 ∗ A.pool ∗ stackAt s.sp messageSerializeStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      messageAt P x.msgA x.msg ∗
      vecU8 A x.ret (x.msg.serialize x.index) ∗
      A.pool ∗ stackAt s0.sp messageSerializeStackX
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `<Message>::serialize` meets `messageSerializeSpecX P A` on `tripleRatchetProgAtExt b ext`. -/
def MessageSerializeOkExt (P : PolyApi) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr messageSerializeName)
    (messageSerializeSpecX P A)

/-- `<Message>::serialize` meets `(messageSerializeSpecX P A).inImage img` on
    `tripleRatchetProgAtExt img.base ext`. -/
def MessageSerializeOkX (P : PolyApi) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr messageSerializeName)
    ((messageSerializeSpecX P A).inImage img)

theorem messageSerialize_fnOff :
    libsignalSessionCode.fnOff messageSerializeName =
      num% (ls_off% "<spqr::v1::chunked::states::Message>::serialize") :=
  ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize"

/-! ## 3. Pure & Separation-Logic Helpers for `<Message>::serialize` -/

theorem encodeVarintLoop_length_le (fuel : Nat) (a : BitVec 64) :
    (encodeVarintLoop fuel a).length ≤ fuel := by
  induction fuel generalizing a with
  | zero => simp [encodeVarintLoop]
  | succ fuel ih =>
    simp only [encodeVarintLoop]; split
    · simp
    · simp only [List.length_cons]; have := ih (a >>> 7); omega

theorem encode_varint_eq_append (a : BitVec 64) (into : Bytes) :
    CryptoVerification.LibsignalSpqrV1.encode_varint a into =
      into ++ encodeVarintLoop MAX_VARINT_BYTES_LEN a := rfl

theorem encode_varint_length_le (a : BitVec 64) (into : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint a into).length ≤ into.length + 10 := by
  rw [encode_varint_eq_append, List.length_append]
  have h := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN a
  have hm : MAX_VARINT_BYTES_LEN = 10 := rfl; omega

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_lo_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 0 64 = lo := by bv_kernel

@[local simp, local arm64_norm, local wp_norm]
theorem extractLsb_hi_append64 (hi lo : BitVec 64) : (hi ++ lo).extractLsb' 64 64 = hi := by bv_kernel

theorem stackAt_messageSerialize_eq (sp : BitVec 64) :
    stackAt sp messageSerializeStackX =
      stackAt (sp - 80#64) spqrEncodeVarintStackX ∗
      (∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64, ∃∗ v56 : BitVec 64,
       ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64, ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64,
       ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 80#64) ↦₆₄ v80) ∗ ((sp - 72#64) ↦₆₄ v72) ∗ ((sp - 64#64) ↦₆₄ v64) ∗ ((sp - 56#64) ↦₆₄ v56) ∗
        ((sp - 48#64) ↦₆₄ v48) ∗ ((sp - 40#64) ↦₆₄ v40) ∗ ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8)) := by
  change stackAt sp (spqrEncodeVarintStackX + 8 * 10) = _
  rw [ProofLib.stackAt_split_cells sp spqrEncodeVarintStackX 10 (by decide)]; congr 1; cells_unfold

theorem stackAt_spqrEncodeVarint_to_allocHook (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      memRegion (sp - 16464#64) 12368 ∗ stackAt sp allocHookStack := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 allocHookStack = sp - BitVec.ofNat 64 spqrEncodeVarintStackX + 12368#64 := by
    change sp - 4096#64 = sp - 16464#64 + 12368#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 spqrEncodeVarintStackX)
    (n := 12368) (k := allocHookStack) (b' := sp - BitVec.ofNat 64 allocHookStack) rfl hbase (by decide)

theorem stackAt_spqrEncodeVarint_to_doReserve (sp : BitVec 64) :
    stackAt sp spqrEncodeVarintStackX =
      memRegion (sp - 16464#64) 12256 ∗ stackAt sp doReserveStack := by
  unfold stackAt
  have hbase : sp - BitVec.ofNat 64 doReserveStack = sp - BitVec.ofNat 64 spqrEncodeVarintStackX + 12256#64 := by
    change sp - 4208#64 = sp - 16464#64 + 12256#64; bv_omega
  exact ProofLib.memRegion_split' (b := sp - BitVec.ofNat 64 spqrEncodeVarintStackX)
    (n := 12256) (k := doReserveStack) (b' := sp - BitVec.ofNat 64 doReserveStack) rfl hbase (by decide)

theorem memRegion_40_split_1_39 (ptr : BitVec 64) :
    memRegion ptr 40 = (∃∗ b0 : BitVec 8, (ptr ↦₈ b0)) ∗ memRegion (ptr + 1#64) 39 := by
  rw [ProofLib.memRegion_split' (b := ptr) (n := 1) (k := 39)
      (b' := ptr + 1#64) rfl (by bv_omega) (by decide), ProofLib.memRegion_one]

def pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : BitVec 64 :=
  b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0

theorem unpack64_pack64 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    unpack64 (pack64 b0 b1 b2 b3 b4 b5 b6 b7) = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  dsimp only [unpack64, pack64]
  have e0 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_kernel
  have e1 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_kernel
  have e2 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_kernel
  have e3 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_kernel
  have e4 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 32 8 = b4 := by bv_kernel
  have e5 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 40 8 = b5 := by bv_kernel
  have e6 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 48 8 = b6 := by bv_kernel
  have e7 : (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0).extractLsb' 56 8 = b7 := by bv_kernel
  rw [e0, e1, e2, e3, e4, e5, e6, e7]

theorem list_eq_unpack64_of_len8 :
    ∀ (bs : List (BitVec 8)), bs.length = 8 → ∃ w : BitVec 64, bs = unpack64 w
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    ⟨pack64 b0 b1 b2 b3 b4 b5 b6 b7, (unpack64_pack64 b0 b1 b2 b3 b4 b5 b6 b7).symm⟩

theorem list_eq_unpack64_4_of_len32 (ds : List (BitVec 8)) (h : ds.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64,
      ds = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 := by
  let l1 := ds.drop 8; let l2 := l1.drop 8; let l3 := l2.drop 8
  have h3 : l2.take 8 ++ l3 = l2 := List.take_append_drop 8 l2
  have h2 : l1.take 8 ++ l2 = l1 := List.take_append_drop 8 l1
  have h1 : ds.take 8 ++ l1 = ds := List.take_append_drop 8 ds
  have hsplit : ds = ds.take 8 ++ l1.take 8 ++ l2.take 8 ++ l3 := by
    rw [List.append_assoc (ds.take 8 ++ l1.take 8), h3, List.append_assoc (ds.take 8), h2, h1]
  obtain ⟨w0, hw0⟩ := list_eq_unpack64_of_len8 (ds.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := list_eq_unpack64_of_len8 (l1.take 8) (by simp [l1, h])
  obtain ⟨w2, hw2⟩ := list_eq_unpack64_of_len8 (l2.take 8) (by simp [l2, l1, h])
  obtain ⟨w3, hw3⟩ := list_eq_unpack64_of_len8 l3 (by simp [l3, l2, l1, h])
  exact ⟨w0, w1, w2, w3, by rw [hsplit, hw0, hw1, hw2, hw3]⟩

theorem pointsToBytes_unpack64_4_eq (a : BitVec 64) (w0 w1 w2 w3 : BitVec 64) :
    (a ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3)) =
      (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) := by
  have hlen : ∀ w : BitVec 64, (unpack64 w).length = 8 := fun _ => rfl
  rw [List.append_assoc (unpack64 w0 ++ unpack64 w1) (unpack64 w2) (unpack64 w3),
    List.append_assoc (unpack64 w0) (unpack64 w1) (unpack64 w2 ++ unpack64 w3),
    pointsToBytes_append, hlen w0, pointsToBytes_append, hlen w1, pointsToBytes_append, hlen w2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, ← pointsTo64_eq_pointsToBytes]

theorem memRegion_32_words4 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗ (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗ (∃∗ d0 : BitVec 64, a ↦₆₄ d0) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24) (b' := a + 8#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16) (b' := a + 16#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8) (b' := a + 24#64) rfl (by bv_omega) (by decide),
    ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
    ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]
  ac_rfl

theorem vecU8At_eq_header_buf (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Buf; simp only [BitVec.ofNat_eq_ofNat]; ac_rfl

theorem pointsTo64_pair (a lo hi : BitVec 64) :
    (a ↦₆₄ lo) ∗ ((a + 8#64) ↦₆₄ hi) = (a ↦₁₂₈ (hi ++ lo)) := by
  unfold pointsTo128; rw [extractLsb_lo_append64, extractLsb_hi_append64]

theorem vecU8At_init_40_one (A : RustAlloc) (v ptr : BitVec 64) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ 40#64) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ 1#64) ∗
      A.live ptr 40 1 ∗ (ptr ↦₈ 1#8) ∗ memRegion (ptr + 1#64) 39) =
    vecU8At A v 40#64 ptr [1#8] := by
  rw [vecU8At_eq_header_buf]; unfold vecU8Buf
  have h40_ne : (40#64 : BitVec 64) ≠ 0#64 := by decide
  have h40_toNat : (40#64 : BitVec 64).toNat = 40 := rfl
  have h1 : (ptr ↦ₛ [1#8]) = (ptr ↦₈ 1#8) := by rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  simp only [List.length_singleton, BitVec.ofNat_eq_ofNat, h40_ne, ↓reduceIte,
    h40_toNat, h1, Nat.reduceSub]
  have hpure : ((1 : Nat) ≤ 40 ∧ 40 < 2 ^ 63 ∧ ptr ≠ 0#64) = True := by simp [hptr]
  rw [hpure, pure_true, emp_sepConj]

/-- Callee-saved registers `x23..x28`, `calleeSavedVRegs`, + `StepInv` preserved across
    `<Message>::serialize`. -/
def MsgSerializeCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧ s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧ s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧ s.readReg64 .x28 = s0.readReg64 .x28 ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧ StepInv s0 s

theorem MsgSerializeCalleeSaved.refl (s : State) : MsgSerializeCalleeSaved s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, StepInv.refl s⟩

theorem MsgSerializeCalleeSaved.trans {s0 s1 s2 : State}
    (h1 : MsgSerializeCalleeSaved s0 s1) (h2 : MsgSerializeCalleeSaved s1 s2) :
    MsgSerializeCalleeSaved s0 s2 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1,
   h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.1.trans h1.2.2.2.2.1,
   h2.2.2.2.2.2.1.trans h1.2.2.2.2.2.1,
   h2.2.2.2.2.2.2.1.trans h1.2.2.2.2.2.2.1,
   h1.2.2.2.2.2.2.2.trans h2.2.2.2.2.2.2.2⟩

theorem MsgSerializeCalleeSaved.of_calleeSavedPreserved {s1 s2 : State}
    (h : CalleeSavedPreserved s1 s2) (hinv : StepInv s1 s2) : MsgSerializeCalleeSaved s1 s2 :=
  ⟨h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
   h.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

/-- Execute a `bl spqr::encode_varint` call inside `<Message>::serialize` when the vector at `v
    = sp - 72#64` has capacity `40#64` and `curBs.length + 10 ≤ 40`, preserving `cap = 40#64`
    and `ptr`. -/
theorem step_call_spqrEncodeVarint_40 {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (henc : SpqrEncodeVarintOkExt b A ext)
    (val v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length + 10 ≤ 40)
    {x : MessageSerializeGhost P_api} {R : SepProp}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P = (vecU8At A v 40#64 ptr curBs ∗ A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        ((vecU8At A v 40#64 ptr (CryptoVerification.LibsignalSpqrV1.encode_varint val curBs) ∗
          A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  refine SepWPp.call_cs (x := EncodeVarintGhost.mk val v 40#64 ptr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [spqrEncodeVarintSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, Or.inl hlen⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [spqrEncodeVarintSpecX, messageSerializeSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [spqrEncodeVarintSpecX, hsp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' =>
      SepWPp.pure_elim fun htrm => SepWPp.pure_elim fun hcap_prop => ?_
    have hloop_le : curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ (40#64 : BitVec 64).toNat := by
      have h1 := encodeVarintLoop_length_le MAX_VARINT_BYTES_LEN val
      have hm : MAX_VARINT_BYTES_LEN = 10 := rfl
      change curBs.length + (encodeVarintLoop MAX_VARINT_BYTES_LEN val).length ≤ 40; omega
    obtain ⟨hcap_eq, hptr_eq⟩ := hcap_prop.2 hloop_le
    subst hcap_eq; subst hptr_eq
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr)
        hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
        (hcs.trans (MsgSerializeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))

def vecRest32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
    memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))

theorem vecU8Buf_eq_open_32 (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length + 32 ≤ cap.toNat) :
    vecU8Buf A cap ptr bs =
      (∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
        ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ d0) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ d1) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ d2) ∗
        ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ d3) ∗
        vecRest32 A cap ptr bs) := by
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hle
  have hpure : (bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) =
      (bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0) := by
    apply propext; constructor <;> (intro ⟨_, h2, h3⟩; exact ⟨by omega, h2, h3⟩)
  unfold vecU8Buf vecRest32
  simp only [hne, ↓reduceIte, hpure]
  have hsplit := memRegion_split (ptr + BitVec.ofNat 64 bs.length) 32 (cap.toNat - (bs.length + 32)) (by omega)
  rw [show 32 + (cap.toNat - (bs.length + 32)) = cap.toNat - bs.length by omega,
    BitVec.add_assoc, ← BitVec.ofNat_add, memRegion_32_words4] at hsplit
  rw [hsplit]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  congr 1; funext d0; congr 1; funext d1; congr 1; funext d2; congr 1; funext d3; ac_rfl

theorem vecU8Buf_append_32_eq (A : RustAlloc) (cap ptr : BitVec 64) (bs ds : List (BitVec 8))
    (w0 w1 w2 w3 : BitVec 64)
    (hle : bs.length + 32 ≤ cap.toNat)
    (hds : ds = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3)
    (hlen32 : ds.length = 32) :
    ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
    ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) ∗
    vecRest32 A cap ptr bs =
      vecU8Buf A cap ptr (bs ++ ds) := by
  have hne : cap ≠ 0 := by intro h0; subst h0; simp at hle
  unfold vecU8Buf vecRest32
  simp only [hne, ↓reduceIte]
  have h4 :
      ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) =
      ((ptr + BitVec.ofNat 64 bs.length) ↦ₛ ds) := by
    rw [hds, pointsToBytes_unpack64_4_eq]
  have hreassoc :
      ((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
      ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3) ∗
      (⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32))) =
      ⌜bs.length + 32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗
        ((ptr ↦ₛ bs) ∗
          (((ptr + BitVec.ofNat 64 bs.length) ↦₆₄ w0) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 8#64) ↦₆₄ w1) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 16#64) ↦₆₄ w2) ∗
           ((ptr + BitVec.ofNat 64 bs.length + 24#64) ↦₆₄ w3))) ∗
        memRegion (ptr + BitVec.ofNat 64 (bs.length + 32)) (cap.toNat - (bs.length + 32)) := by
    ac_rfl
  rw [hreassoc, h4, ← pointsToBytes_append]
  simp only [List.length_append, hlen32]

theorem spqrEncodeVarint_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName +
      bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize") =
      (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName := by
  have h1 := messageSerialize_fnOff; have h2 := spqrEncodeVarint_fnOff
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, messageSerializeName, spqrEncodeVarintName, h1, h2]
  bv_omega

theorem doReserve7_fnAddr_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName +
      bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
        "<spqr::v1::chunked::states::Message>::serialize") =
      (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
  have h1 := messageSerialize_fnOff
  have h2 := ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, messageSerializeName, doReserve7Name, h1, h2]
  bv_omega

private structure MsgSerializeAlloc (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  alloc : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr allocName) (rustAllocSpec A)
  shim : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr shimName) sessionShimSpec
  doReserve7 : subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr doReserve7Name) (doReserveSpec A)

attribute [local irreducible] Program.fnAddr

/-- Execute `bl do_reserve_and_handle [local#7]` (`0x530a0`) inside `<Message>::serialize` when
    `cap = 40#64`, `curBs.length ≤ 32`, and `additional = 32`, growing capacity to `80#64`. -/
private theorem step_call_doReserve7_40 {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : MsgSerializeAlloc b A ext)
    (v ptr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen : curBs.length ≤ 32)
    {x : MessageSerializeGhost P_api} {R : SepProp}
    {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 80#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx2 : s.readReg64 .x2 = 32#64) (hx3 : s.readReg64 .x3 = 1#64) (hx4 : s.readReg64 .x4 = 1#64)
    (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P = (vecU8At A v 40#64 ptr curBs ∗ A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
    (hnext : ∀ (sm : State) (ptr' : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 → sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .fp = s.readReg64 .fp → MsgSerializeCalleeSaved s0 sm →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        ((vecU8At A v 80#64 ptr' curBs ∗
          A.pool ∗ stackAt (sp - 80#64) spqrEncodeVarintStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_80_aligned halign
  have hres_eq : reserveCap (40#64 : BitVec 64).toNat curBs.length 32 = 80 := by
    unfold reserveCap; change max (max (curBs.length + 32) (2 * 40)) 8 = 80; omega
  have hx1_toNat : (s.readReg64 .x1).toNat = curBs.length := by
    rw [hx1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hx2_toNat : (s.readReg64 .x2).toNat = 32 := by rw [hx2]; rfl
  refine SepWPp.call_cs (x := DoReserveCall.mk v 40#64 ptr curBs 32)
    (F := memRegion (sp - 80#64 - 16464#64) 12256 ∗ F)
    hA.doReserve7 hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP, stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)] at hm
    simp only [doReserveSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1_toNat, hx2_toNat, hx3, hx4, by rw [hres_eq]; decide⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [doReserveSpec, messageSerializeSpecX, allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    simp only [doReserveSpec, hsp, hres_eq, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun ptr' => SepWPp.pure_elim fun htrm => ?_
    refine SepWPp.weaken_pre ?_ (hnext sm ptr' hpcm hrunm hspm (htrm.trans htr)
      hcsm.1 hcsm.2.1 hcsm.2.2.1 hcsm.2.2.2.1 hcsm.2.2.2.2.2.2.2.2.2.2.1
      (hcs.trans (MsgSerializeCalleeSaved.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_spqrEncodeVarint_to_doReserve (sp - 80#64)]
    exact Entails.of_eq (by ac_rfl)

theorem rem40_ult_31_of_le {n : Nat} (hle : n + 32 ≤ 40) :
    (31#64).ult (40#64 - BitVec.ofNat 64 n) = true ∧
    (40#64 - BitVec.ofNat 64 n).ule 31#64 = false := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (40#64 - BitVec.ofNat 64 n).toNat = 40 - n := by
    rw [BitVec.toNat_sub_of_le]
    · simp [hn]
    · rw [BitVec.le_def, hn]; change n ≤ 40; omega
  rw [BitVec.ult_eq_decide, BitVec.ule_eq_decide, hsub]
  change decide (31 < 40 - n) = true ∧ decide (40 - n ≤ 31) = false
  exact ⟨decide_eq_true (by omega), decide_eq_false (by omega)⟩

theorem rem40_ult_31_of_gt {n : Nat} (hgt : ¬ (n + 32 ≤ 40)) (hle40 : n ≤ 40) :
    (31#64).ult (40#64 - BitVec.ofNat 64 n) = false ∧
    (40#64 - BitVec.ofNat 64 n).ule 31#64 = true := by
  have hn : (BitVec.ofNat 64 n).toNat = n := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hsub : (40#64 - BitVec.ofNat 64 n).toNat = 40 - n := by
    rw [BitVec.toNat_sub_of_le]
    · simp [hn]
    · rw [BitVec.le_def, hn]; change n ≤ 40; omega
  rw [BitVec.ult_eq_decide, BitVec.ule_eq_decide, hsub]
  change decide (31 < 40 - n) = false ∧ decide (40 - n ≤ 31) = true
  exact ⟨decide_eq_false (by omega), decide_eq_true (by omega)⟩

theorem vecU8At_sp72_eq (A : RustAlloc) (sp cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (sp - 72#64) cap ptr bs =
      ((sp - 72#64) ↦₆₄ cap) ∗ ((sp - 64#64) ↦₆₄ ptr) ∗
      ((sp - 56#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs := by
  rw [vecU8At_eq_header_buf]; simp only [arm64_norm]

/-! ## 4. Epilogue & Chunk Step Lemmas for `<Message>::serialize` -/

/-- Shared return tail (`+0x168..+0x188`, `360..392`): stores `(ptrFinal, capFinal, len)` to
    `[x19]`, restores callee-saved registers & `sp`, and returns. -/
theorem step_msgSerialize_ret {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (capFinal ptrFinal v80 v56 r0 r1 r2 : BitVec 64) (bsFinal : List (BitVec 8))
    (hser : bsFinal = x.msg.serialize x.index) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 360#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 bsFinal.length) (hx19 : s.readReg64 .x19 = x.ret)
    (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P = (((s0.sp - 72#64) ↦₆₄ capFinal) ∗ ((s0.sp - 64#64) ↦₆₄ ptrFinal) ∗
       ((s0.sp - 56#64) ↦₆₄ v56) ∗ vecU8Buf A capFinal ptrFinal bsFinal ∗ messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 360 392
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP; rcases hcs with ⟨h23, h24, h25, h26, h27, h28, hvregs, _⟩
  apply SepWPp.of_sepWP (mid := s0.readReg64 .lr); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine ⟨?_, by simp only [arm64_norm, *], by encodedLen_cc_close⟩; intro hm_f
  have hvec_pack : (x.ret ↦₆₄ capFinal) ∗ ((x.ret + 8#64) ↦₆₄ ptrFinal) ∗
      ((x.ret + 16#64) ↦₆₄ BitVec.ofNat 64 (x.msg.serialize x.index).length) ∗
      vecU8Buf A capFinal ptrFinal bsFinal = vecU8At A x.ret capFinal ptrFinal (x.msg.serialize x.index) := by
    rw [← hser, vecU8At_eq_header_buf]
  simp only [messageSerializeSpecX, vecU8, stackAt_messageSerialize_eq, sepExists_sepConj_left,
    sepExists_sepConj_right, satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v80, capFinal, ptrFinal, v56, s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x22,
    s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19, capFinal, ptrFinal, by simp only [arm64_norm, *], ?_⟩
  rw [← hvec_pack]; convert hm_f using 1; ac_rfl

/-- Non-chunk epilogue (`+0x15c..+0x188`, `348..392`): stores `tag` and finishes via
    `step_msgSerialize_ret`. -/
theorem step_msgSerialize_epilogue_no_chunk {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (ptr v80 r0 r1 r2 : BitVec 64) (bs2 : List (BitVec 8)) (tag : BitVec 8)
    (hlt40 : bs2.length < (40#64 : BitVec 64).toNat) (hser : bs2 ++ [tag] = x.msg.serialize x.index) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 348#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length)
    (hx22 : (s.readReg64 .x22).setWidth 8 = tag) (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P = (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗ messageAt P_api x.msgA x.msg ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 348 360
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP; have hlen1 := bv_len_add_one bs2 tag
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs2, vecU8Buf_eq_open_one A 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]; refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 360#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
  rw [vecU8Buf_snoc_eq A 40#64 ptr bs2 tag hlt40]
  exact step_msgSerialize_ret b A ext x 40#64 ptr v80 (BitVec.ofNat 64 bs2.length) r0 r1 r2 (bs2 ++ [tag]) hser
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩) (by ac_rfl)

/-- Chunk 32-byte copy and epilogue (`+0x13c..+0x158` + `+0x168..+0x188`, `316..344` +
    `360..392`). -/
theorem step_msgSerialize_copy_and_epilogue {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (c : P_api.Chunk) (capFinal ptrFinal v80 r0 r1 r2 : BitVec 64)
    (bs4 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hle32 : bs4.length + 32 ≤ capFinal.toNat)
    (hser : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index)
    (hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg) {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 316#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 bs4.length)
    (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P = (vecU8At A (s0.sp - 72#64) capFinal ptrFinal bs4 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 316 344
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  have hdata_len : (P_api.chunkData c).toList.length = 32 := (P_api.chunkData c).property
  obtain ⟨w0, w1, w2, w3, hw⟩ := list_eq_unpack64_4_of_len32 (P_api.chunkData c).toList hdata_len
  have hchunk_unfold : chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
      ((x.msgA + 0x0a#64) ↦₆₄ w0) ∗ ((x.msgA + 0x12#64) ↦₆₄ w1) ∗ ((x.msgA + 0x1a#64) ↦₆₄ w2) ∗
      ((x.msgA + 0x22#64) ↦₆₄ w3) ∗ ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; dsimp only; rw [hw, pointsToBytes_unpack64_4_eq]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  have hlen32_bv : BitVec.ofNat 64 bs4.length + 32#64 = BitVec.ofNat 64 (bs4 ++ (P_api.chunkData c).toList).length := by
    simp only [List.length_append, hdata_len, BitVec.ofNat_add]
  rw [hchunk_unfold, vecU8At_sp72_eq A s0.sp capFinal ptrFinal bs4, vecU8Buf_eq_open_32 A capFinal ptrFinal bs4 hle32]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  apply SepWPp.of_sepWP_cs (mid := entry + 360#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
  rw [vecU8Buf_append_32_eq A capFinal ptrFinal bs4 (P_api.chunkData c).toList w0 w1 w2 w3 hle32 hw hdata_len]
  exact step_msgSerialize_ret b A ext x capFinal ptrFinal v80 (BitVec.ofNat 64 bs4.length) r0 r1 r2
    (bs4 ++ (P_api.chunkData c).toList) hser
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step⟩)
    (by rw [← hmsg_eq, hchunk_unfold]; ac_rfl)

/-- Full chunk branch (`+0x10c..+0x188` & `+0x190..+0x1ac`, `268..392` & `400..428`): appends
    `tag` to `bs2`, calls `spqr::encode_varint` on `(P_api.chunkIndex c).zeroExtend 64`,
    reserves 32 bytes if `40 - bs4.length ≤ 31`, and finishes via
    `step_msgSerialize_copy_and_epilogue`. -/
private theorem step_msgSerialize_chunk {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : MsgSerializeAlloc b A ext) (henc : SpqrEncodeVarintOkExt b A ext)
    {s0 s : State} (x : MessageSerializeGhost P_api)
    (c : P_api.Chunk) (ptr v80 r0 r1 r2 : BitVec 64)
    (bs2 : List (BitVec 8)) (tag : BitVec 8) (msgTail : SepProp)
    (hlen21 : bs2.length ≤ 21)
    (hser : encode_chunk c (bs2 ++ [tag]) = x.msg.serialize x.index)
    (hmsg_eq :
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
      msgTail = messageAt P_api x.msgA x.msg)
    {R P : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 268#64)
    (hrun : s.status = .Running) (hsp : s.sp = s0.sp - 80#64) (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = x.ret) (hx20 : s.readReg64 .x20 = x.msgA)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 bs2.length) (hx22 : (s.readReg64 .x22).setWidth 8 = tag)
    (hcs : MsgSerializeCalleeSaved s0 s)
    (hP : P =
      (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
       chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s P
      (fun sf P_f => ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 268 316
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 400 428
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by change bs2.length < 40; omega
  have hlen1 := bv_len_add_one bs2 tag
  have hchunk_idx :
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } =
        ((x.msgA + 0x0a#64) ↦ₛ (P_api.chunkData c).toList) ∗
        ((x.msgA + 0x2a#64) ↦₁₆ P_api.chunkIndex c) := by
    unfold chunkAt chunkIndexOff; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  rw [hchunk_idx, vecU8At_sp72_eq A s0.sp 40#64 ptr bs2, vecU8Buf_eq_open_one A 40#64 ptr bs2 hlt40]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs
    (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hinv_step1
  rw [vecU8Buf_snoc_eq A 40#64 ptr bs2 tag hlt40]
  have hvec_bs3 := (vecU8At_sp72_eq A s0.sp 40#64 ptr (bs2 ++ [tag])).symm
  have hpc_enc :
      entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize") =
        (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName := by
    rw [← hentry, spqrEncodeVarint_fnAddr_eq]
  refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (R := R)
    b A ext henc ((P_api.chunkIndex c).zeroExtend 64) (s0.sp - 72#64) ptr s0.sp (entry + 296#64)
    (bs2 ++ [tag]) (by simp only [List.length_append, List.length_singleton]; omega)
    (F :=
      (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
      chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (hcs.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
      by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step1⟩)
    (by rw [hchunk_idx, ← hvec_bs3]; ac_rfl) ?_
  intro sm hpcm hrunm hspm htrm hx19m hx20m _ _ _ hcsm
  have hx19m' : sm.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
  have hx20m' : sm.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
  let bs4 := CryptoVerification.LibsignalSpqrV1.encode_varint ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
  have hbs4_len : bs4.length ≤ 32 := by
    have := encode_varint_length_le ((P_api.chunkIndex c).zeroExtend 64) (bs2 ++ [tag])
    simp only [List.length_append, List.length_singleton] at this; dsimp only [bs4]; omega
  have hser4 : bs4 ++ (P_api.chunkData c).toList = x.msg.serialize x.index := hser
  change SepWPp _ _ sm ((vecU8At A (s0.sp - 72#64) 40#64 ptr bs4 ∗ _) ∗ _) _ _
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs4]
  by_cases hle32 : bs4.length + 32 ≤ 40
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_le hle32
    apply SepWPp.of_sepWP_cs (mid := entry + 316#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    exact step_msgSerialize_copy_and_epilogue b A ext x c 40#64 ptr v80 r0 r1 r2 bs4 tag msgTail
      hle32 hser4 hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]; ac_rfl)
  · obtain ⟨hult31, hule31⟩ := rem40_ult_31_of_gt hle32 (by dsimp only [bs4] at hbs4_len ⊢; omega)
    have hpc_res :
        entry + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
          "<spqr::v1::chunked::states::Message>::serialize") =
          (tripleRatchetProgAtExt b ext).fnAddr doReserve7Name := by
      rw [← hentry, doReserve7_fnAddr_eq]
    apply SepWPp.of_sepWP_cs
      (mid := entry + bv% (2 ^ 64 - ls_rel% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]"
        "<spqr::v1::chunked::states::Message>::serialize"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    refine step_call_doReserve7_40 (P_api := P_api) (x := x) (R := R)
      b A ext hA (s0.sp - 72#64) ptr s0.sp (entry + 420#64) bs4 hbs4_len
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ tag) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗ msgTail ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by rw [vecU8At_sp72_eq]) ?_
    intro sm2 ptr' hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    rw [vecU8At_sp72_eq A s0.sp 80#64 ptr' bs4]
    apply SepWPp.of_sepWP_cs (mid := entry + 316#64)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step3
    have hle80 : bs4.length + 32 ≤ (80#64 : BitVec 64).toNat := by
      change bs4.length + 32 ≤ 80; dsimp only [bs4] at hbs4_len ⊢; omega
    exact step_msgSerialize_copy_and_epilogue b A ext x c 80#64 ptr' v80 r0 r1 r2 bs4 tag msgTail
      hle80 hser4 hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step3⟩)
      (by rw [vecU8At_sp72_eq]; ac_rfl)

/-! ## 5. Entry Block & Main Theorem for `<Message>::serialize` -/

/-- Entry block (`+0x000..+0x060` & `+0x1ac..+0x1b8`, `0..96` & `428..440`): saves callee-saved
    registers, allocates 40-byte buffer via `__rust_alloc(40, 1)`, writes `[1#8]`, and executes
    the first two `spqr::encode_varint` calls (`x.msg.epoch` and `x.index.zeroExtend 64`),
    arriving at `entry + 96#64` with `bs2 = encode_varint (x.index.zeroExtend 64) (encode_varint
    x.msg.epoch [1#8])`. -/
private theorem step_msgSerialize_entry {P_api : PolyApi}
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State))
    (hA : MsgSerializeAlloc b A ext) (henc : SpqrEncodeVarintOkExt b A ext)
    {s0 : State} (x : MessageSerializeGhost P_api)
    (v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2 : BitVec 64)
    {R P : SepProp} {Q : State → SepProp → Prop}
    (hpc0 : s0.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName)
    (hrun0 : s0.status = .Running) (halign : s0.sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = x.msgA) (hx1 : (s0.readReg64 .x1).setWidth 32 = x.index)
    (hx8 : s0.readReg64 .x8 = x.ret)
    (hP : P =
      (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
      ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗
      ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8))
    (hnext : ∀ (sm : State) (ptr : BitVec 64),
      let bs1 := CryptoVerification.LibsignalSpqrV1.encode_varint x.msg.epoch [1#8]
      let bs2 := CryptoVerification.LibsignalSpqrV1.encode_varint (x.index.zeroExtend 64) bs1
      sm.pc = (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName + 96#64 →
      sm.status = .Running → sm.sp = s0.sp - 80#64 → sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret → sm.readReg64 .x20 = x.msgA →
      MsgSerializeCalleeSaved s0 sm → bs2.length ≤ 21 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) sm
        (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
         (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
         (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
         A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .lr) s0 P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (messageSerializeSpecX P_api A).onPanic x s0 sf ∗ R)) := by
  have hfn := messageSerialize_fnOff
  have hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr messageSerializeName +
        BitVec.ofNat 64 (num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_no_alloc_shim_is_unstable_v2")))
      noAllocShimSpec :=
    sub_ok_at_of_fnAddr hA.shim messageSerializeName
      (num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := sub_ok_at_of_fnAddr hA.alloc messageSerializeName
    (num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "__rustc::__rust_alloc"))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := messageSerializeName)
    (k := num% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "alloc::raw_vec::handle_error"))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 0 96
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 428 440
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches; subst hP
  rw [stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64)]
  have hpos40 : 0 < 40 := by decide
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hbound40 : 40 + 1 ≤ 2 ^ 63 := by decide
  apply SepWPp.of_sepWP_cs (mid := entry + 52#64)
  wp_steps; wp_apply; wp_steps; wp_apply
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_step0
  by_cases hoom : sf_1.readReg64 .x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.weaken_pre (P' := ⌜sf_1.trace = sf.trace ++ [allocFailedEvent]⌝ ∗
      (A.pool ∗ stackAt sf.sp allocHookStack ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       memRegion (s0.sp - 16544#64) 12368 ∗
       ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
       ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim fun htrace => ?_)
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_rel% "<spqr::v1::chunked::states::Message>::serialize" "alloc::raw_vec::handle_error"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [messageSerializeSpecX, sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · have hoom_beq : (sf_1.readReg64 .x0 == 0#64) = false := beq_eq_false_iff_ne.mpr hoom
    simp only [hoom, ite_false]
    refine SepWPp.weaken_pre (P' := ⌜(sf_1.readReg64 .x0).toNat % 1 = 0 ∧ sf_1.trace = sf.trace⌝ ∗
      (A.pool ∗ stackAt sf.sp allocHookStack ∗
       A.live (sf_1.readReg64 .x0) 40 1 ∗ memRegion (sf_1.readReg64 .x0) 40 ∗
       (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
       (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
       memRegion (s0.sp - 16544#64) 12368 ∗
       ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗
       ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
       ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim fun ⟨_, htrace⟩ => ?_)
    rw [memRegion_40_split_1_39 (sf_1.readReg64 .x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun b0 => ?_
    apply SepWPp.of_sepWP_cs
      (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step1
    have hpc_enc :
        entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize") =
          (tripleRatchetProgAtExt b ext).fnAddr spqrEncodeVarintName := by
      rw [← hentry, spqrEncodeVarint_fnAddr_eq]
    have hsp_sf : sf.sp = s0.sp - 80#64 := by simp only [wp_norm, arm64_norm, *]
    refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (R := R)
      b A ext henc x.msg.epoch (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp (entry + 84#64)
      [1#8] (by decide)
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hinv_step0.trans hinv_step1⟩ <;> simp only [wp_norm, arm64_norm, *])
      (by
        have hinit := vecU8At_init_40_one A (s0.sp - 72#64) (sf_1.readReg64 .x0) hoom
        simp only [arm64_norm] at hinit
        rw [hsp_sf, ← hinit, stackAt_spqrEncodeVarint_to_allocHook (s0.sp - 80#64),
          show s0.sp - 80#64 - 16464#64 = s0.sp - 16544#64 by bv_omega]
        simp only [arm64_norm]; ac_rfl) ?_
    intro sm1 hpcm1 hrunm1 hspm1 htrm1 hx19m1 hx20m1 hx21m1 _ _ hcsm1
    have hx19m1' : sm1.readReg64 .x19 = x.ret := by simp only [wp_norm, arm64_norm, *]
    have hx20m1' : sm1.readReg64 .x20 = x.msgA := by simp only [wp_norm, arm64_norm, *]
    have hx21m1' : (sm1.readReg64 .x21).setWidth 32 = x.index := by rw [hx21m1]; simp only [wp_norm, arm64_norm, *]
    let bs1 := CryptoVerification.LibsignalSpqrV1.encode_varint x.msg.epoch [1#8]
    have hbs1_len : bs1.length ≤ 11 := by
      have := encode_varint_length_le x.msg.epoch [1#8]; simp only [List.length_singleton] at this; omega
    apply SepWPp.of_sepWP_cs
      (mid := entry + bv% (2 ^ 64 - ls_rel% "spqr::encode_varint" "<spqr::v1::chunked::states::Message>::serialize"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hinv_step2
    refine step_call_spqrEncodeVarint_40 (P_api := P_api) (x := x) (R := R)
      b A ext henc (x.index.zeroExtend 64) (s0.sp - 72#64) (sf_1.readReg64 .x0) s0.sp (entry + 96#64)
      bs1 (by omega)
      (F :=
        (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
        (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗ ((s0.sp - 80#64) ↦₆₄ v80) ∗
        ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm1.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
      by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm], hinv_step2⟩)
      (by ac_rfl) ?_
    intro sm2 hpcm2 hrunm2 hspm2 htrm2 hx19m2 hx20m2 _ _ _ hcsm2
    have hx19m2' : sm2.readReg64 .x19 = x.ret := by simp only [arm64_norm, *]
    have hx20m2' : sm2.readReg64 .x20 = x.msgA := by simp only [arm64_norm, *]
    have hbs2_len :
        (CryptoVerification.LibsignalSpqrV1.encode_varint (x.index.zeroExtend 64) bs1).length ≤ 21 := by
      have := encode_varint_length_le (x.index.zeroExtend 64) bs1; omega
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm2 (sf_1.readReg64 .x0) hpcm2 hrunm2 hspm2 htrm2 hx19m2' hx20m2' hcsm2 hbs2_len)

private theorem messageSerialize_ok_core (P_api : PolyApi) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : MsgSerializeAlloc b A ext) (henc : SpqrEncodeVarintOkExt b A ext) :
    MessageSerializeOkExt P_api b A ext := by
  unfold MessageSerializeOkExt; apply subroutine_ok_of_sepWPp
  intro x R s0 hpc0 hrun0 hpre hsp0
  have halign : s0.sp &&& 15#64 = 0#64 := by simpa only [State.spAligned, beq_iff_eq] using hsp0
  simp only [messageSerializeSpecX, messageAt, memRegion_24, stackAt_messageSerialize_eq,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v80, v72, v64, v56, v48, v40, v32, v24, v16, v8, r2, r1, r0, ⟨hx0, hx1, hx8⟩, hpre⟩
  refine ⟨(x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗
      (x.ret ↦₆₄ r0) ∗ ((x.ret + 8#64) ↦₆₄ r1) ∗ ((x.ret + 16#64) ↦₆₄ r2) ∗
      A.pool ∗ stackAt (s0.sp - 80#64) spqrEncodeVarintStackX ∗
      ((s0.sp - 80#64) ↦₆₄ v80) ∗ ((s0.sp - 72#64) ↦₆₄ v72) ∗ ((s0.sp - 64#64) ↦₆₄ v64) ∗ ((s0.sp - 56#64) ↦₆₄ v56) ∗
      ((s0.sp - 48#64) ↦₆₄ v48) ∗ ((s0.sp - 40#64) ↦₆₄ v40) ∗ ((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8),
    R, by convert hpre using 1; ac_rfl,
    step_msgSerialize_entry b A ext hA henc x v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 r0 r1 r2
      hpc0 hrun0 halign hx0 hx1 hx8 rfl ?_⟩
  intro sm ptr bs1 bs2 hpcm hrunm hspm htrm hx19m hx20m hcsm hbs2_len
  have hlt40 : bs2.length < (40#64 : BitVec 64).toNat := by
    change bs2.length < 40; dsimp only [bs2, bs1] at hbs2_len ⊢; omega
  have hbeq := len_beq_cap_false hlt40
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 96 268
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 344 348
  msgSerialize_fetches_range b (Rust.withPanics ext) messageSerialize_fnOff 392 400
  generalize_entry hentry : (tripleRatchetProgAtExt b ext).fnAddr messageSerializeName = entry
  examples_hide_fetches
  change SepWPp _ _ sm (vecU8At A (s0.sp - 72#64) 40#64 ptr bs2 ∗
    (x.msgA ↦₆₄ x.msg.epoch) ∗ messagePayloadAt P_api x.msgA x.msg.payload ∗ _) _ _
  rw [vecU8At_sp72_eq A s0.sp 40#64 ptr bs2]
  cases hpay : x.msg.payload with
  | none =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 348#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : bs2 ++ [0#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 0#8) ∗ memRegion (x.msgA + 0x09#64) 39 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk b A ext x ptr v80 r0 r1 r2 bs2 0#8 hlt40 hser
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq, ← hmsg_eq]; ac_rfl)
  | ct1Ack b_ack =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 348#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : bs2 ++ [4#8] = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 4#8) ∗
        ((x.msgA + 0x09#64) ↦₈ (if b_ack then 1#8 else 0#8)) ∗ memRegion (x.msgA + 0x0a#64) 38 =
        messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_epilogue_no_chunk b A ext x ptr v80 r0 r1 r2 bs2 4#8 hlt40 hser
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq, ← hmsg_eq]; ac_rfl)
  | hdr c =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : encode_chunk c (bs2 ++ [1#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 1#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A ext hA henc x c ptr v80 r0 r1 r2 bs2 1#8 (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ek c =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : encode_chunk c (bs2 ++ [2#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 2#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A ext hA henc x c ptr v80 r0 r1 r2 bs2 2#8 (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ekCt1Ack c =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : encode_chunk c (bs2 ++ [3#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 3#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A ext hA henc x c ptr v80 r0 r1 r2 bs2 3#8 (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ct1 c =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : encode_chunk c (bs2 ++ [5#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 5#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A ext hA henc x c ptr v80 r0 r1 r2 bs2 5#8 (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq]; ac_rfl)
  | ct2 c =>
    simp only [messagePayloadAt]; apply SepWPp.of_sepWP_cs (mid := entry + 268#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv_step
    have hser : encode_chunk c (bs2 ++ [6#8]) = x.msg.serialize x.index := by
      unfold Message.serialize MessageType.from_payload MessageType.toU8; simp only [hpay]; rfl
    have hmsg_eq : (x.msgA ↦₆₄ x.msg.epoch) ∗ ((x.msgA + 0x08#64) ↦₈ 6#8) ∗ memRegion (x.msgA + 0x09#64) 1 ∗
        chunkAt (x.msgA + 0x0a#64) { index := P_api.chunkIndex c, data := P_api.chunkData c } ∗
        memRegion (x.msgA + 0x2c#64) 4 = messageAt P_api x.msgA x.msg := by unfold messageAt messagePayloadAt; rw [hpay]
    exact step_msgSerialize_chunk b A ext hA henc x c ptr v80 r0 r1 r2 bs2 6#8 (memRegion (x.msgA + 0x2c#64) 4) hbs2_len hser hmsg_eq
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcsm.trans (by simp only [MsgSerializeCalleeSaved, arm64_norm, *])) (by rw [vecU8At_sp72_eq]; ac_rfl)

/-- `<spqr::v1::chunked::states::Message>::serialize` (110 insns) meets `messageSerializeSpecX
    P_api A` on `tripleRatchetProgAtExt b ext` under `AllocContracts4K`. -/
theorem messageSerialize_ok_4k (P_api : PolyApi) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K b A ext) (henc : SpqrEncodeVarintOkExt b A ext) :
    MessageSerializeOkExt P_api b A ext :=
  messageSerialize_ok_core P_api b A ext ⟨hA.alloc, hA.shim, do_reserve_7_ok_ext_4k hA⟩ henc

/-- Image-wrapped `<Message>::serialize` correctness theorem under `AllocContracts4K`. -/
theorem messageSerialize_ok_x_4k (P_api : PolyApi) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts4K img.base A ext) (henc : SpqrEncodeVarintOkExt img.base A ext) :
    MessageSerializeOkX P_api img A ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (messageSerializeSpecX P_api A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (messageSerialize_ok_4k P_api img.base A ext hA henc).mono_outcome
    x R s0 hpc0 hrun0 hpre.2 hsp0 fun _ h => h

theorem messageSerialize_ok_of_contracts_4k (P_api : PolyApi) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (K : MlKem) (ext : String → Option (State → State))
    (hA : AllocContracts4K img.base A ext) (_hhooks : SpqrHooks C A K ext) :
    MessageSerializeOkX P_api img A ext :=
  messageSerialize_ok_x_4k P_api img A ext hA
    (spqrEncodeVarint_ok_ext img.base A ext (growOneU8_ok_ext_4k img.base A ext hA))

/-- `AllocContracts` wrapper for `<Message>::serialize`. -/
theorem messageSerialize_ok_ext (P_api : PolyApi) (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) (henc : SpqrEncodeVarintOkExt b A ext) :
    MessageSerializeOkExt P_api b A ext :=
  messageSerialize_ok_core P_api b A ext ⟨hA.alloc, hA.shim, do_reserve_7_ok_ext hA⟩ henc

theorem messageSerialize_ok_x (P_api : PolyApi) (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) (henc : SpqrEncodeVarintOkExt img.base A ext) :
    MessageSerializeOkX P_api img A ext := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc0 hrun0 hpre hsp0
  change s0.mem ⊨ (⌜ImgCallInv img s0⌝ ∗ (messageSerializeSpecX P_api A).pre x s0) ∗ R at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact (messageSerialize_ok_ext P_api img.base A ext hA henc).mono_outcome
    x R s0 hpc0 hrun0 hpre.2 hsp0 fun _ h => h

theorem messageSerialize_ok_of_contracts_x (P_api : PolyApi) (img : Obj.Image)
    (C : Crypto) (A : RustAlloc) (K : MlKem) (ext : String → Option (State → State))
    (hA : AllocContracts img.base A ext) (_hhooks : SpqrHooks C A K ext) :
    MessageSerializeOkX P_api img A ext :=
  messageSerialize_ok_x P_api img A ext hA
    (spqrEncodeVarint_ok_ext img.base A ext (growOneU8_ok_ext img.base A ext hA))

end CryptoVerification.SpqrV1.Top.MessageSerialize
