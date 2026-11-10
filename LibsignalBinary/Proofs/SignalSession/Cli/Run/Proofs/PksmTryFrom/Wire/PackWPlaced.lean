/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.Pack
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailCWPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncodePure
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable `[LibsignalPlacement]` 248-Byte `sret` Pack (`+0x8c0 → +0x970`)

Proves the 44-instruction `sret` pack (`preKey_pack_8c0_to_970_placed_wpX`) and its
`RunCompose.pksmResAt` and `+0x970` deallocation-chain bridges on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.RunProofs.PksmWire

open Arm64 Arm64.Obj ProofLib ProofLib.GenPlacedFetches ProofLib.ProgramReflection
open CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEncode
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

abbrev pkw_SepWPp := @Wire.SepWPp
private abbrev pkw_done := @Wire.SepWP.done
private abbrev pkw_frame_tryFrom := @Wire.SepWPp.frame_tryFrom
private abbrev pkw_exists_pre := @Wire.SepWPp.exists_pre
private abbrev pkw_mono_pre := @Wire.SepWPp.mono_pre
private abbrev pkw_of_sepWP_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev pkw_of_sepWP_end_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_end_pk

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## 0. Local Bit-Level Normalizers -/

private theorem pkw_truncate32_zext64_and1 (x : BitVec 32) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 x &&& 1#64) = x &&& 1#32 := by
  bv_bits

private theorem pkw_mask32_low_0 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 0 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 0 8 v := by bv_bits
private theorem pkw_mask32_low_8 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 8 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 8 8 v := by bv_bits
private theorem pkw_mask32_low_16 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 16 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 16 8 v := by bv_bits
private theorem pkw_mask32_low_24 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 24 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 24 8 v := by bv_bits

private theorem pkw_extract8_concat4_0 (d c b a : BitVec 8) :
    BitVec.extractLsb' 0 8 (d ++ c ++ b ++ a) = a := by bv_bits
private theorem pkw_extract8_concat4_8 (d c b a : BitVec 8) :
    BitVec.extractLsb' 8 8 (d ++ c ++ b ++ a) = b := by bv_bits
private theorem pkw_extract8_concat4_16 (d c b a : BitVec 8) :
    BitVec.extractLsb' 16 8 (d ++ c ++ b ++ a) = c := by bv_bits
private theorem pkw_extract8_concat4_24 (d c b a : BitVec 8) :
    BitVec.extractLsb' 24 8 (d ++ c ++ b ++ a) = d := by bv_bits

private theorem pkw_extract8_mask32_0 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = a :=
  (pkw_mask32_low_0 w (d ++ c ++ b ++ a)).trans (pkw_extract8_concat4_0 d c b a)
private theorem pkw_extract8_mask32_8 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = b :=
  (pkw_mask32_low_8 w (d ++ c ++ b ++ a)).trans (pkw_extract8_concat4_8 d c b a)
private theorem pkw_extract8_mask32_16 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = c :=
  (pkw_mask32_low_16 w (d ++ c ++ b ++ a)).trans (pkw_extract8_concat4_16 d c b a)
private theorem pkw_extract8_mask32_24 (w : BitVec 64) (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8
      (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 (d ++ c ++ b ++ a)) = d :=
  (pkw_mask32_low_24 w (d ++ c ++ b ++ a)).trans (pkw_extract8_concat4_24 d c b a)
private theorem pkw_extract8_mask32_32 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 32 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 32 8 w := by bv_bits
private theorem pkw_extract8_mask32_40 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 40 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 40 8 w := by bv_bits
private theorem pkw_extract8_mask32_48 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 48 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 48 8 w := by bv_bits
private theorem pkw_extract8_mask32_56 (w : BitVec 64) (v : BitVec 32) :
    BitVec.extractLsb' 56 8 (w &&& bv% (2 ^ 64 - 2 ^ 32) ||| BitVec.zeroExtend 64 v) =
      BitVec.extractLsb' 56 8 w := by bv_bits

private theorem pkw_extract8_concat8_0 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 0 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b0 := by bv_bits
private theorem pkw_extract8_concat8_8 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 8 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b1 := by bv_bits
private theorem pkw_extract8_concat8_16 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 16 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b2 := by bv_bits
private theorem pkw_extract8_concat8_24 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 24 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b3 := by bv_bits
private theorem pkw_extract8_concat8_32 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 32 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b4 := by bv_bits
private theorem pkw_extract8_concat8_40 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 40 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b5 := by bv_bits
private theorem pkw_extract8_concat8_48 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 48 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b6 := by bv_bits
private theorem pkw_extract8_concat8_56 (b7 b6 b5 b4 b3 b2 b1 b0 : BitVec 8) :
    BitVec.extractLsb' 56 8 (b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) = b7 := by bv_bits

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  pkw_extract8_mask32_0 pkw_extract8_mask32_8 pkw_extract8_mask32_16 pkw_extract8_mask32_24
  pkw_extract8_mask32_32 pkw_extract8_mask32_40 pkw_extract8_mask32_48 pkw_extract8_mask32_56
  pkw_extract8_concat8_0 pkw_extract8_concat8_8 pkw_extract8_concat8_16 pkw_extract8_concat8_24
  pkw_extract8_concat8_32 pkw_extract8_concat8_40 pkw_extract8_concat8_48 pkw_extract8_concat8_56
  zeroExtend32_lsr4_truncate8
  truncate8_zeroExtend64_eq zeroExtend32_vb_lsr4_setWidth8 zeroExtend64_vb_lsr4_setWidth8
attribute [local simp]
  truncate8_zeroExtend64_eq zeroExtend32_vb_lsr4_setWidth8 zeroExtend64_vb_lsr4_setWidth8

/-! ## 1. Leaf L5 (`+0x8c0 → +0x970` / `2240 → 2416`): 44-Instruction `sret` Pack -/

/-- (``+0x8c0 → +0x970`, dec `2240 → 2416``): From `SigMsgOkStatePlaced` at `+0x8c0` (`2240`), executes the 44-instruction straight-line `sret`
pack (`+0x8c0 .. +0x96c` → `+0x970` / `2416`), writing the 248-byte `PreKeySignalMessage`
representation at `sret` (`x19`) from the stack slots (`sp' + 12 .. 288`, including `regId` at
`sp' + 56`) and registers (`x0 = serBoxPtr`, `x1 = len`, `x22 = vb.zeroExtend 64`,
`x25 = kyberBoxLen`, `x27 = msgG.pqCap`, `x28 = kyberBoxPtr`), repacking `sp' + 176..288` into
`memRegion (sp' + 176#64) 112`, and establishing `PackOkStatePlaced` at `+0x970` (`2416`). -/
theorem preKey_pack_8c0_to_970_placed_wpX [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal spkVal regId : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hst : SigMsgOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
      msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      (memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢
          (msgWords15At sret
            msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
            msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
            msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
            rk0 rk1 rk2 rk3 addrW0 addrW1
            (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion)) ∗
          (((sret + 120#64) ↦₃₂ BitVec.truncate 32 (BitVec.zeroExtend 64 opkTag &&& 1#64)) ∗
            ((sret + 124#64) ↦₃₂ opkVal)) ∗
          (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
            ((sret + 136#64) ↦₆₄ len)) ∗
          (((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
            ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
            ((sret + 160#64) ↦₃₂ kpkVal) ∗
            memRegion (sret + 164#64) 4) ∗
          pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
          (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
            ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
          ((sret + 232#64) ↦₃₂ regId) ∗
          ((sret + 236#64) ↦₃₂ spkVal) ∗
          ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
          memRegion (sret + 241#64) 7 ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗
          ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ spkVal) ∗
          ((sp' + 56#64) ↦₃₂ regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112))
      (tryFromQp s0) := by
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, _, _, _, _,
    _, hx0, hx1, _, hx28, hx27, hx26, hx25, _, hx23, hx22, _, _, hx19⟩
  rw [memRegion248_sret_split sret]
  simp only [sepConj_assoc]
  refine pkw_mono_pre
    (sepConj_mono_left (memRegion32_entails_pkLayoutAt (sret + 168#64))) ?_
  simp only [sepExists_sepConj_left]
  refine pkw_exists_pre fun c0 => pkw_exists_pre fun c1 =>
    pkw_exists_pre fun c2 => pkw_exists_pre fun c3 =>
    pkw_exists_pre fun c4 => pkw_exists_pre fun c5 =>
    pkw_exists_pre fun c6 => pkw_exists_pre fun c7 =>
    pkw_exists_pre fun c8 => pkw_exists_pre fun cw9 =>
    pkw_exists_pre fun cw13 => pkw_exists_pre fun cw15 =>
    pkw_exists_pre fun cw23 => pkw_exists_pre fun cb31 => ?_
  rw [memRegion120_words15 sret,
      memRegion48_mid_eq (sret + 120#64),
      memRegion48_tail_eq (sret + 200#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine pkw_exists_pre fun b240 =>
    pkw_exists_pre fun u1 => pkw_exists_pre fun u0 =>
    pkw_exists_pre fun w224 => pkw_exists_pre fun w216 =>
    pkw_exists_pre fun w208 => pkw_exists_pre fun w200 =>
    pkw_exists_pre fun k160 =>
    pkw_exists_pre fun w152 => pkw_exists_pre fun w144 =>
    pkw_exists_pre fun w136 => pkw_exists_pre fun w128 =>
    pkw_exists_pre fun p1 => pkw_exists_pre fun p0 =>
    pkw_exists_pre fun s14 => pkw_exists_pre fun s13 =>
    pkw_exists_pre fun s12 => pkw_exists_pre fun s11 =>
    pkw_exists_pre fun s10 => pkw_exists_pre fun s9 =>
    pkw_exists_pre fun s8 => pkw_exists_pre fun s7 =>
    pkw_exists_pre fun s6 => pkw_exists_pre fun s5 =>
    pkw_exists_pre fun s4 => pkw_exists_pre fun s3 =>
    pkw_exists_pre fun s2 => pkw_exists_pre fun s1 =>
    pkw_exists_pre fun s0_w => ?_
  dsimp only [sevenBytesHeadAt, pkLayoutAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine pkw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl (mid := (blkPl_111).base + 2244#64) ?_
  wp_steps
  refine pkw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl1 => ?_
  have h136_tail := fun R => sevenBytesHead_tail_assoc (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h136_tail
  rw [h136_tail]
  refine pkw_of_sepWP_pk keepsFrozenInv_codeRoLoaded hcl1 (mid := (blkPl_111).base + 2268#64) ?_
  wp_steps
  refine pkw_done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl2 => ?_
  rw [← h136_tail]
  have h168_tail := fun R => sevenBytesHead_tail_assoc (sret + 168#64) b0 b1 b2 b3 c4 c5 c6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_tail
  rw [h168_tail]
  dsimp only [pkRestAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine pkw_of_sepWP_end_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  wp_steps
  refine @pkw_done _ _ _ _ _ _ ⟨by simp [calleeSavedVRegs, arm64_norm]⟩
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) fun hcl3 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl3,
      by simp [htr, arm64_norm]⟩,
    by simp [hx19, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx23, arm64_norm]⟩, ?_⟩
  have h168_head := fun R => sevenBytesHead_tail_assoc (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 R
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h168_head
  rw [← h168_head]
  have hm112 :
      ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
      ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
      ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
      ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 176#64) 112 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words14_entails_memRegion112 (sp' + 176#64)
        msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  dsimp only [msgWords15At, pkLayoutAt, sevenBytesHeadAt, pkRestAt]
  simp only [sepConj_assoc, arm64_norm]
  refine Entails.trans
    (Q := (((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
      ((sret ↦₆₄ msgG.pqCap) ∗
        ((sret + 8#64) ↦₆₄ msgG.pqPtr) ∗
        ((sret + 16#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sret + 24#64) ↦₆₄ msgG.ctPtr) ∗
        ((sret + 32#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sret + 40#64) ↦₆₄ msgG.serPtr) ∗
        ((sret + 48#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sret + 56#64) ↦₆₄ rk0) ∗ ((sret + 64#64) ↦₆₄ rk1) ∗
        ((sret + 72#64) ↦₆₄ rk2) ∗ ((sret + 80#64) ↦₆₄ rk3) ∗
        ((sret + 88#64) ↦₆₄ addrW0) ∗ ((sret + 96#64) ↦₆₄ addrW1) ∗
        ((sret + 104#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sret + 112#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
        ((sret + 120#64) ↦₃₂ BitVec.truncate 32 (BitVec.zeroExtend 64 opkTag &&& 1#64)) ∗
        ((sret + 124#64) ↦₃₂ opkVal) ∗
        ((sret + 128#64) ↦₆₄ serBoxPtr) ∗
        ((sret + 136#64) ↦₆₄ len) ∗
        ((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
        ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
        ((sret + 160#64) ↦₃₂ kpkVal) ∗
        memRegion (sret + 164#64) 4 ∗
        ((sret + 168#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sret + 172#64) ↦₈ b4) ∗ ((sret + 173#64) ↦₈ b5) ∗ ((sret + 174#64) ↦₈ b6) ∗
        ((sret + 175#64) ↦₈ b7) ∗ ((sret + 176#64) ↦₈ b8) ∗
        ((sret + 177#64) ↦₃₂ w9) ∗ ((sret + 181#64) ↦₁₆ w13) ∗
        ((sret + 183#64) ↦₆₄ w15) ∗ ((sret + 191#64) ↦₆₄ w23) ∗
        ((sret + 199#64) ↦₈ b31) ∗
        ((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
        ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3) ∗
        ((sret + 232#64) ↦₃₂ regId) ∗
        ((sret + 236#64) ↦₃₂ spkVal) ∗
        ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
        memRegion (sret + 241#64) 7 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ spkVal) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        ((sp' + 136#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
        ((sp' + 140#64) ↦₈ b4) ∗ ((sp' + 141#64) ↦₈ b5) ∗ ((sp' + 142#64) ↦₈ b6) ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3)))
    (by apply entails_of_sep_focus; sep_focus) ?_
  refine Entails.trans (sepConj_mono_left hm112) ?_
  rw [pkw_truncate32_zext64_and1]
  apply entails_of_eq; ac_rfl

/-! ## 2. Leaf L6: Bridge to `RunCompose.pksmResAt` and `deallocChain_970_placed_wpX` -/

/-- (``preKey_pack_8c0_to_970_res_placed_wpX`, `+0x8c0 → +0x970``): Generic bridge combining `preKey_pack_8c0_to_970_placed_wpX` (L5) with any entailment `hBridge` from
the packed 248-byte `sret` layout + heap resources into `Q_res`, preserving all stack spills
(`sp' + 12 .. 288`). -/
theorem preKey_pack_8c0_to_970_res_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap Q_res : SepProp}
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hBridge :
      ((msgWords15At sret
          msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
          msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
          msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
          rk0 rk1 rk2 rk3 addrW0 addrW1
          (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
          msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
        (((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal)) ∗
        (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
          ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 (vb :: body).length) ∗
          boxU8Buf A serBoxPtr (vb :: body)) ∗
        ((((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
            ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
            ((sret + 160#64) ↦₃₂ kpkVal) ∗
            memRegion (sret + 164#64) 4) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen) ∗
        pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
          ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
        ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sret + 236#64) ↦₃₂ sid) ∗
        ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
        memRegion (sret + 241#64) 7) ∗ R_heap ⊢ Q_res)
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      ((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ Q_res ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗
          ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ sid) ∗
          ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112))
      (tryFromQp s0) := by
  refine pkw_frame_tryFrom (preKey_pack_8c0_to_970_placed_wpX hst hpc hrun) ?_
  intro sf Pf ⟨hok, hent⟩
  refine ⟨hok, Entails.trans (sepConj_mono_left hent) ?_⟩
  rw [opkTag_mask64_truncate32_of_ite m.preKeyId opkTag hopkTag]
  simp only [sepConj_assoc] at hBridge
  refine Entails.trans
    (Q := ((msgWords15At sret
          msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
          msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
          msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
          rk0 rk1 rk2 rk3 addrW0 addrW1
          (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
        msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
        ((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal) ∗
        ((sret + 128#64) ↦₆₄ serBoxPtr) ∗
        ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 (vb :: body).length) ∗
        boxU8Buf A serBoxPtr (vb :: body) ∗
        ((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
        ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
        ((sret + 160#64) ↦₃₂ kpkVal) ∗
        memRegion (sret + 164#64) 4 ∗
        kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
        pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        ((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
        ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3) ∗
        ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sret + 236#64) ↦₃₂ sid) ∗
        ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
        memRegion (sret + 241#64) 7 ∗ R_heap)) ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        memRegion (sp' + 176#64) 112))
    (by apply entails_of_eq; ac_rfl) ?_
  exact sepConj_mono_left hBridge

/-- (``preKey_pack_8c0_to_970_okAt_placed_wpE`, `+0x8c0 → +0x970``): Combines `preKey_pack_8c0_to_970_placed_wpX` (L5) with `OkBridge.sret_cells_entails_pksmResAt_some`
to produce `RunCompose.pksmResAt A sret (some (pksmModelOf (vb :: body) vb m bk ik sid innerMsg))`
at `+0x970` (`2416`), preserving all stack spills (`sp' + 12 .. 288`). -/
theorem preKey_pack_8c0_to_970_okAt_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap : SepProp}
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      ((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ RunCompose.pksmResAt A sret
            (some (pksmModelOf (vb :: body) vb m bk ik sid innerMsg)) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗
          ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ sid) ∗
          ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112))
      (tryFromQp s0) :=
  preKey_pack_8c0_to_970_res_placed_wpX hopkTag
    (sret_cells_entails_pksmResAt_some A sret (vb :: body) vb m bk ik sid innerMsg
      msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
      ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
      R_heap hopkTag hopkVal hpk hrk hik)
    hst hpc hrun

/-- (``preKey_pack_8c0_to_970_parse_placed_wpE`, `+0x8c0 → +0x970``): Combines `preKey_pack_8c0_to_970_res_placed_wpX` with `OkBridge.sret_cells_entails_pksmResAt` to
produce `RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body))` directly at `+0x970` (`2416`). -/
theorem preKey_pack_8c0_to_970_parse_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik msg : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap : SepProp}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f)
    (hdec : Pksm.decodeProto body = some m)
    (hbk : m.baseKey = some bk)
    (hik_some : m.identityKey = some ik)
    (hmsg : m.message = some msg)
    (hsid : m.signedPreKeyId = some sid)
    (hbk_ok : ecKeyParses bk = true)
    (hik_ok : ecKeyParses ik = true)
    (hinner : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      ((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body)) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
          ((sp' + 16#64) ↦₃₂ kpkVal) ∗
          ((sp' + 20#64) ↦₃₂ opkTag) ∗
          ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ sid) ∗
          ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
          ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112))
      (tryFromQp s0) :=
  preKey_pack_8c0_to_970_res_placed_wpX hopkTag
    (sret_cells_entails_pksmResAt A sret vb body m bk ik msg sid innerMsg
      msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
      ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
      R_heap hlo hhi hdec hbk hik_some hmsg hsid hbk_ok hik_ok hinner
      hopkTag hopkVal hpk hrk hik)
    hst hpc hrun

/-- **L6b generic (`preKey_pack_8c0_to_970_dealloc_res_placed_wpX`, `+0x8c0 → +0x970`)**:
Frames `preKey_pack_8c0_to_970_res_placed_wpX` with the exact deallocation frame expected by
`ErrTailCWPlaced.deallocChain_970_placed_wpX` at `+0x970` (`2416`). -/
theorem preKey_pack_8c0_to_970_dealloc_res_placed_wpX [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {bkPtr bkCap msgPtr ikPtr : BitVec 64}
    {msgAct ikAct bkAct : Bool} {stackSz : Nat}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap Q_res frame : SepProp}
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hBridge :
      ((msgWords15At sret
          msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
          msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
          msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
          rk0 rk1 rk2 rk3 addrW0 addrW1
          (innerMsg.previousCounter ++ innerMsg.counter) (verHi56 ++ innerMsg.messageVersion) ∗
          msgHeapAt A msgG innerMsg addrW0 addrW1) ∗
        (((sret + 120#64) ↦₃₂ opkTag) ∗ ((sret + 124#64) ↦₃₂ opkVal)) ∗
        (((sret + 128#64) ↦₆₄ serBoxPtr) ∗
          ((sret + 136#64) ↦₆₄ BitVec.ofNat 64 (vb :: body).length) ∗
          boxU8Buf A serBoxPtr (vb :: body)) ∗
        ((((sret + 144#64) ↦₆₄ kyberBoxPtr) ∗
            ((sret + 152#64) ↦₆₄ kyberBoxLen) ∗
            ((sret + 160#64) ↦₃₂ kpkVal) ∗
            memRegion (sret + 164#64) 4) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen) ∗
        pkLayoutAt (sret + 168#64) b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31 ∗
        (((sret + 200#64) ↦₆₄ ik0) ∗ ((sret + 208#64) ↦₆₄ ik1) ∗
          ((sret + 216#64) ↦₆₄ ik2) ∗ ((sret + 224#64) ↦₆₄ ik3)) ∗
        ((sret + 232#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sret + 236#64) ↦₃₂ sid) ∗
        ((sret + 240#64) ↦₈ (vb >>> 4)) ∗
        memRegion (sret + 241#64) 7) ∗ R_heap ⊢ Q_res)
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      (((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap)) ∗
        (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗ frame))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ ⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗
          (Q_res ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 16#64) ↦₃₂ kpkVal) ∗
            ((sp' + 20#64) ↦₃₂ opkTag) ∗
            ((sp' + 24#64) ↦₃₂ opkVal) ∗
            ((sp' + 28#64) ↦₃₂ sid) ∗
            ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 72#64) ↦₆₄ w15) ∗
            ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
            ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
            sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
            ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
            ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
            memRegion (sp' + 176#64) 112 ∗ frame)))
      (tryFromQp s0) := by
  refine pkw_frame_tryFrom (preKey_pack_8c0_to_970_res_placed_wpX hopkTag hBridge hst hpc hrun) ?_
  intro sf Pf ⟨hok, hent⟩
  refine ⟨hok, Entails.trans (sepConj_mono_left hent) ?_⟩
  apply entails_of_eq; ac_rfl

/-- (``preKey_pack_8c0_to_970_dealloc_placed_wpE`, `+0x8c0 → +0x970``): Instantiates `preKey_pack_8c0_to_970_dealloc_res_placed_wpX` with
`OkBridge.sret_cells_entails_pksmResAt_some` to produce
`RunCompose.pksmResAt A sret (some (pksmModelOf (vb :: body) vb m bk ik sid innerMsg))`
plus the exact `ErrTailCWPlaced.deallocChain_970_placed_wpX` frame at `+0x970` (`2416`). -/
theorem preKey_pack_8c0_to_970_dealloc_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {bkPtr bkCap msgPtr ikPtr : BitVec 64}
    {msgAct ikAct bkAct : Bool} {stackSz : Nat}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap frame : SepProp}
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      (((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap)) ∗
        (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗ frame))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ ⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗
          (RunCompose.pksmResAt A sret
              (some (pksmModelOf (vb :: body) vb m bk ik sid innerMsg)) ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 16#64) ↦₃₂ kpkVal) ∗
            ((sp' + 20#64) ↦₃₂ opkTag) ∗
            ((sp' + 24#64) ↦₃₂ opkVal) ∗
            ((sp' + 28#64) ↦₃₂ sid) ∗
            ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 72#64) ↦₆₄ w15) ∗
            ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
            ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
            sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
            ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
            ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
            memRegion (sp' + 176#64) 112 ∗ frame)))
      (tryFromQp s0) :=
  preKey_pack_8c0_to_970_dealloc_res_placed_wpX hopkTag
    (sret_cells_entails_pksmResAt_some A sret (vb :: body) vb m bk ik sid innerMsg
      msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
      ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
      R_heap hopkTag hopkVal hpk hrk hik)
    hst hpc hrun

/-- (``preKey_pack_8c0_to_970_dealloc_parse_placed_wpE`, `+0x8c0 → +0x970``): Instantiates `preKey_pack_8c0_to_970_dealloc_res_placed_wpX` with
`OkBridge.sret_cells_entails_pksmResAt` to produce
`RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body))` plus the exact
`ErrTailCWPlaced.deallocChain_970_placed_wpX` frame at `+0x970` (`2416`). -/
theorem preKey_pack_8c0_to_970_dealloc_parse_placed_wpE [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap serBoxPtr : BitVec 64}
    {bkPtr bkCap msgPtr ikPtr : BitVec 64}
    {msgAct ikAct bkAct : Bool} {stackSz : Nat}
    {vb : BitVec 8} {body : List (BitVec 8)} {m : ProtoPreKeySignalMessage}
    {bk ik msg : List (BitVec 8)} {pk ipk : PublicKey}
    {sid : BitVec 32} {innerMsg : SignalMessage} {msgG : SignalMessageGhost}
    {rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64} {verHi56 : BitVec 56}
    {ik0 ik1 ik2 ik3 : BitVec 64}
    {kpkVal opkTag opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    {R_heap frame : SepProp}
    (hlo : 0x30 ≤ vb.toNat) (hhi : vb.toNat ≤ 0x4f)
    (hdec : Pksm.decodeProto body = some m)
    (hbk : m.baseKey = some bk)
    (hik_some : m.identityKey = some ik)
    (hmsg : m.message = some msg)
    (hsid : m.signedPreKeyId = some sid)
    (hbk_ok : ecKeyParses bk = true)
    (hik_ok : ecKeyParses ik = true)
    (hinner : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hopkTag : opkTag = if m.preKeyId.isSome then 1#32 else 0#32)
    (hopkVal : ∀ v, m.preKeyId = some v → opkVal = v)
    (hpk : (pkOf bk).bytes.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hrk : ∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
      (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))
    (hik : ∀ a : BitVec 64, (a ↦ₛ (pkOf ik).bytes.toList) =
      (a ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗ ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hst : SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 (vb :: body).length) ptr0
      kyberBoxPtr kyberBoxLen ikCap msgCap vb msgG.pqCap serBoxPtr bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2240#64)
    (hrun : s.status = .Running) :
    pkw_SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2416#64) s
      (((memRegion sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
        ((sp' + 16#64) ↦₃₂ kpkVal) ∗
        ((sp' + 20#64) ↦₃₂ opkTag) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ sid) ∗
        ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
        ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        ((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0) ∗ ((sp' + 232#64) ↦₆₄ rk1) ∗
        ((sp' + 240#64) ↦₆₄ rk2) ∗ ((sp' + 248#64) ↦₆₄ rk3) ∗
        ((sp' + 256#64) ↦₆₄ addrW0) ∗ ((sp' + 264#64) ↦₆₄ addrW1) ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion))) ∗
        (msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A serBoxPtr (vb :: body) ∗
          kyberStageOut A kpkVal vb m.kyberPreKeyId m.kyberCiphertext kyberBoxPtr kyberBoxLen ∗
          R_heap)) ∗
        (⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗ frame))
      (fun sf Pf =>
        PackOkStatePlaced s0 sp' sret ikCap msgCap sf ∧
        (Pf ⊢ ⌜msgCap ≠ noneCap ∧ ikCap ≠ noneCap ∧ bkCap ≠ noneCap⌝ ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          deallocSlot A msgCap msgPtr msgAct ∗
          deallocSlot A ikCap ikPtr ikAct ∗
          deallocSlot A bkCap bkPtr bkAct ∗
          A.pool ∗ stackAt sp' stackSz ∗
          (RunCompose.pksmResAt A sret (Pksm.pksmParse (vb :: body)) ∗
            ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗
            ((sp' + 16#64) ↦₃₂ kpkVal) ∗
            ((sp' + 20#64) ↦₃₂ opkTag) ∗
            ((sp' + 24#64) ↦₃₂ opkVal) ∗
            ((sp' + 28#64) ↦₃₂ sid) ∗
            ((sp' + 56#64) ↦₃₂ m.registrationId.getD 0#32) ∗
            ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗
            ((sp' + 72#64) ↦₆₄ w15) ∗
            ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
            ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
            sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
            ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
            ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
            memRegion (sp' + 176#64) 112 ∗ frame)))
      (tryFromQp s0) :=
  preKey_pack_8c0_to_970_dealloc_res_placed_wpX hopkTag
    (sret_cells_entails_pksmResAt A sret vb body m bk ik msg sid innerMsg
      msgG serBoxPtr kyberBoxPtr kyberBoxLen rk0 rk1 rk2 rk3 addrW0 addrW1 verHi56
      ik0 ik1 ik2 ik3 opkTag opkVal kpkVal b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 w9 w13 w15 w23
      R_heap hlo hhi hdec hbk hik_some hmsg hsid hbk_ok hik_ok hinner
      hopkTag hopkVal hpk hrk hik)
    hst hpc hrun

end CryptoVerification.SignalSession.Cli.RunProofs.PksmWire
