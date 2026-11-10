/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedB
public import LibsignalBinary.Proofs.TripleRatchet.Prost.VarintSlice
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSlice
import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRef
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRoot
import ProofLib.SepLogic.WPp

/-!
# Relocatable `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Ok Path and Top-Level Proof

Proves the Segment 4 `.ok` branch (`+2168 .. +2420` → `+1284`), post-loop composition
(`+1120 → +1284`), epilogue (`+1284 → ret`), and top-level `preKeyTryFrom_placed_ok` for Block `111`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.E2E.Pqxdh.ResponderWire

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit bv_sub_add_lit' bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512
  bv_reconstruct_low8 bv_reconstruct_low8_dec bv_zext8_mask truncate16_zext32
  append64_extract_lo append64_extract_hi append32_extract_lo append32_extract_hi
  append32_truncate zeroExtend32_truncate8_eq extractLsb0_8_append56
  zeroExtend32_lsr4_truncate8
  extract8_mask32_0 extract8_mask32_8 extract8_mask32_16 extract8_mask32_24
  extract8_mask32_32 extract8_mask32_40 extract8_mask32_48 extract8_mask32_56
  extract8_concat8_0 extract8_concat8_8 extract8_concat8_16 extract8_concat8_24
  extract8_concat8_32 extract8_concat8_40 extract8_concat8_48 extract8_concat8_56

/-! ## Callee Contracts and `KeepsFrozenInv` Lift Helpers -/

def PreKeyTryCloneOk [LibsignalPlacement] (Inv : Memory → Prop) (A : RustAlloc)
    (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 23)
    (withPreKeyInv Inv (tryCloneFromRefSpec A))

theorem preKeyIntoBoxOk_of_hooks [LibsignalPlacement] {Inv : Memory → Prop}
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    PreKeyIntoBoxOk Inv A H :=
  ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H) (i := 111) (j := 56)
    hcl_of_inv (into_boxed_slice_placed_ok hdealloc hrealloc hpanic)

theorem preKeyTryCloneOk_of_hooks [LibsignalPlacement] {Inv : Memory → Prop}
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec) :
    PreKeyTryCloneOk Inv A H :=
  ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H) (i := 111) (j := 23)
    hcl_of_inv (try_clone_from_ref_placed_ok hshim halloc hmemcpy)

theorem int32Merge_ok_at_prekey_placed [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleAllocErrorSym = some Rust.panicked) :
    subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A)) :=
  ls_subroutine_ok_of_block (callerProg := preKeyPlacedProg H) (i := 111) (j := 8)
    (Prost.int32_merge_placed_ok hshim halloc hpanic)

theorem preKeyDropSpeOk_cro_of_hookSat [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    PreKeyDropSpeOk (LibsignalCodeRoLoaded lsmpl) A H := by
  have h4 : subroutine_ok (Getters.blkPC_5.rebase Getters.blkPl_5.base H) (lsmpl.base 5)
      (withLsCodeRoLoaded lsmpl (Getters.dropSpeSpec A)) :=
    subroutine_ok_mono (Getters.drop_spe_placed_ok hdealloc)
      (fun _ _ s0 hp => by
        have ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [withLsRoLoaded]
        simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj]
        exact ⟨hcro.2, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H)
    (calleeProg := Getters.blkPC_5.rebase Getters.blkPl_5.base H) (i := 111) (j := 5) h4

theorem preKeySigTryFromOk_cro_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A H) (d : TryFromDepsPlaced A H) :
    PreKeySigTryFromOk (LibsignalCodeRoLoaded lsmpl) A H :=
  ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H) (i := 111) (j := 85)
    (Wire.tryFrom_placed_ok_of_deps hS d)

private theorem SepWPp.strengthen_inv {prog : Program} {ret : BitVec 64}
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {s0 : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : Inv s0.mem) (h : SepWPp prog ret s0 P Q Qp) :
    SepWPp prog ret s0 P (fun sf Pf => Inv sf.mem ∧ Q sf Pf) Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hq, hv⟩ | hpan⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, ⟨hkf hinv hsteps.keepsFrozen, hq⟩, hv⟩⟩
  · exact ⟨sf, hsteps, Or.inr hpan⟩

/-! ## `post_seg4_ok_placed_wp` and `post_seg4_after_signal_placed_wp` (`+2168` → `+1284`) -/

set_option maxHeartbeats 800000 in
theorem post_seg4_ok_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A H)
    (hTryClone : PreKeyTryCloneOk Inv A H)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {innerMsg : SignalMessage}
    {ik0 ik1 ik2 ik3 : BitVec 64} {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hsig : SignalMessage.tryFrom protoSignalCodec x.inner = .ok innerMsg)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hpack := @post_seg4_ok_pack_placed_wp _ Inv hkf A H hdealloc x s0
  have hpan := panic_at_prekey_placed (H := H) hpanic
  have hlen_toNat : (BitVec.ofNat 64 x.bytes.length).toNat = x.bytes.length :=
    Nat.mod_eq_of_lt (by omega)
  have hlen_le63 : x.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hstackClone :=
    stackAt_sub_split sp' tryCloneFromRefStack smallRootStack (by decide) (by decide)
  rw [hsig]
  refine SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq (memRegion112_words14 (sp' + 176#64))))) ?_
  dsimp only [signalMessageResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun w280 => SepWPp.exists_pre fun w272 =>
    SepWPp.exists_pre fun w264 => SepWPp.exists_pre fun w256 =>
    SepWPp.exists_pre fun w248 => SepWPp.exists_pre fun w240 =>
    SepWPp.exists_pre fun w232 => SepWPp.exists_pre fun w224 =>
    SepWPp.exists_pre fun w216 => SepWPp.exists_pre fun w208 =>
    SepWPp.exists_pre fun w200 => SepWPp.exists_pre fun w192 =>
    SepWPp.exists_pre fun w184 => SepWPp.exists_pre fun w176 =>
    SepWPp.exists_pre fun msgG => ?_
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length innerMsg.senderRatchetKey.bytes)
  refine SepWPp.mono_pre
    (sepConj_mono_left
      (signalMessageAt_unpack A msgG (sp' + 312#64) innerMsg rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
    SepWPp.exists_pre fun verHi56 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (msgHeapAt_pqCap_lt A msgG innerMsg addrW0 addrW1))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine SepWPp.pure_pre fun hpq_lt => ?_
  have hpq_eq := cap_add1_eq_of_lt hpq_lt
  dsimp only [msgWords15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 23) ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro hinv1
  have hm312 :
      ((sp' + 312#64) ↦₆₄ msgG.pqCap) ∗ ((sp' + 320#64) ↦₆₄ msgG.pqPtr) ∗
      ((sp' + 328#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
      ((sp' + 336#64) ↦₆₄ msgG.ctPtr) ∗
      ((sp' + 344#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
      ((sp' + 352#64) ↦₆₄ msgG.serPtr) ∗
      ((sp' + 360#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
      ((sp' + 368#64) ↦₆₄ rk0) ∗ ((sp' + 376#64) ↦₆₄ rk1) ∗
      ((sp' + 384#64) ↦₆₄ rk2) ∗ ((sp' + 392#64) ↦₆₄ rk3) ∗
      ((sp' + 400#64) ↦₆₄ addrW0) ∗ ((sp' + 408#64) ↦₆₄ addrW1) ∗
      ((sp' + 416#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
      ((sp' + 424#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ⊢
        memRegion (sp' + 312#64) 120 := by
    simpa [msgWords15At, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      msgWords15At_entails_memRegion (sp' + 312#64)
        msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
        msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
        msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
        rk0 rk1 rk2 rk3 addrW0 addrW1
        (innerMsg.previousCounter ++ innerMsg.counter)
        (verHi56 ++ innerMsg.messageVersion)
  refine SepWPp.mono_pre
    (P' := memRegion (sp' + 312#64) 120 ∗
      msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
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
      ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
      (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
      ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
      ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
      ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
      ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
      ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
      ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
      ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
      sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
      boxU8Buf A kyberBoxPtr x.kyberBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
      Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
      A.pool ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans ?_ (sepConj_mono_left hm312)
      simp only [sepConj_assoc]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.call_noPanic_pk hkf (⟨x.ptr, x.bytes⟩ : TryCloneSliceCall) hTryClone
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by tryFromPost_sp_align hsp) hinv1
    (ret_pc := (blkPl_111).base + 2236#64) (by simp_all [arm64_norm])
    (T := (x.ptr ↦ₛ x.bytes) ∗ A.pool ∗ stackAt sp' tryCloneFromRefStack)
    (φ := x.ptr = x.ptr ∧ (BitVec.ofNat 64 x.bytes.length).toNat = x.bytes.length ∧
      x.bytes.length + 1 ≤ 2 ^ 63)
    (by simp_all [tryCloneFromRefSpec, arm64_norm])
    ⟨rfl, hlen_toNat, hlen_le63⟩
    (by rw [hstackClone]; sep_focus)
    ?_
  clear hTryClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [tryCloneFromRefSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun hx1_2 => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by tryFromPost_sp [hsp2, hsp_eq]
  have hx19_2 : s2.readReg64 .x19 = x.sret := by simp [hx19_cs, hx19, arm64_norm]
  have hx20_2 : s2.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length := by
    simp [hx20_cs, hx20, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = 0x44#64 := by simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = ikCap := by simp [hx23_cs, hx23, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = 1569#64 := by simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = msgCap := by simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = kyberBoxPtr := by simp [hx28_cs, hx28, arm64_norm]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · clear hpack
    simp only [hoom, ite_true, sepConj_pure_left_comm, sepConj_assoc]
    refine SepWPp.pure_pre fun ⟨_, htr2⟩ => ?_
    refine SepWPp.of_sepWP (mid := (blkPl_111).ρ lsAllocHandleErrorSym) ?_
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine SepWPp.panic (by simp_all [arm64_norm])
      (by simpa [arm64_norm] using hpan)
      (tryFromQp_of_panicked (by simp [Rust.panicked, htr2, htr, arm64_norm]))
  · clear hpan
    simp only [hoom, ite_false, sepConj_pure_left_comm, sepConj_assoc]
    refine SepWPp.pure_pre fun htr2 => ?_
    refine SepWPp.mono_pre
      (P' := (memRegion x.sret 248 ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
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
          ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
          msgHeapAt A msgG innerMsg addrW0 addrW1 ∗
          boxU8Buf A (s2.readReg64 .x0) x.bytes ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
        ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 312#64) 120))
      (by
        simp only [hstackClone, hsp_eq, arm64_norm]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (hpack hsig hopk hpk hrk hik hoom
        ⟨hsp2_eq, hsp2_align, hinv2, by simp [htr2, htr, arm64_norm]⟩
        hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 hx28_2)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    apply entails_of_eq; ac_rfl

theorem post_seg4_after_signal_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A H)
    (hTryClone : PreKeyTryCloneOk Inv A H)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {ik0 ik1 ik2 ik3 : BitVec 64} {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpk : x.baseKey.toList = pkBytesOf b0 b1 b2 b3 b4 b5 b6 b7 b8 w9 w13 w15 w23 b31)
    (hik : ∀ b : BitVec 64, (b ↦ₛ x.idPub.toList) =
      (b ↦₆₄ ik0) ∗ ((b + 8#64) ↦₆₄ ik1) ∗ ((b + 16#64) ↦₆₄ ik2) ∗ ((b + 24#64) ↦₆₄ ik3))
    (hst : PreKeyPostState Inv s0 sp' s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running)
    (hx29 : s.readReg64 .x29 = sp' + 512#64)
    (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = 1569#64)
    (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap)
    (hx22 : s.readReg64 .x22 = 0x44#64)
    (hx21 : s.readReg64 .x21 = x.ptr)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.bytes.length)
    (hx19 : s.readReg64 .x19 = x.sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 312#64) 120 ∗
          A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  rcases hsig : SignalMessage.tryFrom protoSignalCodec x.inner with e | innerMsg
  · rw [← hsig]
    have h112_split : memRegion (sp' + 176#64) 112 =
        memRegion (sp' + 176#64) 48 ∗ memRegion (sp' + 224#64) 64 := by
      simpa [BitVec.add_assoc, BitVec.reduceAdd] using
        Prost.memRegion_split (sp' + 176#64) 48 64 (by decide)
    refine SepWPp.mono_pre
      (P' := (((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          memRegion (sp' + 176#64) 48 ∗
          signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          memRegion x.sret 248 ∗ boxU8Buf A kyberBoxPtr x.kyberBytes ∗
          Wire.vecU8Buf A msgCap msgPtr x.inner ∗ Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
        ((x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          memRegion (sp' + 224#64) 64))
      (by
        rw [h112_split]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.frame_tryFrom
      (post_seg4_err_placed_wp hkf hdealloc hsig hst hpc hrun
        hx29 hx28 hx26 hx25 hx24 hx23 hx19)
      fun sf Pf ⟨hstf, hent⟩ => ⟨hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    rw [h112_split]
    apply entails_of_eq; ac_rfl
  · rw [← hsig]
    exact post_seg4_ok_placed_wp hkf hdealloc hTryClone hpanic hlt hsig hopk hpk hik hst hpc hrun
      hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19

/-! ## Stack Reassembly Helpers and Chained Post-Loop (`+1120 → +1284`) -/

private theorem memRegion296_split (sp' : BitVec 64) :
    memRegion sp' 296 =
      memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗ memRegion (sp' + 16#64) 96 ∗
      memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
      memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 := by
  rw [show (296 : Nat) = 12 + (4 + (96 + (32 + (32 + (112 + 8))))) by decide,
    Prost.memRegion_split sp' 12 284 (by decide),
    Prost.memRegion_split (sp' + 12#64) 4 280 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64) 96 184 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64) 32 152 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64) 32 120 (by decide),
    Prost.memRegion_split (sp' + 12#64 + 4#64 + 96#64 + 32#64 + 32#64) 112 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem spills96_entails_memRegion (sp' : BitVec 64)
    (w16 w20 w24 w28 w48 w52 w56 w60 w68 : BitVec 32)
    (w32 w40 w72 w80 w88 w96 w104 : BitVec 64) :
    ((sp' + 16#64) ↦₃₂ w16) ∗ ((sp' + 20#64) ↦₃₂ w20) ∗
    ((sp' + 24#64) ↦₃₂ w24) ∗ ((sp' + 28#64) ↦₃₂ w28) ∗
    ((sp' + 32#64) ↦₆₄ w32) ∗ ((sp' + 40#64) ↦₆₄ w40) ∗
    ((sp' + 48#64) ↦₃₂ w48) ∗ ((sp' + 52#64) ↦₃₂ w52) ∗
    ((sp' + 56#64) ↦₃₂ w56) ∗ ((sp' + 60#64) ↦₃₂ w60) ∗
    memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ w68) ∗
    ((sp' + 72#64) ↦₆₄ w72) ∗ ((sp' + 80#64) ↦₆₄ w80) ∗
    ((sp' + 88#64) ↦₆₄ w88) ∗ ((sp' + 96#64) ↦₆₄ w96) ∗
    ((sp' + 104#64) ↦₆₄ w104) ⊢
      memRegion (sp' + 16#64) 96 := by
  rw [show (96 : Nat) =
      4 + (4 + (4 + (4 + (8 + (8 + (4 + (4 +
        (4 + (4 + (4 + (4 + (8 + (8 + (8 + (8 + 8)))))))))))))))
      by decide,
    Prost.memRegion_split (sp' + 16#64) 4 92 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64) 4 88 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64) 4 84 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64) 4 80 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64) 8 72 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64) 8 64 (by decide),
    Prost.memRegion_split (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64) 4 60 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64) 4 56 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64) 4 52 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64) 4 48
      (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 44 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64)
      4 40 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64) 8 32 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64) 8 24 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64) 8 16 (by decide),
    Prost.memRegion_split
      (sp' + 16#64 + 4#64 + 4#64 + 4#64 + 4#64 + 8#64 + 8#64 + 4#64 + 4#64 + 4#64 + 4#64 + 4#64 +
        4#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo32_entails_memRegion _ _)
                (sepConj_mono (pointsTo32_entails_memRegion _ _)
                  (sepConj_mono (pointsTo32_entails_memRegion _ _)
                    (sepConj_mono (pointsTo32_entails_memRegion _ _)
                      (sepConj_mono_right
                        (sepConj_mono (pointsTo32_entails_memRegion _ _)
                          (sepConj_mono (pointsTo64_entails_memRegion _ _)
                            (sepConj_mono (pointsTo64_entails_memRegion _ _)
                              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                (sepConj_mono (pointsTo64_entails_memRegion _ _)
                                  (pointsTo64_entails_memRegion _ _))))))))))))))))

private theorem region152_repack (sp' w296 w304 w440 : BitVec 64) :
    ((sp' + 296#64) ↦₆₄ w296) ∗ ((sp' + 304#64) ↦₆₄ w304) ∗
    memRegion (sp' + 312#64) 120 ∗ memRegion (sp' + 432#64) 8 ∗
    ((sp' + 440#64) ↦₆₄ w440) ⊢ memRegion (sp' + 296#64) 152 := by
  rw [show (152 : Nat) = 8 + (8 + (120 + (8 + 8))) by decide,
    Prost.memRegion_split (sp' + 296#64) 8 144 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64) 8 136 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64) 120 16 (by decide),
    Prost.memRegion_split (sp' + 296#64 + 8#64 + 8#64 + 120#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono_right (pointsTo64_entails_memRegion _ _))))

private theorem stackAt_preKeyTryFrom_unsplit (sp : BitVec 64) (s0 : State) :
    stackAt (sp - 608#64) smallRootStack ∗
    memRegion (sp - 608#64) 296 ∗ memRegion (sp - 608#64 + 296#64) 152 ∗
    memRegion (sp - 608#64 + 448#64) 64 ∗ preKeyCalleeSavedAt (sp - 608#64) s0 ⊢
      stackAt sp preKeyTryFromStack := by
  rw [stackAt_preKeyTryFrom_split sp]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (preKeyCalleeSavedAt_entails_memRegion96 (sp - 608#64) s0))))

set_option maxHeartbeats 800000 in
theorem post_f90_to_034_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A H)
    (hDropSpe : PreKeyDropSpeOk Inv A H)
    (hIntoBox : PreKeyIntoBoxOk Inv A H)
    (hSigTryFrom : PreKeySigTryFromOk Inv A H)
    (hTryClone : PreKeyTryCloneOk Inv A H)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberCap kyberPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {opkVal : BitVec 32}
    (hlt : x.bytes.length < 2 ^ 32)
    (hopk : ∀ v, x.opkId = some v → opkVal = v)
    (hpc : s.pc = (blkPl_111).base + 1120#64)
    (hrun : s.status = .Running)
    (hregs : PreKeyLoopRegs sp' x s)
    (hsp : s.spAligned = true) (hinv : Inv s.mem) (htr : s.trace = s0.trace)
    (hx24 : s.readReg64 .x24 = 0#64) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 1284#64) s
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ memRegion sp' 296 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
          memRegion sp' 296 ∗ memRegion (sp' + 296#64) 152 ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack))
      (tryFromQp s0) := by
  have hlt_in : x.inner.length < 2 ^ 32 := (psmRem_lengths_lt x hlt).2.2.2.2.2.2.2.2.2
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, b8, w9, w13, w15, w23, b31, hpk⟩ :=
    exists_pkBytesOf x.baseKey.toList (List.Vector.toList_length x.baseKey)
  obtain ⟨ik0, ik1, ik2, ik3, _, hik⟩ :=
    exists_unpack64_of_length_32 (List.Vector.toList_length x.idPub)
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 16#64) 96 ∗
        vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
        vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
        vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
        vecU8At A (sp' + 384#64) msgCap msgPtr x.inner ∗
        ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
        ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
        ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
        ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗ lsLogOff))
    (by
      rw [memRegion296_split sp']
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (post_seg1a_f90_to_0ac_placed_wp hkf hDropSpe hpc hrun hregs hsp hinv htr hx24) ?_
  intro s1 P1 hpc1 hrun1 ⟨hst1, hky_lt, hbk_lt, hik_lt, hmsg_lt,
    hx29_1, hx28_1, hx27_1, hx26_1, hx25_1, hx24_1, hx23_1, hx22_1, hx21_1, hx20_1, hx19_1,
    hent1⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
  clear hent1
  refine SepWPp.mono_pre
    (P' := (((sp' + 72#64) ↦₆₄ 33#64) ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        memRegion (sp' + 312#64) 48 ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      (((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 64#64) 4 ∗ ((sp' + 68#64) ↦₃₂ 1#32) ∗
        ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 12#64) 4 ∗
        memRegion (sp' + 112#64) 32 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by
      dsimp only [seg1SpillsAt]
      apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (post_seg1b_0ac_to_1b4_placed_wp hkf hcl_of_inv hDropSpe hst1 hpc1 hrun1 hik_lt hmsg_lt
      hx29_1 hx28_1 hx27_1 hx26_1 hx25_1 hx24_1 hx23_1 hx22_1 hx21_1 hx20_1 hx19_1) ?_
  intro s2 P2 hpc2 hrun2
    ⟨hst2, hx29_2, hx28_2, hx27_2, hx26_2, hx25_2, hx24_2, hx23_2, hx22_2, hx21_2, hx20_2,
      hx19_2, hent2⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
  clear hent2
  refine SepWPp.mono_pre
    (P' := (memRegion (sp' + 12#64) 4 ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 68#64) ↦₃₂ 1#32) ∗ ((sp' + 72#64) ↦₆₄ 33#64) ∗
        memRegion (sp' + 112#64) 32 ∗
        ((sp' + 312#64) ↦₈ 0#8) ∗ ((sp' + 313#64) ↦ₛ x.baseKey.toList) ∗
        memRegion (sp' + 345#64) 15 ∗ Wire.vecU8Buf A kyberCap kyberPtr x.kyberBytes ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗
      (((sp' + 80#64) ↦₆₄ bkPtr) ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗ lsLogOff ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ memRegion (sp' + 64#64) 4 ∗
        ((sp' + 88#64) ↦₆₄ bkCap) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        memRegion (sp' + 360#64) 72 ∗ memRegion (sp' + 432#64) 8 ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (post_seg2_1b4_to_360_placed_wp hkf hIntoBox hpk hst2 hpc2 hrun2 hky_lt
      hx29_2 hx28_2 hx27_2 hx26_2 hx25_2 hx23_2 hx22_2 hx21_2 hx20_2 hx19_2) ?_
  intro s3 P3 hpc3 hrun3 ⟨kyberBoxPtr, hst3,
    hx29_3, hx28_3, hx27_3, hx26_3, hx25_3, hx24_3, hx23_3, hx22_3, hx21_3, hx20_3, hx19_3,
    hent3⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent3) ?_
  clear hent3
  refine SepWPp.mono_pre
    (P' := (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 56#64) ↦₆₄ 33#64) ∗ ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 104#64) ↦₆₄ ikPtr) ∗ memRegion (sp' + 144#64) 32 ∗
        memRegion (sp' + 312#64) 48 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
      (((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        spUnused112 sp' ∗ ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗ ((sp' + 80#64) ↦₆₄ bkPtr) ∗
        Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        ((sp' + 16#64) ↦₃₂ x.kpkId) ∗ ((sp' + 20#64) ↦₃₂ opkTag x) ∗
        ((sp' + 24#64) ↦₃₂ opkVal) ∗ ((sp' + 28#64) ↦₃₂ x.spkId) ∗
        memRegion (sp' + 64#64) 4 ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        memRegion (sp' + 432#64) 8 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        memRegion sp' 12 ∗ memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.bind_frame_tryFrom
    (post_seg3_360_to_3a8_placed_wp hkf hcl_of_inv hSigTryFrom hik hlt_in hst3 hpc3 hrun3
      hx29_3 hx28_3 hx26_3 hx25_3 hx24_3 hx23_3 hx22_3 hx21_3 hx20_3 hx19_3) ?_
  intro s4 P4 hpc4 hrun4
    ⟨hst4, hx29_4, hx28_4, hx27_4, hx26_4, hx25_4, hx24_4, hx23_4, hx22_4, hx21_4, hx20_4,
      hx19_4, hent4⟩
  refine SepWPp.mono_pre (sepConj_mono_left hent4) ?_
  clear hent4
  refine SepWPp.mono_pre
    (P' := (signalMessageResultAt A [] (sp' + 312#64) (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
        memRegion (sp' + 176#64) 112 ∗ (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗
        ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
        ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
        ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
        ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
        ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
        ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
        ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
        sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
        ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
        ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
        boxU8Buf A kyberBoxPtr x.kyberBytes ∗ Wire.vecU8Buf A msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A ikCap ikPtr x.ikBytes ∗ Wire.vecU8Buf A bkCap bkPtr x.bkBytes ∗
        A.pool ∗ stackAt sp' smallRootStack) ∗
      (lsLogOff ∗ memRegion sp' 12 ∗
        ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 x.inner.length) ∗
        ((sp' + 40#64) ↦₆₄ 1569#64) ∗
        ((sp' + 48#64) ↦₃₂ 1#32) ∗ ((sp' + 52#64) ↦₃₂ x.regId) ∗
        ((sp' + 60#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 64#64) 4 ∗
        spUnused112 sp' ∗ memRegion (sp' + 288#64) 8 ∗
        ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
        memRegion (sp' + 432#64) 8 ∗ ((sp' + 440#64) ↦₆₄ (sp' + 296#64))))
    (by apply entails_of_eq; ac_rfl) ?_
  refine SepWPp.frame_tryFrom
    (post_seg4_after_signal_placed_wp hkf hdealloc hTryClone hpanic hlt hopk hpk hik
      hst4 hpc4 hrun4 hx29_4 hx28_4 hx26_4 hx25_4 hx24_4 hx23_4 hx22_4 hx21_4 hx20_4 hx19_4)
    fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, ?_⟩
  refine Entails.trans (sepConj_mono_left hentf) ?_
  have hm12 := pointsTo32_entails_memRegion (sp' + 12#64) (b7.zeroExtend 32)
  have hm96 := spills96_entails_memRegion sp'
    x.kpkId (opkTag x) opkVal x.spkId 1#32 x.regId x.regId 0#32 (b8.zeroExtend 32)
    (BitVec.ofNat 64 x.inner.length) 1569#64 w15 bkPtr bkCap msgPtr ikPtr
  have hm112 := memRegion32_112_pack sp' w23 w9 w13 b31 b0 b1 b2 b3 b4 b5 b6
  have hm144 :
      ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
      ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ⊢
        memRegion (sp' + 144#64) 32 := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using
      words4_entails_memRegion32 (sp' + 144#64) ik0 ik1 ik2 ik3
  have hm152 := region152_repack sp' (cur8 x) 0#64 (sp' + 296#64)
  rw [memRegion296_split sp']
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono
        (sepConj_mono_right
          (sepConj_mono hm12 (sepConj_mono hm96 (sepConj_mono hm112 (sepConj_mono_left hm144)))))
        (sepConj_mono_left hm152))))
  simp only [sepConj_assoc]
  apply entails_of_eq; ac_rfl

/-! ## Epilogue (`+1284 .. +1316`) and Top-Level `preKeyTryFrom_placed_ok` -/

def preKeyTryFromPlacedRawSpec (A : RustAlloc) [LibsignalPlacement] : Spec PreKeyTryFromArgs where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ptr ∧
      (s.readReg64 .x1).toNat = x.bytes.length ∧
      x.bytes.length < 2 ^ 32 ∧
      s.readReg64 .x8 = x.sret⌝ ∗
    (x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
    stackAt s.sp preKeyTryFromStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗
    stackAt s0.sp preKeyTryFromStack ∗ A.pool
  onPanic := fun _ s0 sf =>
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem epilogue_034_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {A : RustAlloc} {H : LibsignalHooks}
    {x : PreKeyTryFromArgs} {s0 s : State}
    (_hsp0 : s0.spAligned = true)
    (hst : PreKeyPostState Inv s0 (s0.sp - 608#64) s)
    (hpc : s.pc = (blkPl_111).base + 1284#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyTryFromPlacedRawSpec A).post x s0 sf))
      (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  unfold preKeyCalleeSavedAt
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  refine SepWPp.of_sepWP_end_pk hkf hinv ?_
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro _hinv1
  refine ⟨by simp_all [arm64_norm], fun hv => ?_, ?_⟩
  · refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], hv⟩
  · dsimp only [preKeyTryFromPlacedRawSpec]
    rw [pure_true_emp (by simp [htr, arm64_norm]), emp_sepConj]
    have hstk := stackAt_preKeyTryFrom_unsplit s0.sp s0
    unfold preKeyCalleeSavedAt at hstk
    simp only [bv_sub_add_lit', BitVec.reduceSub] at hstk
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))
    apply entails_of_eq; ac_rfl

/-- Generic `Inv`-parametric subroutine correctness for Block 111
(`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`) under `[LibsignalPlacement]`. -/
theorem preKeyTryFrom_inv_ok [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    (hdealloc : PreKeyDeallocOk Inv A H)
    (hDropSpe : PreKeyDropSpeOk Inv A H)
    (hIntoBox : PreKeyIntoBoxOk Inv A H)
    (hSigTryFrom : PreKeySigTryFromOk Inv A H)
    (hTryClone : PreKeyTryCloneOk Inv A H)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (withPreKeyInv Inv (preKeyTryFromPlacedRawSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hinv0, hpre0⟩ := extract_withPreKeyInv hpre
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := hcl_of_inv s0.mem hinv0
  have hL : (preKeyPlacedProg H).CodeLoaded s0.mem :=
    (IsLsBlockProg.eq_blockProgram (prog := preKeyPlacedProg H) (i := 111) (H := H)).symm ▸
      hcl0 111 (by decide) (by decide) H (fun _ => none) Syscall.standard
  dsimp only [preKeyTryFromPlacedRawSpec] at hpre0
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  set sp' := s0.sp - 608#64
  have hstk_top := stackAt_preKeyTryFrom_split s0.sp
  have hstk_sub := stackAt_sub_split sp' bytesMergeStack smallRootStack (by decide) (by decide)
  have hmem' : s0.mem ⊨
      (((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool)) ∗ R := by
    ac_nf at hmem ⊢
  have hfull : SepWPp (preKeyPlacedProg H) (s0.readReg64 .x30) s0
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyTryFromPlacedRawSpec A).post x s0 sf))
      (tryFromQp s0) := by
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 296#64) 152 ∗ memRegion (sp' + 512#64) 96 ∗
          A.pool ∗ stackAt sp' bytesMergeStack) ∗
        (memRegion x.sret 248 ∗ lsLogOff ∗
          memRegion sp' 296 ∗ memRegion (sp' + 448#64) 64 ∗
          memRegion (sp' - BitVec.ofNat 64 smallRootStack) (smallRootStack - bytesMergeStack)))
      (by
        rw [hstk_top, show preKeyTryFromSubStack = smallRootStack from rfl]
        dsimp only [sp'] at hstk_sub ⊢
        rw [hstk_sub]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (SepWPp.strengthen_inv hkf hinv0
        (preKey_entry_to_f90_placed_wp hint32 hbytes rfl hlt hpc hrun hsp hcl0 hx0 hx1 hx8)) ?_
    intro s1 P1 hpc1 hrun1 ⟨hinv1, hregs1, hsp1, _hcl1, htr1, hx24_1,
      opkVal, kyberCap, kyberPtr, bkCap, bkPtr, ikCap, ikPtr, msgCap, msgPtr, hopk, hent1⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent1) ?_
    clear hent1
    refine SepWPp.mono_pre
      (P' := ((x.ptr ↦ₛ x.bytes) ∗ memRegion x.sret 248 ∗ memRegion sp' 296 ∗
          ((sp' + 296#64) ↦₆₄ cur8 x) ∗ ((sp' + 304#64) ↦₆₄ 0#64) ∗
          vecU8At A (sp' + 312#64) kyberCap kyberPtr x.kyberBytes ∗
          vecU8At A (sp' + 336#64) bkCap bkPtr x.bkBytes ∗
          vecU8At A (sp' + 360#64) ikCap ikPtr x.ikBytes ∗
          vecU8At A (sp' + 384#64) msgCap msgPtr x.inner ∗
          ((sp' + 408#64) ↦₃₂ 1#32) ∗ ((sp' + 412#64) ↦₃₂ x.regId) ∗
          ((sp' + 416#64) ↦₃₂ opkTag x) ∗ ((sp' + 420#64) ↦₃₂ opkVal) ∗
          ((sp' + 424#64) ↦₃₂ 1#32) ∗ ((sp' + 428#64) ↦₃₂ x.spkId) ∗
          ((sp' + 432#64) ↦₃₂ 1#32) ∗ ((sp' + 436#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 440#64) ↦₆₄ (sp' + 296#64)) ∗
          lsLogOff ∗ A.pool ∗ stackAt sp' smallRootStack) ∗
        (memRegion (sp' + 448#64) 64 ∗ preKeyCalleeSavedAt sp' s0))
      (by
        rw [hstk_sub]
        apply entails_of_eq; ac_rfl) ?_
    refine SepWPp.bind_frame_tryFrom
      (post_f90_to_034_placed_wp hkf hcl_of_inv hdealloc hDropSpe hIntoBox hSigTryFrom hTryClone
        hpanic hlt hopk hpc1 hrun1 hregs1 hsp1 hinv1 htr1 hx24_1) ?_
    intro s2 P2 hpc2 hrun2 ⟨hst2, hent2⟩
    refine SepWPp.mono_pre (sepConj_mono_left hent2) ?_
    clear hent2
    refine SepWPp.mono_pre
      (P' := stackAt (s0.sp - 608#64) smallRootStack ∗
        memRegion (s0.sp - 608#64) 296 ∗
        memRegion (s0.sp - 608#64 + 296#64) 152 ∗
        memRegion (s0.sp - 608#64 + 448#64) 64 ∗
        preKeyCalleeSavedAt (s0.sp - 608#64) s0 ∗
        preKeyResultAt A x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗ lsLogOff ∗ A.pool)
      (by
        dsimp only [sp']
        apply entails_of_eq; ac_rfl) ?_
    exact epilogue_034_placed_wp hkf hsp hst2 hpc2 hrun2
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ |
    ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
        Satisfies.mono (sepConj_mono_left hent_f) hmf⟩))
  · exact reaches_outcome_steps hsteps (reaches_outcome.of_outcome
      (Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)))
  · exact (allowPanic_not_exited hoom).elim

theorem preKeyTryFrom_placed_ok_of_callees [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hint32 : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A)))
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    (hdealloc : PreKeyDeallocOk (LibsignalCodeLoaded lsmpl) A H)
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A H)
    (hIntoBox : PreKeyIntoBoxOk (LibsignalCodeLoaded lsmpl) A H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A H)
    (hTryClone : PreKeyTryCloneOk (LibsignalCodeLoaded lsmpl) A H)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base (preKeyTryFromPlacedSpec A) :=
  preKeyTryFrom_inv_ok keepsFrozenInv_codeLoaded (fun _ h => h)
    hint32 hbytes hdealloc hDropSpe hIntoBox hSigTryFrom hTryClone hpanic

/-- Relocatable `subroutine_ok` for Block `111` (`<PreKeySignalMessage as TryFrom<&[u8]>>::try_from`)
satisfying `preKeyTryFromPlacedSpec A` under `HookSat`. -/
theorem preKeyTryFrom_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A H) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base (preKeyTryFromPlacedSpec A) :=
  preKeyTryFrom_placed_ok_of_callees
    (int32Merge_ok_at_prekey_placed hshim_s halloc hpanic)
    hbytes
    (preKeyDeallocOk_of_hookSat hdealloc)
    hDropSpe
    (preKeyIntoBoxOk_of_hooks (fun _ h => h) hdealloc hrealloc hpanic_raw)
    hSigTryFrom
    (preKeyTryCloneOk_of_hooks (fun _ h => h) hshim halloc hmemcpy)
    hpanic

theorem preKeyTryFrom_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide)
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A)))
    (hDropSpe : PreKeyDropSpeOk (LibsignalCodeLoaded lsmpl) A H)
    (hSigTryFrom : PreKeySigTryFromOk (LibsignalCodeLoaded lsmpl) A H) :
    subroutine_ok callerProg (lsmpl.base 111) (preKeyTryFromPlacedSpec A) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (i := i) (j := 111)
    (preKeyTryFrom_placed_ok hshim_s hshim halloc hdealloc hrealloc hmemcpy hpanic hpanic_raw
      hbytes hDropSpe hSigTryFrom) hi (by decide) (by decide)

/-- `withLsCodeRoLoaded` variant of `preKeyTryFrom_placed_ok`, discharging `drop_spe` (Block `4`) and
`SignalMessage::try_from` (Block `85`). -/
theorem preKeyTryFrom_cro_placed_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hS : TripleRatchetHooksWPlaced A H)
    (d : TryFromDepsPlaced A H)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A))) :
    subroutine_ok (preKeyPlacedProg H) (blkPl_111).base
      (withLsCodeRoLoaded lsmpl (preKeyTryFromPlacedRawSpec A)) :=
  preKeyTryFrom_inv_ok keepsFrozenInv_codeRoLoaded (fun _ h => h.1)
    (int32Merge_ok_at_prekey_placed hshim_s halloc hpanic)
    hbytes
    (preKeyDeallocOk_of_hookSat hdealloc)
    (preKeyDropSpeOk_cro_of_hookSat hdealloc)
    (preKeyIntoBoxOk_of_hooks (fun _ h => h.1) hdealloc hrealloc hpanic_raw)
    (preKeySigTryFromOk_cro_of_deps hS d)
    (preKeyTryCloneOk_of_hooks (fun _ h => h.1) hshim halloc hmemcpy)
    hpanic

theorem preKeyTryFrom_cro_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H] (hi : i < 619 := by decide)
    (hshim_s : HookSat H lsRustNoAllocShimSym sessionShimSpec)
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hrealloc : HookSat H lsRustReallocSym (rustReallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpySpec)
    (hpanic : H lsAllocHandleErrorSym = some Rust.panicked)
    (hpanic_raw : H lsHandleErrorSym = some Rust.panicked)
    (hS : TripleRatchetHooksWPlaced A H)
    (d : TryFromDepsPlaced A H)
    (hbytes : subroutine_ok (preKeyPlacedProg H) (lsmpl.base 7)
      (withLsCodeLoaded lsmpl (bytesMergeRawSpec A))) :
    subroutine_ok callerProg (lsmpl.base 111)
      (withLsCodeRoLoaded lsmpl (preKeyTryFromPlacedRawSpec A)) :=
  ls_subroutine_ok_cro_of_block (callerProg := callerProg) (i := i) (j := 111)
    (preKeyTryFrom_cro_placed_ok hshim_s hshim halloc hdealloc hrealloc hmemcpy hpanic hpanic_raw
      hS d hbytes) hi (by decide) (by decide)

end CryptoVerification.E2E.Pqxdh.ResponderWire
