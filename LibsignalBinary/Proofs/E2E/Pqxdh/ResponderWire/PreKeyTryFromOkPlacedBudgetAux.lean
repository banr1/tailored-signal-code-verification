/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPost
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxes
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `<PreKeySignalMessage as TryFrom<&[u8]>>::try_from` (Block `111`): Ok Path Helpers

Provides budget-threaded callee contract bridges and proves Segment 4
(`+2168 .. +2420` → `+1284`, `post_seg4_ok_placed_wp` and `post_seg4_after_signal_placed_wp`) for
Block `111` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux

open Arm64 ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open ProofLib hiding SepWPp
open CryptoGames.LibsignalSession CryptoVerification.RustHeap CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet hiding tryCloneFromRefSpec
open CryptoVerification.LibsignalTripleRatchet.Prost hiding int32MergeSpec
open CryptoVerification.LibsignalTripleRatchet.Wire hiding
  TripleRatchetHooksWPlaced TryFromDepsPlaced
open CryptoVerification.LibsignalTripleRatchet.Getters hiding
  dropSpeSpec lsRustDeallocSym blkPC_5 blkPl_5
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetFrom
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Split
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  SepWPp SepWPp.pure_pre SepWPp.exists_pre SepWPp.mono_pre
  PreKeyDeallocOk preKeyDeallocOk_of_hookSat PreKeyDropSpeOk
  PreKeyIntoBoxOk PreKeySigTryFromOk PreKeyTryCloneOk
  preKeyIntoBoxOk_of_hooks preKeyTryCloneOk_of_hooks int32Merge_ok_at_prekey_placed
  preKeyDropSpeOk_cro_of_hookSat preKeySigTryFromOk_cro_of_deps
  post_seg4_ok_placed_wp post_seg4_after_signal_placed_wp
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs SeqEnv
  RustCliAllocBudget rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  noAllocShimBudgetSpec framelessMemcpyBudgetSpec
  TryCloneFromRefEnv tryCloneFromRefEvents tryCloneFromRefSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.IntoBoxedSliceBudget (
  into_boxed_slice_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.TryCloneFromRefBudget (
  try_clone_from_ref_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (dropSpeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.ExtBudget (
  drop_spe_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Prost.DefsBudget (int32MergeSpec)
open LibsignalBinary.Proofs.TripleRatchet.Prost.Int32MergeBudget (int32_merge_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromDefsBudget (TripleRatchetHooksWPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (TryFromDepsPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget (tryFrom_placed_ok_of_deps)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromBaseBudget (
  PreKeySeg4OkEnv PreKeySeg4Env
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp SepWPp.let_state
  SepWPp.frame_noPanic_pk SepWPp.call_noPanic_budget_pk
  PreKeyDeallocOk PreKeyDropSpeOk
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget (
  PreKeyIntoBoxOk PreKeySigTryFromOk
  post_seg4_err_placed_wp post_seg4_ok_pack_placed_wp
)

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

def PreKeyTryCloneOk [LibsignalPlacement] (Inv : Memory → Prop) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (H : LibsignalHooks) : Prop :=
  subroutine_ok (preKeyPlacedProg H) (lsmpl.base 23)
    (withPreKeyInv Inv (tryCloneFromRefSpec M A lim))

theorem preKeyIntoBoxOk_of_hooks [LibsignalPlacement] {Inv : Memory → Prop}
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrealloc : HookSat H lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    PreKeyIntoBoxOk Inv A lim H :=
  ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H) (i := 111) (j := 56)
    hcl_of_inv (into_boxed_slice_placed_ok hdealloc hrealloc)

theorem preKeyTryCloneOk_of_hooks [LibsignalPlacement] {Inv : Memory → Prop}
    (hcl_of_inv : ∀ m, Inv m → LibsignalCodeLoaded lsmpl m)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : HookSat H lsMemcpySym framelessMemcpyBudgetSpec) :
    PreKeyTryCloneOk Inv A lim H :=
  ls_subroutine_ok_pk_of_plain (callerProg := preKeyPlacedProg H) (i := 111) (j := 23)
    hcl_of_inv (try_clone_from_ref_placed_ok hshim halloc hmemcpy)

theorem int32Merge_ok_at_prekey_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false)) :
    subroutine_ok (preKeyPlacedProg H) (lsmpl.base 8)
      (withLsCodeLoaded lsmpl (int32MergeSpec A lim)) :=
  ls_subroutine_ok_of_block (callerProg := preKeyPlacedProg H) (i := 111) (j := 8)
    (int32_merge_placed_ok hshim halloc)

theorem preKeyDropSpeOk_cro_of_hookSat [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    PreKeyDropSpeOk (LibsignalCodeRoLoaded lsmpl) A lim H := by
  have h4 : subroutine_ok ((Getters.blkPC_5).rebase (Getters.blkPl_5).base H) (lsmpl.base 5)
      (withLsCodeRoLoaded lsmpl (dropSpeSpec M A lim)) :=
    subroutine_ok_mono (drop_spe_placed_ok hdealloc)
      (fun _ _ s0 hp => by
        have ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hp
        dsimp only [withLsRoLoaded]
        simp only [sepConj_assoc, sepConj_pure_left_comm, satisfies_pure_sepConj]
        exact ⟨hcro.2, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H)
    (calleeProg := (Getters.blkPC_5).rebase (Getters.blkPl_5).base H) (i := 111) (j := 5) h4

theorem preKeySigTryFromOk_cro_of_deps [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hS : TripleRatchetHooksWPlaced A lim H) (d : TryFromDepsPlaced A lim H) :
    PreKeySigTryFromOk (LibsignalCodeRoLoaded lsmpl) A lim H :=
  ls_subroutine_ok_cro_of_block (callerProg := preKeyPlacedProg H) (i := 111) (j := 85)
    (tryFrom_placed_ok_of_deps hS d)

/-! ## `post_seg4_ok_placed_wp` and `post_seg4_after_signal_placed_wp` (`+2168` → `+1284`) -/

set_option maxHeartbeats 800000 in
theorem post_seg4_ok_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A lim H)
    (hTryClone : PreKeyTryCloneOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {innerMsg : SignalMessage}
    {ik0 ik1 ik2 ik3 : BitVec 64} {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hfits : FitsEnv M lim st (PreKeySeg4OkEnv x))
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
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
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
        boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, PreKeySeg4OkEnv x evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
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
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
  rcases hst with ⟨hsp_eq, hsp, hinv, htr⟩
  have hfits_clone : FitsEnv M lim st (TryCloneFromRefEnv ⟨x.ptr, x.bytes⟩) :=
    FitsEnv.seq_left hfits
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
      (signalMessageAt_unpack A.repAlloc msgG (sp' + 312#64) innerMsg rk0 rk1 rk2 rk3 hrk)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
    SepWPp.exists_pre fun verHi56 => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right
      (sepConj_mono_left (msgHeapAt_pqCap_lt A.repAlloc msgG innerMsg addrW0 addrW1))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine SepWPp.pure_pre fun hpq_lt => ?_
  have hpq_eq := cap_add1_eq_of_lt hpq_lt
  dsimp only [msgWords15At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.of_sepWP_pk hkf hinv (mid := lsmpl.base 23) ?_
  wp_steps_sync_111 (lsmpl.base 23)
  refine ProofLib.SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨inferInstance, fun hinv1 => ?_⟩
  apply SepWPp.let_state; intro s_call
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
      msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1 ∗
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
      boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
      Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
      Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
      Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
      A.pool lim st s_call ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans ?_ (sepConj_mono_left hm312)
      simp only [sepConj_assoc]
      apply entails_of_eq; sep_ac_rfl) ?_
  have hsp_call : s_call.sp = sp' := by dsimp only [s_call]; tryFromPost_sp [hsp_eq]
  refine SepWPp.call_noPanic_budget_pk hkf ((⟨x.ptr, x.bytes⟩ : TryCloneSliceCall), st) hTryClone
    (by dsimp only [s_call]; simp_all [arm64_norm])
    (by dsimp only [s_call]; simp_all [arm64_norm])
    (by dsimp only [s_call]; tryFromPost_sp_align hsp)
    hinv1
    (ret_pc := (blkPl_111).base + 2236#64) (by dsimp only [s_call]; simp_all [arm64_norm])
    (T := (x.ptr ↦ₛ x.bytes) ∗ A.pool lim st s_call ∗ stackAt sp' tryCloneFromRefStack)
    (φ := x.ptr = x.ptr ∧ (BitVec.ofNat 64 x.bytes.length).toNat = x.bytes.length ∧
      x.bytes.length + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (TryCloneFromRefEnv ⟨x.ptr, x.bytes⟩))
    (by
      dsimp only [tryCloneFromRefSpec,
        LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack]
      rw [hsp_call]
      have hx0_c : s_call.readReg64 .x0 = x.ptr := by
        dsimp only [s_call]; simp_all [arm64_norm]
      have hx1_c : s_call.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
        dsimp only [s_call]; simp_all [arm64_norm]
      rw [hx0_c, hx1_c])
    ⟨rfl, hlen_toNat, hlen_le63, hfits_clone⟩
    (by rw [hstackClone]; sep_focus)
    ?_
  clear hTryClone
  intro s2 hpc2 hrun2 hsp2 hsp2_align hinv2 hcs2
  dsimp only [tryCloneFromRefSpec,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack]
  rw [hsp_call, sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hser_ne, hx1_2, htr2⟩ => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs, _⟩
  have hsp2_eq : s2.sp = sp' := hsp2.trans hsp_call
  have hx19_2 : s2.readReg64 .x19 = x.sret := by
    dsimp only [s_call] at hx19_cs; simp [hx19_cs, hx19, arm64_norm]
  have hx22_2 : s2.readReg64 .x22 = 0x44#64 := by
    dsimp only [s_call] at hx22_cs; simp [hx22_cs, hx22, arm64_norm]
  have hx23_2 : s2.readReg64 .x23 = ikCap := by
    dsimp only [s_call] at hx23_cs; simp [hx23_cs, hx23, arm64_norm]
  have hx25_2 : s2.readReg64 .x25 = 1569#64 := by
    dsimp only [s_call] at hx25_cs; simp [hx25_cs, hx25, arm64_norm]
  have hx26_2 : s2.readReg64 .x26 = msgCap := by
    dsimp only [s_call] at hx26_cs; simp [hx26_cs, hx26, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by
    dsimp only [s_call] at hx27_cs; simp [hx27_cs, arm64_norm]
  have hx28_2 : s2.readReg64 .x28 = kyberBoxPtr := by
    dsimp only [s_call] at hx28_cs; simp [hx28_cs, hx28, arm64_norm]
  have htr2_eq : s2.trace = s0.trace := by
    dsimp only [s_call] at htr2; simp [htr2, htr, arm64_norm]
  let evs1 := tryCloneFromRefEvents ⟨x.ptr, x.bytes⟩
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
        msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1 ∗
        boxU8Buf A.repAlloc (s2.readReg64 .x0) x.bytes ∗
        boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim (M.stepEvents evs1 st) s2 ∗ stackAt sp' smallRootStack) ∗
      ((x.ptr ↦ₛ x.bytes) ∗ memRegion (sp' + 312#64) 120))
    (by
      dsimp only [tryCloneFromRefStack, evs1] at hstackClone ⊢
      rw [hstackClone]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine SepWPp.frame_noPanic_pk
    (post_seg4_ok_pack_placed_wp (st := M.stepEvents evs1 st) hkf hdealloc
      hsig hopk hpk hrk hik hser_ne
      ⟨hsp2_eq, hsp2_align, hinv2, htr2_eq⟩
      hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx25_2 hx26_2 hx27_2 hx28_2)
    fun sf Pf ⟨evs2, hevs2, hstf, hent⟩ => ?_
  refine ⟨evs1 ++ evs2, SeqEnv.append rfl hevs2, hstf, ?_⟩
  rw [M.stepEvents_append evs1 evs2 st]
  refine Entails.trans (sepConj_mono_left hent) ?_
  apply entails_of_eq; sep_ac_rfl

private theorem mono_noPanic_pk {prog : Program} {ret : BitVec 64}
    {s : Arm64.State} {P : SepProp} {Q Q' : Arm64.State → SepProp → Prop}
    (h : SepWPp prog ret s P Q preKeyNoPanicQp)
    (hq : ∀ sf Pf, Q sf Pf → Q' sf Pf) :
    SepWPp prog ret s P Q' preKeyNoPanicQp := by
  intro R hm hL
  rcases h R hm hL with ⟨sf, hsteps, ⟨hpc, hrun, Pf, hmf, hqf, hv⟩ | ⟨_, _, _, hp⟩ | ⟨_, hoom2⟩⟩
  · exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, Pf, hmf, hq sf Pf hqf, hv⟩⟩
  · exact False.elim hp
  · exact (not_satisfies_false_sepConj hoom2).elim

theorem post_seg4_after_signal_placed_wp [LibsignalPlacement]
    {Inv : Memory → Prop} (hkf : KeepsFrozenInv Inv)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    (hdealloc : PreKeyDeallocOk Inv A lim H)
    (hTryClone : PreKeyTryCloneOk Inv A lim H)
    {x : PreKeyTryFromArgs} {s0 s : State}
    {sp' kyberBoxPtr bkCap bkPtr ikCap ikPtr msgCap msgPtr : BitVec 64}
    {ik0 ik1 ik2 ik3 : BitVec 64} {opkVal : BitVec 32}
    {b0 b1 b2 b3 b4 b5 b6 b7 b8 b31 : BitVec 8}
    {w9 : BitVec 32} {w13 : BitVec 16} {w15 w23 : BitVec 64}
    (hlt : x.bytes.length < 2 ^ 32)
    (hfits : FitsEnv M lim st (PreKeySeg4Env x))
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
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
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
        boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
        Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
        Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
        A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf => ∃ evs : List AllocEvent, PreKeySeg4Env x evs ∧
        PreKeyPostState Inv s0 sp' sf ∧
        (Pf ⊢ preKeyResultAt A.repAlloc x.sret x ∗ (x.ptr ↦ₛ x.bytes) ∗
          ((sp' + 12#64) ↦₃₂ b7.zeroExtend 32) ∗ ((sp' + 16#64) ↦₃₂ x.kpkId) ∗
          ((sp' + 20#64) ↦₃₂ opkTag x) ∗ ((sp' + 24#64) ↦₃₂ opkVal) ∗
          ((sp' + 28#64) ↦₃₂ x.spkId) ∗ ((sp' + 56#64) ↦₃₂ x.regId) ∗
          ((sp' + 68#64) ↦₃₂ b8.zeroExtend 32) ∗ ((sp' + 72#64) ↦₆₄ w15) ∗
          ((sp' + 112#64) ↦₆₄ w23) ∗ ((sp' + 120#64) ↦₈ b31) ∗
          ((sp' + 128#64) ↦₃₂ w9) ∗ ((sp' + 132#64) ↦₁₆ w13) ∗
          sevenBytesHeadAt (sp' + 136#64) b0 b1 b2 b3 b4 b5 b6 ∗
          ((sp' + 144#64) ↦₆₄ ik0) ∗ ((sp' + 152#64) ↦₆₄ ik1) ∗
          ((sp' + 160#64) ↦₆₄ ik2) ∗ ((sp' + 168#64) ↦₆₄ ik3) ∗
          ((sp' + 80#64) ↦₆₄ bkPtr) ∗ ((sp' + 88#64) ↦₆₄ bkCap) ∗
          ((sp' + 96#64) ↦₆₄ msgPtr) ∗ ((sp' + 104#64) ↦₆₄ ikPtr) ∗
          memRegion (sp' + 176#64) 112 ∗ memRegion (sp' + 312#64) 120 ∗
          A.pool lim (M.stepEvents evs st) sf ∗ stackAt sp' smallRootStack))
      preKeyNoPanicQp := by
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
          signalMessageResultAt A.repAlloc [] (sp' + 312#64)
            (SignalMessage.tryFrom protoSignalCodec x.inner) ∗
          memRegion x.sret 248 ∗ boxU8Buf A.repAlloc kyberBoxPtr x.kyberBytes ∗
          Wire.vecU8Buf A.repAlloc msgCap msgPtr x.inner ∗
          Wire.vecU8Buf A.repAlloc ikCap ikPtr x.ikBytes ∗
          Wire.vecU8Buf A.repAlloc bkCap bkPtr x.bkBytes ∗
          A.pool lim st s ∗ stackAt sp' smallRootStack) ∗
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
        apply entails_of_eq; sep_ac_rfl) ?_
    refine SepWPp.frame_noPanic_pk
      (post_seg4_err_placed_wp hkf hdealloc hsig hst hpc hrun
        hx29 hx28 hx26 hx25 hx24 hx23 hx19)
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, Or.inl hevs, hstf, ?_⟩
    refine Entails.trans (sepConj_mono_left hent) ?_
    rw [h112_split]
    apply entails_of_eq; sep_ac_rfl
  · rw [← hsig]
    refine mono_noPanic_pk
      (post_seg4_ok_placed_wp hkf hdealloc hTryClone hlt
        (fun evs hevs => hfits evs (Or.inr hevs))
        hsig hopk hpk hik hst hpc hrun
        hx29 hx28 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19)
      fun sf Pf ⟨evs, hevs, hstf, hent⟩ => ⟨evs, Or.inr hevs, hstf, ?_⟩
    refine Entails.trans hent ?_
    apply entails_of_eq; sep_ac_rfl

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOkPlacedBudgetAux
