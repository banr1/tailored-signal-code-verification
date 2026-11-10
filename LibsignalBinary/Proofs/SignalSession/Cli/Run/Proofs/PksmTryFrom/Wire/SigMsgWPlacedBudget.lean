/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.IdentKeyWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6ExitsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.W6StatesPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromOk
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Budget-Threaded `[LibsignalPlacement]` `SignalMessage::try_from` and `try_clone_from_ref` Stage

Allocation-budget (`RustCliAllocBudget M`) proofs of the `SignalMessage::try_from` call,
`.error e` branch, and `.ok innerMsg` + `try_clone_from_ref` stage (`+0x864 → +0x8c0 / +0x9f0`)
on `preKeyPlacedProg H`.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlacedBudget

open Arm64 ProofLib.ProgramReflection SepProp
open ProofLib hiding SepWPp
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
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.FieldsEpilogue
open CryptoVerification.E2E.Pqxdh.ResponderWire hiding
  preKeyTryFromName preKeyTryFromStack preKeyTryFromSubStack PreKeyLoopRegs SepWPp
  spAligned_sub608 cond_eq_subs1_false
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.PksmWire hiding
  SepWPp smw_SepWPp
  preKey_sigMsg_call_864_to_878_placed_wpX
  preKey_sigMsg_call_864_to_878_from_ident_placed_wpX
  preKey_sigMsg_err_878_to_9f0_placed_wpX
  preKey_sigMsg_ok_878_to_8bc_placed_wpX
  preKey_sigMsg_clone_ok_8bc_to_8c0_placed_wpX
  preKey_sigMsg_clone_oom_8bc_to_a68_placed_wpX
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget (
  preKeyNoPanicQp
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedBBudget (
  SigTryFromConcreteEnv tryFromEnvGen_eq_sigTryFromEnv
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.CalleesPlacedBudget (
  PksmCalleesPlaced
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.DecodeKeyBPlacedBudget (
  sepWP_done_sync_pool_111 sepWP_seg_111
)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.ErrTailBWPlacedBudget (
  sepWPp_anyQp_of_noPanic
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (
  TryCloneFromRefEnv tryCloneFromRefEvents tryCloneFromRefSpecWithStack tryCloneFromRefSpecX
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux (
  TryFromEnvGen tryFromPlacedSpecGen
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBudget (
  sepWPp_end_noPanic_placed
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBoxesBudget (
  TryCloneBytesEnv tryCloneBytesEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget (
  TryFromPostEnv
)

abbrev smw_SepWPp := @Wire.SepWPp
private abbrev SepWPp := @Wire.SepWPp
private abbrev SepWPp.pure_pre := @Wire.SepWPp.pure_pre
private abbrev SepWPp.exists_pre := @Wire.SepWPp.exists_pre
private abbrev SepWPp.mono_pre := @Wire.SepWPp.mono_pre
private abbrev of_sepWP_frozen_pk :=
  @CryptoVerification.E2E.Pqxdh.ResponderWire.SepWPp.of_sepWP_pk
private abbrev of_sepWP_end_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.of_sepWP_end_noPanic_pk
private abbrev call_noPanic_budget_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.call_noPanic_budget_pk
private abbrev frame_noPanic_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.frame_noPanic_pk
private abbrev let_state_pk :=
  @LibsignalBinary.Proofs.E2E.Pqxdh.ResponderWire.PreKeyTryFromPostPlacedABudget.SepWPp.let_state

attribute [local irreducible] Program.fetch Program.externAt?
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp

private theorem smwb_bv_sub_add_lit' (x a b : BitVec 64) : x - a + b = x - (a - b) := by bv_omega
private theorem smwb_bv_sub_sub_lit (x a b : BitVec 64) : x - a - b = x - (a + b) := by bv_omega

attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit smwb_bv_sub_add_lit' smwb_bv_sub_sub_lit BitVec.toNat_zero
  bv_add_neg_8 bv_add_neg_16 bv_add_neg_24 bv_add_neg_32 bv_add_neg_40
  bv_add_neg_48 bv_add_neg_55 bv_add_neg_56 bv_add_neg_64 bv_add_neg_72
  bv_add_neg_80 bv_add_neg_87 bv_add_neg_88 bv_add_neg_96 bv_add_neg_104
  bv_add_neg_112 bv_add_neg_128 bv_add_neg_136 bv_add_neg_152 bv_add_neg_160
  bv_add_neg_168 bv_add_neg_176 bv_add_neg_184 bv_add_neg_186 bv_add_neg_191
  bv_add_neg_192 bv_add_neg_196 bv_add_neg_200 bv_add_neg_216 bv_add_neg_512

/-! ## 0. Thin `SignalMessage::try_from` Envelope Alias -/

/-- Pointer-independent allocation-event envelope for the inner
`<SignalMessage as TryFrom<&[u8]>>::try_from` call on `msg`. -/
abbrev SigMsgCallEnv : List (BitVec 8) → List AllocEvent → Prop :=
  SigTryFromConcreteEnv

theorem tryFromEnvGen_eq_sigMsgCallEnv (ptr ret : BitVec 64) (msg : List (BitVec 8)) :
    TryFromEnvGen (fun g => TryFromPostEnv g.bytes) ⟨ptr, msg, ret⟩ =
      SigMsgCallEnv msg :=
  tryFromEnvGen_eq_sigTryFromEnv TryFromPostEnv ptr msg ret

abbrev preKey_sigMsg_clone_oom_8bc_to_a68_placed_wpX :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.preKey_sigMsg_clone_oom_8bc_to_a68_placed_wpX

abbrev preKey_sigMsg_err_878_to_9f0_noPool_placed_wpX :=
  @CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.preKey_sigMsg_err_878_to_9f0_placed_wpX

/-! ## 1. Leaf L3a (`+0x864 .. +0x878` / `2148 .. 2168`): `SignalMessage::try_from` Call -/

theorem preKey_sigMsg_call_864_to_878_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (SigMsgCallEnv msg))
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2148#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        memRegion (sp' + 312#64) 120 ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        ∃ evsS : List AllocEvent,
          SigMsgCallEnv msg evsS ∧
          IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
            bk pk ik ipk sf ∧
          (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
            ((sp' + 56#64) ↦₃₂ regId) ∗
            ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
            ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            signalMessageResultAt A.repAlloc [] (sp' + 312#64)
              (SignalMessage.tryFrom protoSignalCodec msg) ∗
            Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evsS st) sf ∗ stackAt sp' smallRootStack))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, hx27, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have h56_split := ProofLib.pointsTo64_split32 (sp' + 56#64) w56
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h56_split
  have h56_lo : BitVec.extractLsb' 0 32 w56 = BitVec.truncate 32 w56 := by bv_bits
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₃₂ BitVec.truncate 32 w56) ∗
      ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      (msgPtr ↦ₛ msg) ∗ vecU8Rest A.repAlloc msgCap msgPtr msg ∗
      lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
    (by
      rw [h56_split, h56_lo]
      simp only [sepConj_assoc]
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
            (vecU8Buf_to_slice_rest A.repAlloc msgCap msgPtr msg))))))) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 85) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  have hmsg_toNat : (BitVec.ofNat 64 msg.length).toNat = msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlog_eq : logOff tryFromPlacedImg = lsLogOff := logOff_tryFromPlacedImg
  have hfits_sig :
      FitsEnv M lim st
        (TryFromEnvGen (fun g => TryFromPostEnv g.bytes) ⟨msgPtr, msg, sp' + 312#64⟩) := by
    rw [tryFromEnvGen_eq_sigMsgCallEnv]
    exact hfit
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
    ((⟨msgPtr, msg, sp' + 312#64⟩ : TryFromGhost), st) hC.sigTryFrom
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2168#64) (by simp [s_call, arm64_norm])
    (T := (msgPtr ↦ₛ msg) ∗ memRegion (sp' + 312#64) 120 ∗ logOff tryFromPlacedImg ∗
      stackAt sp' smallRootStack ∗ A.pool lim st s_call)
    (φ := msgPtr = msgPtr ∧ (BitVec.ofNat 64 msg.length).toNat = msg.length ∧
      msg.length < 2 ^ 32 ∧ sp' + 312#64 = sp' + 312#64 ∧
      FitsEnv M lim st
        (TryFromEnvGen (fun g => TryFromPostEnv g.bytes) ⟨msgPtr, msg, sp' + 312#64⟩))
    (by simp [s_call, tryFromPlacedSpecGen, hsp_eq, arm64_norm])
    ⟨rfl, hmsg_toNat, hlt_msg, rfl, hfits_sig⟩
    (by rw [hlog_eq]; sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [tryFromPlacedSpecGen]
  simp only [hlog_eq, sepConj_assoc, sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_pre fun evsS => SepWPp.pure_pre fun htr2 => ?_
  refine SepWPp.pure_pre fun hevsS => ?_
  rw [tryFromEnvGen_eq_sigMsgCallEnv] at hevsS
  rcases hcs2 with
    ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  refine ProofLib.SepWP.done hpc2 hrun2 ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨evsS, hevsS,
    ⟨⟨hsp2_eq, hsp2_align, hcl3, by simp [htr2, s_call, htr, arm64_norm]⟩,
      hbk_ok, hpk_eq, hpk_bytes, hik_deser,
      by simp [hx29_2, s_call, hx29, arm64_norm],
      by simp [hx28_2, s_call, hx28, arm64_norm],
      by simp [hx27_2, s_call, hx27, arm64_norm],
      by simp [hx26_2, s_call, hx26, arm64_norm],
      by simp [hx25_2, s_call, hx25, arm64_norm],
      by simp [hx24_2, s_call, hx24, arm64_norm],
      by simp [hx23_2, s_call, hx23, arm64_norm],
      by simp [hx22_2, s_call, hx22, arm64_norm],
      by simp [hx21_2, s_call, hx21, arm64_norm],
      by simp [hx20_2, s_call, hx20, arm64_norm],
      by simp [hx19_2, s_call, hx19, arm64_norm]⟩, ?_⟩
  have hrepack_msg := slice_rest_to_vecU8Buf A.repAlloc msgCap msgPtr msg
  refine Entails.trans
    (Q := ((msgPtr ↦ₛ msg) ∗ vecU8Rest A.repAlloc msgCap msgPtr msg) ∗
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₃₂ regId) ∗
        ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec msg) ∗
        lsLogOff ∗ A.pool lim (M.stepEvents evsS st) s2 ∗ stackAt sp' smallRootStack))
    (by
      simp only [s_call, hsp_eq, arm64_norm]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hrepack_msg) ?_
  apply entails_of_eq; sep_ac_rfl

theorem preKey_sigMsg_call_864_to_878_from_ident_placed_wpX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgPtr w56 tag : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)} {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (SigMsgCallEnv msg))
    (hlt_msg : msg.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2148#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2168#64) s
      (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
        ((sp' + 56#64) ↦₆₄ w56) ∗
        ((sp' + 96#64) ↦₆₄ msgPtr) ∗
        ((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
        memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72 ∗
        Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
        lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
      (fun sf Pf =>
        ∃ evsS : List AllocEvent,
          SigMsgCallEnv msg evsS ∧
          IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
            bk pk ik ipk sf ∧
          (Pf ⊢ ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
            ((sp' + 56#64) ↦₃₂ regId) ∗
            ((sp' + 60#64) ↦₃₂ BitVec.extractLsb' 32 32 w56) ∗
            ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            signalMessageResultAt A.repAlloc [] (sp' + 312#64)
              (SignalMessage.tryFrom protoSignalCodec msg) ∗
            Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
            lsLogOff ∗ A.pool lim (M.stepEvents evsS st) sf ∗ stackAt sp' smallRootStack))
      Qp := by
  have h120 := ident_slot_entails_memRegion120 sp' tag ipk
  refine SepWPp.mono_pre
    (P' := ((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
      ((sp' + 56#64) ↦₆₄ w56) ∗
      ((sp' + 96#64) ↦₆₄ msgPtr) ∗
      memRegion (sp' + 312#64) 120 ∗
      Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
      lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack)
    (by
      refine Entails.trans
        (Q := (((sp' + 312#64) ↦₆₄ tag) ∗ ((sp' + 320#64) ↦ₛ ipk.bytes.toList) ∗
            memRegion (sp' + 352#64) 8 ∗ memRegion (sp' + 360#64) 72) ∗
          (((sp' + 32#64) ↦₆₄ BitVec.ofNat 64 msg.length) ∗
            ((sp' + 56#64) ↦₆₄ w56) ∗
            ((sp' + 96#64) ↦₆₄ msgPtr) ∗
            Wire.vecU8Buf A.repAlloc msgCap msgPtr msg ∗
            lsLogOff ∗ A.pool lim st s ∗ stackAt sp' smallRootStack))
        (by apply entails_of_eq; sep_ac_rfl) ?_
      refine Entails.trans (sepConj_mono_left h120) ?_
      apply entails_of_eq; sep_ac_rfl) ?_
  exact preKey_sigMsg_call_864_to_878_placed_wpX hC hfit hlt_msg hst hpc hrun

/-! ## 2. Leaf L3b (`+0x878 → +0x9f0` / `2168 → 2544`): `SignalMessage::try_from` Err Branch -/

theorem preKey_sigMsg_err_878_to_9f0_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {msg : List (BitVec 8)} {e : SignalProtocolError}
    {Qp : State → SepProp → Prop}
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .error e)
    (hst : IdentOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb regId
      bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2544#64) s
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 48 ∗ A.pool lim st s)
      (fun sf Pf =>
        SigMsgErrStatePlaced s0 sp' sret kyberBoxPtr kyberBoxLen ikCap msgCap sf ∧
        (Pf ⊢ (∃∗ ew0 : BitVec 64, ∃∗ ew1 : BitVec 64, ∃∗ ew2 : BitVec 64,
          ∃∗ ew3 : BitVec 64, ∃∗ ew4 : BitVec 64, ∃∗ ew5 : BitVec 64,
          ⌜∀ b : BitVec 64,
            (b ↦₆₄ ew0) ∗ ((b + 8#64) ↦₆₄ ew1) ∗ memRegion (b + 16#64) 32 ⊢
              speAt A.repAlloc [] b e⌝ ∗
          ((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
          ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
          ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
          memRegion (sp' + 312#64) 120) ∗ A.pool lim st sf))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, _, _, _, _,
    hx29, hx28, _, hx26, hx25, hx24, hx23, _, _, _, hx19⟩
  rw [hsig]
  dsimp only [signalMessageResultAt, errResultAt]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub, sepConj_assoc]
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_left (speAt_tryFrom_words2 A.repAlloc (sp' + 320#64) hsig))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew0 => SepWPp.exists_pre fun ew1 => ?_
  simp only [sepConj_pure_left_comm]
  refine SepWPp.pure_pre fun hpack => ?_
  refine SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (entails_of_eq
        (CryptoVerification.SignalSession.Cli.RunProofs.PksmWire.memRegion32_words4
          (sp' + 336#64))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun ew5 => SepWPp.exists_pre fun ew4 =>
    SepWPp.exists_pre fun ew3 => SepWPp.exists_pre fun ew2 => ?_
  rw [memRegion48_words6 (sp' + 176#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_pre fun t5 => SepWPp.exists_pre fun t4 =>
    SepWPp.exists_pre fun t3 => SepWPp.exists_pre fun t2 =>
    SepWPp.exists_pre fun t1 => SepWPp.exists_pre fun t0 => ?_
  refine sepWPp_end_noPanic_placed (s0 := s0) hcl ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    by simp [hx29, arm64_norm],
    by simp [hx28, arm64_norm],
    by simp [hx25, arm64_norm],
    by simp [hx26, arm64_norm],
    by simp [hx23, arm64_norm],
    by simp [hx19, arm64_norm]⟩, ?_⟩
  have hm120 := words7_memRegion64_entails_memRegion120 (sp' + 312#64) errTag ew0 ew1 ew2 ew3 ew4 ew5
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm120
  have hex :
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion (sp' + 312#64) 120) ⊢
      (∃∗ ew0' : BitVec 64, ∃∗ ew1' : BitVec 64, ∃∗ ew2' : BitVec 64,
        ∃∗ ew3' : BitVec 64, ∃∗ ew4' : BitVec 64, ∃∗ ew5' : BitVec 64,
        ⌜∀ b : BitVec 64,
          (b ↦₆₄ ew0') ∗ ((b + 8#64) ↦₆₄ ew1') ∗ memRegion (b + 16#64) 32 ⊢
            speAt A.repAlloc [] b e⌝ ∗
        ((sp' + 176#64) ↦₆₄ ew0') ∗ ((sp' + 184#64) ↦₆₄ ew1') ∗
        ((sp' + 192#64) ↦₆₄ ew2') ∗ ((sp' + 200#64) ↦₆₄ ew3') ∗
        ((sp' + 208#64) ↦₆₄ ew4') ∗ ((sp' + 216#64) ↦₆₄ ew5') ∗
        memRegion (sp' + 312#64) 120) := by
    refine Entails.trans ?_ (Entails.sepExists_intro ew0)
    refine Entails.trans ?_ (Entails.sepExists_intro ew1)
    refine Entails.trans ?_ (Entails.sepExists_intro ew2)
    refine Entails.trans ?_ (Entails.sepExists_intro ew3)
    refine Entails.trans ?_ (Entails.sepExists_intro ew4)
    refine Entails.trans ?_ (Entails.sepExists_intro ew5)
    rw [pure_true_emp hpack, emp_sepConj]
    exact Entails.refl _
  refine Entails.trans
    (Q := (((sp' + 312#64) ↦₆₄ errTag) ∗ ((sp' + 320#64) ↦₆₄ ew0) ∗
        ((sp' + 328#64) ↦₆₄ ew1) ∗ ((sp' + 336#64) ↦₆₄ ew2) ∗
        ((sp' + 344#64) ↦₆₄ ew3) ∗ ((sp' + 352#64) ↦₆₄ ew4) ∗
        ((sp' + 360#64) ↦₆₄ ew5) ∗ memRegion (sp' + 368#64) 64) ∗
      (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        A.pool lim st _))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hm120) ?_
  refine Entails.trans
    (Q := (((sp' + 176#64) ↦₆₄ ew0) ∗ ((sp' + 184#64) ↦₆₄ ew1) ∗
        ((sp' + 192#64) ↦₆₄ ew2) ∗ ((sp' + 200#64) ↦₆₄ ew3) ∗
        ((sp' + 208#64) ↦₆₄ ew4) ∗ ((sp' + 216#64) ↦₆₄ ew5) ∗
        memRegion (sp' + 312#64) 120) ∗ A.pool lim st _)
    (by apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hex) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  exact Entails.refl _

/-! ## 3. Leaf L4 (`+0x878 → +0x8bc → +0x8c0`): `Ok(innerMsg)` + `try_clone_from_ref` -/

set_option maxHeartbeats 1200000 in
theorem preKey_sigMsg_ok_878_to_8bc_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {b msg : List (BitVec 8)} {innerMsg : SignalMessage}
    {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (TryCloneBytesEnv b))
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hlen_lt : b.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret (BitVec.ofNat 64 b.length) ptr0 kyberBoxPtr kyberBoxLen
      ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2236#64) s
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 112 ∗
        (ptr0 ↦ₛ b) ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ evsC : List AllocEvent,
          TryCloneBytesEnv b evsC ∧
          sf.sp = sp' ∧ sf.spAligned = true ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          sf.trace = s0.trace ∧ sf.readReg64 .x0 ≠ 0#64 ∧
          ecKeyParses bk = true ∧ pkOf bk = pk ∧ (pkOf bk).bytes.toList = (bk.take 33).drop 1 ∧
          PublicKey.deserialize ik = .ok ipk ∧
          sf.readReg64 .x1 = BitVec.ofNat 64 b.length ∧
          sf.readReg64 .x29 = sp' + 512#64 ∧ sf.readReg64 .x28 = kyberBoxPtr ∧
          sf.readReg64 .x26 = msgCap ∧ sf.readReg64 .x25 = kyberBoxLen ∧
          sf.readReg64 .x24 = sp' + 312#64 ∧ sf.readReg64 .x23 = ikCap ∧
          sf.readReg64 .x22 = vb.zeroExtend 64 ∧ sf.readReg64 .x21 = ptr0 ∧
          sf.readReg64 .x20 = BitVec.ofNat 64 b.length ∧ sf.readReg64 .x19 = sret ∧
          (Pf ⊢ (∃∗ msgG : SignalMessageGhost,
            ∃∗ rk0 : BitVec 64, ∃∗ rk1 : BitVec 64, ∃∗ rk2 : BitVec 64, ∃∗ rk3 : BitVec 64,
            ∃∗ addrW0 : BitVec 64, ∃∗ addrW1 : BitVec 64, ∃∗ verHi56 : BitVec 56,
            ⌜sf.readReg64 .x27 = msgG.pqCap ∧
              (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
                (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3))⌝ ∗
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
            msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1) ∗
            boxU8Buf A.repAlloc (sf.readReg64 .x0) b ∗
            memRegion (sp' + 312#64) 120 ∗
            (ptr0 ↦ₛ b) ∗ A.pool lim (M.stepEvents evsC st) sf ∗
            stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  rcases hst with ⟨⟨hsp_eq, hsp, hcl, htr⟩, hbk_ok, hpk_eq, hpk_bytes, hik_deser,
    hx29, hx28, _, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19⟩
  have hlen_le63 : b.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstackClone := stackAt_skipFieldStackX_tryCloneX sp'
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
  refine of_sepWP_frozen_pk keepsFrozenInv_codeRoLoaded hcl (mid := lsmpl.base 23) ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st fun _ hcl1 => ?_
  refine let_state_pk ?_; intro s_call
  have hm312 := msgWords15At_entails_memRegion (sp' + 312#64)
    msgG.pqCap msgG.pqPtr (BitVec.ofNat 64 innerMsg.pqRatchet.length)
    msgG.ctPtr (BitVec.ofNat 64 innerMsg.ciphertext.length)
    msgG.serPtr (BitVec.ofNat 64 innerMsg.serialized.length)
    rk0 rk1 rk2 rk3 addrW0 addrW1
    (innerMsg.previousCounter ++ innerMsg.counter)
    (verHi56 ++ innerMsg.messageVersion)
  dsimp only [msgWords15At] at hm312
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm312
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
      (ptr0 ↦ₛ b) ∗ A.pool lim st s_call ∗ stackAt sp' (Prost.skipFieldStackX 100))
    (by
      refine Entails.trans ?_ (sepConj_mono_left hm312)
      simp only [s_call, sepConj_assoc]
      apply entails_of_eq; sep_ac_rfl) ?_
  have hfit_clone : FitsEnv M lim st (TryCloneFromRefEnv ⟨ptr0, b⟩) := hfit
  refine call_noPanic_budget_pk keepsFrozenInv_codeRoLoaded
    ((⟨ptr0, b⟩ : TryCloneSliceCall), st) hC.tryCloneX
    (by simp [s_call, arm64_norm]) (by simp [s_call, hrun, arm64_norm])
    (by simp only [s_call, State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcl1
    (ret_pc := (blkPl_111).base + 2236#64) (by simp [s_call, arm64_norm])
    (T := (ptr0 ↦ₛ b) ∗ A.pool lim st s_call ∗ stackAt sp' (extHookStack + 48))
    (φ := ptr0 = ptr0 ∧ (BitVec.ofNat 64 b.length).toNat = b.length ∧
      b.length + 1 ≤ 2 ^ 63 ∧ FitsEnv M lim st (TryCloneFromRefEnv ⟨ptr0, b⟩))
    (by simp [s_call,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecX,
      LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack,
      hsp_eq, arm64_norm])
    ⟨rfl, hlen_toNat, hlen_le63, hfit_clone⟩
    (by
      rw [hstackClone, show LibsignalTripleRatchet.tryCloneFromRefStackX = extHookStack + 48 from rfl]
      sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcl2 hcs2
  dsimp only [LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecX,
    LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget.tryCloneFromRefSpecWithStack]
  rw [sepConj_assoc]
  refine SepWPp.pure_pre fun ⟨hx0_ne, hx1_2, htr2⟩ => ?_
  rcases hcs2 with
    ⟨hx19_cs, hx20_cs, hx21_cs, hx22_cs, hx23_cs, hx24_cs, hx25_cs, hx26_cs, hx27_cs, hx28_cs,
      hx29_cs, _⟩
  have hsp2_eq : s2.sp = sp' := by simp [hsp2, s_call, hsp_eq, arm64_norm]
  have hx27_2 : s2.readReg64 .x27 = msgG.pqCap := by simp [hx27_cs, s_call, arm64_norm]
  refine of_sepWP_end_noPanic_pk keepsFrozenInv_codeRoLoaded hcl2 ?_
  refine ProofLib.SepWP.done hpc2 hrun2 ⟨inferInstance, fun hcl3 => ?_⟩
  refine ⟨tryCloneBytesEvents b, rfl,
    hsp2_eq, hsp2_align, hcl3,
    by simp [htr2, s_call, htr, arm64_norm],
    hx0_ne,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser, hx1_2,
    by simp [hx29_cs, s_call, hx29, arm64_norm],
    by simp [hx28_cs, s_call, hx28, arm64_norm],
    by simp [hx26_cs, s_call, hx26, arm64_norm],
    by simp [hx25_cs, s_call, hx25, arm64_norm],
    by simp [hx24_cs, s_call, hx24, arm64_norm],
    by simp [hx23_cs, s_call, hx23, arm64_norm],
    by simp [hx22_cs, s_call, hx22, arm64_norm],
    by simp [hx21_cs, s_call, hx21, arm64_norm],
    by simp [hx20_cs, s_call, hx20, arm64_norm],
    by simp [hx19_cs, s_call, hx19, arm64_norm], ?_⟩
  have hpack_words :
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
      msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1 ⊢
      ∃∗ msgG' : SignalMessageGhost,
        ∃∗ rk0' : BitVec 64, ∃∗ rk1' : BitVec 64, ∃∗ rk2' : BitVec 64, ∃∗ rk3' : BitVec 64,
        ∃∗ addrW0' : BitVec 64, ∃∗ addrW1' : BitVec 64, ∃∗ verHi56' : BitVec 56,
        ⌜s2.readReg64 .x27 = msgG'.pqCap ∧
          (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
            (a ↦₆₄ rk0') ∗ ((a + 8#64) ↦₆₄ rk1') ∗ ((a + 16#64) ↦₆₄ rk2') ∗ ((a + 24#64) ↦₆₄ rk3'))⌝ ∗
        ((sp' + 176#64) ↦₆₄ msgG'.pqPtr) ∗
        ((sp' + 184#64) ↦₆₄ BitVec.ofNat 64 innerMsg.pqRatchet.length) ∗
        ((sp' + 192#64) ↦₆₄ msgG'.ctPtr) ∗
        ((sp' + 200#64) ↦₆₄ BitVec.ofNat 64 innerMsg.ciphertext.length) ∗
        ((sp' + 208#64) ↦₆₄ msgG'.serPtr) ∗
        ((sp' + 216#64) ↦₆₄ BitVec.ofNat 64 innerMsg.serialized.length) ∗
        ((sp' + 224#64) ↦₆₄ rk0') ∗ ((sp' + 232#64) ↦₆₄ rk1') ∗
        ((sp' + 240#64) ↦₆₄ rk2') ∗ ((sp' + 248#64) ↦₆₄ rk3') ∗
        ((sp' + 256#64) ↦₆₄ addrW0') ∗ ((sp' + 264#64) ↦₆₄ addrW1') ∗
        ((sp' + 272#64) ↦₆₄ (innerMsg.previousCounter ++ innerMsg.counter)) ∗
        ((sp' + 280#64) ↦₆₄ (verHi56' ++ innerMsg.messageVersion)) ∗
        msgHeapAt A.repAlloc msgG' innerMsg addrW0' addrW1' := by
    refine Entails.trans ?_ (Entails.sepExists_intro msgG)
    refine Entails.trans ?_ (Entails.sepExists_intro rk0)
    refine Entails.trans ?_ (Entails.sepExists_intro rk1)
    refine Entails.trans ?_ (Entails.sepExists_intro rk2)
    refine Entails.trans ?_ (Entails.sepExists_intro rk3)
    refine Entails.trans ?_ (Entails.sepExists_intro addrW0)
    refine Entails.trans ?_ (Entails.sepExists_intro addrW1)
    refine Entails.trans ?_ (Entails.sepExists_intro verHi56)
    rw [pure_true_emp ⟨hx27_2, hrk⟩, emp_sepConj]
    exact Entails.refl _
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
        ((sp' + 280#64) ↦₆₄ (verHi56 ++ innerMsg.messageVersion)) ∗
        msgHeapAt A.repAlloc msgG innerMsg addrW0 addrW1) ∗
      (boxU8Buf A.repAlloc (s2.readReg64 .x0) b ∗
        memRegion (sp' + 312#64) 120 ∗
        (ptr0 ↦ₛ b) ∗
        A.pool lim (M.stepEvents (tryCloneBytesEvents b) st) s2 ∗
        stackAt sp' (Prost.skipFieldStackX 100)))
    (by
      rw [hstackClone, show LibsignalTripleRatchet.tryCloneFromRefStackX = extHookStack + 48 from rfl]
      simp only [s_call, hsp_eq, tryCloneFromRefEvents, tryCloneBytesEvents, arm64_norm]
      apply entails_of_eq; sep_ac_rfl) ?_
  refine Entails.trans (sepConj_mono_left hpack_words) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  exact Entails.refl _

theorem preKey_sigMsg_clone_ok_8bc_to_8c0_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks}
    {s0 s : State}
    {sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap msgW0 clonePtr : BitVec 64}
    {vb : BitVec 8}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {Qp : State → SepProp → Prop}
    (hclone_ne : clonePtr ≠ 0#64)
    (hsp_eq : s.sp = sp') (hsp : s.spAligned = true)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hbk_ok : ecKeyParses bk = true) (hpk_eq : pkOf bk = pk)
    (hpk_bytes : (pkOf bk).bytes.toList = (bk.take 33).drop 1)
    (hik_deser : PublicKey.deserialize ik = .ok ipk)
    (hpc : s.pc = (blkPl_111).base + 2236#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = clonePtr)
    (hx1 : s.readReg64 .x1 = len)
    (hx29 : s.readReg64 .x29 = sp' + 512#64) (hx28 : s.readReg64 .x28 = kyberBoxPtr)
    (hx27 : s.readReg64 .x27 = msgW0) (hx26 : s.readReg64 .x26 = msgCap)
    (hx25 : s.readReg64 .x25 = kyberBoxLen) (hx24 : s.readReg64 .x24 = sp' + 312#64)
    (hx23 : s.readReg64 .x23 = ikCap) (hx22 : s.readReg64 .x22 = vb.zeroExtend 64)
    (hx21 : s.readReg64 .x21 = ptr0) (hx20 : s.readReg64 .x20 = len)
    (hx19 : s.readReg64 .x19 = sret) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2240#64) s (A.pool lim st s)
      (fun sf Pf =>
        SigMsgOkStatePlaced s0 sp' sret len ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap vb
          msgW0 clonePtr bk pk ik ipk sf ∧
        (Pf ⊢ A.pool lim st sf))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  have hbeq : (clonePtr == 0#64) = false := beq_false_of_ne hclone_ne
  refine sepWPp_end_noPanic_placed (s0 := s0) hcl ?_
  apply sepWP_seg_111; intro _m_strip; wp_steps
  refine sepWP_done_sync_pool_111 A lim st (F := emp) (hPm := by rw [sepConj_emp]) fun _ hcl1 => ?_
  refine ⟨⟨⟨by tryFromPost_sp [hsp_eq], by tryFromPost_sp_align hsp, hcl1,
      by simp [htr, arm64_norm]⟩,
    hbk_ok, hpk_eq, hpk_bytes, hik_deser, hclone_ne,
    by simp [hx0, arm64_norm], by simp [hx1, arm64_norm],
    by simp [hx29, arm64_norm], by simp [hx28, arm64_norm],
    by simp [hx27, arm64_norm], by simp [hx26, arm64_norm],
    by simp [hx25, arm64_norm], by simp [hx24, arm64_norm],
    by simp [hx23, arm64_norm], by simp [hx22, arm64_norm],
    by simp [hx21, arm64_norm], by simp [hx20, arm64_norm],
    by simp [hx19, arm64_norm]⟩, ?_⟩
  rw [sepConj_emp]
  exact Entails.refl _

/-- Combined `Ok` + clone step (``+0x878 → +0x8c0`, `2168 → 2240``):
Combines `preKey_sigMsg_ok_878_to_8bc_placed_wpX` and `preKey_sigMsg_clone_ok_8bc_to_8c0_placed_wpX`
under `FitsEnv M lim st (TryCloneBytesEnv b)` to establish `SigMsgOkStatePlaced` directly at
`+0x8c0` (`2240`) with `TryCloneBytesEnv b evsC` and `A.pool lim (M.stepEvents evsC st) sf`. -/
theorem preKey_sigMsg_ok_878_to_8c0_placed_wpX [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {H : LibsignalHooks} (hC : PksmCalleesPlaced M A lim H)
    {s0 s : State}
    {sp' sret ptr0 kyberBoxPtr kyberBoxLen ikCap msgCap : BitVec 64}
    {vb : BitVec 8} {regId : BitVec 32}
    {bk : List (BitVec 8)} {pk : PublicKey}
    {ik : List (BitVec 8)} {ipk : PublicKey}
    {b msg : List (BitVec 8)} {innerMsg : SignalMessage}
    {Qp : State → SepProp → Prop}
    (hfit : FitsEnv M lim st (TryCloneBytesEnv b))
    (hsig : SignalMessage.tryFrom protoSignalCodec msg = .ok innerMsg)
    (hlen_lt : b.length < 2 ^ 32)
    (hst : IdentOkStatePlaced s0 sp' sret (BitVec.ofNat 64 b.length) ptr0 kyberBoxPtr kyberBoxLen
      ikCap msgCap vb regId bk pk ik ipk s)
    (hpc : s.pc = (blkPl_111).base + 2168#64)
    (hrun : s.status = .Running) :
    SepWPp (preKeyPlacedProg H) ((blkPl_111).base + 2240#64) s
      (signalMessageResultAt A.repAlloc [] (sp' + 312#64)
          (SignalMessage.tryFrom protoSignalCodec msg) ∗
        memRegion (sp' + 176#64) 112 ∗
        (ptr0 ↦ₛ b) ∗ A.pool lim st s ∗ stackAt sp' (Prost.skipFieldStackX 100))
      (fun sf Pf =>
        ∃ (evsC : List AllocEvent) (msgG : SignalMessageGhost)
          (rk0 rk1 rk2 rk3 addrW0 addrW1 : BitVec 64) (verHi56 : BitVec 56)
          (clonePtr : BitVec 64),
          TryCloneBytesEnv b evsC ∧
          (∀ a : BitVec 64, (a ↦ₛ innerMsg.senderRatchetKey.bytes.toList) =
            (a ↦₆₄ rk0) ∗ ((a + 8#64) ↦₆₄ rk1) ∗ ((a + 16#64) ↦₆₄ rk2) ∗ ((a + 24#64) ↦₆₄ rk3)) ∧
          SigMsgOkStatePlaced s0 sp' sret (BitVec.ofNat 64 b.length) ptr0 kyberBoxPtr kyberBoxLen
            ikCap msgCap vb msgG.pqCap clonePtr bk pk ik ipk sf ∧
          (Pf ⊢ (((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
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
            boxU8Buf A.repAlloc clonePtr b) ∗
            memRegion (sp' + 312#64) 120 ∗
            (ptr0 ↦ₛ b) ∗ A.pool lim (M.stepEvents evsC st) sf ∗
            stackAt sp' (Prost.skipFieldStackX 100)))
      Qp := by
  refine sepWPp_anyQp_of_noPanic ?_
  refine Wire.SepWPp.bind
    (preKey_sigMsg_ok_878_to_8bc_placed_wpX (Qp := preKeyNoPanicQp) hC hfit hsig hlen_lt hst hpc hrun)
    ?_
  rintro sm2 Pm2 hpc2 hrun2
    ⟨evsC, hevsC, hsp2, hal2, hcl2, htr2, hx0_ne, hbk2, hpkeq2, hpkb2, hik2,
      hx1, hx29, hx28, hx26, hx25, hx24, hx23, hx22, hx21, hx20, hx19, hPm2⟩
  refine SepWPp.mono_pre hPm2 ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_pre fun msgG => SepWPp.exists_pre fun rk0 => SepWPp.exists_pre fun rk1 =>
    SepWPp.exists_pre fun rk2 => SepWPp.exists_pre fun rk3 =>
    SepWPp.exists_pre fun addrW0 => SepWPp.exists_pre fun addrW1 =>
    SepWPp.exists_pre fun verHi56 => ?_
  refine SepWPp.pure_pre fun ⟨hx27, hrk⟩ => ?_
  set clonePtr := sm2.readReg64 .x0
  refine SepWPp.mono_pre
    (P' := A.pool lim (M.stepEvents evsC st) sm2 ∗
      (((sp' + 176#64) ↦₆₄ msgG.pqPtr) ∗
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
        boxU8Buf A.repAlloc clonePtr b ∗
        memRegion (sp' + 312#64) 120 ∗
        (ptr0 ↦ₛ b) ∗ stackAt sp' (Prost.skipFieldStackX 100)))
    (by apply entails_of_eq; sep_ac_rfl) ?_
  exact frame_noPanic_pk
    (preKey_sigMsg_clone_ok_8bc_to_8c0_placed_wpX (A := A) (lim := lim)
      (st := M.stepEvents evsC st) (s0 := s0) (clonePtr := clonePtr) (Qp := preKeyNoPanicQp)
      hx0_ne hsp2 hal2 hcl2 htr2 hbk2 hpkeq2 hpkb2 hik2 hpc2 hrun2
      rfl hx1 hx29 hx28 hx27 hx26 hx25 hx24 hx23 hx22 hx21 hx20 hx19)
    fun sf Pf ⟨hok3, hpool3⟩ =>
      ⟨evsC, msgG, rk0, rk1, rk2, rk3, addrW0, addrW1, verHi56, clonePtr, hevsC, hrk, hok3,
        Entails.trans (sepConj_mono_left hpool3) (by apply entails_of_eq; sep_ac_rfl)⟩

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFrom.Wire.SigMsgWPlacedBudget
