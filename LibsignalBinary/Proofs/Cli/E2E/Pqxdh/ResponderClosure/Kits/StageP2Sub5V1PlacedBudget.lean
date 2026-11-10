/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2ErrArmsAPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

/-!
# Budget-Threaded Relocatable Stage P2 Substage P2.5 at SPQR V1

Proves `RustCliAllocBudget M` / `VmPreserved` placed Substage P2.5 (`+0x36ac → +0x125c` / `+0x07bc`
Arm 4 / `+0x125c` Arm 5, including `StageP2MemInv` and `LibsignalFrozen` variants) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit hiding
  IdentitySelfStoreKitPlacedOkI
  kitKpPollPlacedSpecI
  kitKpPollSpec
  kitKpPollSpecE
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf hiding
  kitKpPollSpec
  kitKpPollSpecE
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries hiding isSameAccountDistinctSpec
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding
  promoteMatchingSessionEmptySpec
  promoteStateEmptySpec
  dropProcessPrekeyImplState1Spec
open CryptoVerification.E2E.Pqxdh.ResponderCore hiding
  initializeBobSessionErrOwnedPlacedSpec
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits hiding
  isSameAccountDistinctAtSpec
  p2BobSessV1At
  p2BobSessV1At_intro
  p2_entails_frame_v1
  p2_stageP2bStack_le_bobV1
  p2_isSameAccount_le_bobV1
  p2_isSameAccountExt_le_bobExt
  p2_bobErr4K_le_bobExt
  p2_bind_sepWP_steps_cro_sub5_qpan
  isSameAccountDistinctSpec_to_at_placed
  isSameAccountDistinctSpecExt_to_at_placed
  p2_seg5a_ext_placed_wp
  p2_seg5b_fp_ext_placed_wp
  p2_seg5c1_fp_gen_hooks_placed_wp
  p2_seg5c2_ext_placed_wp
  p2_seg5c3_ext_placed_wp
  p2_seg5d_ext_placed_wp
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  InitializeBobV1OkAtPlaced
  stageP2_sub5_tail_v1_kits_at_placed
  stageP2Sub5TailV1AtPlacedProp
  initializeBobSessionV1StackPlaced
  initializeBobSessionV1StackExtPlaced
  stageP2_sub5_tail_v1_kits_placed
  stageP2_sub5_tail_v1_kits_ext_placed
  stageP2_sub5_tail_v1_kits_4k_placed
  p2_kpPoll_pre_intro_placed
  stageP2_sub5_v1_kits_at_placed
  stageP2Sub5V1AtPlacedProp
  stageP2_sub5_v1_kits_placed
  stageP2_sub5_v1_kits_ext_placed
  stageP2_sub5_v1_kits_4k_placed
  StageP2BaseCalleesPlaced4K
  InitializeBobV1MemInvOkAtPlaced
  InitializeBobV1FrozenOkAtPlaced
  InitializeBobV1FrozenOkPlaced
  InitializeBobV1FrozenOkPlaced4K
  stageP2Sub5V1MemInvAtPlacedProp
  stageP2Sub5V1FrozenAtPlacedProp
  stageP2_sub5_v1_kits_memInv_at_placed
  stageP2_sub5_v1_kits_frozen_placed
  stageP2_sub5_v1_kits_frozen_ext_placed
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget VmPreserved rustDeallocEvents
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitBudget (futDropBudgetSpec)
open LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKitBudget (
  IdentitySelfStoreBudgetEnv kitKpPollSpec kitKpPollSpecE
)
open LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget (
  IdentitySelfStoreKitPlacedOkI kitKpPollPlacedSpecI
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptPlacedABudget (
  AcceptOptFieldsEnv
)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.InitBobErrOwnedPlacedBudget (
  initializeBobSessionErrOwnedFrozenPlacedSpec initializeBobSessionErrOwnedPlacedSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget (
  isSameAccountDistinctAtSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget (
  InitializeBobV1Env
  InitializeBobV1FrozenOkAtPlaced InitializeBobV1FrozenOkAtPlacedOfEnv
  InitializeBobV1FrozenOkPlaced InitializeBobV1FrozenOkPlaced4K
  InitializeBobV1FrozenOkPlaced4KOfEnv InitializeBobV1FrozenOkPlacedOfEnv
  InitializeBobV1MemInvOkAtPlaced InitializeBobV1MemInvOkAtPlacedOfEnv
  InitializeBobV1MemInvOkPlaced InitializeBobV1MemInvOkPlaced4K
  InitializeBobV1MemInvOkPlaced4KOfEnv InitializeBobV1MemInvOkPlacedOfEnv
  InitializeBobV1OkAtPlaced
  InitializeBobV1OkAtPlacedOfEnv
  StageP2BaseCalleesPlaced4K
  StageP2ClosureHooksPlaced
  StageP2PureCalleesPlaced
  StageP2PureCalleesPlaced4K
  StageP2PureCalleesPlaced4KOfEnv
  StageP2PureCalleesPlacedOfEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlacedBudget (
  InitializeBobV1OptFieldsEnv
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5PlacedBudget (
  p2_seg5a_ext_placed_wp
  p2_seg5b_fp_ext_placed_wp
  p2_seg5c1_fp_gen_hooks_placed_wp
  p2_seg5c2_ext_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget (
  initializeBobSessionErrOwned4KPlacedSpec
  initializeBobSessionErrOwnedAtPlacedSpec
  initializeBobSessionErrOwnedFrozen4KPlacedSpec
  initializeBobSessionErrOwnedMemInvAtPlacedSpec
  of_responderCore_errOwned_frozen_placed
  of_stageP2Defs_errOwned4K_frozen_placed
  isSameAccountDistinctSpecExt_to_at_placed
  isSameAccountDistinctSpec_to_at_placed
  of_responderCore_errOwned_placed
  p2BobSessV1At
  p2_bind_sepWP_steps_cro_sub5_qpan
  p2_bind_sepWP_steps_cro_sub5_state
  p2_bobErr4K_le_bobExt
  p2_call_nopanic_rocl_sub5
  p2_isSameAccountExt_le_bobExt
  p2_isSameAccount_le_bobV1
  p2_stageP2bStack_le_bobV1
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.Sub5Placed (
  of_stageP2Defs_errOwned4K_placed
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget (
  initializeBobSessionV1StackExtPlaced
  initializeBobSessionV1StackPlaced
  stageP2_sub5_tail_v1_kits_at_placed_ofEnv
)

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

set_option allowUnsafeReducibility true in
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  protocolAddressAt decryptPrekeySavedRegsAt
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [BitVec.add_assoc]
    | simp only [BitVec.reduceAdd]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

theorem p2_kpPoll_pre_intro_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    {fut out self : BitVec 64} {ist0 : ikit.IdState} {s : State}
    (henv : ikit.envOk s.fs.files)
    (hx0 : s.readReg64 .x0 = fut) (hx8 : s.readReg64 .x8 = out)
    (hfits : FitsEnv M lim st (senv.kpPollEnv ist0)) :
    (skit.kpBoxAt fut self 0#8 ∗ ikit.identityAt self ist0 ∗
      memRegion out 72 ∗ A.pool lim st s ∗ stackAt s.sp skit.kpPollStack) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ⊢
      (kitKpPollPlacedSpecI M A lim skit senv).pre (fut, out, self, ist0, st) s := by
  dsimp only [kitKpPollPlacedSpecI, withLsLogOff, FromRecordCallees.lsLogOff, kitKpPollSpecE,
    withEnvPre, kitKpPollSpec]
  refine sepConj_mono_left ?_
  refine Entails.pure_right henv ?_
  refine Entails.pure_right ⟨hx0, hx8, hfits⟩ ?_
  exact Entails.refl _

/-! ## Substage P2.5 (`+0x36ac -> +0x125c` / Arm 4 `+0x07bc` / Arm 5 `+0x125c`) -/

/-- Envelope-parametric residual statement `Prop` of `stageP2_sub5_v1_kits_at_placed_ofEnv`
parameterized by `bobV1Stk`. -/
abbrev stageP2Sub5V1AtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (inp : AcceptKeysInput) (spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost) (stId : ikit.IdState)
    (s0 s : State) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (opkId : BitVec 32) (b_4f1 b_b98 : BitVec 8)
    (stk : Nat) (F_rest : SepProp),
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp →
    spkBPk.length = 32 →
    opkPkBytes.length = 32 → opkSkBytes.length = 32 →
    (∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 inp.ikBSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) →
    sp - 576#64 ≠ 0#64 →
    bobV1Stk ≤ stk →
    stageP2Sub56Stack skit ≤ stk →
    stk ≤ sp.toNat →
    FitsEnv M lim st (senv.kpPollEnv stId) →
    (∀ kp evsKp drKey, skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp → Model.acceptKeys P inp = some drKey →
      FitsEnv M lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (BobV1Env inp drKey)) →
    (∀ kp evsKp, skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp → Model.acceptKeys P inp = none →
      FitsEnv M lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (AcceptErrEnv inp)) →
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
    s.pc = stageP1EntryPlaced + 0x36ac#64 →
    s.status = .Running →
    s.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    calleeSavedVRegs s = calleeSavedVRegs s0 →
    (∀ s1 : State, s1.trace = s.trace →
      Steps (stageP1ProgPlaced ext) s s1 → ikit.envOk s1.fs.files) →
    s.readReg64 .x0 = idKpFutPtr →
    s.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
    s.readReg64 .x19 = coroPtr →
    s.readReg64 .x21 = coroPtr + 0x390#64 →
    s.readReg64 .x23 = coroPtr + 0x4f2#64 →
    s.readReg64 .x24 = sp + 0x370#64 →
    s.readReg64 .x26 = coroPtr + 0x398#64 →
    s.readReg64 .x27 = ctxPtr →
    s.readReg64 .x28 = sp + 0xa90#64 →
    s.readReg64 .x29 = fp →
    (∀ (kp : IdentityKeyPair) (drKey : DRKey) (evsKp evsBob : List AllocEvent)
        (sf : State) (v_a8' v_b8' v_d0' u_b90' : BitVec 64) (b_b98' : BitVec 8),
      skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp →
      Model.acceptKeys P inp = some drKey →
      BobV1Env inp drKey evsBob →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.kpEvs (.ok kp) →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp (toU8 kp.identityKey.publicKey.bytes.toList)
           spkBPk 0#8 ∗
         p2BobSessV1At A (sp + 0x3e0#64) inp
           (toU8 kp.identityKey.publicKey.bytes.toList) spkBPk drKey
           (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
         cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
         cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsBob) st) sf ∗
         stackAt sp stk ∗ F_rest)
        Q Qp) →
    (∀ (kp : IdentityKeyPair) (evsKp evsErr : List AllocEvent)
        (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State)
        (v_a8' v_b8' v_d0' u_b90' : BitVec 64) (b_b98' : BitVec 8),
      skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp →
      Model.acceptKeys P inp = none →
      AcceptErrEnv inp evsErr →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.kpEvs (.ok kp) →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.pqxdhAcceptErrPayloadAt
           A.repAlloc errTag w2 w3 w4 ∗
         memRegion (sp + 0x418#64) 288 ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp (toU8 kp.identityKey.publicKey.bytes.toList)
           spkBPk 0#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
         cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
         cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗
         A.pool lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr) st) sf ∗
         stackAt sp stk ∗ F_rest)
        Q Qp) →
    (∀ (e : skit.KpErr) (evsKp : List AllocEvent) (s2 : State),
      skit.kpRel stId (.error e) →
      senv.kpPollEnv stId evsKp →
      Steps (stageP1ProgPlaced ext) s s2 →
      s2.pc = stageP1EntryPlaced + 0x7bc#64 →
      s2.status = .Running →
      s2.sp = sp →
      s2.trace = s.trace ++ skit.kpEvs (.error e) →
      s2.readReg64 .x19 = coroPtr →
      s2.readReg64 .x21 = coroPtr + 0x390#64 →
      s2.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s2.readReg64 .x24 = sp + 0x370#64 →
      s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 →
      s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = sp + 0xa90#64 →
      s2.readReg64 .x29 = fp →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
        (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
         memRegion (sp + 0x428#64) 272 ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
         ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
         ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
         ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
         ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
         memRegion (sp + 0x3c8#64) 7 ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents evsKp st) s2 ∗ stackAt sp stk ∗ F_rest)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3e0#64) 344 ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗ F_rest)
      Q Qp

/-- Residual statement `Prop` of `stageP2_sub5_v1_kits_at_placed` (`InitializeBobV1Env F`)
parameterized by `bobV1Stk`. -/
abbrev stageP2Sub5V1AtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5V1AtPlacedOfEnvProp P A lim F (InitializeBobV1Env F) AcceptErrEnv ext skit senv bobV1Stk

set_option maxHeartbeats 1200000 in
/-- Envelope- and Stack-Parameterized Budget-Threaded Placed Substage P2.5
(`+0x36ac -> +0x125c` at SPQR V1):
Polls `IdentityKeyStore::get_identity_key_pair`, drops/frees the future box, checks
`IdentityKey::is_same_account`, and calls `initialize_bob_session` on `stageP1ProgPlaced ext`,
threading `A.pool lim st s`. -/
theorem stageP2_sub5_v1_kits_at_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedAtPlacedSpec P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1OkAtPlacedOfEnv P A lim F BobV1Env ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5V1AtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv bobV1Stk := by
  intro st Qp inp spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s Q
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
    v_a8 v_b8 v_d0 u_b90 opkId b_4f1 b_b98 stk F_rest
    htrusted hreplay hopk_match hwell hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq
    hkp_sk hkp_neq hpqr_ne hstk_bob hstk_sub56 hstk_lt
    hfits_kp hfits_bob_ok hfits_bob_err
    hCode hpc hrun hsp_eq hsp_align hvregs henv_s
    hx0 hx1 hx19 hx21 hx23 hx24 hx26 hx27 hx28 hx29
    hOk hErrBob hErrKp
  subst hsp_eq
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s.sp.isLt)
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.kpFutDrop hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.kpFutSize hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.kpFutAlign hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.kpFutPoll hc.2 hm) ?_
  have hc4f8 : cells (coroPtr + 0x4f8#64) 2 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc4f8) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  have hstep1 := p2_seg5a_ext_placed_wp ext s coroPtr ctxPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) (0#64 + skit.kpPollOff) u_4f8 u_500
    hpc hrun hx0 hx1 hx19 hx27
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1,
    hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_transport lim st s s1 hvm1).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_72_272 s.sp)) (by sep_focus) ?_
  have hstk_poll := p2_stackAt_split_of_le s.sp stk skit.kpPollStack
    (Nat.le_trans (p2_kpPoll_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_nopanic_rocl_sub5
    (x := (idKpFutPtr, s.sp + 0x3e0#64, idStorePtr, stId, st))
    hCode1 (hskitOk.kpPoll (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpPoll_pre_intro_placed skit senv (henv_s s1 htr1 hst01) hx0_1 hx8_1 hfits_kp)
    (by sep_focus)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitKpPollPlacedSpecI, withLsLogOff, FromRecordCallees.lsLogOff, kitKpPollSpecE,
    withEnvPre, kitKpPollSpec]
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2,
    hx28_cs2, hx29_cs2, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evsKp =>
    SepWPp.pure_elim fun ⟨hrel, htr2_1, hevsKp⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ skit.kpEvs ans := by rw [htr2_1, htr1]
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by rw [hvregs2_1, hvregs1, hvregs]
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = coroPtr + 0x390#64 := by rw [hx21_cs2, hx21_1, hx21]
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0x4f2#64 := by rw [hx23_cs2, hx23_1, hx23]
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24]
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = coroPtr + 0x398#64 := by rw [hx26_cs2, hx26_1, hx26]
  have hx27_2 : s2.readReg64 .x27 = ctxPtr := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28]
  have hx29_2 : s2.readReg64 .x29 = fp := by rw [hx29_cs2, hx29_1, hx29]
  cases ans with
  | error e =>
    refine p2_drop_frame_sub5
      (Drop := ((0#64 + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have herr := hErrKp e evsKp s2 hrel hevsKp (hst01.trans hst12) hpc2 hrun2 hsp2 htr2
      hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2 hCode2
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at herr
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok kp =>
    dsimp only [kpPollOutAt]
    have hsp3e1 : (s.sp + 0x3e0#64) + 1#64 = s.sp + 0x3e1#64 := by bv_omega
    have hsp401 : (s.sp + 0x3e0#64) + 0x21#64 = s.sp + 0x401#64 := by bv_omega
    have hsp421 : (s.sp + 0x3e0#64) + 0x41#64 = s.sp + 0x421#64 := by bv_omega
    rw [hsp3e1, hsp401, hsp421, hkp_sk kp hrel]
    refine SepWPp.weaken_frame (Entails.of_eq (sp421_7_272_eq_279 s.sp)) (by sep_focus) ?_
    let ikBPk : SignalPqxdh.Bytes := toU8 kp.identityKey.publicKey.bytes.toList
    have hikBPk_toBv : bytesToBv8 ikBPk = kp.identityKey.publicKey.bytes.toList :=
      bytesToBv8_toU8 _
    have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by
      rw [hikBPk_toBv]; exact kp.identityKey.publicKey.bytes.2
    have hikBPk_len : ikBPk.length = 32 := by
      rw [← bytesToBv8_length]; exact hikBPk_bv
    have hikBSk_bv : (bytesToBv8 inp.ikBSk).length = 32 := by
      rw [bytesToBv8_length]; exact hwell.1
    have hneq_ik : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
        DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes := by
      rw [hikBPk_toBv]; exact hkp_neq kp hrel
    obtain ⟨ik0, ik1, ik2, ik3, hikB0⟩ := exists_words4_of_len32 hikBPk_bv
    obtain ⟨ik4, ik5, ik6, ik7, hikB1⟩ := exists_words4_of_len32 hikBSk_bv
    obtain ⟨opk0, opk1, opk2, opk3, opk4, opk5, opk6, opk7, opk_b64, hopk⟩ :=
      exists_opkSlot65_words (opkPresentTag inp.opkBSk?) hopkPk_len hopkSk_len

    have hkp_words :
        ((s.sp + 0x3e1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 0x401#64) ↦ₛ bytesToBv8 inp.ikBSk) =
        ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ ik0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ ik1) ∗
        ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ ik2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ ik3) ∗
        ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ ik4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ ik5) ∗
        ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ ik6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ ik7) := by
      rw [← hikBPk_toBv, hikB0 (s.sp + 0x3e1#64), hikB1 (s.sp + 0x401#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hkp_sp :
        ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ ik0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ ik1) ∗
        ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ ik2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ ik3) ∗
        ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ ik4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ ik5) ∗
        ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ ik6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ ik7) =
        keyPair64UnalignedAt (s.sp + 0x3e1#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
          (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
          (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_eq_keyPair64UnalignedAt_std3 (s.sp + 0x3e1#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
    refine SepWPp.weaken_frame (Entails.of_eq (hkp_words.trans hkp_sp)) (by sep_focus) ?_
    refine SepWPp.weaken_frame (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (memRegion7_eq_bytes7At (s.sp + 0x3c8#64)))
      (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun s6_b => SepWPp.exists_elim fun s5_b =>
      SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s3_b =>
      SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s1_b =>
      SepWPp.exists_elim fun s0_b => ?_
    have hstep3 := p2_seg5b_fp_ext_placed_wp ext s2 coroPtr msgPtr ctxPtr idKpFutPtr
      (0#64 + skit.kpFutVtOff) (0#64 + skit.kpFutDropOff) fp
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64)
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
      opkId
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
      s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_b98
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      (skit.kpFutDrop_ne_zero rfl) hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2
      (by rw [hsp2]; exact hx24_2) hx26_2 hx27_2 hx29_2
    have hvt0 : (0#64 + skit.kpFutVtOff) + 0x0#64 = 0#64 + skit.kpFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine p2_bind_sepWP_steps_cro_sub5_qpan hCode2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2, hvm3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim (M.stepEvents evsKp st) s2 s3 hvm3_2).symm)
      (by sep_focus) ?_
    refine p2_call_nopanic_rocl_sub5 (x := ()) (P_spec := emp)
      hCode3 (hskitOk.kpFutDrop (by decide)) hpc3 hrun3 hsp3_al hx30_3
      (Entails.refl emp) (by sep_focus)
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr4_3, hvm4_3⟩ => ?_
    rcases hcs4 with ⟨hx19_cs4, hx20_cs4, hx21_cs4, hx22_cs4, hx23_cs4, hx24_cs4, hx25_cs4,
      hx26_cs4, hx27_cs4, hx28_cs4, hx29_cs4, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim (M.stepEvents evsKp st) s3 s4 hvm4_3).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (coro798_64_entails_unaligned_std3 coroPtr) (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun c0_798 => SepWPp.exists_elim fun c1_798 =>
      SepWPp.exists_elim fun c2_798 => SepWPp.exists_elim fun c3_798 =>
      SepWPp.exists_elim fun c4_798 => SepWPp.exists_elim fun c5_798 =>
      SepWPp.exists_elim fun c6_798 =>
      SepWPp.exists_elim fun cw0 => SepWPp.exists_elim fun cw1 =>
      SepWPp.exists_elim fun cw2 => SepWPp.exists_elim fun cw3 =>
      SepWPp.exists_elim fun cw4 => SepWPp.exists_elim fun cw5 =>
      SepWPp.exists_elim fun cw6 => SepWPp.exists_elim fun c63_798 => ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans (p2_allocHook_le_sub56 skit) hstk_sub56) hstk_le64
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg5c1_fp_gen_hooks_placed_wp (st := M.stepEvents evsKp st) ext hH s4
      coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr (0#64 + skit.kpFutVtOff)
      fp (msgPtr + 0x90#64)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      cw0 cw1 cw2 cw3 cw4 cw5 opkId
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
      c0_798 c1_798 c2_798 c3_798 c4_798 c5_798 c6_798
      skit.kpBoxSize hpc4 hrun4 hsp4_align skit.kpBoxSize_ne_zero skit.kpBoxSize_lt
      (hx19_cs4.trans hx19_3) (hx20_cs4.trans hx20_3) (hx21_cs4.trans hx21_3)
      (hx22_cs4.trans hx22_3) (hx23_cs4.trans hx23_3) (hx24_cs4.trans hx24_3)
      (hx27_cs4.trans hx27_3) (hx29_cs4.trans hx29_3)
    rw [hsp4] at hstep5
    refine p2_bind_sepWP_steps_cro_sub5_state hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx3_5, hx8_5, hx9_5, hx10_5, hx11_5,
      hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, hx29_5, hvregs5_4,
      _hlive5⟩
    let st_s5 := M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st
    have hpool5 :
        A.pool lim (M.stepEvents (rustDeallocEvents skit.kpBoxSize 8) (M.stepEvents evsKp st)) s5 =
          A.pool lim st_s5 s5 :=
      congrArg (fun st_ => A.pool lim st_ s5)
        (M.stepEvents_append evsKp (rustDeallocEvents skit.kpBoxSize 8) st).symm
    refine SepWPp.weaken_frame (Entails.of_eq hpool5) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (bytes7At_entails_memRegion7 (s.sp + 0x3c8#64)
        (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
        (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8))
      (by sep_focus) ?_

    have hkp39 : bytes7At (coroPtr + 0x798#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
        ((coroPtr + 0x79f#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7a7#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7af#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7b7#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
        ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
        ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
          bytes7At (coroPtr + 0x7b8#64)
          (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
          (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        keyPair39_eq_words4_bytes7_std3 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4
    refine SepWPp.weaken_frame (Entails.of_eq hkp39) (by sep_focus) ?_
    have hopk_4b0 :
        ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗
        ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) =
        ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
        ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
        ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
        ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
        ((coroPtr + 0x4f0#64) ↦₈ opk_b64) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hopk (coroPtr + 0x4b0#64)
    refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0) (by sep_focus) ?_
    have hc930 : cells (s.sp + 0x930#64) 8 =
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
          ((s.sp + 0x930#64) ↦₆₄ u0) ∗ ((s.sp + 0x938#64) ↦₆₄ u1) ∗
          ((s.sp + 0x940#64) ↦₆₄ u2) ∗ ((s.sp + 0x948#64) ↦₆₄ u3) ∗
          ((s.sp + 0x950#64) ↦₆₄ u4) ∗ ((s.sp + 0x958#64) ↦₆₄ u5) ∗
          ((s.sp + 0x960#64) ↦₆₄ u6) ∗ ((s.sp + 0x968#64) ↦₆₄ u7)) := by
      simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
        sepConj_assoc, sepExists_sepConj_left]
      simp only [sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.weaken_frame (Entails.of_eq hc930) (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_930 => SepWPp.exists_elim fun u_938 =>
      SepWPp.exists_elim fun u_940 => SepWPp.exists_elim fun u_948 =>
      SepWPp.exists_elim fun u_950 => SepWPp.exists_elim fun u_958 =>
      SepWPp.exists_elim fun u_960 => SepWPp.exists_elim fun u_968 => ?_
    have hstep6 := p2_seg5c2_ext_placed_wp ext s5 coroPtr msgPtr
      ik0 ik1 ik2 ik3
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8) cw6
      u_930 u_938 u_940 u_948
      (ik7.extractLsb' 56 8) c63_798 opk_b64
      hpc5 hrun5 hx8_5 hx9_5 hx10_5 hx11_5 hx19_5 (by rw [hsp5, hx23_5])
    rw [hsp5] at hstep6
    refine p2_bind_sepWP_steps_cro_sub5_qpan hCode5 hstep6 (by sep_focus)
      fun s6 hst56 hpc6 hrun6 hCode6 hregs6 => ?_
    rcases hregs6 with ⟨hsp6, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx8_6, hx9_6, hx10_6,
      hx19_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, _, hx28_6, hx29_6, hvregs6_5,
      hvm6_5⟩
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim st_s5 s5 s6 hvm6_5).symm)
      (by sep_focus) ?_
    have hkp32hi : bytes7At (coroPtr + 0x7b8#64)
          (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
          (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
        ((coroPtr + 0x7bf#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7c7#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7cf#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7d7#64) ↦₈ (ik7.extractLsb' 56 8)) =
        ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
        ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        keyPair32Hi_eq_words4_std3 (coroPtr + 0x7b8#64) ik4 ik5 ik6 ik7
    refine SepWPp.weaken_frame (Entails.of_eq hkp32hi) (by sep_focus) ?_
    have hsp3e0_unfold : ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗ keyPair64UnalignedAt (s.sp + 0x3e1#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
          (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
          (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8) ⊢
        memRegion (s.sp + 0x3e0#64) 65 := by
      rw [← hkp_sp]
      exact pointsTo8_words8_entails_memRegion65 (s.sp + 0x3e0#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 0#8
    refine SepWPp.weaken_frame hsp3e0_unfold (by sep_focus) ?_
    have hc4f8_fold :
        ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ⊢
        cells (coroPtr + 0x4f8#64) 2 := by
      rw [hc4f8]
      exact Entails.sepExists_right idKpFutPtr
        (Entails.sepExists_right (0#64 + skit.kpFutVtOff) (Entails.refl _))
    refine SepWPp.weaken_frame hc4f8_fold (by sep_focus) ?_
    refine p2_drop_frame_sub5
      (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
        ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
        ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have hst06 : Steps (stageP1ProgPlaced ext) s s6 :=
      hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans hst56))))
    have htr6 : s6.trace = s.trace ++ skit.kpEvs (.ok kp) := by
      rw [htr6_5, htr5_4, htr4_3, htr3_2, htr2]
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2]
    have hx25_6' : s6.readReg64 .x25 = s.readReg64 .x25 := by
      rw [hx25_6, hx25_5, hx25_cs4, hx25_3, hx25_2]
    have hx26_6' : s6.readReg64 .x26 = coroPtr + 0x398#64 := by
      rw [hx26_6, hx26_5, hx26_cs4, hx26_3]
    have hx28_6' : s6.readReg64 .x28 = s.sp + 0xa90#64 := by
      rw [hx28_6, hx28_5, hx28_cs4, hx28_3, hx28_2]

    have htail := stageP2_sub5_tail_v1_kits_at_placed_ofEnv (st := st_s5) (Qp := Qp)
      ext hSameAcct hInitBobErrOwned hInitBobV1
      hsame_le herr_le inp ikBPk spkBPk
      opkPkBytes opkSkBytes gMe gPeer s0 s6 Q s.sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
      ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 u_950 u_958 u_960 u_968
      opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 opkId opk_b64 b_4f1 stk
      (ikit.identityAt idStorePtr stId ∗ cells (coroPtr + 0x4f8#64) 2 ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
       ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((s.sp + 0xb8#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) ∗
       memRegion (s.sp + 0x3c8#64) 7 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
       ((fp + 0xffffffffffffff88#64) ↦₈ (ik7.extractLsb' 56 8)) ∗ F_rest)
      htrusted hreplay hopk_match hwell hikBPk_len hspkBPk_len hopkSk_eq hneq_ik
      (fun a => by simpa only [BitVec.add_zero] using hikB0 a)
      (fun a => by simpa only [BitVec.add_zero] using hikB1 a)
      (fun a => by simpa only [BitVec.add_zero] using hopk a) hpqr_ne hstk_bob hstk_lt
      (fun drKey hacc => hfits_bob_ok kp evsKp drKey hrel hevsKp hacc)
      (fun hnone => hfits_bob_err kp evsKp hrel hevsKp hnone)
      hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
      (hx0_6.trans hx0_5) (hx1_6.trans hx1_5) hx2_6 (hx3_6.trans hx3_5)
      hx8_6 hx9_6 hx10_6 hx19_6 (hx21_6.trans hx21_5) (hx22_6.trans hx22_5)
      hx23_6 (hx24_6.trans hx24_5) hx28_6'
      (hx29_6.trans hx29_5)
      (fun drKey evsBob sf hacc hevsBob hst6f hpcf hrunf hspf htrf hx19f hx21f hx22f hx23f
        hx24f hx25f hx26f hx28f hx29f hvregsf hCodef => by
        have hok := hOk kp drKey evsKp evsBob sf
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8)
          hrel hevsKp hacc hevsBob (hst06.trans hst6f) hpcf hrunf hspf (htrf.trans htr6)
          hx19f hx21f hx22f hx23f hx24f (hx25f.trans hx25_6') (hx26f.trans hx26_6')
          hx28f hx29f hvregsf hCodef
        dsimp only [st_s5]
        rw [← M.stepEvents_append (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) evsBob st]
        exact p2_sepWPp_weaken_eq hok (by sep_focus))
      (fun evsErr errTag w2_e w3_e w4_e w5_e w6_e sf hnone hevsErr hne2 hne3 hst6f hpcf hrunf
        hspf htrf hx19f hx21f hx22f hx23f hx24f hx25f hx26f hx28f hx29f hvregsf hCodef => by
        have herr := hErrBob kp evsKp evsErr errTag w2_e w3_e w4_e w5_e w6_e sf
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8)
          hrel hevsKp hnone hevsErr hne2 hne3 (hst06.trans hst6f) hpcf hrunf hspf (htrf.trans htr6)
          hx19f hx21f hx22f hx23f hx24f (hx25f.trans hx25_6') (hx26f.trans hx26_6')
          hx28f hx29f hvregsf hCodef
        dsimp only [st_s5]
        rw [← M.stepEvents_append (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) evsErr st]
        exact p2_sepWPp_weaken_eq herr (by sep_focus))
    exact p2_sepWPp_weaken_eq htail (by sep_focus)

abbrev stageP2_sub5_v1_kits_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop} :=
  @stageP2_sub5_v1_kits_at_placed_ofEnv _ M P A lim F (InitializeBobV1Env F) AcceptErrEnv

/-- Placed Kit-Parameterized Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, `StageP2PureCalleesPlacedOfEnv`). -/
theorem stageP2_sub5_v1_kits_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlacedOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackPlaced :=
  stageP2_sub5_v1_kits_at_placed_ofEnv ext skit senv hH hskitOk hskitVt
    (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    (of_responderCore_errOwned_placed hInitBobErrOwned)
    hPure.initializeBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1

/-- Placed Kit-Parameterized Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, `StageP2PureCalleesPlaced`). -/
theorem stageP2_sub5_v1_kits_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced P A lim F AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedPlacedSpec P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackPlaced :=
  stageP2_sub5_v1_kits_placed_ofEnv ext skit senv hH hskitOk hskitVt hPure hInitBobErrOwned

/-- Placed Kit-Parameterized Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, `StageP2PureCalleesPlaced4KOfEnv`). -/
theorem stageP2_sub5_v1_kits_ext_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_at_placed_ofEnv ext skit senv hH hskitOk hskitVt
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    hInitBobErrOwned hPure.initializeBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt

/-- Placed Kit-Parameterized Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, 4K/`Ext` `StageP2PureCalleesPlaced4K`). -/
theorem stageP2_sub5_v1_kits_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwned4KPlacedSpec P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_ext_placed_ofEnv ext skit senv hH hskitOk hskitVt hPure hInitBobErrOwned

abbrev stageP2_sub5_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_sub5_v1_kits_ext_placed

theorem stageP2_sub5_v1_kits_ext_defs_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4KOfEnv P A lim F BobV1Env AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KPlacedSpec
          P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_ext_placed_ofEnv ext skit senv hH hskitOk hskitVt hPure
    (of_stageP2Defs_errOwned4K_placed hInitBobErrOwned)

theorem stageP2_sub5_v1_kits_ext_defs_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced4K P A lim F AcceptErrEnv ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwned4KPlacedSpec
          P A lim AcceptErrEnv)) :
    stageP2Sub5V1AtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_ext_defs_placed_ofEnv ext skit senv hH hskitOk hskitVt hPure hInitBobErrOwned

/-! ## `StageP2MemInv` / `LibsignalFrozen` Generalizations (`stageP2_sub5_v1_kits_memInv_*` / `_frozen_*`) -/

/-- Memory-invariant-parametric residual statement `Prop` of `stageP2_sub5_v1_kits_memInv_at_placed_ofEnv`
parameterized by `Φ : Memory → Prop`, `BobV1Env`, `AcceptErrEnv`, and `bobV1Stk`. -/
abbrev stageP2Sub5V1MemInvAtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop)
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  ∀ {st : M.σ} {Qp : State → SepProp → Prop}
    (inp : AcceptKeysInput) (spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost) (stId : ikit.IdState)
    (s0 s : State) (Q : State → SepProp → Prop)
    (sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     v_a8 v_b8 v_d0 u_b90 : BitVec 64)
    (opkId : BitVec 32) (b_4f1 b_b98 : BitVec 8)
    (stk : Nat) (F_rest : SepProp),
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp →
    spkBPk.length = 32 →
    opkPkBytes.length = 32 → opkSkBytes.length = 32 →
    (∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.privateKey.bytes.toList = bytesToBv8 inp.ikBSk) →
    (∀ kp : IdentityKeyPair, skit.kpRel stId (.ok kp) →
      kp.identityKey.publicKey.bytes.toList ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) →
    sp - 576#64 ≠ 0#64 →
    bobV1Stk ≤ stk →
    stageP2Sub56Stack skit ≤ stk →
    stk ≤ sp.toNat →
    FitsEnv M lim st (senv.kpPollEnv stId) →
    (∀ kp evsKp drKey, skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp → Model.acceptKeys P inp = some drKey →
      FitsEnv M lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (BobV1Env inp drKey)) →
    (∀ kp evsKp, skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp → Model.acceptKeys P inp = none →
      FitsEnv M lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st)
        (AcceptErrEnv inp)) →
    Φ s.mem →
    s.pc = stageP1EntryPlaced + 0x36ac#64 →
    s.status = .Running →
    s.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    calleeSavedVRegs s = calleeSavedVRegs s0 →
    (∀ s1 : State, s1.trace = s.trace →
      Steps (stageP1ProgPlaced ext) s s1 → ikit.envOk s1.fs.files) →
    s.readReg64 .x0 = idKpFutPtr →
    s.readReg64 .x1 = 0#64 + skit.kpFutVtOff →
    s.readReg64 .x19 = coroPtr →
    s.readReg64 .x21 = coroPtr + 0x390#64 →
    s.readReg64 .x23 = coroPtr + 0x4f2#64 →
    s.readReg64 .x24 = sp + 0x370#64 →
    s.readReg64 .x26 = coroPtr + 0x398#64 →
    s.readReg64 .x27 = ctxPtr →
    s.readReg64 .x28 = sp + 0xa90#64 →
    s.readReg64 .x29 = fp →
    (∀ (kp : IdentityKeyPair) (drKey : DRKey) (evsKp evsBob : List AllocEvent)
        (sf : State) (v_a8' v_b8' v_d0' u_b90' : BitVec 64) (b_b98' : BitVec 8),
      skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp →
      Model.acceptKeys P inp = some drKey →
      BobV1Env inp drKey evsBob →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.kpEvs (.ok kp) →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp (toU8 kp.identityKey.publicKey.bytes.toList)
           spkBPk 0#8 ∗
         p2BobSessV1At A (sp + 0x3e0#64) inp
           (toU8 kp.identityKey.publicKey.bytes.toList) spkBPk drKey
           (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
         cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
         cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsBob) st) sf ∗
         stackAt sp stk ∗ F_rest)
        Q Qp) →
    (∀ (kp : IdentityKeyPair) (evsKp evsErr : List AllocEvent)
        (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State)
        (v_a8' v_b8' v_d0' u_b90' : BitVec 64) (b_b98' : BitVec 8),
      skit.kpRel stId (.ok kp) →
      senv.kpPollEnv stId evsKp →
      Model.acceptKeys P inp = none →
      AcceptErrEnv inp evsErr →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.kpEvs (.ok kp) →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = coroPtr + 0x398#64 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.pqxdhAcceptErrPayloadAt
           A.repAlloc errTag w2 w3 w4 ∗
         memRegion (sp + 0x418#64) 288 ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp (toU8 kp.identityKey.publicKey.bytes.toList)
           spkBPk 0#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         cells (coroPtr + 0x4f8#64) 2 ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8') ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8') ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0') ∗
         memRegion (sp + 0x3c8#64) 7 ∗ cells (sp + 0x560#64) 4 ∗
         cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗ cells (sp + 0x930#64) 8 ∗
         cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90') ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98') ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗
         A.pool lim (M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8 ++ evsErr) st) sf ∗
         stackAt sp stk ∗ F_rest)
        Q Qp) →
    (∀ (e : skit.KpErr) (evsKp : List AllocEvent) (s2 : State),
      skit.kpRel stId (.error e) →
      senv.kpPollEnv stId evsKp →
      Steps (stageP1ProgPlaced ext) s s2 →
      s2.pc = stageP1EntryPlaced + 0x7bc#64 →
      s2.status = .Running →
      s2.sp = sp →
      s2.trace = s.trace ++ skit.kpEvs (.error e) →
      s2.readReg64 .x19 = coroPtr →
      s2.readReg64 .x21 = coroPtr + 0x390#64 →
      s2.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s2.readReg64 .x24 = sp + 0x370#64 →
      s2.readReg64 .x25 = s.readReg64 .x25 →
      s2.readReg64 .x26 = coroPtr + 0x398#64 →
      s2.readReg64 .x27 = ctxPtr →
      s2.readReg64 .x28 = sp + 0xa90#64 →
      s2.readReg64 .x29 = fp →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s2
        (kpPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
         memRegion (sp + 0x428#64) 272 ∗
         A.live idKpFutPtr skit.kpBoxSize 8 ∗
         skit.kpBoxAt idKpFutPtr idStorePtr 1#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ∗
         ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
         ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
         ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
         ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         protocolAddressAt A.repAlloc gMe localAddrPtr ∗
         protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
         memRegion (sp + 0x3c8#64) 7 ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         A.pool lim (M.stepEvents evsKp st) s2 ∗ stackAt sp stk ∗ F_rest)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (A.live idKpFutPtr skit.kpBoxSize 8 ∗
       skit.kpBoxAt idKpFutPtr idStorePtr 0#8 ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
       ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ memRegion (coroPtr + 0x798#64) 64 ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
       ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗
       ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A.repAlloc gMe localAddrPtr ∗
       protocolAddressAt A.repAlloc gPeer remoteAddrPtr ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ v_a8) ∗ ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
       ((sp + 0xb8#64) ↦₆₄ v_b8) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       memRegion (sp + 0x3c8#64) 7 ∗ memRegion (sp + 0x3e0#64) 344 ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
       ((fp + 0xffffffffffffff80#64) ↦₆₄ u_b90) ∗ ((fp + 0xffffffffffffff88#64) ↦₈ b_b98) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ stackAt sp stk ∗ F_rest)
      Q Qp

/-- Default (`InitializeBobV1Env F`) `Φ`-guarded residual statement `Prop` of Substage P2.5. -/
abbrev stageP2Sub5V1MemInvAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (Φ : Memory → Prop) (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5V1MemInvAtPlacedOfEnvProp Φ P A lim F (InitializeBobV1Env F) AcceptErrEnv
    ext skit senv bobV1Stk

/-- `LibsignalFrozen`-guarded envelope-parametric residual statement `Prop` of Substage P2.5. -/
abbrev stageP2Sub5V1FrozenAtPlacedOfEnvProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5V1MemInvAtPlacedOfEnvProp (LibsignalFrozen lsmpl) P A lim F BobV1Env AcceptErrEnv
    ext skit senv bobV1Stk

/-- `LibsignalFrozen`-guarded default (`InitializeBobV1Env F`) residual statement `Prop` of Substage P2.5. -/
abbrev stageP2Sub5V1FrozenAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F (InitializeBobV1Env F) AcceptErrEnv
    ext skit senv bobV1Stk

/-- `LibsignalFrozen`-guarded `InitializeBobV1OptFieldsEnv P F` residual statement `Prop` of Substage P2.5. -/
abbrev stageP2Sub5V1FrozenOptFieldsAtPlacedProp [LibsignalPlacement] {M : AllocCostModel}
    (P : Primitives) (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F
    (InitializeBobV1OptFieldsEnv P F) (AcceptOptFieldsEnv P) ext skit senv bobV1Stk

set_option maxHeartbeats 1200000 in
/-- `StageP2MemInv Φ`-Parameterized Budget-Threaded Placed Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1). -/
theorem stageP2_sub5_v1_kits_memInv_at_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1MemInvOkAtPlacedOfEnv Φ P A lim F BobV1Env ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5V1MemInvAtPlacedOfEnvProp Φ P A lim F BobV1Env AcceptErrEnv ext skit senv bobV1Stk := by
  intro st Qp inp spkBPk opkPkBytes opkSkBytes gMe gPeer stId s0 s Q
    sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idKpFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
    v_a8 v_b8 v_d0 u_b90 opkId b_4f1 b_b98 stk F_rest
    htrusted hreplay hopk_match hwell hspkBPk_len hopkPk_len hopkSk_len hopkSk_eq
    hkp_sk hkp_neq hpqr_ne hstk_bob hstk_sub56 hstk_lt
    hfits_kp hfits_bob_ok hfits_bob_err
    hCode hpc hrun hsp_eq hsp_align hvregs henv_s
    hx0 hx1 hx19 hx21 hx23 hx24 hx26 hx27 hx28 hx29
    hOk hErrBob hErrKp
  subst hsp_eq
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s.sp.isLt)
  refine p2_sepWPp_intro_ro_placed (hInv.toCodeRo hCode) (fun hc hm => hskitVt.kpFutDrop hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed (hInv.toCodeRo hCode) (fun hc hm => hskitVt.kpFutSize hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed (hInv.toCodeRo hCode) (fun hc hm => hskitVt.kpFutAlign hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed (hInv.toCodeRo hCode) (fun hc hm => hskitVt.kpFutPoll hc.2 hm) ?_
  have hc4f8 : cells (coroPtr + 0x4f8#64) 2 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x4f8#64) ↦₆₄ u0) ∗ ((coroPtr + 0x500#64) ↦₆₄ u1)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc4f8) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  have hstep1 := p2_seg5a_ext_placed_wp ext s coroPtr ctxPtr idKpFutPtr
    (0#64 + skit.kpFutVtOff) (0#64 + skit.kpPollOff) u_4f8 u_500
    hpc hrun hx0 hx1 hx19 hx27
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_bind_sepWP_steps_memInv_sub5_qpan
    hInv hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, _, hx8_1, hx19_1, hx21_1, hx23_1, hx24_1, hx25_1,
    hx26_1, hx27_1, hx28_1, hx29_1, hx30_1, hvregs1, hvm1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine SepWPp.weaken_frame
    (Entails.of_eq (A.pool_transport lim st s s1 hvm1).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_72_272 s.sp)) (by sep_focus) ?_
  have hstk_poll := p2_stackAt_split_of_le s.sp stk skit.kpPollStack
    (Nat.le_trans (p2_kpPoll_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_call_nopanic_rocl_memInv_sub5
    hInv (x := (idKpFutPtr, s.sp + 0x3e0#64, idStorePtr, stId, st))
    hCode1 (hskitOk.kpPoll (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_kpPoll_pre_intro_placed skit senv (henv_s s1 htr1 hst01) hx0_1 hx8_1 hfits_kp)
    (by sep_focus)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [kitKpPollPlacedSpecI, withLsLogOff, FromRecordCallees.lsLogOff, kitKpPollSpecE,
    withEnvPre, kitKpPollSpec]
  rcases hcs2 with ⟨hx19_cs2, _, hx21_cs2, _, hx23_cs2, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2,
    hx28_cs2, hx29_cs2, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.exists_elim fun evsKp =>
    SepWPp.pure_elim fun ⟨hrel, htr2_1, hevsKp⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have htr2 : s2.trace = s.trace ++ skit.kpEvs ans := by rw [htr2_1, htr1]
  have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by rw [hvregs2_1, hvregs1, hvregs]
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx21_2 : s2.readReg64 .x21 = coroPtr + 0x390#64 := by rw [hx21_cs2, hx21_1, hx21]
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0x4f2#64 := by rw [hx23_cs2, hx23_1, hx23]
  have hx24_2 : s2.readReg64 .x24 = s.sp + 0x370#64 := by rw [hx24_cs2, hx24_1, hx24]
  have hx25_2 : s2.readReg64 .x25 = s.readReg64 .x25 := hx25_cs2.trans hx25_1
  have hx26_2 : s2.readReg64 .x26 = coroPtr + 0x398#64 := by rw [hx26_cs2, hx26_1, hx26]
  have hx27_2 : s2.readReg64 .x27 = ctxPtr := hx27_cs2.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.sp + 0xa90#64 := by rw [hx28_cs2, hx28_1, hx28]
  have hx29_2 : s2.readReg64 .x29 = fp := by rw [hx29_cs2, hx29_1, hx29]
  cases ans with
  | error e =>
    refine p2_drop_frame_sub5
      (Drop := ((0#64 + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have herr := hErrKp e evsKp s2 hrel hevsKp (hst01.trans hst12) hpc2 hrun2 hsp2 htr2
      hx19_2 hx21_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs2
      (hInv.toCodeRo hCode2)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at herr
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok kp =>
    dsimp only [kpPollOutAt]
    have hsp3e1 : (s.sp + 0x3e0#64) + 1#64 = s.sp + 0x3e1#64 := by bv_omega
    have hsp401 : (s.sp + 0x3e0#64) + 0x21#64 = s.sp + 0x401#64 := by bv_omega
    have hsp421 : (s.sp + 0x3e0#64) + 0x41#64 = s.sp + 0x421#64 := by bv_omega
    rw [hsp3e1, hsp401, hsp421, hkp_sk kp hrel]
    refine SepWPp.weaken_frame (Entails.of_eq (sp421_7_272_eq_279 s.sp)) (by sep_focus) ?_
    let ikBPk : SignalPqxdh.Bytes := toU8 kp.identityKey.publicKey.bytes.toList
    have hikBPk_toBv : bytesToBv8 ikBPk = kp.identityKey.publicKey.bytes.toList :=
      bytesToBv8_toU8 _
    have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by
      rw [hikBPk_toBv]; exact kp.identityKey.publicKey.bytes.2
    have hikBPk_len : ikBPk.length = 32 := by
      rw [← bytesToBv8_length]; exact hikBPk_bv
    have hikBSk_bv : (bytesToBv8 inp.ikBSk).length = 32 := by
      rw [bytesToBv8_length]; exact hwell.1
    have hneq_ik : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
        DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes := by
      rw [hikBPk_toBv]; exact hkp_neq kp hrel
    obtain ⟨ik0, ik1, ik2, ik3, hikB0⟩ := exists_words4_of_len32 hikBPk_bv
    obtain ⟨ik4, ik5, ik6, ik7, hikB1⟩ := exists_words4_of_len32 hikBSk_bv
    obtain ⟨opk0, opk1, opk2, opk3, opk4, opk5, opk6, opk7, opk_b64, hopk⟩ :=
      exists_opkSlot65_words (opkPresentTag inp.opkBSk?) hopkPk_len hopkSk_len

    have hkp_words :
        ((s.sp + 0x3e1#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
          ((s.sp + 0x401#64) ↦ₛ bytesToBv8 inp.ikBSk) =
        ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ ik0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ ik1) ∗
        ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ ik2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ ik3) ∗
        ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ ik4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ ik5) ∗
        ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ ik6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ ik7) := by
      rw [← hikBPk_toBv, hikB0 (s.sp + 0x3e1#64), hikB1 (s.sp + 0x401#64)]
      simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    have hkp_sp :
        ((s.sp + 0x3e0#64 + 0x01#64) ↦₆₄ ik0) ∗ ((s.sp + 0x3e0#64 + 0x09#64) ↦₆₄ ik1) ∗
        ((s.sp + 0x3e0#64 + 0x11#64) ↦₆₄ ik2) ∗ ((s.sp + 0x3e0#64 + 0x19#64) ↦₆₄ ik3) ∗
        ((s.sp + 0x3e0#64 + 0x21#64) ↦₆₄ ik4) ∗ ((s.sp + 0x3e0#64 + 0x29#64) ↦₆₄ ik5) ∗
        ((s.sp + 0x3e0#64 + 0x31#64) ↦₆₄ ik6) ∗ ((s.sp + 0x3e0#64 + 0x39#64) ↦₆₄ ik7) =
        keyPair64UnalignedAt (s.sp + 0x3e1#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
          (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
          (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_eq_keyPair64UnalignedAt_std3 (s.sp + 0x3e1#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
    refine SepWPp.weaken_frame (Entails.of_eq (hkp_words.trans hkp_sp)) (by sep_focus) ?_
    refine SepWPp.weaken_frame (skit.kpBoxAt_memRegion idKpFutPtr idStorePtr 1#8) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (memRegion7_eq_bytes7At (s.sp + 0x3c8#64)))
      (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun s6_b => SepWPp.exists_elim fun s5_b =>
      SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s3_b =>
      SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s1_b =>
      SepWPp.exists_elim fun s0_b => ?_
    have hstep3 := p2_seg5b_fp_ext_placed_wp ext s2 coroPtr msgPtr ctxPtr idKpFutPtr
      (0#64 + skit.kpFutVtOff) (0#64 + skit.kpFutDropOff) fp
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64)
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_a8 (coroPtr + 0x390#64) v_b8 ctxPtr v_d0 u_b90
      opkId
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
      s0_b s1_b s2_b s3_b s4_b s5_b s6_b b_b98
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      (skit.kpFutDrop_ne_zero rfl) hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2
      (by rw [hsp2]; exact hx24_2) hx26_2 hx27_2 hx29_2
    have hvt0 : (0#64 + skit.kpFutVtOff) + 0x0#64 = 0#64 + skit.kpFutVtOff :=
      BitVec.add_zero _
    rw [hsp2, hvt0] at hstep3
    refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_bind_sepWP_steps_memInv_sub5_qpan
      hInv hCode2 hstep3 (by sep_focus)
      fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
    rcases hregs3 with ⟨hsp3, htr3_2, _, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3,
      hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2, hvm3_2⟩
    have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim (M.stepEvents evsKp st) s2 s3 hvm3_2).symm)
      (by sep_focus) ?_
    refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_call_nopanic_rocl_memInv_sub5
      hInv (x := ()) (P_spec := emp)
      hCode3 (hskitOk.kpFutDrop (by decide)) hpc3 hrun3 hsp3_al hx30_3
      (Entails.refl emp) (by sep_focus)
      (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
    dsimp only [futDropBudgetSpec]
    refine SepWPp.pure_elim fun ⟨htr4_3, hvm4_3⟩ => ?_
    rcases hcs4 with ⟨hx19_cs4, hx20_cs4, hx21_cs4, hx22_cs4, hx23_cs4, hx24_cs4, hx25_cs4,
      hx26_cs4, hx27_cs4, hx28_cs4, hx29_cs4, hvregs4_3⟩
    have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
    have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim (M.stepEvents evsKp st) s3 s4 hvm4_3).symm)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (coro798_64_entails_unaligned_std3 coroPtr) (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun c0_798 => SepWPp.exists_elim fun c1_798 =>
      SepWPp.exists_elim fun c2_798 => SepWPp.exists_elim fun c3_798 =>
      SepWPp.exists_elim fun c4_798 => SepWPp.exists_elim fun c5_798 =>
      SepWPp.exists_elim fun c6_798 =>
      SepWPp.exists_elim fun cw0 => SepWPp.exists_elim fun cw1 =>
      SepWPp.exists_elim fun cw2 => SepWPp.exists_elim fun cw3 =>
      SepWPp.exists_elim fun cw4 => SepWPp.exists_elim fun cw5 =>
      SepWPp.exists_elim fun cw6 => SepWPp.exists_elim fun c63_798 => ?_
    have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
      (Nat.le_trans (p2_allocHook_le_sub56 skit) hstk_sub56) hstk_le64
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
    have hstep5 := p2_seg5c1_fp_gen_hooks_placed_wp (st := M.stepEvents evsKp st) ext hH s4
      coroPtr msgPtr remoteAddrPtr localAddrPtr idKpFutPtr (0#64 + skit.kpFutVtOff)
      fp (msgPtr + 0x90#64)
      (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8) (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
      (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8) (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
      (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8) (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
      cw0 cw1 cw2 cw3 cw4 cw5 opkId
      (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
      (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) (ik7.extractLsb' 56 8)
      c0_798 c1_798 c2_798 c3_798 c4_798 c5_798 c6_798
      skit.kpBoxSize hpc4 hrun4 hsp4_align skit.kpBoxSize_ne_zero skit.kpBoxSize_lt
      (hx19_cs4.trans hx19_3) (hx20_cs4.trans hx20_3) (hx21_cs4.trans hx21_3)
      (hx22_cs4.trans hx22_3) (hx23_cs4.trans hx23_3) (hx24_cs4.trans hx24_3)
      (hx27_cs4.trans hx27_3) (hx29_cs4.trans hx29_3)
    rw [hsp4] at hstep5
    refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_bind_sepWP_steps_memInv_sub5_state
      hInv hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, hx0_5, hx1_5, hx3_5, hx8_5, hx9_5, hx10_5, hx11_5,
      hx19_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, _, hx28_5, hx29_5, hvregs5_4,
      _hlive5⟩
    let st_s5 := M.stepEvents (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) st
    have hpool5 :
        A.pool lim (M.stepEvents (rustDeallocEvents skit.kpBoxSize 8) (M.stepEvents evsKp st)) s5 =
          A.pool lim st_s5 s5 :=
      congrArg (fun st_ => A.pool lim st_ s5)
        (M.stepEvents_append evsKp (rustDeallocEvents skit.kpBoxSize 8) st).symm
    refine SepWPp.weaken_frame (Entails.of_eq hpool5) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (bytes7At_entails_memRegion7 (s.sp + 0x3c8#64)
        (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
        (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8))
      (by sep_focus) ?_

    have hkp39 : bytes7At (coroPtr + 0x798#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8) ∗
        ((coroPtr + 0x79f#64) ↦₆₄ (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7a7#64) ↦₆₄ (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7af#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7b7#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) =
        ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
        ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
          bytes7At (coroPtr + 0x7b8#64)
          (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
          (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        keyPair39_eq_words4_bytes7_std3 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4
    refine SepWPp.weaken_frame (Entails.of_eq hkp39) (by sep_focus) ?_
    have hopk_4b0 :
        ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗
        ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) =
        ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
        ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
        ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
        ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
        ((coroPtr + 0x4f0#64) ↦₈ opk_b64) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hopk (coroPtr + 0x4b0#64)
    refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0) (by sep_focus) ?_
    have hc930 : cells (s.sp + 0x930#64) 8 =
        (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
         ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
          ((s.sp + 0x930#64) ↦₆₄ u0) ∗ ((s.sp + 0x938#64) ↦₆₄ u1) ∗
          ((s.sp + 0x940#64) ↦₆₄ u2) ∗ ((s.sp + 0x948#64) ↦₆₄ u3) ∗
          ((s.sp + 0x950#64) ↦₆₄ u4) ∗ ((s.sp + 0x958#64) ↦₆₄ u5) ∗
          ((s.sp + 0x960#64) ↦₆₄ u6) ∗ ((s.sp + 0x968#64) ↦₆₄ u7)) := by
      simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
        sepConj_assoc, sepExists_sepConj_left]
      simp only [sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.weaken_frame (Entails.of_eq hc930) (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_930 => SepWPp.exists_elim fun u_938 =>
      SepWPp.exists_elim fun u_940 => SepWPp.exists_elim fun u_948 =>
      SepWPp.exists_elim fun u_950 => SepWPp.exists_elim fun u_958 =>
      SepWPp.exists_elim fun u_960 => SepWPp.exists_elim fun u_968 => ?_
    have hstep6 := p2_seg5c2_ext_placed_wp ext s5 coroPtr msgPtr
      ik0 ik1 ik2 ik3
      (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8) cw6
      u_930 u_938 u_940 u_948
      (ik7.extractLsb' 56 8) c63_798 opk_b64
      hpc5 hrun5 hx8_5 hx9_5 hx10_5 hx11_5 hx19_5 (by rw [hsp5, hx23_5])
    rw [hsp5] at hstep6
    refine LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlacedBudget.p2_bind_sepWP_steps_memInv_sub5_qpan
      hInv hCode5 hstep6 (by sep_focus)
      fun s6 hst56 hpc6 hrun6 hCode6 hregs6 => ?_
    rcases hregs6 with ⟨hsp6, htr6_5, hx0_6, hx1_6, hx2_6, hx3_6, hx8_6, hx9_6, hx10_6,
      hx19_6, hx21_6, hx22_6, hx23_6, hx24_6, hx25_6, hx26_6, _, hx28_6, hx29_6, hvregs6_5,
      hvm6_5⟩
    refine SepWPp.weaken_frame
      (Entails.of_eq (A.pool_transport lim st_s5 s5 s6 hvm6_5).symm)
      (by sep_focus) ?_
    have hkp32hi : bytes7At (coroPtr + 0x7b8#64)
          (ik4.extractLsb' 0 8) (ik4.extractLsb' 8 8) (ik4.extractLsb' 16 8) (ik4.extractLsb' 24 8)
          (ik4.extractLsb' 32 8) (ik4.extractLsb' 40 8) (ik4.extractLsb' 48 8) ∗
        ((coroPtr + 0x7bf#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7c7#64) ↦₆₄ (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7cf#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
        ((coroPtr + 0x7d7#64) ↦₈ (ik7.extractLsb' 56 8)) =
        ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
        ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) := by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        keyPair32Hi_eq_words4_std3 (coroPtr + 0x7b8#64) ik4 ik5 ik6 ik7
    refine SepWPp.weaken_frame (Entails.of_eq hkp32hi) (by sep_focus) ?_
    have hsp3e0_unfold : ((s.sp + 0x3e0#64) ↦₈ 0#8) ∗ keyPair64UnalignedAt (s.sp + 0x3e1#64)
          (ik0.extractLsb' 0 8) (ik0.extractLsb' 8 8) (ik0.extractLsb' 16 8) (ik0.extractLsb' 24 8)
          (ik0.extractLsb' 32 8) (ik0.extractLsb' 40 8) (ik0.extractLsb' 48 8)
          (ik1.extractLsb' 0 56 ++ ik0.extractLsb' 56 8)
          (ik2.extractLsb' 0 56 ++ ik1.extractLsb' 56 8)
          (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
          (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
          (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
          (ik6.extractLsb' 0 56 ++ ik5.extractLsb' 56 8)
          (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
          (ik7.extractLsb' 56 8) ⊢
        memRegion (s.sp + 0x3e0#64) 65 := by
      rw [← hkp_sp]
      exact pointsTo8_words8_entails_memRegion65 (s.sp + 0x3e0#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 0#8
    refine SepWPp.weaken_frame hsp3e0_unfold (by sep_focus) ?_
    have hc4f8_fold :
        ((coroPtr + 0x4f8#64) ↦₆₄ idKpFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ (0#64 + skit.kpFutVtOff)) ⊢
        cells (coroPtr + 0x4f8#64) 2 := by
      rw [hc4f8]
      exact Entails.sepExists_right idKpFutPtr
        (Entails.sepExists_right (0#64 + skit.kpFutVtOff) (Entails.refl _))
    refine SepWPp.weaken_frame hc4f8_fold (by sep_focus) ?_
    refine p2_drop_frame_sub5
      (Drop := ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗
        ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗
        ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have hst06 : Steps (stageP1ProgPlaced ext) s s6 :=
      hst01.trans (hst12.trans (hst23.trans (hst34.trans (hst45.trans hst56))))
    have htr6 : s6.trace = s.trace ++ skit.kpEvs (.ok kp) := by
      rw [htr6_5, htr5_4, htr4_3, htr3_2, htr2]
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2]
    have hx25_6' : s6.readReg64 .x25 = s.readReg64 .x25 := by
      rw [hx25_6, hx25_5, hx25_cs4, hx25_3, hx25_2]
    have hx26_6' : s6.readReg64 .x26 = coroPtr + 0x398#64 := by
      rw [hx26_6, hx26_5, hx26_cs4, hx26_3]
    have hx28_6' : s6.readReg64 .x28 = s.sp + 0xa90#64 := by
      rw [hx28_6, hx28_5, hx28_cs4, hx28_3, hx28_2]

    have htail :=
      LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5AuxPlacedBudget.stageP2_sub5_tail_v1_kits_memInv_at_placed_ofEnv
        hInv (st := st_s5) (Qp := Qp)
        ext hSameAcct hInitBobErrOwned hInitBobV1
        hsame_le herr_le inp ikBPk spkBPk
        opkPkBytes opkSkBytes gMe gPeer s0 s6 Q s.sp coroPtr msgPtr remoteAddrPtr localAddrPtr
        kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
        ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 u_950 u_958 u_960 u_968
        opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 opkId opk_b64 b_4f1 stk
        (ikit.identityAt idStorePtr stId ∗ cells (coroPtr + 0x4f8#64) 2 ∗
         ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((s.sp + 0xa8#64) ↦₆₄ (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)) ∗
         ((s.sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
         ((s.sp + 0xb8#64) ↦₆₄ (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((s.sp + 0xd0#64) ↦₆₄ (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)) ∗
         memRegion (s.sp + 0x3c8#64) 7 ∗
         ((fp + 0xffffffffffffff80#64) ↦₆₄ (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)) ∗
         ((fp + 0xffffffffffffff88#64) ↦₈ (ik7.extractLsb' 56 8)) ∗ F_rest)
        htrusted hreplay hopk_match hwell hikBPk_len hspkBPk_len hopkSk_eq hneq_ik
        (fun a => by simpa only [BitVec.add_zero] using hikB0 a)
        (fun a => by simpa only [BitVec.add_zero] using hikB1 a)
        (fun a => by simpa only [BitVec.add_zero] using hopk a) hpqr_ne hstk_bob hstk_lt
        (fun drKey hacc => hfits_bob_ok kp evsKp drKey hrel hevsKp hacc)
        (fun hnone => hfits_bob_err kp evsKp hrel hevsKp hnone)
        hCode6 hpc6 hrun6 hsp6 hsp_align hvregs6
        (hx0_6.trans hx0_5) (hx1_6.trans hx1_5) hx2_6 (hx3_6.trans hx3_5)
        hx8_6 hx9_6 hx10_6 hx19_6 (hx21_6.trans hx21_5) (hx22_6.trans hx22_5)
        hx23_6 (hx24_6.trans hx24_5) hx28_6'
        (hx29_6.trans hx29_5)
        (fun drKey evsBob sf hacc hevsBob hst6f hpcf hrunf hspf htrf hx19f hx21f hx22f hx23f
          hx24f hx25f hx26f hx28f hx29f hvregsf hCodef => by
          have hok := hOk kp drKey evsKp evsBob sf
            (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
            (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
            (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
            (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
            (ik7.extractLsb' 56 8)
            hrel hevsKp hacc hevsBob (hst06.trans hst6f) hpcf hrunf hspf (htrf.trans htr6)
            hx19f hx21f hx22f hx23f hx24f (hx25f.trans hx25_6') (hx26f.trans hx26_6')
            hx28f hx29f hvregsf hCodef
          dsimp only [st_s5]
          rw [← M.stepEvents_append (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) evsBob st]
          exact p2_sepWPp_weaken_eq hok (by sep_focus))
        (fun evsErr errTag w2_e w3_e w4_e w5_e w6_e sf hnone hevsErr hne2 hne3 hst6f hpcf hrunf
          hspf htrf hx19f hx21f hx22f hx23f hx24f hx25f hx26f hx28f hx29f hvregsf hCodef => by
          have herr := hErrBob kp evsKp evsErr errTag w2_e w3_e w4_e w5_e w6_e sf
            (ik5.extractLsb' 0 56 ++ ik4.extractLsb' 56 8)
            (ik3.extractLsb' 0 56 ++ ik2.extractLsb' 56 8)
            (ik4.extractLsb' 0 56 ++ ik3.extractLsb' 56 8)
            (ik7.extractLsb' 0 56 ++ ik6.extractLsb' 56 8)
            (ik7.extractLsb' 56 8)
            hrel hevsKp hnone hevsErr hne2 hne3 (hst06.trans hst6f) hpcf hrunf hspf (htrf.trans htr6)
            hx19f hx21f hx22f hx23f hx24f (hx25f.trans hx25_6') (hx26f.trans hx26_6')
            hx28f hx29f hvregsf hCodef
          dsimp only [st_s5]
          rw [← M.stepEvents_append (evsKp ++ rustDeallocEvents skit.kpBoxSize 8) evsErr st]
          exact p2_sepWPp_weaken_eq herr (by sep_focus))
    exact p2_sepWPp_weaken_eq htail (by sep_focus)

theorem stageP2_sub5_v1_kits_memInv_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1MemInvOkAtPlaced Φ P A lim F ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5V1MemInvAtPlacedProp Φ P A lim F AcceptErrEnv ext skit senv bobV1Stk :=
  stageP2_sub5_v1_kits_memInv_at_placed_ofEnv hInv ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le

theorem stageP2_sub5_v1_kits_frozen_at_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInvAtPlacedSpec
          (LibsignalFrozen lsmpl) P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1FrozenOkAtPlacedOfEnv P A lim F BobV1Env ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv bobV1Stk :=
  stageP2_sub5_v1_kits_memInv_at_placed_ofEnv StageP2MemInv.frozen ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le

theorem stageP2_sub5_v1_kits_frozen_at_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A.repAlloc uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedMemInvAtPlacedSpec
          (LibsignalFrozen lsmpl) P A lim AcceptErrEnv bobErrStk))
    (hInitBobV1 : InitializeBobV1FrozenOkAtPlaced P A lim F ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5V1FrozenAtPlacedProp P A lim F AcceptErrEnv ext skit senv bobV1Stk :=
  stageP2_sub5_v1_kits_frozen_at_placed_ofEnv ext skit senv hH hskitOk hskitVt
    hSameAcct hInitBobErrOwned hInitBobV1 hsame_le herr_le

/-- `LibsignalFrozen`-guarded Budget-Threaded Placed Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, `_ofEnv`). -/
theorem stageP2_sub5_v1_kits_frozen_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hSame :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl
          (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.isSameAccountDistinctSpec
            A.repAlloc uuidTryParse)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
          (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim AcceptErrEnv)))
    (hInitBobV1 : InitializeBobV1FrozenOkPlacedOfEnv P A lim F BobV1Env ext) :
    stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackPlaced :=
  stageP2_sub5_v1_kits_memInv_at_placed_ofEnv StageP2MemInv.frozen ext skit senv hH hskitOk hskitVt
    (isSameAccountDistinctSpec_to_at_placed hSame)
    (of_responderCore_errOwned_frozen_placed hInitBobErrOwned)
    hInitBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1

theorem stageP2_sub5_v1_kits_frozen_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hSame :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl
          (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsBudget.isSameAccountDistinctSpec
            A.repAlloc uuidTryParse)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
          (initializeBobSessionErrOwnedFrozenPlacedSpec P A lim AcceptErrEnv)))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced P A lim F ext) :
    stageP2Sub5V1FrozenAtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackPlaced :=
  stageP2_sub5_v1_kits_frozen_placed_ofEnv ext skit senv hH hskitOk hskitVt
    hSame hInitBobErrOwned hInitBobV1

/-- `LibsignalFrozen`-guarded Budget-Threaded Placed Substage P2.5 (`+0x36ac -> +0x125c` at SPQR V1, 4K/`Ext`, `_ofEnv`). -/
theorem stageP2_sub5_v1_kits_frozen_ext_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext) :
    stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_memInv_at_placed_ofEnv StageP2MemInv.frozen ext skit senv hH hskitOk hskitVt
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    hInitBobErrOwned hInitBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt

theorem stageP2_sub5_v1_kits_frozen_ext_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (initializeBobSessionErrOwnedFrozen4KPlacedSpec P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4K P A lim F ext) :
    stageP2Sub5V1FrozenAtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_frozen_ext_placed_ofEnv ext skit senv hH hskitOk hskitVt
    hPure hInitBobErrOwned hInitBobV1

abbrev stageP2_sub5_v1_kits_frozen_4k_placed_ofEnv [LibsignalPlacement] :=
  @stageP2_sub5_v1_kits_frozen_ext_placed_ofEnv

abbrev stageP2_sub5_v1_kits_frozen_4k_placed [LibsignalPlacement] :=
  @stageP2_sub5_v1_kits_frozen_ext_placed

theorem stageP2_sub5_v1_kits_frozen_ext_defs_placed_ofEnv [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {BobV1Env : AcceptKeysInput → DRKey → List AllocEvent → Prop}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
          P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4KOfEnv P A lim F BobV1Env ext) :
    stageP2Sub5V1FrozenAtPlacedOfEnvProp P A lim F BobV1Env AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_frozen_ext_placed_ofEnv ext skit senv hH hskitOk hskitVt hPure
    (of_stageP2Defs_errOwned4K_frozen_placed hInitBobErrOwned) hInitBobV1

theorem stageP2_sub5_v1_kits_frozen_ext_defs_placed [LibsignalPlacement] {M : AllocCostModel}
    {P : Primitives} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {AcceptErrEnv : AcceptKeysInput → List AllocEvent → Prop}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    (skit : IdentitySelfStoreSpec ikit) (senv : IdentitySelfStoreBudgetEnv skit)
    (hH : StageP2ClosureHooksPlaced A lim ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI A lim ikit skit senv ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A lim ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget.initializeBobSessionErrOwnedFrozen4KPlacedSpec
          P A lim AcceptErrEnv))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4K P A lim F ext) :
    stageP2Sub5V1FrozenAtPlacedProp P A lim F AcceptErrEnv ext skit senv
      initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_v1_kits_frozen_ext_defs_placed_ofEnv ext skit senv hH hskitOk hskitVt
    hPure hInitBobErrOwned hInitBobV1

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5V1PlacedBudget
