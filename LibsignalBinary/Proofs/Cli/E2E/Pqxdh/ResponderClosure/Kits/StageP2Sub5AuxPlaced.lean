/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2b
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB5Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub5DefsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs

/-!
# Relocatable Stage P2 Substage P2.5 Tail at SPQR V1

Proves placed Substage P2.5 tail theorems (`+0x1168 → +0x125c`, including `StageP2MemInv` and
`LibsignalFrozen` variants) on Block `518` (`stageP1ProgPlaced ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SpqrV1.Top.InitialState (initialStateValue)

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

/-! ## Substage P2.5 Placed Tail (`+0x1168 -> +0x125c`) -/

private theorem p2_initBobErrOwnedAt_unpack_placed (A : RustAlloc) (sp : BitVec 64) :
    Kits.initBobErrOwnedAt A (sp + 0x3e0#64) ⊢
      ∃∗ errTag : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64,
        ⌜errTag ≠ 0xfffffffffffffffe#64 ∧ errTag ≠ 0xfffffffffffffffd#64⌝ ∗
        ((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
        Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (sp + 0x418#64) 288 := by
  dsimp only [Kits.initBobErrOwnedAt, pollReadyOkWord]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_right, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4
    (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

theorem of_cro_errOwned_at_placed [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {P : Primitives} {A : RustAlloc} {stk : Nat}
    (h : subroutine_ok prog entry (Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec P A stk)) :
    subroutine_ok prog entry
      (Sub5Placed.initializeBobSessionErrOwnedMemInvAtPlacedSpec
        (StoreKit.LibsignalCodeRoLoaded lsmpl) P A stk) := by
  refine subroutine_ok_map_panic h ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec,
        Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec,
        StoreKit.withLsCodeRoLoaded] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec,
        Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec,
        StoreKit.withLsCodeRoLoaded] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, ?_, fun sf hpost => ?_, fun sf hpan => hpan⟩
  · dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec,
      Sub5Placed.initializeBobSessionErrOwnedMemInvAtPlacedSpec, withBobMemInv,
      Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec,
      StoreKit.withLsCodeRoLoaded] at hpre ⊢
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
    exact hpre.2
  · dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec,
      Sub5Placed.initializeBobSessionErrOwnedMemInvAtPlacedSpec, withBobMemInv,
      Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec,
      StoreKit.withLsCodeRoLoaded] at hpost ⊢
    exact hpost

set_option maxHeartbeats 1200000 in
/-- Memory-invariant/stack-parameterized Placed Substage P2.5 Tail (`+0x1168 -> +0x125c` at SPQR V1):
Steps `p2_seg5c3_ext_placed_wp`, `isSameAccount`, `p2_seg5d_ext_placed_wp`, and
`initialize_bob_session` (branching on `Model.acceptKeys P inp` into `hOk` with `p2BobSessV1At`
or `hErrBob` Arm 5) under any `StageP2MemInv Φ`. -/
theorem stageP2_sub5_tail_v1_kits_memInv_at_placed [LibsignalPlacement]
    {Φ : Memory → Prop} (hInv : StageP2MemInv Φ)
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (Sub5Placed.initializeBobSessionErrOwnedMemInvAtPlacedSpec Φ P A bobErrStk))
    (hInitBobV1 : InitializeBobV1MemInvOkAtPlaced Φ P A F ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost)
    (s0 s6 : State) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
     kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
     u_950 u_958 u_960 u_968
     opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 : BitVec 64)
    (opkId : BitVec 32) (opk_b64 b_4f1 : BitVec 8)
    (stk : Nat) (F_rest : SepProp)
    (htrusted : inp.trustedPeer = true) (hreplay : inp.replayOk = true)
    (hopk_match : inp.hdr.opkId?.isSome = inp.opkBSk?.isSome)
    (hwell : WellSizedAcceptKeysInput inp)
    (hikBPk_len : ikBPk.length = 32) (hspkBPk_len : spkBPk.length = 32)
    (hopkSk_eq : ∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk)
    (hneq : bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes)
    (hikB0 : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ikBPk) =
      ((a + 0#64) ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗
      ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3))
    (hikB1 : ∀ a : BitVec 64, (a ↦ₛ bytesToBv8 inp.ikBSk) =
      ((a + 0#64) ↦₆₄ ik4) ∗ ((a + 8#64) ↦₆₄ ik5) ∗
      ((a + 16#64) ↦₆₄ ik6) ∗ ((a + 24#64) ↦₆₄ ik7))
    (hopk : ∀ a : BitVec 64,
      (a ↦₈ opkPresentTag inp.opkBSk?) ∗ ((a + 1#64) ↦ₛ opkPkBytes) ∗
        ((a + 33#64) ↦ₛ opkSkBytes) =
      ((a + 0#64) ↦₆₄ opk0) ∗ ((a + 8#64) ↦₆₄ opk1) ∗ ((a + 16#64) ↦₆₄ opk2) ∗
      ((a + 24#64) ↦₆₄ opk3) ∗ ((a + 32#64) ↦₆₄ opk4) ∗ ((a + 40#64) ↦₆₄ opk5) ∗
      ((a + 48#64) ↦₆₄ opk6) ∗ ((a + 56#64) ↦₆₄ opk7) ∗ ((a + 64#64) ↦₈ opk_b64))
    (hpqr_ne : sp - 576#64 ≠ 0#64)
    (hstk_bob : bobV1Stk ≤ stk)
    (hstk_lt : stk ≤ sp.toNat)
    (hCode6 : Φ s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0x1168#64)
    (hrun6 : s6.status = .Running)
    (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr6 : s0.trace <+: s6.trace)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx0_6 : s6.readReg64 .x0 = coroPtr + 0x798#64)
    (hx1_6 : s6.readReg64 .x1 = localAddrPtr)
    (hx2_6 : s6.readReg64 .x2 = msgPtr + 0xc8#64)
    (hx3_6 : s6.readReg64 .x3 = remoteAddrPtr)
    (hx8_6 : s6.readReg64 .x8 = opk_b64.zeroExtend 64)
    (hx9_6 : s6.readReg64 .x9 = msgPtr)
    (hx10_6 : s6.readReg64 .x10 = coroPtr + 0x798#64)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = msgPtr + 0x90#64)
    (hx22_6 : s6.readReg64 .x22 = sp + 0x370#64)
    (hx23_6 : s6.readReg64 .x23 = sp + 0x930#64)
    (hx24_6 : s6.readReg64 .x24 = coroPtr + 0x398#64)
    (hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64)
    (hx29_6 : s6.readReg64 .x29 = fp)
    (hOk : ∀ (drKey : DRKey) (sf : State),
      Model.acceptKeys P inp = some drKey →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         p2BobSessV1At A (sp + 0x3e0#64) inp ikBPk spkBPk drKey
           (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp)
    (hErrBob : ∀ (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State),
      Model.acceptKeys P inp = none →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
         memRegion (sp + 0x418#64) 288 ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗ ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
       ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗ ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 279 ∗
       ((sp + 0x930#64) ↦₆₄ ik0) ∗ ((sp + 0x938#64) ↦₆₄ ik1) ∗ ((sp + 0x940#64) ↦₆₄ ik2) ∗ ((sp + 0x948#64) ↦₆₄ ik3) ∗
       ((sp + 0x950#64) ↦₆₄ u_950) ∗ ((sp + 0x958#64) ↦₆₄ u_958) ∗
       ((sp + 0x960#64) ↦₆₄ u_960) ∗ ((sp + 0x968#64) ↦₆₄ u_968) ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0xa90#64) 8 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt sp.isLt)
  have hikBPk_bv : (bytesToBv8 ikBPk).length = 32 := by
    rw [bytesToBv8_length]; exact hikBPk_len
  have hspkBPk_bv : (bytesToBv8 spkBPk).length = 32 := by
    rw [bytesToBv8_length]; exact hspkBPk_len
  have hspkBSk_bv : (bytesToBv8 inp.spkBSk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.1
  have hikAPk_bv : (bytesToBv8 inp.hdr.ikAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.1
  have hekAPk_bv : (bytesToBv8 inp.hdr.ekAPk).length = 32 := by
    rw [bytesToBv8_length]; exact hwell.2.2.2.2.2.2.2.2.1
  obtain ⟨spk0, spk1, spk2, spk3, hspkPk⟩ := exists_words4_of_len32 hspkBPk_bv
  obtain ⟨spk4, spk5, spk6, spk7, hspkSk⟩ := exists_words4_of_len32 hspkBSk_bv
  obtain ⟨ikA0, ikA1, ikA2, ikA3, hikA⟩ := exists_words4_of_len32 hikAPk_bv
  obtain ⟨ekA0, ekA1, ekA2, ekA3, hekA⟩ := exists_words4_of_len32 hekAPk_bv
  have hspk_398 :
      ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) =
      ((coroPtr + 0x398#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x3a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x3a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x3b0#64) ↦₆₄ spk3) ∗
      ((coroPtr + 0x3b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x3c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x3c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x3d0#64) ↦₆₄ spk7) := by
    rw [hspkPk (coroPtr + 0x398#64), hspkSk (coroPtr + 0x3b8#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hekA_msg : ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) =
      ((msgPtr + 0xa8#64) ↦₆₄ ekA0) ∗ ((msgPtr + 0xb0#64) ↦₆₄ ekA1) ∗
      ((msgPtr + 0xb8#64) ↦₆₄ ekA2) ∗ ((msgPtr + 0xc0#64) ↦₆₄ ekA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hekA (msgPtr + 0xa8#64)
  have hikA_msg : ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) =
      ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hikA (msgPtr + 0xc8#64)
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_msg) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion65_eq_words8_byte (sp + 0x3e0#64)))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_420 => SepWPp.exists_elim fun u_3e0 =>
    SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 =>
    SepWPp.exists_elim fun u_3f8 => SepWPp.exists_elim fun u_400 =>
    SepWPp.exists_elim fun u_408 => SepWPp.exists_elim fun u_410 =>
    SepWPp.exists_elim fun u_418 => ?_
  have hca90 : cells (sp + 0xa90#64) 8 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
       ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64, ∃∗ u6 : BitVec 64, ∃∗ u7 : BitVec 64,
        ((sp + 0xa90#64) ↦₆₄ u0) ∗ ((sp + 0xa98#64) ↦₆₄ u1) ∗
        ((sp + 0xaa0#64) ↦₆₄ u2) ∗ ((sp + 0xaa8#64) ↦₆₄ u3) ∗
        ((sp + 0xab0#64) ↦₆₄ u4) ∗ ((sp + 0xab8#64) ↦₆₄ u5) ∗
        ((sp + 0xac0#64) ↦₆₄ u6) ∗ ((sp + 0xac8#64) ↦₆₄ u7)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hca90) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 =>
    SepWPp.exists_elim fun u_aa0 => SepWPp.exists_elim fun u_aa8 =>
    SepWPp.exists_elim fun u_ab0 => SepWPp.exists_elim fun u_ab8 =>
    SepWPp.exists_elim fun u_ac0 => SepWPp.exists_elim fun u_ac8 => ?_
  have hc560 : cells (sp + 0x560#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x560#64) ↦₆₄ u0) ∗ ((sp + 0x568#64) ↦₆₄ u1) ∗
        ((sp + 0x570#64) ↦₆₄ u2) ∗ ((sp + 0x578#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc560) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_560 => SepWPp.exists_elim fun u_568 =>
    SepWPp.exists_elim fun u_570 => SepWPp.exists_elim fun u_578 => ?_
  have hc6a0 : cells (sp + 0x6a0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x6a0#64) ↦₆₄ u0) ∗ ((sp + 0x6a8#64) ↦₆₄ u1) ∗
        ((sp + 0x6b0#64) ↦₆₄ u2) ∗ ((sp + 0x6b8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc6a0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_6a0 => SepWPp.exists_elim fun u_6a8 =>
    SepWPp.exists_elim fun u_6b0 => SepWPp.exists_elim fun u_6b8 => ?_
  have hc7e0 : cells (sp + 0x7e0#64) 4 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64,
        ((sp + 0x7e0#64) ↦₆₄ u0) ∗ ((sp + 0x7e8#64) ↦₆₄ u1) ∗
        ((sp + 0x7f0#64) ↦₆₄ u2) ∗ ((sp + 0x7f8#64) ↦₆₄ u3)) := by
    simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
      sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc7e0) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_7e0 => SepWPp.exists_elim fun u_7e8 =>
    SepWPp.exists_elim fun u_7f0 => SepWPp.exists_elim fun u_7f8 => ?_
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := by rw [hsp6]; exact hsp_align
  have hstep7 := p2_seg5c3_ext_placed_wp ext s6 coroPtr msgPtr localAddrPtr remoteAddrPtr
    ik4 ik5 ik6 ik7
    spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
    kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3
    ekA0 ekA1 ekA2 ekA3
    u_950 u_958 u_960 u_968
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8 u_ac0 u_ac8
    u_3e0 u_3e8 u_3f0 u_3f8 u_400 u_408 u_410 u_418
    u_560 u_568 u_570 u_578
    u_6a0 u_6a8 u_6b0 u_6b8
    u_7e0 u_7e8 u_7f0 u_7f8
    opk_b64 u_420 b_4f1
    hpc6 hrun6 hsp6_align
    hx0_6 hx1_6 hx2_6 hx3_6
    hx8_6 hx9_6 hx10_6 hx19_6
    (by rw [hx22_6, hsp6]) (by rw [hx23_6, hsp6]) hx24_6 (by rw [hx28_6, hsp6])
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode6
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep7)
    (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7_6, htr7_6, hx0_7, hx1_7, hx2_7, hx3_7, hx19_7, hx21_7, hx22_7, hx23_7,
    hx24_7, hx25_7, hx26_7, _, hx28_7, hx29_7, hx30_7, hvregs7_6⟩
  have hsp7 : s7.sp = sp := hsp7_6
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  let localIk : IdentityKey := ⟨⟨⟨bytesToBv8 ikBPk, hikBPk_bv⟩⟩⟩
  let remoteIk : IdentityKey := ⟨⟨⟨bytesToBv8 inp.hdr.ikAPk, hikAPk_bv⟩⟩⟩
  have hneq' : localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes :=
    hneq.imp
      (fun h => identityKey_ne_of_bytes_ne hikBPk_bv hikAPk_bv
        (fun h_eq => h (congrArg bytesToBv8 h_eq))) id
  have hlocIk_eq : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) =
      ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) := by
    change _ = ((coroPtr + 0x798#64) ↦ₛ bytesToBv8 ikBPk)
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x798#64)).symm
  have hremIk_eq : ((msgPtr + 0xc8#64) ↦₆₄ ikA0) ∗ ((msgPtr + 0xd0#64) ↦₆₄ ikA1) ∗
      ((msgPtr + 0xd8#64) ↦₆₄ ikA2) ∗ ((msgPtr + 0xe0#64) ↦₆₄ ikA3) =
      ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) :=
    hikA_msg.symm
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hremIk_eq) (by sep_focus) ?_
  have hstk_same := p2_stackAt_split_of_le sp stk sameStk
    (Nat.le_trans hsame_le hstk_bob) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same) (by sep_focus) ?_
  have hpc7_eq :
      libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::identity_key::IdentityKey>::is_same_account" = lsmpl.base 17 :=
    BitVec.add_zero _
  rw [hpc7_eq] at hpc7
  refine p2_call_nopanic_lscl_steps_frame_placed
    (x := (coroPtr + 0x798#64, localIk, localAddrPtr, gMe,
           msgPtr + 0xc8#64, remoteIk, remoteAddrPtr, gPeer))
    (R_pure := s7.readReg64 .x0 = coroPtr + 0x798#64 ∧ s7.readReg64 .x1 = localAddrPtr ∧
          s7.readReg64 .x2 = msgPtr + 0xc8#64 ∧ s7.readReg64 .x3 = remoteAddrPtr ∧
          (localIk ≠ remoteIk ∨ DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes))
    (T := ((coroPtr + 0x798#64) ↦ₛ localIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gMe localAddrPtr ∗
          ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) ∗
          protocolAddressAt A gPeer remoteAddrPtr ∗ stackAt sp sameStk)
    (hInv.toCodeRo hCode7) hSameAcct hpc7 hrun7 hsp7_al hx30_7
    (by dsimp only [isSameAccountDistinctAtSpec]; rw [hsp7])
    ⟨hx0_7, hx1_7, hx2_7, hx3_7, hneq'⟩ (by sep_focus)
    (hnext := fun s8 hst78 hpc8 hrun8 hsp8_7 _ hcs8 _ => ?_)
  dsimp only [isSameAccountDistinctAtSpec]; rw [hsp7]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_8_lo, htr8_7⟩ => ?_
  have hCode8 : Φ s8.mem := hInv.of_keepsFrozen hCode7 hst78.keepsFrozen
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := by rw [hsp8]; exact hsp_align
  rcases hcs8 with ⟨hx19_cs8, _, hx21_cs8, hx22_cs8, hx23_cs8, hx24_cs8, hx25_cs8, hx26_cs8, _,
    hx28_cs8, hx29_cs8, hvregscs8⟩
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hx19_cs8.trans hx19_7
  have hx21_8 : s8.readReg64 .x21 = msgPtr + 0x90#64 := by rw [hx21_cs8, hx21_7, hx21_6]
  have hx22_8 : s8.readReg64 .x22 = s8.sp + 0x370#64 := by rw [hx22_cs8, hx22_7, hsp8]
  have hx23_8 : s8.readReg64 .x23 = s8.sp + 0x930#64 := by rw [hx23_cs8, hx23_7, hsp8]
  have hx24_8 : s8.readReg64 .x24 = coroPtr + 0x398#64 := hx24_cs8.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s6.readReg64 .x25 := hx25_cs8.trans hx25_7
  have hx26_8 : s8.readReg64 .x26 = s6.readReg64 .x26 := hx26_cs8.trans hx26_7
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by rw [hx28_cs8, hx28_7, hsp8]
  have hx29_8 : s8.readReg64 .x29 = fp := by rw [hx29_cs8, hx29_7, hx29_6]
  refine SepWPp.weaken_frame (Entails.of_eq hstk_same.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hlocIk_eq.symm) (by sep_focus) ?_
  have hremIk_fold : ((msgPtr + 0xc8#64) ↦ₛ remoteIk.publicKey.bytes.toList) =
      ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := rfl
  refine SepWPp.weaken_frame (Entails.of_eq hremIk_fold) (by sep_focus) ?_
  have h798_64 : ((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
      ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ⊢
      memRegion (coroPtr + 0x798#64) 64 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      words8_entails_memRegion64 (coroPtr + 0x798#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
  refine SepWPp.weaken_frame h798_64 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspk_398.symm) (by sep_focus) ?_
  have hopk_4b0_symm :
      ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x4f0#64) ↦₈ opk_b64) =
      ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 0x4b0#64)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hopk_4b0_symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_msg.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro658_298_eq coroPtr)) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_781 => SepWPp.exists_elim fun c_780 => ?_
  have hc658 : cells (coroPtr + 0x658#64) 37 =
      (∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64, ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64,
       ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64, ∃∗ c10 : BitVec 64, ∃∗ c11 : BitVec 64,
       ∃∗ c12 : BitVec 64, ∃∗ c13 : BitVec 64, ∃∗ c14 : BitVec 64, ∃∗ c15 : BitVec 64, ∃∗ c16 : BitVec 64, ∃∗ c17 : BitVec 64,
       ∃∗ c18 : BitVec 64, ∃∗ c19 : BitVec 64, ∃∗ c20 : BitVec 64, ∃∗ c21 : BitVec 64, ∃∗ c22 : BitVec 64, ∃∗ c23 : BitVec 64,
       ∃∗ c24 : BitVec 64, ∃∗ c25 : BitVec 64, ∃∗ c26 : BitVec 64, ∃∗ c27 : BitVec 64, ∃∗ c28 : BitVec 64, ∃∗ c29 : BitVec 64,
       ∃∗ c30 : BitVec 64, ∃∗ c31 : BitVec 64, ∃∗ c32 : BitVec 64, ∃∗ c33 : BitVec 64, ∃∗ c34 : BitVec 64, ∃∗ c35 : BitVec 64, ∃∗ c36 : BitVec 64,
        ((coroPtr + 0x658#64) ↦₆₄ c0) ∗ ((coroPtr + 0x660#64) ↦₆₄ c1) ∗ ((coroPtr + 0x668#64) ↦₆₄ c2) ∗
        ((coroPtr + 0x670#64) ↦₆₄ c3) ∗ ((coroPtr + 0x678#64) ↦₆₄ c4) ∗ ((coroPtr + 0x680#64) ↦₆₄ c5) ∗
        ((coroPtr + 0x688#64) ↦₆₄ c6) ∗ ((coroPtr + 0x690#64) ↦₆₄ c7) ∗ ((coroPtr + 0x698#64) ↦₆₄ c8) ∗
        ((coroPtr + 0x6a0#64) ↦₆₄ c9) ∗ ((coroPtr + 0x6a8#64) ↦₆₄ c10) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ c11) ∗
        ((coroPtr + 0x6b8#64) ↦₆₄ c12) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ c13) ∗ ((coroPtr + 0x6c8#64) ↦₆₄ c14) ∗
        ((coroPtr + 0x6d0#64) ↦₆₄ c15) ∗ ((coroPtr + 0x6d8#64) ↦₆₄ c16) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ c17) ∗
        ((coroPtr + 0x6e8#64) ↦₆₄ c18) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ c19) ∗ ((coroPtr + 0x6f8#64) ↦₆₄ c20) ∗
        ((coroPtr + 0x700#64) ↦₆₄ c21) ∗ ((coroPtr + 0x708#64) ↦₆₄ c22) ∗ ((coroPtr + 0x710#64) ↦₆₄ c23) ∗
        ((coroPtr + 0x718#64) ↦₆₄ c24) ∗ ((coroPtr + 0x720#64) ↦₆₄ c25) ∗ ((coroPtr + 0x728#64) ↦₆₄ c26) ∗
        ((coroPtr + 0x730#64) ↦₆₄ c27) ∗ ((coroPtr + 0x738#64) ↦₆₄ c28) ∗ ((coroPtr + 0x740#64) ↦₆₄ c29) ∗
        ((coroPtr + 0x748#64) ↦₆₄ c30) ∗ ((coroPtr + 0x750#64) ↦₆₄ c31) ∗ ((coroPtr + 0x758#64) ↦₆₄ c32) ∗
        ((coroPtr + 0x760#64) ↦₆₄ c33) ∗ ((coroPtr + 0x768#64) ↦₆₄ c34) ∗ ((coroPtr + 0x770#64) ↦₆₄ c35) ∗
        ((coroPtr + 0x778#64) ↦₆₄ c36)) := by
    simp (config := { maxSteps := 1000000 }) only
      [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
       sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc658) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_658 => SepWPp.exists_elim fun c_660 => SepWPp.exists_elim fun c_668 =>
    SepWPp.exists_elim fun c_670 => SepWPp.exists_elim fun c_678 => SepWPp.exists_elim fun c_680 =>
    SepWPp.exists_elim fun c_688 => SepWPp.exists_elim fun c_690 => SepWPp.exists_elim fun c_698 =>
    SepWPp.exists_elim fun c_6a0 => SepWPp.exists_elim fun c_6a8 => SepWPp.exists_elim fun c_6b0 =>
    SepWPp.exists_elim fun c_6b8 => SepWPp.exists_elim fun c_6c0 => SepWPp.exists_elim fun c_6c8 =>
    SepWPp.exists_elim fun c_6d0 => SepWPp.exists_elim fun c_6d8 => SepWPp.exists_elim fun c_6e0 =>
    SepWPp.exists_elim fun c_6e8 => SepWPp.exists_elim fun c_6f0 => SepWPp.exists_elim fun c_6f8 =>
    SepWPp.exists_elim fun c_700 => SepWPp.exists_elim fun c_708 => SepWPp.exists_elim fun c_710 =>
    SepWPp.exists_elim fun c_718 => SepWPp.exists_elim fun c_720 => SepWPp.exists_elim fun c_728 =>
    SepWPp.exists_elim fun c_730 => SepWPp.exists_elim fun c_738 => SepWPp.exists_elim fun c_740 =>
    SepWPp.exists_elim fun c_748 => SepWPp.exists_elim fun c_750 => SepWPp.exists_elim fun c_758 =>
    SepWPp.exists_elim fun c_760 => SepWPp.exists_elim fun c_768 => SepWPp.exists_elim fun c_770 =>
    SepWPp.exists_elim fun c_778 => ?_
  have hstep9 := p2_seg5d_ext_placed_wp ext s8 coroPtr (msgPtr + 0x90#64) (s8.readReg64 .x0)
    ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7 spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7
    opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64
    ikA0 ikA1 ikA2 ikA3 ekA0 ekA1 ekA2 ekA3
    c_658 c_660 c_668 c_670 c_678 c_680 c_688 c_690 c_698 c_6a0 c_6a8 c_6b0 c_6b8 c_6c0 c_6c8 c_6d0
    c_6d8 c_6e0 c_6e8 c_6f0 c_6f8 c_700 c_708 c_710 c_718 c_720 c_728 c_730 c_738
    c_740 c_748 c_750 c_758 c_760 c_768 c_770 c_778 opk_b64 c_780 c_781
    hpc8 hrun8 hsp8_align rfl hx19_8 hx21_8 hx22_8 hx23_8 hx24_8 hx28_8
  have hx0_8_b : (s8.readReg64 .x0).setWidth 8 = 0#8 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have h0 := congrArg (fun v => v.getLsbD i) hx0_8_lo
    have hi32 : i < 32 := by omega
    simpa [BitVec.getLsbD_setWidth, hi, hi32] using h0
  rw [hsp8, hx0_8_b] at hstep9
  refine p2_bind_sepWP_steps_memInv_sub5_qpan hInv hCode8
    (by simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using hstep9)
    (by sep_focus)
    fun s9 hst89 hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9_8, htr9_8, hx0_9, hx1_9, hx8_9, hx19_9, hx21_9, hx22_9, hx23_9, hx24_9,
    hx25_9, hx26_9, _, hx28_9, hx29_9, hx30_9, hvregs9_8⟩
  have hsp9 : s9.sp = sp := hsp9_8
  have hsp9_al : s9.spAligned = true := by simpa only [State.spAligned, hsp9] using hsp_align
  refine SepWPp.weaken_frame
    (words8_byte_entails_memRegion65 (sp + 0x3e0#64) opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7
      opk_b64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (sp3e0_344_split_65_279 sp).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 0x930#64) ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words8_entails_cells8 (sp + 0xa90#64) spk0 spk1 spk2 spk3 spk4 spk5 spk6 spk7)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x560#64) kyberKpPubPtr 0x620#64 kyberKpSecPtr 0xc60#64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x6a0#64) ikA0 ikA1 ikA2 ikA3)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (by
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        words4_entails_cells4 (sp + 0x7e0#64) ekA0 ekA1 ekA2 ekA3)
    (by sep_focus) ?_
  have hikB0_658 : ((coroPtr + 0x658#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x660#64) ↦₆₄ ik1) ∗
      ((coroPtr + 0x668#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x670#64) ↦₆₄ ik3) =
      ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB0 (coroPtr + 0x658#64)).symm
  have hikB1_678 : ((coroPtr + 0x678#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x680#64) ↦₆₄ ik5) ∗
      ((coroPtr + 0x688#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x690#64) ↦₆₄ ik7) =
      ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikB1 (coroPtr + 0x678#64)).symm
  have hspkPk_698 : ((coroPtr + 0x698#64) ↦₆₄ spk0) ∗ ((coroPtr + 0x6a0#64) ↦₆₄ spk1) ∗
      ((coroPtr + 0x6a8#64) ↦₆₄ spk2) ∗ ((coroPtr + 0x6b0#64) ↦₆₄ spk3) =
      ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkPk (coroPtr + 0x698#64)).symm
  have hspkSk_6b8 : ((coroPtr + 0x6b8#64) ↦₆₄ spk4) ∗ ((coroPtr + 0x6c0#64) ↦₆₄ spk5) ∗
      ((coroPtr + 0x6c8#64) ↦₆₄ spk6) ∗ ((coroPtr + 0x6d0#64) ↦₆₄ spk7) =
      ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hspkSk (coroPtr + 0x6b8#64)).symm
  have hikA_6d8 : ((coroPtr + 0x6d8#64) ↦₆₄ ikA0) ∗ ((coroPtr + 0x6e0#64) ↦₆₄ ikA1) ∗
      ((coroPtr + 0x6e8#64) ↦₆₄ ikA2) ∗ ((coroPtr + 0x6f0#64) ↦₆₄ ikA3) =
      ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hikA (coroPtr + 0x6d8#64)).symm
  have hekA_6f8 : ((coroPtr + 0x6f8#64) ↦₆₄ ekA0) ∗ ((coroPtr + 0x700#64) ↦₆₄ ekA1) ∗
      ((coroPtr + 0x708#64) ↦₆₄ ekA2) ∗ ((coroPtr + 0x710#64) ↦₆₄ ekA3) =
      ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hekA (coroPtr + 0x6f8#64)).symm
  have hopk_740 : ((coroPtr + 0x740#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x748#64) ↦₆₄ opk1) ∗
      ((coroPtr + 0x750#64) ↦₆₄ opk2) ∗ ((coroPtr + 0x758#64) ↦₆₄ opk3) ∗
      ((coroPtr + 0x760#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x768#64) ↦₆₄ opk5) ∗
      ((coroPtr + 0x770#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x778#64) ↦₆₄ opk7) ∗
      ((coroPtr + 0x780#64) ↦₈ opk_b64) =
      ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗ ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
      ((coroPtr + 0x761#64) ↦ₛ opkSkBytes) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      (hopk (coroPtr + 0x740#64)).symm
  refine SepWPp.weaken_frame (Entails.of_eq hikB0_658) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikB1_678) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkPk_698) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hspkSk_6b8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hikA_6d8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hekA_6f8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hopk_740) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (opkSlot65_eq_optField (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes hopkSk_eq))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (bobParamsFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ikBPk spkBPk))
    (by sep_focus) ?_
  have htr9_6 : s9.trace = s6.trace := by rw [htr9_8, htr8_7, htr7_6]
  have htr9_0 : s0.trace <+: s9.trace := htr9_6 ▸ htr6
  have hvregs9 : calleeSavedVRegs s9 = calleeSavedVRegs s0 := by
    rw [hvregs9_8, hvregscs8, hvregs7_6, hvregs6]
  have hpc9_eq :
      libsignalSessionLib.resolve lsmpl
        "libsignal_protocol::ratchet::initialize_bob_session" = lsmpl.base 75 :=
    BitVec.add_zero _
  rw [hpc9_eq] at hpc9
  cases hacc : Model.acceptKeys P inp with
  | none =>
    have hstk_err := p2_stackAt_split_of_le sp stk bobErrStk
      (Nat.le_trans herr_le hstk_bob) hstk_le64
    refine SepWPp.weaken_frame (Entails.of_eq hstk_err) (by sep_focus) ?_
    refine p2_call_memInv_oom_steps_frame_sub5_qpan hInv
      (x := ({ inp := inp, ikBPk := ikBPk, spkBPk := spkBPk, sameAccountByte := 0#8,
               argPtr := coroPtr + 0x658#64, pqskPtr := kyberKpSecPtr,
               ctSlicePtr := msgPtr + 0x90#64, ctBufPtr := ctBufPtr,
               ratchetKeyPairPtr := coroPtr + 0x398#64,
               outPtr := sp + 0x3e0#64 } : InitBobCallGhost))
      (φ := s9.readReg64 .x0 = coroPtr + 0x658#64 ∧ s9.readReg64 .x1 = coroPtr + 0x398#64 ∧
            s9.readReg64 .x8 = sp + 0x3e0#64 ∧ inp.trustedPeer = true ∧ inp.replayOk = true ∧
            inp.hdr.opkId?.isSome = inp.opkBSk?.isSome ∧ WellSizedAcceptKeysInput inp ∧
            ikBPk.length = 32 ∧ spkBPk.length = 32 ∧ Model.acceptKeys P inp = none)
      (T := bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
              (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗ memRegion (sp + 0x3e0#64) 344 ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp bobErrStk ∗ A.pool)
      hpan hCode9 htr9_0 hInitBobErrOwned
      hpc9 hrun9 hsp9_al hx30_9
      (by dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec]; rw [hsp9])
      ⟨hx0_9, hx1_9, hx8_9, htrusted, hreplay, hopk_match, hwell, hikBPk_len, hspkBPk_len, hacc⟩
      (by sep_focus)
      (hnext := fun sf hst9f hpcf hrunf hspf_9 _ hcsf hCodef => ?_)
    dsimp only [Sub5Placed.initializeBobSessionErrOwnedAtInnerPlacedSpec]
    rw [hsp9]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrf_9 => ?_
    rcases hcsf with ⟨hx19_csf, _, hx21_csf, hx22_csf, hx23_csf, hx24_csf, hx25_csf, hx26_csf, _,
      hx28_csf, hx29_csf, hvregscsf⟩
    refine SepWPp.weaken_frame (Entails.of_eq hstk_err.symm) (by sep_focus) ?_
    refine SepWPp.weaken_frame (p2_initBobErrOwnedAt_unpack_placed A sp) (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun errTag => SepWPp.exists_elim fun w2 =>
      SepWPp.exists_elim fun w3 => SepWPp.exists_elim fun w4 =>
      SepWPp.exists_elim fun w5 => SepWPp.exists_elim fun w6 => ?_
    refine SepWPp.pure_elim fun ⟨herr_ne2, herr_ne3⟩ => ?_
    have hsteps_all := hst67.trans (hst78.trans (hst89.trans hst9f))
    have herr := hErrBob errTag w2 w3 w4 w5 w6 sf hacc herr_ne2 herr_ne3
      hsteps_all hpcf hrunf (hspf_9.trans hsp9) (htrf_9.trans htr9_6)
      (hx19_csf.trans hx19_9) (hx21_csf.trans hx21_9) (hx22_csf.trans hx22_9)
      (hx23_csf.trans hx23_9) (hx24_csf.trans hx24_9)
      (by rw [hx25_csf, hx25_9, hx25_8]) (by rw [hx26_csf, hx26_9, hx26_8])
      (hx28_csf.trans hx28_9) (by rw [hx29_csf, hx29_9, hx29_8])
      (hvregscsf.trans hvregs9) (hInv.toCodeRo hCodef)
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | some drKey =>
    have hstk_v1 := p2_stackAt_split_of_le sp stk bobV1Stk hstk_bob hstk_le64
    refine SepWPp.weaken_frame (Entails.of_eq hstk_v1) (by sep_focus) ?_
    let FrameBob : SepProp :=
      ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
      ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
      ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
      ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
      ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
      ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
      ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
      ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
      opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
      memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
      ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
      ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
      protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
      cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
      cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
      memRegion (sp - BitVec.ofNat 64 stk) (stk - bobV1Stk) ∗ F_rest
    have hpb4 := hInitBobV1 s9 inp ikBPk spkBPk
      (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
      (coroPtr + 0x398#64) (sp + 0x3e0#64) drKey FrameBob
      hCode9 hrun9 hpc9 hsp9_al (by rw [hsp9]; exact hpqr_ne)
      hx0_9 hx1_9 hx8_9 htrusted hreplay hopk_match hwell hikBPk_len hspkBPk_len hacc
    rw [hsp9, hx30_9] at hpb4
    refine p2_sepWPp_weaken_eq
      (p2_bind_loaded_memInv_sub5_qpan hInv hpan hCode9
        (p2_bobPanic_to_panicOom_prefix htr9_0 hpb4) ?_)
      (by dsimp only [FrameBob]; sep_focus)
    rintro sf Pf hst9f hpcf hrunf hCodef
      ⟨localIkBoxPtr, remoteIkBoxPtr, rootKeyBoxPtr, baseKeyBoxPtr, ratchetPubBoxPtr,
        ratchetPrivBoxPtr, chainKeyBoxPtr, spqrCap, spqrBufPtr, pad_f4, c0, c1, c2, c3, c4, d0, d1,
        d2, hn1, hn2, hn3, hn4, hn5, hn6, hn7, hPf, _, _, hspf_9, hcsf, htrf_9⟩
    rcases hcsf with ⟨hx19_csf, _, hx21_csf, hx22_csf, hx23_csf, hx24_csf, hx25_csf, hx26_csf, _,
      hx28_csf, hx29_csf, hvregscsf⟩
    have hsteps_all := hst67.trans (hst78.trans (hst89.trans hst9f))
    have hok := hOk drKey sf hacc hsteps_all hpcf hrunf hspf_9
      (htrf_9.trans htr9_6)
      (hx19_csf.trans hx19_9) (hx21_csf.trans hx21_9) (hx22_csf.trans hx22_9)
      (hx23_csf.trans hx23_9) (hx24_csf.trans hx24_9)
      (by rw [hx25_csf, hx25_9, hx25_8]) (by rw [hx26_csf, hx26_9, hx26_8])
      (hx28_csf.trans hx28_9) (by rw [hx29_csf, hx29_9, hx29_8])
      (hvregscsf.trans hvregs9) (hInv.toCodeRo hCodef)
    refine SepWPp.weaken_pre (Entails.trans hPf ?_) hok
    dsimp only [FrameBob]
    refine p2_entails_frame_v1
      (p2BobSessV1At_intro A (sp + 0x3e0#64) inp ikBPk spkBPk drKey
        (initialStateValue F (p2BobSpqrParams drKey.pqrKey))
        localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr
        chainKeyBoxPtr spqrCap spqrBufPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        hn1 hn2 hn3 hn4 hn5 hn6 hn7)
      (by sep_focus) ?_
    refine p2_entails_frame_v1 (Entails.of_eq hstk_v1.symm) (by sep_focus) ?_
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-- Residual statement `Prop` of `stageP2_sub5_tail_v1_kits_memInv_at_placed` parameterized by
`Φ` and `bobV1Stk`. -/
abbrev stageP2Sub5TailV1MemInvAtPlacedProp [LibsignalPlacement]
    (Φ : Memory → Prop) (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (bobV1Stk : Nat) : Prop :=
  ∀ (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (opkPkBytes opkSkBytes : List (BitVec 8))
    (gMe gPeer : AddrGhost)
    (s0 s6 : State) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (_hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
     kyberKpPubPtr kyberKpSecPtr ctBufPtr fp
     ik0 ik1 ik2 ik3 ik4 ik5 ik6 ik7
     u_950 u_958 u_960 u_968
     opk0 opk1 opk2 opk3 opk4 opk5 opk6 opk7 : BitVec 64)
    (opkId : BitVec 32) (opk_b64 b_4f1 : BitVec 8)
    (stk : Nat) (F_rest : SepProp),
    inp.trustedPeer = true → inp.replayOk = true →
    inp.hdr.opkId?.isSome = inp.opkBSk?.isSome →
    WellSizedAcceptKeysInput inp →
    ikBPk.length = 32 → spkBPk.length = 32 →
    (∀ opkSk, inp.opkBSk? = some opkSk → opkSkBytes = bytesToBv8 opkSk) →
    (bytesToBv8 ikBPk ≠ bytesToBv8 inp.hdr.ikAPk ∨
      DistinctSid uuidTryParse gMe.name.bytes gPeer.name.bytes) →
    (∀ a : BitVec 64, (a ↦ₛ bytesToBv8 ikBPk) =
      ((a + 0#64) ↦₆₄ ik0) ∗ ((a + 8#64) ↦₆₄ ik1) ∗
      ((a + 16#64) ↦₆₄ ik2) ∗ ((a + 24#64) ↦₆₄ ik3)) →
    (∀ a : BitVec 64, (a ↦ₛ bytesToBv8 inp.ikBSk) =
      ((a + 0#64) ↦₆₄ ik4) ∗ ((a + 8#64) ↦₆₄ ik5) ∗
      ((a + 16#64) ↦₆₄ ik6) ∗ ((a + 24#64) ↦₆₄ ik7)) →
    (∀ a : BitVec 64,
      (a ↦₈ opkPresentTag inp.opkBSk?) ∗ ((a + 1#64) ↦ₛ opkPkBytes) ∗
        ((a + 33#64) ↦ₛ opkSkBytes) =
      ((a + 0#64) ↦₆₄ opk0) ∗ ((a + 8#64) ↦₆₄ opk1) ∗ ((a + 16#64) ↦₆₄ opk2) ∗
      ((a + 24#64) ↦₆₄ opk3) ∗ ((a + 32#64) ↦₆₄ opk4) ∗ ((a + 40#64) ↦₆₄ opk5) ∗
      ((a + 48#64) ↦₆₄ opk6) ∗ ((a + 56#64) ↦₆₄ opk7) ∗ ((a + 64#64) ↦₈ opk_b64)) →
    sp - 576#64 ≠ 0#64 →
    bobV1Stk ≤ stk →
    stk ≤ sp.toNat →
    Φ s6.mem →
    s6.pc = stageP1EntryPlaced + 0x1168#64 →
    s6.status = .Running →
    s6.sp = sp →
    (sp &&& 15#64 == 0#64) = true →
    s0.trace <+: s6.trace →
    calleeSavedVRegs s6 = calleeSavedVRegs s0 →
    s6.readReg64 .x0 = coroPtr + 0x798#64 →
    s6.readReg64 .x1 = localAddrPtr →
    s6.readReg64 .x2 = msgPtr + 0xc8#64 →
    s6.readReg64 .x3 = remoteAddrPtr →
    s6.readReg64 .x8 = opk_b64.zeroExtend 64 →
    s6.readReg64 .x9 = msgPtr →
    s6.readReg64 .x10 = coroPtr + 0x798#64 →
    s6.readReg64 .x19 = coroPtr →
    s6.readReg64 .x21 = msgPtr + 0x90#64 →
    s6.readReg64 .x22 = sp + 0x370#64 →
    s6.readReg64 .x23 = sp + 0x930#64 →
    s6.readReg64 .x24 = coroPtr + 0x398#64 →
    s6.readReg64 .x28 = sp + 0xa90#64 →
    s6.readReg64 .x29 = fp →
    (∀ (drKey : DRKey) (sf : State),
      Model.acceptKeys P inp = some drKey →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         p2BobSessV1At A (sp + 0x3e0#64) inp ikBPk spkBPk drKey
           (initialStateValue F (p2BobSpqrParams drKey.pqrKey)) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) →
    (∀ (errTag w2 w3 w4 w5 w6 : BitVec 64) (sf : State),
      Model.acceptKeys P inp = none →
      errTag ≠ 0xfffffffffffffffe#64 → errTag ≠ 0xfffffffffffffffd#64 →
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x125c#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x21 = msgPtr + 0x90#64 →
      sf.readReg64 .x22 = sp + 0x370#64 →
      sf.readReg64 .x23 = sp + 0x930#64 →
      sf.readReg64 .x24 = coroPtr + 0x398#64 →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = s6.readReg64 .x26 →
      sf.readReg64 .x28 = sp + 0xa90#64 →
      sf.readReg64 .x29 = fp →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) sf
        (((sp + 0x3e0#64) ↦₆₄ 0xffffffffffffffff#64) ∗
         speWordsAt (sp + 0x3e8#64) errTag w2 w3 w4 w5 w6 ∗
         Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
         memRegion (sp + 0x418#64) 288 ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
         ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x4b0#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         ((coroPtr + 0x4b1#64) ↦ₛ opkPkBytes) ∗ ((coroPtr + 0x4d1#64) ↦ₛ opkSkBytes) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x698#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x741#64) ↦ₛ opkPkBytes) ∗
         opkUnusedFieldAt (coroPtr + 0x761#64) inp.opkBSk? opkSkBytes ∗
         memRegion (coroPtr + 0x798#64) 64 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
         cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
         cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 8 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ anyHeap ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) →
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s6
      (((coroPtr + 0x798#64) ↦₆₄ ik0) ∗ ((coroPtr + 0x7a0#64) ↦₆₄ ik1) ∗
       ((coroPtr + 0x7a8#64) ↦₆₄ ik2) ∗ ((coroPtr + 0x7b0#64) ↦₆₄ ik3) ∗
       ((coroPtr + 0x7b8#64) ↦₆₄ ik4) ∗ ((coroPtr + 0x7c0#64) ↦₆₄ ik5) ∗
       ((coroPtr + 0x7c8#64) ↦₆₄ ik6) ∗ ((coroPtr + 0x7d0#64) ↦₆₄ ik7) ∗
       ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
       ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
       ((coroPtr + 0x3d8#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x3e8#64) ↦₆₄ kyberKpSecPtr) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗ ((coroPtr + 0x488#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
       ((coroPtr + 0x4b0#64) ↦₆₄ opk0) ∗ ((coroPtr + 0x4b8#64) ↦₆₄ opk1) ∗ ((coroPtr + 0x4c0#64) ↦₆₄ opk2) ∗
       ((coroPtr + 0x4c8#64) ↦₆₄ opk3) ∗ ((coroPtr + 0x4d0#64) ↦₆₄ opk4) ∗ ((coroPtr + 0x4d8#64) ↦₆₄ opk5) ∗
       ((coroPtr + 0x4e0#64) ↦₆₄ opk6) ∗ ((coroPtr + 0x4e8#64) ↦₆₄ opk7) ∗
       ((coroPtr + 0x4f0#64) ↦₈ opk_b64) ∗ ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       memRegion (coroPtr + 0x658#64) 298 ∗ ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗ ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
       ((msgPtr + 0xa8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗ ((msgPtr + 0xc8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
       (kyberKpSecPtr ↦₈ (bytesToBv8 inp.pqspkBSk).getD 0 0#8) ∗
       ((kyberKpSecPtr + 1#64) ↦ₛ (bytesToBv8 inp.pqspkBSk).drop 1) ∗
       (ctBufPtr ↦₈ 8#8) ∗ ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
       ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
       protocolAddressAt A gMe localAddrPtr ∗ protocolAddressAt A gPeer remoteAddrPtr ∗
       memRegion (sp + 0x3e0#64) 65 ∗ memRegion (sp + 0x421#64) 279 ∗
       ((sp + 0x930#64) ↦₆₄ ik0) ∗ ((sp + 0x938#64) ↦₆₄ ik1) ∗ ((sp + 0x940#64) ↦₆₄ ik2) ∗ ((sp + 0x948#64) ↦₆₄ ik3) ∗
       ((sp + 0x950#64) ↦₆₄ u_950) ∗ ((sp + 0x958#64) ↦₆₄ u_958) ∗
       ((sp + 0x960#64) ↦₆₄ u_960) ∗ ((sp + 0x968#64) ↦₆₄ u_968) ∗
       cells (sp + 0x560#64) 4 ∗ cells (sp + 0x6a0#64) 4 ∗ cells (sp + 0x7e0#64) 4 ∗
       cells (sp + 0xa90#64) 8 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp

abbrev stageP2Sub5TailV1AtPlacedProp [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5TailV1MemInvAtPlacedProp (StoreKit.LibsignalCodeRoLoaded lsmpl) P A F ext bobV1Stk

abbrev stageP2Sub5TailV1FrozenAtPlacedProp [LibsignalPlacement]
    (P : Primitives) (A : RustAlloc) (F : ShaCompress)
    (ext : String → Option (State → State))
    (bobV1Stk : Nat) : Prop :=
  stageP2Sub5TailV1MemInvAtPlacedProp (LibsignalFrozen lsmpl) P A F ext bobV1Stk

theorem stageP2_sub5_tail_v1_kits_at_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    {sameStk bobErrStk bobV1Stk : Nat}
    (hSameAcct :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (isSameAccountDistinctAtSpec A uuidTryParse sameStk)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (Sub5Placed.initializeBobSessionErrOwnedAtPlacedSpec P A bobErrStk))
    (hInitBobV1 : InitializeBobV1OkAtPlaced P A F ext bobV1Stk)
    (hsame_le : sameStk ≤ bobV1Stk)
    (herr_le : bobErrStk ≤ bobV1Stk) :
    stageP2Sub5TailV1AtPlacedProp P A F ext bobV1Stk :=
  stageP2_sub5_tail_v1_kits_memInv_at_placed StageP2MemInv.codeRoLoaded ext
    hSameAcct (of_cro_errOwned_at_placed hInitBobErrOwned) hInitBobV1 hsame_le herr_le

abbrev initializeBobSessionV1StackPlaced : Nat := stageP2bStack + 0x700

abbrev initializeBobSessionV1StackExtPlaced : Nat := 768 + Initiator.pqxdhEntryStackExt

/-- Placed Substage P2.5 Tail (`+0x1168 -> +0x125c` at SPQR V1, `StageP2PureCalleesPlaced`). -/
theorem stageP2_sub5_tail_v1_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hPure : StageP2PureCalleesPlaced P A F ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (ResponderCore.initializeBobSessionErrOwnedPlacedSpec P A)) :
    stageP2Sub5TailV1AtPlacedProp P A F ext initializeBobSessionV1StackPlaced :=
  stageP2_sub5_tail_v1_kits_at_placed ext
    (isSameAccountDistinctSpec_to_at_placed hPure.isSameAccount)
    (Sub5Placed.of_responderCore_errOwned_placed hInitBobErrOwned)
    hPure.initializeBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1

/-- Placed Substage P2.5 Tail (`+0x1168 -> +0x125c` at SPQR V1, `StageP2PureCalleesPlaced4K`). -/
theorem stageP2_sub5_tail_v1_kits_ext_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hPure : StageP2PureCalleesPlaced4K P A F ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (Sub5Placed.initializeBobSessionErrOwned4KPlacedSpec P A)) :
    stageP2Sub5TailV1AtPlacedProp P A F ext initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_tail_v1_kits_at_placed ext
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    hInitBobErrOwned hPure.initializeBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt

abbrev stageP2_sub5_tail_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_sub5_tail_v1_kits_ext_placed

/-- `LibsignalFrozen`-guarded Placed Substage P2.5 Tail (`+0x1168 -> +0x125c` at SPQR V1). -/
theorem stageP2_sub5_tail_v1_kits_frozen_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hSame :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 17)
        (withLsCodeLoaded lsmpl (WireEntries.isSameAccountDistinctSpec A uuidTryParse)))
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (StoreKit.withLsCodeRoLoaded lsmpl
          (ResponderCore.initializeBobSessionErrOwnedFrozenPlacedSpec P A)))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced P A F ext) :
    stageP2Sub5TailV1FrozenAtPlacedProp P A F ext initializeBobSessionV1StackPlaced :=
  stageP2_sub5_tail_v1_kits_memInv_at_placed StageP2MemInv.frozen ext
    (isSameAccountDistinctSpec_to_at_placed hSame)
    (Sub5Placed.of_responderCore_errOwned_frozen_placed hInitBobErrOwned)
    hInitBobV1
    p2_isSameAccount_le_bobV1 p2_stageP2bStack_le_bobV1

/-- `LibsignalFrozen`-guarded Placed Substage P2.5 Tail (`+0x1168 -> +0x125c` at SPQR V1, 4K/`Ext`). -/
theorem stageP2_sub5_tail_v1_kits_frozen_ext_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hInitBobErrOwned :
      subroutine_ok (stageP1ProgPlaced ext)
        (lsmpl.base 75)
        (Sub5Placed.initializeBobSessionErrOwnedFrozen4KPlacedSpec P A))
    (hInitBobV1 : InitializeBobV1FrozenOkPlaced4K P A F ext) :
    stageP2Sub5TailV1FrozenAtPlacedProp P A F ext initializeBobSessionV1StackExtPlaced :=
  stageP2_sub5_tail_v1_kits_memInv_at_placed StageP2MemInv.frozen ext
    (isSameAccountDistinctSpecExt_to_at_placed hPure.isSameAccount)
    hInitBobErrOwned hInitBobV1
    p2_isSameAccountExt_le_bobExt p2_bobErr4K_le_bobExt

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
