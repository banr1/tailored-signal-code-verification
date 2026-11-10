/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6V1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common

/-!
# Placed Stage P2 Over-Path Substage P2.6

Proves the `[LibsignalPlacement]` Over-path Substage P2.6 theorem
`stageP2_over_sub6_v1_kits_ext_placed` (`+0x125c → +0x1778` on `Ok`, or `+0x09f4` Arm 6 on
`get_local_registration_id` error).
-/

@[expose] public section

set_option autoImplicit false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt prevArchived1At sessionStateReprAt

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

set_option maxHeartbeats 1200000 in
/-- Placed Over-path Substage P2.6 (`+0x125c → +0x1778`, or `+0x09f4` Arm 6). -/
theorem stageP2_over_sub6_v1_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (stId : ikit.IdState)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr ctxPtr msgPtr remoteAddrPtr localAddrPtr outPtr
     idStorePtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
     p1 p2 v_330 v_388 u_650
     u_298 u_2a0 u_80 u_88 u_90 u_a8 u_b8 u_d0
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp A ext coroPtr g recG sess)
    (mid : List (BitVec 8)) (hmid : mid.length = 280)
    (remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (stk : Nat) (F_rest : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hctBuf_nz : ctBufPtr ≠ 0#64)
    (hstk_sub56 : stageP2Sub56Stack skit ≤ stk)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (hstk_lt : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (henv_s : ∀ s3 : State, s3.trace = s.trace →
      Steps (stageP1ProgPlaced ext) s s3 → ikit.envOk s3.fs.files)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hOk : ∀ (localRegId : BitVec 32) (regIdFutPtr : BitVec 64) (sf : State),
      skit.regIdRel stId (.ok localRegId) →
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = stageP1EntryPlaced + 0x1778#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace ++ skit.regIdEvs (.ok localRegId) →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 →
      sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
      sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (stageP1ProgPlaced ext) ret sf
        (prevArchived1At A coroPtr recG sess ∗
         ((coroPtr + 0xf8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++
           (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
         ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
         ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
         ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
         ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x738#64) ↦₆₄ (msgPtr + 0x90#64)) ∗
         ((coroPtr + 0x740#64) ↦₈ opkPresentTag inp.opkBSk?) ∗
         opkOptFieldAt (coroPtr + 0x761#64) inp.opkBSk? ∗
         ((coroPtr + 0x781#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x398#64) ↦ₛ bytesToBv8 spkBPk) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x658#64) ↦ₛ bytesToBv8 ikBPk) ∗
         ((coroPtr + 0x678#64) ↦ₛ bytesToBv8 inp.ikBSk) ∗
         ((coroPtr + 0x6b8#64) ↦ₛ bytesToBv8 inp.spkBSk) ∗
         ((coroPtr + 0x6d8#64) ↦ₛ bytesToBv8 inp.hdr.ikAPk) ∗
         ((coroPtr + 0x6f8#64) ↦ₛ bytesToBv8 inp.hdr.ekAPk) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
         ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
         cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))) ∗
         ((coroPtr + 0x2a0#64) ↦₆₄ ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
         ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
         ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ ctBufPtr) ∗
         ((msgPtr + 0x98#64) ↦₆₄ 1569#64) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         (ctBufPtr ↦₈ 8#8) ∗
         ((ctBufPtr + 1#64) ↦₈ (bytesToBv8 inp.hdr.kemCt).getD 0 0#8) ∗
         ((ctBufPtr + 2#64) ↦ₛ (bytesToBv8 inp.hdr.kemCt).drop 1) ∗
         ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
         ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((sp + 0x90#64) ↦₆₄ v_388) ∗
         ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
         ((sp + 0xa8#64) ↦₆₄ v_330) ∗
         ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
         ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
         memRegion (sp + 0xbc#64) 4 ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
         ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
         ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
         ((sp + 0x3ac#64) ↦₈ 3#8) ∗
         ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
         ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
         ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
         ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
         ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
         ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
         memRegion (sp + 0xa90#64) 288 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp)
    (hErr : ∀ (e : skit.RegIdErr) (regIdFutPtr : BitVec 64) (s4 : State),
      skit.regIdRel stId (.error e) →
      Steps (stageP1ProgPlaced ext) s s4 →
      s4.pc = stageP1EntryPlaced + 0x9f4#64 →
      s4.status = .Running →
      s4.sp = sp →
      s4.trace = s.trace ++ skit.regIdEvs (.error e) →
      s4.readReg64 .x19 = coroPtr →
      s4.readReg64 .x21 = coroPtr + 0x390#64 →
      s4.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s4.readReg64 .x25 = s.readReg64 .x25 →
      s4.readReg64 .x26 = coroPtr + 0x398#64 →
      s4.readReg64 .x27 = ctxPtr →
      s4.readReg64 .x28 = s.readReg64 .x28 →
      s4.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s4 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem →
      SepWPp (stageP1ProgPlaced ext) ret s4
        (regIdPollOutAt skit (sp + 0x3e0#64) (.error e) ∗
         memRegion (sp + 0x410#64) 296 ∗
         memRegion (sp + 0xa90#64) 288 ∗
         ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
         ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
         A.live regIdFutPtr skit.regIdBoxSize 8 ∗
         skit.regIdBoxAt regIdFutPtr idStorePtr 1#8 ∗
         ikit.identityAt idStorePtr stId ∗
         ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
         ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
         ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
           (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
         ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗ ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         prevSessionsEmptyAt A coroPtr g ∗
         sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
         ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
         ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
         ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
         ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗ ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗ ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
         ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
         ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
         ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
         ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
         ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
         A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
         A.live kyberKpSecPtr 3168 1 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s
      (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ((sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) ∗
       memRegion (sp + 0xa90#64) 288 ∗
       memRegion (coroPtr + 0x4f8#64) 344 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       memRegion (coroPtr + 0x788#64) 16 ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
       ikit.identityAt idStorePtr stId ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  subst hsp_eq
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s.sp.isLt)
  have hrest_len : (mid ++ unpack64 0#64).length = 288 := by simp [hmid, unpack64]
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.regIdSlot hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.regIdFutDrop hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.regIdFutSize hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.regIdFutAlign hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode (fun hc hm => hskitVt.regIdFutPoll hc.2 hm) ?_
  have hsp3e0_split :
      ((s.sp + 0x3e0#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) =
      ((s.sp + 0x3e0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3e8#64) ↦₆₄ p1) ∗
      ((s.sp + 0x3f0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3f8#64) ↦₆₄ 33#64) ∗
      ((s.sp + 0x400#64) ↦₆₄ p2) ∗ ((s.sp + 0x408#64) ↦₆₄ 33#64) ∗
      ((s.sp + 0x410#64) ↦₆₄ 32#64) ∗ ((s.sp + 0x418#64) ↦ₛ (mid ++ unpack64 0#64)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      p2_sub6_bobSession344_split_56_288 (s.sp + 0x3e0#64) p1 p2 mid
  refine SepWPp.weaken_frame (Entails.of_eq hsp3e0_split) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_coro4f8_344_split_words7_288 coroPtr))
    (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 =>
    SepWPp.exists_elim fun u_508 => SepWPp.exists_elim fun u_510 =>
    SepWPp.exists_elim fun u_518 => SepWPp.exists_elim fun u_520 =>
    SepWPp.exists_elim fun u_528 => ?_
  have hc788 : memRegion (coroPtr + 0x788#64) 16 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64,
        ((coroPtr + 0x788#64) ↦₆₄ u0) ∗ ((coroPtr + 0x790#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split' (b := coroPtr + 0x788#64) (n := 8) (k := 8)
          (b' := coroPtr + 0x790#64) rfl (by bv_omega) (by decide)]
    simp only [ProofLib.memRegion_eight, sepConj_assoc, sepExists_sepConj_left]
    simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hc788) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_788 => SepWPp.exists_elim fun u_790 => ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans (p2_alloc_le_sub56_sub6 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hstep1 := p2_seg6a_hooks_placed_wp ext hH s coroPtr idStorePtr ikit.id_vt
    (0#64 + skit.regIdShimOff)
    33#64 p1 33#64 33#64 p2 33#64 32#64
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650
    (mid ++ unpack64 0#64)
    (by decide) hrest_len hpc hrun hsp_align hx19
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode hstep1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, _, _, _, _, hx25_1, _, _, hx28_1, hx29_1,
    hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim := p2_stackAt_split_of_le s.sp stk skit.regIdShimStack
    (Nat.le_trans (p2_regIdShim_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_rocl_sub5_qpan (x := idStorePtr)
    hpan hCode1 (htr1 ▸ htr) (hskitOk.regIdShim (by decide)) hpc1 hrun1 hsp1_al hx30_1
    (hsp1 ▸ p2_regIdShim_pre_intro_placed skit hx0_1)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 hst12 hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
    (hexit_false := fun _ _ => rfl) (hoom_false := fun _ => rfl)
  dsimp only [kitRegIdShimSpec]
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, _, hx25_cs2, _, _, hx28_cs2, hx29_cs2, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, _, _, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim.symm) (by sep_focus) ?_
  set regIdFutPtr : BitVec 64 := s2.readReg64 .x0
  have hstep3 := p2_seg6b_ext_placed_wp ext s2 coroPtr ctxPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) (0#64 + skit.regIdPollOff)
    (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64) u_788 u_790
    hpc2 hrun2 hsp2_align rfl hx1_2 (hx19_cs2.trans hx19_1)
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode2 hstep3
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    fun s3 hst23 hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3_2, hx0_3, _, hx8_3, hx19_3, hx21_3, hx23_3, hx25_3, hx26_3,
    hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have htr3 : s3.trace = s.trace := by rw [htr3_2, htr2_1, htr1]
  have hst03 : Steps (stageP1ProgPlaced ext) s s3 :=
    hst01.trans (hst12.trans hst23)
  refine SepWPp.weaken_frame
    (p2_sp3e0_words6_entails_memRegion48 s.sp 33#64 p1 33#64 33#64 p2 33#64) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (p2_sp410_word_bytes288_entails_memRegion296 s.sp 32#64 (mid ++ unpack64 0#64) hrest_len)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (hrest_len ▸ ProofLib.pointsToBytes_entails_memRegion (s.sp + 0xa90#64) (mid ++ unpack64 0#64))
    (by sep_focus) ?_
  have hstk_poll := p2_stackAt_split_of_le s.sp stk skit.regIdPollStack
    (Nat.le_trans (p2_regIdPoll_le_sub56 skit) hstk_sub56) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_rocl_sub5_qpan
    (x := (regIdFutPtr, s.sp + 0x3e0#64, idStorePtr, stId))
    hpan hCode3 (htr3 ▸ htr) (hskitOk.regIdPoll (by decide)) hpc3 hrun3 hsp3_al hx30_3
    (hsp3 ▸ p2_regIdPoll_pre_intro_placed skit (henv_s s3 htr3 hst03) hx0_3 hx8_3)
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s4 hst34 hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [kitRegIdPollPlacedSpecI, withLsLogOff, FromRecordCallees.lsLogOff,
    kitRegIdPollSpecE, withEnvPre, kitRegIdPollSpec]
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, hx23_cs4, _, hx25_cs4, hx26_cs4, hx27_cs4,
    hx28_cs4, hx29_cs4, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  rw [hsp3]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun ans => SepWPp.pure_elim fun ⟨hrel, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_poll.symm) (by sep_focus) ?_
  have hst04 : Steps (stageP1ProgPlaced ext) s s4 := hst03.trans hst34
  have htr4 : s4.trace = s.trace ++ skit.regIdEvs ans := by rw [htr4_3, htr3]
  have hvregs4 : calleeSavedVRegs s4 = calleeSavedVRegs s0 := by
    rw [hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = coroPtr + 0x390#64 := hx21_cs4.trans hx21_3
  have hx23_4 : s4.readReg64 .x23 = coroPtr + 0x4f2#64 := hx23_cs4.trans hx23_3
  have hx25_4 : s4.readReg64 .x25 = s.readReg64 .x25 := by
    rw [hx25_cs4, hx25_3, hx25_cs2, hx25_1]
  have hx26_4 : s4.readReg64 .x26 = coroPtr + 0x398#64 := hx26_cs4.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = ctxPtr := hx27_cs4.trans hx27_3
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := by
    rw [hx28_cs4, hx28_3, hx28_cs2, hx28_1]
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := by
    rw [hx29_cs4, hx29_3, hx29_cs2, hx29_1]
  cases ans with
  | error e =>
    have hc4f8_fold :
        ((coroPtr + 0x4f8#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x500#64) ↦₆₄ p1) ∗
        ((coroPtr + 0x508#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x510#64) ↦₆₄ 33#64) ∗
        ((coroPtr + 0x518#64) ↦₆₄ p2) ∗ ((coroPtr + 0x520#64) ↦₆₄ 33#64) ∗
        ((coroPtr + 0x528#64) ↦₆₄ 32#64) ∗ ((coroPtr + 0x530#64) ↦ₛ (mid ++ unpack64 0#64)) =
        ((coroPtr + 0x4f8#64) ↦ₛ (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ unpack64 0#64))) := by
      symm
      simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
        p2_sub6_bobSession344_split_56_288 (coroPtr + 0x4f8#64) p1 p2 mid
    refine SepWPp.weaken_frame (Entails.of_eq hc4f8_fold) (by sep_focus) ?_
    refine p2_drop_frame_sub6
      (Drop := ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (0#64 + skit.regIdShimOff)) ∗
        ((0#64 + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.regIdPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have herr := hErr e regIdFutPtr s4 hrel hst04 hpc4 hrun4 hsp4 htr4
      hx19_4 hx21_4 hx23_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 hvregs4 hCode4
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at herr
    exact p2_sepWPp_weaken_eq herr (by sep_focus)
  | ok localRegId =>
    dsimp only [regIdPollOutAt]
    have hsp3e8 : (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 := by bv_omega
    have hsp3ec : (s.sp + 0x3e0#64) + 0xc#64 = s.sp + 0x3ec#64 := by bv_omega
    rw [hsp3e8, hsp3ec]
    refine SepWPp.weaken_frame (Entails.of_eq (p2_sp3ec_36_split_for_seg6c s.sp))
      (by sep_focus) ?_
    conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u_3ec => SepWPp.exists_elim fun u_3f0 =>
      SepWPp.exists_elim fun u_3f8 => SepWPp.exists_elim fun u_400 =>
      SepWPp.exists_elim fun u_408 => ?_
    have hstep5 := p2_seg6c_ext_placed_wp ext s4 coroPtr regIdFutPtr
      (0#64 + skit.regIdFutVtOff) (0#64 + skit.regIdFutDropOff)
      (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) (coroPtr + 0x390#64)
      u_88 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 (coroPtr + 0x390#64) u_b8 u_d0
      u_3f0 u_3f8 u_400 u_408 localRegId u_3ec
      (skit.regIdFutDrop_ne_zero rfl) hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx23_4 hx26_4
    have hvt0 : (0#64 + skit.regIdFutVtOff) + 0x0#64 = 0#64 + skit.regIdFutVtOff :=
      BitVec.add_zero _
    rw [hsp4, hvt0] at hstep5
    refine p2_bind_sepWP_steps_cro_sub5_qpan hCode4 hstep5 (by sep_focus)
      fun s5 hst45 hpc5 hrun5 hCode5 hregs5 => ?_
    rcases hregs5 with ⟨hsp5, htr5_4, _, hx19_5, hx21_5, _, hx23_5, hx24_5, hx25_5, _, _,
      hx28_5, hx29_5, hx30_5, hvregs5_4⟩
    have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
    have htr05 : s0.trace <+: s5.trace :=
      htr.trans (by rw [htr5_4, htr4]; exact List.prefix_append _ _)
    refine SepWPp.weaken_frame
      (p2_sp3e0_after_seg6c_entails_344 s.sp 0xfffffffffffffffe#64 u_3f0 u_3f8 u_400 u_408
        localRegId u_3ec)
      (by sep_focus) ?_
    refine p2_call_oom_rocl_sub5_qpan (x := ()) (P_spec := emp)
      hpan hCode5 htr05 (hskitOk.regIdFutDrop (by decide)) hpc5 hrun5 hsp5_al hx30_5
      (Entails.refl emp)
      (by sep_focus) (fun _ => Entails.pure_left_only False.elim)
      (hnext := fun s6 hst56 hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
      (hexit_false := fun _ _ => rfl) (hoom_false := fun _ => rfl)
    dsimp only [LibsignalPublicApi.StoreSession.futDropSpec]
    refine SepWPp.pure_elim fun htr6_5 => ?_
    rcases hcs6 with ⟨hx19_cs6, _, hx21_cs6, _, hx23_cs6, hx24_cs6, hx25_cs6, _, _,
      hx28_cs6, hx29_cs6, hvregs6_5⟩
    have hsp6 : s6.sp = s.sp := hsp6_5.trans hsp5
    refine SepWPp.weaken_frame (skit.regIdBoxAt_memRegion regIdFutPtr idStorePtr 1#8)
      (by sep_focus) ?_
    refine p2_drop_frame_sub6
      (Drop := ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (0#64 + skit.regIdShimOff)) ∗
        ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗
        ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
        ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
        ((0#64 + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.regIdPollOff)))
      (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
    have hst06 : Steps (stageP1ProgPlaced ext) s s6 :=
      hst04.trans (hst45.trans hst56)
    have htr6 : s6.trace = s.trace ++ skit.regIdEvs (.ok localRegId) := by
      rw [htr6_5, htr5_4, htr4]
    have htr06 : s0.trace <+: s6.trace := by
      rw [htr6]
      exact htr.trans (List.prefix_append _ _)
    have hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0 := by
      rw [hvregs6_5, hvregs5_4, hvregs4]
    have hx25_6 : s6.readReg64 .x25 = s.readReg64 .x25 := by rw [hx25_cs6, hx25_5, hx25_4]
    have hx28_6 : s6.readReg64 .x28 = s.readReg64 .x28 := by rw [hx28_cs6, hx28_5, hx28_4]
    have hx29_6 : s6.readReg64 .x29 = s.readReg64 .x29 := by rw [hx29_cs6, hx29_5, hx29_4]
    exact p2_sepWPp_weaken_eq
      (stageP2_over_sub6_tail_v1_kits_ext_placed ext skit hH hskitVt hPure
        inp ikBPk spkBPk s0 s6 ret Q hpan
        s.sp coroPtr msgPtr remoteAddrPtr localAddrPtr outPtr
        regIdFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
        p1 p2 v_330 v_388
        u_298 u_2a0 u_80 u_90 u_400 u_3f0 u_3f8
        u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
        g recG sess hPromoteOver
        mid hmid localRegId remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8
        msgVerByte b_4f2 b_390 b_3ac stk
        (((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗ ((coroPtr + 0x420#64) ↦₆₄ ikit.id_vt) ∗
         ikit.identityAt idStorePtr stId ∗
         ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
         ((coroPtr + 0x790#64) ↦₆₄ (0#64 + skit.regIdFutVtOff)) ∗
         ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ memRegion (s.sp + 0xa90#64) 288 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_rest)
        hwell hctBuf_nz hstk_pure hstk_lt hCode6 hpc6 hrun6 hsp6 hsp_align htr06 hvregs6
        (hx19_cs6.trans hx19_5) (hx21_cs6.trans hx21_5) (hx23_cs6.trans hx23_5)
        (hx24_cs6.trans hx24_5)
        (fun sf hst6f hpcf hrunf hspf htrf hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
          hx25f hx26f hx27f hx28f hx29f hvregsf hCodef => by
          have hok := hOk localRegId regIdFutPtr sf hrel (hst06.trans hst6f)
            hpcf hrunf hspf (htrf.trans htr6) hx8f hx9f hx10f hx11f hx19f hx20f hx22f hx23f hx24f
            (hx25f.trans hx25_6) hx26f hx27f (hx28f.trans hx28_6) (hx29f.trans hx29_6)
            hvregsf hCodef
          exact p2_sepWPp_weaken_eq hok (by sep_focus)))
      (by sep_focus)

abbrev stageP2_over_sub6_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_over_sub6_v1_kits_ext_placed

abbrev stageP2_over_sub6_v1_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hskitOk : IdentitySelfStoreKitPlacedOkI ikit skit ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced P A F ext) :=
  stageP2_over_sub6_v1_kits_ext_placed ext skit hH hskitOk hskitVt hPure.to_4K.toStageP2BaseCalleesPlaced4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
