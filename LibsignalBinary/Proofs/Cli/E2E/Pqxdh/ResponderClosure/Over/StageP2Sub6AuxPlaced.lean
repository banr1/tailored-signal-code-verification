/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2PurePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6AuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6Aux
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common

/-!
# Placed Stage P2 Over-Path Substage P2.6 Tail

Proves the `[LibsignalPlacement]` Substage P2.6 tail `stageP2_over_sub6_tail_v1_kits_ext_placed`
(`+0x0b3c → +0x1778`), archiving `sess` into `prevArchived1At` and promoting Bob's session into
`coroPtr + 0xf8` via `PromoteOverAtPlacedProp`.
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
  decryptPrekeySavedRegsAt p2BobSessHead56Bv8
  prevArchived1At sessionStateReprAt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem p2_over_alloc_le_overPure :
    allocHookStack ≤ stageP2OverPureAndErrStack :=
  Nat.le_trans p2_alloc_le_pure p2_over_basePure_le_overPure

set_option maxHeartbeats 1200000 in
/-- Placed Over-path Substage P2.6 tail (`+0x0b3c → +0x1778`) promoting the populated 1-session
record via `PromoteOverAtPlacedProp`. -/
theorem stageP2_over_sub6_tail_v1_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (inp : AcceptKeysInput) (ikBPk spkBPk : SignalPqxdh.Bytes)
    (s0 s6 : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr outPtr
     regIdFutPtr kyberKpPubPtr kyberKpSecPtr ctBufPtr
     p1 p2 v_330 v_388
     u_298 u_2a0 u_80 u_90 u_400 u_3f0 u_3f8
     u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (hPromoteOver : PromoteOverAtPlacedProp A ext coroPtr g recG sess)
    (mid : List (BitVec 8)) (hmid : mid.length = 280)
    (localRegId remoteRegId opkIdIsSome opkId kyberPreKeyId signedPreKeyId u_2a8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (stk : Nat) (F_rest : SepProp)
    (hwell : WellSizedAcceptKeysInput inp)
    (hctBuf_nz : ctBufPtr ≠ 0#64)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (hstk_lt : stk ≤ sp.toNat)
    (hCode6 : StoreKit.LibsignalCodeRoLoaded lsmpl s6.mem)
    (hpc6 : s6.pc = stageP1EntryPlaced + 0xb3c#64)
    (hrun6 : s6.status = .Running)
    (hsp6 : s6.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr06 : s0.trace <+: s6.trace)
    (hvregs6 : calleeSavedVRegs s6 = calleeSavedVRegs s0)
    (hx19_6 : s6.readReg64 .x19 = coroPtr)
    (hx21_6 : s6.readReg64 .x21 = regIdFutPtr)
    (hx23_6 : s6.readReg64 .x23 = localRegId.zeroExtend 64)
    (hx24_6 : s6.readReg64 .x24 = 0#64 + skit.regIdFutVtOff)
    (hOk : ∀ sf : State,
      Steps (stageP1ProgPlaced ext) s6 sf →
      sf.pc = stageP1EntryPlaced + 0x1778#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s6.trace →
      sf.readReg64 .x8 = coroPtr + 0xe0#64 →
      sf.readReg64 .x9 = 8#64 →
      sf.readReg64 .x10 = msgVerByte.zeroExtend 64 →
      sf.readReg64 .x11 = coroPtr + 0xf8#64 →
      sf.readReg64 .x19 = coroPtr →
      sf.readReg64 .x20 = 0xfffffffffffffffe#64 →
      sf.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 →
      sf.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) →
      sf.readReg64 .x25 = s6.readReg64 .x25 →
      sf.readReg64 .x26 = v_330 →
      sf.readReg64 .x27 = sp + 0x370#64 →
      sf.readReg64 .x28 = s6.readReg64 .x28 →
      sf.readReg64 .x29 = s6.readReg64 .x29 →
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
         A.pool ∗ stackAt sp stk ∗ F_rest)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) ret s6
      (bobParamsFieldsAt (coroPtr + 0x658#64) kyberKpSecPtr (msgPtr + 0x90#64) ctBufPtr
         (coroPtr + 0x398#64) inp ikBPk spkBPk 0#8 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x500#64) ↦₆₄ p1) ∗
       ((coroPtr + 0x508#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x510#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x518#64) ↦₆₄ p2) ∗
       ((coroPtr + 0x520#64) ↦₆₄ 33#64) ∗
       ((coroPtr + 0x528#64) ↦₆₄ 32#64) ∗
       ((coroPtr + 0x530#64) ↦ₛ (mid ++ unpack64 0#64)) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       memRegion (sp + 0x3e0#64) 344 ∗
       A.live regIdFutPtr skit.regIdBoxSize 8 ∗
       memRegion regIdFutPtr skit.regIdBoxSize ∗
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
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_400) ∗
       ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗ ((sp + 0xb8#64) ↦₆₄ u_3f0) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_3f8) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       A.live kyberKpPubPtr 1568 1 ∗
       memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗
       A.pool ∗ stackAt sp stk ∗ F_rest)
      Q Qp := by
  subst hsp6
  have hstk_le64 : stk ≤ 2 ^ 64 := Nat.le_trans hstk_lt (Nat.le_of_lt s6.sp.isLt)
  refine p2_sepWPp_intro_ro_placed hCode6 (fun hc hm => hskitVt.regIdFutSize hc.2 hm) ?_
  refine p2_sepWPp_intro_ro_placed hCode6 (fun hc hm => hskitVt.regIdFutAlign hc.2 hm) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (bobParamsFieldsAt_intro coroPtr msgPtr kyberKpSecPtr ctBufPtr inp ikBPk
      spkBPk).symm)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (pqsk_entails_memRegion3168 kyberKpSecPtr inp.pqspkBSk
    hwell.2.2.2.2.2.1)
    (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s6.sp stk allocHookStack
    (Nat.le_trans p2_over_alloc_le_overPure hstk_pure) hstk_le64
  have hstk_prom := p2_stackAt_split_of_le s6.sp stk p2PromoteStackX
    (Nat.le_trans p2_over_promoteOver_le_overPure hstk_pure) hstk_le64
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have h530_split := p2_sub6_bobSession288Rest_split_280_4_4 (coroPtr + 0x530#64) mid hmid
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h530_split
  refine SepWPp.weaken_frame (Entails.of_eq h530_split) (by sep_focus) ?_
  have hstep7 := p2_seg6d1_gen_hooks_placed_wp ext hH s6 coroPtr msgPtr regIdFutPtr
    (0#64 + skit.regIdFutVtOff) localRegId remoteRegId 0#32 0#32 skit.regIdBoxSize
    hpc6 hrun6 hsp_align skit.regIdBoxSize_ne_zero skit.regIdBoxSize_lt
    hx19_6 hx21_6 hx23_6 hx24_6
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode6 hstep7 (by sep_focus)
    fun s7 hst67 hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7, hx0_7, hx1_7, hx2_7, hx19_7, hx21_7, _, _, _, hx25_7, _, _,
    hx28_7, hx29_7, hvregs7⟩
  have hsp7_align : (s7.sp &&& 15#64 == 0#64) = true := by rw [hsp7]; exact hsp_align
  refine p2_drop_frame_sub6
    (Drop := ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗
             ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64))
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) ?_
  have h4f8_fold := p2_sub6_bobSession344WithRegIds_fold (coroPtr + 0x4f8#64) p1 p2 mid hmid
    remoteRegId localRegId
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4f8_fold
  refine SepWPp.weaken_frame (Entails.of_eq h4f8_fold) (by sep_focus) ?_
  have hx0_7' : s7.readReg64 .x0 = s7.sp + 0x3e0#64 := by rw [hx0_7, hsp7]
  have hssWithReg_len :=
    p2_sub6_bobSession344WithRegIds_length p1 p2 mid hmid remoteRegId localRegId
  have hstep8 := p2_seg6d2_hooks_placed_wp ext hH s7 coroPtr
    (p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId)))
    hssWithReg_len hpc7 hrun7 hsp7_align hx0_7' hx1_7 hx2_7 hx19_7 hx21_7
  rw [hsp7] at hstep8
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode7 hstep8 (by sep_focus)
    fun s8 hst78 hpc8 hrun8 hCode8 hregs8 => ?_
  rcases hregs8 with ⟨hsp8, htr8, hx0_8, hx1_8, hx19_8, _, _, _, _, hx25_8, _, _, hx28_8, hx29_8,
    hx30_8, hvregs8⟩
  have hsp8_al : s8.spAligned = true := by simpa only [State.spAligned, hsp8] using hsp_align
  have htr08 : s0.trace <+: s8.trace := by rw [htr8, htr7]; exact htr06
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hpc8_eq :
      libsignalSessionLib.resolve lsmpl
        "<libsignal_protocol::state::session::SessionRecord>::promote_state" = lsmpl.base 47 :=
    BitVec.add_zero _
  rw [hpc8_eq] at hpc8
  let newBs := p2BobSessHead56Bv8 p1 p2 ++ (mid ++ (unpack32 remoteRegId ++ unpack32 localRegId))
  refine p2_call_oom_lscl_steps_frame_qpan
    (x := P2PromoteOverCallGhost.mk (s6.sp + 0x3e0#64) newBs)
    (P_spec := prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      A.pool ∗ ((s6.sp + 0x3e0#64) ↦ₛ newBs) ∗ stackAt s6.sp p2PromoteStackX)
    hpan hCode8 htr08
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.subroutine_ok_withLsCodeLoaded_of_withLsCl
      hPromoteOver)
    hpc8 hrun8 hsp8_al hx30_8
    (by
      dsimp only [p2PromoteOverAtSpec]
      rw [hsp8]
      exact Entails.pure_right ⟨hx0_8, hx1_8, hssWithReg_len⟩ (Entails.refl _))
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s9 hst89 hpc9 hrun9 hsp9_8 _ hcs9 hCode9 => ?_)
  dsimp only [p2PromoteOverAtSpec, newBs]
  rw [hsp8, prevArchived1At_eq A coroPtr recG sess, sepConj_assoc]
  refine SepWPp.pure_elim fun htr9_8 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hsp9 : s9.sp = s6.sp := hsp9_8.trans hsp8
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := by rw [hsp9]; exact hsp_align
  rcases hcs9 with ⟨hx19_cs9, _, _, _, _, _, hx25_cs9, _, _, hx28_cs9, hx29_cs9, hvregs9_8⟩
  have hx19_9 : s9.readReg64 .x19 = coroPtr := hx19_cs9.trans hx19_8
  have hx25_9 : s9.readReg64 .x25 = s6.readReg64 .x25 := by rw [hx25_cs9, hx25_8, hx25_7]
  have hx28_9 : s9.readReg64 .x28 = s6.readReg64 .x28 := by rw [hx28_cs9, hx28_8, hx28_7]
  have hx29_9 : s9.readReg64 .x29 = s6.readReg64 .x29 := by rw [hx29_cs9, hx29_8, hx29_7]
  have hstep10 := p2_seg6e_1568_hooks_placed_wp ext hH s9 coroPtr msgPtr ctBufPtr
    kyberKpPubPtr kyberKpSecPtr outPtr u_400 u_3f8
    opkIdIsSome opkId kyberPreKeyId signedPreKeyId 0#8 b_4f2
    hctBuf_nz hpc9 hrun9 hsp9_align hx19_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode9 hstep10 (by sep_focus)
    fun s10 hst910 hpc10 hrun10 hCode10 hregs10 => ?_
  rcases hregs10 with ⟨hsp10, htr10, hx0_10, hx19_10, hx20_10, _, hx22_10, hx23_10, hx24_10,
    hx25_10, _, _, hx28_10, hx29_10, hx30_10, hvregs10⟩
  have hsp10_al : s10.spAligned = true := by simpa only [State.spAligned, hsp10] using hsp_align
  have hstk48 : stackAt s6.sp allocHookStack =
      stackAt (s6.sp - 48#64) (allocHookStack - 48) ∗ cells (s6.sp - 48#64) 6 :=
    ProofLib.stackAt_split_cells s6.sp (allocHookStack - 48) 6 (by decide)
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  have hpc10_eq :
      libsignalSessionLib.resolve lsmpl
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" =
      lsmpl.base 509 :=
    BitVec.add_zero _
  rw [hpc10_eq] at hpc10
  refine p2_call_nopanic_lscl_steps_frame_placed (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (s6.sp - 48#64) 6)
    hCode10 hPure.dropProcessPrekeyImplState1 hpc10 hrun10 hsp10_al hx30_10
    (by
      dsimp only [dropProcessPrekeyImplState1Spec]
      rw [hsp10,
          show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl])
    hx0_10 (by sep_focus)
    (hnext := fun s11 hst1011 hpc11 hrun11 hsp11_10 _ hcs11 hCode11 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp10,
      show (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 by rw [BitVec.add_assoc]; rfl,
      sepConj_assoc]
  refine SepWPp.pure_elim fun htr11_10 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hsp11 : s11.sp = s6.sp := hsp11_10.trans hsp10
  have hsp11_align : (s11.sp &&& 15#64 == 0#64) = true := by rw [hsp11]; exact hsp_align
  rcases hcs11 with ⟨hx19_cs11, hx20_cs11, _, hx22_cs11, hx23_cs11, hx24_cs11, hx25_cs11, _, _,
    hx28_cs11, hx29_cs11, hvregs11_10⟩
  have hx19_11 : s11.readReg64 .x19 = coroPtr := hx19_cs11.trans hx19_10
  have hx20_11 : s11.readReg64 .x20 = 0xfffffffffffffffe#64 := hx20_cs11.trans hx20_10
  have hx22_11 : s11.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 :=
    hx22_cs11.trans hx22_10
  have hx23_11 : s11.readReg64 .x23 = opkIdIsSome.zeroExtend 64 := hx23_cs11.trans hx23_10
  have hx24_11 : s11.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) :=
    hx24_cs11.trans hx24_10
  have hx25_11 : s11.readReg64 .x25 = s6.readReg64 .x25 := by rw [hx25_cs11, hx25_10, hx25_9]
  have hx28_11 : s11.readReg64 .x28 = s6.readReg64 .x28 := by rw [hx28_cs11, hx28_10, hx28_9]
  have hx29_11 : s11.readReg64 .x29 = s6.readReg64 .x29 := by rw [hx29_cs11, hx29_10, hx29_9]
  have hhead_split := p2_sub6_bobSession344WithRegIds_head_split (coroPtr + 0xf8#64) p1 p2 mid
    remoteRegId localRegId
  rw [show (coroPtr + 0xf8#64) + 8#64 = coroPtr + 0x100#64 by
    rw [BitVec.add_assoc]; rfl] at hhead_split
  refine SepWPp.weaken_frame (Entails.of_eq hhead_split) (by sep_focus) ?_
  refine SepWPp.weaken_frame (cells6_250_split_for_seg6f coroPtr) (by sep_focus) ?_
  conv => arg 4; simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun u_250 => SepWPp.exists_elim fun u_258 =>
    SepWPp.exists_elim fun u_260 => SepWPp.exists_elim fun u_268 =>
    SepWPp.exists_elim fun u_26c => SepWPp.exists_elim fun u_270 =>
    SepWPp.exists_elim fun u_278 => ?_
  have hb8_split : ((s6.sp + 0xb8#64) ↦₆₄ u_3f0) =
      ((s6.sp + 0xb8#64) ↦₃₂ (u_3f0.extractLsb' 0 32)) ∗
      ((s6.sp + 0xbc#64) ↦₃₂ (u_3f0.extractLsb' 32 32)) := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo64_split32 (s6.sp + 0xb8#64) u_3f0
  refine SepWPp.weaken_frame (Entails.of_eq hb8_split) (by sep_focus) ?_
  have hpack_lo : ((opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32)) &&& 0xff#64) =
      (opkIdIsSome.zeroExtend 64 &&& 0xff#64) := by bv_kernel
  have hstep12 := p2_seg6f_ext_placed_wp ext s11 coroPtr msgPtr remoteAddrPtr localAddrPtr
    (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))
    ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)
    33#64 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 0xfffffffffffffffe#64 u_90 (coroPtr + 0x4f2#64) 0#64 (coroPtr + 0x390#64)
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 (u_3f0.extractLsb' 0 32)
    msgVerByte b_390 b_3ac
    (by decide) hpack_lo hpc11 hrun11 hsp11_align hx19_11 hx20_11 hx22_11 hx23_11 hx24_11
  rw [hsp11] at hstep12
  have hsub_3b0 : s6.sp + 0x3b0#64 - (s6.sp + 0x3b0#64) + u_3b0 = u_3b0 := by bv_omega
  rw [hsub_3b0] at hstep12
  refine p2_bind_sepWP_steps_cro_sub5_qpan hCode11 hstep12 (by sep_focus)
    fun sf hst11f hpcf hrunf hCodef hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx8_f, hx9_f, hx10_f, hx11_f, hx19_f, hx20_f,
    hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregsf⟩
  refine SepWPp.weaken_frame (Entails.of_eq hhead_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (cells6_250_fold coroPtr 0xfffffffffffffffe#64
      (opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32))
      ((kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64)
      v_330 v_388 signedPreKeyId ((s11.readReg64 (Reg.gpr 11#5)).truncate 32))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (pointsTo32_entails_memRegion (s6.sp + 0xbc#64) (u_3f0.extractLsb' 32 32))
    (by sep_focus) ?_
  have hsteps_6f : Steps (stageP1ProgPlaced ext) s6 sf :=
    hst67.trans (hst78.trans (hst89.trans (hst910.trans (hst1011.trans hst11f))))
  have htr_6f : sf.trace = s6.trace := by
    rw [htrf, htr11_10, htr10, htr9_8, htr8, htr7]
  have hvregs_f : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf, hvregs11_10, hvregs10, hvregs9_8, hvregs8, hvregs7, hvregs6]
  have hok := hOk sf hsteps_6f hpcf hrunf hspf htr_6f hx8_f hx9_f hx10_f hx11_f
    hx19_f hx20_f hx22_f hx23_f hx24_f
    (hx25_f.trans hx25_11) hx26_f hx27_f
    (hx28_f.trans hx28_11) (hx29_f.trans hx29_11)
    hvregs_f hCodef
  exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_over_sub6_tail_v1_kits_4k_placed [LibsignalPlacement] :=
  @stageP2_over_sub6_tail_v1_kits_ext_placed

abbrev stageP2_over_sub6_tail_v1_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hskitVt : IdentitySelfVtablesPlacedOk ikit skit)
    (hPure : StageP2PureCalleesPlaced P A F ext) :=
  stageP2_over_sub6_tail_v1_kits_ext_placed ext skit hH hskitVt hPure.to_4K.toStageP2BaseCalleesPlaced4K

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
