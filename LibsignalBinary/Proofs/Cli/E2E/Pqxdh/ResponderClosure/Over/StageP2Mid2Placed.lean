/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1V4Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Mid2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub3
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common

/-!
# Placed Stage P2 Over-Path Substages P2.1–P2.3

Proves the `[LibsignalPlacement]` Substage P2.1 outer `v4` theorem
`stageP2_over_sub1_v4_kits_ext_placed` (`+0x0868 → +0x0f14`) and the Substages P2.1–P2.3 composition
`stageP2_over_sub1_to_3_kits_ext_placed` (`+0x0868 → +0x0d5c` or Arms 1–2) on `stageP1ProgPlaced ext`.
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
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore hiding sessionRecordEmptyHeaderAt
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)
open CryptoVerification.CliHandshake.RespClosurePlaced

set_option linter.unusedSimpArgs false
set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

local macro "sep_norm" : tactic =>
  `(tactic| repeat (first
    | simp only [↓reduceIte]
    | simp only [sepExists_sepConj_left]
    | simp only [sepExists_sepConj_right]
    | simp only [emp_sepConj]
    | simp only [sepConj_emp]
    | simp only [sepConj_assoc]))

/-! ## Placed Substage P2.1 Outer `v4` (`+0x0868 → +0x0f14`) -/

set_option maxHeartbeats 1200000 in
/-- Placed Over-path Substage P2.1 (`+0x0868 → +0x0f14`, outer `v4`): serializes `baseKey`, runs
`PromoteMatchingMissAtPlacedProp` at `msgVer = 4#8` returning `Ok(false)` with the populated
1-session record intact, frees the 33-byte buffer, and invokes `spkKit.getShim`. -/
theorem stageP2_over_sub1_v4_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (hstk_shim : spkKit.getShimStack ≤ stk)
    (hstk_lt : stk ≤ 2 ^ 64)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr kyberStorePtr kyberStoreVt : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (spkId : BitVec 32) (b_4f1 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 4#8 baseKey.serialize)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt) :
    SepWPp (stageP1ProgPlaced ext) (stageP1EntryPlaced + 0xf14#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       memRegion (s.sp + 0x3e0#64) 16 ∗
       ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
       A.pool ∗
       stackAt s.sp stk)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ spkFutPtr : BitVec 64,
            ⌜sf.readReg64 .x0 = spkFutPtr ∧
              sf.readReg64 .x1 = 0#64 + spkKit.getFutVtOff ∧
              spkFutPtr ≠ 0#64 ∧
              spkFutPtr.toNat % 8 = 0⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            prevSessionsEmptyAt A coroPtr g ∗
            sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
            ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
            memRegion (s.sp + 0x3e0#64) 16 ∗
            ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
            A.live spkFutPtr spkKit.getBoxSize 8 ∗
            spkKit.getBoxAt spkFutPtr spkStorePtr spkId 0#8 ∗
            A.pool ∗
            stackAt s.sp stk) ∧
        sf.sp = s.sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x22 = spkStorePtr ∧
        sf.readReg64 .x23 = 0#64 ∧
        sf.readReg64 .x24 = spkKit.spk_vt ∧
        sf.readReg64 .x25 = s.sp + 0x210#64 ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (PanicOomProp s0) := by
  have hstk_base : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_pure
  have hstep1 := p2_seg1a_ext_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkKit.spk_vt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, hx27_1,
    hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le s.sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_lscl_steps_frame_placed
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp publicKeySerializeStack)
    hCode1 (htr1 ▸ htr) hPure.publicKeySerialize hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1]; exact Entails.pure_right hx0_1 (Entails.refl _))
    (by sep_focus) (fun _ => Entails.refl _)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, hcs2_27, hcs2_28,
    hcs2_29, hvregs2_1⟩
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkKit.spk_vt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 4#64 := hcs2_25.trans hx25_1
  have hx27_2 : s2.readReg64 .x27 = s.readReg64 .x27 := hcs2_27.trans hx27_1
  have hx28_2 : s2.readReg64 .x28 = s.readReg64 .x28 := hcs2_28.trans hx28_1
  have hx29_2 : s2.readReg64 .x29 = s.readReg64 .x29 := hcs2_29.trans hx29_1
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_seg1b_ext_placed_wp ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkKit.spk_vt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, hx22_3,
    _, hx24_3, _, hx26_3, hx27_3, hx28_3, hx29_3, hx30_3, hvregs3_2⟩
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le s.sp stk p2PromoteMissStack
    (Nat.le_trans p2_over_promoteMiss_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode3
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.subroutine_ok_withLsCodeLoaded_of_withLsCl
      hPromMiss)
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, s.sp + 0x3e0#64⟩)
    (R_pure := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (4#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = s.sp + 0x3e0#64)
    (T := prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (s.sp + 0x3e0#64) 16 ∗
      stackAt s.sp p2PromoteMissStack)
    (by dsimp only [p2PromoteMatchingMissAtSpec]; rw [hsp3])
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [p2PromoteMatchingMissAtSpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, hcs4_22, _, hcs4_24, _, hcs4_26, hcs4_27, hcs4_28,
    hcs4_29, hvregs4_3⟩
  have hsp4 : s4.sp = s.sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = spkStorePtr := hcs4_22.trans hx22_3
  have hx24_4 : s4.readReg64 .x24 = spkKit.spk_vt := hcs4_24.trans hx24_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx27_4 : s4.readReg64 .x27 = s.readReg64 .x27 := hcs4_27.trans (hx27_3.trans hx27_2)
  have hx28_4 : s4.readReg64 .x28 = s.readReg64 .x28 := hcs4_28.trans (hx28_3.trans hx28_2)
  have hx29_4 : s4.readReg64 .x29 = s.readReg64 .x29 := hcs4_29.trans (hx29_3.trans hx29_2)
  rw [hsp3,
      show (s.sp + 0x3e0#64) + 8#64 = s.sp + 0x3e8#64 by bv_omega,
      show (s.sp + 0x3e0#64) + 9#64 = s.sp + 0x3e9#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le s.sp stk allocHookStack
    (Nat.le_trans p2_alloc_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc) (by sep_focus) ?_
  have hAct_split :
      processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt kyberStorePtr kyberStoreVt =
      ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
      (((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
       ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64))) := by
    unfold processPrekeyActive10At; ac_rfl
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split) (by sep_focus) ?_
  have hstep5 := p2_seg1c_hooks_placed_wp ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    spkStorePtr spkKit.spk_vt (0#64 + spkKit.getShimOff) spkId
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx22_4 hx24_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx19_5, _, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5,
    hx27_5, hx28_5, hx29_5, hx30_5, hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp3e0_16_rejoin s.sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_shim' := p2_stackAt_split_of_le s.sp stk spkKit.getShimStack hstk_shim hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim') (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hx1_5_32 : s5.readReg32 .x1 = spkId := by
    change (s5.readReg64 .x1).setWidth 32 = spkId
    rw [hx1_5, p2_zext64_trunc32_id]
  refine p2_call_oom_rocl_steps_frame_placed
    (x := ({ self := spkStorePtr, id := spkId } : PreKeyShimCall))
    hCode5 (htr5_eq ▸ htr) (hspkOk.getShim (by decide)) hpc5 hrun5 hsp5_al hx30_5
    (hsp5 ▸ p2_spkGetShim_pre_intro_placed hx0_5 hx1_5_32)
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun sf _ hpcf hrunf hspf_5 _ hcsf hCodef => ?_)
  dsimp only [kitSpkGetShimSpec]
  rcases hcsf with ⟨hcsf_19, _, _, hcsf_22, hcsf_23, hcsf_24, hcsf_25, hcsf_26, hcsf_27, hcsf_28,
    hcsf_29, hvregsf_5⟩
  rw [hsp5]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_f, hfut_nz, hfut_al, htrf_5⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_shim'.symm) (by sep_focus) ?_
  have hvregs_full : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf_5.trans hsp5, htrf_5.trans htr5_eq,
    hcsf_19.trans hx19_5, hcsf_22.trans hx22_5, hcsf_23.trans hx23_5,
    hcsf_24.trans hx24_5, hcsf_25.trans hx25_5, hcsf_26.trans hx26_5,
    hcsf_27.trans (hx27_5.trans hx27_4), hcsf_28.trans (hx28_5.trans hx28_4),
    hcsf_29.trans (hx29_5.trans hx29_4), hvregs_full, hCodef⟩
  refine Entails.sepExists_right (sf.readReg64 .x0) ?_
  rw [← sepConj_assoc]
  refine Entails.pure_right ⟨rfl, hx1_f, hfut_nz, hfut_al⟩ ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## Placed Over-Path Substages P2.1–P2.3 (`+0x0868 → +0x0d5c` or Arms 1–2) -/

set_option maxHeartbeats 1200000 in
/-- Placed Over-path Stage P2 Substages P2.1–P2.3 (`+0x0868 → +0x0d5c` or error exit to
`s0.readReg64 .x30` via Arms 1–2). -/
theorem stageP2_over_sub1_to_3_kits_ext_placed [LibsignalPlacement]
    {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2BaseCalleesPlaced4K A ext)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64)
    (stk : Nat)
    (hstk_p2 : stageP2OverCallStack4K spkKit kpkKit pkKit skit ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop} (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr ctxPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr kyberCtCap
     v_b0 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hstk_sp : stk ≤ sp.toNat)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (signedPreKeyId kyberPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState)
    (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 4#8 baseKey.serialize)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hfs : FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
      (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s)
    (hid_spk : spkKit.idOk signedPreKeyId)
    (hspk_wf : ∀ r : SignedPreKeyRecord, spkKit.getRel stSpk signedPreKeyId (.ok r) →
      spkKit.RecOk r →
      ∃ spkPubBytes spkPrivBytes : List (BitVec 8),
        spkPubBytes.length = 32 ∧ spkPrivBytes.length = 32 ∧
        r.signedPreKey.publicKey = 5#8 :: spkPubBytes ∧ r.signedPreKey.privateKey = spkPrivBytes)
    (hid_kpk : kpkKit.getIdOk kyberPreKeyId)
    (hkpk_wf : ∀ r : KyberPreKeyRecord, kpkKit.getRel stKpk kyberPreKeyId (.ok r) →
      kpkKit.RecOk r →
      ∃ kyberPubBytes kyberPrivBytes : List (BitVec 8),
        kyberPubBytes.length = 1568 ∧ kyberPrivBytes.length = 3168 ∧
        r.signedPreKey.publicKey = 8#8 :: kyberPubBytes ∧
        r.signedPreKey.privateKey = 8#8 :: kyberPrivBytes)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
    (hrun : s.status = .Running) (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s0.trace <+: s.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx8 : s.readReg64 .x8 = kyberStorePtr) (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kpkKit.kpk_vt) (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr) (hx13 : s.readReg64 .x13 = pkKit.pk_vt)
    (hx14 : s.readReg64 .x14 = localAddrPtr) (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = ikit.id_vt) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr) (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkKit.spk_vt)
    (hErrSpk : ∀ (e : spkKit.GetErr) (spkFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt spkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.error e)) ∗
        kpkKit.storeAt kyberStorePtr stKpk ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + spkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ spkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ spkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ spkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ spkKit.getErr.w3 e) ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hErrKpk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (e : kpkKit.GetErr) (kyberFutPtr : BitVec 64) (sf : State) (P_f : SepProp),
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.error e) →
      sf.pc = s0.readReg64 .x30 → sf.status = .Running →
      sf.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.error e) →
      sf.sp = sp + 0xcd0#64 → ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (P_f ⊢
        speErrAt kpkKit.getErr outPtr e ∗
        spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
        kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.error e)) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
        ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
        cells (coroPtr + 0x3d8#64) 4 ∗
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
        ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
        ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
        ((sp + 0x90#64) ↦₆₄ kpkKit.getErr.w5 e) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ kpkKit.getErr.w4 e) ∗
        ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ kpkKit.getErr.w2 e) ∗
        ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ kpkKit.getErr.w3 e) ∗
        memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
        cells (sp + 0x930#64) 8 ∗ cells (sp + 0xa90#64) 6 ∗ memRegion (sp + 0xac0#64) 17 ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ Frame) →
      Q sf P_f)
    (hOk : ∀ (spkRec : SignedPreKeyRecord) (spkPubBytes spkPrivBytes : List (BitVec 8))
      (kpkRec : KyberPreKeyRecord) (kyberPubBytes kyberPrivBytes : List (BitVec 8))
      (pkBuf skBuf kyberFutPtr v90 privCap privPtr : BitVec 64) (s3 : State),
      Steps (stageP1ProgPlaced ext) s s3 →
      FsAt (stageP2EnvOk spkKit kpkKit pkKit ikit)
        (stageP2Quiet spkKit kpkKit pkKit skit) (stageP1ProgPlaced ext) s3 →
      spkKit.getRel stSpk signedPreKeyId (.ok spkRec) → spkKit.RecOk spkRec →
      spkPubBytes.length = 32 → spkPrivBytes.length = 32 →
      spkRec.signedPreKey.publicKey = 5#8 :: spkPubBytes →
      spkRec.signedPreKey.privateKey = spkPrivBytes →
      kpkKit.getRel stKpk kyberPreKeyId (.ok kpkRec) → kpkKit.RecOk kpkRec →
      kyberPubBytes.length = 1568 → kyberPrivBytes.length = 3168 →
      kpkRec.signedPreKey.publicKey = 8#8 :: kyberPubBytes →
      kpkRec.signedPreKey.privateKey = 8#8 :: kyberPrivBytes →
      pkBuf ≠ 0#64 → skBuf ≠ 0#64 →
      s3.pc = stageP1EntryPlaced + 0xd5c#64 →
      s3.status = .Running → s3.sp = sp →
      s3.trace = s.trace ++ spkKit.getEvs signedPreKeyId (.ok spkRec) ++
        kpkKit.getEvs kyberPreKeyId (.ok kpkRec) →
      s3.readReg64 .x19 = coroPtr → s3.readReg64 .x21 = msgPtr + 0x90#64 →
      s3.readReg64 .x22 = kyberCtCap → s3.readReg64 .x23 = coroPtr + 0x4f2#64 →
      s3.readReg64 .x25 = sp + 0x210#64 → s3.readReg64 .x26 = coroPtr + 0x398#64 →
      s3.readReg64 .x27 = ctxPtr → s3.readReg64 .x28 = sp + 0xa90#64 →
      s3.readReg64 .x29 = s.readReg64 .x29 →
      calleeSavedVRegs s3 = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem →
      SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s3
        (spkKit.storeAt spkStorePtr (spkKit.getUpdate stSpk signedPreKeyId (.ok spkRec)) ∗
         kpkKit.storeAt kyberStorePtr (kpkKit.getUpdate stKpk kyberPreKeyId (.ok kpkRec)) ∗
         (pkBuf ↦ₛ kyberPubBytes) ∗ A.live pkBuf 1568 1 ∗
         (skBuf ↦ₛ kyberPrivBytes) ∗ A.live skBuf 3168 1 ∗
         prevSessionsEmptyAt A coroPtr g ∗
         sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
         ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
         ((coroPtr + 0x398#64) ↦ₛ spkPubBytes) ∗
         ((coroPtr + 0x3b8#64) ↦ₛ clampBv8List spkPrivBytes) ∗
         ((coroPtr + 0x3d8#64) ↦₆₄ pkBuf) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x3e8#64) ↦₆₄ skBuf) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ 0xc60#64) ∗
         processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
           idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt ∗
         ((coroPtr + 0x4f1#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         ((coroPtr + 0x4f8#64) ↦₆₄ kyberFutPtr) ∗
         ((coroPtr + 0x500#64) ↦₆₄ (0#64 + kpkKit.getFutVtOff)) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
         ((sp + 0x90#64) ↦₆₄ v90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ 3169#64) ∗
         ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ privCap) ∗
         ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
         ((sp + 0xd0#64) ↦₆₄ privPtr) ∗
         memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 88 ∗
         memRegion (sp + 0x438#64) 280 ∗ cells (sp + 0x930#64) 8 ∗
         memRegion (sp + 0xa90#64) 65 ∗
         decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
         memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ Frame)
        Q Qp) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (spkKit.storeAt spkStorePtr stSpk ∗
       kpkKit.storeAt kyberStorePtr stKpk ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       cells (coroPtr + 0x398#64) 8 ∗ cells (coroPtr + 0x3d8#64) 4 ∗
       cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       cells (coroPtr + 0x4f8#64) 2 ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗ ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗ ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ v_b0) ∗ ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 368 ∗
       cells (sp + 0x930#64) 8 ∗ memRegion (sp + 0xa90#64) 65 ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       memRegion outPtr 48 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp stk ∗ Frame)
      Q Qp := by
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp_eq ▸ hsp_align
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  have hstk_p2' : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk :=
    (stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit) ▸ hstk_p2
  have hstk_base : stageP2CallStack spkKit kpkKit pkKit skit ≤ stk :=
    Nat.le_trans (p2_over_baseCall_le_callStack spkKit kpkKit pkKit skit) hstk_p2'
  have hstk_overPure : stageP2OverPureAndErrStack ≤ stk :=
    Nat.le_trans (p2_over_pure_le_callStack spkKit kpkKit pkKit skit) hstk_p2'
  have hstk_pure : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_overPure
  have hstk_dss : dropSessionStructureLocal2Stack ≤ stk :=
    Nat.le_trans p2_over_dropSS3_le_overPure hstk_overPure
  have hsp_dss : dropSessionStructureLocal2Stack ≤ sp.toNat :=
    Nat.le_trans hstk_dss hstk_sp
  have hstk_dss_split := p2_stackAt_split_of_le sp stk dropSessionStructureLocal2Stack hstk_dss hstk_lt
  refine p2_intro_spk_vt_placed hspkVt hCode ?_
  refine p2_intro_kpk_vt_placed hkpkVt hCode ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_88_280 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_16_72 sp)) (by sep_focus) ?_
  have hsub1 := stageP2_over_sub1_v4_kits_ext_placed (A := A) ext hH hPure spkKit hspkOk
    stk hstk_overPure (Nat.le_trans (p2_spkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_base) hstk_lt
    s0 s coroPtr msgPtr remoteAddrPtr localAddrPtr idStorePtr ikit.id_vt
    preKeyStorePtr pkKit.pk_vt spkStorePtr kyberStorePtr kpkKit.kpk_vt
    g recG sess baseKey signedPreKeyId b_4f1 hPromMiss hCode hpc hrun hsp_align_s htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  rw [hsp_eq] at hsub1
  refine p2_bind_sepWPp_oom_frame_qpan hpan hsub1 (by sep_focus)
    fun s1 hst01 hpc1 hrun1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx19_1, _, _, _, hx25_1, _, _, _, hx29_1, hvregs1, hCode1⟩
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := hsp1 ▸ hsp_align
  have hfs1 := hfs.of_steps hst01 (evs := []) (by rw [htr1, List.append_nil]) (fun _ => NoFsEv.nil)
  sep_norm
  refine SepWPp.exists_elim fun spkFutPtr => SepWPp.pure_elim fun ⟨hx0_1, hx1_1, _, _⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_3e0_split_16_72 sp).symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells2_4f8_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_4f8 => SepWPp.exists_elim fun u_500 => ?_
  refine SepWPp.weaken_frame (p2_cells8_398_to_keyPair64UnalignedAt coroPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun c0_i => SepWPp.exists_elim fun c1_i =>
    SepWPp.exists_elim fun c2_i => SepWPp.exists_elim fun c3_i =>
    SepWPp.exists_elim fun c4_i => SepWPp.exists_elim fun c5_i =>
    SepWPp.exists_elim fun c6_i => SepWPp.exists_elim fun c63_i =>
    SepWPp.exists_elim fun cw0_i => SepWPp.exists_elim fun cw1_i =>
    SepWPp.exists_elim fun cw2_i => SepWPp.exists_elim fun cw3_i =>
    SepWPp.exists_elim fun cw4_i => SepWPp.exists_elim fun cw5_i =>
    SepWPp.exists_elim fun cw6_i => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_cells8_930_split_7_57 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_memRegion7_to_bytes7At (sp + 0x930#64)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun s0_b => SepWPp.exists_elim fun s1_b =>
    SepWPp.exists_elim fun s2_b => SepWPp.exists_elim fun s3_b =>
    SepWPp.exists_elim fun s4_b => SepWPp.exists_elim fun s5_b =>
    SepWPp.exists_elim fun s6_b => ?_
  let Drop_vt : SepProp :=
    ((spkKit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getShimOff)) ∗
    ((0#64 + spkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + spkKit.getFutDropOff)) ∗
    ((0#64 + spkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkKit.getBoxSize) ∗
    ((0#64 + spkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((0#64 + spkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + spkKit.getPollOff)) ∗
    ((kpkKit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getShimOff)) ∗
    ((0#64 + kpkKit.getFutVtOff) ↦₆₄ᵣ (0#64 + kpkKit.getFutDropOff)) ∗
    ((0#64 + kpkKit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kpkKit.getBoxSize) ∗
    ((0#64 + kpkKit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗
    ((0#64 + kpkKit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kpkKit.getPollOff))
  refine p2_sepWPp_frame_eq
    (stageP2_sub2_kits_ext_placed (A := A) ext hH hPure
      spkKit hspkOk kpkKit hkpkOk stk hstk_pure
      (Nat.le_trans (p2_spkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_base)
      (Nat.le_trans (p2_kpkShim_le_stageP2 spkKit kpkKit pkKit skit) hstk_base) hstk_lt
      (s0.readReg64 .x30) s0 s1 _ Q hpan
      coroPtr ctxPtr msgPtr spkStorePtr spkFutPtr kyberStorePtr kyberCtCap
      (coroPtr + 0x4f2#64) v_b0 u_90 u_b8 u_d0 u_4f8 u_500
      signedPreKeyId kyberPreKeyId stSpk
      s0_b s1_b s2_b s3_b s4_b s5_b s6_b
      c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i
      hCode1 (fun sm hst htrm => p2_envOk_spk hfs1 hst htrm) hid_spk hspk_wf hkyber_nz
      hpc1 hrun1 hsp1_align (htr1 ▸ htr) hvregs1 hx0_1 hx1_1 hx19_1 ?_ ?_)
    (by rw [hsp1]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
  ·
    intro e s2 _ hrel_spk hpc2 hrun2 hsp2 htr2_1 hx19_2 hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ _
      hvregs2 hCode2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine SepWPp.weaken_frame
      (sessionAt_entails_sessionStateAt A (coroPtr + 0xf8#64) recG sess) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq hstk_dss_split) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (p2_bytes7_937_to_cells8_930 sp s0_b s1_b s2_b s3_b s4_b s5_b s6_b) (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (Entails.trans (p2_keyPair64UnalignedAt_to_memRegion (coroPtr + 0x398#64)
        c0_i c1_i c2_i c3_i c4_i c5_i c6_i c63_i cw0_i cw1_i cw2_i cw3_i cw4_i cw5_i cw6_i)
        (Entails.of_eq (ProofLib.memRegion_cells (coroPtr + 0x398#64) 8 (by decide))))
      (by sep_focus) ?_
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
        idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
      (by sep_focus) ?_
    have harm1 := p2_over_arm1_err_hooks_placed_ok (Qp := fun _ _ => False)
      hH hPure.dropSessionStructure3 hspkOk s0 s2
      sp coroPtr outPtr spkStorePtr spkFutPtr ctxPtr
      v_b0 u_90 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 u_b8 ctxPtr u_d0
      signedPreKeyId b_2c0 b_390 b_4f2 e
      g recG sess.state hCode2 hsp2 hsp_dss
      hpc2 hrun2 hsp2_align hx19_2 hx21_2 hx23_2 (hx25_2.trans hx25_1) hx26_2 hx27_2 hvregs2
    refine p2_finish_err_arm_drop (Drop := Drop_vt) harm1 (by sep_focus) ?_
      (fun sf P_f _ hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ =>
        hErrSpk e spkFutPtr sf P_f hrel_spk hpcf hrunf (by rw [htrf, htr2_1, htr1])
          hspf hcsf hvregsf hCodef hent)
    dsimp only [Drop_vt]
    rw [hstk_dss_split]
    exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
  ·
    intro spkRec spkPubBytes spkPrivBytes
      v90_2 privCap_2 privPtr_2 _ kyberFutPtr
      b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
      w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
      s2 hst12 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
      hpub_words hpriv_words hkp_lo hkp_hi
      hpc2 hrun2 hsp2 htr2_1 hx0_2 hx1_2 _ _
      hx19_2 _ hx21_2 hx23_2 hx25_2 hx26_2 hx27_2 _ hx29_2
      hvregs2 hCode2
    try rw [hsp1] at hsp2
    try rw [hsp1]
    have hst02 : Steps (stageP1ProgPlaced ext) s s2 := hst01.trans hst12
    have hfs2 := p2_fsAt_step_spk signedPreKeyId (.ok spkRec) hfs1 hst12 htr2_1
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := hsp2 ▸ hsp_align
    refine SepWPp.weaken_frame
      (Entails.of_eq (p2_keyPair64UnalignedAt_eq_bytes32_pair (coroPtr + 0x398#64)
        spkPubBytes spkPrivBytes
        b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2 b63_2 c0_2 c1_2 c2_2 c3_2 c4_2 c5_2 c6_2
        w0_2 w1_2 w2_2 w3_2 w4_2 w5_2 w6_2 u0_kp u1_kp u2_kp u3_kp u4_kp u5_kp u6_kp u7_kp
        hpub_words hpriv_words hkp_lo hkp_hi))
      (by sep_focus) ?_
    sep_norm
    refine SepWPp.weaken_frame
      (p2_bytes7_937_to_cells8_930 sp b0_2 b1_2 b2_2 b3_2 b4_2 b5_2 b6_2)
      (by sep_focus) ?_
    refine SepWPp.weaken_frame (Entails.of_eq (p2_cells4_3d8_eq coroPtr)) (by sep_focus) ?_
    sep_norm
    refine SepWPp.exists_elim fun u_3d8 => SepWPp.exists_elim fun u_3e0 =>
      SepWPp.exists_elim fun u_3e8 => SepWPp.exists_elim fun u_3f0 => ?_
    refine p2_sepWPp_frame_eq
      (stageP2_sub3_kits_ext_placed (A := A) ext hH hPure
        kpkKit hkpkOk stk hstk_pure
        (Nat.le_trans (p2_kpkPoll_le_stageP2 spkKit kpkKit pkKit skit) hstk_base) hstk_lt
        (s0.readReg64 .x30) s0 s2 _ Q hpan
        coroPtr ctxPtr msgPtr kyberFutPtr kyberStorePtr kyberCtCap
        (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) v_b0 spkFutPtr (0#64 + spkKit.getFutVtOff)
        v90_2 u_a8 privCap_2 ctxPtr privPtr_2
        u_3d8 u_3e0 u_3e8 u_3f0
        kyberPreKeyId 0#8 stKpk
        hkyber_nz hCode2 (fun sm hst htrm => p2_envOk_kpk hfs2 hst htrm) hid_kpk hkpk_wf
        hpc2 hrun2 hsp2_align
        (by rw [htr2_1, htr1]; exact htr.trans (List.prefix_append _ _))
        hvregs2 hx0_2 hx1_2 hx19_2 hx21_2 hx23_2 hx26_2 hx27_2 ?_ ?_)
      (by rw [hsp2]; (conv => rhs; simp only [← sepConj_assoc]); sep_focus)
    ·
      intro e s3 _ hrel_kpk hpc3 hrun3 hsp3 htr3_2 hx19_3 hx21_3 hx23_3 hx25_3 hx26_3 hx27_3 _ _
        hvregs3 hCode3
      try rw [hsp2] at hsp3
      try rw [hsp2]
      have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := hsp3 ▸ hsp_align
      refine SepWPp.weaken_frame
        (sessionAt_entails_sessionStateAt A (coroPtr + 0xf8#64) recG sess) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq (p2_memRegion_a90_65_to_cells6 sp)) (by sep_focus) ?_
      refine SepWPp.weaken_frame (Entails.of_eq hstk_dss_split) (by sep_focus) ?_
      have h3d8_fold :
          ((coroPtr + 0x3d8#64) ↦₆₄ u_3d8) ∗ ((coroPtr + 0x3e0#64) ↦₆₄ u_3e0) ∗
          ((coroPtr + 0x3e8#64) ↦₆₄ u_3e8) ∗ ((coroPtr + 0x3f0#64) ↦₆₄ u_3f0) ⊢
          cells (coroPtr + 0x3d8#64) 4 := by
        refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo64_entails_memRegion _ _)))) ?_
        rw [← ProofLib.memRegion_split' (b := coroPtr + 0x3e8#64) (n := 8) (k := 8)
              (b' := coroPtr + 0x3f0#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3e0#64) (n := 8) (k := 16)
              (b' := coroPtr + 0x3e8#64) rfl (by bv_omega) (by decide),
            ← ProofLib.memRegion_split' (b := coroPtr + 0x3d8#64) (n := 8) (k := 24)
              (b' := coroPtr + 0x3e0#64) rfl (by bv_omega) (by decide),
            ProofLib.memRegion_cells (coroPtr + 0x3d8#64) 4 (by decide)]
        exact Entails.refl _
      refine SepWPp.weaken_frame h3d8_fold (by sep_focus) ?_
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      have harm2 := p2_over_arm2_err_hooks_placed_ok (Qp := fun _ _ => False)
        hH hPure.dropSessionStructure3 hkpkOk s0 s3
        sp coroPtr outPtr kyberStorePtr kyberFutPtr ctxPtr
        v_b0 v90_2 (coroPtr + 0x398#64) (coroPtr + 0x4f2#64) u_a8 v_b0 privCap_2 ctxPtr privPtr_2
        kyberPreKeyId b_2c0 b_390 0#8 b_4f2 e
        g recG sess.state hCode3 hsp3 hsp_dss
        hpc3 hrun3 hsp3_align hx19_3 hx21_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1]) hx26_3 hx27_3 hvregs3
      refine p2_finish_err_arm_drop (Drop := Drop_vt) harm2 (by sep_focus) ?_
        (fun sf P_f _ hpcf hrunf htrf hent ⟨hspf, hcsf, hvregsf, hCodef⟩ =>
          hErrKpk spkRec spkPubBytes spkPrivBytes e kyberFutPtr sf P_f
            hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq hrel_kpk
            hpcf hrunf (by rw [htrf, htr3_2, htr2_1, htr1])
            hspf hcsf hvregsf hCodef hent)
      dsimp only [Drop_vt]
      rw [hstk_dss_split]
      exact Entails.of_eq (eq_of_sep_emp (by sep_focus))
    ·
      intro kpkRec kyberPubBytes kyberPrivBytes pkBuf skBuf v90_3 privCap_3 privPtr_3 s3
        hst23 hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3 htr3_2
        hx19_3 hx21_3 hx22_3 hx23_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3
        hvregs3 hCode3
      try rw [hsp2] at hsp3
      try rw [hsp2] at hx28_3
      try rw [hsp2]
      have hst03 : Steps (stageP1ProgPlaced ext) s s3 := hst02.trans hst23
      have hfs3 := p2_fsAt_step_kpk kyberPreKeyId (.ok kpkRec) hfs2 hst23 htr3_2
      refine SepWPp.weaken_frame
        (Entails.of_eq (p2_processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr ikit.id_vt preKeyStorePtr pkKit.pk_vt kyberStorePtr kpkKit.kpk_vt).symm)
        (by sep_focus) ?_
      refine p2_drop_frame_mid (Drop := Drop_vt) (by dsimp only [Drop_vt]; sep_focus) ?_
      have hok := hOk spkRec spkPubBytes spkPrivBytes kpkRec kyberPubBytes kyberPrivBytes
        pkBuf skBuf kyberFutPtr v90_3 privCap_3 privPtr_3 s3
        hst03 hfs3 hrel_spk hrec_spk hspk_pub_len hspk_priv_len hspk_pub_eq hspk_priv_eq
        hrel_kpk hrec_kpk hkyber_pub_len hkyber_priv_len hkyber_pub_eq hkyber_priv_eq
        hpkBuf_nz hskBuf_nz hpc3 hrun3 hsp3
        (by rw [htr3_2, htr2_1, htr1])
        hx19_3 hx21_3 hx22_3 hx23_3
        (by rw [hx25_3, hx25_2, hx25_1])
        hx26_3 hx27_3 hx28_3
        (by rw [hx29_3, hx29_2, hx29_1])
        hvregs3 hCode3
      exact p2_sepWPp_weaken_eq hok (by sep_focus)

abbrev stageP2_over_sub1_to_3_kits_4k_placed := @stageP2_over_sub1_to_3_kits_ext_placed

abbrev stageP2_over_sub1_to_3_kits_placed [LibsignalPlacement]
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext) (hPure : StageP2PureCalleesPlaced P A F ext)
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelfStoreSpec ikit)
    (spkKit : SignedPreKeyStoreSpec A 0#64)
    (hspkVt : SignedPreKeyVtablesPlacedOk spkKit)
    (hspkOk : SignedPreKeyStoreKitPlacedOk spkKit ext)
    (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hkpkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (hkpkOk : KyberPreKeyStoreKitPlacedOk kpkKit ext)
    (pkKit : PreKeyStoreSpec A 0#64)
    (stk : Nat)
    (hstk_p2 : stageP2OverCallStack spkKit kpkKit pkKit skit ≤ stk) :=
  stageP2_over_sub1_to_3_kits_ext_placed ext hH hPure.to_4K.toStageP2BaseCalleesPlaced4K skit
    spkKit hspkVt hspkOk kpkKit hkpkVt hkpkOk pkKit
    stk ((stageP2OverCallStack4K_eq spkKit kpkKit pkKit skit).symm ▸ hstk_p2)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
