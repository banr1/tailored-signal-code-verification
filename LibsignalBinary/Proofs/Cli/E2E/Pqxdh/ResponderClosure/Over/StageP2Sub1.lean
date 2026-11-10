/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Defs
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Tail
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1V4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3Steps
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common -- shake: keep

/-!
# Stage P2 Over-Path Substage P2.1 and Outer `v3` Reject Path

Re-exports `stageP2_over_sub1_v4_kits` and proves the outer `v3` (`msgVer = 3#8`) reject path
(`+0x0868 → s0.readReg64 .x30`), which runs `promote_matching_session` returning `Ok(false)`,
allocates `"X3DH no longer supported"`, drops the `process_prekey_impl` state and `SessionRecord`,
and writes `.error (.protocol (.invalidMessage .preKey .badCiphertext))` to `outPtr`.
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
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
  decryptPrekeySavedRegsAt

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

private theorem p2_strToOwnedStack_le_overPure :
    Matched.strToOwnedLocal2Stack ≤ stageP2OverPureAndErrStack := by
  decide

private theorem p2_cells48_le_overPure : 48 ≤ stageP2OverPureAndErrStack := by
  decide

private theorem p2_stackAt_48_cells6 (sp : BitVec 64) :
    stackAt sp 48 = cells (sp - 48#64) 6 := by
  change memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

private theorem p2_sessionAt_entails_state (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionStateReprAt A ss G sess ⊢ sessionStateAt A ss G sess.state := by
  unfold sessionStateReprAt
  exact Entails.pure_left fun _ => Entails.refl _

/-! ## Outer `v3` Reject Path (`+0x0868 → s0.readReg64 .x30`) -/

set_option maxHeartbeats 1200000 in
/-- `PanicOomProp s0` specification for the outer `v3` reject path (`+0x0868 → s0.readReg64 .x30`). -/
theorem stageP2_over_v3_oom {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hPure : StageP2PureCallees P A F img ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtProp A img ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_sp : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
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
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk)
      (fun sf P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ 24#64) ∗
          memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3e0#64) 24 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          logOff img ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp stk) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      (PanicOomProp s0) := by
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  have hstk_base : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_pure
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp_eq ▸ hsp_align
  let roAddr : BitVec 64 :=
    img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))
  refine p2_intro_rodata_x3dhUnsupported himg hF ?_
  have hstep1 := p2_over_seg1a_v3_ext_wp img.base ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, _,
    hx28_1, _, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  rw [p2_fnAddr_pkSerialize_eq] at hpc1
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_frame_frozen_oom_prefix hF1 hsym1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt sp publicKeySerializeStack)
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (by intro _; rfl) (by intro _ _; rfl)
    fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 _ => ?_
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, _, hcs2_28, _, hvregs2_1⟩
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkStoreVt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 3#64 := hcs2_25.trans hx25_1
  have hx28_2 : s2.readReg64 .x28 = sp + 0xa90#64 := hcs2_28.trans (hx28_1.trans hx28)
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_over_seg1b_v3_ext_wp img.base ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkStoreVt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, _,
    _, _, _, hx26_3, _, hx28_3, _, hx30_3, hvregs3_2⟩
  rw [p2_fnAddr_promoteMatching_eq] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le sp stk p2PromoteMissStack
    (Nat.le_trans p2_over_promoteMiss_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sp3e0_24_split_16_8 sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF3 hsym3 hPromMiss
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, sp + 0x3e0#64⟩)
    (φ := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (3#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64)
    (T := prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (sp + 0x3e0#64) 16 ∗
      stackAt sp p2PromoteMissStack)
    (by dsimp only [p2PromoteMatchingMissAtSpec]; rw [hsp3])
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [p2PromoteMatchingMissAtSpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, _, _, _, _, hcs4_26, _, hcs4_28, _, hvregs4_3⟩
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx28_4 : s4.readReg64 .x28 = sp + 0xa90#64 := hcs4_28.trans (hx28_3.trans hx28_2)
  rw [hsp3,
      show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e0#64) + 9#64 = sp + 0x3e9#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
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
  have hstep5 := p2_over_seg1c_v3_ext_wp img.base ext hA s4 coroPtr msgPtr (s2.readReg64 .x0)
    hb hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_steps_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx2_5, hx19_5, hx25_5, _, hx28_5, _, hx30_5,
    hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp3e0_24_rejoin sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_to := p2_stackAt_split_of_le sp stk Matched.strToOwnedLocal2Stack
    (Nat.le_trans p2_strToOwnedStack_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to) (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hto := Matched.str_to_owned_local2_ok_ext (A := A) (b := img.base) (ext := ext) hA hRO
  refine p2_call_oom_steps_frame
    (spec := Matched.strToOwnedLocal2Spec A)
    (x := (sp + 0x3e0#64, roAddr, x3dhUnsupportedStr))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ x3dhUnsupportedStr) ∗ A.pool ∗
      stackAt sp Matched.strToOwnedLocal2Stack)
    hF5 hsym5 (htr5_eq ▸ htr) hto hpc5 hrun5 hsp5_al hx30_5
    (by
      dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
      rw [hsp5, x3dhUnsupportedStr_length]
      exact Entails.pure_right ⟨hx0_5, hx1_5, hx2_5, by decide, by decide⟩ (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s6 _ hpc6 hrun6 hsp6_5 _ hcs6 hF6 hsym6 => ?_)
  dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
  rw [hsp5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6_5 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to.symm) (by sep_focus) ?_
  refine Matched.SepWPp.drop_ro_frame (D := roAddr ↦ᵣ x3dhUnsupportedStr) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.vecU8_unpack_3e0_64 A sp x3dhUnsupportedStr)
    (by sep_focus) ?_
  rw [x3dhUnsupportedStr_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs6 with ⟨hcs6_19, _, _, _, _, _, hcs6_25, _, _, hcs6_28, _, hvregs6_5⟩
  have hsp6 : s6.sp = sp := hsp6_5.trans hsp5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := hsp6 ▸ hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6_19.trans hx19_5
  have hx25_6 : s6.readReg64 .x25 = sp + 0x210#64 := hcs6_25.trans hx25_5
  have hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64 := hcs6_28.trans (hx28_5.trans hx28_4)
  have hstep7 := p2_over_seg1d_v3_to_drop_ext_wp img.base ext s6 coroPtr outPtr cap ptr 24#64
    u_a8 u_d0 b_4f2 hpc6 hrun6 hsp6_align hx19_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_frame hF6 hsym6 hstep7 (by sep_focus)
    fun s7 _ hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hvregs7_6, hx0_7, hx19_7, hx20_7, hx21_7, hx22_7,
    hx23_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7⟩
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  rw [Matched.dropProcessPrekeyImpl_addr_eq_ext img.base ext] at hpc7
  have hstk48 : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ cells (sp - 48#64) 6 := by
    rw [p2_stackAt_split_of_le sp stk 48 (Nat.le_trans p2_cells48_le_overPure hstk_pure) hstk_lt,
        p2_stackAt_48_cells6]
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF7 hsym7
    (Matched.drop_process_prekey_impl_state1_ok_ext (b := img.base) (ext := ext))
    hpc7 hrun7 hsp7_al hx30_7
    (x := coroPtr + 0x398#64)
    (φ := s7.readReg64 .x0 = coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp7, Matched.coro_398_add_15a])
    hx0_7 (by sep_focus)
    (hnext := fun s8 _ hpc8 hrun8 hsp8_7 _ hcs8 hF8 hsym8 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp7, Matched.coro_398_add_15a, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  rcases hcs8 with ⟨hcs8_19, hcs8_20, hcs8_21, hcs8_22, hcs8_23, hcs8_24,
    hcs8_25, hcs8_26, _, hcs8_28, _, hvregs8_7⟩
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := hsp8 ▸ hsp_align
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hcs8_19.trans hx19_7
  have hx20_8 : s8.readReg64 .x20 = 0x8000000000000018#64 := hcs8_20.trans hx20_7
  have hx21_8 : s8.readReg64 .x21 = 0#64 := hcs8_21.trans hx21_7
  have hx22_8 : s8.readReg64 .x22 = ptr := hcs8_22.trans hx22_7
  have hx23_8 : s8.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 := hcs8_23.trans hx23_7
  have hx24_8 : s8.readReg64 .x24 = cap := hcs8_24.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by
    rw [hsp8]; exact hcs8_25.trans (hx25_7.trans hx25_6)
  have hx26_8 : s8.readReg64 .x26 = outPtr := hcs8_26.trans hx26_7
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by
    rw [hsp8]; exact hcs8_28.trans (hx28_7.trans hx28_6)
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_370_36_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (Matched.coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 =>
    SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u390 => ?_
  have hstep9 := Matched.p2_seg_1698_mismatch_to_3588_ext_wp img.base ext s8 coroPtr outPtr cap ptr
    24#64 u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hb hpc8 hrun8 hsp8_align
    hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx28_8
  rw [hsp8] at hstep9
  refine p2_bind_sepWP_steps_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 _ hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9_8, hvregs9_8, hx19_9, hx22_9, hx25_9, hx26_9, hx28_9, _, _⟩
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := hsp9 ▸ hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Matched.coro_250_6w_entails_cells6 coroPtr 0x8000000000000018#64 cap ptr 24#64 3#64
      (s8.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.a90_mismatch_entails_memRegion48 sp cap ptr 24#64
    (s8.readReg64 .x27)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.w64_3_entails_memRegion24 (sp + 0x3e0#64) cap ptr 24#64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sessionAt_entails_state A (coroPtr + 0xf8#64) recG sess)
    (by sep_focus) ?_
  have hdss_sp : dropSessionStructureLocal2Stack ≤ sp.toNat :=
    Nat.le_trans (Nat.le_trans p2_over_dropSS3_le_overPure hstk_pure) hstk_sp
  have hstk_dss := p2_stackAt_split_of_le sp stk dropSessionStructureLocal2Stack
    (Nat.le_trans p2_over_dropSS3_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_dss) (by sep_focus) ?_
  have hdropTail := Matched.closure_err_drop_record_tail_ext_ok (Qp := fun _ _ => False)
    hA (GenP3.drop_session_structure3_ok_ext hA) s0 s9
    sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
    ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32)
    ((s8.readReg64 .x27).extractLsb' 32 32)
    b_2c0 g recG sess.state
    ⟨hF9, hsym9⟩ hsp9 hdss_sp hpc9 hrun9 hsp9_align
    hx19_9 hx22_9 hx25_9 hx26_9 hx28_9
  refine p2_bind_sepWPp_nopanic_frame (Qp := PanicOomProp s0) hdropTail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_9, hcsf, hvregsf_9, hinvf⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_dss.symm) (by sep_focus) ?_
  have hinv_msg :
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ (s8.readReg64 .x27).extractLsb' 32 32) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr
         x3dhUnsupportedStr) ⊢
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := by
    have hm := Matched.invalidMessage_prekey_out_entails_3 A outPtr cap ptr (s8.readReg64 .x27)
      x3dhUnsupportedStr
    rw [x3dhUnsupportedStr_length] at hm
    exact hm
  refine SepWPp.weaken_frame hinv_msg (by sep_focus) ?_
  have htr_all : sf.trace = s.trace := by
    rw [htrf_9, htr9_8, htr8_7, htr7_6, htr6_5, htr5_eq]
  have hvregs7_6' : calleeSavedVRegs s7 = calleeSavedVRegs s6 := by
    unfold calleeSavedVRegs; rw [hvregs7_6]
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_9, hvregs9_8, hvregs8_7, hvregs7_6',
        hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htr_all, hcsf, hvregs_all, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
/-- Framed polymorphic-`Qp` specification for the outer `v3` reject path (`+0x0868 → s0.readReg64 .x30`). -/
theorem stageP2_over_v3_kits {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hPure : StageP2PureCallees P A F img ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtProp A img ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_sp : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
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
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hOut : ∀ (sf : State) (P_f : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp + 0xcd0#64 →
      sf.trace = s.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      (P_f ⊢
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
          kyberStorePtr kyberStoreVt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
        ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗
        cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
        ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
        ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
        ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ 24#64) ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3e0#64) 24 ∗
        memRegion (sp + 0xa90#64) 48 ∗
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        logOff img ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        A.pool ∗
        stackAt sp stk ∗
        Frame) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk ∗
       Frame)
      Q Qp := by
  have hoom := stageP2_over_v3_oom (P := P) (A := A) (F := F) img ext himg hA hRO hPure
    stk hstk_pure s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt u_a8 u_d0
    g recG sess baseKey b_2c0 b_390 b_4f1 b_4f2 hPromMiss hb hstk_sp
    hF hsym hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
  refine p2_bind_sepWPp_oom_frame_qpan hpan hoom (by sep_focus)
    fun sf hsteps hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf
    (hOut sf _ hsteps hpcf hrunf hspf htrf hcsf hvregsf hinvf ?_)
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## Contract-Backed Outer `v3` Reject Path -/

set_option maxHeartbeats 1200000 in
/-- `StageP2ClosureHooks` / `AllocContractsX` `PanicOomProp s0` specification for the outer `v3`
reject path (`+0x0868 → s0.readReg64 .x30`). -/
theorem stageP2_over_v3_oom_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {roStack : Nat}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext)
    (hAX : AllocContractsX img A ext)
    (hro_le : roStack ≤ extHookStack)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStack))
    (hPure : StageP2PureCallees4K P A F img ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtPropExt A img ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_sp : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
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
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk)
      (fun sf P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ 24#64) ∗
          memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3e0#64) 24 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          logOff img ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp stk) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        ImgCallInv img sf)
      (PanicOomProp s0) := by
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  have hstk_base : stageP2PureAndErrStack ≤ stk :=
    Nat.le_trans p2_over_basePure_le_overPure hstk_pure
  have hsp_align_s : (s.sp &&& 15#64 == 0#64) = true := hsp_eq ▸ hsp_align
  let roAddr : BitVec 64 :=
    img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2608) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 2612))
  refine p2_intro_rodata_x3dhUnsupported himg hF ?_
  have hstep1 := p2_over_seg1a_v3_ext_wp img.base ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_steps_frame hF hsym hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hF1 hsym1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, _,
    hx28_1, _, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  rw [p2_fnAddr_pkSerialize_eq] at hpc1
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le sp stk publicKeySerializeStack
    (Nat.le_trans p2_pkSerStack_le_pure hstk_base) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_frame_frozen_oom_prefix hF1 hsym1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (T := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt sp publicKeySerializeStack)
    (by dsimp only [publicKeySerializeSpec]; rw [hsp1])
    hx0_1 (by sep_focus)
    (by intro _; rfl) (by intro _ _; rfl)
    fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 _ => ?_
  dsimp only [publicKeySerializeSpec]
  rcases hcs2 with ⟨hcs2_19, _, _, hcs2_22, hcs2_23, hcs2_24, hcs2_25, _, _, hcs2_28, _, hvregs2_1⟩
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hcs2_19.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hcs2_22.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hcs2_23.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkStoreVt := hcs2_24.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = 3#64 := hcs2_25.trans hx25_1
  have hx28_2 : s2.readReg64 .x28 = sp + 0xa90#64 := hcs2_28.trans (hx28_1.trans hx28)
  rw [hsp1]
  sep_norm
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
  refine SepWPp.weaken_frame (p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := p2_over_seg1b_v3_ext_wp img.base ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkStoreVt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_steps_frame hF2 hsym2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hF3 hsym3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, _,
    _, _, _, hx26_3, _, hx28_3, _, hx30_3, hvregs3_2⟩
  rw [p2_fnAddr_promoteMatching_eq] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le sp stk p2OverPromoteMissStackExt
    (Nat.le_trans p2_over_promoteMissExt_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (p2_sp3e0_24_split_16_8 sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF3 hsym3 hPromMiss
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, sp + 0x3e0#64⟩)
    (φ := (img.FrozenLoaded s3 ∧ s3.symtab = img.symtab) ∧
      (s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (3#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64))
    (T := prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (sp + 0x3e0#64) 16 ∗
      stackAt sp p2OverPromoteMissStackExt)
    (by dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt]; rw [hsp3, pure_sepConj_pure_assoc])
    ⟨⟨hF3, hsym3⟩, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hF4 hsym4 => ?_)
  dsimp only [Spec.inImage, p2PromoteMatchingMissAtSpecExt]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, _, _, _, _, hcs4_26, _, hcs4_28, _, hvregs4_3⟩
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx28_4 : s4.readReg64 .x28 = sp + 0xa90#64 := hcs4_28.trans (hx28_3.trans hx28_2)
  rw [hsp3,
      show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega,
      show (sp + 0x3e0#64) + 9#64 = sp + 0x3e9#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
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
  have hstep5 := p2_over_seg1c_v3_hooks_wp img.base ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    hb hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_steps_frame hF4 hsym4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hF5 hsym5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx2_5, hx19_5, hx25_5, _, hx28_5, _, hx30_5,
    hvregs5_4⟩
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sp3e0_24_rejoin sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_to := p2_stackAt_split_of_le sp stk (Matched.strToOwnedLocal2StackWith extHookStack)
    (Nat.le_trans p2_over_strToOwnedX_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to) (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  have hto := Matched.str_to_owned_local2_ok_ext_x (img := img) (A := A) (ext := ext) hAX hro_le hRO
  refine p2_call_oom_steps_frame
    (spec := (Matched.strToOwnedLocal2SpecWithStack extHookStack A).inImage img)
    (x := (sp + 0x3e0#64, roAddr, x3dhUnsupportedStr))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ x3dhUnsupportedStr) ∗ A.pool ∗
      stackAt sp (Matched.strToOwnedLocal2StackWith extHookStack))
    hF5 hsym5 (htr5_eq ▸ htr) hto hpc5 hrun5 hsp5_al hx30_5
    (by
      dsimp only [Spec.inImage, Matched.strToOwnedLocal2SpecWithStack, Spec.allowPanicWhen]
      rw [hsp5, x3dhUnsupportedStr_length]
      exact Entails.pure_right ⟨hF5, hsym5⟩
        (Entails.pure_right ⟨hx0_5, hx1_5, hx2_5, by decide, by decide⟩ (Entails.refl _)))
    (by sep_focus)
    (fun _ => by
      dsimp only [Spec.inImage, Matched.strToOwnedLocal2SpecWithStack, Spec.allowPanicWhen]
      exact Entails.refl _)
    (hnext := fun s6 _ hpc6 hrun6 hsp6_5 _ hcs6 hF6 hsym6 => ?_)
  dsimp only [Spec.inImage, Matched.strToOwnedLocal2SpecWithStack, Spec.allowPanicWhen]
  rw [hsp5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6_5 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to.symm) (by sep_focus) ?_
  refine Matched.SepWPp.drop_ro_frame (D := roAddr ↦ᵣ x3dhUnsupportedStr) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.vecU8_unpack_3e0_64 A sp x3dhUnsupportedStr)
    (by sep_focus) ?_
  rw [x3dhUnsupportedStr_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs6 with ⟨hcs6_19, _, _, _, _, _, hcs6_25, _, _, hcs6_28, _, hvregs6_5⟩
  have hsp6 : s6.sp = sp := hsp6_5.trans hsp5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := hsp6 ▸ hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6_19.trans hx19_5
  have hx25_6 : s6.readReg64 .x25 = sp + 0x210#64 := hcs6_25.trans hx25_5
  have hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64 := hcs6_28.trans (hx28_5.trans hx28_4)
  have hstep7 := p2_over_seg1d_v3_to_drop_ext_wp img.base ext s6 coroPtr outPtr cap ptr 24#64
    u_a8 u_d0 b_4f2 hpc6 hrun6 hsp6_align hx19_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_steps_frame hF6 hsym6 hstep7 (by sep_focus)
    fun s7 _ hpc7 hrun7 hF7 hsym7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hvregs7_6, hx0_7, hx19_7, hx20_7, hx21_7, hx22_7,
    hx23_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7⟩
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  rw [Matched.dropProcessPrekeyImpl_addr_eq_ext img.base ext] at hpc7
  have hstk48 : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ cells (sp - 48#64) 6 := by
    rw [p2_stackAt_split_of_le sp stk 48 (Nat.le_trans p2_cells48_le_overPure hstk_pure) hstk_lt,
        p2_stackAt_48_cells6]
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_steps_frame hF7 hsym7
    (Matched.drop_process_prekey_impl_state1_ok_ext (b := img.base) (ext := ext))
    hpc7 hrun7 hsp7_al hx30_7
    (x := coroPtr + 0x398#64)
    (φ := s7.readReg64 .x0 = coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp7, Matched.coro_398_add_15a])
    hx0_7 (by sep_focus)
    (hnext := fun s8 _ hpc8 hrun8 hsp8_7 _ hcs8 hF8 hsym8 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp7, Matched.coro_398_add_15a, sepConj_assoc]
  refine SepWPp.pure_elim fun htr8_7 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk48.symm) (by sep_focus) ?_
  rcases hcs8 with ⟨hcs8_19, hcs8_20, hcs8_21, hcs8_22, hcs8_23, hcs8_24,
    hcs8_25, hcs8_26, _, hcs8_28, _, hvregs8_7⟩
  have hsp8 : s8.sp = sp := hsp8_7.trans hsp7
  have hsp8_align : (s8.sp &&& 15#64 == 0#64) = true := hsp8 ▸ hsp_align
  have hx19_8 : s8.readReg64 .x19 = coroPtr := hcs8_19.trans hx19_7
  have hx20_8 : s8.readReg64 .x20 = 0x8000000000000018#64 := hcs8_20.trans hx20_7
  have hx21_8 : s8.readReg64 .x21 = 0#64 := hcs8_21.trans hx21_7
  have hx22_8 : s8.readReg64 .x22 = ptr := hcs8_22.trans hx22_7
  have hx23_8 : s8.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 := hcs8_23.trans hx23_7
  have hx24_8 : s8.readReg64 .x24 = cap := hcs8_24.trans hx24_7
  have hx25_8 : s8.readReg64 .x25 = s8.sp + 0x210#64 := by
    rw [hsp8]; exact hcs8_25.trans (hx25_7.trans hx25_6)
  have hx26_8 : s8.readReg64 .x26 = outPtr := hcs8_26.trans hx26_7
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by
    rw [hsp8]; exact hcs8_28.trans (hx28_7.trans hx28_6)
  have hlog_eq :
      logOff img =
        ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) :=
    rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_370_36_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (Matched.coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 =>
    SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u390 => ?_
  have hstep9 := Matched.p2_seg_1698_mismatch_to_3588_ext_wp img.base ext s8 coroPtr outPtr cap ptr
    24#64 u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hb hpc8 hrun8 hsp8_align
    hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx28_8
  rw [hsp8] at hstep9
  refine p2_bind_sepWP_steps_frame hF8 hsym8 hstep9 (by sep_focus)
    fun s9 _ hpc9 hrun9 hF9 hsym9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9_8, hvregs9_8, hx19_9, hx22_9, hx25_9, hx26_9, hx28_9, _, _⟩
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := hsp9 ▸ hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Matched.coro_250_6w_entails_cells6 coroPtr 0x8000000000000018#64 cap ptr 24#64 3#64
      (s8.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.a90_mismatch_entails_memRegion48 sp cap ptr 24#64
    (s8.readReg64 .x27)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.w64_3_entails_memRegion24 (sp + 0x3e0#64) cap ptr 24#64)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (p2_sessionAt_entails_state A (coroPtr + 0xf8#64) recG sess)
    (by sep_focus) ?_
  have hdss_sp : dropSessionStructureLocal2Stack ≤ sp.toNat :=
    Nat.le_trans (Nat.le_trans p2_over_dropSS3_le_overPure hstk_pure) hstk_sp
  have hstk_dss := p2_stackAt_split_of_le sp stk dropSessionStructureLocal2Stack
    (Nat.le_trans p2_over_dropSS3_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_dss) (by sep_focus) ?_
  have hdropTail := p2_over_err_drop_record_tail_hooks_ok (Qp := fun _ _ => False)
    hH hPure.dropSessionStructure3 s0 s9
    sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
    ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32)
    ((s8.readReg64 .x27).extractLsb' 32 32)
    b_2c0 g recG sess.state
    ⟨hF9, hsym9⟩ hsp9 hdss_sp hpc9 hrun9 hsp9_align
    hx19_9 hx22_9 hx25_9 hx26_9 hx28_9
  refine p2_bind_sepWPp_nopanic_frame (Qp := PanicOomProp s0) hdropTail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_9, hcsf, hvregsf_9, hinvf⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_dss.symm) (by sep_focus) ?_
  have hinv_msg :
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ (s8.readReg64 .x27).extractLsb' 32 32) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr
         x3dhUnsupportedStr) ⊢
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := by
    have hm := Matched.invalidMessage_prekey_out_entails_3 A outPtr cap ptr (s8.readReg64 .x27)
      x3dhUnsupportedStr
    rw [x3dhUnsupportedStr_length] at hm
    exact hm
  refine SepWPp.weaken_frame hinv_msg (by sep_focus) ?_
  have htr_all : sf.trace = s.trace := by
    rw [htrf_9, htr9_8, htr8_7, htr7_6, htr6_5, htr5_eq]
  have hvregs7_6' : calleeSavedVRegs s7 = calleeSavedVRegs s6 := by
    unfold calleeSavedVRegs; rw [hvregs7_6]
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_9, hvregs9_8, hvregs8_7, hvregs7_6',
        hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htr_all, hcsf, hvregs_all, hinvf⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
theorem stageP2_over_v3_kits_ext {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {roStack : Nat}
    (img : Obj.Image) (ext : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img)
    (hH : StageP2ClosureHooks A img.base ext)
    (hAX : AllocContractsX img A ext)
    (hro_le : roStack ≤ extHookStack)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStack))
    (hPure : StageP2PureCallees4K P A F img ext)
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : PromoteMatchingMissAtPropExt A img ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hstk_sp : stk ≤ sp.toNat)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
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
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hOut : ∀ (sf : State) (P_f : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s sf →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp + 0xcd0#64 →
      sf.trace = s.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      ImgCallInv img sf →
      (P_f ⊢
        processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
          idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
          kyberStorePtr kyberStoreVt ∗
        ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
        ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
        memRegion (coroPtr + 0xe0#64) 368 ∗
        cells (coroPtr + 0x250#64) 6 ∗
        ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
        ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
        ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
        ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
        ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
        ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
        ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
        ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
        ((sp + 0xd0#64) ↦₆₄ 24#64) ∗
        memRegion (sp + 0x370#64) 36 ∗
        memRegion (sp + 0x3e0#64) 24 ∗
        memRegion (sp + 0xa90#64) 48 ∗
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
        logOff img ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        A.pool ∗
        stackAt sp stk ∗
        Frame) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       prevSessionsEmptyAt A coroPtr g ∗
       sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       logOff img ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk ∗
       Frame)
      Q Qp := by
  have hoom := stageP2_over_v3_oom_ext (P := P) (A := A) (F := F) img ext himg hH hAX hro_le hRO
    hPure stk hstk_pure s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt u_a8 u_d0
    g recG sess baseKey b_2c0 b_390 b_4f1 b_4f2 hPromMiss hb hstk_sp
    hF hsym hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
  refine p2_bind_sepWPp_oom_frame_qpan hpan hoom (by sep_focus)
    fun sf hsteps hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf
    (hOut sf _ hsteps hpcf hrunf hspf htrf hcsf hvregsf hinvf ?_)
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
