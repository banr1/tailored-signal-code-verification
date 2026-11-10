/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.StoreKit.Over.ArchiveDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.D3.D3PollRejectAuxPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2V3StepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Mid2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2ErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsEPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Fetch

/-!
# Path-A & Over-Path `v3` Stage P2 Rejection Kits & Stack Splits

Pure version-3 model lemmas, stack/coroutine spatial splits, and relocatable Path-A
(`opt = none`) and Over-Path (`opt = some r`, `¬ SessMatchesPm`) Stage P2 rejection
compositions (`+0x0868 → s0.readReg64 .x30`) for version-3 `PreKeySignalMessage` inputs.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace LibsignalBinary.Proofs.SignalSession.Cli.D3

open Arm64 Arm64.Process ProofLib ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp decryptPrekeyClosureName
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose hiding Bytes
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Poll
open CryptoVerification.SignalSession.Cli.KitInst

/-! ## 1. Pure `v3` Model Lemmas -/

theorem pkToE?_eq_none_of_v3 {pm : PreKeySignalMessage}
    (hv3 : pm.messageVersion = 3#8) : pkToE? pm = none := by
  unfold pkToE?
  rw [hv3]
  rfl

theorem baseKey_serialize_length (pk : PublicKey) :
    pk.serialize.length = 33 := by
  dsimp only [PublicKey.serialize]
  simp [pk.bytes.toList_length]

theorem not_p2SessMatchesMsg_of_v3 {sess : Session (List (BitVec 8))}
    {pm : PreKeySignalMessage} (hv3 : pm.messageVersion = 3#8)
    (hnm : ¬ SessMatchesPm sess pm) :
    ¬ Over.SessMatchesMsg sess 3#8 pm.baseKey.serialize := by
  intro ⟨hver, hbk⟩
  exact hnm ⟨hv3.symm ▸ hver, hbk⟩

theorem not_p2SessMatchesMsg_of_v3' {sess : Session (List (BitVec 8))}
    {pm : PreKeySignalMessage} (hv3 : pm.messageVersion = 3#8)
    (hnm : ¬ SessMatchesPm sess pm) :
    ¬ Over.P2SessMatchesMsg sess 3#8 pm.baseKey.serialize := by
  intro ⟨hver, hbk⟩
  exact hnm ⟨hv3.symm ▸ hver, hbk⟩

/-! ## 2. Stack & Coroutine Spatial Splits for `v3` Stage P2 Reject (`[LibsignalPlacement]`) -/

theorem d3_stackAt_48_cells6 (sp : BitVec 64) :
    stackAt sp 48 = cells (sp - 48#64) 6 := by
  change memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem d3_sp3e0_24_split_9_15 (sp : BitVec 64) :
    memRegion (sp + 992#64) 24 =
      memRegion (sp + 992#64) 9 ∗ memRegion (sp + 1001#64) 15 := by
  rw [ProofLib.memRegion_split (sp + 992#64) 9 15 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem d3_sp3e0_24_rejoin (sp : BitVec 64) (w : BitVec 64) (b : BitVec 8) :
    ((sp + 992#64) ↦₆₄ w) ∗ ((sp + 1000#64) ↦₈ b) ∗ memRegion (sp + 1001#64) 15 ⊢
      memRegion (sp + 992#64) 24 := by
  rw [ProofLib.memRegion_split (sp + 992#64) 8 16 (by decide),
      ProofLib.memRegion_split (sp + 992#64 + 8#64) 1 15 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _))

/-! ## 3. Path A (`opt = none`) Outer `v3` Stage P2 Reject (`+0x0868 → s0.readReg64 .x30`) -/

section StageP2V3Placed

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

set_option maxHeartbeats 1200000 in
theorem stageP2_pathA_v3_oom_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hto : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (Matched.strToOwnedLocal2Spec A)))
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hstk_sp : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
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
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗ cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗ ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗ memRegion outPtr 48 ∗
       FromRecordCallees.lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗ stackAt sp stk)
      (fun sf P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          memRegion (coroPtr + 0xe0#64) 368 ∗ cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ ((msgPtr + 0xf0#64) ↦₈ 3#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗ ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ 24#64) ∗
          memRegion (sp + 0x370#64) 36 ∗ memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0xa90#64) 48 ∗
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          FromRecordCallees.lsLogOff ∗ decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗ stackAt sp stk) ∧
        sf.sp = sp + 0xcd0#64 ∧ sf.trace = s.trace ∧ ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧ StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  refine Over.p2_intro_rodata_x3dhUnsupported_placed hCode ?_
  have hstep1 := Over.p2_over_seg1a_v3_ext_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, _,
    hx28_1, _, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le sp stk publicKeySerializeStack
    (Nat.le_trans (by decide : publicKeySerializeStack ≤ stageP2OverPureAndErrStack) hstk_pure)
    hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_lscl_steps_frame_placed
    (spec := publicKeySerializeSpec A)
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt sp publicKeySerializeStack)
    hCode1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
      rw [hsp1]
      exact Entails.pure_right hx0_1 (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
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
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := Over.p2_over_seg1b_v3_ext_placed_wp ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkStoreVt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, _, _, _, hx8_3, hx19_3, hx21_3, _,
    _, _, _, hx26_3, _, hx28_3, _, hx30_3, hvregs3_2⟩
  simp only [arm64_norm] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom1 := p2_stackAt_split_of_le sp stk 1248
    (Nat.le_trans (by decide : 1248 ≤ stageP2OverPureAndErrStack) hstk_pure) hstk_lt
  have hstk_prom2 := stackAt_1248_promote_eq sp
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (d3_sp3e0_24_split_9_15 sp)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (memRegion_9_sp3e0_eq sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode3 hPure.promoteMatchingSessionEmpty
    hpc3 hrun3 hsp3_al hx30_3
    (x := (coroPtr + 0xe0#64, sp + 0x3e0#64))
    (R_pure := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧ s3.readReg64 .x8 = sp + 0x3e0#64)
    (T := ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
      (∃∗ w0 : BitVec 64, (sp + 0x3e0#64) ↦₆₄ w0) ∗
      (∃∗ b8 : BitVec 8, (sp + 0x3e8#64) ↦₈ b8) ∗
      cells (sp - 1248#64) 8 ∗
      cells (sp - 1184#64) 10 ∗
      (∃∗ w2e0 : BitVec 64, (sp - 448#64) ↦₆₄ w2e0) ∗
      cells (sp - 96#64) 12)
    (by
      dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
      rw [hsp3, show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega])
    ⟨hx0_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [ResponderStore.promoteMatchingSessionEmptySpec]
  rcases hcs4 with ⟨hcs4_19, _, hcs4_21, _, _, _, _, hcs4_26, _, hcs4_28, _, hvregs4_3⟩
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := hsp4 ▸ hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hcs4_19.trans hx19_3
  have hx21_4 : s4.readReg64 .x21 = s2.readReg64 .x0 := hcs4_21.trans hx21_3
  have hx26_4 : s4.readReg64 .x26 = 33#64 := hcs4_26.trans hx26_3
  have hx28_4 : s4.readReg64 .x28 = sp + 0xa90#64 := hcs4_28.trans (hx28_3.trans hx28_2)
  rw [hsp3, show (sp + 0x3e0#64) + 8#64 = sp + 0x3e8#64 by bv_omega]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr4 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom2.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom1.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans (by decide : allocHookStack ≤ stageP2OverPureAndErrStack) hstk_pure) hstk_lt
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
  have hstep5 := Over.p2_over_seg1c_v3_hooks_placed_wp ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx2_5, hx19_5, hx25_5, _, hx28_5, _, hx30_5,
    hvregs5_4⟩
  simp only [arm64_norm] at hpc5
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (d3_sp3e0_24_rejoin sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_to := p2_stackAt_split_of_le sp stk Matched.strToOwnedLocal2Stack
    (Nat.le_trans (by decide : Matched.strToOwnedLocal2Stack ≤ stageP2OverPureAndErrStack) hstk_pure)
    hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to) (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  refine p2_call_oom_lscl_steps_frame_placed
    (spec := Matched.strToOwnedLocal2Spec A)
    (x := (sp + 0x3e0#64, lsρ Over.x3dhUnsupportedSym, Over.x3dhUnsupportedBytes))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗
      (lsρ Over.x3dhUnsupportedSym ↦ᵣ Over.x3dhUnsupportedBytes) ∗ A.pool ∗
      stackAt sp Matched.strToOwnedLocal2Stack)
    hCode5 (htr5_eq ▸ htr) hto hpc5 hrun5 hsp5_al hx30_5
    (by
      dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
      rw [hsp5, Over.x3dhUnsupportedBytes_length]
      exact Entails.pure_right ⟨hx0_5, hx1_5, hx2_5, by decide, by decide⟩ (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s6 _ hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
  dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
  rw [hsp5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6_5 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to.symm) (by sep_focus) ?_
  refine Matched.SepWPp.drop_ro_frame
    (D := lsρ Over.x3dhUnsupportedSym ↦ᵣ Over.x3dhUnsupportedBytes) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.vecU8_unpack_3e0_64 A sp Over.x3dhUnsupportedBytes)
    (by sep_focus) ?_
  rw [Over.x3dhUnsupportedBytes_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs6 with ⟨hcs6_19, _, _, _, _, _, hcs6_25, _, _, hcs6_28, _, hvregs6_5⟩
  have hsp6 : s6.sp = sp := hsp6_5.trans hsp5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := hsp6 ▸ hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6_19.trans hx19_5
  have hx25_6 : s6.readReg64 .x25 = sp + 0x210#64 := hcs6_25.trans hx25_5
  have hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64 := hcs6_28.trans (hx28_5.trans hx28_4)
  have hstep7 := Over.p2_over_seg1d_v3_to_drop_ext_placed_wp ext s6 coroPtr outPtr cap ptr 24#64
    u_a8 u_d0 b_4f2 hpc6 hrun6 hsp6_align hx19_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_qp_frame_placed hCode6 hstep7 (by sep_focus)
    fun s7 _ hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hvregs7_6, hx0_7, hx19_7, hx20_7, hx21_7, hx22_7,
    hx23_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7⟩
  simp only [arm64_norm] at hpc7
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  have hstk48 : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ cells (sp - 48#64) 6 := by
    rw [p2_stackAt_split_of_le sp stk 48
          (Nat.le_trans (by decide : 48 ≤ stageP2OverPureAndErrStack) hstk_pure) hstk_lt,
        d3_stackAt_48_cells6]
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode7 hPure.dropProcessPrekeyImplState1
    hpc7 hrun7 hsp7_al hx30_7
    (x := coroPtr + 0x398#64)
    (R_pure := s7.readReg64 .x0 = coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    (by
      dsimp only [CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
      rw [hsp7, Matched.coro_398_add_15a])
    hx0_7 (by sep_focus)
    (hnext := fun s8 _ hpc8 hrun8 hsp8_7 _ hcs8 hCode8 => ?_)
  dsimp only [CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
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
  have hx28_8 : s8.readReg64 .x28 = s8.sp + 0xa90#64 := by
    rw [hsp8]; exact hcs8_28.trans (hx28_7.trans hx28_6)
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (Matched.coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 => SepWPp.exists_elim fun u260 =>
    SepWPp.exists_elim fun u268 => SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun uaa0 =>
    SepWPp.exists_elim fun uaa8 => SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 => ?_
  have hr23_lo :
      ((cap.extractLsb' 0 32).zeroExtend 64).extractLsb' 0 32 = cap.extractLsb' 0 32 := by
    clear * -; bv_bits
  have hstep9a := Kits.p2_err_tail_b1_ext_placed_wp ext s8 coroPtr outPtr
    0x8000000000000018#64 cap ptr 24#64 3#64 (s8.readReg64 .x27)
    ((cap.extractLsb' 0 32).zeroExtend 64)
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8 b_390
    (by decide) hr23_lo hpc8 hrun8 hsp8_align
    hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 rfl hx28_8
  rw [hsp8] at hstep9a
  refine p2_bind_sepWP_qp_frame_placed hCode8 hstep9a (by sep_focus)
    fun s8b _ hpc8b hrun8b hCode8b hregs8b => ?_
  rcases hregs8b with ⟨hsp8b, htr8b_8, hx19_8b, _, hx21_8b, hx25_8b, hx26_8b, hx28_8b, _, _, hvregs8b_8⟩
  have hsp8b_align : (s8b.sp &&& 15#64 == 0#64) = true := hsp8b ▸ hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (Matched.coro_250_6w_entails_cells6 coroPtr 0x8000000000000018#64 cap ptr 24#64 3#64 (s8.readReg64 .x27))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.w64_3_entails_memRegion24 (sp + 0x3e0#64) cap ptr 24#64)
    (by sep_focus) ?_
  have hdr_eq :
      ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) =
        ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ 8#64) ∗
        ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xf8#64) ↦₆₄ (-1#64)) := by
    unfold ResponderStore.sessionRecordEmptyHeaderAt
    simp only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceNeg]
  refine SepWPp.weaken_frame (Entails.of_eq hdr_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_370_36_split sp) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 => SepWPp.exists_elim fun u380 =>
    SepWPp.exists_elim fun u388 => SepWPp.exists_elim fun u390 => ?_
  have hx21_8b' : s8b.readReg64 .x21 = s8b.sp + 0x370#64 := by rw [hx21_8b, hsp8b]
  have hx25_8b' : s8b.readReg64 .x25 = s8b.sp + 0x210#64 := by rw [hx25_8b, hsp8b]
  have hx28_8b' : s8b.readReg64 .x28 = s8b.sp + 0xa90#64 := by rw [hx28_8b, hsp8b]
  have hstep9b := Kits.p2_err_tail_b2_ext_placed_wp ext s8b coroPtr
    0x8000000000000018#64 outPtr
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
    ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    u370 u378 u380 u388 (cap.extractLsb' 0 32) ((s8.readReg64 .x27).extractLsb' 32 32) u390
    hpc8b hrun8b hsp8b_align hx19_8b hx21_8b' hx25_8b' hx26_8b hx28_8b'
  rw [hsp8b] at hstep9b
  refine p2_bind_sepWP_qp_frame_placed hCode8b hstep9b (by sep_focus)
    fun s9 _ hpc9 hrun9 hCode9 hregs9 => ?_
  rcases hregs9 with ⟨hsp9, htr9_8b, hx19_9, hx22_9, hx25_9, hx26_9, hx28_9, _, _, hvregs9_8b⟩
  have hsp9_align : (s9.sp &&& 15#64 == 0#64) = true := hsp9 ▸ hsp_align
  refine SepWPp.weaken_frame (Matched.a90_mismatch_entails_memRegion48 sp cap ptr 24#64
    (s8.readReg64 .x27)) (by sep_focus) ?_
  have hf8 :
      ((coroPtr + 0xf8#64) ↦₆₄ (-1#64)) ∗ memRegion (coroPtr + 0x100#64) 336 ⊢
        memRegion (coroPtr + 0xf8#64) 344 := by
    rw [ProofLib.memRegion_split (coroPtr + 0xf8#64) 8 336 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono_left (ProofLib.pointsTo64_entails_memRegion _ _)
  refine SepWPp.weaken_frame hf8 (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0)) (by sep_focus) ?_
  refine SepWPp.weaken_frame (memRegion_48_out_entails outPtr) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u_ret0 => SepWPp.exists_elim fun u_ret08 =>
    SepWPp.exists_elim fun u_ret0c => SepWPp.exists_elim fun u_ret14 =>
    SepWPp.exists_elim fun u_ret1c => SepWPp.exists_elim fun u_ret24 =>
    SepWPp.exists_elim fun u_ret2c => ?_
  have hx25_9' : s9.readReg64 .x25 = s9.sp + 0x210#64 := by rw [hsp9]; exact hx25_9
  have hstep10 := Kits.p3_err_tail_b_ext_placed_wp ext s9 coroPtr outPtr
    0x8000000000000018#64 8#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
    ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (cap.extractLsb' 0 32) ((s8.readReg64 .x27).extractLsb' 32 32)
    u_ret08 u_ret2c b_2c0
    hpc9 hrun9 hsp9_align hx19_9 hx22_9 hx25_9' hx26_9 hx28_9
  rw [hsp9] at hstep10
  refine p2_bind_sepWP_qp_frame_placed hCode9 hstep10 (by sep_focus)
    fun sf _ hpcf hrunf hCodef hregsf => ?_
  rcases hregsf with ⟨hspf, htrf_9, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f,
    hx25f, hx26f, hx27f, hx28f, hx29f, _, hvregsf_9⟩
  have hinv_msg :
      (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
       ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
       ((outPtr + 0x14#64) ↦₆₄ ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
       ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x24#64) ↦₆₄ ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
       ((outPtr + 0x2c#64) ↦₃₂ (s8.readReg64 .x27).extractLsb' 32 32) ∗
       CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr
         Over.x3dhUnsupportedBytes) ⊢
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := by
    have hm := Matched.invalidMessage_prekey_out_entails_3_placed A outPtr cap ptr
      (s8.readReg64 .x27) Over.x3dhUnsupportedBytes
    rw [Over.x3dhUnsupportedBytes_length] at hm
    exact hm
  refine SepWPp.weaken_frame hinv_msg (by sep_focus) ?_
  refine SepWPp.weaken_frame
    (sp_370_rejoin sp
      (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
      ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
      ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
      ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
      ((s8.readReg64 .x27).extractLsb' 32 32))
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (coro_e0_368_fold coroPtr 0#64 8#64 0#64) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (savedRegsAt_eq_sp_c70 sp s0).symm) (by sep_focus) ?_
  have htr_all : sf.trace = s.trace := by
    rw [htrf_9, htr9_8b, htr8b_8, htr8_7, htr7_6, htr6_5, htr5_eq]
  have hvregs7_6' : calleeSavedVRegs s7 = calleeSavedVRegs s6 := by
    unfold calleeSavedVRegs; rw [hvregs7_6]
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_9, hvregs9_8b, hvregs8b_8, hvregs8_7, hvregs7_6',
        hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htr_all,
    ⟨hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, True.intro⟩,
    hvregs_all, hCodef⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
theorem stageP2_pathA_v3_kits_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hto : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (Matched.strToOwnedLocal2Spec A)))
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hstk_sp : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
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
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp + 0xcd0#64 →
      sf.trace = s.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
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
        FromRecordCallees.lsLogOff ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        A.pool ∗
        stackAt sp stk ∗
        Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ResponderStore.sessionRecordEmptyHeaderAt (coroPtr + 0xe0#64) ∗
       memRegion (coroPtr + 0x100#64) 336 ∗
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
       FromRecordCallees.lsLogOff ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk ∗
       Frame)
      Q Qp := by
  have hoom := stageP2_pathA_v3_oom_placed ext hH hPure hto
    stk hstk_pure s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt u_a8 u_d0
    baseKey b_2c0 b_390 b_4f1 b_4f2 hstk_sp
    hCode hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
  refine p2_bind_sepWPp_oom_frame_qpan hpan hoom (by sep_focus)
    fun sf hsteps hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hCodef⟩ => ?_
  refine SepWPp.done hpcf hrunf
    (hOut sf _ hsteps hpcf hrunf hspf htrf hcsf hvregsf hCodef ?_)
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

/-! ## 4. Over-Path C (`opt = some r`, `¬ SessMatchesPm`) Outer `v3` Stage P2 Reject -/

set_option maxHeartbeats 1200000 in
theorem stageP2_over_v3_oom_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpan_eq : Rust.withPanics ext = ext)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hto : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (Matched.strToOwnedLocal2Spec A)))
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : Over.PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hstk_sp : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
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
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       Matched.prevSessionsEmptyAt A coroPtr g ∗
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
       FromRecordCallees.lsLogOff ∗
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
          FromRecordCallees.lsLogOff ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp stk) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hstk_lt : stk ≤ 2 ^ 64 := Nat.le_trans hstk_sp (Nat.le_of_lt sp.isLt)
  refine Over.p2_intro_rodata_x3dhUnsupported_placed hCode ?_
  have hstep1 := Over.p2_over_seg1a_v3_ext_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine p2_bind_sepWP_qp_frame_placed hCode hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hCode1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1, _, _,
    hx28_1, _, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp_align
  have hstk_ser := p2_stackAt_split_of_le sp stk publicKeySerializeStack
    (Nat.le_trans (by decide : publicKeySerializeStack ≤ stageP2OverPureAndErrStack) hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser) (by sep_focus) ?_
  sep_norm
  refine p2_call_oom_lscl_steps_frame_placed
    (spec := publicKeySerializeSpec A)
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt sp publicKeySerializeStack)
    hCode1 (htr1 ▸ htr) hPure.publicKeySerialize
    hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
      rw [hsp1]
      exact Entails.pure_right hx0_1 (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hCode2 => ?_)
  dsimp only [publicKeySerializeSpec, Spec.allowPanicWhen]
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
  refine SepWPp.weaken_frame (Over.p2_boxU8Buf_pk_serialize_entails A (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_ser.symm) (by sep_focus) ?_
  have hstep3 := Over.p2_over_seg1b_v3_ext_placed_wp ext s2 coroPtr (s2.readReg64 .x0) spkStorePtr
    spkStoreVt hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  rw [hsp2] at hstep3
  refine p2_bind_sepWP_qp_frame_placed hCode2 hstep3 (by sep_focus)
    fun s3 _ hpc3 hrun3 hCode3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3, htr3, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3, _,
    _, _, _, hx26_3, _, hx28_3, _, hx30_3, hvregs3_2⟩
  simp only [arm64_norm] at hpc3
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3] using hsp_align
  have hstk_prom := p2_stackAt_split_of_le sp stk Over.p2PromoteMissStack
    (Nat.le_trans Over.p2_over_promoteMiss_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (Over.p2_sp3e0_24_split_16_8 sp)) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode3
    (CryptoVerification.E2E.Record.Serialization.SerializeBodyAuxX.subroutine_ok_withLsCodeLoaded_of_withLsCl
      hPromMiss)
    hpc3 hrun3 hsp3_al hx30_3
    (x := ⟨s2.readReg64 .x0, sp + 0x3e0#64⟩)
    (R_pure := s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = (3#8 : BitVec 8).zeroExtend 64 ∧
      s3.readReg64 .x2 = s2.readReg64 .x0 ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64)
    (T := Matched.prevSessionsEmptyAt A coroPtr g ∗
      sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
      ((s2.readReg64 .x0) ↦ₛ baseKey.serialize) ∗
      memRegion (sp + 0x3e0#64) 16 ∗
      stackAt sp Over.p2PromoteMissStack)
    (by dsimp only [Over.p2PromoteMatchingMissAtSpec]; rw [hsp3])
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3⟩ (by sep_focus)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hCode4 => ?_)
  dsimp only [Over.p2PromoteMatchingMissAtSpec]
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
  refine SepWPp.weaken_frame (Over.p2_serBytes_entails_memRegion33 (s2.readReg64 .x0) baseKey)
    (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_prom.symm) (by sep_focus) ?_
  have hstk_alloc := p2_stackAt_split_of_le sp stk allocHookStack
    (Nat.le_trans (by decide : allocHookStack ≤ stageP2OverPureAndErrStack) hstk_pure) hstk_lt
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
  have hstep5 := Over.p2_over_seg1c_v3_hooks_placed_wp ext hH s4 coroPtr msgPtr (s2.readReg64 .x0)
    hpc4 hrun4 hsp4_align hx19_4 hx21_4 hx26_4
  rw [hsp4] at hstep5
  refine p2_bind_sepWP_qp_frame_placed hCode4 hstep5 (by sep_focus)
    fun s5 _ hpc5 hrun5 hCode5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5, htr5, hx0_5, hx1_5, hx2_5, hx19_5, hx25_5, _, hx28_5, _, hx30_5,
    hvregs5_4⟩
  simp only [arm64_norm] at hpc5
  have hsp5_al : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq hAct_split.symm) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Over.p2_sp3e0_24_rejoin_placed sp 0#64 0#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_alloc.symm) (by sep_focus) ?_
  have hstk_to := p2_stackAt_split_of_le sp stk Matched.strToOwnedLocal2Stack
    (Nat.le_trans Over.p2_strToOwnedStack_le_overPure_placed hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to) (by sep_focus) ?_
  sep_norm
  have htr5_eq : s5.trace = s.trace := by rw [htr5, htr4, htr3, htr2, htr1]
  refine p2_call_oom_lscl_steps_frame_placed
    (spec := Matched.strToOwnedLocal2Spec A)
    (x := (sp + 0x3e0#64, lsρ Over.x3dhUnsupportedSym, Over.x3dhUnsupportedBytes))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗
      (lsρ Over.x3dhUnsupportedSym ↦ᵣ Over.x3dhUnsupportedBytes) ∗ A.pool ∗
      stackAt sp Matched.strToOwnedLocal2Stack)
    hCode5 (htr5_eq ▸ htr) hto hpc5 hrun5 hsp5_al hx30_5
    (by
      dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
      rw [hsp5, Over.x3dhUnsupportedBytes_length]
      exact Entails.pure_right ⟨hx0_5, hx1_5, hx2_5, by decide, by decide⟩ (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s6 _ hpc6 hrun6 hsp6_5 _ hcs6 hCode6 => ?_)
  dsimp only [Matched.strToOwnedLocal2Spec, Spec.allowPanicWhen]
  rw [hsp5, sepConj_assoc]
  refine SepWPp.pure_elim fun htr6_5 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq hstk_to.symm) (by sep_focus) ?_
  refine Matched.SepWPp.drop_ro_frame
    (D := lsρ Over.x3dhUnsupportedSym ↦ᵣ Over.x3dhUnsupportedBytes) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.vecU8_unpack_3e0_64 A sp Over.x3dhUnsupportedBytes)
    (by sep_focus) ?_
  rw [Over.x3dhUnsupportedBytes_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs6 with ⟨hcs6_19, _, _, _, _, _, hcs6_25, _, _, hcs6_28, _, hvregs6_5⟩
  have hsp6 : s6.sp = sp := hsp6_5.trans hsp5
  have hsp6_align : (s6.sp &&& 15#64 == 0#64) = true := hsp6 ▸ hsp_align
  have hx19_6 : s6.readReg64 .x19 = coroPtr := hcs6_19.trans hx19_5
  have hx25_6 : s6.readReg64 .x25 = sp + 0x210#64 := hcs6_25.trans hx25_5
  have hx28_6 : s6.readReg64 .x28 = sp + 0xa90#64 := hcs6_28.trans (hx28_5.trans hx28_4)
  have hstep7 := Over.p2_over_seg1d_v3_to_drop_ext_placed_wp ext s6 coroPtr outPtr cap ptr 24#64
    u_a8 u_d0 b_4f2 hpc6 hrun6 hsp6_align hx19_6
  rw [hsp6] at hstep7
  refine p2_bind_sepWP_qp_frame_placed hCode6 hstep7 (by sep_focus)
    fun s7 _ hpc7 hrun7 hCode7 hregs7 => ?_
  rcases hregs7 with ⟨hsp7, htr7_6, hvregs7_6, hx0_7, hx19_7, hx20_7, hx21_7, hx22_7,
    hx23_7, hx24_7, hx25_7, hx26_7, _, hx28_7, _, hx30_7⟩
  simp only [arm64_norm] at hpc7
  have hsp7_al : s7.spAligned = true := by simpa only [State.spAligned, hsp7] using hsp_align
  have hstk48 : stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - 48) ∗ cells (sp - 48#64) 6 := by
    rw [p2_stackAt_split_of_le sp stk 48
          (Nat.le_trans Over.p2_cells48_le_overPure_placed hstk_pure) hstk_lt,
        Over.p2_stackAt_48_cells6_placed]
  refine SepWPp.weaken_frame (Entails.of_eq hstk48) (by sep_focus) ?_
  simp only [sepConj_assoc]
  refine p2_call_nopanic_lscl_steps_frame_placed hCode7 hPure.dropProcessPrekeyImplState1
    hpc7 hrun7 hsp7_al hx30_7
    (x := coroPtr + 0x398#64)
    (R_pure := s7.readReg64 .x0 = coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    (by
      dsimp only [CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
      rw [hsp7, Matched.coro_398_add_15a])
    hx0_7 (by sep_focus)
    (hnext := fun s8 _ hpc8 hrun8 hsp8_7 _ hcs8 hCode8 => ?_)
  dsimp only [CryptoVerification.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplState1Spec]
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
  have hlog_eq : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  refine SepWPp.weaken_frame (Entails.of_eq hlog_eq) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_370_36_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Matched.memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (Matched.coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 => SepWPp.exists_elim fun u260 =>
    SepWPp.exists_elim fun u268 => SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 => SepWPp.exists_elim fun uaa0 =>
    SepWPp.exists_elim fun uaa8 => SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 =>
    SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 => SepWPp.exists_elim fun u380 =>
    SepWPp.exists_elim fun u388 => SepWPp.exists_elim fun u390 => ?_
  have hstep9 := Matched.p2_seg_1698_mismatch_to_3588_placed_wp ext s8 coroPtr outPtr cap ptr
    24#64 u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hpc8 hrun8 hsp8_align
    hx19_8 hx20_8 hx21_8 hx22_8 hx23_8 hx24_8 hx25_8 hx28_8
  rw [hpan_eq, hsp8] at hstep9
  refine p2_bind_sepWP_qp_frame_placed hCode8 hstep9 (by sep_focus)
    fun s9 _ hpc9 hrun9 hCode9 hregs9 => ?_
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
  refine SepWPp.weaken_frame (Over.p2_sessionAt_entails_state_placed A (coroPtr + 0xf8#64) recG sess)
    (by sep_focus) ?_
  have hdss_sp : dropSessionStructureLocal2Stack ≤ sp.toNat :=
    Nat.le_trans (Nat.le_trans Over.p2_over_dropSS3_le_overPure hstk_pure) hstk_sp
  have hstk_dss := p2_stackAt_split_of_le sp stk dropSessionStructureLocal2Stack
    (Nat.le_trans Over.p2_over_dropSS3_le_overPure hstk_pure) hstk_lt
  refine SepWPp.weaken_frame (Entails.of_eq hstk_dss) (by sep_focus) ?_
  have hdropTail := Over.p2_over_err_drop_record_tail_hooks_placed_ok
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
    hH hPure.dropSessionStructure3 s0 s9
    sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((24#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (24#64 : BitVec 64).extractLsb' 32 32)
    ((s8.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32)
    ((s8.readReg64 .x27).extractLsb' 32 32)
    b_2c0 g recG sess.state
    hCode9 hsp9 hdss_sp hpc9 hrun9 hsp9_align
    hx19_9 hx22_9 hx25_9 hx26_9 hx28_9
  refine SepWPp.bind_sepWPp_steps_frame hdropTail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_9, hcsf, hvregsf_9, hCodef⟩ => ?_
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
         Over.x3dhUnsupportedBytes) ⊢
        apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) := by
    have hm := Matched.invalidMessage_prekey_out_entails_3_placed A outPtr cap ptr
      (s8.readReg64 .x27) Over.x3dhUnsupportedBytes
    rw [Over.x3dhUnsupportedBytes_length] at hm
    exact hm
  refine SepWPp.weaken_frame hinv_msg (by sep_focus) ?_
  have htr_all : sf.trace = s.trace := by
    rw [htrf_9, htr9_8, htr8_7, htr7_6, htr6_5, htr5_eq]
  have hvregs7_6' : calleeSavedVRegs s7 = calleeSavedVRegs s6 := by
    unfold calleeSavedVRegs; rw [hvregs7_6]
  have hvregs_all : calleeSavedVRegs sf = calleeSavedVRegs s0 := by
    rw [hvregsf_9, hvregs9_8, hvregs8_7, hvregs7_6',
        hvregs6_5, hvregs5_4, hvregs4_3, hvregs3_2, hvregs2_1, hvregs1, hvregs]
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htr_all, hcsf, hvregs_all, hCodef⟩
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 800000 in
theorem stageP2_over_v3_kits_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hpan_eq : Rust.withPanics ext = ext)
    (hH : StageP2ClosureHooksPlaced A ext)
    (hPure : StageP2BaseCalleesPlaced4K A ext)
    (hto : subroutine_ok (stageP1ProgPlaced ext) (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (Matched.strToOwnedLocal2Spec A)))
    (stk : Nat)
    (hstk_pure : stageP2OverPureAndErrStack ≤ stk)
    (s0 s : State) (Frame : SepProp) (Q : State → SepProp → Prop)
    {Qp : State → SepProp → Prop}
    (hpan : ∀ sf Pf, CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0 sf Pf → Qp sf Pf)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
     idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
     spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt
     u_a8 u_d0 : BitVec 64)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (baseKey : PublicKey) (b_2c0 b_390 b_4f1 b_4f2 : BitVec 8)
    (hPromMiss : Over.PromoteMatchingMissAtPlacedProp A ext coroPtr g recG sess 3#8 baseKey.serialize)
    (hstk_sp : stk ≤ sp.toNat)
    (hCode : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = stageP1EntryPlaced + 0x868#64)
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
      Steps (stageP1ProgPlaced ext) s sf →
      sf.pc = s0.readReg64 .x30 →
      sf.status = .Running →
      sf.sp = sp + 0xcd0#64 →
      sf.trace = s.trace →
      ClosureCalleeSaved s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
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
        FromRecordCallees.lsLogOff ∗
        decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
        A.pool ∗
        stackAt sp stk ∗
        Frame) →
      Q sf P_f) :
    SepWPp (stageP1ProgPlaced ext) (s0.readReg64 .x30) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       Matched.prevSessionsEmptyAt A coroPtr g ∗
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
       FromRecordCallees.lsLogOff ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp stk ∗
       Frame)
      Q Qp := by
  have hoom := stageP2_over_v3_oom_placed ext hpan_eq hH hPure hto
    stk hstk_pure s0 s sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt u_a8 u_d0
    g recG sess baseKey b_2c0 b_390 b_4f1 b_4f2 hPromMiss hstk_sp
    hCode hpc hrun hsp_eq hsp_align htr hvregs
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28
  refine p2_bind_sepWPp_oom_frame_qpan hpan hoom (by sep_focus)
    fun sf hsteps hpcf hrunf ⟨hspf, htrf, hcsf, hvregsf, hCodef⟩ => ?_
  refine SepWPp.done hpcf hrunf
    (hOut sf _ hsteps hpcf hrunf hspf htrf hcsf hvregsf hCodef ?_)
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end StageP2V3Placed

end LibsignalBinary.Proofs.SignalSession.Cli.D3
