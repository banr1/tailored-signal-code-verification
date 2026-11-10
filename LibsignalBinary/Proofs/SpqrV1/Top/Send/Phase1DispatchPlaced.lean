/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendLeaves1
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Dispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPbPlaced
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1StepsPlaced
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Relocatable `spqr::send::<HookRng>` Phase 1c: `<States>::from_pb` Call, Error Path, and Dispatch

Verifies `spqr_send_pre_states_from_pb_224_placed`, `spqr_send_states_from_pb_err_step_placed`,
and `spqr_send_states_from_pb_ok_step_placed` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send.Placed

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm]
  bv_sub_add_lit BitVec.toNat_zero bv_add_add_lit1 bv_add_add_lit2
  sp_add_30_add_80 sp_add_1260_add_8 sp_add_1260_add_16 sp_add_1260_add_24 sp_add_1260_add_32
  sp_add_1268_add_8 sp_add_1268_add_16 sp_add_1268_add_24
  sp_add_930_add_8 sp_add_930_add_16
  sp_add_950_add_8 sp_add_950_add_16 sp_add_950_add_24 sp_add_950_add_32
  sp_add_958_add_8 sp_add_958_add_16 sp_add_958_add_24
  sp_add_4096_add_608 sp_add_4096_add_640 sp_add_4096_add_96
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

omit [LibsignalPlacement] in
@[local arm64_norm, local wp_norm]
private theorem bv_add_add_lit_p1dp (x : BitVec 64) (a b : Nat) :
    (x + BitVec.ofNat 64 a) + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  bv_omega

/-! ## Pre-Call Step (`+224 -> lsρ statesFromPbName`) -/

/-- Relocatable pre-call setup (`+224 -> lsmpl.base 333`):
    computes `x8 = sp + 0x1260`, `x0 = sp + 0xb0`, `x21 = sp + 0x1260`, and branches with link
    (`x30 = spqrSendPlacedEntry + 248#64`) to `<States>::from_pb` (Block `333`). -/
theorem spqr_send_pre_states_from_pb_224_placed
    {ext : String → Option (State → State)}
    {s0 s : State} {sp : BitVec 64} {P : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 224#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx20 : s.readReg64 .x20 = sp + 0x30#64)
    (hnext : ∀ sf : State,
      sf.pc = lsmpl.base 333 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = sp + 0xb0#64 →
      sf.readReg64 .x8 = sp + 0x1260#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = sp + 0x30#64 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 →
      sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      sf.readReg64 .x30 = spqrSendPlacedEntry + 248#64 →
      SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) sf P post) :
    SepWP (spqrSendPlacedProg ext) (lsmpl.base 333) s P post := by
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  wp_steps
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩
    (by simp only [arm64_norm, *])

/-! ## `States.from_pb = .error (.err err)` Return Path -/

/-- Relocatable `States.from_pb = .error (.err err)` path (`+248 -> +872 -> +4608/+904 -> s0.lr`):
    copies the `Err` header from `sp + 0x1260..0x1280` via `sp + 0x930..0x948` to `ret` (`x19`),
    drops `pq.versionNegotiation` (if `some`) and `pq.chain`, and returns to `s0.lr`. -/
theorem spqr_send_states_from_pb_err_step_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (s0 s : State) (ret w0 w1 : BitVec 64)
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (err : LibsignalSpqrV1.Error) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1260 - 0xb0) ∗
        resultChunkedStatesAt A (F := F) ((s0.sp - 0x1f80#64) + 0x1260#64) (.error (.err err)) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1600#64) (0x1f20 - 0x1600) ∗
        memRegion ret 72 ∗
        A.pool ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          spqrSendResultAt A ret none ∗
          A.pool ∗
          stackAt s0.sp spqrSendStack ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  by_cases hslt : BitVec.slt w0 1#64 = true
  · have hge_false := slt_one_true_iff hslt
    refine seq_clean_lscro hcrl
      (mid := spqrSendPlacedEntry + 4608#64)
      (P_mid :=
        stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗
        (spqrSendResultAt A ret none ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split := resultChunkedStatesAt_err_entails_head32_896 A (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
              (sepConj_mono herr_split
                (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro rw8
      apply ProofLib.SepWP.exists_left; intro rw16
      apply ProofLib.SepWP.exists_left; intro rw24
      apply ProofLib.SepWP.exists_left; intro ew1
      apply ProofLib.SepWP.exists_left; intro ew2
      apply ProofLib.SepWP.exists_left; intro ew3
      apply ProofLib.SepWP.exists_left; intro s0_930
      apply ProofLib.SepWP.exists_left; intro s1_938
      apply ProofLib.SepWP.exists_left; intro s2_940
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := rejoin_b0_to_1f20_after_states_err fsp LibsignalTripleRatchetRepr.noneCap ew1 ew2 ew3
        have hret := err_ret_entails_sendResultAt_none A ret ew1 ew2 ew3
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              DecodeState.optVersionNegotiationPBTailAt A w0 w1 (fsp + 64#64) vn)) ∗
            (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
            ((ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn_drop) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · intro s2 hpc2 hrun2 hcrl2 ⟨hsp2, htr2, hvregs2⟩
      have hep := spqr_send_chain_drop_epilogue_4608_placed hdropChain s0 s2 chain
        (spqrSendResultAt A ret none ∗ Rest)
        hcrl2 hsp0_align hpc2 hrun2 hsp2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine seq_lscro hcrl
      (mid := spqrSendPlacedEntry + 904#64)
      (Mid := fun s1 P1 =>
        0 < w0.toNat ∧ w0.toNat < 2 ^ 63 ∧ w1 ≠ 0 ∧
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
          A.live w1 w0.toNat 1 ∗
          memRegion w1 w0.toNat ∗
          ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          A.pool ∗
          (spqrSendResultAt A ret none ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx26 ⊢
      have herr_split := resultChunkedStatesAt_err_entails_head32_896 A (F := F) (fsp + 4704#64) err
      have ha1268 : (fsp + 4704#64) + 8#64 = fsp + 4712#64 := by bv_omega
      have ha1270 : (fsp + 4704#64) + 16#64 = fsp + 4720#64 := by bv_omega
      have ha1278 : (fsp + 4704#64) + 24#64 = fsp + 4728#64 := by bv_omega
      have ha1280 : (fsp + 4704#64) + 32#64 = fsp + 4736#64 := by bv_omega
      rw [ha1268, ha1270, ha1278, ha1280] at herr_split
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono (memRegion_b0_to_1260_split_930 fsp)
              (sepConj_mono herr_split
                (sepConj_mono_right (sepConj_mono_left (memRegion_ret_72_split_err ret))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro rw8
      apply ProofLib.SepWP.exists_left; intro rw16
      apply ProofLib.SepWP.exists_left; intro rw24
      apply ProofLib.SepWP.exists_left; intro ew1
      apply ProofLib.SepWP.exists_left; intro ew2
      apply ProofLib.SepWP.exists_left; intro ew3
      apply ProofLib.SepWP.exists_left; intro s0_930
      apply ProofLib.SepWP.exists_left; intro s1_938
      apply ProofLib.SepWP.exists_left; intro s2_940
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
             DecodeState.optVersionNegotiationPBTailAt A w0 w1 (fsp + 64#64) vn) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
             ((fsp + 2352#64) ↦₆₄ ew1) ∗
             ((fsp + 2360#64) ↦₆₄ ew2) ∗
             ((fsp + 2368#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
             ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
             ((fsp + 4712#64) ↦₆₄ ew1) ∗
             ((fsp + 4720#64) ↦₆₄ ew2) ∗
             ((fsp + 4728#64) ↦₆₄ ew3) ∗
             memRegion (fsp + 4736#64) 896 ∗
             memRegion (fsp + 5632#64) (0x1f20 - 0x1600) ∗
             (ret ↦₆₄ 18446744073709551615#64) ∗
             ((ret + 8#64) ↦₆₄ ew1) ∗
             ((ret + 16#64) ↦₆₄ ew2) ∗
             ((ret + 24#64) ↦₆₄ ew3) ∗
             memRegion (ret + 32#64) 40 ∗
             A.pool ∗
             spqrSendSavedRegs fsp s0 ∗
             Rest) by ac_rfl))
          (sepConj_mono_left hvn_drop)) ?_
      wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      refine ⟨hw0_pos, hw0_lt, hw1_ne, ?_,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
      have hb0 := rejoin_b0_to_1f20_after_states_err fsp LibsignalTripleRatchetRepr.noneCap ew1 ew2 ew3
      have hret := err_ret_entails_sendResultAt_none A ret ew1 ew2 ew3
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion (fsp + 176#64) (0x930 - 0xb0) ∗
           ((fsp + 2352#64) ↦₆₄ ew1) ∗
           ((fsp + 2360#64) ↦₆₄ ew2) ∗
           ((fsp + 2368#64) ↦₆₄ ew3) ∗
           memRegion (fsp + 2376#64) (0x1260 - 0x948) ∗
           ((fsp + 4704#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
           ((fsp + 4712#64) ↦₆₄ ew1) ∗
           ((fsp + 4720#64) ↦₆₄ ew2) ∗
           ((fsp + 4728#64) ↦₆₄ ew3) ∗
           memRegion (fsp + 4736#64) 896 ∗
           memRegion (fsp + 5632#64) (0x1f20 - 0x1600)) ∗
          ((ret ↦₆₄ 18446744073709551615#64) ∗
           ((ret + 8#64) ↦₆₄ ew1) ∗
           ((ret + 16#64) ↦₆₄ ew2) ∗
           ((ret + 24#64) ↦₆₄ ew3) ∗
           memRegion (ret + 32#64) 40) ∗
          (stackAt fsp spqrSendCalleeStack ∗
           memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32 ∗
           A.live w1 w0.toNat 1 ∗
           memRegion w1 w0.toNat ∗
           ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hb0 (sepConj_mono_left hret)) ?_
      exact Entails.of_eq (by ac_rfl)
    · intro s1 P1 hpc1 hrun1 hcrl1 ⟨hw0_pos, hw0_lt, hw1_ne, hP1, hsp1, hx23_1, htr1, hvregs1⟩
      refine SepWP.weaken_pre hP1 ?_
      have hep := spqr_send_vn_chain_drop_epilogue_904_placed hA hdropChain s0 s1 w0 w1 chain
        (spqrSendResultAt A ret none ∗ Rest)
        hcrl1 hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-! ## `States.from_pb = .ok st0` Relocation and Jump-Table 1 Dispatch -/

/-- Relocatable `States.from_pb = .ok st0` relocation + jump-table 1 dispatch
    (`+248 -> spqrSendPlacedEntry + statesSendArmOffset st0`):
    relocates `chunkedStatesAt A (sp + 0x1260) st0` to `chunkedStatesAt A (sp + 0x950) st0`
    and dispatches across all 11 `States` variants to `spqrSendPlacedEntry + statesSendArmOffset st0`. -/
theorem spqr_send_states_from_pb_ok_step_placed
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    {s0 s : State} {sp : BitVec 64}
    {v1 : V1State} {st0 : States spqrPolyApi (spqrAuthApi F)} {Frame : SepProp}
    {target_pc : BitVec 64} {post : State → SepProp → Prop}
    (hpc : s.pc = spqrSendPlacedEntry + 248#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htrace : s.trace = s0.trace)
    (hx21 : s.readReg64 .x21 = sp + 0x1260#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hfrom : States.from_pb spqrPolyApi (spqrAuthApi F) v1 = .ok st0)
    (hnext : ∀ sf : State,
      sf.pc = spqrSendPlacedEntry + statesSendArmOffset st0 →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = chunkedStatesWord0 st0 →
      sf.readReg64 .x21 = sp + 0x1260#64 →
      sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = sp + 0x950#64 →
      sf.readReg64 .x25 = sp + 0x550#64 →
      sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x28 = sp + 0x1060#64 →
      (sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s) →
      SepWP (spqrSendPlacedProg ext) target_pc sf
        ((chunkedStatesAt A (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) target_pc s
      ((resultChunkedStatesAt A (F := F) (sp + 0x1260#64)
          (States.from_pb spqrPolyApi (spqrAuthApi F) v1) ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ Frame) post := by
  rw [hfrom]
  dsimp only [resultChunkedStatesAt]
  have hsplit_ok :
      ((chunkedStatesAt A (sp + 0x1260#64) st0 ∗
        memRegion (sp + 0x930#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendStatesJumpTablePlacedAt) ∗ Frame) ⊢
      ∃∗ bs : List (BitVec 8), ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ bs896 : List (BitVec 8),
        ⌜bs = unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ bs896 ∧ bs896.length = 896⌝ ∗
        (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
         ((sp + 0x1268#64) ↦₆₄ w1) ∗
         ((sp + 0x1270#64) ↦₆₄ w2) ∗
         ((sp + 0x1278#64) ↦₆₄ w3) ∗
         ((sp + 0x1280#64) ↦ₛ bs896) ∗
         relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
         memRegion (sp + 0x930#64) 24 ∗
         memRegion (sp + 0x950#64) 928 ∗
         spqrSendStatesJumpTablePlacedAt ∗ Frame) := by
    refine Entails.trans (sepConj_mono_left (sepConj_mono_left (chunkedStatesAt_1260_entails_reloc A sp st0))) ?_
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w1
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w2
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro w3
    rw [sepExists_sepConj_left, sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro bs896
    refine Entails.sepExists_right bs (Entails.sepExists_right w1
      (Entails.sepExists_right w2 (Entails.sepExists_right w3 (Entails.sepExists_right bs896 ?_))))
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hsplit_ok ?_
  apply ProofLib.SepWP.exists_left; intro bs
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro bs896
  refine SepWP.pure_elim fun ⟨hbs, hlen896⟩ => ?_
  rw [memRegion_sp_930_split_24 sp, memRegion_sp_950_split_4words_896 sp]
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro d3_968
  apply ProofLib.SepWP.exists_left; intro d2_960
  apply ProofLib.SepWP.exists_left; intro d1_958
  apply ProofLib.SepWP.exists_left; intro d0_950
  apply ProofLib.SepWP.exists_left; intro s2_940
  apply ProofLib.SepWP.exists_left; intro s1_938
  apply ProofLib.SepWP.exists_left; intro s0_930
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, spqrSendName, spqrSendRoSym, BitVec.ofNat_eq_ofNat] at hpc hnext ⊢
  wp_steps
  refine SepWP.call_subroutine_frame hmemcpy
    (x := (sp + 0x970#64, sp + 0x1280#64, bs896))
    (F := ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
      ((sp + 0x1268#64) ↦₆₄ w1) ∗
      ((sp + 0x1270#64) ↦₆₄ w2) ∗
      ((sp + 0x1278#64) ↦₆₄ w3) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
      ((sp + 0x930#64) ↦₆₄ w1) ∗
      ((sp + 0x938#64) ↦₆₄ w2) ∗
      ((sp + 0x940#64) ↦₆₄ w3) ∗
      ((sp + 0x950#64) ↦₆₄ d0_950) ∗
      ((sp + 0x958#64) ↦₆₄ d1_958) ∗
      ((sp + 0x960#64) ↦₆₄ d2_960) ∗
      ((sp + 0x968#64) ↦₆₄ d3_968) ∗
      spqrSendStatesJumpTablePlacedAt ∗ Frame)
    (ret_pc := (blkPl_124).base + 308#64)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by unfold State.spAligned; simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    ?_
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen896, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm]⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  · intro s1 hpc1 hrun1 hsp1 hcc1
    dsimp only [sessionMemcpyRegionSpec]
    rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr1⟩ => ?_
    have hsp1' : s1.sp = sp := by rw [hsp1]; simp only [arm64_norm, *]
    have htr1' : s1.trace = s0.trace := by rw [htr1]; simp only [arm64_norm, *]
    have hx19_1 : s1.readReg64 .x19 = s.readReg64 .x19 := by rw [hcc1.1]; simp only [arm64_norm, *]
    have hx20_1 : s1.readReg64 .x20 = chunkedStatesWord0 st0 := by rw [hcc1.2.1]; simp only [arm64_norm, *]
    have hx21_1 : s1.readReg64 .x21 = sp + 0x1260#64 := by rw [hcc1.2.2.1]; simp only [arm64_norm, *]
    have hx22_1 : s1.readReg64 .x22 = s.readReg64 .x22 := by rw [hcc1.2.2.2.1]; simp only [arm64_norm, *]
    have hx23_1 : s1.readReg64 .x23 = s.readReg64 .x23 := by rw [hcc1.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx24_1 : s1.readReg64 .x24 = sp + 0x950#64 := by rw [hcc1.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx25_1 : s1.readReg64 .x25 = sp + 0x550#64 := by rw [hcc1.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx26_1 : s1.readReg64 .x26 = sp + 0x1260#64 := by rw [hcc1.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx28_1 : s1.readReg64 .x28 = sp + 4192#64 := by rw [hcc1.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hx29_1 : s1.readReg64 .x29 = s.readReg64 .x29 := by rw [hcc1.2.2.2.2.2.2.2.2.2.2.1]; simp only [arm64_norm, *]
    have hvregs_1 : calleeSavedVRegs s1 = calleeSavedVRegs s := by rw [hcc1.2.2.2.2.2.2.2.2.2.2.2]; simp only [wp_norm, arm64_norm, *]
    have hreasm :
        ((sp + 0x970#64) ↦ₛ bs896) ∗
        ((sp + 0x1280#64) ↦ₛ bs896) ∗
        ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x1268#64) ↦₆₄ w1) ∗
        ((sp + 0x1270#64) ↦₆₄ w2) ∗
        ((sp + 0x1278#64) ↦₆₄ w3) ∗
        relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
        ((sp + 0x930#64) ↦₆₄ w1) ∗
        ((sp + 0x938#64) ↦₆₄ w2) ∗
        ((sp + 0x940#64) ↦₆₄ w3) ∗
        ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
        ((sp + 0x958#64) ↦₆₄ w1) ∗
        ((sp + 0x960#64) ↦₆₄ w2) ∗
        ((sp + 0x968#64) ↦₆₄ w3) ∗
        spqrSendStatesJumpTableWordsAt (lsρ spqrSendRoSym) ∗ Frame ⊢
        (chunkedStatesAt A (sp + 0x950#64) st0 ∗
          memRegion (sp + 0x930#64) 24 ∗
          memRegion (sp + 0x1260#64) 928 ∗
          spqrSendStatesJumpTablePlacedAt) ∗ Frame := by
      rw [← spqrSendStatesJumpTablePlacedAt_eq_words]
      have hst := reassemble_chunkedStatesAt_950 A sp st0 w1 w2 w3 hbs
      have h930 := words3_930_entails_memRegion_24 sp w1 w2 w3
      have h1260 := reassemble_1260_after_memcpy sp (chunkedStatesWord0 st0) w1 w2 w3 hlen896
      have hreord1 :
          ((sp + 0x970#64) ↦ₛ bs896) ∗
          ((sp + 0x1280#64) ↦ₛ bs896) ∗
          ((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x1268#64) ↦₆₄ w1) ∗
          ((sp + 0x1270#64) ↦₆₄ w2) ∗
          ((sp + 0x1278#64) ↦₆₄ w3) ∗
          relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs ∗
          ((sp + 0x930#64) ↦₆₄ w1) ∗
          ((sp + 0x938#64) ↦₆₄ w2) ∗
          ((sp + 0x940#64) ↦₆₄ w3) ∗
          ((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
          ((sp + 0x958#64) ↦₆₄ w1) ∗
          ((sp + 0x960#64) ↦₆₄ w2) ∗
          ((sp + 0x968#64) ↦₆₄ w3) ∗
          spqrSendStatesJumpTablePlacedAt ∗ Frame =
          ((((sp + 0x950#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x958#64) ↦₆₄ w1) ∗
            ((sp + 0x960#64) ↦₆₄ w2) ∗
            ((sp + 0x968#64) ↦₆₄ w3) ∗
            ((sp + 0x970#64) ↦ₛ bs896) ∗
            relocatedHeap (fun dst => chunkedStatesTail920At A dst st0) bs) ∗
           (((sp + 0x930#64) ↦₆₄ w1) ∗
            ((sp + 0x938#64) ↦₆₄ w2) ∗
            ((sp + 0x940#64) ↦₆₄ w3)) ∗
           (((sp + 0x1260#64) ↦₆₄ chunkedStatesWord0 st0) ∗
            ((sp + 0x1268#64) ↦₆₄ w1) ∗
            ((sp + 0x1270#64) ↦₆₄ w2) ∗
            ((sp + 0x1278#64) ↦₆₄ w3) ∗
            ((sp + 0x1280#64) ↦ₛ bs896)) ∗
           spqrSendStatesJumpTablePlacedAt) ∗ Frame := by ac_rfl
      rw [hreord1]
      exact sepConj_mono_left (sepConj_mono hst (sepConj_mono h930 (sepConj_mono_left h1260)))
    rw [spqrSendStatesJumpTablePlacedAt_eq_words]
    dsimp only [spqrSendStatesJumpTableWordsAt, spqrSendRoSym, BitVec.ofNat_eq_ofNat] at hreasm ⊢
    cases st0 with
    | ct1Sampled st =>
      dsimp only [chunkedStatesWord0, statesSendArmOffset, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm hnext ⊢
      cases hs : st.sending_ct1.s <;>
        { rw [hs] at hx20_1 hreasm
          dsimp only [polyEncoderTagVal, polyEncoderPointsTag, polyEncoderPolysTag, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm ⊢
          wp_steps 16
          refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hreasm) ?_
          exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, polyEncoderTagVal, polyEncoderPointsTag, polyEncoderPolysTag, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
            (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩ }
    | keysUnsampled _ | keysSampled _ | headerSent _ | ct1Received _
    | ekSentCt1Received _ | noHeaderReceived _ | headerReceived _
    | ekReceivedCt1Sampled _ | ct1Acknowledged _ | ct2Sampled _ =>
      dsimp only [chunkedStatesWord0, statesSendArmOffset, BitVec.ofNat_eq_ofNat] at hx20_1 hreasm hnext ⊢
      wp_steps 16
      refine SepWP.weaken_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hreasm) ?_
      exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) ⟨by simp only [arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩

end CryptoVerification.SpqrV1.Top.Send
