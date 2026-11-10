/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1FromPb
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1Steps
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WPFrozen

/-!
# Relocatable `spqr::send::<HookRng>` Phase 1b: Inner-State Unpack (Block 124)

Verifies `spqr_send_inner_none_step_placed` (`+156 -> s0.lr`) and
`spqr_send_inner_some_to_224_placed` (`+156 -> +224`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
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

attribute [local simp, local arm64_norm, local wp_norm]
  none3Cap_add_three_beq_zero

theorem seq_lscro {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P : SepProp} {Mid : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P Mid)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Mid sm Pm → SepWP prog tgt sm Pm post) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ hf hkf => LibsignalCodeRoLoaded.of_keepsFrozen hf hkf) hcrl
    (SepWP.mono_frozen (fun _ _ hf hkf => LibsignalCodeRoLoaded.of_keepsFrozen hf hkf) hcrl h1
      (fun sm Pm hpcm hrunm hcrl_m hMid _ => h2 sm Pm hpcm hrunm hcrl_m hMid))

/-- Relocatable `pq.inner = none` path from `+156` to `s0.lr`:
    loads `[sp + 0xb0] = none3Cap`, finishes relocating `pq.versionNegotiation` to `sp + 0x30`,
    writes `Ok(Send { state: [], msg: [], key: None })` to `*ret`, and drops
    `pq.versionNegotiation` and `pq.chain` before returning. -/
theorem spqr_send_inner_none_step_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hdropChain : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 136)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (s0 s : State) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB)
    (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hlen16 : bs16.length = 16)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) none ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        memRegion ret 72 ∗
        A.pool ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          spqrSendResultAt A ret (some ([], none, [])) ∗
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
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest))
      (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, DecodeState.optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro r8
      apply ProofLib.SepWP.exists_left; intro r16
      apply ProofLib.SepWP.exists_left; intro r24
      apply ProofLib.SepWP.exists_left; intro r32
      apply ProofLib.SepWP.exists_left; intro r40
      apply ProofLib.SepWP.exists_left; intro r48
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
        have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
        have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
        have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
        have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
        rw [ha56, ha64, ha72, ha80] at hvn_raw
        have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
        rw [ha56, ha64, hslt] at hvn_drop
        simp only [↓reduceIte] at hvn_drop
        have hvn48 := Entails.trans hvn_raw hvn_drop
        have h60 : memRegion fsp 48 ∗ memRegion (fsp + 48#64) 48 ⊢ memRegion fsp 96 := by
          rw [memRegion_rejoin_30_48 fsp]
          exact Entails.refl _
        have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
        have hret := empty_ok_sendResult_entails A ret
        refine Entails.trans
          (Entails.of_eq (show _ =
            (memRegion fsp 48 ∗
             (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
              ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
              ((fsp + 80#64) ↦ₛ bs16) ∗
              (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
                ((unpack64 w2 ++ unpack64 w3) ++ bs16))) ∗
            (((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
            ((ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans
          (sepConj_mono (Entails.trans (sepConj_mono_right hvn48) h60)
            (sepConj_mono hb0 (sepConj_mono_left hret))) ?_
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    · intro s2 hpc2 hrun2 hcrl2 ⟨hsp2, htr2, hvregs2⟩
      have hep := spqr_send_chain_drop_epilogue_4608_placed hdropChain s0 s2 chain
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)
        hcrl2 hsp0_align hpc2 hrun2 hsp2
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩
  · have hslt_f : BitVec.slt w0 1#64 = false := Bool.eq_false_iff.mpr hslt
    have hge_true := slt_one_false_iff hslt_f
    refine seq_lscro hcrl (mid := spqrSendPlacedEntry + 904#64)
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
          (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x23 = w0 ∧
        s1.trace = s.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0)
      ?_ ?_
    · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, DecodeState.optProtoPqRatchetInnerAt,
        BitVec.ofNat_eq_ofNat] at hpc ⊢
      generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 ⊢
      have hvn_raw := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
      have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
      have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
      have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
      have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
      rw [ha56, ha64, ha72, ha80] at hvn_raw
      have hvn_drop := optVersionNegotiationPBTail_cleanup_entails A (fsp + 48#64) w0 w1 vn
      rw [ha56, ha64, hslt_f] at hvn_drop
      simp only [Bool.false_eq_true, ↓reduceIte] at hvn_drop
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left (memRegion_sendResult_split_56 ret)))))))))))))))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro r0
      apply ProofLib.SepWP.exists_left; intro r8
      apply ProofLib.SepWP.exists_left; intro r16
      apply ProofLib.SepWP.exists_left; intro r24
      apply ProofLib.SepWP.exists_left; intro r32
      apply ProofLib.SepWP.exists_left; intro r40
      apply ProofLib.SepWP.exists_left; intro r48
      wp_steps
      have hvn_all := Entails.trans hvn_raw hvn_drop
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
             ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
             ((fsp + 80#64) ↦ₛ bs16) ∗
             (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
               ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 48 ∗
             ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
             ((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
             memRegion (fsp + 184#64) 216 ∗
             ((fsp + 400#64) ↦₆₄ w1) ∗
             ((fsp + 408#64) ↦₆₄ w2) ∗
             ((fsp + 416#64) ↦₆₄ w3) ∗
             memRegion (fsp + 424#64) (0x1f20 - 0x1a8) ∗
             (ret ↦₆₄ 0#64) ∗
             ((ret + 8#64) ↦₆₄ 1#64) ∗
             ((ret + 16#64) ↦₆₄ 0#64) ∗
             ((ret + 24#64) ↦₆₄ 0#64) ∗
             ((ret + 32#64) ↦₆₄ 1#64) ∗
             ((ret + 40#64) ↦₆₄ 0#64) ∗
             ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
             memRegion (ret + 56#64) 16 ∗
             A.pool ∗
             spqrSendSavedRegs fsp s0 ∗
             Rest) by ac_rfl))
          (sepConj_mono_left hvn_all)) ?_
      wp_focus_pure; rintro ⟨hw0_pos, hw0_lt, hw1_ne⟩
      refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
      refine ⟨hw0_pos, hw0_lt, hw1_ne, ?_,
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *],
        by simp only [wp_norm, arm64_norm, *]⟩
      have hb0 := inner_none_b0_rejoin fsp w1 w2 w3
      have hret := empty_ok_sendResult_entails A ret
      refine Entails.trans
        (Entails.of_eq (show _ =
          (((fsp + 176#64) ↦₆₄ DecodeState.none3Cap) ∗
           memRegion (fsp + 184#64) 216 ∗
           ((fsp + 400#64) ↦₆₄ w1) ∗
           ((fsp + 408#64) ↦₆₄ w2) ∗
           ((fsp + 416#64) ↦₆₄ w3) ∗
           memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
          ((ret ↦₆₄ 0#64) ∗
           ((ret + 8#64) ↦₆₄ 1#64) ∗
           ((ret + 16#64) ↦₆₄ 0#64) ∗
           ((ret + 24#64) ↦₆₄ 0#64) ∗
           ((ret + 32#64) ↦₆₄ 1#64) ∗
           ((ret + 40#64) ↦₆₄ 0#64) ∗
           ((ret + 48#64) ↦₆₄ 18446744073709551615#64) ∗
           memRegion (ret + 56#64) 16) ∗
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
        (spqrSendResultAt A ret (some ([], none, [])) ∗ Rest)
        hcrl1 hsp0_align hpc1 hrun1 hsp1 hx23_1 hw0_pos hw0_lt hw1_ne
      refine SepWP.mono hep ?_
      intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
      refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr1⟩

/-- Relocatable `pq.inner = some (.v1 v1)` step (`+156 -> +224`):
    loads `w_in ≠ none3Cap` from `[sp + 0xb0]`, completes the 32-byte relocation of
    `pq.versionNegotiation` into `[sp + 0x30..0x50)`, and branches to `+224`. -/
theorem spqr_send_inner_some_to_224_placed {H_inner : V1InnerHeapPred} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h_inner_eq : ∀ a st, DecodeState.optProtoInnerStateAt H_inner A a st = Drop.optProtoInnerStateAt A a st)
    (s0 s : State) (ret : BitVec 64)
    (w0 w1 w2 w3 w30 w38 w40 w48 : BitVec 64) (bs16 : List (BitVec 8))
    (vn : Option VersionNegotiationPB) (chain : Option ChainPB) (v1 : V1State)
    (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 156#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64)
    (hlen16 : bs16.length = 16) :
    SepWP (spqrSendPlacedProg ext) (spqrSendPlacedEntry + 224#64) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w30) ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w38) ∗
        (((s0.sp - 0x1f80#64) + 0x40#64) ↦₆₄ w40) ∗
        (((s0.sp - 0x1f80#64) + 0x48#64) ↦₆₄ w48) ∗
        (((s0.sp - 0x1f80#64) + 0x50#64) ↦ₛ bs16) ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
        DecodeState.optProtoPqRatchetInnerAt H_inner A ((s0.sp - 0x1f80#64) + 0xb0#64) (some (.v1 v1)) ∗
        (((s0.sp - 0x1f80#64) + 0x190#64) ↦₆₄ w1) ∗
        (((s0.sp - 0x1f80#64) + 0x198#64) ↦₆₄ w2) ∗
        (((s0.sp - 0x1f80#64) + 0x1a0#64) ↦₆₄ w3) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x1a8#64) (0x1f20 - 0x1a8) ∗
        (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
          ((unpack64 w2 ++ unpack64 w3) ++ bs16) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        Rest)
      (fun sm Pm =>
        (Pm ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x30 ∗
          (((s0.sp - 0x1f80#64) + 0x30#64) ↦₆₄ w0) ∗
          (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
          DecodeState.optVersionNegotiationPBTailAt A w0 w1 ((s0.sp - 0x1f80#64) + 0x40#64) vn ∗
          ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) chain ∗
          Drop.optProtoInnerStateAt A ((s0.sp - 0x1f80#64) + 0xb0#64) v1.innerState ∗
          memRegion ((s0.sp - 0x1f80#64) + 0x190#64) (0x1f20 - 0x190) ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
          Rest) ∧
        sm.sp = s0.sp - 0x1f80#64 ∧
        sm.readReg64 .x19 = ret ∧
        sm.readReg64 .x20 = (s0.sp - 0x1f80#64) + 0x30#64 ∧
        sm.readReg64 .x23 = w0 ∧
        sm.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        sm.trace = s.trace ∧
        calleeSavedVRegs sm = calleeSavedVRegs s) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, DecodeState.optProtoPqRatchetInnerAt,
    BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [h_inner_eq]
  generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align hx20 hx26 ⊢
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (optProtoInnerStateAt_expose_head A (fsp + 176#64) v1.innerState)))))))))) ?_
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro win
  wp_focus_pure; intro hwin_ne
  have hwin_br := ne_none3Cap_add_three_beq_zero_false hwin_ne
  have hwin_bne := ne_none3Cap_add_three_bne_zero_true hwin_ne
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) ?_
  refine ⟨?_,
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *],
    by simp only [wp_norm, arm64_norm, *]⟩
  have hvn := reassemble_optVersionNegotiationPBTail_raw A (fsp + 48#64) w0 w1 w2 w3 bs16 vn hlen16
  have ha56 : (fsp + 48#64) + 8#64 = fsp + 56#64 := by bv_omega
  have ha64 : (fsp + 48#64) + 16#64 = fsp + 64#64 := by bv_omega
  have ha72 : (fsp + 48#64) + 24#64 = fsp + 72#64 := by bv_omega
  have ha80 : (fsp + 48#64) + 32#64 = fsp + 80#64 := by bv_omega
  rw [ha56, ha64, ha72, ha80] at hvn
  have hin := optProtoInnerStateAt_unexpose_head A (fsp + 176#64) win v1.innerState
  have h190 := rejoin_190_to_1f20 fsp w1 w2 w3
  refine Entails.trans
    (Entails.of_eq (show _ =
      (((fsp + 48#64) ↦₆₄ w0) ∗ ((fsp + 56#64) ↦₆₄ w1) ∗
       ((fsp + 64#64) ↦₆₄ w2) ∗ ((fsp + 72#64) ↦₆₄ w3) ∗
       ((fsp + 80#64) ↦ₛ bs16) ∗
       (relocOptVersionNegotiationPBTailAt A w0 w1 vn).1
         ((unpack64 w2 ++ unpack64 w3) ++ bs16)) ∗
      (((fsp + 176#64) ↦₆₄ win) ∗ optProtoInnerStateHeadRest A (fsp + 176#64) win v1.innerState) ∗
      (((fsp + 400#64) ↦₆₄ w1) ∗ ((fsp + 408#64) ↦₆₄ w2) ∗
       ((fsp + 416#64) ↦₆₄ w3) ∗ memRegion (fsp + 424#64) (0x1f20 - 0x1a8)) ∗
      (stackAt fsp spqrSendCalleeStack ∗
       memRegion fsp 48 ∗
       ProtoRepr.optChainPBAt A (fsp + 96#64) chain ∗
       spqrSendSavedRegs fsp s0 ∗
       Rest) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hvn (sepConj_mono hin (sepConj_mono_left h190))) ?_
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
