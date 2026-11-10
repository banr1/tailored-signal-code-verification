/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Phase1
import ProofLib.SepLogic.WPp

/-!
# Relocatable Phase 1 Prologue & Shared Epilogues for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)

Proves relocatable `.rodata` jump-table unpacking, the prologue (`+0 -> +76`), and shared
cleanup/return epilogues (`+904`, `+4608`, `+4632 -> s0.lr`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth hiding Entails.sepExists_elim
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.EncoderFromPb
open CryptoVerification.SpqrV1.Poly.NextChunk (AllocContractsPlaced)
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.EncodeVarint
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  CryptoVerification.SpqrV1.Drop.none2Cap_add_two_beq_zero
  CryptoVerification.SpqrV1.Drop.noneCap_add_two_beq_zero

attribute [local simp, local arm64_norm, local wp_norm]
  Top.Send.sp_sub_96_add_16 Top.Send.sp_sub_96_add_32 Top.Send.sp_sub_96_add_48
  Top.Send.sp_sub_96_add_64 Top.Send.sp_sub_96_add_80
  sp_sub_96_sub_4096 sp_sub_4192_sub_3872 sp_sub_8064_add_4096 sp_sub_3968_add_3872
  sp_sub_8064_add_7968 sp_sub_8064_add_7976 sp_sub_8064_add_7984 sp_sub_8064_add_7992
  sp_sub_8064_add_8000 sp_sub_8064_add_8008 sp_sub_8064_add_8016 sp_sub_8064_add_8024
  sp_sub_8064_add_8032 sp_sub_8064_add_8040 sp_sub_8064_add_8048 sp_sub_8064_add_8056
  sp_sub_3968_add_608 fsp_add_30_add_30

/-! ## 1. Sequencing with `LibsignalCodeRoLoaded` Preservation -/

theorem seq_clean_lscro {prog : Program} {mid tgt : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q sm →
      SepWP prog tgt sm P_mid post) :
    SepWP prog tgt s P post := by
  refine sepWP_seq_lscro hcrl (SepWP.mono h1 ?_)
  intro sm Pm hpc hrun ⟨hPm, hQ⟩ hcrl_m
  exact SepWP.weaken_pre hPm (h2 sm hpc hrun hcrl_m hQ)

/-! ## 2. `.rodata` Jump Table Extraction from `LibsignalRoLoaded lsmpl s.mem` -/

/-- The 64-byte `.rodata` symbol `spqrSendRoSym` decomposes into the three jump tables
    (`22 + 22 + 20 = 64` bytes) of `spqr::send::<signal_session_ratchet::Coins>`. -/
theorem spqrSendRoSym_bytes_split :
    ((lsρ spqrSendRoSym) ↦ᵣ
      (spqrSendStatesJumpTableBytes ++
        (spqrSendEncodeJumpTableBytes ++ spqrSendDropJumpTableBytes))) =
      (spqrSendStatesJumpTablePlacedAt ∗
        spqrSendEncodeJumpTablePlacedAt ∗
        spqrSendDropJumpTablePlacedAt) := by
  have h1 := ProofLib.pointsToBytesRO_append (lsρ spqrSendRoSym)
    spqrSendStatesJumpTableBytes
    (spqrSendEncodeJumpTableBytes ++ spqrSendDropJumpTableBytes)
  have h2 := ProofLib.pointsToBytesRO_append
    (lsρ spqrSendRoSym + BitVec.ofNat 64 spqrSendStatesJumpTableBytes.length)
    spqrSendEncodeJumpTableBytes
    spqrSendDropJumpTableBytes
  have hlen1 : BitVec.ofNat 64 spqrSendStatesJumpTableBytes.length = 22#64 := by decide
  have hlen2 : (lsρ spqrSendRoSym + 22#64) + BitVec.ofNat 64 spqrSendEncodeJumpTableBytes.length =
      lsρ spqrSendRoSym + 44#64 := by
    have : BitVec.ofNat 64 spqrSendEncodeJumpTableBytes.length = 22#64 := by decide
    rw [this]; bv_omega
  rw [hlen1] at h1 h2
  rw [hlen2] at h2
  rw [h1, h2]
  rfl

/-- Extract the three `spqr::send` jump tables from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_spqrSendJumpTablesPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ spqrSendStatesJumpTablePlacedAt ∗
      spqrSendEncodeJumpTablePlacedAt ∗
      spqrSendDropJumpTablePlacedAt ∗ P := by
  have h64 : s.mem ⊨
      ((lsρ spqrSendRoSym) ↦ᵣ
        (spqrSendStatesJumpTableBytes ++
          (spqrSendEncodeJumpTableBytes ++ spqrSendDropJumpTableBytes))) ∗ P :=
    lsro_intro_chk (sym := spqrSendRoSym)
      (bs := spqrSendStatesJumpTableBytes ++
        (spqrSendEncodeJumpTableBytes ++ spqrSendDropJumpTableBytes))
      hro (by decide +kernel) hP
  rwa [spqrSendRoSym_bytes_split, sepConj_assoc, sepConj_assoc] at h64

/-- Extract `statesFromPbJumpTablePlacedAt` from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_statesFromPbJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesFromPbJumpTablePlacedAt ∗ P := by
  unfold statesFromPbJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := "spqr:.rodata.<spqr::v1::chunked::states::States>::from_pb")
    (bs := statesFromPbJumpTableBytes)
    hro (by decide +kernel) hP

/-- Extract `statesIntoPbJumpTablePlacedAt` from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_statesIntoPbJumpTablePlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ statesIntoPbJumpTablePlacedAt ∗ P := by
  unfold statesIntoPbJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := "spqr:.rodata.<spqr::v1::chunked::states::States>::into_pb")
    (bs := statesIntoPbJumpTableBytes)
    hro (by decide +kernel) hP

/-- Extract `Prost.MessageMerge.v1StateJumpTablesPlacedAt` from `LibsignalRoLoaded lsmpl s.mem`. -/
theorem lsro_v1StateJumpTablesPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt ∗ P := by
  unfold CryptoVerification.SpqrV1.Prost.MessageMerge.v1StateJumpTablesPlacedAt
  rw [sepConj_assoc]
  refine CryptoVerification.SpqrV1.Prost.MessageMerge.rodata_v1StateMergeJumpTablePlacedExpanded hro ?_
  unfold Drop.optProtoInnerStateJumpTablePlacedAt
  exact lsro_intro_chk
    (sym := Drop.optProtoInnerStateJumpTableSym)
    (bs := Drop.optProtoInnerStateJumpTableBytes)
    hro (by decide +kernel) hP

/-- Extract the full `spqrSendRoPlacedAt` bundle from `LibsignalRoLoaded lsmpl s.mem`
    and `GF.Mul2U16.tokenInitPlacedAt`. -/
theorem lsro_spqrSendRoPlacedAt {s : State} (hro : LibsignalRoLoaded lsmpl s.mem)
    {P : SepProp} (hP : s.mem ⊨ CryptoVerification.SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ P) :
    s.mem ⊨ spqrSendRoPlacedAt ∗ P := by
  unfold spqrSendRoPlacedAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine lsro_spqrSendJumpTablesPlacedAt hro ?_
  refine lsro_v1StateJumpTablesPlacedAt hro ?_
  refine lsro_statesFromPbJumpTablePlacedAt hro ?_
  refine lsro_statesIntoPbJumpTablePlacedAt hro ?_
  exact CryptoVerification.SpqrV1.GF.UnacceleratedMul.rodata_reduceTable_placed hro hP

/-! ## 3. Shared Epilogue (`+4632 -> s0.lr`) -/

/-- Relocatable epilogue (`+4632 -> s0.lr`):
    adds `0x1000 + 0xf20 = 0x1f20` (`7968`) to `sp = s0.sp - 0x1f80`, restores `x19..x30`
    from `s0.sp - 96`, and executes `ret`. -/
theorem spqr_send_epilogue_4632_placed {ext : String → Option (State → State)}
    (s0 s : State) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4632#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  rw [spqrSendSavedRegs_eq_sp0 s0]
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · have hrest := stack_restore_spqrSend s0.sp s0
    rw [spqrSendSavedRegs_eq_sp0 s0] at hrest
    refine Entails.trans
      (Entails.of_eq (show _ =
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) ∗ Rest by ac_rfl))
      (sepConj_mono_left hrest)
  · wp_done

/-! ## 4. Prologue (`+0 -> +76`) -/

/-- Relocatable prologue (`+0 -> +76`):
    saves `x19..x30` at `s0.sp - 96`, sets `x29 = s0.sp - 96`, `sp = s0.sp - 0x1f80`,
    `x19 = ret`, `x0 = stV`, `x8 = x21 = x26 = sp + 0x1260`, and probes `[s0.sp - 4192]` and `[sp]`. -/
theorem spqr_send_prologue_placed {ext : String → Option (State → State)}
    (s0 : State) (ret stV : BitVec 64) (Rest : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s0.pc = spqrSendPlacedEntry)
    (hrun : s0.status = .Running)
    (hx0 : s0.readReg64 .x0 = ret)
    (hx1 : s0.readReg64 .x1 = stV) :
    SepWP (spqrSendPlacedProg ext)
      (spqrSendPlacedEntry + 76#64) s0
      (stackAt s0.sp spqrSendStack ∗ Rest)
      (fun s1 P1 =>
        (P1 ⊢
          stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
          memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
          spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗ Rest) ∧
        s1.sp = s0.sp - 0x1f80#64 ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        s1.readReg64 .x19 = ret ∧
        s1.readReg64 .x0 = stV ∧
        s1.readReg64 .x8 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x21 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.readReg64 .x26 = (s0.sp - 0x1f80#64) + 0x1260#64 ∧
        s1.trace = s0.trace ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s0) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hsp4192_align : ((s0.sp - 4192#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 4192#64 hsp0_align (by decide)
  have hsp96_align : ((s0.sp - 96#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 96#64 hsp0_align (by decide)
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_conv_pre =>
    rw [stackAt_spqrSend_eq_callee_and_frame s0.sp,
        sp_sub_8064_add_7968 s0.sp,
        ProofLib.memRegion_cells (s0.sp - 96#64) 12 (by decide),
        memRegion_7968_split_probes s0.sp]
  cells_unfold
  wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply ProofLib.SepWP.exists_left; intro w0
  apply ProofLib.SepWP.exists_left; intro w1
  apply ProofLib.SepWP.exists_left; intro w2
  apply ProofLib.SepWP.exists_left; intro w3
  apply ProofLib.SepWP.exists_left; intro w4
  apply ProofLib.SepWP.exists_left; intro w5
  apply ProofLib.SepWP.exists_left; intro w6
  apply ProofLib.SepWP.exists_left; intro w7
  apply ProofLib.SepWP.exists_left; intro w8
  apply ProofLib.SepWP.exists_left; intro w9
  apply ProofLib.SepWP.exists_left; intro w10
  apply ProofLib.SepWP.exists_left; intro w11
  apply ProofLib.SepWP.exists_left; intro v_probe
  apply ProofLib.SepWP.exists_left; intro v0
  wp_steps
  refine EncoderFromPb.align_pre ?_ ?_
  · rw [spqrSendSavedRegs_eq_sp0 s0]
    have hfsp := probes_entails_memRegion_7968 s0.sp 0#64 0#64
    refine Entails.trans
      (Entails.of_eq (show _ =
        (((s0.sp - 0x1f80#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 8056#64) 3864 ∗
         ((s0.sp - 4192#64) ↦₆₄ 0#64) ∗
         memRegion (s0.sp - 4184#64) 4088) ∗
        (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) ∗
         Rest) by ac_rfl))
      (Entails.trans (sepConj_mono_left hfsp) (Entails.of_eq (by ac_rfl)))
  · wp_done

/-! ## 5. Shared Cleanup Epilogues (`+4608` and `+904`) -/

/-- Relocatable shared `st.chain` drop + register-restore epilogue (`+4608 -> s0.lr`):
    drops `ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh` (calling Block `439`
    when `some`), rejoins `memRegion (s0.sp - 0x1f80#64) 0x1f20`, and runs `spqr_send_epilogue_4632_placed`. -/
theorem spqr_send_chain_drop_epilogue_4608_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (s0 s : State) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 4608#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x60 ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  refine EncoderFromPb.seq_clean
    (mid := spqrSendPlacedEntry + 4632#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x1f20 ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      (A.pool ∗ Rest))
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry,
      withLsCodeRoLoaded, dropProtoSpqrChainSpec, chainPBSize, BitVec.ofNat_eq_ofNat] at hpc hdrop ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    cases optCh with
    | none =>
      have hnone : ProtoRepr.optChainPBAt A (fsp + 96#64) none =
          (((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap) ∗
           memRegion ((fsp + 96#64) + 8#64) 72) := rfl
      wp_conv_pre => rw [hnone]
      wp_steps
      refine EncoderFromPb.align_pre ?_ ?_
      · have hch := optChainPBAt_none_entails_memRegion_80' A (fsp + 96#64)
        rw [hnone] at hch
        refine Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ LibsignalTripleRatchetRepr.noneCap ∗
             memRegion ((fsp + 96#64) + 8#64) 72) ∗
            (memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             stackAt fsp spqrSendCalleeStack ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono_left hch) ?_
        rw [← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
    | some ch =>
      have hsome : ProtoRepr.optChainPBAt A (fsp + 96#64) (some ch) =
          ProtoRepr.chainPBAt A (fsp + 96#64) ch := rfl
      wp_conv_pre => rw [hsome]
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (chainPBAt_entails_first_word A (fsp + 96#64) ch)))) ?_
      wp_simp_pre [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      apply ProofLib.SepWP.exists_left; intro cap
      apply ProofLib.SepWP.exists_left; intro ptr
      wp_focus_pure; intro hcap_lt
      have hne_none := Top.Send.cap_add_one_beq_zero_false hcap_lt
      wp_steps
      refine SepWP.weaken_pre
        (Entails.trans
          (Entails.of_eq (show _ =
            ((fsp + 96#64) ↦₆₄ cap ∗
             chainPBRestAt A (fsp + 96#64) cap ptr ch) ∗
            (stackAt fsp spqrSendCalleeStack ∗
             memRegion fsp 96 ∗
             memRegion (fsp + 176#64) 7792 ∗
             spqrSendSavedRegs fsp s0 ∗
             A.pool ∗ Rest) by ac_rfl))
          (sepConj_mono_left (first_word_entails_chainPBAt A (fsp + 96#64) cap ptr ch))) ?_
      wp_conv_pre => rw [stackAt_spqrSendCallee_split_dropStack48 fsp]
      have hcl : LibsignalCodeLoaded lsmpl s.mem := hcrl.1
      have hro : LibsignalRoLoaded lsmpl s.mem := hcrl.2
      wp_call hdrop ⟨fsp + 96#64, ch⟩
      refine EncoderFromPb.align_pre ?_ ?_
      · rw [hsp, stackAt_spqrSendCallee_split_dropStack48 fsp,
            ← memRegion_rejoin_60_80 fsp]
        exact Entails.of_eq (by ac_rfl)
      · wp_done
  · intro s2 hpc2 hrun2 ⟨hsp2, htr2, hvregs2⟩
    have hep := spqr_send_epilogue_4632_placed (ext := ext) s0 s2 (A.pool ∗ Rest) hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcc_f, htr_f.trans htr2⟩

/-- Relocatable shared `st.version_negotiation.auth_key` dealloc + `st.chain` drop + register-restore epilogue
    (`+904 -> s0.lr`):
    loads `w1` from `[sp + 0x38]`, calls `__rust_dealloc(w1, w0.toNat, 1)`, and jumps to `+4608`. -/
theorem spqr_send_vn_chain_drop_epilogue_904_placed {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced A ext)
    (hdrop : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 439)
      (withLsCodeRoLoaded lsmpl (dropProtoSpqrChainSpec A)))
    (s0 s : State) (w0 w1 : BitVec 64) (optCh : Option ChainPB) (Rest : SepProp)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 904#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0x1f80#64)
    (hx23 : s.readReg64 .x23 = w0)
    (hw0_pos : 0 < w0.toNat)
    (hw0_lt : w0.toNat < 2 ^ 63)
    (hw1_ne : w1 ≠ 0)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0 := by simp only [wp_norm, arm64_norm, *]) :
    SepWP (spqrSendPlacedProg ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
        memRegion (s0.sp - 0x1f80#64) 0x30 ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x30#64) 8 ∗
        (((s0.sp - 0x1f80#64) + 0x38#64) ↦₆₄ w1) ∗
        memRegion ((s0.sp - 0x1f80#64) + 0x40#64) 32 ∗
        A.live w1 w0.toNat 1 ∗
        memRegion w1 w0.toNat ∗
        ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
        memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
        spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
        A.pool ∗ Rest)
      (fun sf Pf =>
        (Pf ⊢ stackAt s0.sp spqrSendStack ∗ A.pool ∗ Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s.trace) := by
  have hfsp_align : ((s0.sp - 0x1f80#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 0x1f80#64 hsp0_align (by decide)
  have hdealloc_raw : subroutine_ok (spqrSendPlacedProg ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem hA.dealloc
  refine seq_clean_lscro hcrl
    (mid := spqrSendPlacedEntry + 4608#64)
    (P_mid :=
      stackAt (s0.sp - 0x1f80#64) spqrSendCalleeStack ∗
      memRegion (s0.sp - 0x1f80#64) 0x60 ∗
      ProtoRepr.optChainPBAt A ((s0.sp - 0x1f80#64) + 0x60#64) optCh ∗
      memRegion ((s0.sp - 0x1f80#64) + 0xb0#64) (0x1f20 - 0xb0) ∗
      spqrSendSavedRegs (s0.sp - 0x1f80#64) s0 ∗
      A.pool ∗ Rest)
    (Q := fun sm => sm.sp = s0.sp - 0x1f80#64 ∧ sm.trace = s.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    ?_ ?_
  · dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
    generalize hfsp_eq : s0.sp - 8064#64 = fsp at hsp hfsp_align ⊢
    wp_steps
    wp_conv_pre => rw [stackAt_spqrSendCallee_split_allocHook fsp]
    wp_call hdealloc_raw (w1, w0.toNat, 1)
    wp_steps
    refine EncoderFromPb.align_pre ?_ ?_
    · rw [hsp, stackAt_spqrSendCallee_split_allocHook fsp]
      have h60 := memRegion_rejoin_30_8_8_32 fsp w1
      refine Entails.trans
        (Entails.of_eq (show _ =
          (memRegion fsp 48 ∗
           memRegion (fsp + 48#64) 8 ∗
           ((fsp + 56#64) ↦₆₄ w1) ∗
           memRegion (fsp + 64#64) 32) ∗
          (memRegion (fsp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
           stackAt fsp allocHookStack ∗
           ProtoRepr.optChainPBAt A (fsp + 96#64) optCh ∗
           memRegion (fsp + 176#64) 7792 ∗
           spqrSendSavedRegs fsp s0 ∗
           A.pool ∗ Rest) by ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left h60) ?_
      exact Entails.of_eq (by ac_rfl)
    · wp_done
  · intro s2 hpc2 hrun2 hcrl2 ⟨hsp2, htr2, hvregs2⟩
    have hep := spqr_send_chain_drop_epilogue_4608_placed hdrop s0 s2 optCh Rest hcrl2 hsp0_align hpc2 hrun2 hsp2
    refine SepWP.mono hep ?_
    intro sf Pf _ _ ⟨hPf, hsp_f, hcc_f, htr_f⟩
    refine ⟨hPf, hsp_f, hcc_f, htr_f.trans htr2⟩

end CryptoVerification.Cli.SpqrV1.Top.Send
