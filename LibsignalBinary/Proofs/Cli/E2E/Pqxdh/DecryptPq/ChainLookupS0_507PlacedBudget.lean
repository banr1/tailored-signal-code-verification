/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux
public import LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
import ProofLib.RegChain

/-!
# Budget-Threaded Relocatable Segment `S0` on Block `507`

`VmPreserved`-recording `reaches_pc` step lemmas and budget-threaded `S0PSeamPlaced` contracts
(`cliTryDecryptSpecPPlaced` to `LoadRatchetStatePlaced` with zero allocations) for Segment `S0` of
`try_decrypt_with_state::<signal_session_handshake::Coins>` under `DistinctSid`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudget

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto IdentityKey PublicKey)
open CryptoVerification (
  LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
  blkPC_252 blkPl_252 lsBlackBoxU8Sym ls_subroutine_ok_of_block lsmpl withLsCodeLoaded
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8At)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalSessionRepr (chainAt msgTypeByte vecGhostAt)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser optSenderChainAt optTailVecAt protocolAddressAt sessionStateAt
  signalMessageAt uuidTryParse
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TryDecryptGhost logOff rootStack uuidTryParseCodeSpec uuidTryParseSpec
  withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  localIdentityKeyStack localIdentityOkAt remoteIdentityKeyStack remoteIdentityOkAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  segLoadRatchetPC_at tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  exists_localGroupA_of_length_32 exists_remoteGroupC_of_length_32
  exists_remoteGroupC_of_memRegion_32 exists_word64_of_memRegion_8
  identityKeys_prologue_extract identityKeys_step2_extract identityKeys_step2_recombine
  identityKeys_step4_extract identityKeys_step4_to_memRegion_1352
  identityKeys_step5_some_extract identityKeys_step5_some_recombine
  localGroupA localGroupA_eq_localGroupB logOff_tryDecryptDummyImg
  reaches_pc_lscl reaches_pc_lsro_preserve reaches_pc_seq_lscl
  remoteGroupC remoteGroupC_eq_remoteGroupD remoteGroupD sepWP_to_reaches_pc
  stackAt_tryDecryptSubStack_sub tryDecryptDummyImg words4At words8At
)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid isSameAccountDistinctStack)
open CryptoVerification.Cli.CoinsTape (cliTapeAt cliTapeAt_entails_cliTapeAfter_zero)
open CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt (cliTryDecryptCommonHeapPlaced)
open CryptoVerification.CliHandshake.TryDecPlaced (
  blkPC_508 blkPl_508 instIsLsBlockProg_508
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Getters.DefsBudget (remoteIdentityKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (
  local_identity_key_placed_ok remote_identity_key_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.VerifyMacBudgetAux (
  protocolAddressAt_atState
)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountBudget (
  isSameAccountDistinctSpec
)
open LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccountPlacedBudget (
  isSameAccountEqDistinct_placed_ok_at isSameAccountEqDistinct_placed_ok_of_contract
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget (
  LoadRatchetStatePlaced S0PSeamPlaced cliTryDecryptSpecPPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.TightPTrapPlacedBudget (
  tryDecryptPlacedSpecP
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudgetAux (
  identityKeys_507_call_remote_ik_wp_placed identityKeys_507_copy_local_ik_wp_placed
  identityKeys_507_prologue_wp_placed identityKeys_507_remote_ik_common_wp_placed
  identityKeys_507_remote_none_wp_placed identityKeys_507_remote_some_wp_distinct_placed
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

/-! ## `A.atState` Normalization for `isSameAccountDistinctSpec` -/

theorem isSameAccountDistinctSpec_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (parse : UuidParser) :
    isSameAccountDistinctSpec (A.atState lim st s) parse =
      isSameAccountDistinctSpec A.repAlloc parse := by
  simp only [isSameAccountDistinctSpec,
    CryptoVerification.E2E.Pqxdh.WireEntries.isSameAccountDistinctSpec,
    protocolAddressAt_atState]

/-! ## `VmPreserved` Step Lemmas on Block `507` -/

theorem identityKeys_507_step1_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 : State)
    (hcl : LibsignalCodeLoaded lsmpl s0.mem) (h_pc : s0.pc = (blkPl_508).base)
    (h_run : s0.status = .Running) (h_sp_align : s0.spAligned = true)
    (hx0 : s0.readReg64 .x0 = x.ret) (hx1 : s0.readReg64 .x1 = x.ss)
    (hx2 : s0.readReg64 .x2 = x.remA) (hx3 : s0.readReg64 .x3 = x.locA)
    (hx4 : s0.readReg64 .x4 = x.msgA) (hx5 : (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType)
    (hdeser_loc : PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey)
    (hm : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 84#64) s0
      (fun s1 => VmPreserved s0 s1 ∧ s1.sp = sp ∧ s1.spAligned = true ∧
        (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) ∧
        s1.readReg64 .x19 = x.ret ∧ s1.readReg64 .x20 = sp + 320#64 ∧
        s1.readReg64 .x21 = x.ss ∧ s1.readReg64 .x22 = x.msgA ∧
        s1.readReg64 .x23 = sp + 1280#64 ∧ (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s1.readReg64 .x25 = x.locA ∧ s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.mem ⊨ localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗
          memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
          vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗ memRegion sp 48 ∗
          ((sp + 48#64) ↦₆₄ x.remA) ∗ stackAt sp tryDecryptSubStack ∗
          tryDecryptSavedRegs s0.sp s0 ∗ F)) := by
  have _ := instIsLsBlockProg_508 H
  dsimp only; let sp := s0.sp - 1504#64
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, w_sp0, w_sp48, hm1⟩ :=
    identityKeys_prologue_extract hm
  have hm_pre : s0.mem ⊨
      (words4At (s0.sp - 96#64) r0 r1 r2 r3 ∗ words8At (s0.sp - 64#64) r4 r5 r6 r7 r8 r9 r10 r11 ∗
       (sp ↦₆₄ w_sp0) ∗ ((sp + 48#64) ↦₆₄ w_sp48) ∗ vecGhostAt A x.G.localIk x.ss ∗
       memRegion (sp + 400#64) 33 ∗ logOff tryDecryptDummyImg ∗ stackAt sp localIdentityKeyStack) ∗
      (memRegion (sp + 8#64) 40 ∗ memRegion (sp + 56#64) 344 ∗ memRegion (sp + 433#64) 975 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack) ∗ F) := by
    dsimp only [sp] at hm1 ⊢; convert hm1 using 1; sep_ac_rfl
  have hlocal := ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H)
    (local_identity_key_placed_ok A H)
  have hwp := identityKeys_507_prologue_wp_placed hlocal x s0 hcl
    r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 w_sp0 w_sp48
    h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s1 _ _ ⟨P_f, hm_s1, hvm1, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, hPf⟩
  refine ⟨hvm1, hsp, halign, htr, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx29, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s1
  have h48 : (sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40 ⊢ memRegion sp 48 := by
    refine Entails.trans (sepConj_mono_left (pointsTo64_entails_memRegion sp 0#64)) ?_
    rw [← memRegion_split sp 8 40 (by decide)]; exact Entails.refl _
  have hm3 : s1.mem ⊨
      ((sp ↦₆₄ 0#64) ∗ memRegion (sp + 8#64) 40) ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗
       memRegion (sp + 433#64) 975 ∗ vecGhostAt A x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
       ((sp + 48#64) ↦₆₄ x.remA) ∗
       (stackAt sp localIdentityKeyStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - localIdentityKeyStack)) ∗
       tryDecryptSavedRegs s0.sp s0 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp localIdentityKeyStack (by decide)] at hm3
  have hm4 := Satisfies.mono (sepConj_mono_left h48) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_507_step2_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s1 : State)
    (h_pc : s1.pc = (blkPl_508).base + 84#64) (h_run : s1.status = .Running)
    (h_sp : s1.sp = s0.sp - 1504#64) (h_sp_align : s1.spAligned = true)
    (htr : s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0)
    (hx19 : s1.readReg64 .x19 = x.ret) (hx20 : s1.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s1.readReg64 .x21 = x.ss) (hx22 : s1.readReg64 .x22 = x.msgA)
    (hx23 : s1.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s1.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s1.readReg64 .x25 = x.locA) (hx29 : s1.readReg64 .x29 = s0.sp - 96#64)
    (hm : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 156#64) s1
      (fun s2 => VmPreserved s1 s2 ∧ s2.sp = sp ∧ s2.spAligned = true ∧
        (s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0) ∧
        s2.readReg64 .x0 = x.ss ∧ s2.readReg64 .x8 = sp + 400#64 ∧
        s2.readReg64 .x19 = x.ret ∧ s2.readReg64 .x20 = sp + 320#64 ∧
        s2.readReg64 .x21 = x.ss ∧ s2.readReg64 .x22 = x.msgA ∧
        s2.readReg64 .x23 = sp + 1280#64 ∧ (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s2.readReg64 .x25 = x.locA ∧ s2.readReg64 .x29 = s0.sp - 96#64 ∧
        (s2.mem ⊨ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 344 ∗
          memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
          memRegion (sp + 1312#64) 96 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hx29' : s1.readReg64 .x29 = sp + 1408#64 := by rw [hx29]; dsimp only [sp]; bv_omega
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, w0, w1, w2, b31, hloc_eq⟩ :=
    exists_localGroupA_of_length_32 (List.Vector.toList_length x.st.localIdentity.publicKey.bytes)
  have hm_433 : s1.mem ⊨ memRegion (sp + 433#64) 975 ∗
      (localIdentityOkAt (sp + 400#64) x.st.localIdentity ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, dw0, dw1, dw2, db31, u1104, u1112, hm_ext⟩ :=
    identityKeys_step2_extract hm_433
  unfold localIdentityOkAt at hm_ext
  rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, hloc_eq (sp + 401#64)] at hm_ext
  have hm_pre : s1.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ localGroupA (sp + 401#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 ∗
       localGroupA (sp + 1280#64) d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 ∗
       ((sp + 1104#64) ↦₆₄ u1104) ∗ ((sp + 1112#64) ↦₈ u1112)) ∗
      (memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       memRegion (sp + 1113#64) 167 ∗ memRegion (sp + 1312#64) 96 ∗ memRegion (sp + 56#64) 344 ∗ F) := by
    dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hwp := identityKeys_507_copy_local_ik_wp_placed (H := H) x s0 s1
    b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 b31 d0 d1 d2 d3 d4 d5 d6 dw0 dw1 dw2 db31 u1104 u1112
    h_pc h_run h_sp h_sp_align hx20 hx21 hx23 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s2 _ _ ⟨P_f, hm_s2, hvm2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hPf⟩
  refine ⟨hvm2, hsp2, halign2, by reg_chain, hx0_2, hx8_2, by reg_chain, hx20_2, hx21_2,
    by reg_chain, hx23_2, by reg_chain, by reg_chain, by rw [hx29_2]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s2
  rw [← localGroupA_eq_localGroupB, ← localGroupA_eq_localGroupB,
      ← hloc_eq (sp + 401#64), ← hloc_eq (sp + 1280#64)] at hm2
  have hm3 : s2.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 433#64) 1 ∗ memRegion (sp + 434#64) 670 ∗
       ((sp + 1104#64) ↦₆₄ w2) ∗ ((sp + 1112#64) ↦₈ b31) ∗ memRegion (sp + 1113#64) 167) ∗
      (memRegion (sp + 56#64) 344 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  have hm4 := Satisfies.mono (sepConj_mono_left (identityKeys_step2_recombine sp x.st.localIdentity w2 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_507_step3_reaches_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hrem : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 29)
      (withLsCodeLoaded lsmpl (remoteIdentityKeyPlacedSpec A)))
    (x : TryDecryptGhost) (F : SepProp) (s0 s2 : State)
    (hcl : LibsignalCodeLoaded lsmpl s2.mem)
    (h_pc : s2.pc = (blkPl_508).base + 156#64) (h_run : s2.status = .Running)
    (h_sp : s2.sp = s0.sp - 1504#64) (h_sp_align : s2.spAligned = true)
    (htr : s2.trace = s0.trace ∧ calleeSavedVRegs s2 = calleeSavedVRegs s0)
    (hx0 : s2.readReg64 .x0 = x.ss) (hx8 : s2.readReg64 .x8 = (s0.sp - 1504#64) + 400#64)
    (hx19 : s2.readReg64 .x19 = x.ret) (hx20 : s2.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s2.readReg64 .x21 = x.ss) (hx22 : s2.readReg64 .x22 = x.msgA)
    (hx23 : s2.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s2.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s2.readReg64 .x25 = x.locA) (hx29 : s2.readReg64 .x29 = s0.sp - 96#64)
    (hdeser_rem :
      match x.st.remoteIdentity with
      | none => x.G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey)
    (hm : s2.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 24#64) ∗
      memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 160#64) s2
      (fun s3 => VmPreserved s2 s3 ∧ s3.sp = sp ∧ s3.spAligned = true ∧
        (s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0) ∧
        s3.readReg64 .x19 = x.ret ∧ s3.readReg64 .x20 = sp + 320#64 ∧
        s3.readReg64 .x21 = x.ss ∧ s3.readReg64 .x22 = x.msgA ∧
        s3.readReg64 .x23 = sp + 1280#64 ∧ (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s3.readReg64 .x25 = x.locA ∧ s3.readReg64 .x29 = s0.sp - 96#64 ∧
        (s3.mem ⊨ vecGhostAt A x.G.remoteIk (x.ss + 24#64) ∗
          remoteIdentityOkAt (sp + 400#64) x.st.remoteIdentity ∗
          logOff tryDecryptDummyImg ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)] at hm
  have hm_pre : s2.mem ⊨
      (vecGhostAt A x.G.remoteIk (x.ss + 24#64) ∗ memRegion (s2.sp + 400#64) 34 ∗
       logOff tryDecryptDummyImg ∗ stackAt s2.sp remoteIdentityKeyStack) ∗
      (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - remoteIdentityKeyStack) ∗ F) := by
    rw [h_sp]; convert hm using 1; sep_ac_rfl
  have hx8' : s2.readReg64 .x8 = s2.sp + 400#64 := by rw [h_sp]; exact hx8
  have hwp := identityKeys_507_call_remote_ik_wp_placed hrem x s2 hcl h_pc h_run h_sp_align hx0 hx8' hdeser_rem
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s3 _ _ ⟨P_f, hm_s3, hvm3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hPf⟩
  refine ⟨hvm3, by reg_chain, halign3, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s3; rw [h_sp] at hm2
  rw [stackAt_tryDecryptSubStack_sub s0.sp remoteIdentityKeyStack (by decide)]
  convert hm2 using 1; sep_ac_rfl

theorem identityKeys_507_step4_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (tag : BitVec 8) (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s3.pc = (blkPl_508).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hent_402 : remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
      memRegion ((s0.sp - 1504#64) + 402#64) 32)
    (hm : s3.mem ⊨ ((s0.sp - 1504#64 + 400#64) ↦₈ 0#8) ∗ ((s0.sp - 1504#64 + 401#64) ↦₈ tag) ∗
      remoteGroupC ((s0.sp - 1504#64) + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 384#64) s3
      (fun s4 => VmPreserved s3 s4 ∧ s4.sp = sp ∧ s4.spAligned = true ∧
        (s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0) ∧
        s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13 ∧
        s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21 ∧
        s4.readReg64 .x10 = BitVec.zeroExtend 64 b22 ∧ s4.readReg64 .x11 = BitVec.zeroExtend 64 tag ∧
        s4.readReg64 .x19 = x.ret ∧ s4.readReg64 .x20 = sp + 320#64 ∧
        s4.readReg64 .x21 = x.ss ∧ s4.readReg64 .x22 = x.msgA ∧
        s4.readReg64 .x23 = sp + 1280#64 ∧ (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
        s4.readReg64 .x25 = x.locA ∧ s4.readReg64 .x29 = s0.sp - 96#64 ∧
        (s4.mem ⊨ memRegion (sp + 400#64) 34 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
          ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
          memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
          memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  have hm_sub : s3.mem ⊨ (memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846) ∗
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u352, u360, u976, u980, u981, hm_ext⟩ := identityKeys_step4_extract hm_sub
  have hm_pre : s3.mem ⊨
      (((s3.sp + 400#64) ↦₈ 0#8) ∗ ((s3.sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (s3.sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
       ((s3.sp + 352#64) ↦₆₄ u352) ∗ ((s3.sp + 360#64) ↦₈ u360) ∗
       ((s3.sp + 976#64) ↦₃₂ u976) ∗ ((s3.sp + 980#64) ↦₈ u980) ∗ ((s3.sp + 981#64) ↦₈ u981)) ∗
      (memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s3.readReg64 .x20 = s3.sp + 320#64 := by rw [h_sp]; exact hx20
  have hwp := identityKeys_507_remote_ik_common_wp_placed (H := H) s3 tag
    w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u352 u360 u976 u980 u981 h_pc h_run h_sp_align hx20'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s4 _ _ ⟨P_f, hm_s4, hvm4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hPf⟩
  refine ⟨hvm4, by reg_chain, halign4, by reg_chain, hx8_4, hx9_4, hx10_4, hx11_4,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s4; rw [h_sp] at hm2
  have h400_34 :
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ⊢
      memRegion (sp + 400#64) 34 := by
    refine Entails.trans (sepConj_mono (pointsTo8_entails_memRegion (sp + 400#64) 0#8)
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 401#64) tag) hent_402)) ?_
    rw [show sp + 402#64 = (sp + 401#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 401#64) 1 32 (by decide),
        show sp + 401#64 = (sp + 400#64) + 1#64 by bv_omega,
        ← memRegion_split (sp + 400#64) 1 33 (by decide)]; exact Entails.refl _
  have hm3 : s4.mem ⊨
      (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ tag) ∗
       remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31) ∗
      (((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 56#64) 296 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  exact Satisfies.mono (sepConj_mono_left h400_34) hm3

theorem identityKeys_507_step5_none_reaches_placed [LibsignalPlacement]
    {H : String → Option (State → State)} (x : TryDecryptGhost) (F : SepProp) (s0 s4 : State)
    (h_pc : s4.pc = (blkPl_508).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx11 : s4.readReg64 .x11 = 0#64) (hx19 : s4.readReg64 .x19 = x.ret)
    (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64) (hx21 : s4.readReg64 .x21 = x.ss)
    (hx22 : s4.readReg64 .x22 = x.msgA) (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hm : s4.mem ⊨ memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 472#64) s4
      (fun s5 => VmPreserved s4 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ memRegion (sp + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [memRegion_split (sp + 56#64) 968 384 (by decide), show sp + 56#64 + 968#64 = sp + 1024#64 by bv_omega,
      memRegion_split (sp + 1024#64) 8 376 (by decide), show sp + 1024#64 + 8#64 = sp + 1032#64 by bv_omega,
      memRegion_split (sp + 1032#64) 8 368 (by decide), show sp + 1032#64 + 8#64 = sp + 1040#64 by bv_omega,
      memRegion_split (sp + 1040#64) 240 128 (by decide), show sp + 1040#64 + 240#64 = sp + 1280#64 by bv_omega,
      memRegion_split (sp + 1280#64) 8 120 (by decide), show sp + 1280#64 + 8#64 = sp + 1288#64 by bv_omega] at hm
  have hm1 : s4.mem ⊨ memRegion (sp + 1024#64) 8 ∗ (memRegion (sp + 1032#64) 8 ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u1024, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : s4.mem ⊨ memRegion (sp + 1032#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ memRegion (sp + 1280#64) 8 ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm1 using 1; sep_ac_rfl
  obtain ⟨u1032, hm2⟩ := exists_word64_of_memRegion_8 hm2
  have hm3 : s4.mem ⊨ memRegion (sp + 1280#64) 8 ∗ (((sp + 1024#64) ↦₆₄ u1024) ∗ ((sp + 1032#64) ↦₆₄ u1032) ∗
       logOff tryDecryptDummyImg ∗ (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F)) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨u1280, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm_pre : s4.mem ⊨
      (((s4.sp + 1024#64) ↦₆₄ u1024) ∗ ((s4.sp + 1032#64) ↦₆₄ u1032) ∗ ((s4.sp + 1280#64) ↦₆₄ u1280) ∗ logOff tryDecryptDummyImg) ∗
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1040#64) 240 ∗ memRegion (sp + 1288#64) 120 ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm3 ⊢; convert hm3 using 1; sep_ac_rfl
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hwp := identityKeys_507_remote_none_wp_placed (H := H) s4 u1024 u1032 u1280 h_pc h_run h_sp_align hx11 hx29'
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hvm5, by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm4 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm4
  have hm5 : s5.mem ⊨
      (memRegion (sp + 56#64) 968 ∗ memRegion (sp + 1024#64) 16 ∗ memRegion (sp + 1040#64) 240 ∗
       memRegion (sp + 1280#64) 8 ∗ memRegion (sp + 1288#64) 120) ∗ (logOff tryDecryptDummyImg ∗ F) := by
    dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
  rw [show sp + 1288#64 = (sp + 1280#64) + 8#64 by bv_omega, ← memRegion_split (sp + 1280#64) 8 120 (by decide),
      show sp + 1280#64 = (sp + 1040#64) + 240#64 by bv_omega, ← memRegion_split (sp + 1040#64) 240 128 (by decide),
      show sp + 1040#64 = (sp + 1024#64) + 16#64 by bv_omega, ← memRegion_split (sp + 1024#64) 16 368 (by decide),
      show sp + 1024#64 = (sp + 56#64) + 968#64 by bv_omega, ← memRegion_split (sp + 56#64) 968 384 (by decide)] at hm5
  exact hm5

theorem identityKeys_507_step5_some_reaches_distinct_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hsame : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)))
    (x : TryDecryptGhost) (remIk : IdentityKey) (F : SepProp) (s0 s4 : State)
    (hcl : LibsignalCodeLoaded lsmpl s4.mem)
    (w0 : BitVec 32) (b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : BitVec 8)
    (w3 : BitVec 64) (b31 : BitVec 8)
    (h_pc : s4.pc = (blkPl_508).base + 384#64) (h_run : s4.status = .Running)
    (h_sp : s4.sp = s0.sp - 1504#64) (h_sp_align : s4.spAligned = true)
    (htr : s4.trace = s0.trace ∧ calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx8 : s4.readReg64 .x8 = pack64 b6 b7 b8 b9 b10 b11 b12 b13)
    (hx9 : s4.readReg64 .x9 = pack64 b14 b15 b16 b17 b18 b19 b20 b21)
    (hx10 : s4.readReg64 .x10 = BitVec.zeroExtend 64 b22) (hx11 : s4.readReg64 .x11 = 1#64)
    (hx19 : s4.readReg64 .x19 = x.ret) (hx20 : s4.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s4.readReg64 .x21 = x.ss) (hx22 : s4.readReg64 .x22 = x.msgA)
    (hx23 : s4.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s4.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s4.readReg64 .x25 = x.locA) (hx29 : s4.readReg64 .x29 = s0.sp - 96#64)
    (hrem_eq : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
      remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    (hdiff : x.st.localIdentity ≠ remIk ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s4.mem ⊨ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗ memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗
      ((s0.sp - 1504#64 + 352#64) ↦₆₄ w3) ∗ ((s0.sp - 1504#64 + 360#64) ↦₈ b31) ∗
      ((s0.sp - 1504#64 + 976#64) ↦₃₂ w0) ∗ ((s0.sp - 1504#64 + 980#64) ↦₈ b4) ∗
      ((s0.sp - 1504#64 + 981#64) ↦₈ b5) ∗ memRegion ((s0.sp - 1504#64) + 56#64) 296 ∗
      memRegion ((s0.sp - 1504#64) + 361#64) 39 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 542 ∗
      memRegion ((s0.sp - 1504#64) + 982#64) 298 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗
      protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
      stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 472#64) s4
      (fun s5 => VmPreserved s4 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
          protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
          stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rw [stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStack (by decide)] at hm
  have hm_sub : s4.mem ⊨ (memRegion (sp + 400#64) 34 ∗ memRegion (sp + 56#64) 296) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
       ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
       memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       memRegion (sp + 1312#64) 96 ∗ protocolAddressAt A x.loc x.locA ∗
       protocolAddressAt A x.rem x.remA ∗ stackAt sp isSameAccountDistinctStack ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack) ∗ F) := by
    dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
  obtain ⟨u400, u408, dw0, db4, db5, db6, db7, db8, db9, db10, db11, db12, db13, db14, db15, db16,
    db17, db18, db19, db20, db21, db22, dw3, db31, hm_ext⟩ :=
    identityKeys_step5_some_extract hm_sub
  have hm_pre : s4.mem ⊨
      (((s4.sp + 48#64) ↦₆₄ x.remA) ∗ ((s4.sp + 400#64) ↦₆₄ u400) ∗ ((s4.sp + 408#64) ↦₈ u408) ∗
       ((s4.sp + 352#64) ↦₆₄ w3) ∗ ((s4.sp + 360#64) ↦₈ b31) ∗ ((s4.sp + 976#64) ↦₃₂ w0) ∗
       ((s4.sp + 980#64) ↦₈ b4) ∗ ((s4.sp + 981#64) ↦₈ b5) ∗
       remoteGroupD (s4.sp + 56#64) dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16
         db17 db18 db19 db20 db21 db22 dw3 db31 ∗
       ((s4.sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
       protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
       stackAt s4.sp isSameAccountDistinctStack) ∗
      (memRegion (sp + 409#64) 25 ∗ memRegion (sp + 88#64) 264 ∗ memRegion (sp + 361#64) 39 ∗
       memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗ memRegion (sp + 1312#64) 96 ∗
       memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack) ∗ F) := by
    rw [h_sp]; dsimp only [sp] at hm_ext ⊢; convert hm_ext using 1; sep_ac_rfl
  have hx20' : s4.readReg64 .x20 = s4.sp + 320#64 := by rw [h_sp]; exact hx20
  have hx29' : s4.readReg64 .x29 = s4.sp + 1408#64 := by rw [hx29, h_sp]; bv_omega
  have hwp := identityKeys_507_remote_some_wp_distinct_placed hsame x remIk s4 hcl
    w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
    w3 b31 u400 u408 dw0 db4 db5 db6 db7 db8 db9 db10 db11 db12 db13 db14 db15 db16 db17 db18 db19
    db20 db21 db22 dw3 db31
    h_pc h_run h_sp_align hx8 hx9 hx10 hx11 hx20' hx25 hx29' hrem_eq hdiff
  refine reaches_pc_mono (sepWP_to_reaches_pc hwp hm_pre) ?_
  intro s5 _ _ ⟨P_f, hm_s5, hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hPf⟩
  refine ⟨hvm5, by reg_chain, halign5, by reg_chain, hx1_5, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, hx25_5, by rw [hx29_5, h_sp]; bv_omega, ?_⟩
  have hm2 := Satisfies.mono (sepConj_mono_left hPf) hm_s5; rw [h_sp] at hm2
  have hm3 : s5.mem ⊨
      (((sp + 56#64) ↦ₛ remIk.publicKey.bytes.toList) ∗ memRegion (sp + 88#64) 264 ∗
       ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ memRegion (sp + 361#64) 39 ∗
       ((sp + 400#64) ↦₈ b6) ∗ ((sp + 401#64) ↦₆₄ pack64 b7 b8 b9 b10 b11 b12 b13 b14) ∗
       memRegion (sp + 409#64) 25 ∗ memRegion (sp + 434#64) 542 ∗ ((sp + 976#64) ↦₃₂ w0) ∗
       ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 982#64) 298 ∗
       ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗ memRegion (sp + 1312#64) 96) ∗
      (((sp + 48#64) ↦₆₄ x.remA) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
       (stackAt sp isSameAccountDistinctStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - isSameAccountDistinctStack)) ∗ F) := by
    dsimp only [sp] at hm2 ⊢; convert hm2 using 1; sep_ac_rfl
  rw [← stackAt_tryDecryptSubStack_sub s0.sp isSameAccountDistinctStack (by decide)] at hm3
  have hm4 := Satisfies.mono
    (sepConj_mono_left (identityKeys_step5_some_recombine sp x.st.localIdentity remIk w0 b4 b5 b6
      (pack64 b7 b8 b9 b10 b11 b12 b13 b14) w3 b31)) hm3
  dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl

theorem identityKeys_507_step45_reaches_distinct_placed [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hsameDist : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A uuidTryParse)))
    (x : TryDecryptGhost) (F : SepProp) (s0 s3 : State)
    (hcl : LibsignalCodeLoaded lsmpl s3.mem)
    (h_pc : s3.pc = (blkPl_508).base + 160#64) (h_run : s3.status = .Running)
    (h_sp : s3.sp = s0.sp - 1504#64) (h_sp_align : s3.spAligned = true)
    (htr : s3.trace = s0.trace ∧ calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hx19 : s3.readReg64 .x19 = x.ret) (hx20 : s3.readReg64 .x20 = (s0.sp - 1504#64) + 320#64)
    (hx21 : s3.readReg64 .x21 = x.ss) (hx22 : s3.readReg64 .x22 = x.msgA)
    (hx23 : s3.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64)
    (hx24 : (s3.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s3.readReg64 .x25 = x.locA) (hx29 : s3.readReg64 .x29 = s0.sp - 96#64)
    (hnot_self : x.st.remoteIdentity ≠ some x.st.localIdentity ∨
      DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes)
    (hm : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
      memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
      ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
      memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
      logOff tryDecryptDummyImg ∗ protocolAddressAt A x.loc x.locA ∗
      protocolAddressAt A x.rem x.remA ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ F) :
    let sp := s0.sp - 1504#64
    reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 472#64) s3
      (fun s5 => VmPreserved s3 s5 ∧ s5.sp = sp ∧ s5.spAligned = true ∧
        (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
        (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
        s5.readReg64 .x20 = sp + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
        s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = sp + 1280#64 ∧
        (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
        s5.readReg64 .x29 = s0.sp - 96#64 ∧
        (s5.mem ⊨ ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 56#64) 1352 ∗
          logOff tryDecryptDummyImg ∗ protocolAddressAt A x.loc x.locA ∗
          protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
  dsimp only; let sp := s0.sp - 1504#64
  rcases hrem_opt : x.st.remoteIdentity with _ | remIk
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    have hm_402 : s3.mem ⊨ memRegion (sp + 402#64) 32 ∗
        (((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗ memRegion (sp + 56#64) 344 ∗
         memRegion (sp + 434#64) 846 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗
         protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hent_402, hm_402⟩ :=
      exists_remoteGroupC_of_memRegion_32 hm_402
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 0#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗
         protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F) := by
      dsimp only [sp] at hm_402 ⊢; convert hm_402 using 1; sep_ac_rfl
    refine reaches_pc_seq
      (identityKeys_507_step4_reaches_placed (H := H) x _ s0 s3 0#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 (hent_402 (sp + 402#64)) hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hvm4, hsp4, halign4, htr4, _, _, _, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩
    have hm4_re : s4.mem ⊨
        (memRegion (sp + 56#64) 296 ∗ ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗
         memRegion (sp + 361#64) 39 ∗ memRegion (sp + 400#64) 34 ∗ memRegion (sp + 434#64) 542 ∗
         ((sp + 976#64) ↦₃₂ w0) ∗ ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗
         memRegion (sp + 982#64) 298 ∗ ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96) ∗
        (logOff tryDecryptDummyImg ∗ (((sp + 48#64) ↦₆₄ x.remA) ∗
         protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F)) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    have hm4_1352 := Satisfies.mono (sepConj_mono_left (identityKeys_step4_to_memRegion_1352 sp x.st.localIdentity w0 b4 b5 w3 b31)) hm4_re
    refine reaches_pc_mono
      (identityKeys_507_step5_none_reaches_placed (H := H) x
        (((sp + 48#64) ↦₆₄ x.remA) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ stackAt sp tryDecryptSubStack ∗ F)
        s0 s4 hpc4 hrun4 hsp4 halign4 htr4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4 hm4_1352) ?_
    intro s5 _ _ ⟨hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hvm4.trans hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    dsimp only [sp] at hm5; convert hm5 using 1; sep_ac_rfl
  · rw [hrem_opt] at hm; dsimp only [remoteIdentityOkAt] at hm
    rw [show sp + 400#64 + 1#64 = sp + 401#64 by bv_omega, show sp + 400#64 + 2#64 = sp + 402#64 by bv_omega] at hm
    obtain ⟨w0, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, w3, b31, hrem_c⟩ :=
      exists_remoteGroupC_of_length_32 (List.Vector.toList_length remIk.publicKey.bytes)
    have hent_402 : remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ⊢
        memRegion (sp + 402#64) 32 := by
      rw [← hrem_c (sp + 402#64)]
      have hlen : remIk.publicKey.bytes.toList.length = 32 := List.Vector.toList_length _
      have h := pointsToBytes_entails_memRegion (sp + 402#64) remIk.publicKey.bytes.toList; rwa [hlen] at h
    rw [hrem_c (sp + 402#64)] at hm
    have hm_s4 : s3.mem ⊨
        ((sp + 400#64) ↦₈ 0#8) ∗ ((sp + 401#64) ↦₈ 1#8) ∗
        remoteGroupC (sp + 402#64) w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 ∗
        memRegion (sp + 56#64) 344 ∗ memRegion (sp + 434#64) 846 ∗
        (((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion (sp + 1312#64) 96 ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗ logOff tryDecryptDummyImg ∗
         stackAt sp tryDecryptSubStack ∗ (protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗ F)) := by
      dsimp only [sp] at hm ⊢; convert hm using 1; sep_ac_rfl
    refine reaches_pc_seq_lscl hcl
      (identityKeys_507_step4_reaches_placed (H := H) x _ s0 s3 1#8 w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22
        w3 b31 h_pc h_run h_sp h_sp_align htr hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx29 hent_402 hm_s4) ?_
    intro s4 hpc4 hrun4 ⟨hvm4, hsp4, halign4, htr4, hx8_4, hx9_4, hx10_4, hx11_4, hx19_4, hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx29_4, hm4⟩ hcl4
    have hrem_d : ∀ a : BitVec 64, (a ↦ₛ remIk.publicKey.bytes.toList) =
        remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31 :=
      fun a => (hrem_c a).trans (remoteGroupC_eq_remoteGroupD a w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31)
    have hdiff : x.st.localIdentity ≠ remIk ∨ DistinctSid uuidTryParse x.loc.name.bytes x.rem.name.bytes := by
      rcases hnot_self with hne | hdist
      · left; intro heq; apply hne; rw [hrem_opt, heq]
      · exact Or.inr hdist
    have hm4_re : s4.mem ⊨
        ((sp + 48#64) ↦₆₄ x.remA) ∗ memRegion (sp + 400#64) 34 ∗
        ((sp + 352#64) ↦₆₄ w3) ∗ ((sp + 360#64) ↦₈ b31) ∗ ((sp + 976#64) ↦₃₂ w0) ∗
        ((sp + 980#64) ↦₈ b4) ∗ ((sp + 981#64) ↦₈ b5) ∗ memRegion (sp + 56#64) 296 ∗
        memRegion (sp + 361#64) 39 ∗ memRegion (sp + 434#64) 542 ∗ memRegion (sp + 982#64) 298 ∗
        ((sp + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion (sp + 1312#64) 96 ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        stackAt sp tryDecryptSubStack ∗ (logOff tryDecryptDummyImg ∗ F) := by
      dsimp only [sp] at hm4 ⊢; convert hm4 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (identityKeys_507_step5_some_reaches_distinct_placed hsameDist x remIk (logOff tryDecryptDummyImg ∗ F) s0 s4 hcl4
        w0 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 w3 b31
        hpc4 hrun4 hsp4 halign4 htr4 hx8_4 hx9_4 hx10_4 hx11_4 hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx29_4
        hrem_d hdiff hm4_re) ?_
    intro s5 _ _ ⟨hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩
    refine ⟨hvm4.trans hvm5, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, ?_⟩
    convert hm5 using 1; sep_ac_rfl

/-! ## Budget-Threaded `S0PSeamPlaced` Contracts -/

/-- Budget-threaded Segment `S0` seam (`S0PSeamPlaced`) on Block `507` given `hsameDist`
at `A.repAlloc`. -/
theorem s0_507_placed_ok_P [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hsameDist : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A.repAlloc uuidTryParse))) :
    S0PSeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base
      C A lim ctl uuidTryParse S tdEnv := by
  have _ := instIsLsBlockProg_508 H
  intro x st_init R s0 h_pc h_run h_sp_align hpre
  dsimp only [cliTryDecryptSpecPPlaced, withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hcl0, hro0⟩, hpre⟩
  dsimp only [tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_hfits, hpre⟩
  let A0 : RustAlloc := A.atState lim st_init s0
  change s0.mem ⊨
    (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP
      C A0 ctl uuidTryParse S).pre x s0 ∗ R at hpre
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptPlacedSpecP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hx4, hx5, hnot_self, _, _, _⟩, hm0⟩
  have hlog_dummy : lsLogOff = logOff tryDecryptDummyImg := by
    rw [lsLogOff, logOff_tryDecryptDummyImg]
  rw [hlog_dummy] at hm0
  unfold sessionStateAt at hm0; rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm0
  rcases hm0 with ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, hm0⟩
  have hsame0 : subroutine_ok ((blkPC_508).rebase (blkPl_508).base H) (lsmpl.base 17)
      (withLsCodeLoaded lsmpl (isSameAccountDistinctSpec A0 uuidTryParse)) := by
    simpa only [A0, isSameAccountDistinctSpec_atState] using hsameDist
  have hm_s1 : s0.mem ⊨ stackAt s0.sp rootStack ∗ vecGhostAt A0 x.G.localIk x.ss ∗ logOff tryDecryptDummyImg ∗
      (vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗
       vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
       ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
       signalMessageAt A0 x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ A0.pool ∗ R) := by
    convert hm0 using 1; sep_ac_rfl
  have hseg : segLoadRatchetPC_at (blkPl_508).base = (blkPl_508).base + 472#64 := rfl
  rw [hseg]
  have hmain : reaches_pc ((blkPC_508).rebase (blkPl_508).base H) ((blkPl_508).base + 472#64) s0
      (fun s5 =>
        (VmPreserved s0 s5 ∧ s5.sp = s0.sp - 1504#64 ∧ s5.spAligned = true ∧
          (s5.trace = s0.trace ∧ calleeSavedVRegs s5 = calleeSavedVRegs s0) ∧
          (s5.readReg64 .x1).setWidth 32 = 0#32 ∧ s5.readReg64 .x19 = x.ret ∧
          s5.readReg64 .x20 = (s0.sp - 1504#64) + 320#64 ∧ s5.readReg64 .x21 = x.ss ∧
          s5.readReg64 .x22 = x.msgA ∧ s5.readReg64 .x23 = (s0.sp - 1504#64) + 1280#64 ∧
          (s5.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧ s5.readReg64 .x25 = x.locA ∧
          s5.readReg64 .x29 = s0.sp - 96#64 ∧
          (s5.mem ⊨ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
            memRegion ((s0.sp - 1504#64) + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗
            protocolAddressAt A0 x.loc x.locA ∗ protocolAddressAt A0 x.rem x.remA ∗
            stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
            (vecGhostAt A0 x.G.localIk x.ss ∗ vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗
             memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
             vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
             vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
             vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
             optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
             optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
             ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
             ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
             signalMessageAt A0 x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ A0.pool ∗ R))) ∧
        LibsignalCodeLoaded lsmpl s5.mem) := by
    refine reaches_pc_seq_lscl hcl0
      (identityKeys_507_step1_reaches_placed (H := H) x _ s0 hcl0 h_pc h_run h_sp_align hx0 hx1 hx2 hx3 hx4 hx5 hdeser_loc hm_s1) ?_
    intro s1 hpc1 hrun1 ⟨hvm1, hsp1, halign1, htr1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx29_1, hm1⟩ hcl1
    have hm_s2 : s1.mem ⊨ localIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.localIdentity ∗
        memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 433#64) 975 ∗
        (vecGhostAt A0 x.G.localIk x.ss ∗ vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗
         memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
         stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗
         (vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
          optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
          ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
          ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ logOff tryDecryptDummyImg ∗ memRegion x.ret 48 ∗
          protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
          signalMessageAt A0 x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ A0.pool ∗ R)) := by
      convert hm1 using 1; sep_ac_rfl
    refine reaches_pc_seq_lscl hcl1
      (identityKeys_507_step2_reaches_placed (H := H) x _ s0 s1 hpc1 hrun1 hsp1 halign1 htr1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 hm_s2) ?_
    intro s2 hpc2 hrun2 ⟨hvm2, hsp2, halign2, htr2, hx0_2, hx8_2, hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx29_2, hm2⟩ hcl2
    have hm_s3 : s2.mem ⊨ vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗
        memRegion ((s0.sp - 1504#64) + 400#64) 34 ∗ logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        (memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
         ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
         memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ vecGhostAt A0 x.G.localIk x.ss ∗
         memRegion (s0.sp - 1504#64) 48 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
         tryDecryptSavedRegs s0.sp s0 ∗
         (vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
          optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
          ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
          ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
          protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
          signalMessageAt A0 x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ A0.pool ∗ R)) := by
      convert hm2 using 1; sep_ac_rfl
    have hrem := ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H)
      (remote_identity_key_placed_ok A0 H)
    refine reaches_pc_seq_lscl hcl2
      (identityKeys_507_step3_reaches_placed hrem x _ s0 s2 hcl2 hpc2 hrun2 hsp2 halign2 htr2 hx0_2 hx8_2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx29_2 hdeser_rem hm_s3) ?_
    intro s3 hpc3 hrun3 ⟨hvm3, hsp3, halign3, htr3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx29_3, hm3⟩ hcl3
    have hm_s45 : s3.mem ⊨ remoteIdentityOkAt ((s0.sp - 1504#64) + 400#64) x.st.remoteIdentity ∗
        memRegion ((s0.sp - 1504#64) + 56#64) 344 ∗ memRegion ((s0.sp - 1504#64) + 434#64) 846 ∗
        ((s0.sp - 1504#64 + 1280#64) ↦ₛ x.st.localIdentity.publicKey.bytes.toList) ∗
        memRegion ((s0.sp - 1504#64) + 1312#64) 96 ∗ ((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
        logOff tryDecryptDummyImg ∗ protocolAddressAt A0 x.loc x.locA ∗ protocolAddressAt A0 x.rem x.remA ∗
        stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
        (vecGhostAt A0 x.G.localIk x.ss ∗ vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗
         memRegion (s0.sp - 1504#64) 48 ∗ tryDecryptSavedRegs s0.sp s0 ∗
         vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
         vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
         vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
         optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
         optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
         ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
         ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
         signalMessageAt A0 x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ A0.pool ∗ R) := by
      convert hm3 using 1; sep_ac_rfl
    refine reaches_pc_mono
      (reaches_pc_lscl hcl3
        (identityKeys_507_step45_reaches_distinct_placed hsame0 x _ s0 s3 hcl3 hpc3 hrun3 hsp3 halign3 htr3
          hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx29_3 hnot_self hm_s45)) ?_
    intro s5 _ _ ⟨⟨hvm45, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩
    exact ⟨⟨((hvm1.trans hvm2).trans hvm3).trans hvm45,
      hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩
  refine reaches_pc_mono (reaches_pc_lsro_preserve hro0 hmain) ?_
  intro s5 hpc5 hrun5 ⟨⟨⟨hvm, hsp5, halign5, htr5, hx1_5, hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx29_5, hm5⟩, hcl5⟩, hro5⟩
  have hA_eq : A.atState lim st_init s5 = A0 := A.atState_eq_of_vmPreserved lim st_init hvm
  unfold LoadRatchetStatePlaced CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetStatePlaced
  dsimp only
  rw [hA_eq]
  rw [← hseg] at hpc5
  refine ⟨hpc5, ⟨hrun5, hsp5, h_sp_align, halign5, hx29_5, htr5.1, ⟨hcl5, hro5⟩, htr5.2⟩,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx1_5, ?_⟩
  unfold sessionStateAt cliTryDecryptCommonHeapPlaced
  rw [hlog_dummy, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hdeser_loc, hdeser_rem, hss_rest⟩, ?_⟩
  have hm5_tape : s5.mem ⊨
      cliTapeAt ctl x.cur x.rest ∗ (((s0.sp - 1504#64 + 48#64) ↦₆₄ x.remA) ∗
       memRegion (s0.sp - 1504#64 + 56#64) 1352 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ vecGhostAt A0 x.G.localIk x.ss ∗
       vecGhostAt A0 x.G.remoteIk (x.ss + 24#64) ∗ memRegion (s0.sp - 1504#64) 48 ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       vecU8At A0 (x.ss + 48#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
       vecAt A0 104 8 (chainAt A0) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
       vecGhostAt A0 x.G.alice (x.ss + 96#64) ∗ vecU8At A0 (x.ss + 120#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
       optSenderChainAt A0 (x.ss + 144#64) x.G.sender x.st.senderChain ∗
       optTailVecAt A0 48 (x.ss + 248#64) x.G.pending ∗ optTailVecAt A0 32 (x.ss + 296#64) x.G.kyber ∗
       ((x.ss + 328#64) ↦₃₂ x.st.sessionVersion) ∗ ((x.ss + 332#64) ↦₃₂ x.st.previousCounter) ∗
       ((x.ss + 336#64) ↦ₛ x.G.regIds) ∗ memRegion x.ret 48 ∗
       protocolAddressAt A0 x.rem x.remA ∗ protocolAddressAt A0 x.loc x.locA ∗
       signalMessageAt A0 x.msgG x.msgA x.msg ∗ A0.pool ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  have hm5_after := Satisfies.mono
    (sepConj_mono_left (cliTapeAt_entails_cliTapeAfter_zero ctl x.cur x.rest)) hm5_tape
  convert hm5_after using 1; sep_ac_rfl

/-- Specialize `s0_507_placed_ok_P` using `blackBoxHook` and `withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse))` on Block `252`. -/
theorem s0_507_placed_ok_P_of_callees [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : LibsignalHooks}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withLsCodeLoaded lsmpl (withVmPreserved (uuidTryParseCodeSpec uuidTryParse)))) :
    S0PSeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base
      C A lim ctl uuidTryParse S tdEnv := by
  have _ := instIsLsBlockProg_508 H
  exact s0_507_placed_ok_P (isSameAccountEqDistinct_placed_ok_at A.repAlloc h_bb huuid)

/-- Specialize `s0_507_placed_ok_P` using `blackBoxHook` and `withVmPreserved (uuidTryParseSpec uuidTryParse)` on Block `252`. -/
theorem s0_507_placed_ok_P_of_contract [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : LibsignalHooks}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook)
    (huuid : subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
      (withVmPreserved (uuidTryParseSpec uuidTryParse))) :
    S0PSeamPlaced ((blkPC_508).rebase (blkPl_508).base H) (blkPl_508).base
      C A lim ctl uuidTryParse S tdEnv := by
  have _ := instIsLsBlockProg_508 H
  exact s0_507_placed_ok_P
    (ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H)
      (isSameAccountEqDistinct_placed_ok_of_contract A.repAlloc h_bb huuid))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.ChainLookupS0_507PlacedBudget
