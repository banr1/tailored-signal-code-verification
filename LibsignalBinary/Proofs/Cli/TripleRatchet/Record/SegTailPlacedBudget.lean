/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Record.SegTailBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable CLI `SegTail`

Threads `RustCliAllocBudget M` and `SeamBudget` across the `"decryption failed"` error-tail segment
(`+0x850 → +0x1e8c`) on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget

open Arm64 ProofLib
open scoped LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget
open CryptoGames.LibsignalSession (Crypto SessionState)
open CryptoVerification (
  LibsignalPlacement LibsignalCodeLoaded LibsignalRoLoaded
  lsmpl lsro_intro_chk lsLogFilterAddr
  lsRustNoAllocShimSym lsRustAllocSym sepWP_seq_lscl
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  SessionGhost uuidTryParse speWord
  protocolAddressAt signalMessageAt sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel RecordDecryptGhost rootStack
  decryptionFailedStr recordResultAt recordResultTag
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  dropSessionStructureLocal2Stack lsLogOff
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  RecErr errsAt
  decryptionFailedStr_split_shared_lb
  sessionStateExposedAt_shared_lb sessionStateAt_expose_shared_lb
  sessionStateAt_localIk_cap_lt_shared_lb
  recordResultAt_decryptionFailed_intro_shared_lb
)
open CryptoVerification.LibsignalTripleRatchet.Record.SegTailRegReadSimp (
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
)
open CryptoVerification.CliRatchet.DecPlaced (blkPC_463 blkPl_463)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  ls_hook_ok_226
  recFPCPlaced recMetaPlaced recFramePlaced
  decryptionFailedSym
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  VmPreserved AllocCallPreserved FreeOnlyEvs
  FitsEvents FitsEnv SeqEnv RustLayoutOk
  rustAllocEvents subroutine_ok_allocNoOom_of_budget
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  TryDecryptEnvArgs SegTailEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatchBudget (
  sessionStateAt_atState recordResultAt_atState errsAt_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBasePlacedBudget (
  cliRecFramePlaced_atState
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegMismatchPlacedBudget (
  sepWP_cut_here
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (
  FStatePlaced JStatePlaced SegTailPlacedSpec
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre

private theorem cap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  bv_omega

private theorem rodata_decryptionFailed_placed_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ decryptionFailedSym) ↦ᵣ decryptionFailedStr) ∗ P :=
  lsro_intro_chk hro (by rw [decryptionFailedStr_split_shared_lb]; decide +kernel) hP

private theorem pointsToBytesRO_decryptionFailed (a : BitVec 64) :
    (a ↦ᵣ decryptionFailedStr) =
      (a ↦₆₄ᵣ 0x6974707972636564#64) ∗ ((a + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
        ((a + 16#64) ↦₈ᵣ 0x64#8) := by
  rw [decryptionFailedStr_split_shared_lb, pointsToBytesRO_append, pointsToBytesRO_append]
  change (a ↦ᵣ [0x64#8, 0x65#8, 0x63#8, 0x72#8, 0x79#8, 0x70#8, 0x74#8, 0x69#8]) ∗
    (((a + 8#64) ↦ᵣ [0x6f#8, 0x6e#8, 0x20#8, 0x66#8, 0x61#8, 0x69#8, 0x6c#8, 0x65#8]) ∗
     ((a + 8#64 + 8#64) ↦ᵣ [0x64#8])) = _
  rw [pointsToBytesRO8_eq_pointsTo64RO, pointsToBytesRO8_eq_pointsTo64RO,
    pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp]
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  rw [h16]
  rfl

private theorem stackAt_root_split_dropLocal2 (sp : BitVec 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_split_bottom sp dropSessionStructureLocal2Stack
    (rootStack - dropSessionStructureLocal2Stack) (by decide)

private theorem stackAt_dropLocal2_split_alloc (sp : BitVec 64) :
    stackAt sp dropSessionStructureLocal2Stack =
      memRegion (sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack) 96 ∗
        stackAt sp allocHookStack :=
  stackAt_split_bottom sp allocHookStack 96 (by decide)

private theorem memRegion_0x6b0_split (a : BitVec 64) :
    memRegion a 0x6b0 = (∃∗ w : BitVec 64, (a ↦₆₄ w) ∗ memRegion (a + 8#64) 0x6a8) := by
  rw [memRegion_split a 8 0x6a8 (by decide), memRegion_eight, sepExists_sepConj_left]

private theorem memRegion_slot48_split (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ b4 : BitVec 8, ∃∗ w3 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w0 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
        ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₈ b4) ∗ memRegion (a + 33#64) 15) := by
  rw [memRegion_split a 8 40 (by decide),
    memRegion_split (a + 8#64) 8 32 (by decide),
    memRegion_split (a + 8#64 + 8#64) 8 24 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 1 15 (by decide),
    memRegion_eight, memRegion_eight, memRegion_eight, memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_17_split (p : BitVec 64) :
    memRegion p 17 =
      (∃∗ u2 : BitVec 8, ∃∗ u1 : BitVec 64, ∃∗ u0 : BitVec 64,
        (p ↦₆₄ u0) ∗ ((p + 8#64) ↦₆₄ u1) ∗ ((p + 16#64) ↦₈ u2)) := by
  rw [memRegion_split p 8 9 (by decide),
    memRegion_split (p + 8#64) 8 1 (by decide),
    memRegion_eight, memRegion_eight, memRegion_one]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]

private theorem recFramePlaced_expose_rep [LibsignalPlacement] (A : RustAlloc)
    (x : RecordDecryptGhost) (sp : BitVec 64) :
    recFramePlaced A x sp =
      ∃∗ w5f0 : BitVec 64,
        memRegion sp 0x80 ∗
        ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
        memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
        ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
        memRegion (sp + 0x4e0#64) 0xd0 ∗
        ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
        ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗ memRegion (sp + 0x5bd#64) 3 ∗
        ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
        ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
        (((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ memRegion (sp + 0x5f0#64 + 8#64) 0x6a8) ∗
        memRegion (sp + 0xdf8#64) 8 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
          stackAt sp dropSessionStructureLocal2Stack) ∗ A.pool := by
  unfold recFramePlaced lsLogOff
  rw [memRegion_0x6b0_split (sp + 0x5f0#64), stackAt_root_split_dropLocal2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

private def segTailFrame [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (x : RecordDecryptGhost) (sp : BitVec 64) (r_err : RecErr) : SepProp :=
  memRegion sp 0x80 ∗
  ((sp + 0x88#64) ↦₆₄ x.locA) ∗ ((sp + 0x90#64) ↦₆₄ x.msgA) ∗
  memRegion (sp + 0x98#64) 4 ∗ ((sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
  ((sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((sp + 0xf0#64) ↦₆₄ x.locA) ∗
  memRegion (sp + 0x4e0#64) 0xd0 ∗
  ((sp + 0x5b0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x5b8#64) 4 ∗
  memRegion (sp + 0x5bd#64) 3 ∗
  ((sp + 0x5c0#64) ↦₆₄ (sp + 0x5bc#64)) ∗ ((sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
  ((sp + 0x5d0#64) ↦₆₄ (sp + 0x5b0#64)) ∗
  memRegion (sp + 0x5f0#64 + 8#64) 0x6a8 ∗ memRegion (sp + 0xdf8#64) 8 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - dropSessionStructureLocal2Stack) ∗
  sessionStateExposedAt_shared_lb A (sp + 0x138#64) x.G x.st ∗
  errsAt A (sp + 0x5d8#64) [r_err] ∗
  cliTapeAfter ctl x.cur x.rest (x.draws C)

private def segTailActPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State)
    (x : RecordDecryptGhost) (sp : BitVec 64)
    (w5f0 w0 w1 w2 w3 : BitVec 64) (b4 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  ((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 0x6974707972636564#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗
  ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 0x64#8) ∗
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ w5f0) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
  sessionStateAt A.repAlloc (sp + 0xca0#64) G₂ st₂ ∗
  ((sp + 0x4b0#64) ↦₆₄ w0) ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ w1) ∗
  ((sp + 0x4b0#64 + 16#64) ↦₆₄ w2) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ w3) ∗
  ((sp + 0x4b0#64 + 32#64) ↦₈ b4) ∗ memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
  stackAt sp dropSessionStructureLocal2Stack ∗ A.pool lim st s

private def segTailPostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st' : M.σ) (sf : State)
    (x : RecordDecryptGhost) (sp : BitVec 64) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
  ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
  ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  memRegion (sp + 0xca0#64) 344 ∗
  recordResultAt A.repAlloc (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
  stackAt sp dropSessionStructureLocal2Stack ∗ A.pool lim st' sf

private theorem segTail_finish_mem [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st' : M.σ) (s_end : State)
    (x : RecordDecryptGhost) (sp p : BitVec 64) (hp : p ≠ 0) (m : Memory) (F : SepProp)
    (hm : m ⊨
      (((lsmpl.ρ decryptionFailedSym) ↦₆₄ᵣ 7598822138193339748#64) ∗
       ((lsmpl.ρ decryptionFailedSym + 8#64) ↦₆₄ᵣ 7308332162361618031#64) ∗
       ((lsmpl.ρ decryptionFailedSym + 16#64) ↦₈ᵣ 100#8)) ∗
      (((sp + 0x4b0#64) ↦₆₄ speWord 24 ∗ ((sp + 0x4b0#64 + 8#64) ↦₆₄ 17#64) ∗
        ((sp + 0x4b0#64 + 16#64) ↦₆₄ p) ∗ ((sp + 0x4b0#64 + 24#64) ↦₆₄ 17#64) ∗
        ((sp + 0x4b0#64 + 32#64) ↦₈ msgTypeByte .whisper) ∗
        memRegion (sp + 0x4b0#64 + 33#64) 15 ∗
        A.live p 17 1 ∗
        (p ↦₆₄ 0x6974707972636564#64) ∗
        ((p + 8#64) ↦₆₄ 0x656c696166206e6f#64) ∗
        ((p + 16#64) ↦₈ 0x64#8)) ∗
       ((memRegion (sp - BitVec.ofNat 64 dropSessionStructureLocal2Stack) 96 ∗
         stackAt sp allocHookStack) ∗
        (((sp + 0x80#64) ↦₆₄ x.sret) ∗ ((sp + 0x128#64) ↦₆₄ x.prevPtr) ∗
         ((sp + 0x130#64) ↦₆₄ 0#64) ∗ ((sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
         ((sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
         ((sp + 0x5f0#64) ↦₆₄ (bv% (2 ^ 64 - 1))) ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         memRegion (sp + 0xca0#64) 344 ∗
         A.pool lim st' s_end) ∗ F))) :
    m ⊨ segTailPostPlaced A lim st' s_end x sp ∗ F := by
  have hm_keep := Satisfies.of_sep_right hm
  have hm_res := recordResultAt_decryptionFailed_intro_shared_lb A.repAlloc (sp + 0x4b0#64) p hp hm_keep
  rw [← stackAt_dropLocal2_split_alloc sp] at hm_res
  exact Eq.mp (congrArg (m ⊨ ·) (by unfold segTailPostPlaced; sep_ac_rfl)) hm_res

set_option maxHeartbeats 1600000 in
theorem segTail_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {H : String → Option (State → State)} :
    SegTailPlacedSpec C A lim ctl uuidTryParse S tdEnv H := by
  intro hshim_sat halloc_sat _hpanic_eq hdrop2 x st_init st R s0 s hF hL
  obtain ⟨hsb, hpc_s, ⟨hrun, hsp, hsp_align, hx29, htrace, hfl, hvregs⟩, hmodel, hmem⟩ := hF
  dsimp only [recFPCPlaced] at hpc_s
  have hfit_tail : FitsEnv M lim st SegTailEnv := hsb.1.seq_left
  rw [cliRecFramePlaced_atState, sessionStateAt_atState] at hmem
  conv at hmem =>
    simp only [sessionStateAt_atState, errsAt_atState]
  have hsp0_align : (s0.sp &&& 15#64 == 0#64) = true := by
    simpa [State.spAligned, hsp] using hsp_align
  have hcap_lt : x.G.localIk.cap.toNat < 2 ^ 63 :=
    sessionStateAt_localIk_cap_lt_shared_lb
      (P := recFramePlaced A.repAlloc x s0.sp ∗ A.pool lim st s)
      (by simpa only [sepConj_assoc] using hmem)
  have hcap_ne : x.G.localIk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hfl.1
  have hro := hfl.2
  have hshim := ls_hook_ok_226 (by decide) hshim_sat
  have halloc := subroutine_ok_allocNoOom_of_budget (ls_hook_ok_226 (by decide) halloc_sat)
  have hmem_ro := rodata_decryptionFailed_placed_intro hro hmem
  clear hmem
  rw [pointsToBytesRO_decryptionFailed, recFramePlaced_expose_rep A.repAlloc x s0.sp,
    RustCliAllocBudget.repAlloc_pool, sepConj_emp,
    sessionStateAt_expose_shared_lb A.repAlloc (s0.sp + 0x138#64) x.G x.st,
    memRegion_slot48_split (s0.sp + 0x4b0#64)] at hmem_ro
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hmem_ro
  obtain ⟨b4, w3, w2, w1, w0, r_err, G₂, st₂, w5f0, hmem_ro⟩ := hmem_ro
  have hmem_split : s.mem ⊨
      segTailActPlaced A lim st s x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂ ∗
      (segTailFrame C A.repAlloc ctl x s0.sp r_err ∗ R) := by
    dsimp only [segTailActPlaced, segTailFrame]
    arm64_sep_close
  clear hmem_ro
  have hwp : SepWP ((blkPC_463).rebase (blkPl_463).base H)
      ((blkPl_463).base + 7820#64) s
      (segTailActPlaced A lim st s x s0.sp w5f0 w0 w1 w2 w3 b4 G₂ st₂)
      (fun s' P_f => ∃ evs_tail : List AllocEvent,
        SegTailEnv evs_tail ∧
        s'.sp = s0.sp ∧ s'.spAligned = true ∧
        s'.readReg64 .x29 = s0.readReg64 .x29 ∧ s'.trace = s0.trace ∧
        s'.readReg64 .x26 = s0.sp + 0xa0#64 ∧ s'.readReg64 .x27 = x.sret ∧
        s'.readReg64 .x28 = speWord 24 ∧ calleeSavedVRegs s' = calleeSavedVRegs s0 ∧
        (∀ m F, (m ⊨ P_f ∗ F) →
          (m ⊨ segTailPostPlaced A lim (M.stepEvents evs_tail st) s' x s0.sp ∗ F))) := by
    dsimp only [segTailActPlaced]
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : RustLayoutOk 17 1 := ⟨⟨by decide, hpow2, by decide⟩, by decide⟩
    have hcap_beq : (x.G.localIk.cap + 1#64 == 0#64) = false :=
      beq_eq_false_iff_ne.mpr hcap_ne
    apply sepWP_seq_lscl hcl (mid := lsmpl.base 442)
    by_vm_open (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
      intro hvm1 hcl_call
      refine SepWP.transport_budgetPool hvm1 (hnext := ?_); clear hvm1
      wp_apply
      let evs_drop : List AllocEvent := w
      have hevs_drop : FreeOnlyEvs evs_drop := hpost
      have htr_drop : sf.trace = _ := ‹sf.trace = _›
      have hfit_alloc : FitsEvents M lim (M.stepEvents evs_drop st) (rustAllocEvents 17 1) :=
        (hfit_tail.seq_right hevs_drop) (rustAllocEvents 17 1) rfl
      rw [hsp, stackAt_dropLocal2_split_alloc s0.sp]
      apply sepWP_cut_here (mid := (blkPl_463).base + 6840#64)
      by_vm_open (
        wp_steps
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
        intro hvm2a
        let s_2a := (fun {a b : State} (_ : VmPreserved a b) => b) hvm2a
        refine SepWP.transport_budgetPool hvm2a (hnext := ?_)
        wp_step
        apply sepWP_cut_here (mid := lsmpl.ρ lsRustNoAllocShimSym)
        by_vm_open (
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
          intro hvm2b
          have hvm2 : VmPreserved s_2a _ :=
            VmPreserved.trans
              (by
                dsimp only [s_2a]
                rw [Placed.BudgetVmSteps.vmPreserved_setPC,
                  Placed.BudgetVmSteps.vmPreserved_writeReg64]
                exact VmPreserved.refl _)
              hvm2b
          refine SepWP.transport_budgetPool hvm2 (hnext := ?_); clear hvm2 hvm2b s_2a hvm2a
          wp_apply
          have hsp_sf1 : sf_1.sp = sf.sp := by assumption
          refine SepWP.transport_budgetPool (by assumption) (hnext := ?_)
          apply sepWP_cut_here (mid := lsmpl.ρ lsRustAllocSym)
          by_vm_open (
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
            intro hvm3
            refine SepWP.transport_budgetPool hvm3 (hnext := ?_); clear hvm3
            wp_apply
            have hacp_alloc : AllocCallPreserved sf_1 sf_2 := by assumption
            have hoom : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0#64 := ‹sf_2.readReg64 .x0 ≠ 0#64›
            have hoom'' : sf_2.readReg64 (Reg.gpr 0#5) ≠ 0 := hoom
            have hoom_beq : (sf_2.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
              beq_eq_false_iff_ne.mpr hoom
            have htr_alloc := hacp_alloc.2.1
            try dsimp only [Bool.false_eq_true, ↓reduceIte]
            rw [memRegion_17_split (sf_2.readReg64 (Reg.gpr 0#5))]
            simp only [sepExists_sepConj_left, sepExists_sepConj_right]
            refine SepWP.exists_elim fun u2 => SepWP.exists_elim fun u1 =>
              SepWP.exists_elim fun u0 => ?_
            wp_step
            wp_step
            wp_step
            by_vm_open (
              wp_steps
              refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ⟨by simp only [wp_norm, arm64_norm], ?_⟩
              intro hvm4_tail
              have hvm4 : VmPreserved sf_2 _ :=
                VmPreserved.trans (by simp only [wp_norm, arm64_norm]) hvm4_tail
              let s_end := (fun {a b : State} (_ : VmPreserved a b) => b) hvm4
              have hpool4 := A.pool_transport lim
                (M.stepEvents (rustAllocEvents 17 1) (M.stepEvents evs_drop st)) sf_2 s_end hvm4
              refine ⟨evs_drop ++ rustAllocEvents 17 1,
                SeqEnv.append hevs_drop rfl,
                by simp only [wp_norm, arm64_norm, *],
                by simp only [State.spAligned, wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [speWord, wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *], ?_⟩
              intro m F hm
              rw [← hpool4] at hm
              rw [← M.stepEvents_append evs_drop (rustAllocEvents 17 1) st] at hm
              rw [hsp_sf1, hsp_sf, hsp] at hm
              simp only [wp_norm, arm64_norm] at hm
              apply segTail_finish_mem A lim _ s_end x s0.sp (sf_2.readReg64 (Reg.gpr 0#5)) hoom'' m F
              dsimp only [speWord, dropSessionStructureLocal2Stack]
              arm64_sep_close
            )
          )
        )
      )
    )
  obtain ⟨s', hsteps, hout⟩ := SepWP.to_reaches_pc hwp hmem_split hL
  rcases hout with ⟨hpc', hrun', P_f, hmf, evs_tail, hevs_tail,
      hsp', hsp_align', hx29', htr', hx26', hx27', hx28', hvregs', hent⟩ | ⟨_, hoom⟩
  · refine ⟨s', hsteps, Or.inl ⟨M.stepEvents evs_tail st,
      hsb.step (fun _ _ => SeqEnv.append) hevs_tail, ?_⟩⟩
    have hmeta' : recMetaPlaced s0 s' :=
      ⟨hrun', hsp', hsp_align', hx29', htr', hfl.of_keepsFrozen hsteps.keepsFrozen, hvregs'⟩
    have hno_pan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
      rw [hmodel]; decide
    have htag : s'.readReg64 .x28 = recordResultTag (x.model C S uuidTryParse).1 := by
      rw [hmodel, recordResultTag]; exact hx28'
    refine ⟨hpc', hmeta', hno_pan, hx26', hx27', htag, ?_⟩
    have hmf' := hent s'.mem (segTailFrame C A.repAlloc ctl x s0.sp r_err ∗ R) hmf
    clear hmf
    rw [hmodel, cliRecFramePlaced_atState, sessionStateAt_atState, recordResultAt_atState]
    rw [recFramePlaced_expose_rep A.repAlloc x s0.sp,
      RustCliAllocBudget.repAlloc_pool, sepConj_emp,
      sessionStateAt_expose_shared_lb A.repAlloc (s0.sp + 0x138#64) x.G x.st]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    refine ⟨[r_err], bv% (2 ^ 64 - 1), ?_⟩
    rw [errsAt_atState]
    dsimp only [segTailPostPlaced, segTailFrame] at hmf'
    arm64_sep_close
  · exact (not_satisfies_false_sepConj hoom).elim

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegTailPlacedBudget
