/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.MainBudget -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `LoadRatchet` Symbolic Execution Lemmas

Relocatable `[LibsignalPlacement]` Segment S1 symbolic execution step lemmas on block `130`,
recording `VmPreserved` across error/success continuations after `TripleRatchet::from_session_state`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSymBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Mut TripleRatchet)
open CryptoVerification (
  LibsignalPlacement LibsignalRoLoaded blkPC_57 blkPl_57 lsLogFilterAddr lsmpl
  ls_subroutine_ok_of_block
)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  errTag protocolAddressAt sessionStateAt signalMessageAt tapeAfter
)
open CryptoVerification.LibsignalTripleRatchet (
  TrFromGhost TryDecryptGhost trFromStack trResultAt
)
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet (withLsRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  tryDecryptCommonHeap tryDecryptSavedRegs tryDecryptSubStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (
  SepWP.bind_framed SepWP.rw_pre blkPC_131 blkPl_131 logOff_tryDecryptDummyImg
  memRegion_0x38_split_trFrom reaches_pc_call_lscl reaches_pc_lsro reaches_pc_seq_lscl
  retEpiloguePC_placed segFindChainPC_placed segLoadRatchetPC_placed sepWP_to_reaches_pc
  stackAt_tryDecryptSubStack_sub tryDecryptDummyImg tryDecryptEntry_placed
  tryDecryptMidMeta_placed tryDecryptWPInv
  words4At words5At words8At words32At words32At_40_eq words32At_198_eq
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget (LoadRatchetState_placed)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget (sepWP_blk130_vm)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244PlacedBudget (
  trFromPlacedSpec trFromRawPlacedSpec
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Relocatable (`[LibsignalPlacement]`) Budget-Threaded Segment S1 Symbolic Steps -/

theorem loadRatchet_bl_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)} {s0 s : State}
    (hpc : s.pc = segLoadRatchetPC_placed)
    (hmeta : tryDecryptWPInv s0 s) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) (blkPl_57).base s emp
      (fun s1 P1 =>
        P1 = emp ∧
        VmPreserved s s1 ∧
        tryDecryptWPInv s0 s1 ∧
        s1.readReg64 Reg.lr = (blkPl_131).base + 484#64 ∧
        s1.readReg64 .x0 = s.readReg64 .x21 ∧
        (s1.readReg64 .x1).setWidth 32 = (s.readReg64 .x1).setWidth 32 ∧
        s1.readReg64 .x8 = sp + 0x190#64 ∧
        CalleeSavedPreserved s s1) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segLoadRatchetPC_placed, tryDecryptEntry_placed] at hpc
  apply sepWP_blk130_vm (mid := (blkPl_57).base)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]; rfl)
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  refine SepWP.done (by simp_all [wp_norm, arm64_norm]; rfl) (by simp_all [wp_norm, arm64_norm]) ?_
  refine ⟨rfl, hvm,
    ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], hs0_align,
      by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
      by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm], ?_⟩
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, wp_norm, arm64_norm, *]

theorem loadRatchet_call_trFrom_reaches_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {ctl : BitVec 64} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec M A lim))
    (x : TryDecryptGhost) (R : SepProp) (s0 s : State)
    (hS1 : LoadRatchetState_placed A lim stB ctl x R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    let res := Mut.exec TripleRatchet.fromSessionState x.st
    reaches_pc prog ((blkPl_131).base + 484#64) s
      (fun s_ret =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          tryDecryptMidMeta_placed s0 s_ret ∧
          s_ret.readReg64 .x19 = x.ret ∧
          s_ret.readReg64 .x20 = sp + 0x140#64 ∧
          s_ret.readReg64 .x21 = x.ss ∧
          s_ret.readReg64 .x22 = x.msgA ∧
          s_ret.readReg64 .x23 = sp + 0x500#64 ∧
          (s_ret.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType ∧
          s_ret.readReg64 .x25 = x.locA ∧
          (s_ret.mem ⊨
            sessionStateAt A.repAlloc x.ss x.G.afterTrFrom res.2 ∗
            trResultAt A.repAlloc (sp + 0x190#64) x.G res.1 ∗
            memRegion x.ret 48 ∗
            memRegion sp 0x30 ∗
            ((sp + 0x30#64) ↦₆₄ x.remA) ∗
            memRegion (sp + 0x38#64) 0x158 ∗
            memRegion (sp + 0x298#64) 0x2e8 ∗
            tryDecryptCommonHeap (A.atState lim (M.stepEvents evs stB) s_ret) ctl
              tryDecryptDummyImg x 0 s0 ∗ R)) := by
  dsimp only
  let sp := s0.sp - 1504#64
  rcases hS1 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx1, hmem⟩
  have hwp_bl := loadRatchet_bl_wp_placed (H := H) hpc (tryDecryptMidMeta_placed.to_wpInv hmeta)
  have hmem_emp : s.mem ⊨ emp ∗
      (sessionStateAt (A.atState lim stB s) x.ss x.G x.st ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x548 ∗
       tryDecryptCommonHeap (A.atState lim stB s) ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    rw [emp_sepConj]; exact hmem
  refine reaches_pc_seq_lscl hmeta.2.2.2.2.2.2.1
    (reaches_pc_lsro hro (sepWP_to_reaches_pc hwp_bl hmem_emp)) ?_
  intro s_call hpc_call _ ⟨⟨P1, hm_call, ⟨hP1, hvm_c, hwpInv_call, hlr_call, hx0_c, hx1_c, hx8_c, hcs_c⟩⟩, hro_call⟩ hcl_call
  subst hP1
  rw [emp_sepConj] at hm_call
  unfold tryDecryptCommonHeap at hm_call
  rw [memRegion_0x38_split_trFrom, logOff_tryDecryptDummyImg,
      stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide)] at hm_call
  have hpool_eq : (A.atState lim stB s).pool = A.pool lim stB s_call :=
    congrArg (·.pool) (A.atState_eq_of_vmPreserved lim stB hvm_c).symm
  have hlive_pa : ∀ pa p st' s',
      protocolAddressAt (A.atState lim st' s') pa p = protocolAddressAt A.repAlloc pa p :=
    fun _ _ _ _ => rfl
  have hlive_sm : ∀ g p m st' s',
      signalMessageAt (A.atState lim st' s') g p m = signalMessageAt A.repAlloc g p m :=
    fun _ _ _ _ _ => rfl
  have hlive_ss : ∀ p G st0 st' s',
      sessionStateAt (A.atState lim st' s') p G st0 = sessionStateAt A.repAlloc p G st0 :=
    fun _ _ _ _ _ => rfl
  rw [hpool_eq, hlive_ss, hlive_pa, hlive_pa, hlive_sm] at hm_call
  have hsp_call : s_call.sp = sp := hwpInv_call.2.1
  have halign_call : s_call.spAligned = true := hwpInv_call.2.2.2.1
  let tg : TrFromGhost := { ss := x.ss, G := x.G, st := x.st, ret := sp + 0x190#64 }
  let F_call : SepProp :=
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    signalMessageAt A.repAlloc x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    memRegion (s0.sp - 262144#64) (tryDecryptSubStack - trFromStack) ∗
    tryDecryptSavedRegs s0.sp s0 ∗ R
  have htrFrom_blk :=
    ls_subroutine_ok_of_block (callerProg := (blkPC_131).rebase (blkPl_131).base H) htrFrom
  have hpre_call : s_call.mem ⊨ (withLsRoLoaded lsmpl (trFromRawPlacedSpec M A lim)).pre (tg, stB) s_call ∗ F_call := by
    dsimp only [withLsRoLoaded, trFromRawPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hro_call, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0_c.trans hx21, hx1_c.trans hx1, hx8_c⟩, ?_⟩
    rw [hsp_call]
    change s_call.mem ⊨ _
    dsimp only [tg, F_call, sp] at hm_call ⊢
    convert hm_call using 1; sep_ac_rfl
  refine reaches_pc_call_lscl htrFrom_blk (tg, stB) F_call hpc_call hwpInv_call.1 hlr_call hcl_call hpre_call
    (fun s_ret hpc_ret hrun_ret hsp_ret hcs_ret hcl_ret hpost_ret => ?_) halign_call
  refine reaches_pc_refl hpc_ret hrun_ret ?_
  dsimp only [withLsRoLoaded, trFromRawPlacedSpec] at hpost_ret
  rw [sepExists_sepConj_left, satisfies_sepExists] at hpost_ret
  rcases hpost_ret with ⟨evs, hpost_ret⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_ret
  rcases hpost_ret with ⟨⟨hevs, _hAfter, htr_ret⟩, hm_ret⟩
  have hsp_ret' : s_ret.sp = s0.sp - 1504#64 := by reg_chain
  have halign_ret : s_ret.spAligned = true := by
    rw [State.spAligned, hsp_ret', ← hwpInv_call.2.1]; exact halign_call
  have hmeta_ret : tryDecryptMidMeta_placed s0 s_ret :=
    ⟨hrun_ret, hsp_ret', hwpInv_call.2.2.1, halign_ret, by reg_chain, by reg_chain, hcl_ret, by reg_chain⟩
  refine ⟨evs, hevs, hmeta_ret, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    by reg_chain, by reg_chain, ?_⟩
  rw [hsp_call] at hm_ret
  unfold tryDecryptCommonHeap
  rw [logOff_tryDecryptDummyImg, stackAt_tryDecryptSubStack_sub s0.sp trFromStack (by decide),
      hlive_pa, hlive_pa, hlive_sm]
  change s_ret.mem ⊨ _
  dsimp only [tg, TrFromGhost.model, F_call, sp] at hm_ret ⊢
  convert hm_ret using 1; sep_ac_rfl

theorem loadRatchet_err_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {ret tag w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64}
    {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx19 : s.readReg64 .x19 = ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog retEpiloguePC_placed s
      (((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ tag) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       (ret ↦₆₄ r0) ∗
       words5At (ret + 8#64) r1 r2 r3 r4 r5)
      (fun sf P =>
        P = (((sp + 0x190#64) ↦₆₄ errTag) ∗
             ((sp + 0x198#64) ↦₆₄ tag) ∗
             words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
             ((sp + 0x500#64) ↦₆₄ tag) ∗
             words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
             (ret ↦₆₄ tag) ∗
             words5At (ret + 8#64) w0 w1 w2 w3 w4) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf) := by
  dsimp only
  rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed]
  unfold words5At errTag
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 916#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩⟩

theorem loadRatchet_ok_1a_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA g20 w0 w1 w2 w3 w4 w5 t0 t1 t2 t3 t4 t5 : BitVec 64} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 528#64) s
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
       ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5))
      (fun sf P =>
        P = (((sp + 0x20#64) ↦₆₄ locA) ∗ ((sp + 0x190#64) ↦₆₄ cap) ∗ words4At (sp + 0x198#64) w0 w1 w2 w3 ∗
             ((sp + 0x1b8#64) ↦₆₄ w4) ∗ ((sp + 0x1c0#64) ↦₆₄ w5) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5)) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x8 = cap ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = sp + 0x190#64 ∧ sf.readReg64 .x27 = sp + 0x38#64) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 528#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1b_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap remA msgA d_cap w6 w7 w16 w17 w24 w25 w26 w27 w28 w29 w30 w31 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_131).base + 528#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = cap) (hx22 : s.readReg64 .x22 = msgA)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 588#64) s
      (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
       ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
       words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
       words8At (sp + 0x100#64) d24 d25 d26 d27 d28 d29 d30 d31)
      (fun sf P =>
        P = (((sp + 0x30#64) ↦₆₄ remA) ∗ ((sp + 0x38#64) ↦₆₄ cap) ∗ ((sp + 0x1c8#64) ↦₆₄ w6) ∗
             ((sp + 0x1d0#64) ↦₆₄ w7) ∗ ((sp + 0x218#64) ↦₆₄ w16) ∗ ((sp + 0x220#64) ↦₆₄ w17) ∗
             words8At (sp + 0x258#64) w24 w25 w26 w27 w28 w29 w30 w31 ∗
             words8At (sp + 0x100#64) w24 w25 w26 w27 w28 w29 w30 w31) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 0x38#64 ∧ sf.readReg64 .x1 = msgA + 0x38#64 ∧
        sf.readReg64 .x8 = remA ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = sp + 0x2c0#64 ∧ sf.readVReg128 0#5 = w17 ++ w16 ∧ sf.readVReg128 2#5 = w7 ++ w6) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 588#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1c_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {w8 w9 w16 w17 w18 w19 w20 w21 w22 w23 d16 d17 d18 d19 d20 d21 d22 d23 : BitVec 64}
    {s0 s : State} (hpc : s.pc = (blkPl_131).base + 588#64) (hmeta : tryDecryptWPInv s0 s)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hx27 : s.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64)
    (hq0 : s.readVReg128 0#5 = w17 ++ w16) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) ((blkPl_131).base + 620#64) s
      (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
       ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
       words8At (sp + 0xc0#64) d16 d17 d18 d19 d20 d21 d22 d23)
      (fun sf P =>
        P = (((sp + 0x1d8#64) ↦₆₄ w8) ∗ ((sp + 0x1e0#64) ↦₆₄ w9) ∗ ((sp + 0x228#64) ↦₆₄ w18) ∗
             ((sp + 0x230#64) ↦₆₄ w19) ∗ words4At (sp + 0x238#64) w20 w21 w22 w23 ∗
             words8At (sp + 0xc0#64) w16 w17 w18 w19 w20 w21 w22 w23) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = s.readReg64 .x8 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readVReg128 0#5 = w9 ++ w8 ∧ sf.readVReg128 2#5 = s.readVReg128 2#5) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 620#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_1d_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {remA msgA g2a0 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 620#64) (hmeta : tryDecryptWPInv s0 s)
    (hx8 : s.readReg64 .x8 = remA) (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64)
    (hq0 : s.readVReg128 0#5 = w9 ++ w8) (hq2 : s.readVReg128 2#5 = w7 ++ w6) :
    let sp := s0.sp - 1504#64
    SepWP ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
      (((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
       words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter) ∗ words8At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 ∗
       words8At (sp + 0x80#64) d8 d9 d10 d11 d12 d13 d14 d15)
      (fun sf P =>
        P = (((sp + 0x28#64) ↦₃₂ counter) ∗ ((sp + 0x1e8#64) ↦₆₄ w10) ∗ ((sp + 0x1f0#64) ↦₆₄ w11) ∗
             words4At (sp + 0x1f8#64) w12 w13 w14 w15 ∗ ((sp + 0x2a0#64) ↦₆₄ remA) ∗
             ((sp + 0x2ac#64) ↦₈ (s.readReg64 .x26).setWidth 8) ∗ words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
             ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗ ((msgA + 0x68#64) ↦₃₂ counter) ∗
             words8At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 ∗
             words8At (sp + 0x80#64) w8 w9 w10 w11 w12 w13 w14 w15) ∧
        VmPreserved s sf ∧
        tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = s.readReg64 .x0 ∧ sf.readReg64 .x1 = s.readReg64 .x1 ∧
        sf.readReg64 .x8 = sp + 0x190#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = s.readReg64 .x28) := by
  dsimp only; rcases hmeta with ⟨hrun, hsp, hs0_align, halign, hx29, htr⟩
  dsimp only [segFindChainPC_placed, tryDecryptEntry_placed]
  unfold words8At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]
  apply sepWP_blk130_vm (mid := (blkPl_131).base + 676#64)
  intro _m_strip
  wp_steps
  refine SepWP.done (by simp_all [wp_norm, arm64_norm])
    (by simp_all [wp_norm, arm64_norm]) fun _m_real hnsp => ?_
  have hvm : VmPreserved s _ := hnsp.toVmPreserved (by simp only [wp_norm, arm64_norm])
  wp_finish
  exact ⟨by ac_rfl, hvm, ⟨by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    hs0_align, by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm]⟩,
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm],
    by simp_all [wp_norm, arm64_norm], by simp_all [wp_norm, arm64_norm]⟩

theorem loadRatchet_ok_wp_placed [LibsignalPlacement]
    {H : String → Option (State → State)}
    {cap locA remA msgA g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
     w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
     d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
     d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64}
    {counter g28 : BitVec 32} {g2ac : BitVec 8} {s0 s : State}
    (hcap : cap + 1#64 ≠ 0#64) (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptWPInv s0 s)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx22 : s.readReg64 .x22 = msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx25 : s.readReg64 .x25 = locA) :
    let prog := (blkPC_131).rebase (blkPl_131).base H
    let sp := s0.sp - 1504#64
    SepWP prog segFindChainPC_placed s
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x30#64) ↦₆₄ remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ cap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((msgA + 0x68#64) ↦₃₂ counter))
      (fun sf P =>
        ∃ b2ac : BitVec 8,
          P = (((sp + 0x20#64) ↦₆₄ locA) ∗ ((sp + 0x28#64) ↦₃₂ counter) ∗ ((sp + 0x30#64) ↦₆₄ remA) ∗
               ((sp + 0x38#64) ↦₆₄ cap) ∗
               words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x190#64) ↦₆₄ cap) ∗
               words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
                 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
               ((sp + 0x2a0#64) ↦₆₄ remA) ∗ ((sp + 0x2ac#64) ↦₈ b2ac) ∗
               words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
               ((msgA + 0x68#64) ↦₃₂ counter)) ∧
          VmPreserved s sf ∧
          tryDecryptWPInv s0 sf ∧ sf.readReg64 .x0 = sp + 0x38#64 ∧ sf.readReg64 .x1 = msgA + 0x38#64 ∧
          sf.readReg64 .x8 = sp + 0x190#64 ∧ sf.readReg64 .x19 = s.readReg64 .x19 ∧
          sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
          sf.readReg64 .x22 = s.readReg64 .x22 ∧ sf.readReg64 .x23 = s.readReg64 .x23 ∧
          sf.readReg64 .x24 = s.readReg64 .x24 ∧ sf.readReg64 .x25 = sp + 0x190#64 ∧
          sf.readReg64 .x27 = sp + 0x38#64 ∧ sf.readReg64 .x28 = sp + 0x2c0#64) := by
  dsimp only
  have h1a := loadRatchet_ok_1a_wp_placed (H := H)
    (cap := cap) (locA := locA) (g20 := g20)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    hcap hpc hmeta hx20 hx23 hx25
  refine SepWP.rw_pre (by rw [words32At_40_eq, words32At_198_eq]) ?_
  refine SepWP.bind_framed h1a (by sep_frame) ?_
  intro s1a P1a ⟨hP1a, hvm1a, hmeta1a, hx8_1a, hx19_1a, hx20_1a, hx21_1a, hx22_1a, hx23_1a, hx24_1a, hx25_1a, hx27_1a⟩ hpc1a
  subst hP1a
  have h1b := loadRatchet_ok_1b_wp_placed (H := H)
    (cap := cap) (remA := remA) (msgA := msgA) (d_cap := d_cap)
    (w6 := w6) (w7 := w7) (w16 := w16) (w17 := w17)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27)
    (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27)
    (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    hpc1a hmeta1a hx8_1a (hx22_1a.trans hx22) hx25_1a hx27_1a
  refine SepWP.bind_framed h1b (by sep_frame) ?_
  intro s1b P1b ⟨hP1b, hvm1b, hmeta1b, hx0_1b, hx1_1b, hx8_1b, hx19_1b, hx20_1b, hx21_1b, hx22_1b, hx23_1b, hx24_1b, hx25_1b, hx27_1b, hx28_1b, hq0_1b, hq2_1b⟩ hpc1b
  subst hP1b
  have h1c := loadRatchet_ok_1c_wp_placed (H := H)
    (w8 := w8) (w9 := w9) (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19)
    (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19)
    (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    hpc1b hmeta1b (hx25_1b.trans hx25_1a) (hx27_1b.trans hx27_1a) hq0_1b
  refine SepWP.bind_framed h1c (by sep_frame) ?_
  intro s1c P1c ⟨hP1c, hvm1c, hmeta1c, hx0_1c, hx1_1c, hx8_1c, hx19_1c, hx20_1c, hx21_1c, hx22_1c, hx23_1c, hx24_1c, hx25_1c, hx27_1c, hx28_1c, hq0_1c, hq2_1c⟩ hpc1c
  subst hP1c
  have h1d := loadRatchet_ok_1d_wp_placed (H := H)
    (remA := remA) (msgA := msgA) (g2a0 := g2a0)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5)
    (w6 := w6) (w7 := w7) (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11)
    (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (counter := counter) (g28 := g28) (g2ac := g2ac)
    hpc1c hmeta1c (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
    hq0_1c (by reg_chain)
  refine SepWP.bind_framed h1d (by sep_frame) ?_
  intro sf Pf ⟨hPf, hvm1d, hmetaf, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hpcf
  subst hPf
  refine SepWP.done hpcf hmetaf.1 ⟨(s1c.readReg64 .x26).setWidth 8, ?_,
    hvm1a.trans (hvm1b.trans (hvm1c.trans hvm1d)), hmetaf, by reg_chain⟩
  rw [words32At_40_eq, words32At_198_eq]
  sep_ac_rfl

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSymBudget
