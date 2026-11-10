/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move

/-!
# Budget-Threaded Placed Segment 2: `receiver_chains` (Block `518`)

Deterministic allocation-event trace `cloneChainsEvents` / `CloneChainsEnv` and budget-threaded
(`[LibsignalPlacement]`, `RustCliAllocBudget M`) Segment 2 proofs (`cloneChains_vregs_placed_ok`,
`+0x19b0 → +0x1a5c`, `genP3J1PlacedBudget → genP3J2PlacedBudget`) on Block `518`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

open scoped CryptoVerification.RustHeap CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (SessionState SignalMessage)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (GenP3J2Witness genP3ChainsSpillScratch genP3PendSpillScratch genP3SenderInlineWords genP3TailSpillScratch)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1 (lsAllocSym lsShimSym)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (dpClosureEntryM3Placed genP3CallFramePlaced)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.LibsignalSessionRepr (chainAt)
open CryptoVerification.LibsignalTripleRatchet (rootStack sessionShimSpec)
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone (chainCloneStack)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (optSenderChainHeap)
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps (ofNat_ne_zero_of_pos segClone_bv_ofNat_mul_104_toNat segClone_vecBufRest segClone_vecBuf_chain_nil_eq segClone_vecBuf_chain_of_arrayAt segClone_vecBuf_expose_arrayAt segClone_vecBuf_reassemble_arrayAt stackAt_chainClone_eq_alloc)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost SessionGhost SignalMessageGhost)
open CryptoVerification.RustHeap (allocHookStack arrayAt vecBuf vecU8Buf)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge (rustAllocShimVmSpec)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudgetAux (
  m3a2SessionStatePure m3a2SessionStateRestAt' rc_alloc_call_placed_budget_ok
  rc_alloc_prehdr_placed_wp_vm rc_alloc_prep_placed_wp_vm rc_empty_placed_wp_vm
  rc_epilogue_placed_wp_vm rc_loop_placed_budget_ok rc_prebranch_placed_wp_vm
  sessionStateAt_coro_placed_eq
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget (
  genP3J1PlacedBudget genP3J2PlacedBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux (
  bind_sepWP_vm_pool_placed ret_sepWP_vm_pool_placed sepWPp_bind_frame_any sepWPp_done_any
  sepWPp_exists_elim_any sepWPp_pure_elim_any sepWPp_weaken_frame_any sepWPp_weaken_pre_any
)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (chainCloneEvents)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec subroutine_ok_sessionShimBudget_of_rustAllocShimVm
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## 1. Deterministic `AllocEvent` Trace & Envelope for `CloneChains` -/

/-- Deterministic `AllocEvent` sequence emitted by Segment 2 (`+0x19b0 → +0x1a5c`) of Stage P3
    `SessionState::clone`:
    - `[]` when `st.receiverChains = []`;
    - `rustAllocEvents (st.receiverChains.length * 104) 8` followed by
      `(recG.chains.zip st.receiverChains).flatMap chainCloneEvents` when non-empty. -/
def cloneChainsEvents (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent :=
  if st.receiverChains = [] then []
  else rustAllocEvents (st.receiverChains.length * 104) 8 ++
    (recG.chains.zip st.receiverChains).flatMap chainCloneEvents

/-- Exact allocation envelope for Segment 2 (`+0x19b0 → +0x1a5c`) of Stage P3
    `SessionState::clone`. -/
def CloneChainsEnv (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = cloneChainsEvents recG st

theorem cloneChainsEnv_events (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    CloneChainsEnv recG st (cloneChainsEvents recG st) := rfl

theorem fitsEvents_cloneChains_of_fitsEnv (M : AllocCostModel) (lim : BudgetLimits)
    (stB : M.σ) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (h : FitsEnv M lim stB (CloneChainsEnv recG st)) :
    FitsEvents M lim stB (cloneChainsEvents recG st) :=
  h (cloneChainsEvents recG st) rfl

private theorem sessionShimBudget_of_noAllocShimBudget {P : Program} {a : BitVec 64}
    (h : subroutine_ok P a noAllocShimBudgetSpec) :
    subroutine_ok P a sessionShimBudgetSpec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [noAllocShimBudgetSpec, sessionShimBudgetSpec, sessionShimSpec] at hq ⊢
  rw [satisfies_pure_sepConj] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hq.1.2, hq.1.1, hq.2⟩

/-! ## 2. Budget-Threaded `cloneChains_vregs_placed_ok` (`+0x19b0 → +0x1a5c`) -/

set_option maxHeartbeats 800000 in
/-- Total-correctness (`onPanic` polymorphic, `onOom = ⌜False⌝` under `FitsEvents`) relocatable
    `[LibsignalPlacement]` Segment 2 (`+0x19b0 → +0x1a5c`,
    `genP3J1PlacedBudget → genP3J2PlacedBudget`) on `lsProg_518 ext`. -/
theorem cloneChains_vregs_placed_ok_stepEvents [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEvents M lim stB (cloneChainsEvents recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x19b0#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x1a5c#64) s
      (genP3J1PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J2PlacedBudget A lim (M.stepEvents (cloneChainsEvents recG st) stB)
          sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
          recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  dsimp only [genP3J1PlacedBudget, genP3ChainsSpillScratch]
  refine sepWPp_exists_elim_any fun w => ?_
  refine sepWPp_pure_elim_any fun ⟨hsp, hx19, hx23, hx24, hx25, hx27, hx29, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_coro_placed_eq A.repAlloc coroPtr recG st]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine sepWPp_exists_elim_any fun cs => ?_
  refine sepWPp_pure_elim_any fun hpure => ?_
  have hchains_len : recG.chains.length = st.receiverChains.length := hpure.2.2.1
  have hzip_len : (recG.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains_len]
  rw [hzip_len, ← hsp]
  have hpre := rc_prebranch_placed_wp_vm ext s coroPtr
    (BitVec.ofNat 64 st.receiverChains.length)
    w.newLocIdPtr (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
    cs.u_60 cs.u_68 cs.u_70
    hpc hrun hsp_al hx19 hx23 hx24 hx25
  refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro hpre (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 _ hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
  have htr1 : s1.trace = s0.trace := htr1_s.trans htr
  have hx27_1' : s1.readReg64 .x27 = sp + 0x370#64 := hx27_1.trans hx27
  have hx29_1' : s1.readReg64 .x29 = fp := hx29_1.trans hx29
  rw [hsp]
  cases hrc_eq : st.receiverChains with
  | nil =>
    simp only [hrc_eq, List.length_nil, beq_self_eq_true, ↓reduceIte]
      at hpc1 hx23_1 ⊢
    have hev_nil : cloneChainsEvents recG st = [] := by
      simp [cloneChainsEvents, hrc_eq]
    have hemp := rc_empty_placed_wp_vm ext s1 hpc1 hrun1
    refine ret_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro1 hemp
      (by simp only [emp_sepConj]; sep_focus)
      fun sf _ _ hcrof _ hregsf => ?_
    rcases hregsf with ⟨hspf_1, htrf_1, hx19_f, hx23_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregsf_1⟩
    refine ⟨?_, htrf_1.trans htr1, hcrof, hvregsf_1.trans hvregs1⟩
    rw [emp_sepConj, hev_nil, LibsignalBinary.Heap.AllocCostModel.stepEvents_nil]
    let w' : GenP3J2Witness := { toGenP3J1Witness := w, newRcPtr := 8#64, chains' := [] }
    refine Entails.sepExists_right w' ?_
    apply Entails.pure_right
      ⟨hspf_1.trans hsp1, hx19_f.trans hx19_1,
       by simp [hrc_eq, hx23_f, hx23_1],
       hx25_f, hx27_f.trans hx27_1', hx28_f.trans hx28_1, hx29_f.trans hx29_1',
       by simp [w', hrc_eq], hsc_rel, hsc_inl⟩
    dsimp only [genP3J2PlacedBudget, w']
    rw [sessionStateAt_coro_placed_eq A.repAlloc coroPtr recG st, hrc_eq]
    simp only [List.zip_nil_right, List.length_nil,
      segClone_vecBuf_chain_nil_eq A.repAlloc, emp_sepConj, sepConj_assoc]
    refine Entails.trans
      (Q := ⌜m3a2SessionStatePure recG st⌝ ∗
        (((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
          ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
          ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) recG.chainsCap recG.chainsPtr [] ∗
          m3a2SessionStateRestAt' A.repAlloc coroPtr recG st ∗
          A.pool lim stB sf ∗
          stackAt sp chainCloneStack ∗
          memRegion (sp + 0x3e0#64) 104 ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            rem loc msgG msg ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
            recG.localIk.bytes ∗
          vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
            recG.remoteIk.bytes ∗
          vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
          optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
          genP3PendSpillScratch sp ∗
          genP3TailSpillScratch sp ∗
          ((sp + 0x48#64) ↦₆₄ w.c0) ∗
          ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
          ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
          ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
          ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
          ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
          ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
          ((sp + 0x98#64) ↦₆₄ 32#64) ∗
          ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
          genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
      ?_ (Entails.of_eq (by sep_ac_rfl))
    apply Entails.pure_right hpure
    exact Entails.of_eq (by sep_ac_rfl)
  | cons rc rcs_tl =>
    have hn_pos : 0 < (rc :: rcs_tl).length := by simp
    have hn_lt32 : (rc :: rcs_tl).length < 2 ^ 32 := by rw [← hrc_eq]; exact hrc_len
    have hmul_lt : (rc :: rcs_tl).length * 104 < 2 ^ 63 := by simp [List.length_cons] at hn_lt32 ⊢; omega
    have hmul_lt' : (rcs_tl.length + 1) * 104 < 2 ^ 63 := hmul_lt
    have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by omega
    have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
    have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by omega
    have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
        (rc :: rcs_tl).length * 104 := segClone_bv_ofNat_mul_104_toNat hmul_lt
    have hlen_beq : (BitVec.ofNat 64 (rc :: rcs_tl).length == 0#64) = false :=
      beq_false_of_ne (ofNat_ne_zero_of_pos hn_pos (by omega))
    rw [hrc_eq] at hpc1 hx23_1
    simp only [hlen_beq, Bool.false_eq_true, ↓reduceIte] at hpc1
    cases hgs_eq : recG.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hev_cons :
          cloneChainsEvents recG st =
            rustAllocEvents ((rc :: rcs_tl).length * 104) 8 ++
              ((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents := by
        simp [cloneChainsEvents, hrc_eq, hgs_eq]
      have hfits_split :
          FitsEvents M lim stB (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) ∧
          FitsEvents M lim (M.stepEvents (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) stB)
            (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) :=
        (fitsEvents_append M lim _ _ stB).mp (hev_cons ▸ hfits)
      rcases hfits_split with ⟨hfits_alloc, hfits_loop⟩
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A.repAlloc (stride := 104) 8 (chainAt A.repAlloc)
          recG.chainsCap recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) emp
      rw [sepConj_emp, sepConj_emp] at hexpose
      refine sepWPp_weaken_frame_any hexpose (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine sepWPp_pure_elim_any fun _ => ?_
      have hprep := rc_alloc_prep_placed_wp_vm ext hshim s1 coroPtr recG.chainsPtr
        (BitVec.ofNat 64 (rc :: rcs_tl).length)
        hpc1 hrun1 hsp1_al hx19_1 hx23_1
      refine bind_sepWP_vm_pool_placed (A := A) (lim := lim) (st := stB) hcro1 hprep (by sep_focus)
        fun s2 hpc2 hrun2 hcro2 _ hregs2 => ?_
      rcases hregs2 with ⟨hsp2_1, htr2_1, hx0_2, hx1_2, hx19_2, _,
        hx23_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs2_1⟩
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_1] using hsp1_al
      have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
      have hx27_2' : s2.readReg64 .x27 = sp + 0x370#64 := hx27_2.trans hx27_1'
      have hx29_2' : s2.readReg64 .x29 = fp := hx29_2.trans hx29_1'
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hx0_2_nat : (s2.readReg64 .x0).toNat = (rc :: rcs_tl).length * 104 := by
        rw [hx0_2, htoNat_mul]
      have halloc_step :=
        rc_alloc_call_placed_budget_ok (Qp := fun _ _ => False) ext halloc s2
          ((rc :: rcs_tl).length * 104) emp
          hpos_mul hsz_le63 hfits_alloc hcro2 hpc2 hrun2 hsp2_al hx0_2_nat hx1_2 hx30_2
      rw [hsp2, sepConj_emp] at halloc_step
      refine sepWPp_bind_frame_any halloc_step (by sep_focus)
        fun s3 _ hpc3 hrun3 ⟨hent3, hnz3, hsp3_2, htr3_2, hcs3, hcro3⟩ => ?_
      rw [sepConj_emp] at hent3
      refine sepWPp_weaken_pre_any (sepConj_mono_left hent3) ?_
      simp only [sepConj_assoc]
      have hsp3 : s3.sp = sp := hsp3_2
      have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2, ← hsp2] using hsp2_al
      have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
      rcases hcs3 with ⟨hx19_cs3, _, _, _, hx23_cs3, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs3_2⟩
      have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
      have hx23_3 : s3.readReg64 .x23 = BitVec.ofNat 64 (rc :: rcs_tl).length :=
        hx23_cs3.trans hx23_2
      have hx24_3 : s3.readReg64 .x24 = recG.chainsPtr := hx24_cs3.trans hx24_2
      have hx27_3 : s3.readReg64 .x27 = sp + 0x370#64 := hx27_cs3.trans hx27_2'
      have hx29_3 : s3.readReg64 .x29 = fp := hx29_cs3.trans hx29_2'
      set ptr' := s3.readReg64 .x0
      refine sepWPp_weaken_frame_any
        (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
      have hprehdr := rc_alloc_prehdr_placed_wp_vm ext s3 ptr'
        (BitVec.ofNat 64 (rc :: rcs_tl).length) recG.chainsPtr
        hnz3 hpc3 hrun3 rfl hx23_3 hx24_3
      refine bind_sepWP_vm_pool_placed (A := A) (lim := lim)
        (st := M.stepEvents (rustAllocEvents ((rc :: rcs_tl).length * 104) 8) stB)
        hcro3 hprehdr (by simp only [emp_sepConj]; sep_focus)
        fun s4 hpc4 hrun4 hcro4 _ hregs4 => ?_
      rcases hregs4 with ⟨hsp4_3, htr4_3, hx1_4, hx19_4, hx20_4, hx21_4,
        hx22_4, hx23_4, hx25_4, hx27_4, hx29_4, hvregs4_3⟩
      rw [emp_sepConj]
      have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
      have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_3] using hsp3_al
      have htr4 : s4.trace = s0.trace := htr4_3.trans htr3
      have hx19_4' : s4.readReg64 .x19 = coroPtr := hx19_4.trans hx19_3
      have hx22_4' : s4.readReg64 .x22 =
          0#64 + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 := by
        rw [hx22_4, List.length_cons, BitVec.zero_add]
      have hx23_4' : s4.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) := hx23_4
      have hx27_4' : s4.readReg64 .x27 = s4.sp + 0x370#64 := by
        rw [hsp4]; exact hx27_4.trans hx27_3
      have hx29_4' : s4.readReg64 .x29 = fp := hx29_4.trans hx29_3
      have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
      have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
      have hmr_eq : memRegion ptr' ((rc :: rcs_tl).length * 104) =
          memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) := by
        rw [hptr_zero, hsz_eq]
      rw [hmr_eq, hsz_eq, ← hsp4]
      refine sepWPp_weaken_pre_any
        (P' := A.pool lim (M.stepEvents (rustAllocEvents ((rcs_tl.length + 1) * 104) 8) stB) s4 ∗
                arrayAt (chainAt A.repAlloc) 104 recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                memRegion (s4.sp + 0x3e0#64) 104 ∗
                stackAt s4.sp chainCloneStack ∗
                (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
                  ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
                  ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
                  ((s4.sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
                  ((s4.sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
                  ((s4.sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
                  ((s4.sp + 0x98#64) ↦₆₄ 32#64) ∗
                  segClone_vecBufRest A.repAlloc 104 8 recG.chainsCap recG.chainsPtr
                    ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  ((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
                  m3a2SessionStateRestAt' A.repAlloc coroPtr recG st ∗
                  ((s4.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                  genP3CallFramePlaced A.repAlloc s4.sp remAddrPtr locAddrPtr whisperMsgPtr cur
                    msgVer rest rem loc msgG msg ∗
                  vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
                    recG.localIk.bytes ∗
                  vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
                    recG.remoteIk.bytes ∗
                  vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
                  optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
                  genP3PendSpillScratch s4.sp ∗
                  genP3TailSpillScratch s4.sp ∗
                  ((s4.sp + 0x48#64) ↦₆₄ w.c0) ∗
                  ((s4.sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
                  ((s4.sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
                  ((s4.sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
                  ((s4.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
                  genP3SenderInlineWords s4.sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine rc_loop_placed_budget_ok ext hcc s0 _ _ coroPtr
        (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' fp rcs_tl
        (M.stepEvents (rustAllocEvents ((rcs_tl.length + 1) * 104) 8) stB)
        s4 rc g gs_tl recG.chainsPtr 0#64 _
        hgs_tl hmul_lt' hsz_le hfits_loop hcro4 hpc4 hrun4 hsp4_al htr4
        hx1_4 hx19_4' hx20_4 hx21_4 hx22_4' hx23_4' hx25_4 hx27_4' hx29_4'
        fun s5 gs' hgs'_len hpc5 hrun5 hcro5 hsp5_4 hsp5_al htr5
          hx19_5 hx20_5 hx25_5 hx27_5 hx29_5 hvregs5_4 => ?_
      have hsp5 : s5.sp = sp := hsp5_4.trans hsp4
      rw [hsp4] at hx27_5 ⊢
      rw [hptr_zero, ← hsp5]
      have hepi := rc_epilogue_placed_wp_vm ext s5 hpc5 hrun5 hsp5_al
      refine ret_sepWP_vm_pool_placed (A := A) (lim := lim)
        (st := M.stepEvents (((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents)
          (M.stepEvents (rustAllocEvents ((rcs_tl.length + 1) * 104) 8) stB))
        hcro5 hepi (by sep_focus)
        fun sf _ _ hcrof _ hregsf => ?_
      rcases hregsf with
        ⟨hspf_5, htrf_5, hx19_f, hx23_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregsf_5⟩
      refine ⟨?_, htrf_5.trans htr5, hcrof,
        hvregsf_5.trans (hvregs5_4.trans (hvregs4_3.trans (hvregs3_2.trans (hvregs2_1.trans hvregs1))))⟩
      rw [hsp5, hev_cons, hsz_eq, ← LibsignalBinary.Heap.AllocCostModel.stepEvents_append]
      let w' : GenP3J2Witness :=
        { toGenP3J1Witness := w, newRcPtr := ptr', chains' := gs' }
      refine Entails.sepExists_right w' ?_
      apply Entails.pure_right
        ⟨hspf_5.trans hsp5,
         hx19_f.trans hx19_5,
         by rw [hx23_f, hx20_5, hrc_eq],
         hx25_f.trans hx25_5,
         hx27_f.trans hx27_5,
         hx28_f,
         hx29_f.trans hx29_5,
         by rw [hrc_eq]; exact hgs'_len,
         hsc_rel, hsc_inl⟩
      dsimp only [genP3J2PlacedBudget, w']
      rw [sessionStateAt_coro_placed_eq A.repAlloc coroPtr recG st, hgs_eq, hrc_eq]
      have hzip_src_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs_tl]
      have hzip_dst_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
        simp [hgs'_len]
      rw [hzip_src_len]
      have hsrc_buf := segClone_vecBuf_reassemble_arrayAt A.repAlloc 104 8 (chainAt A.repAlloc)
        recG.chainsCap recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
      have hdst_buf :
          (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
            arrayAt (chainAt A.repAlloc) 104 ptr' (gs'.zip (rc :: rcs_tl))) ⊢
          vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr'
            (gs'.zip (rc :: rcs_tl)) := by
        have h := segClone_vecBuf_chain_of_arrayAt A.repAlloc ptr' (gs'.zip (rc :: rcs_tl))
          (by rw [hzip_dst_len]; exact hn_pos)
          (by rw [hzip_dst_len]; exact hmul_lt)
          hnz3
        rwa [hzip_dst_len, hsz_eq] at h
      refine Entails.trans
        (Q := (arrayAt (chainAt A.repAlloc) 104 recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                segClone_vecBufRest A.repAlloc 104 8 recG.chainsCap recG.chainsPtr
                  ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
              (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
                arrayAt (chainAt A.repAlloc) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
              (((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
                ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
                ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
                m3a2SessionStateRestAt' A.repAlloc coroPtr recG st ∗
                A.pool lim
                  (M.stepEvents
                    (rustAllocEvents ((rcs_tl.length + 1) * 104) 8 ++
                      ((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) stB) sf ∗
                stackAt sp chainCloneStack ∗
                memRegion (sp + 0x3e0#64) 104 ∗
                ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
                  rest rem loc msgG msg ∗
                vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
                  recG.localIk.bytes ∗
                vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
                  recG.remoteIk.bytes ∗
                vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
                optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
                genP3PendSpillScratch sp ∗
                genP3TailSpillScratch sp ∗
                ((sp + 0x48#64) ↦₆₄ w.c0) ∗
                ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
                ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
                ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
                ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
                ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
                ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
                ((sp + 0x98#64) ↦₆₄ 32#64) ∗
                ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
                genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
        (Entails.of_eq (by sep_ac_rfl)) ?_
      refine Entails.trans (sepConj_mono hsrc_buf (sepConj_mono_left hdst_buf)) ?_
      refine Entails.trans
        (Q := ⌜m3a2SessionStatePure recG st⌝ ∗
          (vecBuf A.repAlloc 104 8 (chainAt A.repAlloc) recG.chainsCap recG.chainsPtr
              ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            vecBuf A.repAlloc 104 8 (chainAt A.repAlloc)
              (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' (gs'.zip (rc :: rcs_tl)) ∗
            ((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
            ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
            ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
            m3a2SessionStateRestAt' A.repAlloc coroPtr recG st ∗
            A.pool lim
              (M.stepEvents
                (rustAllocEvents ((rcs_tl.length + 1) * 104) 8 ++
                  ((g :: gs_tl).zip (rc :: rcs_tl)).flatMap chainCloneEvents) stB) sf ∗
            stackAt sp chainCloneStack ∗
            memRegion (sp + 0x3e0#64) 104 ∗
            ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
            genP3CallFramePlaced A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
              rem loc msgG msg ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
              recG.localIk.bytes ∗
            vecU8Buf A.repAlloc (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
              recG.remoteIk.bytes ∗
            vecU8Buf A.repAlloc 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
            optSenderChainHeap A.repAlloc w.sender' st.senderChain ∗
            genP3PendSpillScratch sp ∗
            genP3TailSpillScratch sp ∗
            ((sp + 0x48#64) ↦₆₄ w.c0) ∗
            ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
            ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
            ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
            ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
            ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
            ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
            ((sp + 0x98#64) ↦₆₄ 32#64) ∗
            ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
            genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
        ?_ (by simp only [sepConj_assoc]; exact Entails.of_eq (by sep_ac_rfl))
      apply Entails.pure_right hpure
      exact Entails.of_eq (by sep_ac_rfl)

/-- Envelope-form (`FitsEnv M lim stB (CloneChainsEnv recG st)`) counterpart of
    `cloneChains_vregs_placed_ok_stepEvents`. -/
theorem cloneChains_vregs_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneChainsEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x19b0#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x1a5c#64) s
      (genP3J1PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          CloneChainsEnv recG st evs ∧
          (P_f ⊢ genP3J2PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp := by
  have hstep :=
    cloneChains_vregs_placed_ok_stepEvents (Qp := fun _ _ => False)
      ext hshim halloc hcc s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
      msgVer rest recG st rem loc msgG msg hrc_len hsp_align hsp_root
      (fitsEvents_cloneChains_of_fitsEnv M lim stB recG st hfits)
      hcro hpc hrun htr
  refine sepWPp_bind_frame_any hstep (sepConj_emp _).symm fun s1 P_f hpc1 hrun1 ⟨hent1, htr1, hcro1, hv1⟩ => ?_
  rw [sepConj_emp]
  exact sepWPp_done_any hpc1 hrun1 ⟨cloneChainsEvents recG st, rfl, hent1, htr1, hcro1, hv1⟩

/-- Variant accepting `noAllocShimBudgetSpec` directly. -/
theorem cloneChains_vregs_noAllocShim_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneChainsEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x19b0#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x1a5c#64) s
      (genP3J1PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          CloneChainsEnv recG st evs ∧
          (P_f ⊢ genP3J2PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  cloneChains_vregs_placed_ok ext (sessionShimBudget_of_noAllocShimBudget hshim) halloc hcc
    s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_len hsp_align hsp_root hfits hcro hpc hrun htr

/-- VM-hook entry variant accepting `rustAllocShimVmSpec` directly. -/
theorem cloneChains_vregs_vmHooks_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {stB : M.σ}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) rustAllocShimVmSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hcc : ChainClone3OkPlaced A lim ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hsp_root : rootStack ≤ sp.toNat)
    (hfits : FitsEnv M lim stB (CloneChainsEnv recG st))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x19b0#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x1a5c#64) s
      (genP3J1PlacedBudget A lim stB sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s)
      (fun s1 P_f =>
        ∃ evs : List AllocEvent,
          CloneChainsEnv recG st evs ∧
          (P_f ⊢ genP3J2PlacedBudget A lim (M.stepEvents evs stB)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
            recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧
          LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
      Qp :=
  cloneChains_vregs_placed_ok ext
    (subroutine_ok_sessionShimBudget_of_rustAllocShimVm hshim) halloc hcc
    s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg hrc_len hsp_align hsp_root hfits hcro hpc hrun htr

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudget
