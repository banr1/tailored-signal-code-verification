/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.SpecsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Relocatable Tag-7 (`receiver_chains`) Push Segment (`+0x2310 → +0x2160`)

Total-correctness (`RustCliAllocBudget M`) verification of Segment B of the tag-7
(`receiver_chains`) decode arm on Block `518` (`lsProg_518`) under `[LibsignalPlacement]`,
advancing `A.pool lim st s` along the exact allocation envelope `OverDecRecvSegBEnv`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (maxReceiverChains)
open CryptoVerification (LibsignalPlacement lsmpl withLsCl)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (PanicOomProp)
open CryptoVerification.E2E.Record.DeserializeGeneral (ChainG GenField)
open Symbolic.Swarm.TRREF.B3DeserQ (GenFieldQ SSGQ)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkPl_518 lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec (
  OverDecG OverDecRegsPlaced
  SepWPp_exists_left_rc SepWPp_pure_left_rc
  len_ne_cap_of_lt_rc memRegion104_bf0_join_rc memRegion104_eq_exists_chunks104_6QWAt_rc
  memRegion344_a90_split_rc ofNat_length_eq_cap_of_eq_rc
  overDecStackX overPrevElemRestExt prostChainGAt_move_chunks104_rc
  prostSSGQAt_eq_recv_sep_rest vecAt_recv_open_q_ext vecBuf_recv_full_open_rc_ext
  vecBuf_recv_not_full_open_rc_ext
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget
)
open LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget (
  AllocContractsPlaced growOne104Events growOneChainSpecX growOneChainStackX
  growOneChain_placed_ok_cl growOneChain_placed_ok_x
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushAPlacedBudget (
  growOne_lscl_post_elim_sp_q_ext growOne_lscl_pre_eq_q_ext
  growOne_plain_post_elim_sp_q_ext growOne_plain_pre_eq_q_ext
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  Chain3OverDecG Chain3OverDecRegsPlaced
  OverDecRecvSegBEnv
  SepWPp_bind_sepWP_frame_lscl_pl SepWPp_bind_sepWP_frame_pl
  SepWPp_call_frame_lscl_noPanic_pl SepWPp_call_frame_plain_noPanic_pl
  SepWPp_mono_post_pl SepWPp_weaken_frame_pl
  chain3OverDecStackX chain3OverPrevElemRestExt
  fitsEnv_growOne_of_segB overDecHeapBudget overDecHeapPlBudget
  overDecRecvPostMergeHeapBudget overDecRecvPostMergeHeapPlBudget
  overDecRecvSegBEnv_grow overDecRecvSegBEnv_nil recv2114HeapPlacedBudget
  stackAt_sub_eq_pl step_2310_to_2114_of_ne_placed_budget step_2310_to_growOne_of_eq_placed_budget
  step_234c_to_2114_placed_budget step_from_2114_to_2160_full_lscl_pl_budget
  step_from_2114_to_2160_full_pl_budget toPrevDecG
)

export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  OverDecRecvSegBEnv overDecRecvSegBEnv_nil overDecRecvSegBEnv_grow fitsEnv_growOne_of_segB
  overDecRecvPostMergeHeapPlBudget
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  overDecHeapPlBudget overDecHeapPlBudget_eq_atState
  overDecRecvPostMergeHeapBudget overDecRecvPostMergeHeapBudget_eq_atState
  overDecHeapBudget
)
export LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudgetAux (
  overDecHeapBudget_eq_atState
)

/-! ## Plain `OverDecRecvSegBPlacedBudgetStmt` (`PrevDec.OverDecG`) -/

/-- Budget-threaded Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) of the tag-7 (`receiver_chains`) arm on `lsProg_518 ext` with panic postcondition `Qp`. -/
def OverDecRecvSegBPlacedBudgetStmtGen [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Qp : M.σ → State → State → SepProp → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)) (st : M.σ),
    ∀ (s0 s : State) (g : OverDecG) (v : SSGQ) (c : ChainG) (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    FitsEnv M lim st (OverDecRecvSegBEnv v.base.recv.length) →
    OverDecRegsPlaced ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (lsProg_518 ext) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapPlBudget A lim st s g rest v c)
      (fun sf P_f => ∃ evs : List AllocEvent,
        OverDecRecvSegBEnv v.base.recv.length evs ∧
        OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapPlBudget A lim (M.stepEvents evs st) sf g rest
          (v.apply (.base (.recv c)))))
      (Qp st s0)

abbrev OverDecRecvSegBPlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  OverDecRecvSegBPlacedBudgetStmtGen A lim (fun _ s0 => PanicOomProp s0)

set_option maxHeartbeats 800000 in
/-- Budget-threaded Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) parameterized by `growOneChainSpecX` at `lsmpl.base 43`. -/
theorem overDecRecv_segB_placed_of_grow_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : M.σ → State → State → SepProp → Prop}
    (hGrow : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 43) (growOneChainSpecX M A lim)) :
    OverDecRecvSegBPlacedBudgetStmtGen A lim Qp := by
  intro ext st s0 s g v c rest _hOk hFresh _hsuf _hlen hfit hregs hx0
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, _hCL,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapPlBudget
  rw [prostSSGQAt_eq_recv_sep_rest A.repAlloc (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame_pl (vecAt_recv_open_q_ext A.repAlloc g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame_pl (prostChainGAt_move_chunks104_rc A.repAlloc (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame_pl
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame_pl (vecBuf_recv_full_open_rc_ext A.repAlloc cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    simp only [A.repAlloc_live_norm]
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    have hfit_grow : FitsEnv M lim st (LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.GrowOne104Env cap) :=
      fitsEnv_growOne_of_segB hfull hfit
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed_budget A lim st ext s g cap
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_pl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 _hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_plain_noPanic_pl
      (x := ((g.q + 0x978#64, cap, ptr, bs), st))
      (hGrow ext) hpcs1 hruns1 hals1 hlrs1
      (growOne_plain_pre_eq_q_ext A lim st g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt, hfit_grow⟩
      (by sep_focus)
      (by intro sf; rfl)
      (by intro _ _; rfl)
      ?_
    intro sm hpcm hrunm hspm _halm hcsm _hCLm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame_pl
      (growOne_plain_post_elim_sp_q_ext A lim st g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame_pl (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed_budget A lim (M.stepEvents (growOne104Events cap) st) ext sm g cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame_pl hstep2 (by sep_focus)
      fun s2 hpcs2 hruns2 hCLs2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hCLs2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlacedBudget A lim
        (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
        s2 g rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · unfold recv2114HeapPlacedBudget
      rw [stackAt_sub_eq_pl g.q overDecStackX growOneChainStackX]
      sep_ac_rfl
    · rw [sepConj_emp]
      refine SepWPp_mono_post_pl ?_
        (step_from_2114_to_2160_full_pl_budget A lim
          (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st)
          ext s0 s2 g v c rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c
          hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2)
      rintro sf P_f ⟨hregsf, hentf⟩
      exact ⟨growOne104Events (BitVec.ofNat 64 v.base.recv.length), Or.inr rfl, hregsf, hentf⟩
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A.repAlloc cap ptr v.base.recv hlt hcap_lt]
    simp only [A.repAlloc_live_norm]
    have hstep1 := step_2310_to_2114_of_ne_placed_budget A lim st ext s g cap (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_pl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hCLs1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hCLs1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlacedBudget A lim st s1 g rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by unfold recv2114HeapPlacedBudget; sep_ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    refine SepWPp_mono_post_pl ?_
      (step_from_2114_to_2160_full_pl_budget A lim st ext s0 s1 g v c rest cap ptr
        q0 q1 q2 q3 q4 q5 w6 H_c hlt hcap_lt hptr hmov_c hregs1 hx22s1)
    rintro sf P_f ⟨hregsf, hentf⟩
    exact ⟨[], overDecRecvSegBEnv_nil v.base.recv.length, hregsf, hentf⟩

theorem overDecRecv_segB_placed_of_grow [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hGrow : ∀ ext, subroutine_ok (lsProg_518 ext) (lsmpl.base 43) (growOneChainSpecX M A lim)) :
    OverDecRecvSegBPlacedBudgetStmt A lim :=
  overDecRecv_segB_placed_of_grow_gen hGrow

/-! ## `LibsignalCodeLoaded`-Backed `OverDecRecvSegBLsclPlacedBudgetStmt` (`VerNe.Chain3.OverDecG`) -/

/-- `LibsignalCodeLoaded`-backed Segment B (`(blkPl_518).base + 0x2310 → +0x2160`) on `lsProg_518 (Rust.withPanics ext)` under `GrowOneXBudget.AllocContractsPlaced`. -/
def OverDecRecvSegBLsclPlacedBudgetStmtGen [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Qp : M.σ → State → State → SepProp → Prop) : Prop :=
  ∀ (ext : String → Option (State → State)),
    AllocContractsPlaced M A lim (Rust.withPanics ext) →
    ∀ (st : M.σ) (s0 s : State) (g : Chain3OverDecG) (v : SSGQ) (c : ChainG)
      (rest : List (BitVec 8)),
    (GenFieldQ.base (.recv c)).Ok →
    (GenFieldQ.base (.recv c)).Fresh v →
    ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc →
    g.enc.length < 2 ^ 62 →
    FitsEnv M lim st (OverDecRecvSegBEnv v.base.recv.length) →
    Chain3OverDecRegsPlaced ext s0 g 0x2310#64 s →
    s.readReg64 .x0 = 0#64 →
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapBudget A lim st s g rest v c)
      (fun sf P_f => ∃ evs : List AllocEvent,
        OverDecRecvSegBEnv v.base.recv.length evs ∧
        Chain3OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest
          (v.apply (.base (.recv c)))))
      (Qp st s0)

abbrev OverDecRecvSegBLsclPlacedBudgetStmt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) : Prop :=
  OverDecRecvSegBLsclPlacedBudgetStmtGen A lim (fun _ s0 => PanicOomProp s0)

set_option maxHeartbeats 800000 in
/-- `LibsignalCodeLoaded` Segment B (`+0x2310 → +0x2160`) parameterized by `withLsCl lsmpl (growOneChainSpecX M A lim)`. -/
theorem overDecRecv_segB_lscl_ok_of_grow_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hGrow : subroutine_ok (lsProg_518 (Rust.withPanics ext)) (lsmpl.base 43)
      (withLsCl lsmpl (growOneChainSpecX M A lim)))
    (st : M.σ) (s0 s : State) (g : Chain3OverDecG) (v : SSGQ) (c : ChainG)
    (rest : List (BitVec 8))
    (_hOk : (GenFieldQ.base (.recv c)).Ok)
    (hFresh : (GenFieldQ.base (.recv c)).Fresh v)
    (_hsuf : ((GenFieldQ.base (.recv c)).enc ++ rest) <:+ g.enc)
    (_hlen : g.enc.length < 2 ^ 62)
    (hfit : FitsEnv M lim st (OverDecRecvSegBEnv v.base.recv.length))
    (hregs : Chain3OverDecRegsPlaced ext s0 g 0x2310#64 s)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x2160#64) s
      (overDecRecvPostMergeHeapBudget A lim st s g rest v c)
      (fun sf P_f => ∃ evs : List AllocEvent,
        OverDecRecvSegBEnv v.base.recv.length evs ∧
        Chain3OverDecRegsPlaced ext s0 g 0x2160#64 sf ∧
        (P_f ⊢ overDecHeapBudget A lim (M.stepEvents evs st) sf g rest
          (v.apply (.base (.recv c)))))
      Qp := by
  have hfresh : v.base.recv.length < maxReceiverChains := hFresh.2
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hcl,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  unfold overDecRecvPostMergeHeapBudget
  rw [prostSSGQAt_eq_recv_sep_rest A.repAlloc (g.q + 0x930#64) v,
      memRegion344_a90_split_rc g.q]
  refine SepWPp_weaken_frame_pl (vecAt_recv_open_q_ext A.repAlloc g.q v.base.recv)
    (by sep_focus) ?_
  apply SepWPp_exists_left_rc; intro cap
  apply SepWPp_exists_left_rc; intro ptr
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; rintro ⟨hlen_le, hcap_lt, hptr⟩
  refine SepWPp_weaken_frame_pl (prostChainGAt_move_chunks104_rc A.repAlloc (g.q + 0xbf0#64) c)
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i q0 q1 q2 q3 q4 q5 w6 H_c
  rw [sepConj_assoc]
  apply SepWPp_pure_left_rc; intro hmov_c
  refine SepWPp_weaken_frame_pl
    (Entails.of_eq (memRegion104_eq_exists_chunks104_6QWAt_rc (g.q + 0xa90#64)))
    (by sep_focus) ?_
  repeat' (apply SepWPp_exists_left_rc; intro _)
  rename_i d0 d1 d2 d3 d4 d5 dw6
  by_cases hfull : v.base.recv.length = cap.toNat
  · refine SepWPp_weaken_frame_pl (vecBuf_recv_full_open_rc_ext A.repAlloc cap ptr v.base.recv hfull)
      (by sep_focus) ?_
    apply SepWPp_exists_left_rc; intro bs
    apply SepWPp_exists_left_rc; intro H_arr
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hbs_len, hmov_arr⟩
    simp only [A.repAlloc_live_norm]
    have hlen_cap : BitVec.ofNat 64 v.base.recv.length = cap := ofNat_length_eq_cap_of_eq_rc hfull
    have hmax_lt : 8 + max (2 * cap.toNat) 4 * 104 ≤ 2 ^ 63 := by
      have h5 : maxReceiverChains = 5 := rfl
      omega
    have hfit_grow : FitsEnv M lim st (LibsignalBinary.Proofs.SessionRecordAt.Stage1X.GrowOneXBudget.GrowOne104Env cap) :=
      fitsEnv_growOne_of_segB hfull hfit
    rw [hlen_cap]
    have hstep1 := step_2310_to_growOne_of_eq_placed_budget A lim st (Rust.withPanics ext)
      s (toPrevDecG g) cap q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_lscl_pl hcl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hcls1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx0s1, hlrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    dsimp only [toPrevDecG] at hsps1 hx0s1 hx19s1 hx20s1 hx21s1 hx26s1 hx27s1 hx28s1 hx29s1
    have hals1 : s1.spAligned = true := by
      simp only [State.spAligned]
      rwa [hsps1, ← hsp]
    rw [stackAt_sub_eq_pl g.q chain3OverDecStackX growOneChainStackX]
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_call_frame_lscl_noPanic_pl
      (x := ((g.q + 0x978#64, cap, ptr, bs), st))
      hcls1 hGrow hpcs1 hruns1 hals1 hlrs1
      (growOne_lscl_pre_eq_q_ext A lim st g.q cap ptr bs s1 hsps1)
      ⟨hbs_len, hx0s1, hptr, hmax_lt, hfit_grow⟩
      (by sep_focus)
      (by intro sf; rfl)
      (by intro _ _; rfl)
      ?_
    intro sm hpcm hrunm hspm _halm hcsm hclm
    obtain ⟨hx19m, hx20m, hx21m, hx22m, _, hx24m, hx25m, hx26m, hx27m, hx28m, hfpm, hvregsm⟩ := hcsm
    rw [hx19s1] at hx19m; rw [hx20s1] at hx20m; rw [hx21s1] at hx21m; rw [hx22s1] at hx22m
    rw [hx24s1] at hx24m; rw [hx25s1] at hx25m; rw [hx26s1] at hx26m; rw [hx27s1] at hx27m
    rw [hx28s1] at hx28m; rw [hx29s1] at hfpm; rw [hsps1] at hspm
    refine SepWPp_weaken_frame_pl
      (growOne_lscl_post_elim_sp_q_ext A lim st g.q cap ptr v.base.recv bs s1 sm hsps1 hfull hfresh hbs_len)
      rfl ?_
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro _hclm'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; intro htrm
    have htrm' : sm.trace = s0.trace := htrm.trans (htrs1.trans htr)
    apply SepWPp_exists_left_rc; intro cap'
    apply SepWPp_exists_left_rc; intro p'
    rw [sepConj_assoc]
    apply SepWPp_pure_left_rc; rintro ⟨hlt_cap', hcap_lt', hp'⟩
    refine SepWPp_weaken_frame_pl (hmov_arr p') (by sep_focus) ?_
    have hstep2 := step_234c_to_2114_placed_budget A lim (M.stepEvents (growOne104Events cap) st)
      (Rust.withPanics ext) sm (toPrevDecG g) cap
      hpcm hrunm hspm hx19m hx20m hx21m hx22m hx24m hx25m hx26m hx27m hx28m hfpm
    refine SepWPp_bind_sepWP_frame_lscl_pl hclm hstep2 (by sep_focus)
      fun s2 hpcs2 hruns2 hcls2 hpost2 => ?_
    rcases hpost2 with ⟨hsps2, htrs2, hx19s2, hx20s2, hx21s2, hx22s2,
      hx24s2, hx25s2, hx26s2, hx27s2, hx28s2, hx29s2, hvregss2⟩
    dsimp only [toPrevDecG] at hsps2 hx19s2 hx20s2 hx21s2 hx26s2 hx27s2 hx28s2 hx29s2
    have hals2 : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsps2, ← hsp]
    rw [← hlen_cap] at hx22s2 ⊢
    have hregs2 : Chain3OverDecRegsPlaced ext s0 g 0x2114#64 s2 :=
      ⟨hpcs2, hruns2, hsps2, hals2, htrs2.trans htrm', hcls2,
       hx19s2, hx20s2, hx26s2, hx21s2, hx24s2, hx25s2, hx27s2, hx28s2, hx29s2,
       ((hvregss2.trans hvregsm).trans hvregss1).trans hvregs⟩
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlacedBudget A lim
        (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st) s2
        (toPrevDecG g) rest v cap' p' q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq ?_) (sepConj_emp _).symm ?_
    · simp only [recv2114HeapPlacedBudget, overPrevElemRestExt,
        chain3OverPrevElemRestExt, overDecStackX, chain3OverDecStackX,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overPrevElemRestExt,
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecStackX,
        A.repAlloc_live_norm]
      rw [stackAt_sub_eq_pl g.q 65536 growOneChainStackX]
      sep_ac_rfl
    · rw [sepConj_emp]
      refine SepWPp_mono_post_pl ?_
        (step_from_2114_to_2160_full_lscl_pl_budget A lim
          (M.stepEvents (growOne104Events (BitVec.ofNat 64 v.base.recv.length)) st) ext s0 s2 g v c
          rest cap' p' q0 q1 q2 q3 q4 q5 w6 H_c hlt_cap' hcap_lt' hp' hmov_c hregs2 hx22s2)
      rintro sf P_f ⟨hregsf, hentf⟩
      exact ⟨growOne104Events (BitVec.ofNat 64 v.base.recv.length), Or.inr rfl, hregsf, hentf⟩
  · have hlt : v.base.recv.length < cap.toNat := by omega
    have hne : BitVec.ofNat 64 v.base.recv.length ≠ cap := len_ne_cap_of_lt_rc hlt
    rw [vecBuf_recv_not_full_open_rc_ext A.repAlloc cap ptr v.base.recv hlt hcap_lt]
    simp only [A.repAlloc_live_norm]
    have hstep1 := step_2310_to_2114_of_ne_placed_budget A lim st (Rust.withPanics ext)
      s (toPrevDecG g) cap (BitVec.ofNat 64 v.base.recv.length)
      q0 q1 q2 q3 q4 q5 d0 d1 d2 d3 d4 d5 w6 dw6
      hne hpc hrun hsp hal hx0 hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
    refine SepWPp_bind_sepWP_frame_lscl_pl hcl hstep1 (by sep_focus)
      fun s1 hpcs1 hruns1 hcls1 hpost1 => ?_
    rcases hpost1 with ⟨hsps1, htrs1, hx19s1, hx20s1, hx21s1, hx22s1,
      hx24s1, hx25s1, hx26s1, hx27s1, hx28s1, hx29s1, hvregss1⟩
    dsimp only [toPrevDecG] at hsps1 hx19s1 hx20s1 hx21s1 hx26s1 hx27s1 hx28s1 hx29s1
    have hals1 : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsps1, ← hsp]
    have hregs1 : Chain3OverDecRegsPlaced ext s0 g 0x2114#64 s1 :=
      ⟨hpcs1, hruns1, hsps1, hals1, htrs1.trans htr, hcls1,
       hx19s1, hx20s1, hx26s1, hx21s1, hx24s1, hx25s1, hx27s1, hx28s1, hx29s1,
       hvregss1.trans hvregs⟩
    refine SepWPp_weaken_frame_pl (memRegion104_bf0_join_rc g.q q0 q1 q2 q3 q4 q5 w6)
      (by sep_focus) ?_
    refine SepWPp_weaken_frame_pl
      (P₂ := recv2114HeapPlacedBudget A lim st s1 (toPrevDecG g) rest v cap ptr q0 q1 q2 q3 q4 q5 w6 H_c)
      (Entails.of_eq (by
        simp only [recv2114HeapPlacedBudget, overPrevElemRestExt,
          chain3OverPrevElemRestExt, overDecStackX, chain3OverDecStackX,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overPrevElemRestExt,
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.overDecStackX,
          A.repAlloc_live_norm]
        sep_ac_rfl))
      (sepConj_emp _).symm ?_
    rw [sepConj_emp]
    refine SepWPp_mono_post_pl ?_
      (step_from_2114_to_2160_full_lscl_pl_budget A lim st ext s0 s1 g v c rest cap ptr
        q0 q1 q2 q3 q4 q5 w6 H_c hlt hcap_lt hptr hmov_c hregs1 hx22s1)
    rintro sf P_f ⟨hregsf, hentf⟩
    exact ⟨[], overDecRecvSegBEnv_nil v.base.recv.length, hregsf, hentf⟩

theorem overDecRecv_segB_lscl_ok_gen [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : M.σ → State → State → SepProp → Prop} :
    OverDecRecvSegBLsclPlacedBudgetStmtGen A lim Qp :=
  fun ext hAlloc st s0 s g v c rest hOk hFresh hsuf hlen hfit hregs hx0 =>
    overDecRecv_segB_lscl_ok_of_grow_gen ext
      (growOneChain_placed_ok_cl (growOneChain_placed_ok_x hAlloc))
      st s0 s g v c rest hOk hFresh hsuf hlen hfit hregs hx0

theorem overDecRecv_segB_lscl_ok_ext [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} :
    OverDecRecvSegBLsclPlacedBudgetStmt A lim :=
  overDecRecv_segB_lscl_ok_gen

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvPushPlacedBudget
