/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlaced
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp

/-!
# Spatial Bundles and Substage P3.5 `Ok` Core for `Matched.M3PrevCapPlacedBudget`

Budget-threaded spatial bundles (`A.atState`), Block-`518` pool-synchronizing basic-block steppers,
and Substage P3.5 `Ok` path proofs (`stageP3_sub5_placed_ok`, `stageP3_sub5_decResult_placed_ok`)
for `Matched.M3PrevCapPlacedBudget`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsMemcpySym lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost protocolAddressAt sessionStateAt signalMessageAt
  vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  rootStack sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  SetSessionStateGhost growOneSpeStack lsLogOff setSessionStateStack
)
open CryptoVerification.LibsignalTripleRatchet.RawByteMove (
  SessionInline sessionStateAt_eq_inline_sep_heap sessionStateAt_move_bytes_twice
)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (decResultAt_ok_unpack eq_of_sep_emp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  genP3SpillAll genP3SpillAll_entails_s5 memRegion344_104_240_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  LsTokenInitM3 dpClosureEntryM3Placed prevSessionsEmptyAt stageP3Sub5ExtraPrePrevEmpty
)
open CryptoVerification.CliHandshake.RespClosurePlaced (blkLib_eq_518 blkPl_518 lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsBPlacedBudget (
  blkLib_518_noSvc0
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (setSessionStateSpec)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero
attribute [local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg

local macro "wp_steps_sync_518 " ext:term:max mid:term : tactic => `(tactic| (
  apply sepWP_seg_ls_vm (Q := lsProg_518 (hooksException $ext))
    blkLib_eq_518 blkLib_518_noSvc0 (mid := $mid)
  intro _m_strip
  wp_steps
  refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs) fun _m_real _hnsp => ?_
  refine ProofLib.SepWP.transport_budgetPool
    (_hnsp.toVmPreserved (by first | wp_norm_lhs | simp only [wp_norm, arm64_norm]))
    (hnext := ?_)
))

/-! ## Budget-threaded spatial bundles -/

def stageP3DispatchPrePrevEmptyPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s_pool : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchPrePrevEmptyPlaced
    (A.atState lim st_b s_pool) s0 s coroPtr outPtr initErrsPtr g res b_2c0 G₂ recG st₂ recSt

def stageP3DispatchOkMidPrevEmptyPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr ptCap ptPtr : BitVec 64) (g : RecordGhost)
    (pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchOkMidPrevEmptyPlaced
    (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G₂ st₂

def genP3S5PostFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (msgVer : BitVec 32)
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
    A.repAlloc sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer rem loc msgG msg
    coinsPost

def genP3CallFramePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (sp remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (rem loc : AddrGhost)
    (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3CallFramePlaced
    A.repAlloc sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc msgG msg

def genP3PrePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PrePlaced
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg s

def genP3PostSpatialPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s_pool : State)
    (sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    (A.atState lim st_b s_pool) sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg

def genP3PostEqPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg s

def genP3PostNePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg s

def genP3PostPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) (s : State) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced
    (A.atState lim st_b s) sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
    recG st rem loc msgG msg s

def stageP3ErrPrePrevEmptyM3Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s_pool : State)
    (coroPtr outPtr initErrsPtr : BitVec 64) (g : RecordGhost)
    (e : SignalProtocolError) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
    (A.atState lim st_b s_pool) s0 s coroPtr outPtr initErrsPtr g e b_2c0 G₂ recG st₂ recSt

def stageP3ErrPostPrevEmptyM3Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s sf : State)
    (coroPtr outPtr : BitVec 64) (e : SignalProtocolError) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
    (A.atState lim st_b sf) s0 s coroPtr outPtr e

theorem postTryDecrypt_entails_s5DispatchPrevEmpty_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (s0 s s_pool : State)
    (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (g : RecordGhost) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) :
    (LsTokenInitM3 ∗
      sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A.repAlloc (s.sp + 0x270#64) res ∗
      protocolAddressAt A.repAlloc rem remAddrPtr ∗
      protocolAddressAt A.repAlloc loc locAddrPtr ∗
      signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
      coinsPost ∗
      lsLogOff ∗
      stackAt s.sp rootStack ∗
      A.pool lim st_b s_pool) ∗
    (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0) ⊢
    stageP3DispatchPrePrevEmptyPlaced A lim st_b s0 s s_pool coroPtr outPtr initErrsPtr g
      res b_2c0 G' recG st₂ st ∗
    genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.postTryDecrypt_entails_s5DispatchPrevEmpty_placed
    (A := A.atState lim st_b s_pool) s0 s coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr
    whisperMsgPtr g msgVer b_2c0 res G' recG st₂ st rem loc msgG msg coinsPost

/-! ## `SepWPp` sequencing and framing combinators -/

theorem sepWPp_weaken_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P P₁ P₂ F : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P₁ ⊢ P₂) (hP : P = P₁ ∗ F)
    (hwp : SepWPp prog ret s (P₂ ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.weaken_pre (hP ▸ sepConj_mono_left hent) hwp

theorem sepWPp_lift_false_qp {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q (fun _ _ => False)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sf, hsteps, hok | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ := h R hm hL
  · exact ⟨sf, hsteps, Or.inl hok⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem sepWPp_frame_false_qp {prog : Program} {ret : BitVec 64} {s : State}
    {P F_frame : SepProp} {Q : State → SepProp → Prop}
    (hwp : SepWPp prog ret s P (fun sf P_f => Q sf (P_f ∗ F_frame)) (fun _ _ => False)) :
    SepWPp prog ret s (P ∗ F_frame) Q (fun _ _ => False) := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_f, hmf, hQ⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ :=
    hwp (F_frame ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_f ∗ F_frame, hmf, hQ⟩⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem ret_sepWPp_frame_false {prog : Program} {ret : BitVec 64} {s : State}
    {P P_stage F : SepProp} {Q_stage Q : State → SepProp → Prop}
    (hstage : SepWPp prog ret s P_stage Q_stage (fun _ _ => False))
    (hP : P = P_stage ∗ F)
    (hret : ∀ sf P_m, sf.pc = ret → sf.status = .Running → Q_stage sf P_m → Q sf (P_m ∗ F)) :
    SepWPp prog ret s P Q (fun _ _ => False) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sf, hsteps, ⟨hpc, hrun, P_m, hmf, hQ⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hmf
    exact ⟨sf, hsteps, Or.inl ⟨hpc, hrun, P_m ∗ F, hmf, hret sf P_m hpc hrun hQ⟩⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem bind_sepWPp_false_steps_framed {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_stage F F_frame : SepProp} {Q_mid Q Qp : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage Q_mid (fun _ _ => False)) (hP : P = P_stage ∗ F)
    (hnext : ∀ sm P_m, Steps prog s sm → sm.pc = mid → sm.status = .Running → Q_mid sm P_m →
      SepWPp prog ret sm ((P_m ∗ F) ∗ F_frame) Q Qp) :
    SepWPp prog ret s (P ∗ F_frame) Q Qp := by
  intro R hm hL
  have hm0 : s.mem ⊨ P_stage ∗ ((F ∗ F_frame) ∗ R) := by
    rw [hP] at hm; simpa only [sepConj_assoc] using hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hqm⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ :=
    hstage ((F ∗ F_frame) ∗ R) hm0 hL
  · have hmm' : sm.mem ⊨ ((P_m ∗ F) ∗ F_frame) ∗ R := by simpa only [sepConj_assoc] using hmm
    obtain ⟨sf, hsteps', hout'⟩ := hnext sm P_m hsteps hpcm hrunm hqm R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem bind_sepWP_lscro_steps_m3_placed [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim hoom | exact (not_satisfies_false_sepConj hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post sm ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hsteps hpc hrun (hcro.of_keepsFrozen hsteps.keepsFrozen)
      hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

theorem call_lscl_nopanic_m3 [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_false : ∀ sf, spec.onPanic x s sf = ⌜False⌝ := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, Steps prog s sf → sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intro _; rfl) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, _⟩ := hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hoom_post⟩
  rotate_right
  · dsimp only [withLsCodeLoaded] at hoom_post
    rw [hoom_false] at hoom_post
    exact (not_satisfies_false_sepConj hoom_post).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hspm hsp_alm hcsm (hcro.of_keepsFrozen hsteps.keepsFrozen)
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hpan_false] at hpost
    exact (allowPanic_not_exited hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## Block-`518` pool-synchronizing basic-block steppers -/

/-- Pool-threaded `dpClosureEntryM3Placed + 0x1cd4 → lsmpl.base 508` under `[LibsignalPlacement]`. -/
theorem p3_bl_tryDecrypt_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd4#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_518 ext) (lsmpl.base 508) s (A.pool lim st_b s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st_b s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧
        s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x1cd8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext (lsmpl.base 508)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (sepConj_emp _), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Pool-threaded `dpClosureEntryM3Placed + 0x1dfc → +0x34dc` under `[LibsignalPlacement]`. -/
theorem p3_seg7b_x24_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1dfc#64) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s (A.pool lim st_b s)
      (fun s1 P_f =>
        (P_f ⊢ A.pool lim st_b s1) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  wp_steps_sync_518 ext ((blkPl_518).base + 0x34dc#64)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨Entails.of_eq (sepConj_emp _), rfl, rfl, by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

/-- Pool-threaded `dpClosureEntryM3Placed + 0x1cd8 → lsmpl.base 48` across `memcpy` under
`[LibsignalPlacement]`. -/
theorem p3_seg7a_x24_placed_wp [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (ext : String → Option (State → State))
    (hmemcpy_in : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (s : State) (coroPtr retPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (lsProg_518 ext) (lsmpl.base 48) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ lsLogOff ∗
       ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗ A.pool lim st_b s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ lsLogOff ∗
          ((s.sp + 0xa90#64) ↦ₛ ssBytes) ∗ ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗ A.pool lim st_b s1) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = retPtr ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧ s1.readReg64 .x30 = dpClosureEntryM3Placed + 0x1dfc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hmemcpy := hmemcpy_in
  dsimp only [dpClosureEntryM3Placed, lsLogOff, lsLogFilterAddr, lsMemcpySym,
    sessionMemcpyRegionBudgetSpec, withVmPreserved, sessionMemcpyRegionSpec,
    memcpyRegionSpec] at hmemcpy hpc ⊢
  rw [← hss_len]
  wp_steps_sync_518 ext (lsρ "memcpy")
  simp only [State.setMem_setMem]
  wp_call hmemcpy (s.sp + 0x3e0#64, s.sp + 0xa90#64, ssBytes)
  refine SepWP.transport_budgetPool ‹VmPreserved _ sf› (hnext := ?_)
  wp_steps_sync_518 ext (lsmpl.base 48)
  simp only [State.setMem_setMem]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨Entails.of_eq (by sep_ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
     by simp_all [arm64_norm]⟩

/-! ## Budget-threaded Substage P3.5 `Ok` path (`+0x1cd8 → +0x34dc`) -/

/-- Budget-threaded `[LibsignalPlacement]` Substage P3.5 `Ok` core
(`dpClosureEntryM3Placed + 0x1cd8 → +0x34dc`), advancing `A.pool` by `FreeOnlyEvs`. -/
theorem stageP3_sub5_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hSetState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ lsLogOff ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st_b s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ lsLogOff ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
            memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧ sf.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  rw [sessionStateAt_eq_inline_sep_heap A.repAlloc (s.sp + 0xa90#64) G₂ st₂]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun bs => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (P₂ := ⌜bs.length = 344 ∧ SessionInline G₂ st₂ bs⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hbs_len, hinl⟩ => ?_
  have hstep1 := p3_seg7a_x24_placed_wp A lim st_b ext hmemcpy s coroPtr retPtr bs
    hbs_len hpc hrun hsp_align hx19
  refine bind_sepWP_lscro_steps_m3_placed hcro hstep1 (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx19_1, hx24_1, hx25_1, hx26_1, hx27_1,
    hx29_1, hx30_1, hvregs_1⟩
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  refine call_lscl_nopanic_m3
    (x := ((⟨coroPtr + 0xe0#64, s.sp + 0x3e0#64, some (recG, recSt), bs⟩ : SetSessionStateGhost), st_b))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xe0#64 + 0x18#64) recG recSt ∗
          ((s.sp + 0x3e0#64) ↦ₛ bs) ∗ A.pool lim st_b s1 ∗ stackAt s.sp setSessionStateStack)
    hcro1 hSetState hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [setSessionStateSpec]; rw [hsp1_s])
    (And.intro hx0_1 (And.intro hx1_1 hbs_len))
    (by have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
        rw [h18]; sep_focus)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 _ hcs2 hcro2 => ?_)
  dsimp only [setSessionStateSpec]
  rw [hsp1_s]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun evs => ?_
  refine SepWPp.pure_elim fun ⟨htr2_1, hevs_free, _⟩ => ?_
  have h18 : coroPtr + 0xe0#64 + 0x18#64 = coroPtr + 0xf8#64 := by bv_omega
  rw [h18]
  refine sepWPp_weaken_frame
    (sessionStateAt_move_bytes_twice A.repAlloc (s.sp + 0xa90#64) (s.sp + 0x3e0#64)
      (coroPtr + 0xf8#64) G₂ st₂ hinl)
    (by sep_focus) ?_
  have hsp2_s : s2.sp = s.sp := hsp2_1.trans hsp1_s
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, hx25_cs2, hx26_cs2, hx27_cs2, _, hx29_cs2,
    hvregs_cs2⟩
  have hstep3 := p3_seg7b_x24_placed_wp A lim (M.stepEvents evs st_b) ext s2 coroPtr hpc2 hrun2
    (hx19_cs2.trans hx19_1)
  refine bind_sepWP_lscro_steps_m3_placed hcro2 hstep3 (by sep_focus)
    fun sf _ hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_2, htrf_2, hx19_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
    hvregs_f⟩
  exact SepWPp.done hpcf hrunf ⟨evs, hevs_free,
    Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_2.trans hsp2_s, htrf_2.trans (htr2_1.trans (htr1_s.trans htr)), hcrof, hx19_f,
    hx24_f.trans (hx24_cs2.trans hx24_1), hx25_f.trans (hx25_cs2.trans hx25_1),
    hx26_f.trans (hx26_cs2.trans hx26_1), hx27_f.trans (hx27_cs2.trans hx27_1),
    hx28_f, hx29_f.trans (hx29_cs2.trans hx29_1), hvregs_f.trans (hvregs_cs2.trans hvregs_1)⟩

/-- Budget-threaded `[LibsignalPlacement]` Substage P3.5 `vecResultAt (.ok pt)`
(`+0x1cd8 → +0x34dc`). -/
theorem stageP3_sub5_decResult_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hSetState : subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (st_b : M.σ) (s0 s : State) (coroPtr retPtr : BitVec 64)
    (pt : List (BitVec 8)) (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1cd8#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x34dc#64) s
      (((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
       vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) ∗ lsLogOff ∗
       sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₂ st₂ ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
       sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗
       A.pool lim st_b s ∗ stackAt s.sp setSessionStateStack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent, ∃ ptCap ptPtr : BitVec 64,
          FreeOnlyEvs evs ∧
          pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64 ∧
          (P_f ⊢ ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ retPtr) ∗
            ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗ ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
            ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
            memRegion (s.sp + 0x290#64) 16 ∗ (ptPtr ↦ₛ pt) ∗
            (if ptCap = 0#64 then emp
             else A.live ptPtr ptCap.toNat 1 ∗
               memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
            lsLogOff ∗ sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G₂ st₂ ∗
            memRegion (s.sp + 0x3e0#64) 344 ∗ memRegion (s.sp + 0xa90#64) 344 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp setSessionStateStack) ∧
          sf.sp = s.sp ∧ sf.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl sf.mem ∧
          sf.readReg64 .x19 = coroPtr ∧ sf.readReg64 .x24 = s.readReg64 .x24 ∧
          sf.readReg64 .x25 = s.sp + 0x210#64 ∧ sf.readReg64 .x26 = retPtr ∧
          sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x28 = 0xfffffffffffffffe#64 ∧
          sf.readReg64 .x29 = s.readReg64 .x29 ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      (fun _ _ => False) := by
  refine sepWPp_weaken_frame (decResultAt_ok_unpack A.repAlloc (s.sp + 0x270#64) pt)
    (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun ptCap => SepWPp.exists_elim fun ptPtr => ?_
  refine sepWPp_weaken_frame
    (P₁ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (P₂ := ⌜pt.length ≤ ptCap.toNat ∧ ptCap.toNat < 2 ^ 63 ∧ ptPtr ≠ 0#64⌝)
    (Entails.refl _) (by sep_focus) ?_
  refine SepWPp.pure_elim fun ⟨hpt_le, hpt_lt, hpt_ne⟩ => ?_
  have hsub := stageP3_sub5_placed_ok ext hmemcpy hSetState st_b s0 s coroPtr retPtr G₂ recG
    st₂ recSt hcro hpc hrun hsp_align htr hx19
  refine ret_sepWPp_frame_false hsub (by sep_focus)
    fun sf _ _ _ ⟨evs, hevs_free, hPf, hspf, htrf, hcrof, hx19f, hx24f, hx25f, hx26f, hx27f,
      hx28f, hx29f, hvregsf⟩ => ?_
  refine ⟨evs, ptCap, ptPtr, hevs_free, hpt_le, hpt_lt, hpt_ne, ?_,
    hspf, htrf, hcrof, hx19f, hx24f, hx25f, hx26f, hx27f, hx28f, hx29f, hvregsf⟩
  have hlive_eq :
      (if ptCap = 0#64 then emp
       else A.repAlloc.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
  rw [hlive_eq]
  exact Entails.trans (sepConj_mono_left hPf) (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux
