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
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget
import LibsignalBinary.Proofs.TripleRatchet.Hooks.Defs
import LibsignalBinary.Proofs.TripleRatchet.Record.SegMismatch
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable Stage P3 over General `prevSessionsEmptyAt`

Budget-threaded `[LibsignalPlacement]` and `[LibsignalFullPlacement]` Stage P3 over general
`prevSessionsEmptyAt A.repAlloc coroPtr g` on Block `518` (`lsProg_518 ext`), proving
`stageP3Gen_prevEmpty_vregs_placed_ok_of_parts` and `stageP3Gen_prevEmpty_vregs_full_placed_ok_of_parts`
under `StageP3M3Env`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (Crypto SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement lsHandleErrorSym lsMemcpySym lsRustAllocSym lsRustDeallocSym
  lsRustNoAllocShimSym lsRustReallocSym lsmpl lsρ ls_subroutine_ok_of_block withLsCodeLoaded
)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost UuidParser decryptDraws protocolAddressAt
  sessionStateAt signalMessageAt uuidTryParse vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SeedsLen32 SpqrModel TryDecryptGhost rootStack sessionMemcpyRegionSpec
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  growOneSpeStack lsLogOff setSessionStateStack
)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (stackAt_root_split_grow)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.SignalSession.Coins (coinsAfterPlaced coinsAtPlaced)
open CryptoVerification.E2E.Pqxdh.WireEntries (DistinctSid)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (ClosureCalleeSaved decryptPrekeySavedRegsAt)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (eq_of_sep_emp)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (
  genP3S5Model genP3S5ModelPanicProp genP3SpillAll genP3SpillAll_entails_s5
  memRegion344_104_240_eq
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  LsTokenInitM3 cloneExitPCPlaced dpClosureEntryM3Placed prevSessionsEmptyAt
  stageP3Sub5ExtraPrePrevEmpty
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget SeqEnv
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget (
  ChainClone3OkPlaced SenderChainClone3OkPlaced
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWP_lscro_steps_m3_placed bind_sepWPp_false_steps_framed
  genP3PostEqPlaced genP3PostNePlaced genP3PostPlaced genP3PostSpatialPlaced genP3PrePlaced
  genP3S5PostFramePlaced p3_bl_tryDecrypt_placed_wp postTryDecrypt_entails_s5DispatchPrevEmpty_placed
  ret_sepWPp_frame_false sepWPp_frame_false_qp sepWPp_lift_false_qp sepWPp_weaken_frame
  stageP3DispatchOkMidPrevEmptyPlaced stageP3DispatchPrePrevEmptyPlaced
  stageP3ErrPostPrevEmptyM3Placed stageP3ErrPrePrevEmptyM3Placed
  stageP3_sub5_decResult_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget (
  pqxdhLogClosurePlacedSpec
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget (tryDecryptPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (noAllocShimBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightBudget (tryDecryptOnPanicTight)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec growOneSpeEvents growOneSpeEnv_events growOneSpeSpec
  setSessionStateSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local1Budget (
  drop_session_structure_local1_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.GrowSpeBudget (grow_one_spe_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.SetStateBudget (
  set_session_state_placed_ok
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromFEnv FromMEnv FromVPostTdEnv SegCloneEnv SegTailEnv TryDecryptEnvArgs
  segCloneEvents tryDecryptEnvArgs
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Stage P3 allocation event envelopes -/

/-- `TryDecryptEnvArgs` at the Stage P3 `.preKey` call site for cloned session `G₁`. -/
def stageP3M3TryDecryptEnvArgs (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : TryDecryptEnvArgs where
  G := G₁
  st := st
  rem := rem
  loc := loc
  msgG := msgG
  msg := msg
  msgType := .preKey
  rest := rest

/-- Prefix event envelope emitted along Stage P3 up to `+0x34dc` (`Ok pt` continuation into `M4`):
`SessionStructure::clone`, `try_decrypt_with_state`, and `set_session_state` (`FreeOnlyEvs`). -/
def StageP3OkPrefixM3Env (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st)
    (SeqEnv (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) FreeOnlyEvs)

/-- Full event envelope emitted along Stage P3 on `st.version = msgVer` and `Err e` (`e ≠ .panic`):
`SessionStructure::clone`, `try_decrypt_with_state`, and `FromVPostTdEnv`. -/
def StageP3ErrM3Env (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (rest : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st)
    (SeqEnv (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) FromVPostTdEnv)

/-- Full event envelope emitted along Stage P3 on `st.version ≠ msgVer`:
`SessionStructure::clone` followed by `FromMEnv`. -/
def StageP3VerNeM3Env (recG : SessionGhost) (st : SessionState (List (BitVec 8))) :
    List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st) FromMEnv

/-- Combined Stage P3 allocation event envelope for `M3PrevCapPlacedBudget`. -/
def StageP3M3Env (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (msgVer : BitVec 32) (rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if st.version = msgVer then
    ∃ G₁ : SessionGhost, CloneRel recG G₁ ∧
      StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs
  else
    StageP3VerNeM3Env recG st evs

private theorem fitsEnv_segClone_of_stageP3M3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hfits : FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim st_b (SegCloneEnv recG st) := by
  intro e1 he1
  refine hfits e1 ?_
  by_cases hver : st.version = msgVer
  · simp only [StageP3M3Env, hver, ↓reduceIte]
    exact ⟨recG, ⟨rfl, rfl, rfl, rfl⟩, Or.inl he1⟩
  · simp only [StageP3M3Env, hver, ↓reduceIte]
    exact Or.inl he1

private theorem fitsEnv_td_of_stageP3M3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (hfits : FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b)
      (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) := by
  intro e_td htd
  have hfull : StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest
      (segCloneEvents recG st ++ e_td) := by
    simp only [StageP3M3Env, hver, ↓reduceIte]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, e_td, rfl, rfl, Or.inl htd⟩⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_td st_b).mp (hfits _ hfull)).2

private theorem fitsEnv_postTd_of_stageP3M3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)} {evs_td : List AllocEvent}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (htd : tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td)
    (hfits : FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents evs_td (M.stepEvents (segCloneEvents recG st) st_b))
      FromVPostTdEnv := by
  intro e_post hpost
  have hfull : StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest
      ((segCloneEvents recG st ++ evs_td) ++ e_post) := by
    simp only [StageP3M3Env, hver, ↓reduceIte, List.append_assoc]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, evs_td ++ e_post, rfl, rfl,
      Or.inr ⟨evs_td, e_post, rfl, htd, hpost⟩⟩⟩
  rw [← M.stepEvents_append]
  exact ((fitsEvents_append M lim (segCloneEvents recG st ++ evs_td) e_post st_b).mp
    (hfits _ hfull)).2

private theorem fitsEnv_fromM_of_stageP3M3Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {rest : List (BitVec 8)}
    (hver : st.version ≠ msgVer)
    (hfits : FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b) FromMEnv := by
  intro e_m hm
  have hfull : StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest
      (segCloneEvents recG st ++ e_m) := by
    simp only [StageP3M3Env, hver, ↓reduceIte]
    exact Or.inr ⟨segCloneEvents recG st, e_m, rfl, rfl, hm⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_m st_b).mp (hfits _ hfull)).2

/-! ## Budget-threaded component statements and callee specs -/

def CloneGenVRegsPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    ∀ (st_b : M.σ) (s0 s : State)
      (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (rest : List (BitVec 8))
      (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage),
      FitsEnv M lim st_b (SegCloneEnv recG st) →
      st.receiverChains.length < 2 ^ 32 →
      (sp &&& 15#64 == 0#64) = true →
      rootStack ≤ sp.toNat →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 →
      s.status = .Running →
      s.trace = s0.trace →
      SepWPp (lsProg_518 ext) (cloneExitPCPlaced st msgVer) s
        (genP3PrePlaced A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
          msgVer rest recG st rem loc msgG msg s)
        (fun s1 P_f =>
          (P_f ⊢ genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
            sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
            rest recG st rem loc msgG msg s1) ∧
          s1.trace = s0.trace ∧ LibsignalCodeRoLoaded lsmpl s1.mem ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s)
        (fun _ _ => False)

/-- Budget-threaded `[LibsignalPlacement]` CLI `tryDecryptPlacedSpec` weakened to `DistinctSid`
(matching `Poll.pollTryDecryptPlacedSpecP`). -/
def pollTryDecryptM3PlacedSpecP [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st_b) s =>
    ⌜FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.pollTryDecryptM3PlacedSpecP
        C (A.atState lim st_b s) ctl uuidParse S).pre x s
  post := (tryDecryptPlacedSpec C A lim ctl uuidParse S tdEnv).post
  onPanic := (tryDecryptPlacedSpec C A lim ctl uuidParse S tdEnv).onPanic

/-- Budget-threaded `[LibsignalPlacement]` `pollTryDecryptM3PlacedSpecTPTight`
(dropping both `S.recvPanics` and `allocFailedIn`, retaining only model panics). -/
def pollTryDecryptM3PlacedSpecTPTight [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) : Spec (TryDecryptGhost × M.σ) :=
  { pollTryDecryptM3PlacedSpecP C A lim ctl uuidParse S tdEnv with
    pre := fun (x, st_b) s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        LsTokenInitM3 ∗
        (pollTryDecryptM3PlacedSpecP C A lim ctl uuidParse S tdEnv).pre (x, st_b) s
    post := fun (x, st_b) s0 sf =>
      LsTokenInitM3 ∗
        (pollTryDecryptM3PlacedSpecP C A lim ctl uuidParse S tdEnv).post (x, st_b) s0 sf
    onPanic := fun (x, _) s0 sf => tryDecryptOnPanicTight C S uuidParse x s0 sf }

private theorem stageP3_clone_prevEmpty_vregs_prefix_placed_steps [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (C : Crypto) (K : MlKem) (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym)
      (rustCliAllocBudgetSpec M A lim false))
    (hmemcpy : subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec)
    (hcc : ChainClone3OkPlaced A lim ext) (hscc : SenderChainClone3OkPlaced A lim ext)
    (st_b : M.σ) (s0 s : State)
    (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (g : RecordGhost) (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F_frame : SepProp) (Q : State → SepProp → Prop)
    (hfits_clone : FitsEnv M lim st_b (SegCloneEnv recG st))
    (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x1778#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (htr : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hCont : ∀ (s1 : State) (P1 : SepProp),
      Steps (lsProg_518 ext) s s1 →
      s1.pc = cloneExitPCPlaced st msgVer → s1.status = .Running → s1.trace = s0.trace →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl s1.mem →
      (P1 ⊢
        genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
          s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
        (LsTokenInitM3 ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 P1 Q
        (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (LsTokenInitM3 ∗
        genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
        F_frame)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  intro R hm hL
  have hstep := hClone ext hshim halloc hmemcpy hcc hscc st_b s0 s s.sp (s.readReg64 .x29)
    coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest recG st rem loc msgG msg
    hfits_clone hrc_lt hsp_align hsp_root hcro hpc hrun htr
  let F : SepProp :=
    LsTokenInitM3 ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame
  have hP :
      (LsTokenInitM3 ∗
        genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
          whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗ F_frame) =
      genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗ F := by
    dsimp only [F]; ac_rfl
  rw [hP, sepConj_assoc] at hm
  obtain ⟨s1, hsteps,
      ⟨hpc1, hrun1, P1, hm1, hent1, htr1, hcro1, hvregs1_s⟩ | ⟨_, _, _, hf⟩ | ⟨_, hoom⟩⟩ :=
    hstep (F ∗ R) hm hL
  · rw [← sepConj_assoc] at hm1
    obtain ⟨sf, hsteps', hout'⟩ :=
      hCont s1 (P1 ∗ F) hsteps hpc1 hrun1 htr1 (hvregs1_s.trans hvregs) hcro1
        (sepConj_mono_left hent1) R hm1 (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact hf.elim
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 1200000 in
private theorem stageP3_call_tryDecrypt_placed_steps [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)) (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (hroot : subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)))
    (st_b : M.σ) (s0 s s1 : State)
    (coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (G₁ : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (F : SepProp) (Q : State → SepProp → Prop)
    (hver : st.version = msgVer)
    (hfits_td : FitsEnv M lim st_b
      (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)))
    (hnot_self : st.remoteIdentity ≠ some st.localIdentity ∨
      DistinctSid uuidTryParse loc.name.bytes rem.name.bytes)
    (hseeds : SeedsLen32 st) (hrc_lt : st.receiverChains.length < 2 ^ 32)
    (hpq_lt : st.pqRatchetState.length < 2 ^ 32)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) (hsp_root : rootStack ≤ s.sp.toNat)
    (hcro1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hpc1 : s1.pc = dpClosureEntryM3Placed + 0x1cd4#64) (hrun1 : s1.status = .Running)
    (hs1_sp : s1.sp = s.sp) (htr1 : s1.trace = s0.trace)
    (hx0_1 : s1.readReg64 .x0 = s.sp + 0x270#64) (hx1_1 : s1.readReg64 .x1 = s.sp + 0xa90#64)
    (hx2_1 : s1.readReg64 .x2 = remAddrPtr) (hx3_1 : s1.readReg64 .x3 = locAddrPtr)
    (hx4_1 : s1.readReg64 .x4 = whisperMsgPtr) (hx5_1 : s1.readReg64 .x5 = 3#64)
    (hx19_1 : s1.readReg64 .x19 = coroPtr) (hx24_1 : s1.readReg64 .x24 = s.sp + 0x370#64)
    (hx27_1 : s1.readReg64 .x27 = ctxPtr)
    (hCont : ∀ (s2 : State) (G' : SessionGhost) (evs_td : List AllocEvent),
      Steps (lsProg_518 ext) s1 s2 →
      tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td →
      (genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic →
      G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G' →
      s2.pc = dpClosureEntryM3Placed + 0x1cd8#64 → s2.status = .Running →
      s2.sp = s.sp → s2.trace = s0.trace → LibsignalCodeRoLoaded lsmpl s2.mem →
      s2.readReg64 .x19 = coroPtr → s2.readReg64 .x24 = s.sp + 0x370#64 →
      s2.readReg64 .x27 = ctxPtr → calleeSavedVRegs s2 = calleeSavedVRegs s1 →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s2
        ((LsTokenInitM3 ∗
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
          protocolAddressAt A.repAlloc rem remAddrPtr ∗
          protocolAddressAt A.repAlloc loc locAddrPtr ∗
          signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
          coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
          lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
      ((LsTokenInitM3 ∗ sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗ memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_b s1) ∗ F)
      Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0) := by
  have hbl := p3_bl_tryDecrypt_placed_wp A lim st_b ext s1 hpc1 hrun1
  refine bind_sepWP_lscro_steps_m3_placed hcro1 hbl (by sep_focus)
    fun sc hsteps_bl hpcc hrunc hcroc hregsc => ?_
  rcases hregsc with ⟨hspc_1, htrc_1, hx0_c, hx1_c, hx2_c, hx3_c, hx4_c, hx5_c,
    hx19_c, hx24_c, hx27_c, _, hx30_c, hvregs_c⟩
  have hspc : sc.sp = s.sp := hspc_1.trans hs1_sp
  have hspc_al : sc.spAligned = true := by simpa only [State.spAligned, hspc] using hsp_align
  have htrc_0 : sc.trace = s0.trace := htrc_1.trans htr1
  let x : TryDecryptGhost := {
    G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
    msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
    msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest
  }
  intro R hm hL
  have hpre_c :
      sc.mem ⊨
        (withLsCodeLoaded lsmpl
          (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse
            (spqrV1 C.F K) tdEnv)).pre (x, st_b) sc ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.pollTryDecryptM3PlacedSpecP,
      CryptoVerification.Cli.CoinsTape.cliTapeAt, x]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcroc.1, ?_⟩
    rw [hspc, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hpq_lt, ?_⟩
    have hx5_byte : (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey := by
      rw [hx5_c, hx5_1]; rfl
    have hfits_x : FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs {
        G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
        msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
        msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest })) := hfits_td
    have hp_fits : FitsEnv M lim st_b (tdEnv (tryDecryptEnvArgs {
        G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
        msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
        msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest })) = True :=
      propext ⟨fun _ => trivial, fun _ => hfits_x⟩
    have hp2 : (sc.readReg64 .x0 = s.sp + 0x270#64 ∧ sc.readReg64 .x1 = s.sp + 0xa90#64 ∧
        sc.readReg64 .x2 = remAddrPtr ∧ sc.readReg64 .x3 = locAddrPtr ∧
        sc.readReg64 .x4 = whisperMsgPtr ∧ (sc.readReg64 .x5).setWidth 8 = msgTypeByte .preKey ∧
        (st.remoteIdentity ≠ some st.localIdentity ∨
          DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) ∧
        SeedsLen32 st ∧ st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat) = True :=
      propext ⟨fun _ => trivial, fun _ =>
        ⟨hx0_c.trans hx0_1, hx1_c.trans hx1_1, hx2_c.trans hx2_1, hx3_c.trans hx3_1,
         hx4_c.trans hx4_1, hx5_byte, hnot_self, hseeds, hrc_lt, hsp_root⟩⟩
    rw [hp_fits, hp2, pure_true, emp_sepConj, emp_sepConj]
    have hpool_eq : (A.atState lim st_b sc).pool = A.pool lim st_b sc := rfl
    have hss_eq : sessionStateAt (A.atState lim st_b sc) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa1_eq : protocolAddressAt (A.atState lim st_b sc) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa2_eq : protocolAddressAt (A.atState lim st_b sc) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_b sc) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    rw [hpool_eq, hss_eq, hpa1_eq, hpa2_eq, hsm_eq]
    exact Arm64.Satisfies.mono (Entails.of_eq (by ac_rfl)) hm
  obtain ⟨s2, hsteps2, hout2, _⟩ :=
    hroot.no_fault_before_outcome (x, st_b) (F ∗ R) sc hpcc hrunc hpre_c hspc_al hL
  rcases hout2 with ⟨⟨hpc2_lr, hsp2_c, hrun2⟩, ⟨_, hcs2⟩, hm2⟩ | ⟨hpan, hm_pan⟩ | ⟨_, _, hexit⟩ | ⟨_, hoom⟩
  · dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight, pollTryDecryptM3PlacedSpecP,
      tryDecryptPlacedSpec,
      CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec,
      CryptoVerification.Cli.CoinsTape.cliTapeAfter, TryDecryptGhost.model, x] at hm2
    rw [hspc] at hm2
    have hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem := hcroc.of_keepsFrozen hsteps2.keepsFrozen
    have hm2_ex_evs :
        s2.mem ⊨
          ∃∗ evs_td : List AllocEvent,
            ⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
            (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
              ((∃∗ G' : SessionGhost,
                  ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                    (genP3S5Model C K rem loc msg rest st).2) ∗
                LsTokenInitM3 ∗
                vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
                protocolAddressAt A.repAlloc rem remAddrPtr ∗
                protocolAddressAt A.repAlloc loc locAddrPtr ∗
                signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
                coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
                lsLogOff ∗ stackAt s.sp rootStack ∗
                A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R)) := by
      rw [sepExists_sepConj_right, sepExists_sepConj_left] at hm2
      rw [satisfies_sepExists] at hm2 ⊢
      obtain ⟨evs_td, hm2_ev⟩ := hm2
      refine ⟨evs_td, ?_⟩
      have hss_eq2 : ∀ G',
          sessionStateAt (A.atState lim (M.stepEvents evs_td st_b) s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := fun _ => rfl
      have hvec_eq2 :
          vecResultAt (A.atState lim (M.stepEvents evs_td st_b) s2) (s.sp + 0x270#64)
            (genP3S5Model C K rem loc msg rest st).1 =
          vecResultAt A.repAlloc (s.sp + 0x270#64)
            (genP3S5Model C K rem loc msg rest st).1 := rfl
      have hpa1_eq2 :
          protocolAddressAt (A.atState lim (M.stepEvents evs_td st_b) s2) rem remAddrPtr =
          protocolAddressAt A.repAlloc rem remAddrPtr := rfl
      have hpa2_eq2 :
          protocolAddressAt (A.atState lim (M.stepEvents evs_td st_b) s2) loc locAddrPtr =
          protocolAddressAt A.repAlloc loc locAddrPtr := rfl
      have hsm_eq2 :
          signalMessageAt (A.atState lim (M.stepEvents evs_td st_b) s2) msgG whisperMsgPtr msg =
          signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
      have hpool_eq2 : (A.atState lim (M.stepEvents evs_td st_b) s2).pool =
          A.pool lim (M.stepEvents evs_td st_b) s2 := rfl
      have hargs_eq : tryDecryptEnvArgs {
          G := G₁, st := st, rem := rem, loc := loc, msgG := msgG, msg := msg,
          msgType := .preKey, ss := s.sp + 0xa90#64, remA := remAddrPtr, locA := locAddrPtr,
          msgA := whisperMsgPtr, ret := s.sp + 0x270#64, cur := cur, rest := rest } =
        stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest := rfl
      simp only [hss_eq2, hvec_eq2, hpa1_eq2, hpa2_eq2, hsm_eq2, hpool_eq2, hargs_eq] at hm2_ev
      have heq_ev :
          (LsTokenInitM3 ∗
            (⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
              (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
                (∃∗ G' : SessionGhost,
                  ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                  sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                    (genP3S5Model C K rem loc msg rest st).2) ∗
                vecResultAt A.repAlloc (s.sp + 0x270#64)
                  (genP3S5Model C K rem loc msg rest st).1 ∗
                protocolAddressAt A.repAlloc rem remAddrPtr ∗
                protocolAddressAt A.repAlloc loc locAddrPtr ∗
                signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
                coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
                lsLogOff ∗ stackAt s.sp rootStack ∗
                A.pool lim (M.stepEvents evs_td st_b) s2))) ∗ (F ∗ R) =
          ⌜tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td⌝ ∗
          (⌜(genP3S5Model C K rem loc msg rest st).1 ≠ .error .panic ∧ s2.trace = sc.trace⌝ ∗
            ((∃∗ G' : SessionGhost,
                ⌜G₁.AfterTryDecrypt (genP3S5Model C K rem loc msg rest st).1.toBool G'⌝ ∗
                sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
                  (genP3S5Model C K rem loc msg rest st).2) ∗
              LsTokenInitM3 ∗
              vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
              protocolAddressAt A.repAlloc rem remAddrPtr ∗
              protocolAddressAt A.repAlloc loc locAddrPtr ∗
              signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
              coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
              lsLogOff ∗ stackAt s.sp rootStack ∗
              A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R)) := by ac_rfl
      rwa [heq_ev] at hm2_ev
    rw [satisfies_sepExists] at hm2_ex_evs
    obtain ⟨evs_td, hm2_td⟩ := hm2_ex_evs
    rw [satisfies_pure_sepConj] at hm2_td
    rcases hm2_td with ⟨htd_evs, hm2_pull⟩
    rw [satisfies_pure_sepConj] at hm2_pull
    rcases hm2_pull with ⟨⟨hnpan, htr2_c⟩, hm2_ex⟩
    rw [sepExists_sepConj_left, satisfies_sepExists] at hm2_ex
    obtain ⟨G', hm2_G⟩ := hm2_ex
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm2_G
    obtain ⟨hdec_rel, hm2_rest⟩ := hm2_G
    have hm2_cont :
        s2.mem ⊨
          ((LsTokenInitM3 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
              (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F) ∗ R := by
      have heq2 :
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' (genP3S5Model C K rem loc msg rest st).2 ∗
          (LsTokenInitM3 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗
            A.pool lim (M.stepEvents evs_td st_b) s2 ∗ F ∗ R) =
          ((LsTokenInitM3 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
              (genP3S5Model C K rem loc msg rest st).2 ∗
            vecResultAt A.repAlloc (s.sp + 0x270#64) (genP3S5Model C K rem loc msg rest st).1 ∗
            protocolAddressAt A.repAlloc rem remAddrPtr ∗
            protocolAddressAt A.repAlloc loc locAddrPtr ∗
            signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
            coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
            lsLogOff ∗ stackAt s.sp rootStack ∗
            A.pool lim (M.stepEvents evs_td st_b) s2) ∗ F) ∗ R := by ac_rfl
      rwa [heq2] at hm2_rest
    rcases hcs2 with ⟨hx19_cs2, _, _, _, _, hx24_cs2, _, _, hx27_cs2, _, _, hvregs_cs2⟩
    obtain ⟨sf, hsteps3, hout3⟩ :=
      hCont s2 G' evs_td (hsteps_bl.trans hsteps2) htd_evs hnpan hdec_rel
        (hpc2_lr.trans hx30_c) hrun2
        (hsp2_c.trans hspc) (htr2_c.trans htrc_0) hcro2
        (hx19_cs2.trans (hx19_c.trans hx19_1)) (hx24_cs2.trans (hx24_c.trans hx24_1))
        (hx27_cs2.trans (hx27_c.trans hx27_1)) (hvregs_cs2.trans hvregs_c)
        R hm2_cont (hsteps2.codeLoaded hL)
    exact ⟨sf, hsteps2.trans hsteps3, hout3⟩
  · dsimp only [withLsCodeLoaded, pollTryDecryptM3PlacedSpecTPTight,
      tryDecryptOnPanicTight, TryDecryptGhost.model, x] at hm_pan
    rw [sepConj_assoc, satisfies_pure_sepConj] at hm_pan
    rcases hm_pan with ⟨⟨hmod_pan, hpref_c⟩, hm_any⟩
    have hpref_0 : s0.trace <+: s2.trace := htrc_0 ▸ hpref_c
    have hm_any_R : s2.mem ⊨ anyHeap ∗ R := by
      rw [← sepConj_assoc] at hm_any
      exact Arm64.Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hm_any
    refine ⟨s2, hsteps2, Or.inr (Or.inl ⟨hpan,
      ⌜st.version = msgVer ∧ (genP3S5Model C K rem loc msg rest st).1 = .error .panic ∧
          s0.trace <+: s2.trace⌝ ∗ anyHeap, ?_, fun _ h => h⟩)⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hver, hmod_pan, hpref_0⟩, hm_any_R⟩
  · exact (allowPanic_not_exited hexit).elim
  · exact (not_satisfies_false_sepConj hoom).elim

/-- Budget-threaded `[LibsignalPlacement]` Substage P3.5 error path
(`dpClosureEntryM3Placed + 0x1cd8 → s0.readReg64 .x30`) for `Matched/M3PrevErrBPlacedBudget`. -/
def StageP3Sub5ErrPrevEmptyPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromVPostTdEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (e : SignalProtocolError), e ≠ .panic →
      ∀ (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost)
        (st₂ recSt : SessionState (List (BitVec 8))),
        LibsignalCodeRoLoaded lsmpl s.mem →
        s.pc = dpClosureEntryM3Placed + 0x1cd8#64 →
        s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true →
        s.trace = s0.trace →
        s.readReg64 .x19 = coroPtr →
        s.readReg64 .x24 = s.sp + 0x370#64 →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
          (stageP3ErrPrePrevEmptyM3Placed A lim st_b s0 s s coroPtr outPtr initErrsPtr g e b_2c0
            G₂ recG st₂ recSt)
          (fun sf P_f =>
            ∃ evs_err : List AllocEvent,
              FromVPostTdEnv evs_err ∧
              (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b)
                s0 s sf coroPtr outPtr e) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
          (fun _ _ => False)

/-- Budget-threaded `[LibsignalPlacement]` version-mismatch error path
(`dpClosureEntryM3Placed + 0x1e04 → s0.readReg64 .x30`) for `Matched/M3PrevVerNePlacedBudget`. -/
def StageP3VerNePrevEmptyPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromMEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (msgVer : BitVec 32) (b_2c0 : BitVec 8) (g : RecordGhost) (G₁ recG : SessionGhost)
        (st : SessionState (List (BitVec 8))),
        LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
          (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            memRegion (s.sp + 0x270#64) 48 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
            prevSessionsEmptyAt A.repAlloc coroPtr g ∗
            ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
            lsLogOff ∗
            memRegion outPtr 48 ∗
            memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            memRegion (s.sp + 0x930#64) 48 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim st_b s1 ∗
            stackAt s.sp growOneSpeStack)
          (fun sf P_f =>
            ∃ evs_vn : List AllocEvent,
              FromMEnv evs_vn ∧
              (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf
                coroPtr outPtr (.invalidMessage .preKey .decryptionFailed)) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
          (fun _ _ => False)

/-! ## Caller-lifted `set_session_state` (Block 48) and `grow_one_spe` (Block 42) -/

/-- Caller-lifted `setSessionStateSpec M A lim` at `lsmpl.base 48` on `lsProg_518 ext`. -/
theorem set_session_state_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hmemcpy : HookSat ext lsMemcpySym (withVmPreserved sessionMemcpyRegionSpec))
    (hdealloc : HookSat ext lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (set_session_state_placed_ok hmemcpy (drop_session_structure_local1_placed_ok hdealloc))
    (by decide)

/-- Caller-lifted `growOneSpeSpec M A lim` at `lsmpl.base 42` on `lsProg_518 ext`. -/
theorem grow_one_spe_placed_ok_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext lsRustNoAllocShimSym noAllocShimBudgetSpec)
    (halloc : HookSat ext lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hrealloc : HookSat ext lsRustReallocSym (rustCliReallocBudgetSpec M A lim)) :
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) :=
  ls_subroutine_ok_of_block (callerProg := lsProg_518 ext)
    (grow_one_spe_placed_ok hshim halloc hrealloc)
    (by decide)

/-! ## Main Stage P3 composition -/

def StageP3PrevEmptyVRegsM3PlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 519) (withLsCodeLoaded lsmpl pqxdhLogClosurePlacedSpec) →
    ext lsHandleErrorSym = some Rust.panicked →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (evs_ok : List AllocEvent) (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmptyPlaced A lim (M.stepEvents evs_ok st_b) s0 s s'
            coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (evs_err : List AllocEvent)
          (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_err →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeM3Env recG st evs_vn →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalPlacement]` Stage P3 (`dpClosureEntryM3Placed + 0x1778 → +0x34dc` /
`s0.readReg64 .x30`) over general `prevSessionsEmptyAt A.repAlloc coroPtr g` under `StageP3M3Env`. -/
theorem stageP3Gen_prevEmpty_vregs_placed_ok_of_parts [LibsignalPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hErrSub5 : StageP3Sub5ErrPrevEmptyPlacedStmt)
    (hVerNeSub : StageP3VerNePrevEmptyPlacedStmt) :
    StageP3PrevEmptyVRegsM3PlacedStmt := by
  intro M A lim ext C ctl K tdEnv
    hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hLogClosure hpanic
    hcc hscc hroot
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    g recG st rem loc msgG msg F_frame Q
    hfits hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hcro hpc hrun hsp_align hsp_root htr hvregs
    hOk hErr hVerNe
  have hfits_clone := fitsEnv_segClone_of_stageP3M3Env hfits
  refine stageP3_clone_prevEmpty_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hcc hscc st_b
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur g msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
        s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗
      F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td : FitsEnv M lim st_clone
        (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) :=
      fitsEnv_td_of_stageP3M3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp :=
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool lim st_clone s1) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_placed_steps ext C ctl K tdEnv hroot st_clone
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrevEmpty_placed A lim st_td s0 s s2
            coroPtr ctxPtr outPtr initErrsPtr
            remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hfits_post : FitsEnv M lim st_td FromVPostTdEnv :=
        fitsEnv_postTd_of_stageP3M3Env hver hclone_rel htd_evs hfits
      have herr := hErrSub5 ext hshim halloc hdealloc hmemcpy hGrow hDropSS3 hLogClosure hpanic
        st_td s0 s2 coroPtr outPtr initErrsPtr hfits_post hinit_ne e he_npan b_2c0
        g G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
        at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp
      apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' e evs_tot sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.trans (sepConj_mono_left hPf_err)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 :
          vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          prevSessionsEmptyAt (A.atState lim st_td s2) coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState st_td
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' pt ptCap ptPtr evs_ok s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmptyPlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchOkMidPrevEmptyPlaced
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          prevSessionsEmptyAt (A.atState lim (M.stepEvents evs_ok st_b) s') coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp
    apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM : FitsEnv M lim st_clone FromMEnv :=
      fitsEnv_fromM_of_stageP3M3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := hVerNeSub ext hshim halloc hdealloc hGrow hDropSS3 hLogClosure hpanic
      st_clone s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hfits_fromM hinit_ne
      msgVer b_2c0 g G₁ recG st
      hcro1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeM3Env recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]
      rw [M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFramePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
    exact Entails.trans (sepConj_mono_left hPf_vn)
      (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

/-! ## `[LibsignalFullPlacement]` / `LibsignalFrozen` variants -/

/-- Budget-threaded `[LibsignalFullPlacement]` Substage P3.5 error path
(`dpClosureEntryM3Placed + 0x1cd8 → s0.readReg64 .x30`), discharging Block `519` from
`LibsignalFrozen lsmpl s.mem`. -/
def StageP3Sub5ErrPrevEmptyFullPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s : State) (coroPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromVPostTdEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (e : SignalProtocolError), e ≠ .panic →
      ∀ (b_2c0 : BitVec 8) (g : RecordGhost) (G₂ recG : SessionGhost)
        (st₂ recSt : SessionState (List (BitVec 8))),
        CryptoVerification.LibsignalFrozen lsmpl s.mem →
        s.pc = dpClosureEntryM3Placed + 0x1cd8#64 →
        s.status = .Running →
        (s.sp &&& 15#64 == 0#64) = true →
        s.trace = s0.trace →
        s.readReg64 .x19 = coroPtr →
        s.readReg64 .x24 = s.sp + 0x370#64 →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
          (stageP3ErrPrePrevEmptyM3Placed A lim st_b s0 s s coroPtr outPtr initErrsPtr g e b_2c0
            G₂ recG st₂ recSt)
          (fun sf P_f =>
            ∃ evs_err : List AllocEvent,
              FromVPostTdEnv evs_err ∧
              (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b)
                s0 s sf coroPtr outPtr e) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
          (fun _ _ => False)

/-- Budget-threaded `[LibsignalFullPlacement]` version-mismatch error path
(`dpClosureEntryM3Placed + 0x1e04 → s0.readReg64 .x30`), discharging Block `519` from
`LibsignalFrozen lsmpl s.mem`. -/
def StageP3VerNePrevEmptyFullPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State)),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ∀ (st_b : M.σ) (s0 s s1 : State) (coroPtr ctxPtr outPtr initErrsPtr : BitVec 64),
      FitsEnv M lim st_b FromMEnv →
      initErrsPtr ≠ 0#64 →
      ∀ (msgVer : BitVec 32) (b_2c0 : BitVec 8) (g : RecordGhost) (G₁ recG : SessionGhost)
        (st : SessionState (List (BitVec 8))),
        CryptoVerification.LibsignalFrozen lsmpl s1.mem →
        s1.pc = dpClosureEntryM3Placed + 0x1e04#64 →
        s1.status = .Running →
        s1.sp = s.sp →
        (s.sp &&& 15#64 == 0#64) = true →
        s1.trace = s0.trace →
        s1.readReg64 .x9 = msgVer.setWidth 64 →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x24 = s.sp + 0x370#64 →
        s1.readReg64 .x27 = ctxPtr →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1
          (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
            memRegion (s.sp + 0x270#64) 48 ∗
            sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
            ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
            ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
            prevSessionsEmptyAt A.repAlloc coroPtr g ∗
            ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
            lsLogOff ∗
            memRegion outPtr 48 ∗
            memRegion (s.sp + 0x250#64) 20 ∗
            memRegion (s.sp + 0x370#64) 36 ∗
            memRegion (s.sp + 0x930#64) 48 ∗
            decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim st_b s1 ∗
            stackAt s.sp growOneSpeStack)
          (fun sf P_f =>
            ∃ evs_vn : List AllocEvent,
              FromMEnv evs_vn ∧
              (P_f ⊢ stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf
                coroPtr outPtr (.invalidMessage .preKey .decryptionFailed)) ∧
              sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
              LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s1)
          (fun _ _ => False)

/-- Budget-threaded `[LibsignalFullPlacement]` Stage P3 statement on `lsProg_518 ext`,
discharging Block `519` internally from `LibsignalFrozen lsmpl s.mem`. -/
def StageP3PrevEmptyVRegsM3FullPlacedStmt [CryptoVerification.LibsignalFullPlacement] : Prop :=
  ∀ {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (ext : String → Option (State → State))
    (C : Crypto) (ctl : BitVec 64) (K : MlKem)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop),
    subroutine_ok (lsProg_518 ext) (lsρ lsRustNoAllocShimSym) sessionShimBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustAllocSym) (rustCliAllocBudgetSpec M A lim false) →
    subroutine_ok (lsProg_518 ext) (lsρ lsRustDeallocSym) (rustCliDeallocBudgetSpec M A lim) →
    subroutine_ok (lsProg_518 ext) (lsρ lsMemcpySym) sessionMemcpyRegionBudgetSpec →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 42) (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
    subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ext lsHandleErrorSym = some Rust.panicked →
    ChainClone3OkPlaced A lim ext →
    SenderChainClone3OkPlaced A lim ext →
    subroutine_ok (lsProg_518 ext) (lsmpl.base 508)
      (withLsCodeLoaded lsmpl
        (pollTryDecryptM3PlacedSpecTPTight C A lim ctl uuidTryParse (spqrV1 C.F K) tdEnv)) →
    ∀ (st_b : M.σ) (s0 s : State)
      (coroPtr ctxPtr outPtr initErrsPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
      (msgVer : BitVec 32) (b_2c0 : BitVec 8) (rest : List (BitVec 8))
      (g : RecordGhost) (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
      (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
      (F_frame : SepProp) (Q : State → SepProp → Prop),
      FitsEnv M lim st_b (StageP3M3Env tdEnv recG st rem loc msgG msg msgVer rest) →
      initErrsPtr ≠ 0#64 →
      (st.remoteIdentity ≠ some st.localIdentity ∨
        DistinctSid uuidTryParse loc.name.bytes rem.name.bytes) →
      SeedsLen32 st → st.receiverChains.length < 2 ^ 32 → st.pqRatchetState.length < 2 ^ 32 →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      s.pc = dpClosureEntryM3Placed + 0x1778#64 → s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true → rootStack ≤ s.sp.toNat →
      s.trace = s0.trace → calleeSavedVRegs s = calleeSavedVRegs s0 →
      (∀ (G₁ G' : SessionGhost) (pt : List (BitVec 8)) (ptCap ptPtr : BitVec 64)
          (evs_ok : List AllocEvent) (s' : State) (P_s' : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt true G' →
        StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok →
        (genP3S5Model C K rem loc msg rest st).1 = .ok pt →
        pt.length ≤ ptCap.toNat → ptCap.toNat < 2 ^ 63 → ptPtr ≠ 0#64 →
        Steps (lsProg_518 ext) s s' → s'.pc = dpClosureEntryM3Placed + 0x34dc#64 →
        s'.status = .Running → s'.sp = s.sp → s'.trace = s0.trace →
        calleeSavedVRegs s' = calleeSavedVRegs s0 →
        s'.readReg64 .x19 = coroPtr → s'.readReg64 .x24 = s.sp + 0x370#64 →
        s'.readReg64 .x25 = s.sp + 0x210#64 → s'.readReg64 .x26 = outPtr →
        s'.readReg64 .x27 = ctxPtr → s'.readReg64 .x28 = 0xfffffffffffffffe#64 →
        LibsignalCodeRoLoaded lsmpl s'.mem →
        (P_s' ⊢
          stageP3DispatchOkMidPrevEmptyPlaced A lim (M.stepEvents evs_ok st_b) s0 s s'
            coroPtr outPtr initErrsPtr ptCap ptPtr g pt b_2c0 G'
            (genP3S5Model C K rem loc msg rest st).2 ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s' (P_s' ∗ F_frame) Q
          (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)) →
      (∀ (G₁ G' : SessionGhost) (e : SignalProtocolError) (evs_err : List AllocEvent)
          (sf : State) (P_f : SepProp),
        st.version = msgVer → CloneRel recG G₁ → G₁.AfterTryDecrypt false G' →
        StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_err →
        (genP3S5Model C K rem loc msg rest st).1 = .error e → e ≠ .panic →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_err st_b) s0 s sf coroPtr outPtr e ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      (∀ (evs_vn : List AllocEvent) (sf : State) (P_f : SepProp),
        st.version ≠ msgVer →
        StageP3VerNeM3Env recG st evs_vn →
        (P_f ⊢
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ memRegion (s.sp + 0x3e0#64) 344 ∗
          stageP3ErrPostPrevEmptyM3Placed A lim (M.stepEvents evs_vn st_b) s0 s sf coroPtr outPtr
            (.invalidMessage .preKey .decryptionFailed) ∗
          genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
            rem loc msgG msg (coinsAtPlaced cur rest)) →
        sf.sp = s.sp + 0xcd0#64 → sf.trace = s0.trace → ClosureCalleeSaved s0 sf →
        calleeSavedVRegs sf = calleeSavedVRegs s0 → LibsignalCodeRoLoaded lsmpl sf.mem →
        Q sf (P_f ∗ F_frame)) →
      SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
        (LsTokenInitM3 ∗
          genP3PrePlaced A lim st_b s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
            whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s ∗
          stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0 ∗
          F_frame)
        Q (genP3S5ModelPanicProp C K rem loc st msg msgVer rest s0)

set_option maxHeartbeats 1200000 in
/-- Budget-threaded `[LibsignalFullPlacement]` Stage P3
(`dpClosureEntryM3Placed + 0x1778 → +0x34dc` / `s0.readReg64 .x30`) over general
`prevSessionsEmptyAt A.repAlloc coroPtr g`, discharging Block `519` from `LibsignalFrozen`. -/
theorem stageP3Gen_prevEmpty_vregs_full_placed_ok_of_parts [CryptoVerification.LibsignalFullPlacement]
    (hClone : CloneGenVRegsPlacedStmt)
    (hErrSub5 : StageP3Sub5ErrPrevEmptyFullPlacedStmt)
    (hVerNeSub : StageP3VerNePrevEmptyFullPlacedStmt) :
    StageP3PrevEmptyVRegsM3FullPlacedStmt := by
  intro M A lim ext C ctl K tdEnv
    hshim halloc hdealloc hmemcpy hGrow hSetState hDropSS3 hpanic
    hcc hscc hroot
    st_b s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur msgVer b_2c0 rest
    g recG st rem loc msgG msg F_frame Q
    hfits hinit_ne hnot_self hseeds hrc_lt hpq_lt
    hfr hpc hrun hsp_align hsp_root htr hvregs
    hOk hErr hVerNe
  have hcro : LibsignalCodeRoLoaded lsmpl s.mem := LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.LoopErrPlacedBudget.lscro_of_frozen hfr
  have hfits_clone := fitsEnv_segClone_of_stageP3M3Env hfits
  refine stageP3_clone_prevEmpty_vregs_prefix_placed_steps hClone C K ext
    hshim halloc hmemcpy hcc hscc st_b
    s0 s coroPtr ctxPtr outPtr initErrsPtr
    remAddrPtr locAddrPtr whisperMsgPtr cur g msgVer b_2c0 rest
    recG st rem loc msgG msg F_frame Q hfits_clone hrc_lt hcro hpc hrun hsp_align hsp_root
    htr hvregs
    fun s1 P1 hsteps01 hpc1 hrun1 htr1 hvregs1 hcro1 hent1 => ?_
  have hfr1 : CryptoVerification.LibsignalFrozen lsmpl s1.mem := CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps01.keepsFrozen
  refine SepWPp.weaken_pre hent1 ?_
  refine SepWPp.weaken_pre
    (P' := (genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
        s.sp (s.readReg64 .x29) coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s1 ∗
      (LsTokenInitM3 ∗
        stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0)) ∗
      F_frame)
    (Entails.of_eq (by ac_rfl)) ?_
  by_cases hver : st.version = msgVer
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostEqPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, _,
      hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun hclone_rel => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_td : FitsEnv M lim st_clone
        (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) :=
      fitsEnv_td_of_stageP3M3Env hver hclone_rel hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    change SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s1 _ Q _
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    let F_dec : SepProp :=
      sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrevEmpty A.repAlloc s0 s coroPtr outPtr initErrsPtr g b_2c0
    refine SepWPp.weaken_pre
      (P' := (LsTokenInitM3 ∗
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st ∗
        protocolAddressAt A.repAlloc rem remAddrPtr ∗
        protocolAddressAt A.repAlloc loc locAddrPtr ∗
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
        memRegion (s.sp + 0x270#64) 48 ∗
        coinsAtPlaced cur rest ∗
        lsLogOff ∗
        stackAt s.sp rootStack ∗
        A.pool lim st_clone s1) ∗ (F_dec ∗ F_frame))
      (Entails.of_eq (eq_of_sep_emp (by dsimp only [F_dec]; sep_focus))) ?_
    refine stageP3_call_tryDecrypt_placed_steps ext C ctl K tdEnv hroot st_clone
      s0 s s1 coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
      G₁ st rem loc msgG msg (F_dec ∗ F_frame) Q
      hver hfits_td hnot_self hseeds hrc_lt hpq_lt hsp_align hsp_root
      hcro1 hpc1 hrun1 hs1_sp htr1
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx5_1 hx19_1 hx24_1 hx27_1
      fun s2 G' evs_td hsteps12 htd_evs hnpan hdec_rel hpc2 hrun2 hs2_sp htr2 hcro2
          hx19_2 hx24_2 hx27_2 hvregs2_1 => ?_
    have hvregs2 : calleeSavedVRegs s2 = calleeSavedVRegs s0 := hvregs2_1.trans hvregs1
    have hsteps02 : Steps (lsProg_518 ext) s s2 := hsteps01.trans hsteps12
    have hfr2 : CryptoVerification.LibsignalFrozen lsmpl s2.mem := CryptoVerification.libsignalFrozen_of_keepsFrozen hfr hsteps02.keepsFrozen
    let st_td := M.stepEvents evs_td st_clone
    refine SepWPp.weaken_pre
      (Entails.trans (Entails.of_eq (sepConj_assoc _ F_dec F_frame).symm)
        (sepConj_mono_left
          (postTryDecrypt_entails_s5DispatchPrevEmpty_placed A lim st_td s0 s s2
            coroPtr ctxPtr outPtr initErrsPtr
            remAddrPtr locAddrPtr whisperMsgPtr g msgVer b_2c0
            (genP3S5Model C K rem loc msg rest st).1 G' recG
            (genP3S5Model C K rem loc msg rest st).2 st rem loc msgG msg
            (coinsAfterPlaced cur rest (decryptDraws C st msg.senderRatchetKey rest))))) ?_
    have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hs2_sp]; exact hsp_align
    have hx24_2' : s2.readReg64 .x24 = s2.sp + 0x370#64 := by rw [hx24_2, hs2_sp]
    unfold stageP3DispatchPrePrevEmptyPlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchPrePrevEmptyPlaced
    rcases hres : (genP3S5Model C K rem loc msg rest st).1 with e | pt
    · have he_npan : e ≠ .panic := fun h => hnpan (hres.trans (h ▸ rfl))
      have hdec_false : G₁.AfterTryDecrypt false G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hfits_post : FitsEnv M lim st_td FromVPostTdEnv :=
        fitsEnv_postTd_of_stageP3M3Env hver hclone_rel htd_evs hfits
      have herr := hErrSub5 ext hshim halloc hdealloc hmemcpy hGrow hDropSS3 hpanic
        st_td s0 s2 coroPtr outPtr initErrsPtr hfits_post hinit_ne e he_npan b_2c0
        g G' recG (genP3S5Model C K rem loc msg rest st).2 st
        hfr2 hpc2 hrun2 hsp2_align htr2 hx19_2 hx24_2'
      unfold stageP3ErrPrePrevEmptyM3Placed
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPrePrevEmptyM3Placed
        at herr
      have herr_post : ∀ st_e sf,
          stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s2 sf coroPtr outPtr e =
            stageP3ErrPostPrevEmptyM3Placed A lim st_e s0 s sf coroPtr outPtr e := by
        intro st_e sf
        unfold stageP3ErrPostPrevEmptyM3Placed
          CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3ErrPostPrevEmptyM3Placed
        rw [hs2_sp]
      simp only [herr_post, hs2_sp] at herr
      apply sepWPp_lift_false_qp
      apply sepWPp_frame_false_qp
      refine ret_sepWPp_frame_false herr (by sep_focus)
        fun sf _ _ _ ⟨evs_err, herr_evs, hPf_err, hspf, htrf, hcc_f, hcrof, hvregsf_2⟩ => ?_
      let evs_tot := segCloneEvents recG st ++ (evs_td ++ evs_err)
      have hevs_tot : StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_tot :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_err, rfl, rfl,
          Or.inr ⟨evs_td, evs_err, rfl, htd_evs, herr_evs⟩⟩
      have hstep_tot : M.stepEvents evs_err st_td = M.stepEvents evs_tot st_b := by
        dsimp only [st_td, st_clone, evs_tot]
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hstep_tot] at hPf_err
      refine hErr G₁ G' e evs_tot sf _ hver hclone_rel hdec_false hevs_tot hres he_npan ?_
        hspf htrf hcc_f (hvregsf_2.trans hvregs2) hcrof
      exact Entails.trans (sepConj_mono_left hPf_err)
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
    · have hdec_true : G₁.AfterTryDecrypt true G' := by
        simpa [hres, Except.toBool] using hdec_rel
      have hstack_set :
          stackAt s.sp growOneSpeStack =
            memRegion (s.sp - 4608#64) 352 ∗ stackAt s.sp setSessionStateStack :=
        stackAt_split_bottom s.sp setSessionStateStack 352 (by decide)
      rw [hstack_set]
      have hvec_eq_s2 :
          vecResultAt (A.atState lim st_td s2) (s.sp + 0x270#64) (.ok pt) =
          vecResultAt A.repAlloc (s.sp + 0x270#64) (.ok pt) := rfl
      have hss_g_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (s.sp + 0xa90#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hss_rec_eq_s2 :
          sessionStateAt (A.atState lim st_td s2) (coroPtr + 0xf8#64) recG st =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
      have hprev_eq_s2 :
          prevSessionsEmptyAt (A.atState lim st_td s2) coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
      have hpool_eq_s2 : (A.atState lim st_td s2).pool = A.pool lim st_td s2 := rfl
      simp only [hvec_eq_s2, hss_g_eq_s2, hss_rec_eq_s2, hprev_eq_s2, hpool_eq_s2]
      have hok := stageP3_sub5_decResult_placed_ok ext hmemcpy hSetState st_td
        s0 s2 coroPtr outPtr pt G' recG
        (genP3S5Model C K rem loc msg rest st).2 st
        hcro2 hpc2 hrun2 hsp2_align htr2 hx19_2
      rw [hs2_sp] at hok
      refine bind_sepWPp_false_steps_framed hok (by sep_focus)
        fun s' P_m hsteps2' hpc' hrun' ⟨evs_free, ptCap, ptPtr, hevs_free,
          hpt_le, hpt_lt, hpt_ne, hPs',
          hsp', htr', hcro', hx19', hx24', hx25', hx26', hx27', hx28', _, hvregs'_2⟩ => ?_
      let evs_ok := segCloneEvents recG st ++ (evs_td ++ evs_free)
      have hevs_ok : StageP3OkPrefixM3Env tdEnv recG G₁ st rem loc msgG msg rest evs_ok :=
        Or.inr ⟨segCloneEvents recG st, evs_td ++ evs_free, rfl, rfl,
          Or.inr ⟨evs_td, evs_free, rfl, htd_evs, hevs_free⟩⟩
      have hstep_ok : M.stepEvents evs_free st_td = M.stepEvents evs_ok st_b := by
        dsimp only [st_td, st_clone, evs_ok]
        rw [M.stepEvents_append, M.stepEvents_append]
      rw [hstep_ok] at hPs'
      refine hOk G₁ G' pt ptCap ptPtr evs_ok s' _ hver hclone_rel hdec_true hevs_ok hres
        hpt_le hpt_lt hpt_ne (hsteps02.trans hsteps2') hpc' hrun' hsp' htr'
        (hvregs'_2.trans hvregs2)
        hx19' (hx24'.trans hx24_2) hx25' hx26' (hx27'.trans hx27_2) hx28' hcro' ?_
      unfold stageP3DispatchOkMidPrevEmptyPlaced
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.stageP3DispatchOkMidPrevEmptyPlaced
      rw [hstack_set]
      have hlive_s' :
          (if ptCap = 0#64 then emp
           else (A.atState lim (M.stepEvents evs_ok st_b) s').live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) =
          (if ptCap = 0#64 then emp
           else A.live ptPtr ptCap.toNat 1 ∗
             memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) := rfl
      have hss_s' :
          sessionStateAt (A.atState lim (M.stepEvents evs_ok st_b) s') (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 =
          sessionStateAt A.repAlloc (coroPtr + 0xf8#64) G'
            (genP3S5Model C K rem loc msg rest st).2 := rfl
      have hprev_s' :
          prevSessionsEmptyAt (A.atState lim (M.stepEvents evs_ok st_b) s') coroPtr g =
          prevSessionsEmptyAt A.repAlloc coroPtr g := rfl
      have hpool_s' :
          (A.atState lim (M.stepEvents evs_ok st_b) s').pool =
          A.pool lim (M.stepEvents evs_ok st_b) s' := rfl
      rw [hlive_s', hss_s', hprev_s', hpool_s']
      exact Entails.trans (sepConj_mono_left hPs')
        (Entails.of_eq (eq_of_sep_emp (by sep_focus)))
  · simp only [cloneExitPCPlaced, genP3PostPlaced,
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostPlaced,
      hver, ↓reduceIte] at hpc1 ⊢
    apply sepWPp_lift_false_qp
    apply sepWPp_frame_false_qp
    unfold CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostNePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3PostSpatialPlaced
      stageP3Sub5ExtraPrePrevEmpty
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hs1_sp, hx9_1, hx19_1, hx24_1, hx27_1, _⟩ => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun G₁ => ?_
    refine sepWPp_weaken_frame
      (P₁ := ⌜CloneRel recG G₁⌝) (P₂ := ⌜CloneRel recG G₁⌝)
      (Entails.refl _) (by sep_focus) ?_
    refine SepWPp.pure_elim fun _ => ?_
    set st_clone := M.stepEvents (segCloneEvents recG st) st_b
    have hfits_fromM : FitsEnv M lim st_clone FromMEnv :=
      fitsEnv_fromM_of_stageP3M3Env hver hfits
    have hss_rec_eq : sessionStateAt (A.atState lim st_clone s1) (coroPtr + 0xf8#64) recG st =
        sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st := rfl
    have hss_g1_eq : sessionStateAt (A.atState lim st_clone s1) (s.sp + 0xa90#64) G₁ st =
        sessionStateAt A.repAlloc (s.sp + 0xa90#64) G₁ st := rfl
    have hpa_rem_eq : protocolAddressAt (A.atState lim st_clone s1) rem remAddrPtr =
        protocolAddressAt A.repAlloc rem remAddrPtr := rfl
    have hpa_loc_eq : protocolAddressAt (A.atState lim st_clone s1) loc locAddrPtr =
        protocolAddressAt A.repAlloc loc locAddrPtr := rfl
    have hsm_eq : signalMessageAt (A.atState lim st_clone s1) msgG whisperMsgPtr msg =
        signalMessageAt A.repAlloc msgG whisperMsgPtr msg := rfl
    have hpool_s1_eq : (A.atState lim st_clone s1).pool = A.pool lim st_clone s1 := rfl
    simp only [hss_rec_eq, hss_g1_eq, hpa_rem_eq, hpa_loc_eq, hsm_eq, hpool_s1_eq]
    refine sepWPp_weaken_frame (genP3SpillAll_entails_s5 s.sp) (by sep_focus) ?_
    refine sepWPp_weaken_frame (Entails.of_eq (stackAt_root_split_grow s.sp))
      (by sep_focus) ?_
    refine sepWPp_weaken_frame (Entails.of_eq (memRegion344_104_240_eq s.sp))
      (by sep_focus) ?_
    have hver_ne := hVerNeSub ext hshim halloc hdealloc hGrow hDropSS3 hpanic
      st_clone s0 s s1 coroPtr ctxPtr outPtr initErrsPtr hfits_fromM hinit_ne
      msgVer b_2c0 g G₁ recG st
      hfr1 hpc1 hrun1 hs1_sp hsp_align htr1 hx9_1 hx19_1 hx24_1 hx27_1
    refine ret_sepWPp_frame_false hver_ne (by sep_focus)
      fun sf _ _ _ ⟨evs_vn, hvn_evs, hPf_vn, hspf, htrf, hcc_f, hcrof, hvregsf_1⟩ => ?_
    let evs_vn_tot := segCloneEvents recG st ++ evs_vn
    have hevs_vn_tot : StageP3VerNeM3Env recG st evs_vn_tot :=
      Or.inr ⟨segCloneEvents recG st, evs_vn, rfl, rfl, hvn_evs⟩
    have hstep_vn : M.stepEvents evs_vn st_clone = M.stepEvents evs_vn_tot st_b := by
      dsimp only [st_clone, evs_vn_tot]
      rw [M.stepEvents_append]
    rw [hstep_vn] at hPf_vn
    refine hVerNe evs_vn_tot sf _ hver hevs_vn_tot ?_ hspf htrf hcc_f
      (hvregsf_1.trans hvregs1) hcrof
    unfold genP3S5PostFramePlaced
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.genP3S5PostFramePlaced
    exact Entails.trans (sepConj_mono_left hPf_vn)
      (Entails.of_eq (eq_of_sep_emp (by sep_focus)))

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
