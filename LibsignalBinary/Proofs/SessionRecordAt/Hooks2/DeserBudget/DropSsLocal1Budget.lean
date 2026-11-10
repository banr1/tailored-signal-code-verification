/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public meta import Lean -- shake: keep
public meta import ProofLib -- shake: keep
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift
public meta import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DropSsLocal1Ext
import GeneratedLean.LibsignalSessionCode -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.Chain.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded `SessionStructure` Drop Glue Proofs

Proves relocatable `[LibsignalPlacement]` total-correctness (`onOom := ⌜False⌝`,
`onPanic := ⌜False⌝`) contracts for:
* `core::ptr::drop_glue::<Vec<MessageKey>>` (Block `3`, `16,432` B);
* `core::ptr::drop_glue::<Vec<Chain>>` (Block `2`, `16,480` B);
* `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`, `16,512` B), consuming
  `sessionStateAt A.repAlloc ss G st` and crediting `ssStateLargeLive M G st` back from `liveLarge`
  with non-increasing `cumSmall` and `peakLarge`;
* `fromRecord_clone_and_drop_budget_bounds` composing clone and drop peak bounds.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  ChainKey ReceiverChain SenderChain MessageKeyGenerator SessionState
)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded
  withLsCodeLoaded withLsCl lsmpl lsρ lsRustDeallocSym blkPC_6 blkPl_6
)
open CryptoVerification.RustHeap (
  RustAlloc LayoutOk arrayAt vecAt vecHeader vecU8At vecU8At_entails_dealloc
)
open CryptoVerification.LibsignalSessionRepr (
  VecPin VecGhost MessageKeyGhost ChainGhost optChainKeyNone
  vecGhostAt optChainKeyAt messageKeyAt chainAt
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  TailVecGhost SenderChainGhost SessionGhost noneCap
  optSenderChainAt optTailVecAt sessionStateAt
)
open CryptoVerification.LibsignalTripleRatchet (
  extHookStack ls_subroutine_ok_cl_of_callee
)
open CryptoVerification.LibsignalTripleRatchet.Getters (
  DropVecMessageKeyGhost DropVecChainGhost
  blkPC_2 blkPl_2 blkPC_3 blkPl_3
)
open CryptoVerification.LibsignalTripleRatchet.Getters.DropGlueFacts (
  slt_one_iff_eq_zero vecAt_expose_loop mkHeadersAt mkHeadersAt_entails_memRegion_104
  ofNat_succ_eq_add_one ofNat_beq_zero_false ofNat_add_one_beq_one_false
  tail_len_mul_lt cons_len_mul add_104_add_48
  sep_pull_body sep_push_body sep_rejoin_loop post_loop_weaken
  chainOuterHeadersAt chainOuterHeadersAt_entails_memRegions chain_memRegions_entails_104
)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost
)
open Proofs.libsignal.Stage1X (lscall_of_withLsCl)
open Proofs.libsignal.Hooks2 (
  subroutine_ok_withLsCodeLoaded_map'
  dropVecMessageKeyStackX dropVecChainStackX dropSessionStructureLocal1StackX
  vecPinDeallocX ckDeallocX sgnPinDeallocX
  layoutOk_u8_x layoutOk_mul104_x
  messageKeyAt_entails_deallocX vecGhostAt_entails_pin_deallocX vecU8At_entails_pin_deallocX
  stackAt_dropVecMessageKeyX_split stackAt_dropVecMessageKeyX_split_bottom
  stackAt_dropVecChainX_split stackAt_ss_local1_split_x
  stackAt_dropVecChainX_split_alloc stackAt_dropVecChainX_split_mk
  stackAt_dropVecMessageKeyX_split_alloc
  cap0_weaken_48_extHook tail_dealloc_pre_weaken_ext tail_dealloc_post_48_extHook
  cap0_weaken_48_vecChain_ext tail_dealloc_vecChain_pre_weaken_ext vecChain_tail_dealloc_post_ext
  Saved32Preserved ssPresQ cap_add_one_ne_zero_x
  ssFirst3HeadersAt ssFirst3_entails_dealloc_x ssFirst3HeadersAt_entails_memRegions_x
  ssTail3HeadersAt ssTail3HeadersAt_entails_memRegions_x
  ssSender1HeadersAt ssSender1HeadersAt_entails_memRegions_x
  ssSender1_memRegions_entails_104_x sender_none_entails_memRegion_104_x
  sessionTail_entails_memRegion_16 session_memRegions_entails_344_x pq_header24_weaken_x
  drop4_strengthen_post_x ssSavedFrame ssPqPart ssTail3Dealloc ssFirst3Mem ss9MemRegions
  ss_epilogue_pure_extract tail_dealloc_ss_local1_pre_weaken_ext tail_stack_128_from_bottom_ext
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustLayoutOk VmPreserved
  rustDeallocEvents RustCliAllocBudget
)
open LibsignalBinary.Heap.IfaceBudgetLemmas (rustCliDeallocNoOomExternSpecWithStack)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.FineCredit (
  HasFineReallocCredit
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.Potential (
  bytesLargeLive bytesLargeLive_zero vec104LargeLive vec104LargeLive_zero
  stepEvents_free_bytes stepEvents_free_vec104
  sgnCapLargeLive messageKeyLargeLive chainPairLargeLive chainGhostLargeLive
  senderChainLargeLive optTailVecLargeLive ssStateLargeLive ssLargeLive ssClonePeakLarge
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift (
  AllocContractsBudgetPlaced rustLayoutOk_of_layoutOk
  trapHooks sepWP_rebase_vmPreserved sepWP_seq_vmPreserved sepWP_seq_lscl_vm
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.GrowOne104Budget (
  dealloc_extern_of_budgetPlaced
)

/-- Compatibility alias for `DropSessionStructureGhost`. -/
abbrev DropSessionStructureLocal1Ghost := DropSessionStructureGhost

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local simp, local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero

private meta def collectAppArgsModMData : Lean.Expr → List Lean.Expr → Lean.Expr × List Lean.Expr
  | .mdata _ e, acc => collectAppArgsModMData e acc
  | .app f a, acc => collectAppArgsModMData f (a :: acc)
  | e, acc => (e, acc)

private meta def isTrapRebase (arity : Nat) (e : Lean.Expr) : Bool :=
  let (fn, args) := collectAppArgsModMData e []
  fn.isConstOf ``Arm64.Program.rebase &&
    args.length == arity &&
    match args[2]? with
    | some h =>
      h.consumeMData.isConstOf
        ``LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.HookLift.trapHooks
    | none => false

syntax "by_vm_steps_withSvc_dsl " tacticSeq : tactic

elab_rules : tactic
  | `(tactic| by_vm_steps_withSvc_dsl $tac:tacticSeq) => do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let lctx0 ← Lean.MonadLCtx.getLCtx
      let insts0 ← Lean.Meta.getLocalInstances
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      unless ty.getAppFn.isConstOf ``SepWP && ty.getAppNumArgs == 6 do
        throwError "by_vm_steps_withSvc_dsl: expected `SepWP ((P.rebase b trapHooks).withSvc noSyscalls) ...`, got{Lean.indentExpr ty}"
      let e2 := (ty.getArg! 0).consumeMData
      unless e2.getAppFn.isConstOf ``Arm64.Program.withSvc && e2.getAppNumArgs == 2 do
        throwError "by_vm_steps_withSvc_dsl: program is not `Program.withSvc`:{Lean.indentExpr e2}"
      let e1 := (e2.getArg! 0).consumeMData
      let arity := (collectAppArgsModMData e1 []).2.length
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      let mut revInfos : Array (Nat × Lean.MVarId × Lean.Expr) := #[]
      for r in rem do
        if !(← r.isAssigned) then
          let info ← r.withContext do
            let rDecl ← r.getDecl
            let mut newFVars : Array Lean.FVarId := #[]
            for d in rDecl.lctx do
              if !d.isImplementationDetail && !lctx0.contains d.fvarId then
                newFVars := newFVars.push d.fvarId
            let (reverted, rRev) ← r.revert newFVars (preserveOrder := true)
            let revTy0 ← Lean.instantiateMVars (← rRev.getType)
            let revTy := revTy0.replace fun sub =>
              if isTrapRebase arity sub then some e2 else none
            pure (reverted.size, rRev, revTy)
          revInfos := revInfos.push info
      let rec closeWithTmp (idx : Nat) (tmps : Array Lean.Expr) :
          Lean.Elab.Tactic.TacticM (Array Lean.MVarId) := do
        if h : idx < revInfos.size then
          let (_, rRev, revTy) := revInfos[idx]
          Lean.Meta.withLocalDeclD (Lean.Name.num `_vmTmp idx) revTy fun fTmp => do
            rRev.assign fTmp
            closeWithTmp (idx + 1) (tmps.push fTmp)
        else
          let prf1 ← Lean.instantiateMVars g1
          let prf2 := prf1.replace fun sub =>
            if isTrapRebase arity sub then some e2 else none
          let mut freshGoals : Array Lean.MVarId := #[]
          let mut freshExprs : Array Lean.Expr := #[]
          for (nRev, _, revTy) in revInfos do
            let gFresh ← Lean.Meta.mkFreshExprMVarAt lctx0 insts0 revTy
            freshExprs := freshExprs.push gFresh
            let (_, gReintro) ← gFresh.mvarId!.introNP nRev
            freshGoals := freshGoals.push gReintro
          let prf3 := prf2.replace fun sub =>
            match tmps.findIdx? (· == sub) with
            | some j => freshExprs[j]?
            | none => none
          g.assign prf3
          return freshGoals
      let newRem ← closeWithTmp 0 #[]
      Lean.Elab.Tactic.setGoals (newRem.toList ++ savedGoals.tail!)

macro "wp_steps_lscl_vm_s " mid:term " as " hvm:ident hcl:ident : tactic =>
  `(tactic| (
    apply sepWP_seq_lscl_vm ‹_› (mid := $mid)
    by_vm_steps_withSvc_dsl (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident $hcl:ident))

private theorem sepWP_ret_vmPreserved_dsl {P : Program} {b tgt : BitVec 64} {Hk : LibsignalHooks}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    (hwp : SepWP ((P.rebase b trapHooks).withSvc noSyscalls) tgt s Pre
      (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) tgt sm Pm post))) :
    SepWP (P.rebase b Hk) tgt s Pre post :=
  sepWP_seq_vmPreserved (mid := tgt) hwp

macro "wp_steps_to_tgt_vm_s" " as " hvm:ident : tactic =>
  `(tactic| (
    apply sepWP_ret_vmPreserved_dsl
    by_vm_steps_withSvc_dsl (
      wp_steps
      refine SepWP.done (by first | wp_norm_goal | wp_norm_lhs | rfl) (by wp_norm_lhs)
        ⟨by simp only [wp_norm, arm64_norm], ?_⟩)
    intro $hvm:ident))

private theorem seq_clean_lscl_budget [LibsignalPlacement]
    {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {P_mid : State → SepProp}
    {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running → LibsignalCodeLoaded lsmpl sm.mem → Q sm →
      SepWP prog target sm (P_mid sm) post) :
    SepWP prog target s P post := by
  apply CryptoVerification.sepWP_seq_lscl hcl (mid := mid)
  refine SepWP.mono h1 ?_
  rintro sm Pm hpcm hrunm ⟨hent, hQ⟩ hclm
  exact SepWP.weaken_pre hent (h2 sm hpcm hrunm hclm hQ)

private theorem align_pre_budget {prog : Program} {target : BitVec 64} {s : State}
    {P : SepProp} {P_mid : State → SepProp} {Q : State → Prop}
    (heq : P = P_mid s)
    (h : SepWP prog target s (P_mid s) (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm)) :
    SepWP prog target s P (fun sm Pm => (Pm ⊢ P_mid sm) ∧ Q sm) := by
  rw [heq]
  exact h

private theorem sepWP_let_state {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    (P' : State → SepProp) (heq : P = P' s)
    (hwp : SepWP prog tgt s (P' s) post) :
    SepWP prog tgt s P post := by
  rw [heq]
  exact hwp

private theorem weaken_pre_at_state {prog : Program} {tgt : BitVec 64} {s : State}
    {P : SepProp} {post : State → SepProp → Prop}
    {P1 P2 : State → SepProp}
    (hent : ∀ s', P1 s' ⊢ P2 s') (heq : P = P1 s)
    (hwp : SepWP prog tgt s (P2 s) post) :
    SepWP prog tgt s P post := by
  rw [heq]
  exact SepWP.weaken_pre (hent s) hwp


/-! ## 1. Deterministic Drop Event Lists & Deallocation Credit Lemmas -/

/-- Events emitted by dropping one `VecPin` (`cap == 0#64` skips `__rust_dealloc`). -/
def pinFreeEvents (pin : VecPin) : List AllocEvent :=
  if (pin.cap == 0#64) = true then []
  else rustDeallocEvents pin.cap.toNat 1

/-- Events emitted by dropping a signed-niche `cap : BitVec 64` (`cap.slt 1#64` skips dealloc). -/
def sgnCapFreeEvents (cap : BitVec 64) : List AllocEvent :=
  if cap.slt 1#64 = true then []
  else rustDeallocEvents cap.toNat 1

/-- Events emitted by dropping a `Vec<104>` outer buffer (`align = 8`, `cap == 0#64` skips). -/
def vec104FreeEvents (cap : BitVec 64) : List AllocEvent :=
  if (cap == 0#64) = true then []
  else rustDeallocEvents (cap.toNat * 104) 8

/-- Events emitted by one iteration of `drop_glue::<Vec<MessageKey>>` (`cipher`, `mac`, `iv`, `seed`). -/
def mkFreeEvents (pin : MessageKeyGhost) : List AllocEvent :=
  pinFreeEvents pin.cipher ++ pinFreeEvents pin.mac ++
    pinFreeEvents pin.iv ++ pinFreeEvents pin.seed

/-- Events emitted by `drop_glue::<Vec<MessageKey>>` (Block `3`). -/
def dropVecMessageKeyEvents (cap : BitVec 64)
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) : List AllocEvent :=
  (mks.flatMap fun gk => mkFreeEvents gk.1) ++ vec104FreeEvents cap

/-- Deterministic capacity word stored at `chain + 0x48` (`optChainKeyNone` on `none`, `pin.cap` on `some`). -/
def optCkCapVal (pin : VecPin) : Option ChainKey → BitVec 64
  | none => optChainKeyNone
  | some _ => pin.cap

/-- Events emitted by one iteration of `drop_glue::<Vec<Chain>>` (`srk`, `priv`, `ck`, `message_keys`). -/
def chainPairFreeEvents (gc : ChainGhost × ReceiverChain) : List AllocEvent :=
  pinFreeEvents ⟨gc.1.srk.cap, gc.1.srk.ptr⟩ ++
    pinFreeEvents ⟨gc.1.priv.cap, gc.1.priv.ptr⟩ ++
    sgnCapFreeEvents (optCkCapVal gc.1.ck gc.2.chainKey) ++
    dropVecMessageKeyEvents gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys)

/-- Events emitted by `drop_glue::<Vec<Chain>>` (Block `2`). -/
def dropVecChainEvents (cap : BitVec 64)
    (cs : List (ChainGhost × ReceiverChain)) : List AllocEvent :=
  (cs.flatMap chainPairFreeEvents) ++ vec104FreeEvents cap

/-- Deterministic capacity word of `optTailVecAt` (`noneCap` on `none`, `tg.vec.cap` on `some tg`). -/
def optTailCapVal : Option TailVecGhost → BitVec 64
  | none => noneCap
  | some tg => tg.vec.cap

/-- Events emitted by `first3` (`local_identity_public`, `remote_identity_public`, `root_key`). -/
def ssFirst3FreeEvents (G : SessionGhost) : List AllocEvent :=
  pinFreeEvents ⟨G.localIk.cap, G.localIk.ptr⟩ ++
    pinFreeEvents ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ++
    pinFreeEvents G.root

/-- Events emitted by the `sender_chain` drop segment (`+76 → +156`). -/
def senderFreeEvents : Option SenderChainGhost → List AllocEvent
  | none => []
  | some sg =>
    pinFreeEvents ⟨sg.srk.cap, sg.srk.ptr⟩ ++
      pinFreeEvents ⟨sg.priv.cap, sg.priv.ptr⟩ ++
      sgnCapFreeEvents sg.ck.cap ++
      dropVecMessageKeyEvents sg.mkCap []

/-- Events emitted by `tail3` (`pending_pre_key`, `pending_kyber_pre_key`, `alice_base_key`). -/
def ssTail3FreeEvents (G : SessionGhost) : List AllocEvent :=
  sgnCapFreeEvents (optTailCapVal G.pending) ++
    sgnCapFreeEvents (optTailCapVal G.kyber) ++
    pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩

/-- Complete deterministic `AllocEvent` trace of `drop_glue::<SessionStructure> [local#1]` (Block `6`). -/
def dropSessionStructureLocal1Events (G : SessionGhost)
    (st : SessionState (List (BitVec 8))) : List AllocEvent :=
  ssFirst3FreeEvents G ++
    senderFreeEvents G.sender ++
    dropVecChainEvents G.chainsCap (G.chains.zip st.receiverChains) ++
    ssTail3FreeEvents G ++
    pinFreeEvents G.pq

/-- Pure layout invariants extracted non-destructively from `chainAt`. -/
def ChainPairCapsOk (gc : ChainGhost × ReceiverChain) : Prop :=
  gc.1.keys.length = gc.2.messageKeys.length ∧
    ∀ ck, gc.2.chainKey = some ck → gc.1.ck.cap.toNat < 2 ^ 63

/-- List-level `ChainPairCapsOk` extracted from `vecAt ... (chainAt A) ... cs`. -/
def ChainListCapsOk (cs : List (ChainGhost × ReceiverChain)) : Prop :=
  ∀ gc ∈ cs, ChainPairCapsOk gc

/-- Pure capacity bound extracted from `optTailVecAt`. -/
def TailCapOk (opt : Option TailVecGhost) : Prop :=
  ∀ tg, opt = some tg → tg.vec.cap.toNat < 2 ^ 63

/-- Pure layout invariants extracted non-destructively from `sessionStateAt`. -/
def SessionDropCapsOk (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  (∀ sg, G.sender = some sg → sg.ck.cap.toNat < 2 ^ 63) ∧
    ChainListCapsOk (G.chains.zip st.receiverChains) ∧
    TailCapOk G.pending ∧
    TailCapOk G.kyber

private theorem stepEvents_free_seq (M : AllocCostModel) [HasFineReallocCredit M]
    {evs₁ evs₂ : List AllocEvent} {c₁ c₂ : Nat} {st : M.σ}
    (h1 : HasFineReallocCredit.cumSmall (M.stepEvents evs₁ st) ≤ HasFineReallocCredit.cumSmall st ∧
          HasFineReallocCredit.liveLarge (M.stepEvents evs₁ st) ≤ HasFineReallocCredit.liveLarge st - c₁ ∧
          HasFineReallocCredit.peakLarge (M.stepEvents evs₁ st) ≤ HasFineReallocCredit.peakLarge st)
    (h2 : ∀ s1 : M.σ,
          HasFineReallocCredit.cumSmall (M.stepEvents evs₂ s1) ≤ HasFineReallocCredit.cumSmall s1 ∧
          HasFineReallocCredit.liveLarge (M.stepEvents evs₂ s1) ≤ HasFineReallocCredit.liveLarge s1 - c₂ ∧
          HasFineReallocCredit.peakLarge (M.stepEvents evs₂ s1) ≤ HasFineReallocCredit.peakLarge s1) :
    HasFineReallocCredit.cumSmall (M.stepEvents (evs₁ ++ evs₂) st) ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge (M.stepEvents (evs₁ ++ evs₂) st) ≤
      HasFineReallocCredit.liveLarge st - (c₁ + c₂) ∧
    HasFineReallocCredit.peakLarge (M.stepEvents (evs₁ ++ evs₂) st) ≤ HasFineReallocCredit.peakLarge st := by
  rw [M.stepEvents_append]
  have h2' := h2 (M.stepEvents evs₁ st)
  refine ⟨by omega, by omega, by omega⟩

theorem stepEvents_pinFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (pin : VecPin) (st : M.σ) :
    let st' := M.stepEvents (pinFreeEvents pin) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - bytesLargeLive M pin.cap.toNat ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold pinFreeEvents
  by_cases h0 : (pin.cap == 0#64) = true
  · have hc0 : pin.cap = 0#64 := beq_iff_eq.mp h0
    simp only [h0, ↓reduceIte]
    simp only [hc0, BitVec.toNat_ofNat, Nat.zero_mod,
      bytesLargeLive_zero, Nat.sub_zero, AllocCostModel.stepEvents_nil, le_refl, and_self]
  · simp only [h0, ↓reduceIte]
    have hne : pin.cap.toNat ≠ 0 := by
      intro hc
      apply h0
      have heq : pin.cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
      simp [heq]
    exact stepEvents_free_bytes M hne st

theorem stepEvents_sgnCapFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : BitVec 64) (st : M.σ) :
    let st' := M.stepEvents (sgnCapFreeEvents cap) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - sgnCapLargeLive M cap ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold sgnCapFreeEvents sgnCapLargeLive
  by_cases hslt : cap.slt 1#64 = true
  · simp only [hslt, ↓reduceIte, Nat.sub_zero, AllocCostModel.stepEvents_nil, le_refl, and_self]
  · simp only [hslt, ↓reduceIte]
    have hne : cap.toNat ≠ 0 := by
      intro hc
      have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
      subst heq
      exact hslt (by decide)
    exact stepEvents_free_bytes M hne st

theorem stepEvents_vec104FreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : BitVec 64) (st : M.σ) :
    let st' := M.stepEvents (vec104FreeEvents cap) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - vec104LargeLive M cap.toNat ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold vec104FreeEvents
  by_cases h0 : (cap == 0#64) = true
  · have hc0 : cap = 0#64 := beq_iff_eq.mp h0
    simp only [h0, ↓reduceIte]
    simp only [hc0, BitVec.toNat_ofNat, Nat.zero_mod,
      vec104LargeLive_zero, Nat.sub_zero, AllocCostModel.stepEvents_nil, le_refl, and_self]
  · simp only [h0, ↓reduceIte]
    have hne : cap.toNat ≠ 0 := by
      intro hc
      apply h0
      have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [hc]; rfl)
      simp [heq]
    exact stepEvents_free_vec104 M hne st

theorem sgnCapLargeLive_eq_bytesLargeLive_of_lt (M : AllocCostModel) [HasFineReallocCredit M]
    {cap : BitVec 64} (hlt : cap.toNat < 2 ^ 63) :
    sgnCapLargeLive M cap = bytesLargeLive M cap.toNat := by
  unfold sgnCapLargeLive
  simp only [slt_one_iff_eq_zero hlt]
  by_cases hc : cap = 0
  · simp only [hc, ↓reduceIte]
    have hz : (0 : BitVec 64).toNat = 0 := rfl
    rw [hz, bytesLargeLive_zero]
  · simp only [hc, ↓reduceIte]

theorem stepEvents_mkFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (pin : MessageKeyGhost) (st : M.σ) :
    let st' := M.stepEvents (mkFreeEvents pin) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - messageKeyLargeLive M pin ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  unfold mkFreeEvents messageKeyLargeLive
  have h12 := stepEvents_free_seq M (stepEvents_pinFreeEvents_bounds M pin.cipher st)
    (stepEvents_pinFreeEvents_bounds M pin.mac)
  have h123 := stepEvents_free_seq M h12 (stepEvents_pinFreeEvents_bounds M pin.iv)
  exact stepEvents_free_seq M h123 (stepEvents_pinFreeEvents_bounds M pin.seed)

theorem stepEvents_mkListFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (mks : List (MessageKeyGhost × MessageKeyGenerator)) (st : M.σ) :
    let st' := M.stepEvents (mks.flatMap fun gk => mkFreeEvents gk.1) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - (mks.map fun gk => messageKeyLargeLive M gk.1).sum ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  induction mks generalizing st with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, Nat.sub_zero,
      AllocCostModel.stepEvents_nil, le_refl, and_self]
  | cons gk tl ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    exact stepEvents_free_seq M (stepEvents_mkFreeEvents_bounds M gk.1 st) ih

theorem stepEvents_dropVecMessageKey_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : BitVec 64) (mks : List (MessageKeyGhost × MessageKeyGenerator)) (st : M.σ) :
    let st' := M.stepEvents (dropVecMessageKeyEvents cap mks) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st -
        ((mks.map fun gk => messageKeyLargeLive M gk.1).sum + vec104LargeLive M cap.toNat) ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st :=
  stepEvents_free_seq M (stepEvents_mkListFreeEvents_bounds M mks st)
    (stepEvents_vec104FreeEvents_bounds M cap)

private theorem map_fst_zip_eq {α β γ : Type} (f : α → γ) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      ((xs.zip ys).map fun xy => f xy.1) = xs.map f
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | x :: xs, _ :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zip_cons_cons, List.map_cons, map_fst_zip_eq f xs ys h]

private def optCkLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    (pin : VecPin) : Option ChainKey → Nat
  | none => 0
  | some _ => bytesLargeLive M pin.cap.toNat

def optSenderLargeLive (M : AllocCostModel) [HasFineReallocCredit M] :
    Option SenderChainGhost → Nat
  | none => 0
  | some sg => senderChainLargeLive M sg

private theorem chainPairLargeLive_eq_sum (M : AllocCostModel) [HasFineReallocCredit M]
    (gc : ChainGhost × ReceiverChain) :
    chainPairLargeLive M gc =
      bytesLargeLive M gc.1.srk.cap.toNat +
      bytesLargeLive M gc.1.priv.cap.toNat +
      optCkLargeLive M gc.1.ck gc.2.chainKey +
      vec104LargeLive M gc.1.mkCap.toNat +
      (gc.1.keys.map (messageKeyLargeLive M)).sum := by
  unfold chainPairLargeLive optCkLargeLive
  cases gc.2.chainKey <;> rfl

private theorem ssStateLargeLive_eq_sum (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    ssStateLargeLive M G st =
      bytesLargeLive M G.localIk.cap.toNat +
      bytesLargeLive M G.remoteIk.cap.toNat +
      bytesLargeLive M G.root.cap.toNat +
      optSenderLargeLive M G.sender +
      vec104LargeLive M G.chainsCap.toNat +
      ((G.chains.zip st.receiverChains).map (chainPairLargeLive M)).sum +
      optTailVecLargeLive M G.pending +
      optTailVecLargeLive M G.kyber +
      bytesLargeLive M G.alice.cap.toNat +
      bytesLargeLive M G.pq.cap.toNat := by
  unfold ssStateLargeLive optSenderLargeLive
  cases G.sender <;> rfl

private theorem sgnCapLargeLive_optCkCapVal_eq (M : AllocCostModel) [HasFineReallocCredit M]
    {pin : VecPin} {ck : Option ChainKey}
    (hok : ∀ c, ck = some c → pin.cap.toNat < 2 ^ 63) :
    sgnCapLargeLive M (optCkCapVal pin ck) = optCkLargeLive M pin ck := by
  cases ck with
  | none =>
    unfold optCkCapVal optCkLargeLive sgnCapLargeLive
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte]
  | some c =>
    unfold optCkCapVal optCkLargeLive
    exact sgnCapLargeLive_eq_bytesLargeLive_of_lt M (hok c rfl)

theorem stepEvents_chainPairFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {gc : ChainGhost × ReceiverChain} (hok : ChainPairCapsOk gc) (st : M.σ) :
    let st' := M.stepEvents (chainPairFreeEvents gc) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - chainPairLargeLive M gc ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold chainPairFreeEvents
  have h12 := stepEvents_free_seq M (stepEvents_pinFreeEvents_bounds M ⟨gc.1.srk.cap, gc.1.srk.ptr⟩ st)
    (stepEvents_pinFreeEvents_bounds M ⟨gc.1.priv.cap, gc.1.priv.ptr⟩)
  have h123 := stepEvents_free_seq M h12
    (stepEvents_sgnCapFreeEvents_bounds M (optCkCapVal gc.1.ck gc.2.chainKey))
  have h1234 := stepEvents_free_seq M h123
    (stepEvents_dropVecMessageKey_bounds M gc.1.mkCap (gc.1.keys.zip gc.2.messageKeys))
  dsimp only at h1234
  rw [sgnCapLargeLive_optCkCapVal_eq M hok.2,
      map_fst_zip_eq (messageKeyLargeLive M) gc.1.keys gc.2.messageKeys hok.1] at h1234
  rw [chainPairLargeLive_eq_sum]
  rcases h1234 with ⟨hc, hl, hp⟩
  exact ⟨hc, by omega, hp⟩

theorem stepEvents_chainListFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {cs : List (ChainGhost × ReceiverChain)} (hok : ChainListCapsOk cs) (st : M.σ) :
    let st' := M.stepEvents (cs.flatMap chainPairFreeEvents) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - (cs.map (chainPairLargeLive M)).sum ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  induction cs generalizing st with
  | nil =>
    simp only [List.flatMap_nil, List.map_nil, List.sum_nil, Nat.sub_zero,
      AllocCostModel.stepEvents_nil, le_refl, and_self]
  | cons gc tl ih =>
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
    have hhd : ChainPairCapsOk gc := hok gc (List.mem_cons_self ..)
    have htl : ChainListCapsOk tl := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    exact stepEvents_free_seq M (stepEvents_chainPairFreeEvents_bounds M hhd st) (ih htl)

theorem stepEvents_dropVecChain_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (cap : BitVec 64) {cs : List (ChainGhost × ReceiverChain)}
    (hok : ChainListCapsOk cs) (st : M.σ) :
    let st' := M.stepEvents (dropVecChainEvents cap cs) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st -
        ((cs.map (chainPairLargeLive M)).sum + vec104LargeLive M cap.toNat) ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st :=
  stepEvents_free_seq M (stepEvents_chainListFreeEvents_bounds M hok st)
    (stepEvents_vec104FreeEvents_bounds M cap)

theorem stepEvents_ssFirst3FreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    (G : SessionGhost) (st : M.σ) :
    let st' := M.stepEvents (ssFirst3FreeEvents G) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st -
        (bytesLargeLive M G.localIk.cap.toNat +
          bytesLargeLive M G.remoteIk.cap.toNat +
          bytesLargeLive M G.root.cap.toNat) ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold ssFirst3FreeEvents
  have h12 := stepEvents_free_seq M (stepEvents_pinFreeEvents_bounds M ⟨G.localIk.cap, G.localIk.ptr⟩ st)
    (stepEvents_pinFreeEvents_bounds M ⟨G.remoteIk.cap, G.remoteIk.ptr⟩)
  have h123 := stepEvents_free_seq M h12 (stepEvents_pinFreeEvents_bounds M G.root)
  dsimp only at h123
  exact h123

theorem stepEvents_senderFreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {senderG : Option SenderChainGhost}
    (hok : ∀ sg, senderG = some sg → sg.ck.cap.toNat < 2 ^ 63) (st : M.σ) :
    let st' := M.stepEvents (senderFreeEvents senderG) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - optSenderLargeLive M senderG ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  cases senderG with
  | none =>
    simp only [senderFreeEvents, optSenderLargeLive, Nat.sub_zero,
      AllocCostModel.stepEvents_nil, le_refl, and_self]
  | some sg =>
    unfold senderFreeEvents optSenderLargeLive senderChainLargeLive
    have h12 := stepEvents_free_seq M (stepEvents_pinFreeEvents_bounds M ⟨sg.srk.cap, sg.srk.ptr⟩ st)
      (stepEvents_pinFreeEvents_bounds M ⟨sg.priv.cap, sg.priv.ptr⟩)
    have h123 := stepEvents_free_seq M h12 (stepEvents_sgnCapFreeEvents_bounds M sg.ck.cap)
    have h1234 := stepEvents_free_seq M h123 (stepEvents_dropVecMessageKey_bounds M sg.mkCap [])
    dsimp only at h1234
    simp only [List.map_nil, List.sum_nil, Nat.zero_add,
      sgnCapLargeLive_eq_bytesLargeLive_of_lt M (hok sg rfl)] at h1234
    rcases h1234 with ⟨hc, hl, hp⟩
    exact ⟨hc, by omega, hp⟩

private theorem sgnCapLargeLive_optTailCapVal_eq (M : AllocCostModel) [HasFineReallocCredit M]
    {opt : Option TailVecGhost} (hok : TailCapOk opt) :
    sgnCapLargeLive M (optTailCapVal opt) = optTailVecLargeLive M opt := by
  cases opt with
  | none =>
    unfold optTailCapVal optTailVecLargeLive sgnCapLargeLive
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [hslt, ↓reduceIte]
  | some tg =>
    unfold optTailCapVal optTailVecLargeLive
    exact sgnCapLargeLive_eq_bytesLargeLive_of_lt M (hok tg rfl)

theorem stepEvents_ssTail3FreeEvents_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} (hp : TailCapOk G.pending) (hk : TailCapOk G.kyber) (st : M.σ) :
    let st' := M.stepEvents (ssTail3FreeEvents G) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st -
        (optTailVecLargeLive M G.pending + optTailVecLargeLive M G.kyber +
          bytesLargeLive M G.alice.cap.toNat) ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold ssTail3FreeEvents
  have h12 := stepEvents_free_seq M
    (stepEvents_sgnCapFreeEvents_bounds M (optTailCapVal G.pending) st)
    (stepEvents_sgnCapFreeEvents_bounds M (optTailCapVal G.kyber))
  have h123 := stepEvents_free_seq M h12
    (stepEvents_pinFreeEvents_bounds M ⟨G.alice.cap, G.alice.ptr⟩)
  dsimp only at h123
  rw [sgnCapLargeLive_optTailCapVal_eq M hp, sgnCapLargeLive_optTailCapVal_eq M hk] at h123
  exact h123

theorem stepEvents_dropSessionStructureLocal1_bounds (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {st_s : SessionState (List (BitVec 8))}
    (hok : SessionDropCapsOk G st_s) (st : M.σ) :
    let st' := M.stepEvents (dropSessionStructureLocal1Events G st_s) st
    HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
    HasFineReallocCredit.liveLarge st' ≤
      HasFineReallocCredit.liveLarge st - ssStateLargeLive M G st_s ∧
    HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st := by
  dsimp only
  unfold dropSessionStructureLocal1Events
  rcases hok with ⟨hsnd, hchs, hp, hk⟩
  have h12 := stepEvents_free_seq M (stepEvents_ssFirst3FreeEvents_bounds M G st)
    (stepEvents_senderFreeEvents_bounds M hsnd)
  have h123 := stepEvents_free_seq M h12
    (stepEvents_dropVecChain_bounds M G.chainsCap hchs)
  have h1234 := stepEvents_free_seq M h123 (stepEvents_ssTail3FreeEvents_bounds M hp hk)
  have h12345 := stepEvents_free_seq M h1234 (stepEvents_pinFreeEvents_bounds M G.pq)
  rw [ssStateLargeLive_eq_sum]
  rcases h12345 with ⟨hc, hl, hp0⟩
  exact ⟨hc, by omega, hp0⟩

private theorem chainPairLargeLive_eq_chainGhostLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    {gc : ChainGhost × ReceiverChain} (hok : ChainPairCapsOk gc)
    (hnone : gc.2.chainKey = none → gc.1.ck.cap.slt 1#64 = true) :
    chainPairLargeLive M gc = chainGhostLargeLive M gc.1 := by
  rw [chainPairLargeLive_eq_sum]
  unfold chainGhostLargeLive optCkLargeLive
  cases hopt : gc.2.chainKey with
  | none =>
    unfold sgnCapLargeLive
    simp only [hnone hopt, ↓reduceIte]
  | some ck =>
    rw [sgnCapLargeLive_eq_bytesLargeLive_of_lt M (hok.2 ck hopt)]

private theorem map_chainPairLargeLive_eq (M : AllocCostModel) [HasFineReallocCredit M] :
    ∀ (gs : List ChainGhost) (cs : List ReceiverChain),
      gs.length = cs.length →
      ChainListCapsOk (gs.zip cs) →
      (∀ gc ∈ gs.zip cs, gc.2.chainKey = none → gc.1.ck.cap.slt 1#64 = true) →
      ((gs.zip cs).map (chainPairLargeLive M)).sum =
        (gs.map (chainGhostLargeLive M)).sum
  | [], _, _, _, _ => rfl
  | _ :: _, [], hlen, _, _ => by simp at hlen
  | g :: gs, c :: cs, hlen, hok, hnone => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have hhd_ok : ChainPairCapsOk (g, c) := hok (g, c) (List.mem_cons_self ..)
    have hhd_none : (g, c).2.chainKey = none → (g, c).1.ck.cap.slt 1#64 = true :=
      hnone (g, c) (List.mem_cons_self ..)
    have htl_ok : ChainListCapsOk (gs.zip cs) := fun x hx => hok x (List.mem_cons_of_mem _ hx)
    have htl_none : ∀ gc ∈ gs.zip cs, gc.2.chainKey = none → gc.1.ck.cap.slt 1#64 = true :=
      fun x hx => hnone x (List.mem_cons_of_mem _ hx)
    rw [chainPairLargeLive_eq_chainGhostLargeLive M hhd_ok hhd_none,
        map_chainPairLargeLive_eq M gs cs hlen htl_ok htl_none]

theorem ssStateLargeLive_eq_ssLargeLive (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {st_s : SessionState (List (BitVec 8))}
    (hlen : G.chains.length = st_s.receiverChains.length)
    (hok : ChainListCapsOk (G.chains.zip st_s.receiverChains))
    (hnone : ∀ gc ∈ G.chains.zip st_s.receiverChains,
      gc.2.chainKey = none → gc.1.ck.cap.slt 1#64 = true) :
    ssStateLargeLive M G st_s = ssLargeLive M G := by
  unfold ssStateLargeLive ssLargeLive
  rw [map_chainPairLargeLive_eq M G.chains st_s.receiverChains hlen hok hnone]

/-! ## 2. Non-Destructive Invariant Extraction & Deterministic Exposure Lemmas -/

private theorem vecU8At_entails_cap_lt (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ ⌜cap.toNat < 2 ^ 63⌝ ∗ vecU8At A v cap ptr bs := by
  unfold vecU8At
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  intro h
  exact Entails.pure_right h.2.1 (Entails.pure_right h (Entails.refl _))

private theorem optChainKeyAt_entails_capOk (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ⌜∀ c, ck = some c → pin.cap.toNat < 2 ^ 63⌝ ∗ optChainKeyAt A pin ck a := by
  cases ck with
  | none =>
    exact Entails.pure_right (fun _ h => nomatch h) (Entails.refl _)
  | some c =>
    unfold optChainKeyAt
    refine Entails.trans
      (sepConj_mono_left (vecU8At_entails_cap_lt A a pin.cap pin.ptr (keyToBytes32 c.key))) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left
    intro hlt
    exact Entails.pure_right (fun _ _ => hlt) (Entails.refl _)

private theorem chainAt_entails_capsOk (A : RustAlloc) (gc : ChainGhost × ReceiverChain)
    (a : BitVec 64) :
    chainAt A gc a ⊢ ⌜ChainPairCapsOk gc⌝ ∗ chainAt A gc a := by
  unfold chainAt
  apply Entails.pure_left
  intro hp
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (optChainKeyAt_entails_capOk A gc.1.ck gc.2.chainKey _)))) ?_
  have hpull :
      (vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
          (gc.1.keys.zip gc.2.messageKeys) ∗
        (⌜∀ c, gc.2.chainKey = some c → gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64))) =
      ⌜∀ c, gc.2.chainKey = some c → gc.1.ck.cap.toNat < 2 ^ 63⌝ ∗
        (vecGhostAt A gc.1.srk a ∗ vecGhostAt A gc.1.priv (a + 24#64) ∗
          vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
            (gc.1.keys.zip gc.2.messageKeys) ∗
          optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64)) := by sep_ac_rfl
  change _ ⊢ ⌜ChainPairCapsOk gc⌝ ∗ (⌜_⌝ ∗ (vecGhostAt A gc.1.srk a ∗ _))
  rw [hpull]
  apply Entails.pure_left
  intro hck
  exact Entails.pure_right ⟨hp.2.2.1, hck⟩ (Entails.pure_right hp (Entails.refl _))

private theorem arrayAt_chainAt_entails_capsOk (A : RustAlloc) :
    ∀ (cs : List (ChainGhost × ReceiverChain)) (ptr : BitVec 64),
      arrayAt (chainAt A) 104 ptr cs ⊢
        ⌜ChainListCapsOk cs⌝ ∗ arrayAt (chainAt A) 104 ptr cs
  | [], _ =>
    Entails.pure_right (fun _ h => nomatch h) (Entails.refl _)
  | gc :: tl, ptr => by
    unfold arrayAt
    refine Entails.trans
      (sepConj_mono (chainAt_entails_capsOk A gc ptr)
        (arrayAt_chainAt_entails_capsOk A tl (ptr + 104#64))) ?_
    have hpull :
        (⌜ChainPairCapsOk gc⌝ ∗ chainAt A gc ptr) ∗
          (⌜ChainListCapsOk tl⌝ ∗ arrayAt (chainAt A) 104 (ptr + 104#64) tl) =
        ⌜ChainPairCapsOk gc⌝ ∗ ⌜ChainListCapsOk tl⌝ ∗
          (chainAt A gc ptr ∗ arrayAt (chainAt A) 104 (ptr + 104#64) tl) := by sep_ac_rfl
    change _ ⊢ ⌜ChainListCapsOk (gc :: tl)⌝ ∗ (chainAt A gc ptr ∗ arrayAt (chainAt A) 104 (ptr + 104#64) tl)
    rw [hpull]
    apply Entails.pure_left
    intro hhd
    apply Entails.pure_left
    intro htl
    refine Entails.pure_right ?_ (Entails.refl _)
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hhd
    · exact htl x hmem

theorem vecAt_chainAt_entails_capsOk (A : RustAlloc) (v cap ptr : BitVec 64)
    (cs : List (ChainGhost × ReceiverChain)) :
    vecAt A 104 8 (chainAt A) v cap ptr cs ⊢
      ⌜ChainListCapsOk cs⌝ ∗ vecAt A 104 8 (chainAt A) v cap ptr cs := by
  unfold vecAt CryptoVerification.RustHeap.vecBuf
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  intro hbuf
  by_cases hc : cap = 0
  · subst hc
    have h0 : cs.length = 0 := by
      have hle := hbuf.1
      have hz : (0 : BitVec 64).toNat = 0 := rfl
      rw [hz] at hle
      omega
    have hnil : cs = [] := List.eq_nil_of_length_eq_zero h0
    subst hnil
    exact Entails.pure_right (fun _ h => nomatch h) (Entails.pure_right hbuf (Entails.refl _))
  · simp only [hc, ↓reduceIte]
    refine Entails.trans
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
        (arrayAt_chainAt_entails_capsOk A cs ptr)))) ?_
    have hpull :
        vecHeader v cap ptr (BitVec.ofNat 64 cs.length) ∗
          (A.live ptr (cap.toNat * 104) 8 ∗
            (⌜ChainListCapsOk cs⌝ ∗ arrayAt (chainAt A) 104 ptr cs) ∗
            memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) =
        ⌜ChainListCapsOk cs⌝ ∗
          (vecHeader v cap ptr (BitVec.ofNat 64 cs.length) ∗
            (A.live ptr (cap.toNat * 104) 8 ∗ arrayAt (chainAt A) 104 ptr cs ∗
              memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104))) := by
      sep_ac_rfl
    rw [hpull]
    apply Entails.pure_left
    intro hcs
    exact Entails.pure_right hcs (Entails.pure_right hbuf (Entails.refl _))

private theorem optTailVecAt_entails_capOk (A : RustAlloc) (size : Nat)
    (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢ ⌜TailCapOk opt⌝ ∗ optTailVecAt A size a opt := by
  cases opt with
  | none =>
    exact Entails.pure_right (fun _ h => nomatch h) (Entails.refl _)
  | some tg =>
    unfold optTailVecAt vecGhostAt
    apply Entails.pure_left
    intro htail
    refine Entails.trans
      (sepConj_mono_left (vecU8At_entails_cap_lt A a tg.vec.cap tg.vec.ptr tg.vec.bytes)) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left
    intro hlt
    exact Entails.pure_right (fun _ h => by cases h; exact hlt)
      (Entails.pure_right htail (Entails.refl _))

private theorem optSenderChainAt_entails_capOk (A : RustAlloc) (a : BitVec 64)
    (senderG : Option SenderChainGhost) (senderSt : Option SenderChain) :
    optSenderChainAt A a senderG senderSt ⊢
      ⌜∀ sg, senderG = some sg → sg.ck.cap.toNat < 2 ^ 63⌝ ∗
        optSenderChainAt A a senderG senderSt := by
  cases senderG with
  | none =>
    exact Entails.pure_right (fun _ h => nomatch h) (Entails.refl _)
  | some sg =>
    cases senderSt with
    | none =>
      change ⌜False⌝ ⊢ _
      rw [← sepConj_emp (⌜False⌝ : SepProp)]
      exact Entails.pure_left False.elim
    | some sc =>
      unfold optSenderChainAt
      apply Entails.pure_left
      intro hp
      refine Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (optChainKeyAt_entails_capOk A sg.ck (some sc.chainKey) _)))) ?_
      have hpull :
          (vecGhostAt A sg.srk a ∗ vecGhostAt A sg.priv (a + 24#64) ∗
            vecAt A 104 8 (messageKeyAt A) (a + 48#64) sg.mkCap sg.mkPtr [] ∗
            (⌜∀ c, some sc.chainKey = some c → sg.ck.cap.toNat < 2 ^ 63⌝ ∗
              optChainKeyAt A sg.ck (some sc.chainKey) (a + 72#64))) =
          ⌜∀ c, some sc.chainKey = some c → sg.ck.cap.toNat < 2 ^ 63⌝ ∗
            (vecGhostAt A sg.srk a ∗ vecGhostAt A sg.priv (a + 24#64) ∗
              vecAt A 104 8 (messageKeyAt A) (a + 48#64) sg.mkCap sg.mkPtr [] ∗
              optChainKeyAt A sg.ck (some sc.chainKey) (a + 72#64)) := by sep_ac_rfl
      change _ ⊢ ⌜_⌝ ∗ (⌜_⌝ ∗ (vecGhostAt A sg.srk a ∗ _))
      rw [hpull]
      apply Entails.pure_left
      intro hck
      exact Entails.pure_right
        (fun sg' h => by cases h; exact hck sc.chainKey rfl)
        (Entails.pure_right hp (Entails.refl _))

theorem optChainKeyAt_entails_det_dealloc (A : RustAlloc) (pin : VecPin)
    (ck : Option ChainKey) (a : BitVec 64) :
    optChainKeyAt A pin ck a ⊢
      ∃∗ ptr : BitVec 64,
        (a ↦₆₄ optCkCapVal pin ck) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 16 ∗
        ckDeallocX A (optCkCapVal pin ck) ptr := by
  cases ck with
  | none =>
    unfold optChainKeyAt optCkCapVal
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
          (b' := a + 16#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro ptr
    refine Entails.sepExists_right ptr ?_
    have hslt : optChainKeyNone.slt 1#64 = true := by decide
    simp only [ckDeallocX, hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some c =>
    unfold optChainKeyAt optCkCapVal
    have hvec : vecU8At A a pin.cap pin.ptr (keyToBytes32 c.key) ⊢
        (a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ckDeallocX A pin.cap pin.ptr := by
      refine Entails.trans (vecU8At_entails_dealloc A a pin.cap pin.ptr (keyToBytes32 c.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left
      rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader ckDeallocX
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      by_cases hc : pin.cap = 0
      · simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
        exact Entails.refl _
      · have hfalse : (pin.cap = 0) = False := eq_false hc
        have hslt_false : (pin.cap.slt 1#64 = true) = False := by
          apply eq_false; rw [slt_one_iff_eq_zero hcap_lt]; exact hc
        simp only [hfalse, hslt_false, ↓reduceIte]
        exact Entails.trans (Entails.pure_right hcap_lt (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl))
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right pin.ptr ?_
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4) ⊢
          memRegion (a + 16#64) 16 := by
      rw [ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
            (b' := a + 24#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := a + 24#64) (n := 4) (k := 4)
            (b' := a + 28#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
    have hgroup :
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
          ckDeallocX A pin.cap pin.ptr) ∗
        ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4 =
        ((a ↦₆₄ pin.cap) ∗ ((a + 8#64) ↦₆₄ pin.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 c.key).length) ∗
           ((a + 24#64) ↦₃₂ c.index) ∗ memRegion (a + 28#64) 4)) ∗
        ckDeallocX A pin.cap pin.ptr := by sep_ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right h16))) ?_
    exact Entails.of_eq (by sep_ac_rfl)

theorem chainAt_entails_det_dealloc (A : RustAlloc) (a : BitVec 64)
    (g : ChainGhost) (c : ReceiverChain) :
    chainAt A (g, c) a ⊢
      ∃∗ ckPtr : BitVec 64,
        chainOuterHeadersAt a g (optCkCapVal g.ck c.chainKey) ckPtr ∗
        vecPinDeallocX A ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A (optCkCapVal g.ck c.chainKey) ckPtr ∗
        vecAt A 104 8 (messageKeyAt A) (a + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) := by
  unfold chainAt chainOuterHeadersAt
  apply Entails.pure_left
  intro _
  have h1 := vecGhostAt_entails_pin_deallocX A g.srk a
  have h2 := vecGhostAt_entails_pin_deallocX A g.priv (a + 24#64)
  have h3 := optChainKeyAt_entails_det_dealloc A g.ck c.chainKey (a + 72#64)
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  have hc1 : (a + 72#64) + 8#64 = a + 80#64 := by bv_omega
  have hc2 : (a + 72#64) + 16#64 = a + 88#64 := by bv_omega
  rw [ha1, ha2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro ckPtr
  refine Entails.sepExists_right ckPtr ?_
  exact Entails.of_eq (by sep_ac_rfl)

theorem optTailVecAt_entails_det_dealloc (A : RustAlloc) (size : Nat)
    (hsz24 : 24 ≤ size) (hsz64 : size ≤ 64) (a : BitVec 64) (opt : Option TailVecGhost) :
    optTailVecAt A size a opt ⊢
      ∃∗ ptr : BitVec 64,
        (a ↦₆₄ optTailCapVal opt) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) (size - 16) ∗
        sgnPinDeallocX A (optTailCapVal opt) ptr := by
  cases opt with
  | none =>
    unfold optTailVecAt optTailCapVal
    have hsplit : size - 8 = 8 + (size - 16) := by omega
    rw [hsplit,
        ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := size - 16)
          (b' := a + 16#64) rfl (by bv_omega) (by omega),
        ProofLib.memRegion_eight (a + 8#64),
        sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim
    intro ptr
    refine Entails.sepExists_right ptr ?_
    have hslt : noneCap.slt 1#64 = true := by decide
    simp only [sgnPinDeallocX, ckDeallocX, hslt, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some g =>
    unfold optTailVecAt optTailCapVal
    apply Entails.pure_left
    intro htail
    have hvec : vecGhostAt A g.vec a ⊢
        (a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          sgnPinDeallocX A g.vec.cap g.vec.ptr := by
      unfold vecGhostAt
      refine Entails.trans (vecU8At_entails_dealloc A a g.vec.cap g.vec.ptr g.vec.bytes) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left
      rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader sgnPinDeallocX ckDeallocX
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      by_cases hc : g.vec.cap = 0
      · simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]
        exact Entails.refl _
      · have hfalse : (g.vec.cap = 0) = False := eq_false hc
        have hslt_false : (g.vec.cap.slt 1#64 = true) = False := by
          apply eq_false; rw [slt_one_iff_eq_zero hcap_lt]; exact hc
        simp only [hfalse, hslt_false, ↓reduceIte]
        exact Entails.trans (Entails.pure_right hcap_lt (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl))
    refine Entails.trans (sepConj_mono_left hvec) ?_
    refine Entails.sepExists_right g.vec.ptr ?_
    have h16 :
        (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ⊢
          memRegion (a + 16#64) (size - 16) := by
      have hsplit : size - 16 = 8 + (size - 24) := by omega
      rw [hsplit,
          ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := size - 24)
            (b' := a + 24#64) rfl (by bv_omega) (by omega)]
      apply sepConj_mono (pointsTo64_entails_memRegion _ _)
      have hb := pointsToBytes_entails_memRegion (a + 24#64) g.tail
      rwa [htail] at hb
    have hpull1 :
        (((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗
          sgnPinDeallocX A g.vec.cap g.vec.ptr) ∗
          ((a + 24#64) ↦ₛ g.tail)) =
        ((a ↦₆₄ g.vec.cap) ∗ ((a + 8#64) ↦₆₄ g.vec.ptr) ∗
          (((a + 16#64) ↦₆₄ BitVec.ofNat 64 g.vec.bytes.length) ∗ ((a + 24#64) ↦ₛ g.tail)) ∗
          sgnPinDeallocX A g.vec.cap g.vec.ptr) := by sep_ac_rfl
    rw [hpull1]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16))

theorem ssTail3_entails_det_dealloc (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost) :
    optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
    ∃∗ pPtr : BitVec 64, ∃∗ kPtr : BitVec 64,
      ssTail3HeadersAt ss (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr G ∗
      sgnPinDeallocX A (optTailCapVal G.pending) pPtr ∗
      sgnPinDeallocX A (optTailCapVal G.kyber) kPtr ∗
      vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩ := by
  have h1 := optTailVecAt_entails_det_dealloc A 48 (by decide) (by decide) (ss + 248#64) G.pending
  have h2 := optTailVecAt_entails_det_dealloc A 32 (by decide) (by decide) (ss + 296#64) G.kyber
  have h3 := vecGhostAt_entails_pin_deallocX A G.alice (ss + 96#64)
  have hofs : ((ss + 248#64) + 8#64 = ss + 256#64) ∧ ((ss + 248#64) + 16#64 = ss + 264#64) ∧
      ((ss + 296#64) + 8#64 = ss + 304#64) ∧ ((ss + 296#64) + 16#64 = ss + 312#64) ∧
      ((ss + 96#64) + 8#64 = ss + 104#64) ∧ ((ss + 96#64) + 16#64 = ss + 112#64) := by
    and_intros <;> bv_omega
  rcases hofs with ⟨ha1, ha2, hb1, hb2, hc1, hc2⟩
  rw [ha1, ha2] at h1
  rw [hb1, hb2] at h2
  rw [hc1, hc2] at h3
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 h3)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim
  intro pPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim
  intro kPtr
  refine Entails.sepExists_right pPtr (Entails.sepExists_right kPtr ?_)
  unfold ssTail3HeadersAt
  exact Entails.of_eq (by sep_ac_rfl)

theorem optSenderChainAt_some_entails_det_ss_local1 (A : RustAlloc) (ss : BitVec 64)
    (sg : SenderChainGhost) (sc : SenderChain) :
    optSenderChainAt A (ss + 144#64) (some sg) (some sc) ⊢
      ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
      (ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
        vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
        vecPinDeallocX A ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
        sgnPinDeallocX A sg.ck.cap sg.ck.ptr) ∗
      vecAt A 104 8 (messageKeyAt A) (ss + 192#64) sg.mkCap sg.mkPtr [] := by
  unfold optSenderChainAt
  apply Entails.pure_left
  rintro ⟨_, _, _, _⟩
  have h1 : vecGhostAt A sg.srk (ss + 144#64) ⊢
      ⌜sg.srk.cap + 1#64 ≠ 0#64⌝ ∗
      ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
      memRegion (ss + 160#64) 8 ∗
      vecPinDeallocX A ⟨sg.srk.cap, sg.srk.ptr⟩ := by
    unfold vecGhostAt
    refine Entails.trans
      (vecU8At_entails_dealloc A (ss + 144#64) sg.srk.cap sg.srk.ptr sg.srk.bytes) ?_
    rw [sepConj_pure_left_comm]
    apply Entails.pure_left
    rintro ⟨_, hcap_lt, _⟩
    refine Entails.pure_right (cap_add_one_ne_zero_x hcap_lt) ?_
    unfold vecHeader vecPinDeallocX
    have hbeq : ((sg.srk.cap == 0#64) = true) ↔ sg.srk.cap = 0 := beq_iff_eq
    simp only [hbeq]
    rw [show (ss + 144#64) + 8#64 = ss + 152#64 by bv_omega,
        show (ss + 144#64) + 16#64 = ss + 160#64 by bv_omega]
    have hgroup1 :
        (((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
          ((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length)) ∗
          (if sg.srk.cap = 0 then emp
           else A.live sg.srk.ptr sg.srk.cap.toNat 1 ∗
             memRegion sg.srk.ptr sg.srk.cap.toNat) =
        ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
          (((ss + 160#64) ↦₆₄ BitVec.ofNat 64 sg.srk.bytes.length) ∗
            (if sg.srk.cap = 0 then emp
             else A.live sg.srk.ptr sg.srk.cap.toNat 1 ∗
               memRegion sg.srk.ptr sg.srk.cap.toNat)) := by sep_ac_rfl
    have hgroup2 :
        ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
          memRegion (ss + 160#64) 8 ∗
          (if sg.srk.cap = 0 then emp
           else ⌜sg.srk.cap.toNat < 2 ^ 63⌝ ∗
             (A.live sg.srk.ptr sg.srk.cap.toNat 1 ∗
               memRegion sg.srk.ptr sg.srk.cap.toNat)) =
        ((ss + 144#64) ↦₆₄ sg.srk.cap) ∗ ((ss + 152#64) ↦₆₄ sg.srk.ptr) ∗
          (memRegion (ss + 160#64) 8 ∗
            (if sg.srk.cap = 0 then emp
             else ⌜sg.srk.cap.toNat < 2 ^ 63⌝ ∗
               (A.live sg.srk.ptr sg.srk.cap.toNat 1 ∗
                 memRegion sg.srk.ptr sg.srk.cap.toNat))) := by sep_ac_rfl
    rw [hgroup1, hgroup2]
    refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
    by_cases hc : sg.srk.cap = 0
    · simp only [hc, ite_true]; exact Entails.refl _
    · simp only [hc, ite_false]; exact Entails.pure_right hcap_lt (Entails.refl _)
  have h2 := vecGhostAt_entails_pin_deallocX A sg.priv (ss + 168#64)
  have h3 : optChainKeyAt A sg.ck (some sc.chainKey) (ss + 216#64) ⊢
      ((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
        memRegion (ss + 232#64) 16 ∗ sgnPinDeallocX A sg.ck.cap sg.ck.ptr := by
    unfold optChainKeyAt
    have hvec : vecU8At A (ss + 216#64) sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key) ⊢
        ((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
          ((ss + 232#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 sc.chainKey.key).length) ∗
          sgnPinDeallocX A sg.ck.cap sg.ck.ptr := by
      refine Entails.trans
        (vecU8At_entails_dealloc A (ss + 216#64) sg.ck.cap sg.ck.ptr (keyToBytes32 sc.chainKey.key)) ?_
      rw [sepConj_pure_left_comm]
      apply Entails.pure_left
      rintro ⟨_, hcap_lt, _⟩
      unfold vecHeader sgnPinDeallocX ckDeallocX
      rw [show (ss + 216#64) + 8#64 = ss + 224#64 by bv_omega,
          show (ss + 216#64) + 16#64 = ss + 232#64 by bv_omega]
      simp only [slt_one_iff_eq_zero hcap_lt, sepConj_assoc]
      by_cases hc : sg.ck.cap = 0
      · simp only [hc, ↓reduceIte, sepConj_emp, emp_sepConj]; exact Entails.refl _
      · have hfalse : (sg.ck.cap = 0) = False := eq_false hc
        have hslt_false : (sg.ck.cap.slt 1#64 = true) = False := by
          apply eq_false; rw [slt_one_iff_eq_zero hcap_lt]; exact hc
        simp only [hfalse, hslt_false, ↓reduceIte]
        exact Entails.trans (Entails.pure_right hcap_lt (Entails.refl _))
          (Entails.of_eq (by sep_ac_rfl))
    refine Entails.trans (sepConj_mono_left hvec) ?_
    have h16 :
        (((ss + 232#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 sc.chainKey.key).length) ∗
          ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4) ⊢
          memRegion (ss + 232#64) 16 := by
      rw [ProofLib.memRegion_split' (b := ss + 232#64) (n := 8) (k := 8)
            (b' := ss + 240#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := ss + 240#64) (n := 4) (k := 4)
            (b' := ss + 244#64) rfl (by bv_omega) (by decide)]
      exact sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo32_entails_memRegion _ _))
    rw [show (ss + 216#64) + 24#64 = ss + 240#64 by bv_omega,
        show (ss + 216#64) + 28#64 = ss + 244#64 by bv_omega]
    have hgroup :
        (((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
          ((ss + 232#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 sc.chainKey.key).length) ∗
          sgnPinDeallocX A sg.ck.cap sg.ck.ptr) ∗
        ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4 =
        (((ss + 216#64) ↦₆₄ sg.ck.cap) ∗ ((ss + 224#64) ↦₆₄ sg.ck.ptr) ∗
          (((ss + 232#64) ↦₆₄ BitVec.ofNat 64 (keyToBytes32 sc.chainKey.key).length) ∗
           ((ss + 240#64) ↦₃₂ sc.chainKey.index) ∗ memRegion (ss + 244#64) 4)) ∗
        sgnPinDeallocX A sg.ck.cap sg.ck.ptr := by sep_ac_rfl
    rw [hgroup]
    refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right h16))) ?_
    exact Entails.of_eq (by sep_ac_rfl)
  rw [show (ss + 168#64) + 8#64 = ss + 176#64 by bv_omega,
      show (ss + 168#64) + 16#64 = ss + 184#64 by bv_omega] at h2
  rw [show (ss + 144#64) + 24#64 = ss + 168#64 by bv_omega,
      show (ss + 144#64) + 48#64 = ss + 192#64 by bv_omega,
      show (ss + 144#64) + 72#64 = ss + 216#64 by bv_omega]
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_right h3))) ?_
  unfold ssSender1HeadersAt
  exact Entails.of_eq (by sep_ac_rfl)

theorem sessionStateAt_entails_det_dealloc (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st ⊢
      ⌜SessionDropCapsOk G st⌝ ∗
      ∃∗ pPtr : BitVec 64, ∃∗ kPtr : BitVec 64,
        (ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A G.root) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (ssTail3HeadersAt ss (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr G ∗
          sgnPinDeallocX A (optTailCapVal G.pending) pPtr ∗
          sgnPinDeallocX A (optTailCapVal G.kyber) kPtr ∗
          vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) ∗
        (((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
          memRegion (ss + 136#64) 8 ∗ vecPinDeallocX A G.pq) ∗
        memRegion (ss + 328#64) 16 := by
  unfold sessionStateAt
  apply Entails.pure_left
  rintro ⟨_, _, _, _, hreg, _, _⟩
  have hreord :
      (vecGhostAt A G.localIk ss ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        optSenderChainAt A (ss + 0x90#64) G.sender st.senderChain ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
        ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      ((vecGhostAt A G.localIk ss ∗
          vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
          vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey)) ∗
        optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
        vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
          (G.chains.zip st.receiverChains) ∗
        (optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
          optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
          vecGhostAt A G.alice (ss + 0x60#64)) ∗
        vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
        (((ss + 0x148#64) ↦₃₂ st.sessionVersion) ∗
          ((ss + 0x14c#64) ↦₃₂ st.previousCounter) ∗
          ((ss + 0x150#64) ↦ₛ G.regIds))) := by sep_ac_rfl
  rw [hreord]
  have hsnd_ok := optSenderChainAt_entails_capOk A (ss + 144#64) G.sender st.senderChain
  have hchs_ok := vecAt_chainAt_entails_capsOk A (ss + 72#64) G.chainsCap G.chainsPtr
    (G.chains.zip st.receiverChains)
  have hp_ok := optTailVecAt_entails_capOk A 48 (ss + 0xf8#64) G.pending
  have hk_ok := optTailVecAt_entails_capOk A 32 (ss + 0x128#64) G.kyber
  have h1 := ssFirst3_entails_dealloc_x A ss G st
  have h2 : optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
      optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
      vecGhostAt A G.alice (ss + 0x60#64) ⊢
      ⌜TailCapOk G.pending⌝ ∗ ⌜TailCapOk G.kyber⌝ ∗
      (∃∗ pPtr : BitVec 64, ∃∗ kPtr : BitVec 64,
        ssTail3HeadersAt ss (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr G ∗
        sgnPinDeallocX A (optTailCapVal G.pending) pPtr ∗
        sgnPinDeallocX A (optTailCapVal G.kyber) kPtr ∗
        vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩) := by
    refine Entails.trans (sepConj_mono_left hp_ok) ?_
    rw [sepConj_assoc]
    apply Entails.pure_left
    intro hpv
    refine Entails.trans (sepConj_mono_right (sepConj_mono_left hk_ok)) ?_
    have hpull_k :
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
          ((⌜TailCapOk G.kyber⌝ ∗ optTailVecAt A 32 (ss + 0x128#64) G.kyber) ∗
            vecGhostAt A G.alice (ss + 0x60#64)) =
        ⌜TailCapOk G.kyber⌝ ∗
          (optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
            optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
            vecGhostAt A G.alice (ss + 0x60#64)) := by sep_ac_rfl
    rw [hpull_k]
    apply Entails.pure_left
    intro hkv
    exact Entails.pure_right hpv
      (Entails.pure_right hkv (ssTail3_entails_det_dealloc A ss G))
  have h3 := vecU8At_entails_pin_deallocX A (ss + 120#64) G.pq st.pqRatchetState
  rw [show (ss + 120#64) + 8#64 = ss + 128#64 by bv_omega,
      show (ss + 120#64) + 16#64 = ss + 136#64 by bv_omega] at h3
  have h4 := sessionTail_entails_memRegion_16 ss st.sessionVersion st.previousCounter G.regIds hreg
  refine Entails.trans
    (sepConj_mono h1 (sepConj_mono hsnd_ok (sepConj_mono hchs_ok
      (sepConj_mono h2 (sepConj_mono h3 h4))))) ?_
  set P1 := ssFirst3HeadersAt ss G ∗ vecPinDeallocX A ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
    vecPinDeallocX A ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗ vecPinDeallocX A G.root
  set P2 := optSenderChainAt A (ss + 144#64) G.sender st.senderChain
  set P3 := vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr
    (G.chains.zip st.receiverChains)
  set P4 := ∃∗ pPtr : BitVec 64, ∃∗ kPtr : BitVec 64,
    ssTail3HeadersAt ss (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr G ∗
      sgnPinDeallocX A (optTailCapVal G.pending) pPtr ∗
      sgnPinDeallocX A (optTailCapVal G.kyber) kPtr ∗
      vecPinDeallocX A ⟨G.alice.cap, G.alice.ptr⟩
  set P5 := ((ss + 120#64) ↦₆₄ G.pq.cap) ∗ ((ss + 128#64) ↦₆₄ G.pq.ptr) ∗
    memRegion (ss + 136#64) 8 ∗ vecPinDeallocX A G.pq
  set P6 := memRegion (ss + 328#64) 16
  have hpull_all :
      P1 ∗ (⌜∀ sg, G.sender = some sg → sg.ck.cap.toNat < 2 ^ 63⌝ ∗ P2) ∗
        (⌜ChainListCapsOk (G.chains.zip st.receiverChains)⌝ ∗ P3) ∗
        (⌜TailCapOk G.pending⌝ ∗ ⌜TailCapOk G.kyber⌝ ∗ P4) ∗ P5 ∗ P6 =
      ⌜∀ sg, G.sender = some sg → sg.ck.cap.toNat < 2 ^ 63⌝ ∗
      ⌜ChainListCapsOk (G.chains.zip st.receiverChains)⌝ ∗
      ⌜TailCapOk G.pending⌝ ∗ ⌜TailCapOk G.kyber⌝ ∗
      (P1 ∗ P2 ∗ P3 ∗ P4 ∗ P5 ∗ P6) := by sep_ac_rfl
  rw [hpull_all]
  apply Entails.pure_left; intro hsndv
  apply Entails.pure_left; intro hchsv
  apply Entails.pure_left; intro hpv
  apply Entails.pure_left; intro hkv
  refine Entails.pure_right ⟨hsndv, hchsv, hpv, hkv⟩ ?_
  dsimp only [P4]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pPtr; refine Entails.sepExists_right pPtr ?_
  apply Entails.sepExists_elim; intro kPtr; refine Entails.sepExists_right kPtr ?_
  exact Entails.of_eq (by sep_ac_rfl)

/-! ## 3. Budget-Threaded `drop_glue::<Vec<MessageKey>>` (Block `3`) -/

@[local simp] private theorem repAlloc_live_eq {M : AllocCostModel} (A : RustCliAllocBudget M) :
    A.repAlloc.live = A.live := rfl

@[reducible]
private def Saved48Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧
  s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧
  s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem expose_pin_deallocX_zero_b {A : RustAlloc} {pin : VecPin}
    (hcap : (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin = emp := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_pin_deallocX_b {A : RustAlloc} {pin : VecPin}
    (hcap : ¬ (pin.cap == 0#64) = true) :
    vecPinDeallocX A pin =
      ⌜pin.cap.toNat < 2 ^ 63⌝ ∗ (A.live pin.ptr pin.cap.toNat 1 ∗ memRegion pin.ptr pin.cap.toNat) := by
  unfold vecPinDeallocX; simp [hcap]

private theorem expose_ckDeallocX_zero_b {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr = emp := by
  unfold ckDeallocX; simp [hcap]

private theorem expose_ckDeallocX_ne_b {A : RustAlloc} {ckCap ckPtr : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) :
    ckDeallocX A ckCap ckPtr =
      ⌜ckCap.toNat < 2 ^ 63⌝ ∗ (A.live ckPtr ckCap.toNat 1 ∗ memRegion ckPtr ckCap.toNat) := by
  unfold ckDeallocX; simp [hcap]

private theorem pull_pure4_b {φ : Prop} {H P R1 R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P) ∗ R1) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P ∗ R1) ∗ R2) := by
  sep_ac_rfl

private theorem pull_pure3_b {φ : Prop} {H P R2 : SepProp} :
    (H ∗ (⌜φ⌝ ∗ P)) ∗ R2 = ⌜φ⌝ ∗ ((H ∗ P) ∗ R2) := by
  sep_ac_rfl

private theorem rustLayoutOk_u8_of_ne_zero {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat < 2 ^ 63) :
    RustLayoutOk cap.toNat 1 := by
  apply rustLayoutOk_of_layoutOk (by decide)
  apply layoutOk_u8_x _ hlt
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

private theorem rustLayoutOk_u8_of_not_slt1 {ckCap : BitVec 64}
    (hcap : ¬ ckCap.slt 1#64 = true) (hlt : ckCap.toNat < 2 ^ 63) :
    RustLayoutOk ckCap.toNat 1 := by
  apply rustLayoutOk_of_layoutOk (by decide)
  apply layoutOk_u8_x _ hlt
  intro h0
  have heq : ckCap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  rw [heq] at hcap
  exact hcap (by decide)

private theorem rustLayoutOk_mul104_of_ne_zero {cap : BitVec 64}
    (hcap : ¬ (cap == 0#64) = true) (hlt : cap.toNat * 104 < 2 ^ 63) :
    RustLayoutOk (cap.toNat * 104) 8 := by
  apply rustLayoutOk_of_layoutOk (by decide)
  apply layoutOk_mul104_x _ hlt
  intro h0
  apply hcap
  have heq : cap = 0#64 := BitVec.eq_of_toNat_eq (by rw [h0]; rfl)
  subst heq; rfl

open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-- Budget-threaded contract for `drop_glue::<Vec<MessageKey>>` (Block `3`,
`dropVecMessageKeyStackX = 16,432` B): `onOom := ⌜False⌝`, `onPanic := ⌜False⌝`, leaves `cumSmall`
and `peakLarge` non-increasing, and credits `(x.mks.map (messageKeyLargeLive M ∘ Prod.fst)).sum +
vec104LargeLive M x.cap.toNat` back from `liveLarge`. -/
def dropVecMessageKeyBudgetSpecX [LibsignalPlacement]
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗
      stackAt s.sp dropVecMessageKeyStackX
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents (dropVecMessageKeyEvents x.cap x.mks) st
    ⌜sf.trace = s0.trace ∧
      HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st -
          ((x.mks.map fun gk => messageKeyLargeLive M gk.1).sum +
            vec104LargeLive M x.cap.toNat) ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st⌝ ∗
      memRegion x.v 24 ∗ A.pool lim st' sf ∗ stackAt s0.sp dropVecMessageKeyStackX

set_option maxHeartbeats 800000 in
private theorem drop_vec_message_key_budget_placed_body [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (pin : MessageKeyGhost) (mk : MessageKeyGenerator)
      (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_3).base + 48#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H)
        ((blkPl_3).base + 36#64) s
        (messageKeyAt A.repAlloc (pin, mk) cur ∗ A.pool lim st s ∗
          stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗
            A.pool lim (M.stepEvents (mkFreeEvents pin) st) sm ∗
            stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
  intro cur cnt pin mk st s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre (sepConj_mono_left (messageKeyAt_entails_deallocX A.repAlloc cur pin mk)) ?_
  let st1 := M.stepEvents (pinFreeEvents pin.cipher) st
  let st2 := M.stepEvents (pinFreeEvents pin.mac) st1
  let st3 := M.stepEvents (pinFreeEvents pin.iv) st2
  let st4 := M.stepEvents (pinFreeEvents pin.seed) st3
  have hmk_eq : M.stepEvents (mkFreeEvents pin) st = st4 := by
    unfold mkFreeEvents
    simp only [st1, st2, st3, st4, M.stepEvents_append]
  rw [hmk_eq]
  refine seq_clean_lscl_budget hcl (mid := (blkPl_3).base + 68#64)
    (P_mid := fun sm =>
      (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.mac ∗
        vecPinDeallocX A.repAlloc pin.iv ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
      A.pool lim st1 sm ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
  · by_cases hcap : (pin.cipher.cap == 0#64) = true
    · have hst1 : st1 = st := by dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_zero_b hcap, emp_sepConj]; dsimp only [mkHeadersAt]
      dsimp only [mkHeadersAt]
      wp_steps_to_tgt_vm_s as hvm
      apply SepWP.transport_budgetPool hvm
      refine align_pre_budget (by rw [hst1]; sep_ac_rfl) ?_
      wp_done
    · have hst1 : st1 = M.stepEvents (rustDeallocEvents pin.cipher.cap.toNat 1) st := by
        dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_b hcap, pull_pure4_b]; dsimp only [mkHeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
      apply SepWP.transport_budgetPool hvm_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      simp only [repAlloc_live_eq]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (pin.cipher.ptr, pin.cipher.cap.toNat, 1, st)
      refine align_pre_budget (by rw [hst1, hsp]; dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_budget hcl1 (mid := (blkPl_3).base + 88#64)
      (P_mid := fun sm =>
        (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.iv ∗
          vecPinDeallocX A.repAlloc pin.seed) ∗
        A.pool lim st2 sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
    · by_cases hcap : (pin.mac.cap == 0#64) = true
      · have hst2 : st2 = st1 := by dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_zero_b hcap, emp_sepConj]; dsimp only [mkHeadersAt]
        dsimp only [mkHeadersAt]
        wp_steps_to_tgt_vm_s as hvm
        apply SepWP.transport_budgetPool hvm
        refine align_pre_budget (by rw [hst2]; sep_ac_rfl) ?_
        wp_done
      · have hst2 : st2 = M.stepEvents (rustDeallocEvents pin.mac.cap.toNat 1) st1 := by
          dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_b hcap, pull_pure4_b]; dsimp only [mkHeadersAt]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
        wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
        apply SepWP.transport_budgetPool hvm_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        simp only [repAlloc_live_eq]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (pin.mac.ptr, pin.mac.cap.toNat, 1, st1)
        refine align_pre_budget (by rw [hst2, hsp_1]; dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_budget hcl2 (mid := (blkPl_3).base + 108#64)
        (P_mid := fun sm =>
          (mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
          A.pool lim st3 sm ∗ stackAt fsp extHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) ?_ ?_
      · by_cases hcap : (pin.iv.cap == 0#64) = true
        · have hst3 : st3 = st2 := by dsimp [st3]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_zero_b hcap, emp_sepConj]; dsimp only [mkHeadersAt]
          dsimp only [mkHeadersAt]
          wp_steps_to_tgt_vm_s as hvm
          apply SepWP.transport_budgetPool hvm
          refine align_pre_budget (by rw [hst3]; sep_ac_rfl) ?_
          wp_done
        · have hst3 : st3 = M.stepEvents (rustDeallocEvents pin.iv.cap.toNat 1) st2 := by
            dsimp [st3]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_b hcap, pull_pure4_b]; dsimp only [mkHeadersAt]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
          apply SepWP.transport_budgetPool hvm_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          simp only [repAlloc_live_eq]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (pin.iv.ptr, pin.iv.cap.toNat, 1, st2)
          refine align_pre_budget (by rw [hst3, hsp_2]; dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
          wp_done
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_3).rebase (blkPl_3).base H)
            ((blkPl_3).base + 36#64) s3
            ((mkHeadersAt cur pin ∗ vecPinDeallocX A.repAlloc pin.seed) ∗
              A.pool lim st3 s3 ∗ stackAt fsp extHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ mkHeadersAt cur pin ∗ A.pool lim st4 sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 48#64) := by
          by_cases hcap : (pin.seed.cap == 0#64) = true
          · have hst4 : st4 = st3 := by dsimp [st4]; unfold pinFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_pin_deallocX_zero_b hcap, sepConj_emp]; dsimp only [mkHeadersAt]
            dsimp only [mkHeadersAt]
            wp_steps_to_tgt_vm_s as hvm
            apply SepWP.transport_budgetPool hvm
            refine align_pre_budget (by rw [hst4]; sep_ac_rfl) ?_
            wp_done
          · have hst4 : st4 = M.stepEvents (rustDeallocEvents pin.seed.cap.toNat 1) st3 := by
              dsimp [st4]; unfold pinFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_pin_deallocX_b hcap, pull_pure3_b]; dsimp only [mkHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
            wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
            apply SepWP.transport_budgetPool hvm_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            simp only [repAlloc_live_eq]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (pin.seed.ptr, pin.seed.cap.toNat, 1, st3)
            wp_steps_to_tgt_vm_s as hvm_ret
            apply SepWP.transport_budgetPool hvm_ret
            refine align_pre_budget (by rw [hst4, hsp_3]; dsimp only [mkHeadersAt]; sep_ac_rfl) ?_
            wp_done
        exact SepWP.mono hstep4 fun sm Pm _ _ h =>
          ⟨Entails.trans h.1 (sepConj_mono_left (mkHeadersAt_entails_memRegion_104 cur pin)), h.2⟩


private def dropVecMessageKeyEventsSpecX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecMessageKeyGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.v x.cap x.ptr x.mks ∗
      A.pool lim st s ∗
      stackAt s.sp dropVecMessageKeyStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      A.pool lim (M.stepEvents (dropVecMessageKeyEvents x.cap x.mks) st) sf ∗
      stackAt s0.sp dropVecMessageKeyStackX

set_option maxHeartbeats 800000 in
private theorem drop_vec_message_key_budget_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (MessageKeyGhost × MessageKeyGenerator)) (cur : BitVec 64)
      (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_3).base + 48#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 48#64 →
      SepWP ((blkPC_3).rebase (blkPl_3).base H)
        ((blkPl_3).base + 132#64) s
        (arrayAt (messageKeyAt A.repAlloc) 104 cur rest ∗ A.pool lim st s ∗
          stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗
            A.pool lim (M.stepEvents (rest.flatMap fun gk => mkFreeEvents gk.1) st) sm ∗
            stackAt fsp extHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_message_key_budget_placed_body hdealloc s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨pin, mk⟩
    intro cur st s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    let st1 := M.stepEvents (mkFreeEvents pin) st
    rw [show arrayAt (messageKeyAt A.repAlloc) 104 cur ((pin, mk) :: tl) =
          messageKeyAt A.repAlloc (pin, mk) cur ∗
            arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_budget hcl (mid := (blkPl_3).base + 36#64)
      (hbody cur (BitVec.ofNat 64 ((pin, mk) :: tl).length) pin mk st s
        (arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      have hst_nil : M.stepEvents (((pin, mk) :: []).flatMap fun gk => mkFreeEvents gk.1) st = st1 := by
        simp [st1]
      rw [hst_nil]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx21_4 ⊢
      wp_steps_to_tgt_vm_s as hvm_end
      apply SepWP.transport_budgetPool hvm_end
      wp_done
    | cons hd2 tl2 =>
      have hst_cons :
          M.stepEvents (((pin, mk) :: hd2 :: tl2).flatMap fun gk => mkFreeEvents gk.1) st =
            M.stepEvents ((hd2 :: tl2).flatMap fun gk => mkFreeEvents gk.1) st1 := by
        simp [st1, M.stepEvents_append]
      rw [hst_cons]
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((pin, mk) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx21_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps_lscl_vm_s ((blkPl_3).base + 48#64) as hvm_step hcl_step
      apply SepWP.transport_budgetPool hvm_step
      refine sepWP_let_state
        (fun s_step => arrayAt (messageKeyAt A.repAlloc) 104 (cur + 104#64) (hd2 :: tl2) ∗
          A.pool lim st1 s_step ∗ stackAt fsp extHookStack ∗ (memRegion cur 104 ∗ Frame))
        (by sep_ac_rfl) ?_
      refine SepWP.mono
        (ih (cur + 104#64) st1 _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl hrun4 hcl_step
          ⟨by simp only [wp_norm, arm64_norm]; exact hx23_4,
           by simp only [wp_norm, arm64_norm]; exact hx24_4,
           by simp only [wp_norm, arm64_norm]; exact hx25_4,
           by simp only [wp_norm, arm64_norm]; exact hx26_4,
           by simp only [wp_norm, arm64_norm]; exact hx27_4,
           by simp only [wp_norm, arm64_norm]; exact hx28_4,
           hsp_4, htrace_4, hvregs_4⟩
          (by simp only [wp_norm, arm64_norm]; exact hx19_4)
          (by simp only [wp_norm, arm64_norm]; exact hx20_4)
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm, add_104_add_48])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (pin, mk) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

set_option maxHeartbeats 800000 in
private theorem drop_vec_message_key_events_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base
      (withLsCodeLoaded lsmpl (dropVecMessageKeyEventsSpecX M A lim)) := by
  unfold withLsCodeLoaded dropVecMessageKeyEventsSpecX
  wp_init xpair s0
  obtain ⟨⟨v, cap, ptr, mks⟩, st⟩ := xpair
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hdealloc := dealloc_extern_of_budgetPlaced hA
    (callerProg := (blkPC_3).rebase (blkPl_3).base H)
  have hloop := drop_vec_message_key_budget_placed_loop hdealloc
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecMessageKeyX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (messageKeyAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  let st_loop := M.stepEvents (mks.flatMap fun gk => mkFreeEvents gk.1) st
  refine seq_clean_lscl_budget hcl0 (mid := (blkPl_3).base + 132#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 mks.length) ∗
      memRegion ptr (mks.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (mks.length * 104)) ((cap.toNat - mks.length) * 104)) ∗
      A.pool lim st_loop sm ∗
      stackAt (s0.sp - 48#64) extHookStack ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases mks with
    | nil =>
      have hst0 : st_loop = st := rfl
      rw [hst0]
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps_to_tgt_vm_s as hvm0
      apply SepWP.transport_budgetPool hvm0
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_budget hcl0 (mid := (blkPl_3).base + 48#64)
        (P_mid := fun sm =>
          arrayAt (messageKeyAt A.repAlloc) 104 ptr (hd :: tl) ∗
          A.pool lim st sm ∗ stackAt (s0.sp - 48#64) extHookStack ∗
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                 ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (hd :: tl).length ∧
          sm.readReg64 .x22 = ptr + 48#64)
        ?_ ?_
      · wp_steps_to_tgt_vm_s as hvm0
        apply SepWP.transport_budgetPool hvm0
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
        refine ⟨Entails.of_eq (by sep_ac_rfl),
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
      · intro sm hpcm hrunm hcl_loop ⟨hpresm, hx19m, hx20m, hx21m, hx22m⟩
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align
            (hd :: tl) ptr st sm _
            (List.cons_ne_nil _ _) hlen_lt hpcm hrunm hcl_loop
            hpresm hx19m hx20m hx21m hx22m) ?_
        intro sf Pf _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp [st_loop]; sep_ac_rfl)), h.2⟩
  · intro sm hpcm hrunm hcl_m ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre
      (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr mks.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · have hst' : M.stepEvents (dropVecMessageKeyEvents cap mks) st = st_loop := by
        unfold dropVecMessageKeyEvents vec104FreeEvents
        simp [hcap, st_loop, M.stepEvents_append]
      rw [hst']
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_to_tgt_vm_s as hvm_end
      apply SepWP.transport_budgetPool hvm_end
      refine weaken_pre_at_state
        (fun s' => cap0_weaken_48_extHook (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.pool lim st_loop s') s0.sp
          (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22)
          (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack,
              Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; sep_ac_rfl) ?_
      wp_done
    · have hst' :
          M.stepEvents (dropVecMessageKeyEvents cap mks) st =
            M.stepEvents (rustDeallocEvents (cap.toNat * 104) 8) st_loop := by
        unfold dropVecMessageKeyEvents vec104FreeEvents
        simp [hcap, st_loop, M.stepEvents_append]
      rw [hst']
      simp only [eq_false hcap, ↓reduceIte, repAlloc_live_eq]
      have hlay := rustLayoutOk_mul104_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_tail hcl_tail
      apply SepWP.transport_budgetPool hvm_tail
      have hdealloc0 := lscall_of_withLsCl hdealloc hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine weaken_pre_at_state
        (fun s' => tail_dealloc_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))
          (A.pool lim st_loop s') s0.sp
          (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22)
          (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack,
              Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; sep_ac_rfl) ?_
      dsimp only [Proofs.libsignal.Stage1X.extHookStack, extHookStack]
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8, st_loop)
      refine weaken_pre_at_state
        (fun s' => tail_dealloc_post_48_extHook (s0.readReg64 (Reg.gpr 0#5))
          (A.pool lim (M.stepEvents (rustDeallocEvents (cap.toNat * 104) 8) st_loop) s') s0.sp)
        (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack]) ?_
      wp_done

private theorem drop_vec_message_key_events_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeyEventsSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 3) (drop_vec_message_key_events_placed_ok hA)

theorem drop_vec_message_key_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_3).rebase (blkPl_3).base H)
      (blkPl_3).base
      (withLsCodeLoaded lsmpl (dropVecMessageKeyBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' (drop_vec_message_key_events_placed_ok hA)
    fun ⟨x, st⟩ R s0 hpre => ⟨(x, st), R, hpre, fun sf hpost => ?_⟩
  dsimp only [dropVecMessageKeyEventsSpecX, dropVecMessageKeyBudgetSpecX] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  have hcred := stepEvents_dropVecMessageKey_bounds M x.cap x.mks st
  exact ⟨⟨hpost.1, hcred.1, hcred.2.1, hcred.2.2⟩, hpost.2⟩

theorem drop_vec_message_key_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 3)
      (withLsCl lsmpl (dropVecMessageKeyBudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 3) (drop_vec_message_key_budget_placed_ok hA)

/-! ## 4. Budget-Threaded `drop_glue::<Vec<Chain>>` (Block `2`, calling Block `3`) -/

/-- Budget-threaded contract for `drop_glue::<Vec<Chain>>` (Block `2`,
`dropVecChainStackX = 16,480` B): `onOom := ⌜False⌝`, `onPanic := ⌜False⌝`, leaves `cumSmall`
and `peakLarge` non-increasing, and credits `(x.cs.map (chainPairLargeLive M)).sum +
vec104LargeLive M x.cap.toNat` back from `liveLarge`. -/
def dropVecChainBudgetSpecX [LibsignalPlacement]
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗
      stackAt s.sp dropVecChainStackX
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents (dropVecChainEvents x.cap x.cs) st
    ⌜sf.trace = s0.trace ∧
      HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st -
          ((x.cs.map (chainPairLargeLive M)).sum +
            vec104LargeLive M x.cap.toNat) ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st⌝ ∗
      memRegion x.v 24 ∗ A.pool lim st' sf ∗ stackAt s0.sp dropVecChainStackX

private def dropVecChainEventsSpecX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropVecChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.v ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
      A.pool lim st s ∗
      stackAt s.sp dropVecChainStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.v 24 ∗
      A.pool lim (M.stepEvents (dropVecChainEvents x.cap x.cs) st) sf ∗
      stackAt s0.sp dropVecChainStackX

set_option maxHeartbeats 800000 in
private theorem drop_vec_chain_budget_placed_body [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeyEventsSpecX M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (g : ChainGhost) (c : ReceiverChain)
      (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_2).base + 56#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = cnt →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 44#64) s
        (chainAt A.repAlloc (g, c) cur ∗ A.pool lim st s ∗
          stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 104 ∗
            A.pool lim (M.stepEvents (chainPairFreeEvents (g, c)) st) sm ∗
            stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
  intro cur cnt g c st s Frame hpc hrun hcl hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  refine SepWP.weaken_pre
    (sepConj_mono_left (chainAt_entails_det_dealloc A.repAlloc cur g c)) ?_
  wp_pull_exists
  rename_i ckPtr
  let ckCap := optCkCapVal g.ck c.chainKey
  let st1 := M.stepEvents (pinFreeEvents ⟨g.srk.cap, g.srk.ptr⟩) st
  let st2 := M.stepEvents (pinFreeEvents ⟨g.priv.cap, g.priv.ptr⟩) st1
  let st3 := M.stepEvents (sgnCapFreeEvents ckCap) st2
  let st4 := M.stepEvents (dropVecMessageKeyEvents g.mkCap (g.keys.zip c.messageKeys)) st3
  have hcp_eq : M.stepEvents (chainPairFreeEvents (g, c)) st = st4 := by
    unfold chainPairFreeEvents
    simp only [ckCap, st1, st2, st3, st4, M.stepEvents_append]
  rw [hcp_eq, stackAt_dropVecMessageKeyX_split_bottom fsp]
  refine SepWP.weaken_pre
    (P' := (chainOuterHeadersAt cur g ckCap ckPtr ∗
        vecPinDeallocX A.repAlloc ⟨g.srk.cap, g.srk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A.repAlloc ckCap ckPtr) ∗
      A.pool lim st s ∗ stackAt fsp extHookStack ∗
      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Entails.of_eq (by
      dsimp only [ckCap, chainOuterHeadersAt, extHookStack, Proofs.libsignal.Stage1X.extHookStack]
      sep_ac_rfl)) ?_
  refine seq_clean_lscl_budget hcl (mid := (blkPl_2).base + 76#64)
    (P_mid := fun sm =>
      (chainOuterHeadersAt cur g ckCap ckPtr ∗
        vecPinDeallocX A.repAlloc ⟨g.priv.cap, g.priv.ptr⟩ ∗
        ckDeallocX A.repAlloc ckCap ckPtr) ∗
      A.pool lim st1 sm ∗ stackAt fsp extHookStack ∗
      (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
          (g.keys.zip c.messageKeys) ∗
        memRegion (fsp - 16432#64) 48 ∗ Frame))
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
      sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
  · by_cases hcap : (g.srk.cap == 0#64) = true
    · have hst1 : st1 = st := by dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap, emp_sepConj]; dsimp only [chainOuterHeadersAt]
      dsimp only [chainOuterHeadersAt]
      wp_steps_to_tgt_vm_s as hvm
      apply SepWP.transport_budgetPool hvm
      refine align_pre_budget (by rw [hst1]; sep_ac_rfl) ?_
      wp_done
    · have hst1 : st1 = M.stepEvents (rustDeallocEvents g.srk.cap.toNat 1) st := by
        dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨g.srk.cap, g.srk.ptr⟩) hcap, pull_pure4_b]; dsimp only [chainOuterHeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
      apply SepWP.transport_budgetPool hvm_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      simp only [repAlloc_live_eq]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (g.srk.ptr, g.srk.cap.toNat, 1, st)
      refine align_pre_budget (by rw [hst1, hsp]; dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
    refine seq_clean_lscl_budget hcl1 (mid := (blkPl_2).base + 96#64)
      (P_mid := fun sm =>
        (chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A.repAlloc ckCap ckPtr) ∗
        A.pool lim st2 sm ∗ stackAt fsp extHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
        sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
    · by_cases hcap : (g.priv.cap == 0#64) = true
      · have hst2 : st2 = st1 := by dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap, emp_sepConj]; dsimp only [chainOuterHeadersAt]
        dsimp only [chainOuterHeadersAt]
        wp_steps_to_tgt_vm_s as hvm
        apply SepWP.transport_budgetPool hvm
        refine align_pre_budget (by rw [hst2]; sep_ac_rfl) ?_
        wp_done
      · have hst2 : st2 = M.stepEvents (rustDeallocEvents g.priv.cap.toNat 1) st1 := by
          dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨g.priv.cap, g.priv.ptr⟩) hcap, pull_pure4_b]; dsimp only [chainOuterHeadersAt]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
        wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
        apply SepWP.transport_budgetPool hvm_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        simp only [repAlloc_live_eq]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (g.priv.ptr, g.priv.cap.toNat, 1, st1)
        refine align_pre_budget (by rw [hst2, hsp_1]; dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
      refine seq_clean_lscl_budget hcl2 (mid := (blkPl_2).base + 36#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
            (g.keys.zip c.messageKeys) ∗
          A.pool lim st3 sm ∗ stackAt fsp dropVecMessageKeyStackX ∗
          ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
          sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) ?_ ?_
      · have hstep3 : SepWP ((blkPC_2).rebase (blkPl_2).base H)
            ((blkPl_2).base + 36#64) s2
            ((chainOuterHeadersAt cur g ckCap ckPtr ∗ ckDeallocX A.repAlloc ckCap ckPtr) ∗
              A.pool lim st2 s2 ∗ stackAt fsp extHookStack ∗
              (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
                  (g.keys.zip c.messageKeys) ∗
                memRegion (fsp - 16432#64) 48 ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ chainOuterHeadersAt cur g ckCap ckPtr ∗
                A.pool lim st3 sm ∗ stackAt fsp extHookStack ∗
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
                    (g.keys.zip c.messageKeys) ∗
                  memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          by_cases hcap : ckCap.slt 1#64 = true
          · have hst3 : st3 = st2 := by dsimp [st3]; unfold sgnCapFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_ckDeallocX_zero_b hcap, sepConj_emp]; dsimp only [chainOuterHeadersAt]
            dsimp only [chainOuterHeadersAt]
            wp_steps_to_tgt_vm_s as hvm
            apply SepWP.transport_budgetPool hvm
            refine align_pre_budget (by rw [hst3]; sep_ac_rfl) ?_
            wp_done
          · have hst3 : st3 = M.stepEvents (rustDeallocEvents ckCap.toNat 1) st2 := by
              dsimp [st3]; unfold sgnCapFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_ckDeallocX_ne_b hcap, pull_pure3_b]; dsimp only [chainOuterHeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlay := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
            wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
            apply SepWP.transport_budgetPool hvm_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            simp only [repAlloc_live_eq]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (ckPtr, ckCap.toNat, 1, st2)
            wp_steps_to_tgt_vm_s as hvm_ret
            apply SepWP.transport_budgetPool hvm_ret
            refine align_pre_budget (by rw [hst3, hsp_2]; dsimp only [chainOuterHeadersAt]; sep_ac_rfl) ?_
            wp_done
        refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
        refine Entails.trans
          (sepConj_mono_left (chainOuterHeadersAt_entails_memRegions cur g ckCap ckPtr)) ?_
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp]
        exact Entails.of_eq (by
          dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack]
          sep_ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP ((blkPC_2).rebase (blkPl_2).base H)
            ((blkPl_2).base + 44#64) s3
            (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (cur + 48#64) g.mkCap g.mkPtr
                (g.keys.zip c.messageKeys) ∗
              A.pool lim st3 s3 ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗ Frame))
            (fun sm Pm =>
              (Pm ⊢ (memRegion (cur + 48#64) 24 ∗ memRegion cur 48 ∗ memRegion (cur + 72#64) 32) ∗
                A.pool lim st4 sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧
              sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v ∧
              sm.readReg64 .x21 = cur + 48#64 ∧ sm.readReg64 .x22 = cnt) := by
          wp_steps_lscl_vm_s (lsmpl.base 3) as hvm_mk hcl_mk
          apply SepWP.transport_budgetPool hvm_mk
          have hcall_mk := lscall_of_withLsCl hdrop_mk hcl_mk
          wp_call hcall_mk (⟨cur + 48#64, g.mkCap, g.mkPtr, g.keys.zip c.messageKeys⟩, st3)
          refine align_pre_budget (by dsimp [st4]; rw [hsp_3]; sep_ac_rfl) ?_
          wp_done
        refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨?_, h.2⟩)
        have h1 := h.1
        rw [stackAt_dropVecMessageKeyX_split_bottom fsp] at h1
        dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack] at h1 ⊢
        exact Entails.trans h1 (sepConj_mono_left (chain_memRegions_entails_104 cur))


set_option maxHeartbeats 800000 in
private theorem drop_vec_chain_budget_placed_loop [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeyEventsSpecX M A lim)))
    (s0 : State) (fsp v ptr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List (ChainGhost × ReceiverChain)) (cur : BitVec 64)
      (st : M.σ) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 104 < 2 ^ 63 →
      s.pc = (blkPl_2).base + 56#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved48Preserved s0 s fsp → s.readReg64 .x19 = ptr → s.readReg64 .x20 = v →
      s.readReg64 .x21 = cur + 48#64 → s.readReg64 .x22 = BitVec.ofNat 64 rest.length →
      SepWP ((blkPC_2).rebase (blkPl_2).base H)
        ((blkPl_2).base + 124#64) s
        (arrayAt (chainAt A.repAlloc) 104 cur rest ∗ A.pool lim st s ∗
          stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 104) ∗
            A.pool lim (M.stepEvents (rest.flatMap chainPairFreeEvents) st) sm ∗
            stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ptr ∧ sm.readReg64 .x20 = v) := by
  have hbody := drop_vec_chain_budget_placed_body hdealloc hdrop_mk s0 fsp v ptr hfsp_align
  intro rest
  induction rest with
  | nil => intro _ _ _ _ hne; exact absurd rfl hne
  | cons hd tl ih =>
    rcases hd with ⟨g, c⟩
    intro cur st s Frame _ hlen hpc hrun hcl hpres hx19 hx20 hx21 hx22
    let st1 := M.stepEvents (chainPairFreeEvents (g, c)) st
    rw [show arrayAt (chainAt A.repAlloc) 104 cur ((g, c) :: tl) =
          chainAt A.repAlloc (g, c) cur ∗
            arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl from rfl,
        sep_pull_body]
    refine seq_clean_lscl_budget hcl (mid := (blkPl_2).base + 44#64)
      (hbody cur (BitVec.ofNat 64 ((g, c) :: tl).length) g c st s
        (arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) tl ∗ Frame)
        hpc hrun hcl hpres hx19 hx20 hx21 hx22) ?_
    intro s4 hpc4 hrun4 hcl4 ⟨⟨hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4, hx20_4, hx21_4, hx22_4⟩
    cases tl with
    | nil =>
      have hst_nil : M.stepEvents (((g, c) :: []).flatMap chainPairFreeEvents) st = st1 := by
        simp [st1]
      rw [hst_nil]
      simp only [List.length_cons, List.length_nil, Nat.zero_add, Nat.one_mul,
        arrayAt, emp_sepConj] at hx22_4 ⊢
      wp_steps_to_tgt_vm_s as hvm_end
      apply SepWP.transport_budgetPool hvm_end
      wp_done
    | cons hd2 tl2 =>
      have hst_cons :
          M.stepEvents (((g, c) :: hd2 :: tl2).flatMap chainPairFreeEvents) st =
            M.stepEvents ((hd2 :: tl2).flatMap chainPairFreeEvents) st1 := by
        simp [st1, M.stepEvents_append]
      rw [hst_cons]
      have htl_ne : hd2 :: tl2 ≠ [] := List.cons_ne_nil _ _
      have htl_len := tail_len_mul_lt hlen
      rw [show ((g, c) :: hd2 :: tl2).length = (hd2 :: tl2).length + 1 from rfl,
          ofNat_succ_eq_add_one] at hx22_4
      have hne1 := ofNat_add_one_beq_one_false (n := (hd2 :: tl2).length) (by simp) htl_len
      wp_steps_lscl_vm_s ((blkPl_2).base + 56#64) as hvm_step hcl_step
      apply SepWP.transport_budgetPool hvm_step
      refine sepWP_let_state
        (fun s_step => arrayAt (chainAt A.repAlloc) 104 (cur + 104#64) (hd2 :: tl2) ∗
          A.pool lim st1 s_step ∗ stackAt fsp dropVecMessageKeyStackX ∗
          (memRegion cur 104 ∗ Frame))
        (by sep_ac_rfl) ?_
      refine SepWP.mono
        (ih (cur + 104#64) st1 _ (memRegion cur 104 ∗ Frame)
          htl_ne htl_len rfl hrun4 hcl_step
          ⟨by simp only [wp_norm, arm64_norm]; exact hx23_4,
           by simp only [wp_norm, arm64_norm]; exact hx24_4,
           by simp only [wp_norm, arm64_norm]; exact hx25_4,
           by simp only [wp_norm, arm64_norm]; exact hx26_4,
           by simp only [wp_norm, arm64_norm]; exact hx27_4,
           by simp only [wp_norm, arm64_norm]; exact hx28_4,
           hsp_4, htrace_4, hvregs_4⟩
          (by simp only [wp_norm, arm64_norm]; exact hx19_4)
          (by simp only [wp_norm, arm64_norm]; exact hx20_4)
          (by simp only [wp_norm, arm64_norm, add_104_add_48])
          (by simp only [wp_norm, arm64_norm])) ?_
      intro sf Pf _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      have hsplit := cons_len_mul (g, c) (hd2 :: tl2) 104
      have hbound : 104 + (hd2 :: tl2).length * 104 ≤ 2 ^ 64 := by
        rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
      rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 104 ((hd2 :: tl2).length * 104) hbound]
      exact Entails.refl _

set_option maxHeartbeats 800000 in
private theorem drop_vec_chain_events_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainEventsSpecX M A lim)) := by
  unfold withLsCodeLoaded dropVecChainEventsSpecX
  wp_init xpair s0
  obtain ⟨⟨v, cap, ptr, cs⟩, st⟩ := xpair
  dsimp only at *
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = v := by assumption
  subst hx0
  have hdealloc := dealloc_extern_of_budgetPlaced hA
    (callerProg := (blkPC_2).rebase (blkPl_2).base H)
  have hdrop_mk := drop_vec_message_key_events_placed_ok_cl
    (callerProg := (blkPC_2).rebase (blkPl_2).base H) hA
  have hloop := drop_vec_chain_budget_placed_loop hdealloc hdrop_mk
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  nth_rw 1 [stackAt_dropVecChainX_split s0.sp]
  cells_unfold
  wp_pull_exists
  refine SepWP.weaken_pre
    (sepConj_mono_left (vecAt_expose_loop A.repAlloc 104 8 (chainAt A.repAlloc)
      (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim ?_
  rintro ⟨hlen_le, hcap_lt, hlen_lt, hptr_ne⟩
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  let st_loop := M.stepEvents (cs.flatMap chainPairFreeEvents) st
  refine seq_clean_lscl_budget hcl0 (mid := (blkPl_2).base + 124#64)
    (P_mid := fun sm =>
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗ ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
      ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
      memRegion ptr (cs.length * 104) ∗
      (if cap = 0 then emp
       else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
         memRegion (ptr + BitVec.ofNat 64 (cs.length * 104)) ((cap.toNat - cs.length) * 104)) ∗
      A.pool lim st_loop sm ∗
      stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
      ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))
    (Q := fun sm =>
      Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = ptr ∧
      sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · cases cs with
    | nil =>
      have hst0 : st_loop = st := rfl
      rw [hst0]
      simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj]
      wp_steps_to_tgt_vm_s as hvm0
      apply SepWP.transport_budgetPool hvm0
      wp_done
    | cons hd tl =>
      have hne0 := ofNat_beq_zero_false (n := (hd :: tl).length) (by simp) hlen_lt
      refine seq_clean_lscl_budget hcl0 (mid := (blkPl_2).base + 56#64)
        (P_mid := fun sm =>
          arrayAt (chainAt A.repAlloc) 104 ptr (hd :: tl) ∗
          A.pool lim st sm ∗ stackAt (s0.sp - 48#64) dropVecMessageKeyStackX ∗
          ((s0.readReg64 (Reg.gpr 0#5) ↦₆₄ cap) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₆₄ ptr) ∗
            ((s0.readReg64 (Reg.gpr 0#5) + 16#64) ↦₆₄ BitVec.ofNat 64 (hd :: tl).length) ∗
            (if cap = 0 then emp
             else A.repAlloc.live ptr (cap.toNat * 104) 8 ∗
               memRegion (ptr + BitVec.ofNat 64 ((hd :: tl).length * 104))
                 ((cap.toNat - (hd :: tl).length) * 104)) ∗
            ((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
        (Q := fun sm =>
          Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = ptr ∧
          sm.readReg64 .x20 = s0.readReg64 (Reg.gpr 0#5) ∧
          sm.readReg64 .x21 = ptr + 48#64 ∧
          sm.readReg64 .x22 = BitVec.ofNat 64 (hd :: tl).length)
        ?_ ?_
      · wp_steps_to_tgt_vm_s as hvm0
        apply SepWP.transport_budgetPool hvm0
        refine SepWP.done (by wp_norm_goal) (by wp_norm_lhs) ?_
        refine ⟨Entails.of_eq (by sep_ac_rfl),
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, rfl, rfl⟩
      · intro sm hpcm hrunm hcl_loop ⟨hpresm, hx19m, hx20m, hx21m, hx22m⟩
        refine SepWP.mono
          (hloop s0 (s0.sp - 48#64) (s0.readReg64 (Reg.gpr 0#5)) ptr hfsp_align
            (hd :: tl) ptr st sm _
            (List.cons_ne_nil _ _) hlen_lt hpcm hrunm hcl_loop
            hpresm hx19m hx20m hx21m hx22m) ?_
        intro sf Pf _ _ h
        exact ⟨Entails.trans h.1 (Entails.of_eq (by dsimp [st_loop]; sep_ac_rfl)), h.2⟩
  · intro sm hpcm hrunm hcl_m ⟨⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩, hx19, hx20⟩
    refine SepWP.weaken_pre
      (post_loop_weaken A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) cap ptr cs.length hlen_le hcap_lt _) ?_
    by_cases hcap : (cap == 0#64) = true
    · have hst' : M.stepEvents (dropVecChainEvents cap cs) st = st_loop := by
        unfold dropVecChainEvents vec104FreeEvents
        simp [hcap, st_loop, M.stepEvents_append]
      rw [hst']
      simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
      wp_steps_to_tgt_vm_s as hvm_end
      apply SepWP.transport_budgetPool hvm_end
      refine weaken_pre_at_state
        (fun s' => cap0_weaken_48_vecChain_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.pool lim st_loop s') s0.sp
          (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22)
          (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by dsimp only [Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; sep_ac_rfl) ?_
      wp_done
    · have hst' :
          M.stepEvents (dropVecChainEvents cap cs) st =
            M.stepEvents (rustDeallocEvents (cap.toNat * 104) 8) st_loop := by
        unfold dropVecChainEvents vec104FreeEvents
        simp [hcap, st_loop, M.stepEvents_append]
      rw [hst']
      simp only [eq_false hcap, ↓reduceIte, repAlloc_live_eq]
      have hlay := rustLayoutOk_mul104_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_tail hcl_tail
      apply SepWP.transport_budgetPool hvm_tail
      have hdealloc0 := lscall_of_withLsCl hdealloc hcl_tail
      have hmul : 104#64 * cap = BitVec.ofNat 64 (cap.toNat * 104) := by bv_omega
      refine weaken_pre_at_state
        (fun s' => tail_dealloc_vecChain_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5)) cap ptr
          (A.live ptr (cap.toNat * 104) 8 ∗ memRegion ptr (cap.toNat * 104))
          (A.pool lim st_loop s') s0.sp
          (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x22)
          (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19))
        (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack,
              Reg.fp, Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22]; sep_ac_rfl) ?_
      dsimp only [Proofs.libsignal.Stage1X.extHookStack, extHookStack]
      have : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
      wp_call hdealloc0 (ptr, cap.toNat * 104, 8, st_loop)
      refine weaken_pre_at_state
        (fun s' => vecChain_tail_dealloc_post_ext (s0.readReg64 (Reg.gpr 0#5))
          (A.pool lim (M.stepEvents (rustDeallocEvents (cap.toNat * 104) 8) st_loop) s') s0.sp)
        (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack]) ?_
      wp_done

private theorem drop_vec_chain_events_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 2)
      (withLsCl lsmpl (dropVecChainEventsSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 2) (drop_vec_chain_events_placed_ok hA)

theorem drop_vec_chain_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_2).rebase (blkPl_2).base H)
      (blkPl_2).base
      (withLsCodeLoaded lsmpl (dropVecChainBudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' (drop_vec_chain_events_placed_ok hA)
    fun ⟨x, st⟩ R s0 hpre => ?_
  have hcaps : ChainListCapsOk x.cs := by
    have hm := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (vecAt_chainAt_entails_capsOk A.repAlloc x.v x.cap x.ptr x.cs)))) hpre
    have hm' : s0.mem ⊨ ⌜ChainListCapsOk x.cs⌝ ∗
        ((⌜s0.readReg64 .x0 = x.v ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) x.v x.cap x.ptr x.cs ∗
          A.pool lim st s0 ∗ stackAt s0.sp dropVecChainStackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  refine ⟨(x, st), R, hpre, fun sf hpost => ?_⟩
  dsimp only [dropVecChainEventsSpecX, dropVecChainBudgetSpecX] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  have hcred := stepEvents_dropVecChain_bounds M x.cap hcaps st
  exact ⟨⟨hpost.1, hcred.1, hcred.2.1, hcred.2.2⟩, hpost.2⟩

theorem drop_vec_chain_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 2)
      (withLsCl lsmpl (dropVecChainBudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 2) (drop_vec_chain_budget_placed_ok hA)

/-! ## 5. Budget-Threaded `drop_glue::<SessionStructure> [local#1]` (Block `6`) -/

/-- Budget-threaded contract for `core::ptr::drop_glue::<SessionStructure> [local#1]` (Block `6`,
`dropSessionStructureLocal1StackX = 16,512` B), consuming `sessionStateAt A.repAlloc x.ss x.G x.st`
(**unchanged**), leaving `cumSmall` and `peakLarge` non-increasing, and crediting
`ssStateLargeLive M x.G x.st` back from `liveLarge` (equal to `ssLargeLive M x.G` whenever
`none` chain-keys carry `ck.cap.slt 1#64 = true`, see `ssStateLargeLive_eq_ssLargeLive`). -/
def dropSessionStructureLocal1BudgetSpecX [LibsignalPlacement]
    (M : AllocCostModel) [HasFineReallocCredit M]
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureLocal1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1StackX
  post := fun (x, st) s0 sf =>
    let st' := M.stepEvents (dropSessionStructureLocal1Events x.G x.st) st
    ⌜sf.trace = s0.trace ∧
      HasFineReallocCredit.cumSmall st' ≤ HasFineReallocCredit.cumSmall st ∧
      HasFineReallocCredit.liveLarge st' ≤
        HasFineReallocCredit.liveLarge st - ssStateLargeLive M x.G x.st ∧
      HasFineReallocCredit.peakLarge st' ≤ HasFineReallocCredit.peakLarge st⌝ ∗
      memRegion x.ss 344 ∗ A.pool lim st' sf ∗ stackAt s0.sp dropSessionStructureLocal1StackX

private def dropSessionStructureLocal1EventsSpecX [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (DropSessionStructureLocal1Ghost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      sessionStateAt A.repAlloc x.ss x.G x.st ∗
      A.pool lim st s ∗
      stackAt s.sp dropSessionStructureLocal1StackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗
      A.pool lim (M.stepEvents (dropSessionStructureLocal1Events x.G x.st) st) sf ∗
      stackAt s0.sp dropSessionStructureLocal1StackX

set_option maxHeartbeats 800000 in
private theorem drop_ss_local1_budget_placed_first3 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 12#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp → s.readReg64 .x0 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 76#64) s
        ((ssFirst3HeadersAt ss G ∗
          vecPinDeallocX A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc G.root) ∗
          A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion ss 24 ∗ memRegion (ss + 24#64) 24 ∗ memRegion (ss + 48#64) 24) ∗
            A.pool lim (M.stepEvents (ssFirst3FreeEvents G) st) sm ∗
            stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
  intro G st s Frame hpc hrun hcl hpres hx0
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  let st1 := M.stepEvents (pinFreeEvents ⟨G.localIk.cap, G.localIk.ptr⟩) st
  let st2 := M.stepEvents (pinFreeEvents ⟨G.remoteIk.cap, G.remoteIk.ptr⟩) st1
  let st3 := M.stepEvents (pinFreeEvents G.root) st2
  have hf3_eq : M.stepEvents (ssFirst3FreeEvents G) st = st3 := by
    unfold ssFirst3FreeEvents
    simp only [st1, st2, st3, M.stepEvents_append]
  rw [hf3_eq]
  refine seq_clean_lscl_budget hcl (mid := (blkPl_6).base + 36#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt ss G ∗
        vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc G.root) ∗
      A.pool lim st1 sm ∗ stackAt fsp extHookStack ∗ Frame)
    (Q := ssPresQ s0 fsp ss) ?_ ?_
  · by_cases hcap : (G.localIk.cap == 0#64) = true
    · have hst1 : st1 = st := by dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨G.localIk.cap, G.localIk.ptr⟩) hcap, emp_sepConj]; dsimp only [ssFirst3HeadersAt]
      dsimp only [ssFirst3HeadersAt]
      wp_steps_to_tgt_vm_s as hvm
      apply SepWP.transport_budgetPool hvm
      refine align_pre_budget (by rw [hst1]; sep_ac_rfl) ?_
      wp_done
    · have hst1 : st1 = M.stepEvents (rustDeallocEvents G.localIk.cap.toNat 1) st := by
        dsimp [st1]; unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨G.localIk.cap, G.localIk.ptr⟩) hcap, pull_pure4_b]; dsimp only [ssFirst3HeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
      apply SepWP.transport_budgetPool hvm_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      simp only [repAlloc_live_eq]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (G.localIk.ptr, G.localIk.cap.toNat, 1, st)
      refine align_pre_budget (by rw [hst1, hsp]; dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
      wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean_lscl_budget hcl1 (mid := (blkPl_6).base + 56#64)
      (P_mid := fun sm =>
        (ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
        A.pool lim st2 sm ∗ stackAt fsp extHookStack ∗ Frame)
      (Q := ssPresQ s0 fsp ss) ?_ ?_
    · by_cases hcap : (G.remoteIk.cap == 0#64) = true
      · have hst2 : st2 = st1 := by dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨G.remoteIk.cap, G.remoteIk.ptr⟩) hcap, emp_sepConj]; dsimp only [ssFirst3HeadersAt]
        dsimp only [ssFirst3HeadersAt]
        wp_steps_to_tgt_vm_s as hvm
        apply SepWP.transport_budgetPool hvm
        refine align_pre_budget (by rw [hst2]; sep_ac_rfl) ?_
        wp_done
      · have hst2 : st2 = M.stepEvents (rustDeallocEvents G.remoteIk.cap.toNat 1) st1 := by
          dsimp [st2]; unfold pinFreeEvents; simp [hcap]
        conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨G.remoteIk.cap, G.remoteIk.ptr⟩) hcap, pull_pure4_b]; dsimp only [ssFirst3HeadersAt]
        refine SepWP.pure_elim fun hcap_lt => ?_
        have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
        wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
        apply SepWP.transport_budgetPool hvm_c
        have hcall := lscall_of_withLsCl hdealloc hcl_c
        simp only [repAlloc_live_eq]
        have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
        wp_call hcall (G.remoteIk.ptr, G.remoteIk.cap.toNat, 1, st1)
        refine align_pre_budget (by rw [hst2, hsp_1]; dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
        wp_done
    · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 76#64) s2
          ((ssFirst3HeadersAt ss G ∗ vecPinDeallocX A.repAlloc G.root) ∗
            A.pool lim st2 s2 ∗ stackAt fsp extHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ssFirst3HeadersAt ss G ∗ A.pool lim st3 sm ∗ stackAt fsp extHookStack ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        by_cases hcap : (G.root.cap == 0#64) = true
        · have hst3 : st3 = st2 := by dsimp [st3]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_zero_b hcap, sepConj_emp]; dsimp only [ssFirst3HeadersAt]
          dsimp only [ssFirst3HeadersAt]
          wp_steps_to_tgt_vm_s as hvm
          apply SepWP.transport_budgetPool hvm
          refine align_pre_budget (by rw [hst3]; sep_ac_rfl) ?_
          wp_done
        · have hst3 : st3 = M.stepEvents (rustDeallocEvents G.root.cap.toNat 1) st2 := by
            dsimp [st3]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_b hcap, pull_pure3_b]; dsimp only [ssFirst3HeadersAt]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
          apply SepWP.transport_budgetPool hvm_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          simp only [repAlloc_live_eq]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (G.root.ptr, G.root.cap.toNat, 1, st2)
          refine align_pre_budget (by rw [hst3, hsp_2]; dsimp only [ssFirst3HeadersAt]; sep_ac_rfl) ?_
          wp_done
      exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
        ⟨Entails.trans h.1 (sepConj_mono_left (ssFirst3HeadersAt_entails_memRegions_x ss G)), h.2⟩)


set_option maxHeartbeats 800000 in
private theorem drop_ss_local1_budget_placed_sender [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (hdrop_mk : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsmpl.base 3) (withLsCl lsmpl (dropVecMessageKeyEventsSpecX M A lim)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (senderG : Option SenderChainGhost) (senderSt : Option SenderChain)
      (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 76#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp → s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 156#64) s
        (optSenderChainAt A.repAlloc (ss + 144#64) senderG senderSt ∗
          A.pool lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion (ss + 144#64) 104 ∗
            A.pool lim (M.stepEvents (senderFreeEvents senderG) st) sm ∗
            stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
  intro senderG senderSt st s Frame hpc hrun hcl hpres hx19
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  cases senderG with
  | none =>
    cases senderSt with
    | none =>
      have hnone : optSenderChainAt A.repAlloc (ss + 144#64) none none =
          (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) := by
        unfold optSenderChainAt; rw [show (ss + 144#64) + 8#64 = ss + 152#64 by bv_omega]
      have hsnd0 : M.stepEvents (senderFreeEvents none) st = st := rfl
      rw [hnone, hsnd0]
      have hstep : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s
          ((((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
            A.pool lim st s ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (((ss + 144#64) ↦₆₄ noneCap) ∗ memRegion (ss + 152#64) 96) ∗
              A.pool lim st sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
            Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
        dsimp only [noneCap]
        wp_steps_to_tgt_vm_s as hvm
        apply SepWP.transport_budgetPool hvm
        wp_done
      refine SepWP.mono hstep (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
      rw [show ss + 152#64 = (ss + 144#64) + 8#64 by bv_omega]
      exact sepConj_mono_left (sender_none_entails_memRegion_104_x (ss + 144#64))
    | some _ =>
      simp only [optSenderChainAt]
      rw [show (⌜False⌝ : SepProp) = ⌜False⌝ ∗ emp by rw [sepConj_emp], sepConj_assoc]
      exact SepWP.pure_elim False.elim
  | some sg =>
    cases senderSt with
    | none =>
      simp only [optSenderChainAt]
      rw [show (⌜False⌝ : SepProp) = ⌜False⌝ ∗ emp by rw [sepConj_emp], sepConj_assoc]
      exact SepWP.pure_elim False.elim
    | some sc =>
      refine SepWP.weaken_pre
        (sepConj_mono_left (optSenderChainAt_some_entails_det_ss_local1 A.repAlloc ss sg sc)) ?_
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun hcmn => ?_
      have hcmn_beq : (sg.srk.cap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hcmn
      let st1 := M.stepEvents (pinFreeEvents ⟨sg.srk.cap, sg.srk.ptr⟩) st
      let st2 := M.stepEvents (pinFreeEvents ⟨sg.priv.cap, sg.priv.ptr⟩) st1
      let st3 := M.stepEvents (sgnCapFreeEvents sg.ck.cap) st2
      let st4 := M.stepEvents (dropVecMessageKeyEvents sg.mkCap []) st3
      have hsnd_eq : M.stepEvents (senderFreeEvents (some sg)) st = st4 := by
        unfold senderFreeEvents
        simp only [st1, st2, st3, st4, M.stepEvents_append]
      rw [hsnd_eq, stackAt_dropVecMessageKeyX_split_alloc fsp]
      refine SepWP.weaken_pre (P' :=
        (ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
          vecPinDeallocX A.repAlloc ⟨sg.srk.cap, sg.srk.ptr⟩ ∗
          vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
          ckDeallocX A.repAlloc sg.ck.cap sg.ck.ptr) ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗
        (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
          memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Entails.of_eq (by
          dsimp only [ssSender1HeadersAt, sgnPinDeallocX,
            extHookStack, Proofs.libsignal.Stage1X.extHookStack]
          sep_ac_rfl)) ?_
      refine seq_clean_lscl_budget hcl (mid := (blkPl_6).base + 104#64)
        (P_mid := fun sm =>
          (ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
            vecPinDeallocX A.repAlloc ⟨sg.priv.cap, sg.priv.ptr⟩ ∗
            ckDeallocX A.repAlloc sg.ck.cap sg.ck.ptr) ∗
          A.pool lim st1 sm ∗ stackAt fsp extHookStack ∗
          (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
            memRegion (fsp - 16432#64) 48 ∗ Frame))
        (Q := ssPresQ s0 fsp ss) ?_ ?_
      · by_cases hcap : (sg.srk.cap == 0#64) = true
        · have hst1 : st1 = st := by dsimp [st1]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨sg.srk.cap, sg.srk.ptr⟩) hcap, emp_sepConj]; dsimp only [ssSender1HeadersAt]
          dsimp only [ssSender1HeadersAt]
          wp_steps_to_tgt_vm_s as hvm
          apply SepWP.transport_budgetPool hvm
          refine align_pre_budget (by rw [hst1]; sep_ac_rfl) ?_
          wp_done
        · have hst1 : st1 = M.stepEvents (rustDeallocEvents sg.srk.cap.toNat 1) st := by
            dsimp [st1]; unfold pinFreeEvents; simp [hcap]
          conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨sg.srk.cap, sg.srk.ptr⟩) hcap, pull_pure4_b]; dsimp only [ssSender1HeadersAt]
          refine SepWP.pure_elim fun hcap_lt => ?_
          have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
          wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
          apply SepWP.transport_budgetPool hvm_c
          have hcall := lscall_of_withLsCl hdealloc hcl_c
          simp only [repAlloc_live_eq]
          have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
          wp_call hcall (sg.srk.ptr, sg.srk.cap.toNat, 1, st)
          refine align_pre_budget (by rw [hst1, hsp]; dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
          wp_done
      · intro s1 hpc1 hrun1 hcl1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
        refine seq_clean_lscl_budget hcl1 (mid := (blkPl_6).base + 124#64)
          (P_mid := fun sm =>
            (ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
              ckDeallocX A.repAlloc sg.ck.cap sg.ck.ptr) ∗
            A.pool lim st2 sm ∗ stackAt fsp extHookStack ∗
            (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              memRegion (fsp - 16432#64) 48 ∗ Frame))
          (Q := ssPresQ s0 fsp ss) ?_ ?_
        · by_cases hcap : (sg.priv.cap == 0#64) = true
          · have hst2 : st2 = st1 := by dsimp [st2]; unfold pinFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨sg.priv.cap, sg.priv.ptr⟩) hcap, emp_sepConj]; dsimp only [ssSender1HeadersAt]
            dsimp only [ssSender1HeadersAt]
            wp_steps_to_tgt_vm_s as hvm
            apply SepWP.transport_budgetPool hvm
            refine align_pre_budget (by rw [hst2]; sep_ac_rfl) ?_
            wp_done
          · have hst2 : st2 = M.stepEvents (rustDeallocEvents sg.priv.cap.toNat 1) st1 := by
              dsimp [st2]; unfold pinFreeEvents; simp [hcap]
            conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨sg.priv.cap, sg.priv.ptr⟩) hcap, pull_pure4_b]; dsimp only [ssSender1HeadersAt]
            refine SepWP.pure_elim fun hcap_lt => ?_
            have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
            wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
            apply SepWP.transport_budgetPool hvm_c
            have hcall := lscall_of_withLsCl hdealloc hcl_c
            simp only [repAlloc_live_eq]
            have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
            wp_call hcall (sg.priv.ptr, sg.priv.cap.toNat, 1, st1)
            refine align_pre_budget (by rw [hst2, hsp_1]; dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
            wp_done
        · intro s2 hpc2 hrun2 hcl2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
          refine seq_clean_lscl_budget hcl2 (mid := (blkPl_6).base + 148#64)
            (P_mid := fun sm =>
              vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
              A.pool lim st3 sm ∗ stackAt fsp dropVecMessageKeyStackX ∗
              ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
            (Q := ssPresQ s0 fsp ss) ?_ ?_
          · have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 148#64) s2
                ((ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
                  ckDeallocX A.repAlloc sg.ck.cap sg.ck.ptr) ∗
                  A.pool lim st2 s2 ∗ stackAt fsp extHookStack ∗
                  (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                    memRegion (fsp - 16432#64) 48 ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ ssSender1HeadersAt ss sg sg.ck.cap sg.ck.ptr ∗
                    A.pool lim st3 sm ∗ stackAt fsp extHookStack ∗
                    (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                      memRegion (fsp - 16432#64) 48 ∗ Frame)) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              by_cases hcap : sg.ck.cap.slt 1#64 = true
              · have hst3 : st3 = st2 := by dsimp [st3]; unfold sgnCapFreeEvents; simp [hcap]
                conv => arg 4; rw [expose_ckDeallocX_zero_b hcap, sepConj_emp]; dsimp only [ssSender1HeadersAt]
                dsimp only [ssSender1HeadersAt]
                wp_steps_to_tgt_vm_s as hvm
                apply SepWP.transport_budgetPool hvm
                refine align_pre_budget (by rw [hst3]; sep_ac_rfl) ?_
                wp_done
              · have hst3 : st3 = M.stepEvents (rustDeallocEvents sg.ck.cap.toNat 1) st2 := by
                  dsimp [st3]; unfold sgnCapFreeEvents; simp [hcap]
                conv => arg 4; rw [expose_ckDeallocX_ne_b hcap, pull_pure3_b]; dsimp only [ssSender1HeadersAt]
                refine SepWP.pure_elim fun hcap_lt => ?_
                have hlay := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
                wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
                apply SepWP.transport_budgetPool hvm_c
                have hcall := lscall_of_withLsCl hdealloc hcl_c
                simp only [repAlloc_live_eq]
                have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
                wp_call hcall (sg.ck.ptr, sg.ck.cap.toNat, 1, st2)
                refine align_pre_budget (by rw [hst3, hsp_2]; dsimp only [ssSender1HeadersAt]; sep_ac_rfl) ?_
                wp_done
            refine SepWP.mono hstep3 (fun sm Pm _ _ h => ⟨Entails.trans h.1 ?_, h.2⟩)
            refine Entails.trans
              (sepConj_mono_left (ssSender1HeadersAt_entails_memRegions_x ss sg sg.ck.cap sg.ck.ptr)) ?_
            rw [stackAt_dropVecMessageKeyX_split_alloc fsp]
            exact Entails.of_eq (by
              dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack]
              sep_ac_rfl)
          · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
            have hstep4 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 156#64) s3
                (vecAt A.repAlloc 104 8 (messageKeyAt A.repAlloc) (ss + 192#64) sg.mkCap sg.mkPtr [] ∗
                  A.pool lim st3 s3 ∗ stackAt fsp dropVecMessageKeyStackX ∗
                  ((memRegion (ss + 144#64) 48 ∗ memRegion (ss + 216#64) 32) ∗ Frame))
                (fun sm Pm =>
                  (Pm ⊢ (memRegion (ss + 192#64) 24 ∗ memRegion (ss + 144#64) 48 ∗
                      memRegion (ss + 216#64) 32) ∗
                    A.pool lim st4 sm ∗ stackAt fsp dropVecMessageKeyStackX ∗ Frame) ∧
                  Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
              wp_steps_lscl_vm_s (lsmpl.base 3) as hvm_mk hcl_mk
              apply SepWP.transport_budgetPool hvm_mk
              have hdrop_mk0 := lscall_of_withLsCl hdrop_mk hcl_mk
              wp_call hdrop_mk0 (⟨ss + 192#64, sg.mkCap, sg.mkPtr, []⟩, st3)
              refine align_pre_budget (by dsimp [st4]; rw [hsp_3]; sep_ac_rfl) ?_
              wp_done
            refine SepWP.mono hstep4 (fun sm Pm _ _ h => ⟨?_, h.2⟩)
            have h1 := h.1
            rw [stackAt_dropVecMessageKeyX_split_alloc fsp] at h1
            dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack] at h1 ⊢
            exact Entails.trans h1 (sepConj_mono_left (ssSender1_memRegions_entails_104_x ss))


set_option maxHeartbeats 400000 in
private theorem drop_ss_local1_tail3_step1 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (G : SessionGhost) (pCap pPtr kCap kPtr : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_6).base + 164#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpres : Saved32Preserved s0 s fsp) (hx19 : s.readReg64 .x19 = ss) :
    SepWP ((blkPC_6).rebase (blkPl_6).base H)
      ((blkPl_6).base + 188#64) s
      ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        ckDeallocX A.repAlloc pCap pPtr ∗
        ckDeallocX A.repAlloc kCap kPtr ∗
        vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            ckDeallocX A.repAlloc kCap kPtr ∗
            vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool lim (M.stepEvents (sgnCapFreeEvents pCap) st) sm ∗
          stackAt fsp extHookStack ∗ Frame) ∧
        ssPresQ s0 fsp ss sm) := by
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  by_cases hcap : pCap.slt 1#64 = true
  · have hst1 : M.stepEvents (sgnCapFreeEvents pCap) st = st := by
      unfold sgnCapFreeEvents; simp [hcap]
    conv => arg 4; rw [expose_ckDeallocX_zero_b hcap, emp_sepConj]; dsimp only [ssTail3HeadersAt]
    dsimp only [ssTail3HeadersAt]
    wp_steps_to_tgt_vm_s as hvm
    apply SepWP.transport_budgetPool hvm
    refine align_pre_budget (by rw [hst1]; sep_ac_rfl) ?_
    wp_done
  · have hst1 : M.stepEvents (sgnCapFreeEvents pCap) st =
        M.stepEvents (rustDeallocEvents pCap.toNat 1) st := by
      unfold sgnCapFreeEvents; simp [hcap]
    conv => arg 4; rw [expose_ckDeallocX_ne_b hcap, pull_pure4_b]; dsimp only [ssTail3HeadersAt]
    refine SepWP.pure_elim fun hcap_lt => ?_
    have hlay := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
    wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
    apply SepWP.transport_budgetPool hvm_c
    have hcall := lscall_of_withLsCl hdealloc hcl_c
    simp only [repAlloc_live_eq]
    have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hcall (pPtr, pCap.toNat, 1, st)
    refine align_pre_budget (by rw [hst1, hsp]; dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
    wp_done

set_option maxHeartbeats 400000 in
private theorem drop_ss_local1_tail3_step2 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (G : SessionGhost) (pCap pPtr kCap kPtr : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_6).base + 188#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpres : Saved32Preserved s0 s fsp) (hx19 : s.readReg64 .x19 = ss) :
    SepWP ((blkPC_6).rebase (blkPl_6).base H)
      ((blkPl_6).base + 212#64) s
      ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        ckDeallocX A.repAlloc kCap kPtr ∗
        vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
            vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool lim (M.stepEvents (sgnCapFreeEvents kCap) st) sm ∗
          stackAt fsp extHookStack ∗ Frame) ∧
        ssPresQ s0 fsp ss sm) := by
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  by_cases hcap : kCap.slt 1#64 = true
  · have hst2 : M.stepEvents (sgnCapFreeEvents kCap) st = st := by
      unfold sgnCapFreeEvents; simp [hcap]
    conv => arg 4; rw [expose_ckDeallocX_zero_b hcap, emp_sepConj]; dsimp only [ssTail3HeadersAt]
    dsimp only [ssTail3HeadersAt]
    wp_steps_to_tgt_vm_s as hvm
    apply SepWP.transport_budgetPool hvm
    refine align_pre_budget (by rw [hst2]; sep_ac_rfl) ?_
    wp_done
  · have hst2 : M.stepEvents (sgnCapFreeEvents kCap) st =
        M.stepEvents (rustDeallocEvents kCap.toNat 1) st := by
      unfold sgnCapFreeEvents; simp [hcap]
    conv => arg 4; rw [expose_ckDeallocX_ne_b hcap, pull_pure4_b]; dsimp only [ssTail3HeadersAt]
    refine SepWP.pure_elim fun hcap_lt => ?_
    have hlay := rustLayoutOk_u8_of_not_slt1 hcap hcap_lt
    wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
    apply SepWP.transport_budgetPool hvm_c
    have hcall := lscall_of_withLsCl hdealloc hcl_c
    simp only [repAlloc_live_eq]
    have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    wp_call hcall (kPtr, kCap.toNat, 1, st)
    refine align_pre_budget (by rw [hst2, hsp]; dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
    wp_done

set_option maxHeartbeats 400000 in
private theorem drop_ss_local1_tail3_step3 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (G : SessionGhost) (pCap pPtr kCap kPtr : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_6).base + 212#64) (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpres : Saved32Preserved s0 s fsp) (hx19 : s.readReg64 .x19 = ss) :
    SepWP ((blkPC_6).rebase (blkPl_6).base H)
      ((blkPl_6).base + 232#64) s
      ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗
            memRegion (ss + 96#64) 24) ∗
          A.pool lim (M.stepEvents (pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩) st) sm ∗
          stackAt fsp extHookStack ∗ Frame) ∧
        Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
  rcases hpres with ⟨hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  have hstep3 : SepWP ((blkPC_6).rebase (blkPl_6).base H) ((blkPl_6).base + 232#64) s
      ((ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
        vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
        A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ssTail3HeadersAt ss pCap pPtr kCap kPtr G ∗
          A.pool lim (M.stepEvents (pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩) st) sm ∗
          stackAt fsp extHookStack ∗ Frame) ∧
        Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
    by_cases hcap : (G.alice.cap == 0#64) = true
    · have hst3 : M.stepEvents (pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩) st = st := by
        unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_zero_b (pin := ⟨G.alice.cap, G.alice.ptr⟩) hcap, sepConj_emp]; dsimp only [ssTail3HeadersAt]
      dsimp only [ssTail3HeadersAt]
      wp_steps_to_tgt_vm_s as hvm
      apply SepWP.transport_budgetPool hvm
      refine align_pre_budget (by rw [hst3]; sep_ac_rfl) ?_
      wp_done
    · have hst3 : M.stepEvents (pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩) st =
          M.stepEvents (rustDeallocEvents G.alice.cap.toNat 1) st := by
        unfold pinFreeEvents; simp [hcap]
      conv => arg 4; rw [expose_pin_deallocX_b (pin := ⟨G.alice.cap, G.alice.ptr⟩) hcap, pull_pure3_b]; dsimp only [ssTail3HeadersAt]
      refine SepWP.pure_elim fun hcap_lt => ?_
      have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
      wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_c hcl_c
      apply SepWP.transport_budgetPool hvm_c
      have hcall := lscall_of_withLsCl hdealloc hcl_c
      simp only [repAlloc_live_eq]
      have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
      wp_call hcall (G.alice.ptr, G.alice.cap.toNat, 1, st)
      refine align_pre_budget (by rw [hst3, hsp]; dsimp only [ssTail3HeadersAt]; sep_ac_rfl) ?_
      wp_done
  exact SepWP.mono hstep3 (fun sm Pm _ _ h =>
    ⟨Entails.trans h.1
      (sepConj_mono_left (ssTail3HeadersAt_entails_memRegions_x ss pCap pPtr kCap kPtr G)), h.2⟩)

private theorem drop_ss_local1_budget_placed_tail3 [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hdealloc : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (lsρ lsRustDeallocSym)
      (withLsCl lsmpl (rustCliDeallocNoOomExternSpecWithStack M A lim extHookStack)))
    (s0 : State) (fsp ss : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (G : SessionGhost) (pPtr kPtr : BitVec 64) (st : M.σ) (s : State) (Frame : SepProp),
      s.pc = (blkPl_6).base + 164#64 → s.status = .Running →
      LibsignalCodeLoaded lsmpl s.mem →
      Saved32Preserved s0 s fsp → s.readReg64 .x19 = ss →
      SepWP ((blkPC_6).rebase (blkPl_6).base H)
        ((blkPl_6).base + 232#64) s
        ((ssTail3HeadersAt ss (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr G ∗
          sgnPinDeallocX A.repAlloc (optTailCapVal G.pending) pPtr ∗
          sgnPinDeallocX A.repAlloc (optTailCapVal G.kyber) kPtr ∗
          vecPinDeallocX A.repAlloc ⟨G.alice.cap, G.alice.ptr⟩) ∗
          A.pool lim st s ∗ stackAt fsp extHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ (memRegion (ss + 248#64) 48 ∗ memRegion (ss + 296#64) 32 ∗
              memRegion (ss + 96#64) 24) ∗
            A.pool lim (M.stepEvents (ssTail3FreeEvents G) st) sm ∗
            stackAt fsp extHookStack ∗ Frame) ∧
          Saved32Preserved s0 sm fsp ∧ sm.readReg64 .x19 = ss) := by
  intro G pPtr kPtr st s Frame hpc hrun hcl hpres hx19
  have ht3_eq : M.stepEvents (ssTail3FreeEvents G) st =
      M.stepEvents (pinFreeEvents ⟨G.alice.cap, G.alice.ptr⟩)
        (M.stepEvents (sgnCapFreeEvents (optTailCapVal G.kyber))
          (M.stepEvents (sgnCapFreeEvents (optTailCapVal G.pending)) st)) := by
    unfold ssTail3FreeEvents
    simp only [M.stepEvents_append]
  rw [ht3_eq]
  dsimp only [sgnPinDeallocX]
  refine seq_clean_lscl_budget hcl (mid := (blkPl_6).base + 188#64)
    (drop_ss_local1_tail3_step1 hdealloc s0 fsp ss hfsp_align
      G (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr st s Frame
      hpc hrun hcl hpres hx19) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx19_1⟩
  refine seq_clean_lscl_budget hcl1 (mid := (blkPl_6).base + 212#64)
    (drop_ss_local1_tail3_step2 hdealloc s0 fsp ss hfsp_align
      G (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr
      (M.stepEvents (sgnCapFreeEvents (optTailCapVal G.pending)) st) s1 Frame
      hpc1 hrun1 hcl1 hpres1 hx19_1) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
  exact drop_ss_local1_tail3_step3 hdealloc s0 fsp ss hfsp_align
    G (optTailCapVal G.pending) pPtr (optTailCapVal G.kyber) kPtr
    (M.stepEvents (sgnCapFreeEvents (optTailCapVal G.kyber))
      (M.stepEvents (sgnCapFreeEvents (optTailCapVal G.pending)) st))
    s2 Frame hpc2 hrun2 hcl2 hpres2 hx19_2


private theorem ss_local1_tail_dealloc_post_ext (ss : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    memRegion (ss + 120#64) 24 ∗ ss9MemRegions ss ∗ pool ∗
      memRegion (sp - 16512#64) 128 ∗ stackAt sp extHookStack ⊢
    (memRegion (ss + 120#64) 24 ∗ ss9MemRegions ss) ∗ pool ∗
      (stackAt (sp - 32#64) dropVecChainStackX ∗ cells (sp - 32#64) 4) := by
  have hst := tail_stack_128_from_bottom_ext sp
  dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack] at hst ⊢
  rw [← hst]
  dsimp only [ss9MemRegions]
  exact Entails.of_eq (by sep_ac_rfl)

set_option maxHeartbeats 800000 in
private theorem drop_session_structure_local1_events_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1EventsSpecX M A lim)) := by
  unfold withLsCodeLoaded dropSessionStructureLocal1EventsSpecX
  wp_init xpair s0
  obtain ⟨⟨ss, G, st_s⟩, st⟩ := xpair
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hx0 : s0.readReg64 (Reg.gpr 0#5) = ss := by assumption
  subst hx0
  have hdealloc := dealloc_extern_of_budgetPlaced
    (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA
  have hdrop_mk := drop_vec_message_key_events_placed_ok_cl
    (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA
  have hdrop_vc := drop_vec_chain_events_placed_ok_cl
    (callerProg := (blkPC_6).rebase (blkPl_6).base H) hA
  have hfirst3 := drop_ss_local1_budget_placed_first3 hdealloc
  have hsender := drop_ss_local1_budget_placed_sender hdealloc hdrop_mk
  have htail3 := drop_ss_local1_budget_placed_tail3 hdealloc
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 32#64 (by assumption) (by decide)
  rw [stackAt_ss_local1_split_x s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i v0 v1 v2 v3
  refine drop4_strengthen_post_x (session_memRegions_entails_344_x (s0.readReg64 (Reg.gpr 0#5))) ?_
  refine SepWP.weaken_pre
    (sepConj_mono_left
      (sessionStateAt_entails_det_dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G st_s)) ?_
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun _hcaps_ok => ?_
  wp_pull_exists
  rename_i pPtr kPtr
  let pCap := optTailCapVal G.pending
  let kCap := optTailCapVal G.kyber
  let st1 := M.stepEvents (ssFirst3FreeEvents G) st
  let st2 := M.stepEvents (senderFreeEvents G.sender) st1
  let st3 := M.stepEvents (dropVecChainEvents G.chainsCap (G.chains.zip st_s.receiverChains)) st2
  let st4 := M.stepEvents (ssTail3FreeEvents G) st3
  let st5 := M.stepEvents (pinFreeEvents G.pq) st4
  have hst_all : M.stepEvents (dropSessionStructureLocal1Events G st_s) st = st5 := by
    unfold dropSessionStructureLocal1Events
    simp only [st1, st2, st3, st4, st5, M.stepEvents_append]
  rw [hst_all]
  refine seq_clean_lscl_budget hcl0 (mid := (blkPl_6).base + 12#64)
    (P_mid := fun sm =>
      (ssFirst3HeadersAt (s0.readReg64 (Reg.gpr 0#5)) G ∗
        vecPinDeallocX A.repAlloc ⟨G.localIk.cap, G.localIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc ⟨G.remoteIk.cap, G.remoteIk.ptr⟩ ∗
        vecPinDeallocX A.repAlloc G.root) ∗
      A.pool lim st sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗
      (optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st_s.senderChain ∗
        vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
          G.chainsCap G.chainsPtr (G.chains.zip st_s.receiverChains) ∗
        ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 96 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 .x0 = s0.readReg64 (Reg.gpr 0#5))
    ?_ ?_
  · rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
    have hsp_sub : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
    rw [hsp_sub]
    wp_steps_to_tgt_vm_s as hvm0
    apply SepWP.transport_budgetPool hvm0
    refine align_pre_budget (by
      dsimp only [pCap, kCap, ssFirst3HeadersAt, ssTail3HeadersAt, ssTail3Dealloc,
        ssPqPart, ssSavedFrame, extHookStack, Proofs.libsignal.Stage1X.extHookStack,
        Reg.x19, Reg.lr, Reg.fp]
      sep_ac_rfl) ?_
    wp_done
  · intro s1 hpc1 hrun1 hcl1 ⟨hpres1, hx0_1⟩
    refine seq_clean_lscl_budget hcl1 (mid := (blkPl_6).base + 76#64)
      (P_mid := fun sm =>
        optSenderChainAt A.repAlloc (s0.readReg64 (Reg.gpr 0#5) + 144#64) G.sender st_s.senderChain ∗
        A.pool lim st1 sm ∗ stackAt (s0.sp - 32#64) dropVecMessageKeyStackX ∗
        (vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
          G.chainsCap G.chainsPtr (G.chains.zip st_s.receiverChains) ∗
        ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
        ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
        ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
        memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
        memRegion (s0.sp - 16512#64) 48 ∗
        ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
      (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
      ?_ ?_
    · refine SepWP.mono
        (hfirst3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align G st s1 _
          hpc1 hrun1 hcl1 hpres1 hx0_1) ?_
      intro sm Pm _ _ h
      refine ⟨Entails.trans h.1 ?_, h.2⟩
      rw [stackAt_dropVecMessageKeyX_split_alloc (s0.sp - 32#64)]
      have hsp_sub1 : (s0.sp - 32#64) - 16432#64 = s0.sp - 16464#64 := by bv_omega
      rw [hsp_sub1,
          ProofLib.memRegion_split' (b := s0.sp - 16512#64) (n := 48) (k := 48)
            (b' := s0.sp - 16464#64) rfl (by bv_omega) (by decide)]
      dsimp only [st1, ssFirst3Mem, extHookStack, Proofs.libsignal.Stage1X.extHookStack]
      exact Entails.of_eq (by sep_ac_rfl)
    · intro s2 hpc2 hrun2 hcl2 ⟨hpres2, hx19_2⟩
      refine seq_clean_lscl_budget hcl2 (mid := (blkPl_6).base + 156#64)
        (P_mid := fun sm =>
          vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (s0.readReg64 (Reg.gpr 0#5) + 72#64)
            G.chainsCap G.chainsPtr (G.chains.zip st_s.receiverChains) ∗
          A.pool lim st2 sm ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
          (ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
          ssPqPart A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq ∗
          ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
          ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3))
        (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
        ?_ ?_
      · refine SepWP.mono
          (hsender s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
            G.sender st_s.senderChain st1 s2 _ hpc2 hrun2 hcl2 hpres2 hx19_2) ?_
        intro sm Pm _ _ h
        refine ⟨Entails.trans h.1 ?_, h.2⟩
        rw [stackAt_dropVecChainX_split_mk (s0.sp - 32#64)]
        have hsp_sub2 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
        rw [hsp_sub2]
        dsimp only [st2]
        exact Entails.of_eq (by sep_ac_rfl)
      · intro s3 hpc3 hrun3 hcl3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        refine seq_clean_lscl_budget hcl3 (mid := (blkPl_6).base + 164#64)
          (P_mid := fun sm =>
            ssTail3Dealloc A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) pCap pPtr kCap kPtr G ∗
            A.pool lim st3 sm ∗ stackAt (s0.sp - 32#64) extHookStack ∗
            (((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A.repAlloc G.pq) ∗
            ssFirst3Mem (s0.readReg64 (Reg.gpr 0#5)) ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 72#64) 24 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 144#64) 104 ∗
            memRegion (s0.readReg64 (Reg.gpr 0#5) + 328#64) 16 ∗
            memRegion (s0.sp - 16512#64) 96 ∗
            ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
          (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
          ?_ ?_
        · have hs3_align : (s3.sp &&& 15#64 == 0#64) = true := by
            rw [hsp_3]; exact hfsp_align
          wp_steps_lscl_vm_s (lsmpl.base 2) as hvm_vc hcl_vc
          apply SepWP.transport_budgetPool hvm_vc
          have hdrop_vc0 := lscall_of_withLsCl hdrop_vc hcl_vc
          wp_call hdrop_vc0 (⟨s0.readReg64 (Reg.gpr 0#5) + 72#64, G.chainsCap, G.chainsPtr,
            G.chains.zip st_s.receiverChains⟩, st2)
          refine align_pre_budget ?_ ?_
          · dsimp only [st3]
            rw [hsp_3, stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub3 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub3]
            dsimp only [ssTail3HeadersAt, ssTail3Dealloc, ssPqPart, ssFirst3Mem, ssSavedFrame,
              extHookStack, Proofs.libsignal.Stage1X.extHookStack]
            sep_ac_rfl
          · wp_done
        · intro s4 hpc4 hrun4 hcl4 ⟨⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4, hsp_4, htrace_4, hvregs_4⟩, hx19_4⟩
          refine seq_clean_lscl_budget hcl4 (mid := (blkPl_6).base + 232#64)
            (P_mid := fun sm =>
              ((s0.readReg64 (Reg.gpr 0#5) + 120#64) ↦₆₄ G.pq.cap) ∗
              ((s0.readReg64 (Reg.gpr 0#5) + 128#64) ↦₆₄ G.pq.ptr) ∗
              memRegion (s0.readReg64 (Reg.gpr 0#5) + 136#64) 8 ∗ vecPinDeallocX A.repAlloc G.pq ∗
              ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗
              A.pool lim st4 sm ∗ stackAt (s0.sp - 32#64) dropVecChainStackX ∗
              ssSavedFrame s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
            (Q := ssPresQ s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)))
            ?_ ?_
          · refine SepWP.mono
              (htail3 s0 (s0.sp - 32#64) (s0.readReg64 (Reg.gpr 0#5)) hfsp_align
                G pPtr kPtr st3 s4 _ hpc4 hrun4 hcl4
                ⟨hx20_4, hx21_4, hx22_4, hx23_4, hx24_4, hx25_4, hx26_4, hx27_4, hx28_4,
                  hsp_4, htrace_4, hvregs_4⟩ hx19_4) ?_
            intro sm Pm _ _ h
            refine ⟨Entails.trans h.1 ?_, h.2⟩
            rw [stackAt_dropVecChainX_split_alloc (s0.sp - 32#64)]
            have hsp_sub4 : (s0.sp - 32#64) - 16480#64 = s0.sp - 16512#64 := by bv_omega
            rw [hsp_sub4]
            dsimp only [st4, ss9MemRegions, ssFirst3Mem,
              extHookStack, Proofs.libsignal.Stage1X.extHookStack]
            exact Entails.of_eq (by sep_ac_rfl)
          · intro s5 hpc5 hrun5 hcl5 ⟨⟨hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx26_5, hx27_5, hx28_5, hsp_5, htrace_5, hvregs_5⟩, hx19_5⟩
            dsimp only [ssSavedFrame]
            by_cases hcap : (G.pq.cap == 0#64) = true
            · have hst5 : st5 = st4 := by dsimp [st5]; unfold pinFreeEvents; simp [hcap]
              rw [hst5]
              dsimp only [vecPinDeallocX]
              simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
              wp_steps_to_tgt_vm_s as hvm_end
              apply SepWP.transport_budgetPool hvm_end
              refine weaken_pre_at_state
                (fun s' => pq_header24_weaken_x (s0.readReg64 (Reg.gpr 0#5)) G.pq.cap G.pq.ptr
                  (ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)) ∗ A.pool lim st4 s' ∗
                    stackAt (s0.sp - 32#64) dropVecChainStackX ∗
                    ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
                    ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ ((s0.sp - 8#64) ↦₆₄ v3)))
                (by dsimp only [Reg.fp, Reg.lr, Reg.x19]; sep_ac_rfl) ?_
              wp_done
            · have hst5 : st5 = M.stepEvents (rustDeallocEvents G.pq.cap.toNat 1) st4 := by
                dsimp [st5]; unfold pinFreeEvents; simp [hcap]
              rw [hst5, ss_epilogue_pure_extract A.repAlloc (s0.readReg64 (Reg.gpr 0#5)) G.pq hcap]
              refine SepWP.pure_elim fun hcap_lt => ?_
              have hlay := rustLayoutOk_u8_of_ne_zero hcap hcap_lt
              wp_steps_lscl_vm_s (lsρ lsRustDeallocSym) as hvm_tail hcl_tail
              apply SepWP.transport_budgetPool hvm_tail
              have hdealloc0 := lscall_of_withLsCl hdealloc hcl_tail
              simp only [repAlloc_live_eq]
              refine weaken_pre_at_state
                (fun s' => tail_dealloc_ss_local1_pre_weaken_ext (s0.readReg64 (Reg.gpr 0#5))
                  G.pq.cap G.pq.ptr
                  (A.live G.pq.ptr G.pq.cap.toNat 1 ∗ memRegion G.pq.ptr G.pq.cap.toNat)
                  (ss9MemRegions (s0.readReg64 (Reg.gpr 0#5)))
                  (A.pool lim st4 s') s0.sp
                  (s0.readReg64 .fp) (s0.readReg64 .lr) (s0.readReg64 .x19) v3)
                (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack,
                      Reg.fp, Reg.lr, Reg.x19]; sep_ac_rfl) ?_
              dsimp only [Proofs.libsignal.Stage1X.extHookStack, extHookStack]
              have : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
              wp_call hdealloc0 (G.pq.ptr, G.pq.cap.toNat, 1, st4)
              refine weaken_pre_at_state
                (fun s' => ss_local1_tail_dealloc_post_ext (s0.readReg64 (Reg.gpr 0#5))
                  (A.pool lim (M.stepEvents (rustDeallocEvents G.pq.cap.toNat 1) st4) s') s0.sp)
                (by dsimp only [extHookStack, Proofs.libsignal.Stage1X.extHookStack]
                    sep_ac_rfl) ?_
              cells_unfold; wp_pull_exists; wp_done

theorem drop_session_structure_local1_budget_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok ((blkPC_6).rebase (blkPl_6).base H) (blkPl_6).base
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1BudgetSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map' (drop_session_structure_local1_events_placed_ok hA)
    fun ⟨x, st⟩ R s0 hpre => ?_
  have hcaps : SessionDropCapsOk x.G x.st := by
    have hm := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left
        (sessionStateAt_entails_det_dealloc A.repAlloc x.ss x.G x.st)))) hpre
    have hm' : s0.mem ⊨ ⌜SessionDropCapsOk x.G x.st⌝ ∗
        ((⌜s0.readReg64 .x0 = x.ss ∧ LsRetAddr624 (s0.readReg64 .lr)⌝ ∗
          (∃∗ pPtr : BitVec 64, ∃∗ kPtr : BitVec 64,
            (ssFirst3HeadersAt x.ss x.G ∗
              vecPinDeallocX A.repAlloc ⟨x.G.localIk.cap, x.G.localIk.ptr⟩ ∗
              vecPinDeallocX A.repAlloc ⟨x.G.remoteIk.cap, x.G.remoteIk.ptr⟩ ∗
              vecPinDeallocX A.repAlloc x.G.root) ∗
            optSenderChainAt A.repAlloc (x.ss + 144#64) x.G.sender x.st.senderChain ∗
            vecAt A.repAlloc 104 8 (chainAt A.repAlloc) (x.ss + 72#64) x.G.chainsCap x.G.chainsPtr
              (x.G.chains.zip x.st.receiverChains) ∗
            (ssTail3HeadersAt x.ss (optTailCapVal x.G.pending) pPtr
                (optTailCapVal x.G.kyber) kPtr x.G ∗
              sgnPinDeallocX A.repAlloc (optTailCapVal x.G.pending) pPtr ∗
              sgnPinDeallocX A.repAlloc (optTailCapVal x.G.kyber) kPtr ∗
              vecPinDeallocX A.repAlloc ⟨x.G.alice.cap, x.G.alice.ptr⟩) ∗
            (((x.ss + 120#64) ↦₆₄ x.G.pq.cap) ∗ ((x.ss + 128#64) ↦₆₄ x.G.pq.ptr) ∗
              memRegion (x.ss + 136#64) 8 ∗ vecPinDeallocX A.repAlloc x.G.pq) ∗
            memRegion (x.ss + 328#64) 16) ∗
          A.pool lim st s0 ∗ stackAt s0.sp dropSessionStructureLocal1StackX) ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    rw [satisfies_pure_sepConj] at hm'
    exact hm'.1
  refine ⟨(x, st), R, hpre, fun sf hpost => ?_⟩
  dsimp only [dropSessionStructureLocal1EventsSpecX, dropSessionStructureLocal1BudgetSpecX] at hpost ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  have hcred := stepEvents_dropSessionStructureLocal1_bounds M hcaps st
  exact ⟨⟨hpost.1, hcred.1, hcred.2.1, hcred.2.2⟩, hpost.2⟩

theorem drop_session_structure_local1_budget_placed_ok_cl [LibsignalPlacement]
    {M : AllocCostModel} [HasFineReallocCredit M]
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {H : LibsignalHooks}
    {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H]
    (hA : AllocContractsBudgetPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 6)
      (withLsCl lsmpl (dropSessionStructureLocal1BudgetSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (j := 6) (drop_session_structure_local1_budget_placed_ok hA)

/-- Explicit post-drop credit lemma: if `liveLarge st₂ ≤ L_before + ssLargeLive M G`, then after
`dropSessionStructureLocal1` transitions `st₂ ↦ st₃`, `liveLarge st₃ ≤ L_before` (`ssLargeLive M G`
is credited back). -/
theorem liveLarge_after_dropSessionStructureLocal1_le
    (M : AllocCostModel) [HasFineReallocCredit M]
    {G : SessionGhost} {L_before : Nat} {st₂ st₃ : M.σ}
    (hlive₂ : HasFineReallocCredit.liveLarge st₂ ≤ L_before + ssLargeLive M G)
    (hdrop : HasFineReallocCredit.liveLarge st₃ ≤
      HasFineReallocCredit.liveLarge st₂ - ssLargeLive M G) :
    HasFineReallocCredit.liveLarge st₃ ≤ L_before := by
  omega

/-- End-to-end `FromRecord` clone-then-drop budget composition theorem (resolving the ~208 MiB
`FromRecord` peak symbolically in `(M : AllocCostModel) [HasFineReallocCredit M]`):
starting at `liveLarge st₁ ≤ L₀ + ssLargeLive M G` (after `SessionRecord::deserialize`), cloning `G`
into exact-sized `G'` (`liveLarge st₂ ≤ L₀ + ssLargeLive M G + ssLargeLive M G'`,
`peakLarge st₂ ≤ max P₁ (L₀ + ssLargeLive M G + ssClonePeakLarge M G')`) and then executing
`dropSessionStructureLocal1` on `G` yields:
1. **Post-drop live bound:** `liveLarge st₃ ≤ L₀ + ssLargeLive M G'` (only the cloned `RatchetState`
   remains live; under Tier T2's `cLarge = 8,195` at `|bs| ≤ 2^21` on `≤ 5` honest chains,
   `208.02 MiB` transient drops back to `≤ L₀ + 109,060,099` B `≈ 104.01 MiB` post-drop);
2. **Transient peak bound:** `peakLarge st₃ ≤ max P₁ (L₀ + ssLargeLive M G + ssClonePeakLarge M G')`. -/
theorem fromRecord_clone_and_drop_budget_bounds
    (M : AllocCostModel) [HasFineReallocCredit M]
    {G G' : SessionGhost} {L₀ C₁ C₂ P₁ : Nat} {st₂ st₃ : M.σ}
    (hclone_cum : HasFineReallocCredit.cumSmall st₂ ≤ C₁ + C₂)
    (hclone_live : HasFineReallocCredit.liveLarge st₂ ≤ L₀ + ssLargeLive M G + ssLargeLive M G')
    (hclone_peak : HasFineReallocCredit.peakLarge st₂ ≤
      max P₁ (L₀ + ssLargeLive M G + ssClonePeakLarge M G'))
    (hdrop_cum : HasFineReallocCredit.cumSmall st₃ ≤ HasFineReallocCredit.cumSmall st₂)
    (hdrop_live : HasFineReallocCredit.liveLarge st₃ ≤
      HasFineReallocCredit.liveLarge st₂ - ssLargeLive M G)
    (hdrop_peak : HasFineReallocCredit.peakLarge st₃ ≤ HasFineReallocCredit.peakLarge st₂) :
    HasFineReallocCredit.cumSmall st₃ ≤ C₁ + C₂ ∧
    HasFineReallocCredit.liveLarge st₃ ≤ L₀ + ssLargeLive M G' ∧
    HasFineReallocCredit.peakLarge st₃ ≤ max P₁ (L₀ + ssLargeLive M G + ssClonePeakLarge M G') := by
  refine ⟨by omega, by omega, by omega⟩

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserBudget.DropSsLocal1Budget
