/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Segment S5 (`PqRecv`) Shared Definitions & Helpers

Defines `spqrRecvRawSpecPlaced`, the Segment S5 allocator event envelope `PqRecvEnv`, `A.atState`
representation normalizers, and shared panic/stepping helpers over `RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs

open Arm64 ProofLib ProofLib.ProgramReflection
open scoped CryptoVerification CryptoVerification.LibsignalTripleRatchet
  CryptoVerification.LibsignalTripleRatchet.Decrypt
  CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoGames.HKDF (Salt)
open CryptoGames.LibsignalSession (
  Crypto SignalProtocolError TripleRatchet SessionState MessageKeyGenerator
)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ lsroCheck lsro_intro_chk lsRustDeallocSym
)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8 vecU8At vecHeader)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser uuidTryParse errTag utf8 speWord protocolAddressAt tapeAfter
  sessionStateAt signalMessageAt
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TrGhost trAt spqrRecvResultAt spqrRecvKeyAt
  TryDecryptGhost VecArg LibsignalCodeRoLoaded withLsCodeRoLoaded
  logOff extHookStack spqrRecvStack
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt (
  blkPC_131 blkPl_131 blkLib_eq_131 tryDecryptPlacedImg tryDecryptSubStack
  tryDecryptSavedRegs tryDecryptCommonHeap segPqRecvPC_at segDeriveKeysPC_at errTailPC_at
  speTag speBodyAt
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive (
  tryDecryptMidMetaCore steps_done_of_sepWP_midMeta_placed modelFn_error_panic_eq
  mr_cut mr_cut_add stackAt_sub sp_fp_eq sp56_weaken buf_to_mr sepWP_8_mr7_to_64
  concat56_8_cbz64_zero concat56_8_cbz64_ne_zero concat56_8_cbz32_ne_zero
  byte_ne_zero_cbz32 byte_ne_zero_cbz64_32
  speBodyAt_invalidState_fold speBodyAt_pqRatchet_fold
  pointsTo8_memRegion7_to_64 pointsTo64_to_8_memRegion7
  trRestAt trAt_split_pq signalMessageRestAt signalMessageAt_split_pq
  cap_add_one_ne_zero extractLsb0_8_append56 spqrRecvRawSpec
)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive.KeyDeriveCallees (
  lsFormatInnerSym lsTryDecryptRoSym lsroCheck_tryDecryptRoSym
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv SeqEnv FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv formatInnerBudgetEnvSpec formatInnerBudgetSpec
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ConsumeMsgKeyBudget (
  steps_call_out_placed steps_call_out_placed_cro
)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  ErrTailStatePlaced PqRecvStatePlaced DeriveKeysStatePlaced
  tryDecryptOnPanic tryDecryptFnOnPanic S5SeamPlaced S5SeamXPlaced
)

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## 1. `A.atState` Representation Rewrites & Segment Combinators -/

namespace Simp

@[scoped simp] theorem sessionStateAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    sessionStateAt (A.atState lim st s) = sessionStateAt A.repAlloc := rfl

@[scoped simp] theorem trAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    trAt (A.atState lim st s) = trAt A.repAlloc := rfl

@[scoped simp] theorem trRestAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    trRestAt (A.atState lim st s) = trRestAt A.repAlloc := rfl

@[scoped simp] theorem speBodyAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    speBodyAt (A.atState lim st s) = speBodyAt A.repAlloc := rfl

@[scoped simp] theorem protocolAddressAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

@[scoped simp] theorem signalMessageAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    signalMessageAt (A.atState lim st s) = signalMessageAt A.repAlloc := rfl

@[scoped simp] theorem signalMessageRestAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    signalMessageRestAt (A.atState lim st s) = signalMessageRestAt A.repAlloc := rfl

@[scoped simp] theorem vecU8At_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecU8At (A.atState lim st s) = vecU8At A.repAlloc := rfl

@[scoped simp] theorem vecU8_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    vecU8 (A.atState lim st s) = vecU8 A.repAlloc := rfl

@[scoped simp] theorem spqrRecvKeyAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    spqrRecvKeyAt (A.atState lim st s) = spqrRecvKeyAt A.repAlloc := rfl

@[scoped simp] theorem spqrRecvResultAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    spqrRecvResultAt (A.atState lim st s) = spqrRecvResultAt A.repAlloc := rfl

@[scoped simp] theorem vecArg_at_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) (v : VecArg) :
    v.at (A.atState lim st s) = v.at A.repAlloc := rfl

end Simp

open scoped Simp
open Simp (
  sessionStateAt_atState trAt_atState trRestAt_atState speBodyAt_atState
  protocolAddressAt_atState signalMessageAt_atState signalMessageRestAt_atState
  vecU8At_atState vecU8_atState spqrRecvKeyAt_atState spqrRecvResultAt_atState
  vecArg_at_atState
)

/-- State-parameterized `steps_of_sepWP_placed` allowing `P_mid : State → SepProp` to carry
    `A.pool lim st sm`. -/
theorem steps_of_sepWP_placed_state [LibsignalPlacement] {prog : Program}
    {mid : BitVec 64} {s : State} {P R : SepProp} {P_mid : State → SepProp}
    {RegMid Out : State → Prop}
    (hmem : s.mem ⊨ P ∗ R) (hL : prog.CodeLoaded s.mem)
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm =>
      (sm.mem ⊨ Pm ∗ R) → RegMid sm ∧ (sm.mem ⊨ P_mid sm ∗ R)))
    (h2 : ∀ sm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      prog.CodeLoaded sm.mem → RegMid sm → (sm.mem ⊨ P_mid sm ∗ R) →
      ∃ s', Steps prog sm s' ∧ Out s') :
    ∃ s', Steps prog s s' ∧ Out s' := by
  rcases h1.elim hmem hL with ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, himp⟩ | ⟨_, hoom⟩⟩
  · obtain ⟨hReg, hmm'⟩ := himp hmm
    obtain ⟨s', hsteps', hout⟩ :=
      h2 sm hpc hrun (hcl.of_keepsFrozen hsteps.keepsFrozen)
        (hsteps.codeLoaded hL) hReg hmm'
    exact ⟨s', hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

theorem s5_out_add_np_evs {α : Type} {prog : Program} {s : State}
    {Ev : α → Prop} {Normal : α → State → Prop} {Panic : State → Prop} {np : Bool}
    (hnp : np = false)
    (h : ∃ s', Steps prog s s' ∧ ((∃ evs, Ev evs ∧ Normal evs s') ∨ Panic s')) :
    ∃ s', Steps prog s s' ∧ ((∃ evs, Ev evs ∧ Normal evs s' ∧ np = false) ∨ Panic s') := by
  obtain ⟨s', hsteps, (⟨evs, hev, hn⟩ | hp)⟩ := h
  · exact ⟨s', hsteps, Or.inl ⟨evs, hev, hn, hnp⟩⟩
  · exact ⟨s', hsteps, Or.inr hp⟩

theorem tryDecryptFnOnPanic_eq_tryDecryptOnPanic (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (S : SpqrModel) (x : TryDecryptGhost) (s0 sf : State) :
    tryDecryptFnOnPanic C decFn uuidTryParse S x s0 sf =
      tryDecryptOnPanic C uuidTryParse S x s0 sf := by
  unfold tryDecryptFnOnPanic tryDecryptOnPanic
  simp only [modelFn_error_panic_eq]

/-! ## 2. Budget `spqr::recv` Contract & Segment S5 Event Envelope (`PqRecvEnv`) -/

/-- Budget-threaded relocatable `[LibsignalPlacement]` `spqr::recv` raw contract, parameterized by
    `RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop` and dropping
    `allocFailedIn` from `onPanic` so only `S.recvPanics` remains. -/
def spqrRecvRawSpecPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop) :
    Spec ((VecArg × VecArg × BitVec 64) × M.σ) where
  pre := fun ((st_v, msg_v, ret), st) s =>
    ⌜FitsEnv M lim st (RecvEnv st_v.bytes msg_v.bytes)⌝ ∗
      (spqrRecvRawSpec (A.atState lim st s) S).pre (st_v, msg_v, ret) s
  post := fun ((st_v, msg_v, ret), st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜RecvEnv st_v.bytes msg_v.bytes evs⌝ ∗
      (spqrRecvRawSpec (A.atState lim (M.stepEvents evs st) sf) S).post (st_v, msg_v, ret) s0 sf
  onPanic := fun ((st_v, msg_v, _), _) s0 sf =>
    ⌜S.recvPanics st_v.bytes msg_v.bytes ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Allocator event envelope of Segment S5 (`pqRecv`):
    - on `S.recv tr.pqrState x.msg.pqRatchet = .ok _`, `RecvEnv tr.pqrState x.msg.pqRatchet`;
    - on `.error _`, `RecvEnv` followed by `fmtEnv` followed by an optional `mkg.seed` free
      (`FreeOnlyEvs`). -/
def PqRecvEnv (S : SpqrModel)
    (RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop)
    (fmtEnv : List AllocEvent → Prop := FormatInnerEnv)
    (x : TryDecryptGhost) (tr : TripleRatchet (List (BitVec 8))) :
    List AllocEvent → Prop :=
  match S.recv tr.pqrState x.msg.pqRatchet with
  | .ok _ => RecvEnv tr.pqrState x.msg.pqRatchet
  | .error _ =>
    SeqEnv (SeqEnv (RecvEnv tr.pqrState x.msg.pqRatchet) fmtEnv) FreeOnlyEvs

theorem fitsEnv_recv_of_pqRecvEnv {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    (h : FitsEnv M lim st (PqRecvEnv S RecvEnv fmtEnv x tr)) :
    FitsEnv M lim st (RecvEnv tr.pqrState x.msg.pqRatchet) := by
  unfold PqRecvEnv at h
  cases hrecv : S.recv tr.pqrState x.msg.pqRatchet <;> rw [hrecv] at h
  · exact h.seq_left.seq_left
  · exact h

theorem fitsEnv_fmt_of_pqRecvEnv_err {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {sd : Bool}
    {evs1 : List AllocEvent}
    (hrecv : S.recv tr.pqrState x.msg.pqRatchet = .error sd)
    (h : FitsEnv M lim st (PqRecvEnv S RecvEnv fmtEnv x tr))
    (h1 : RecvEnv tr.pqrState x.msg.pqRatchet evs1) :
    FitsEnv M lim (M.stepEvents evs1 st) fmtEnv := by
  unfold PqRecvEnv at h
  rw [hrecv] at h
  exact h.seq_left.seq_right h1

theorem pqRecvEnv_of_err_parts {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {fmtEnv : List AllocEvent → Prop}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {sd : Bool}
    {evs1 evs2 evs3 : List AllocEvent}
    (hrecv : S.recv tr.pqrState x.msg.pqRatchet = .error sd)
    (h1 : RecvEnv tr.pqrState x.msg.pqRatchet evs1)
    (h2 : fmtEnv evs2)
    (h3 : FreeOnlyEvs evs3) :
    PqRecvEnv S RecvEnv fmtEnv x tr ((evs1 ++ evs2) ++ evs3) := by
  unfold PqRecvEnv
  rw [hrecv]
  exact SeqEnv.append (SeqEnv.append h1 h2) h3

theorem onPanic_of_spqrRecv_budget_placed [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {S : SpqrModel}
    {RecvEnv : List (BitVec 8) → List (BitVec 8) → List AllocEvent → Prop}
    {x : TryDecryptGhost} {st_v msg_v : VecArg} {ret : BitVec 64} {st_m : M.σ}
    {F R : SepProp} {s0 sm sf : State}
    (htrace : sm.trace = s0.trace)
    (hst : st_v.bytes = x.st.pqRatchetState)
    (hmsg : msg_v.bytes = x.msg.pqRatchet)
    (h : sf.mem ⊨ ((spqrRecvRawSpecPlaced A lim S RecvEnv).onPanic
      ((st_v, msg_v, ret), st_m) sm sf ∗ F) ∗ R) :
    sf.mem ⊨ tryDecryptOnPanic C uuidTryParse S x s0 sf ∗ R := by
  dsimp only [spqrRecvRawSpecPlaced, tryDecryptOnPanic] at h ⊢
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at h
  rcases h with ⟨⟨hpan, hpref⟩, hmem⟩
  rw [← sepConj_assoc] at hmem
  rw [hst, hmsg] at hpan
  rw [htrace] at hpref
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨⟨Or.inr hpan, hpref⟩,
    Satisfies.mono (sepConj_mono_left (ProofLib.entails_anyHeap _)) hmem⟩


end LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecvBudgetDefs
