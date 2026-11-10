/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Placed
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import ProofLib.Placed.OpcodeExclusion

/-!
# Budget-Threaded `<Ct1SentEkReceived>::send_ct2`: Specs, Relocatable Loops, and Prologue

Defines allocator event envelopes (`UnchunkedSendCt2PreEnv`, `UnchunkedSendCt2PostEnv`)
and `[LibsignalPlacement]` `RustCliAllocBudget` contracts, and lifts the Issue-1275 loops
and Segment 1 prologue with `VmPreserved` and pool synchronization.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget

open Arm64 Arm64.Obj ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement blkLib_eq_347 blkPC_347 blkPl_347
   libsignalSessionLib lsLogFilterAddr lsmpl)
open CryptoVerification.RustHeap (vecU8 vecU8At)
open CryptoVerification.LibsignalTripleRatchet (reserveCap)
open CryptoVerification.LibsignalSpqrV1
  (Bytes MlKem issue1275NeedsFlip spqrAuthApi swapAdjacentPairs)
open CryptoVerification.SpqrV1.Drop (unchunkedCt1SentEkReceivedAt unchunkedCt2SentAt)
open CryptoVerification.SpqrV1.States.Leaves (UnchunkedSendCt2Ghost unchunkedSendCt2Stack)
open CryptoVerification.SpqrV1.Unchunked
  (ScanLoopSaved SwapLoopSaved
   sendCt2CalleeSavedAt unchunkedSendCt2PlacedRoAt vecU8HeapAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs
   RustCliAllocBudget VmPreserved fitsEvents_append
   rustAllocEvents rustDeallocEvents rustReallocEvents)
open LibsignalBinary.Heap.SpecBudget (libcruxHmacSha256Events)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (hooksException sepWP_seg_ls_vm)
open VerifiedLibraries.RustStd (checkBlockNoSvc0 blockProgram_rebase_allInstrs_not_isSvc0)

abbrev Ct1SentEkReceived :=
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1SentEkReceived

/-! ## Allocator Event Envelopes -/

/-- Conditional 2080-byte workspace allocation in Segment 2 when `issue1275NeedsFlip` triggers. -/
def sendCt2FlipAllocEvents (es : Bytes) : List AllocEvent :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then rustAllocEvents 2080 1 else []

/-- Conditional 2080-byte workspace deallocation in Segment 3 when `issue1275NeedsFlip` triggers. -/
def sendCt2FlipDeallocEvents (es : Bytes) : List AllocEvent :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then rustDeallocEvents 2080 1 else []

/-- Combined allocator events across Segments 2 and 3: optional 2080-byte `es` flip workspace
    allocation, 128-byte `ct2` buffer allocation, and optional 2080-byte workspace deallocation. -/
def sendCt2Seg23Events (es : Bytes) : List AllocEvent :=
  sendCt2FlipAllocEvents es ++ rustAllocEvents 128 1 ++ sendCt2FlipDeallocEvents es

/-- Slow-path allocator events of `ct1.reserve(128)` (`do_reserve_and_handle` at capacity `cap`
    and length `ct1Len`). -/
def sendCt2Reserve128Events (cap : BitVec 64) (ct1Len : Nat) : List AllocEvent :=
  let newCap := reserveCap cap.toNat ct1Len 128
  if cap = 0#64 then rustAllocEvents newCap 1
  else rustReallocEvents cap.toNat newCap 1

/-- Allocator event envelope of Segment 4 (`ct1.reserve(128)`): either `[]` on the spare-capacity
    fast path (`128 ≤ cap - ct1Len`), or `sendCt2Reserve128Events cap ct1Len` on the slow path
    (`ct1Len ≤ cap.toNat ≤ ct1Len + 127`). -/
def SendCt2Reserve128Env (ct1Len : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  ∃ cap : BitVec 64, ct1Len ≤ cap.toNat ∧ cap.toNat ≤ ct1Len + 127 ∧
    evs = sendCt2Reserve128Events cap ct1Len

theorem SendCt2Reserve128Env.nil (ct1Len : Nat) : SendCt2Reserve128Env ct1Len [] :=
  Or.inl rfl

theorem SendCt2Reserve128Env.slow {cap : BitVec 64} {ct1Len : Nat}
    (hle : ct1Len ≤ cap.toNat) (hhi : cap.toNat ≤ ct1Len + 127) :
    SendCt2Reserve128Env ct1Len (sendCt2Reserve128Events cap ct1Len) :=
  Or.inr ⟨cap, hle, hhi, rfl⟩

/-- Allocation events in Segment 5a prior to trailing buffer drops:
    `slice_concat_3` (`35 + 8 + (ct1Len + 128)` bytes) followed by `libcrux_hmac::hmac`. -/
def sendCt2ConcatHmacEvents (ct1Len : Nat) : List AllocEvent :=
  rustAllocEvents (35 + 8 + (ct1Len + 128)) 1 ++ libcruxHmacSha256Events

/-- Allocation-phase prefix envelope of `<Ct1SentEkReceived>::send_ct2` (Segments 2–5a up to
    `libcrux_hmac::hmac`), prior to the four trailing `FreeOnlyEvs` buffer deallocations. -/
def UnchunkedSendCt2PreEnv {F : ShaCompress} (x : UnchunkedSendCt2Ghost F)
    (evs : List AllocEvent) : Prop :=
  ∃ evsRes : List AllocEvent,
    SendCt2Reserve128Env x.st.ct1.length evsRes ∧
    evs = sendCt2Seg23Events x.st.es ++ evsRes ++ sendCt2ConcatHmacEvents x.st.ct1.length

/-- Postcondition allocator event envelope of `<Ct1SentEkReceived>::send_ct2` (Block `347`):
    an allocation prefix in `UnchunkedSendCt2PreEnv x` followed by `FreeOnlyEvs` from dropping
    the temporary MAC input buffer and consumed `ct1`, `es`, and `ek` `Vec<u8>` buffers. -/
def UnchunkedSendCt2PostEnv {F : ShaCompress} (x : UnchunkedSendCt2Ghost F)
    (evs : List AllocEvent) : Prop :=
  ∃ evsPre evsFree : List AllocEvent,
    UnchunkedSendCt2PreEnv x evsPre ∧ FreeOnlyEvs evsFree ∧ evs = evsPre ++ evsFree

abbrev UnchunkedSendCt2Env {F : ShaCompress} := @UnchunkedSendCt2PostEnv F

theorem UnchunkedSendCt2PostEnv.of_pre {F : ShaCompress} {x : UnchunkedSendCt2Ghost F}
    {evs : List AllocEvent} (h : UnchunkedSendCt2PreEnv x evs) :
    UnchunkedSendCt2PostEnv x evs :=
  ⟨evs, [], h, FreeOnlyEvs.nil, (List.append_nil _).symm⟩

/-! ## Budget-Threaded Specifications and Postconditions -/

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded relocatable specification of
    `<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2` (Block `347`). -/
def unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PreEnv PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.outA ∧ s.readReg64 .x1 = x.stA ∧
      x.st.send_ct2 K = .ok (x.outUc, x.ct2, x.mac) ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.outA 104 ∗
      unchunkedCt1SentEkReceivedAt A.repAlloc x.stA x.st ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim st s ∗ stackAt s.sp unchunkedSendCt2Stack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ PostEnv x evs⌝ ∗
      unchunkedCt2SentAt A.repAlloc x.outA x.outUc ∗
      vecU8 A.repAlloc (x.outA + 56#64) x.ct2 ∗
      vecU8 A.repAlloc (x.outA + 80#64) x.mac ∗
      memRegion x.stA 128 ∗
      unchunkedSendCt2PlacedRoAt ∗
      A.pool lim (M.stepEvents evs st) sf ∗
      stackAt s0.sp unchunkedSendCt2Stack

abbrev unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) :=
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K Env Env

abbrev unchunkedCt1SentEkReceivedSendCt2PlacedSpec [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) :
    Spec (UnchunkedSendCt2Ghost F × M.σ) :=
  unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K
    UnchunkedSendCt2PreEnv UnchunkedSendCt2PostEnv

def UnchunkedCt1SentEkReceivedSendCt2PlacedOk [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem) (H : LibsignalHooks) : Prop :=
  subroutine_ok ((blkPC_347).rebase (blkPl_347).base H) (blkPl_347).base
    (unchunkedCt1SentEkReceivedSendCt2PlacedSpec M A lim F K)

abbrev sendCt2PlacedPostQOfPostEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (PostEnv : UnchunkedSendCt2Ghost F → List AllocEvent → Prop)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ R) →
      (sf.mem ⊨
        (unchunkedCt1SentEkReceivedSendCt2PlacedSpecOfPrePostEnv M A lim F K
          UnchunkedSendCt2PreEnv PostEnv).post (x, st) s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev sendCt2PlacedPostQOfEnv [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (Env : UnchunkedSendCt2Ghost F → List AllocEvent → Prop)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  sendCt2PlacedPostQOfPostEnv M A lim F K Env x st s0 R

abbrev sendCt2PlacedPostQ [LibsignalPlacement]
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (F : ShaCompress) (K : MlKem)
    (x : UnchunkedSendCt2Ghost F) (st : M.σ) (s0 : State) (R : SepProp) :
    State → SepProp → Prop :=
  sendCt2PlacedPostQOfPostEnv M A lim F K UnchunkedSendCt2PostEnv x st s0 R

/-- Panic postcondition of budget-threaded `send_ct2`: unreachable (`False`) because every panic
    path in `send_ct2` is either guarded by `x.st.send_ct2 K = .ok _` or an allocator OOM. -/
abbrev sendCt2PlacedPostQp : State → SepProp → Prop :=
  fun _ _ => False

/-! ## `VmPreserved` Lifting for Instruction Segments -/

private theorem swapLoopSaved_of_setMem {s sm' : State} {m_strip m_real : Memory}
    (h : SwapLoopSaved (s.setMem m_strip) sm') :
    SwapLoopSaved s (sm'.setMem m_real) := by
  rcases h with ⟨h19, h20, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp, htr, hv⟩
  cases s; cases sm'
  exact ⟨h19, h20, h22, h23, h24, h25, h26, h27, h28, h29, h30, hsp, htr, hv⟩

private theorem scanLoopSaved_of_setMem {s sm' : State} {m_strip m_real : Memory}
    (h : ScanLoopSaved (s.setMem m_strip) sm') :
    ScanLoopSaved s (sm'.setMem m_real) := by
  rcases h with ⟨h19, h20, h23, h24, h25, h26, h27, h28, h29, h30, hsp, htr, hv⟩
  cases s; cases sm'
  exact ⟨h19, h20, h23, h24, h25, h26, h27, h28, h29, h30, hsp, htr, hv⟩

private theorem blk347_patchSafe_noSvc0 :
    (libsignalSessionLib.blockLib 347).text.patchSafe svc0Pat = true := by
  rw [← blkLib_eq_347]; decide +kernel

private theorem blk347_patchSafe_noMsrTpidrEl0 :
    (libsignalSessionLib.blockLib 347).text.patchSafe msrTpidrEl0Pat = true := by
  rw [← blkLib_eq_347]; decide +kernel

private theorem option_or_isSome {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

private theorem findSome?_ite_map_status {α : Type} (l : List (String × Nat)) (off : Nat)
    (tbl : String → Option α) {f : State → State}
    (h : (l.findSome? fun (n, o) =>
      if o == off then (tbl n).map (fun _ (s : State) => s.setStatus (.Exception "ext")) else none) =
      some f)
    (s : State) : (f s).status = .Exception "ext" := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?] at h
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact ih h
    · simp only [ho, ↓reduceIte] at h
      cases htn : tbl n with
      | none => simp only [htn, Option.map] at h; exact ih h
      | some _ => simp only [htn, Option.map] at h; injection h with hf; subst hf; cases s; rfl

private theorem blockProgram_hooksException_externAt?_isSome (lib : MultiPlacedLib)
    (pl : MultiPlacement) (i : Nat) (H : LibsignalHooks) (pc : BitVec 64) :
    ((lib.blockProgram pl i (hooksException H)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome, option_or_isSome]
  rw [findSome?_isSome_congr _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then hooksException H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;> simp [hooksException]

private theorem blockProgram_hooksException_externAt?_not_running {lib : MultiPlacedLib}
    {pl : MultiPlacement} {i : Nat} {H : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hooksException H)).externAt? pc = some f)
    (s : State) : (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h
  dsimp only [hooksException] at h
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h
  rw [findSome?_ite_map_status _ _ _ h]
  decide

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem blk347_allInstrs_noSvc0 (pl : MultiPlacement) (H : LibsignalHooks) :
    (libsignalSessionLib.blockProgram pl 347 H).allInstrs (fun ins => !ins.isSvc0) = true :=
  PlacedLib.program_noSvc0_of_patchSafe blk347_patchSafe_noSvc0
    (libsignalSessionLib.blockPlacement pl 347) (fun _ => none) H

private theorem blk347_allInstrs_noMsrTpidrEl0 (pl : MultiPlacement) (H : LibsignalHooks) :
    (libsignalSessionLib.blockProgram pl 347 H).allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
  PlacedLib.program_noMsrTpidrEl0_of_patchSafe blk347_patchSafe_noMsrTpidrEl0
    (libsignalSessionLib.blockPlacement pl 347) (fun _ => none) H

private theorem steps_multi_lift_strip_vm (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    (H : LibsignalHooks)
    (hall_svc : (lib.blockProgram pl i (hooksException H)).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr : (lib.blockProgram pl i (hooksException H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps (lib.blockProgram pl i (hooksException H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := lib.blockProgram pl i (hooksException H)
    let P := lib.blockProgram pl i H
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 → Q.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∧
        Steps P s1 sf ∧ VmPreserved s1 sf := by
  intro Q P
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := by
      cases hrest with
      | refl => exact hrun_f
      | step hs _ => cases hs <;> assumption
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      exact False.elim (blockProgram_hooksException_externAt?_not_running he _ hrb')
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_codeLoaded_of_keep hL1
      have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
        strip_execOnlyIn_of_keep Q s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := (by cases s1; rfl)
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := (by cases s1; rfl)
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
          blockProgram_hooksException_externAt?_isSome lib pl i H s1.pc
        rw [his] at hfe'
        cases heP : (P.externAt? s1.pc).isSome
        · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
          by_cases hal_pc : s1.pc.toNat % 4 = 0
          · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
            split at hfe'
            · contradiction
            · rename_i hce'
              have hce : s1.mem.canExec s1.pc 4 = true := by
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                unfold Memory.canExec at hce' ⊢
                rw [Memory.allPerm_iff] at hce' ⊢
                intro k hk
                have hxk := hce' k hk
                rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
              have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                  s1.mem.read32 s1.pc := by
                simp [Memory.read32, ProofLib.strip_read8]
              rw [hr32] at hfe'
              simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
              exact hfe'
          · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
            contradiction
        · simp only [heP, ↓reduceIte] at hfe'
          contradiction
      have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
          ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
      obtain ⟨sf, hsf_eq, hsteps_P, hvm_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q hLQ_next
      have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
      have htp1 := Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        VmPreserved.trans (hnsp1.toVmPreserved htp1) hvm_rest⟩

private theorem sepWP_seg_multi_lift_vm {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {prog Q : Program} {i : Nat} {H : LibsignalHooks}
    (hP_eq : prog = lib.blockProgram mpl i H)
    (hQ_eq : Q = lib.blockProgram mpl i (hooksException H))
    (hall_svc : (lib.blockProgram mpl i (hooksException H)).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr : (lib.blockProgram mpl i (hooksException H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {post₁ : Memory → State → SepProp → Prop}
    {post₂ : State → SepProp → Prop}
    (horig : ∀ m_strip : Memory,
      SepWP Q target (s.setMem m_strip) Pre (post₁ m_strip))
    (himp : ∀ (m_strip m_real : Memory) (sm' : State) (Pm : SepProp),
      VmPreserved s (sm'.setMem m_real) →
      post₁ m_strip sm' Pm →
      post₂ (sm'.setMem m_real) Pm) :
    SepWP prog target s Pre post₂ := by
  subst hP_eq; subst hQ_eq
  let Q0 := lib.blockProgram mpl i (hooksException H)
  let keep := ProofLib.progKeep Q0
  let m_strip := ProofLib.stripExecOutside keep s.mem
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  have hL_Q0 : Q0.CodeLoaded s.mem := hL.of_base_code rfl rfl
  have hL_Qstrip : Q0.CodeLoaded m_strip := strip_codeLoaded_of_keep hL_Q0
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hstrip_eq : s.setMem m_strip = ProofLib.stripS keep s := by cases s; rfl
  have hm_strip' : (s.setMem m_strip).mem ⊨ Pre ∗ R_view := by
    cases s; exact hm_strip
  have hL_Qstrip' : Q0.CodeLoaded (s.setMem m_strip).mem := by
    cases s; exact hL_Qstrip
  obtain ⟨sm', hstepsQ, ⟨hpcm', hrun_m', Pm, hmm', hpost1⟩ | ⟨_, hoom⟩⟩ :=
      SepWP.to_reaches_pc (horig m_strip) hm_strip' hL_Qstrip'
  · obtain ⟨sm, hsm_eq, hstepsP0, hvm⟩ :=
      steps_multi_lift_strip_vm lib mpl i H hall_svc hall_msr hstepsQ hrun_m' s hstrip_eq hL_Q0
    have hsm_setMem : sm'.setMem sm.mem = sm := by
      rw [hsm_eq]; cases sm; rfl
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := hvm.perm_eq
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hvm' : VmPreserved s (sm'.setMem sm.mem) := hsm_setMem.symm ▸ hvm
    have hpost2 := himp m_strip sm.mem sm' Pm hvm' hpost1
    rw [hsm_setMem] at hpost2
    have hpcm : sm.pc = target := by rw [← hsm_setMem]; exact hpcm'
    have hrunm : sm.status = .Running := by rw [← hsm_setMem]; exact hrun_m'
    exact ⟨sm, hstepsP0, Or.inl ⟨hpcm, hrunm, Pm, hmm, hpost2⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

private theorem sepWP_lift_347_vm [LibsignalPlacement] {H : LibsignalHooks}
    {target : BitVec 64} {s : State} {Pre : SepProp}
    {post₁ : Memory → State → SepProp → Prop}
    {post₂ : State → SepProp → Prop}
    (horig : ∀ m_strip : Memory,
      SepWP ((blkPC_347).rebase (blkPl_347).base (hooksException H))
        target (s.setMem m_strip) Pre (post₁ m_strip))
    (himp : ∀ (m_strip m_real : Memory) (sm' : State) (Pm : SepProp),
      VmPreserved s (sm'.setMem m_real) →
      post₁ m_strip sm' Pm →
      post₂ (sm'.setMem m_real) Pm) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H) target s Pre post₂ :=
  sepWP_seg_multi_lift_vm
    (inferInstance : IsLsBlockProg ((blkPC_347).rebase (blkPl_347).base H) 347 H).eq_blockProgram
    (inferInstance :
      IsLsBlockProg ((blkPC_347).rebase (blkPl_347).base (hooksException H))
        347 (hooksException H)).eq_blockProgram
    (blk347_allInstrs_noSvc0 lsmpl (hooksException H))
    (blk347_allInstrs_noMsrTpidrEl0 lsmpl (hooksException H))
    horig himp

/-! ## Issue-1275 Loops with `VmPreserved` -/

theorem swap_loop_step_last_placed [LibsignalPlacement] {H : LibsignalHooks}
    (basePtr : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hpc : s.pc = (blkPl_347).base + 516#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = 2046#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 552#64)
      s (((basePtr + 2046#64) ↦ₛ [b0, b1]) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + 2046#64) ↦ₛ [b1, b0]) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.swap_loop_step_last_placed (H := hooksException H)
        basePtr b0 b1 (s.setMem m_strip) Frame
        (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx22) (by cases s; exact hx8))
    fun _ _ sm' _ hvm ⟨hPf, hx21, hsaved⟩ =>
      ⟨hPf, by cases sm'; exact hx21, swapLoopSaved_of_setMem hsaved, hvm⟩

theorem swap_loop_step_more_placed [LibsignalPlacement] {H : LibsignalHooks}
    (basePtr off : BitVec 64) (b0 b1 : BitVec 8) (s : State) (Frame : SepProp)
    (hoff : off.toNat < 2046)
    (hpc : s.pc = (blkPl_347).base + 516#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 516#64)
      s (((basePtr + off) ↦₈ b0) ∗ ((basePtr + off + 1#64) ↦₈ b1) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦₈ b1) ∗ ((basePtr + off + 1#64) ↦₈ b0) ∗ Frame) ∧
        sf.readReg64 .x8 = off + 2#64 ∧
        SwapLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.swap_loop_step_more_placed (H := hooksException H)
        basePtr off b0 b1 (s.setMem m_strip) Frame hoff
        (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx22) (by cases s; exact hx8))
    fun _ _ sm' _ hvm ⟨hPf, hx8', hsaved⟩ =>
      ⟨hPf, by cases sm'; exact hx8', swapLoopSaved_of_setMem hsaved, hvm⟩

theorem swap_loop_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (basePtr : BitVec 64)
    (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp)
    (hne : bs ≠ [])
    (hmod : bs.length % 2 = 0)
    (hsum : off.toNat + bs.length = 2048)
    (hpc : s.pc = (blkPl_347).base + 516#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 552#64)
      s (((basePtr + off) ↦ₛ bs) ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.swap_loop_placed_ok (H := hooksException H)
        basePtr bs off (s.setMem m_strip) Frame hne hmod hsum
        (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx22) (by cases s; exact hx8))
    fun _ _ sm' _ hvm ⟨hPf, hx21, hsaved⟩ =>
      ⟨hPf, by cases sm'; exact hx21, swapLoopSaved_of_setMem hsaved, hvm⟩

theorem swap_loop_placed_pool_ok [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (basePtr : BitVec 64)
    (bs : Bytes) (off : BitVec 64) (s : State) (Frame : SepProp)
    (hne : bs ≠ [])
    (hmod : bs.length % 2 = 0)
    (hsum : off.toNat + bs.length = 2048)
    (hpc : s.pc = (blkPl_347).base + 516#64)
    (hrun : s.status = .Running)
    (hx22 : s.readReg64 .x22 = basePtr)
    (hx8 : s.readReg64 .x8 = off) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 552#64)
      s (((basePtr + off) ↦ₛ bs) ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = (((basePtr + off) ↦ₛ swapAdjacentPairs bs) ∗ A.pool lim st sf ∗ Frame) ∧
        sf.readReg64 .x21 = 1#64 ∧
        SwapLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (swap_loop_placed_ok basePtr bs off s (A.pool lim st s ∗ Frame)
      hne hmod hsum hpc hrun hx22 hx8)
    fun sf Pf hpcm hrunm ⟨hPf, hx21, hsaved, hvm⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hx21, hsaved, hvm⟩

theorem scan_loop_false_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (blkPl_347).base + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 552#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.scan_loop_false_placed_ok (H := hooksException H)
        ptr bs rem (s.setMem m_strip) Frame
        hbs_ne hbs_mod hbs_le hrem hflip
        (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx8) (by cases s; exact hx9)
        (by cases s; exact hx10) (by cases s; exact hx11)
        (by cases s; exact hx13) (by cases s; exact hx28))
    fun _ _ sm' _ hvm ⟨hPf, hx21, hx22, hx28', hsaved⟩ =>
      ⟨hPf, by cases sm'; exact hx21,
        by cases s; cases sm'; exact hx22,
        by cases sm'; exact hx28',
        scanLoopSaved_of_setMem hsaved, hvm⟩

theorem scan_loop_false_placed_pool_ok [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = false)
    (hpc : s.pc = (blkPl_347).base + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64)
    (hx28 : s.readReg64 .x28 = bv% (2 ^ 64 - 1)) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 552#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ Frame) ∧
        sf.readReg64 .x21 = 0#64 ∧
        sf.readReg64 .x22 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (scan_loop_false_placed_ok ptr bs rem s (A.pool lim st s ∗ Frame)
      hbs_ne hbs_mod hbs_le hrem hflip hpc hrun hx8 hx9 hx10 hx11 hx13 hx28)
    fun sf Pf hpcm hrunm ⟨hPf, hx21, hx22, hx28', hsaved, hvm⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hx21, hx22, hx28', hsaved, hvm⟩

theorem scan_loop_true_placed_ok [LibsignalPlacement] {H : LibsignalHooks}
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (blkPl_347).base + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 472#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ Frame) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.scan_loop_true_placed_ok (H := hooksException H)
        ptr bs rem (s.setMem m_strip) Frame
        hbs_ne hbs_mod hbs_le hrem hflip
        (by cases s; exact hpc) (by cases s; exact hrun)
        (by cases s; exact hx8) (by cases s; exact hx9)
        (by cases s; exact hx10) (by cases s; exact hx11)
        (by cases s; exact hx13))
    fun _ _ _ _ hvm ⟨hPf, hsaved⟩ =>
      ⟨hPf, scanLoopSaved_of_setMem hsaved, hvm⟩

theorem scan_loop_true_placed_pool_ok [LibsignalPlacement] {H : LibsignalHooks}
    {M : AllocCostModel} (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ptr : BitVec 64) (bs : Bytes) (rem : BitVec 64) (s : State) (Frame : SepProp)
    (hbs_ne : bs ≠ [])
    (hbs_mod : bs.length % 2 = 0)
    (hbs_le : bs.length ≤ 512)
    (hrem : rem = BitVec.ofNat 64 bs.length)
    (hflip : issue1275NeedsFlip bs = true)
    (hpc : s.pc = (blkPl_347).base + 136#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = ptr)
    (hx9 : s.readReg64 .x9 = rem)
    (hx10 : s.readReg64 .x10 = 2#64)
    (hx11 : s.readReg64 .x11 = 65534#64)
    (hx13 : s.readReg64 .x13 = 65535#64) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 472#64)
      s ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st s ∗ Frame)
      (fun sf Pf =>
        Pf = ((ptr ↦ₛ bs) ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim st sf ∗ Frame) ∧
        ScanLoopSaved s sf ∧
        VmPreserved s sf) := by
  refine SepWP.seq
    (scan_loop_true_placed_ok ptr bs rem s (A.pool lim st s ∗ Frame)
      hbs_ne hbs_mod hbs_le hrem hflip hpc hrun hx8 hx9 hx10 hx11 hx13)
    fun sf Pf hpcm hrunm ⟨hPf, hsaved, hvm⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm ⟨rfl, hsaved, hvm⟩

/-! ## Segment 1: Prologue (`+0x00 → +0x88`) -/

theorem send_ct2_prologue_to_scan_placed [LibsignalPlacement] {H : LibsignalHooks}
    {F : ShaCompress} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (blkPl_347).base)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 136#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A.repAlloc ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        Frame)
      (fun sf Pf =>
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        VmPreserved s0 sf) := by
  rcases s0 with
    ⟨regs, vregs, sp, pc, pstate, mem, tpidrEl0, fpsr, brkStart, brk, fs, oracle, oracleIdx,
     exclFails, trace, status, symtab, sigActions, sigAltStack, physMemAvail⟩
  let s0 : State :=
    ⟨regs, vregs, sp, pc, pstate, mem, tpidrEl0, fpsr, brkStart, brk, fs, oracle, oracleIdx,
     exclFails, trace, status, symtab, sigActions, sigAltStack, physMemAvail⟩
  refine sepWP_lift_347_vm
    (fun m_strip =>
      CryptoVerification.SpqrV1.Unchunked.send_ct2_prologue_to_scan_placed (H := hooksException H)
        A.repAlloc outA stA st rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr
        l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
        (s0.setMem m_strip) Frame hes_len hek_len hpc hrun hsp hx0 hx1)
    fun _ _ sm' _ hvm
      ⟨hPf, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
        hx25, hx26, hx27, hx28, hx29⟩ => by
      cases sm'
      exact ⟨hPf, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
        hx25, hx26, hx27, hx28, hx29, hvm⟩

theorem send_ct2_prologue_to_scan_placed_pool [LibsignalPlacement] {H : LibsignalHooks}
    {F : ShaCompress} {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (stCost : M.σ)
    (outA stA : BitVec 64)
    (st : Ct1SentEkReceived (spqrAuthApi F))
    (rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr ct1Cap ct1Ptr : BitVec 64)
    (l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : BitVec 64)
    (s0 : State) (Frame : SepProp)
    (hes_len : st.es.length = 2080)
    (hek_len : st.ek.length = 1152)
    (hpc : s0.pc = (blkPl_347).base)
    (hrun : s0.status = .Running)
    (hsp : (s0.sp &&& 15#64 == 0#64) = true)
    (hx0 : s0.readReg64 .x0 = outA)
    (hx1 : s0.readReg64 .x1 = stA) :
    SepWP ((blkPC_347).rebase (blkPl_347).base H)
      ((blkPl_347).base + 136#64)
      s0
      ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
        ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
        ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
        ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
        ((stA + 48#64) ↦₆₄ esCap) ∗ ((stA + 56#64) ↦₆₄ esPtr) ∗
        ((stA + 64#64) ↦₆₄ BitVec.ofNat 64 st.es.length) ∗
        ((stA + 72#64) ↦₆₄ ekCap) ∗ ((stA + 80#64) ↦₆₄ ekPtr) ∗
        ((stA + 88#64) ↦₆₄ BitVec.ofNat 64 st.ek.length) ∗
        ((stA + 96#64) ↦₆₄ ct1Cap) ∗ ((stA + 104#64) ↦₆₄ ct1Ptr) ∗
        ((stA + 112#64) ↦₆₄ BitVec.ofNat 64 st.ct1.length) ∗
        ((stA + 120#64) ↦₆₄ st.epoch) ∗
        vecU8HeapAt A.repAlloc ct1Cap ct1Ptr st.ct1 ∗
        ((s0.sp - 328#64) ↦₆₄ l0) ∗ ((s0.sp - 320#64) ↦₆₄ l1) ∗
        ((s0.sp - 312#64) ↦₆₄ l2) ∗ ((s0.sp - 304#64) ↦₆₄ l3) ∗
        ((s0.sp - 296#64) ↦₆₄ l4) ∗ ((s0.sp - 288#64) ↦₆₄ l5) ∗
        ((s0.sp - 272#64) ↦₆₄ s64) ∗ memRegion (s0.sp - 264#64) 120 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((s0.sp - 96#64) ↦₆₄ c0) ∗ ((s0.sp - 88#64) ↦₆₄ c1) ∗
        ((s0.sp - 80#64) ↦₆₄ c2) ∗ ((s0.sp - 72#64) ↦₆₄ c3) ∗
        ((s0.sp - 64#64) ↦₆₄ c4) ∗ ((s0.sp - 56#64) ↦₆₄ c5) ∗
        ((s0.sp - 48#64) ↦₆₄ c6) ∗ ((s0.sp - 40#64) ↦₆₄ c7) ∗
        ((s0.sp - 32#64) ↦₆₄ c8) ∗ ((s0.sp - 24#64) ↦₆₄ c9) ∗
        ((s0.sp - 16#64) ↦₆₄ c10) ∗ ((s0.sp - 8#64) ↦₆₄ c11) ∗
        A.pool lim stCost s0 ∗ Frame)
      (fun sf Pf =>
        Pf = ((stA ↦₆₄ rkCap) ∗ ((stA + 8#64) ↦₆₄ rkPtr) ∗
          ((stA + 16#64) ↦₆₄ BitVec.ofNat 64 st.auth.rootKey.length) ∗
          ((stA + 24#64) ↦₆₄ mkCap) ∗ ((stA + 32#64) ↦₆₄ mkPtr) ∗
          ((stA + 40#64) ↦₆₄ BitVec.ofNat 64 st.auth.macKey.length) ∗
          memRegion (stA + 48#64) 80 ∗
          ((s0.sp - 328#64) ↦₆₄ esCap) ∗ ((s0.sp - 320#64) ↦₆₄ ekCap) ∗
          ((s0.sp - 312#64) ↦₆₄ st.epoch) ∗
          vecU8At A.repAlloc (s0.sp - 304#64) ct1Cap ct1Ptr st.ct1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          ((s0.sp - 120#64) ↦₆₄ e0) ∗
          sendCt2CalleeSavedAt s0 ∗
          A.pool lim stCost sf ∗ Frame) ∧
        sf.sp = s0.sp - 336#64 ∧
        sf.trace = s0.trace ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        sf.readReg64 .x8 = esPtr + 1536#64 ∧
        sf.readReg64 .x9 = 512#64 ∧
        sf.readReg64 .x10 = 2#64 ∧
        sf.readReg64 .x11 = 65534#64 ∧
        sf.readReg64 .x13 = 65535#64 ∧
        sf.readReg64 .x19 = esPtr ∧
        sf.readReg64 .x20 = ekPtr ∧
        sf.readReg64 .x23 = outA ∧
        sf.readReg64 .x24 = stA ∧
        sf.readReg64 .x25 = mkPtr ∧
        sf.readReg64 .x26 = BitVec.ofNat 64 st.auth.macKey.length ∧
        sf.readReg64 .x27 = 1152#64 ∧
        sf.readReg64 .x28 = bv% (2 ^ 64 - 1) ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        VmPreserved s0 sf) := by
  refine SepWP.seq
    (send_ct2_prologue_to_scan_placed A outA stA st rkCap rkPtr mkCap mkPtr esCap esPtr ekCap ekPtr
      ct1Cap ct1Ptr l0 l1 l2 l3 l4 l5 s64 e0 c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11
      s0 (A.pool lim stCost s0 ∗ Frame) hes_len hek_len hpc hrun hsp hx0 hx1)
    fun sf Pf hpcm hrunm
      ⟨hPf, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
        hx25, hx26, hx27, hx28, hx29, hvm⟩ => ?_
  rw [hPf, ← A.pool_of_vmPreserved hvm]
  exact SepWP.done hpcm hrunm
    ⟨rfl, hsp', htr', hvregs', hx8, hx9, hx10, hx11, hx13, hx19, hx20, hx23, hx24,
      hx25, hx26, hx27, hx28, hx29, hvm⟩

end LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2PlacedBudget
