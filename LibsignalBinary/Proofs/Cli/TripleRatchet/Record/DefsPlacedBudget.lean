/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
public import LibsignalBinary.Proofs.TripleRatchet.Keys.Defs
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

/-!
# Budget-Threaded Seam States and Segment Specifications for CLI `try_decrypt_from_record`

Threads `RustCliAllocBudget M`, `SeamBudget`, and `VmPreserved` across the `[LibsignalPlacement]`
callee contracts, checkpoint seam states (`V`, `M`, `F`, `J`), segment contracts, and seam
composition on CLI Block `463`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement lsmpl withLsCodeLoaded
  lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsHandleErrorSym
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser SessionGhost
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TryDecryptGhost RecordDecryptGhost rootStack region_ok
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  regionOutcome region_reaches region_reaches_steps region_ok_of_reaches
)
open CryptoVerification.CliRatchet.DecPlaced (
  blkPC_463 blkPl_463
)
open CryptoVerification.Cli.LibsignalTripleRatchet.Record (
  recEntryPlaced recExitPlaced
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEnv FreeOnlyEvs
  rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  growOneSpeSpec setSessionStateSpec
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneSpec senderChainCloneSpec
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  SeamBudget TryDecryptEnvArgs tryDecryptEnvArgs
  FromFEnv FromMEnv FromVEnv RecordDecryptEnv
)

/-! ## Callee, Region, and Seam Specifications -/

/-- Budget-threaded `[LibsignalPlacement]` CLI `try_decrypt_with_state` contract (`allocFailedIn`
dropped from `onPanic`). -/
def tryDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Budget-threaded `[LibsignalPlacement]` CLI `try_decrypt_from_record` region contract
(`allocFailedIn` dropped from `onPanic`). -/
def recordDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (RecordDecryptEnv tdEnv x)⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜RecordDecryptEnv tdEnv x evs⌝ ∗
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Seam `V` (`+0x69c` on Block `463`) with budget state `st` and `SeamBudget` for `FromVEnv tdEnv x G₁`. -/
def VStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st (FromVEnv tdEnv x G₁) ∧
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStatePlaced
    (A.atState lim st s) ctl x G₁ R s0 s

/-- Seam `M` (`+0x7e4` on Block `463`) with budget state `st` and `SeamBudget` for `FromMEnv`. -/
def MStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FromMEnv ∧
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.MStatePlaced
    (A.atState lim st s) ctl x G₁ R s0 s

/-- Seam `F` (`+0x850` on Block `463`) with budget state `st` and `SeamBudget` for `FromFEnv`. -/
def FStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FromFEnv ∧
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.FStatePlaced
    C (A.atState lim st s) ctl parse S x R s0 s

/-- Seam `J` (`+0x1e8c` on Block `463`) with budget state `st` and `SeamBudget` for `FreeOnlyEvs`. -/
def JStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FreeOnlyEvs ∧
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.JStatePlaced
    C (A.atState lim st s) ctl parse S x R s0 s

/-! ## Segment Specifications and Composition -/

def SegClonePlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec →
  HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false) →
  HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim) →
  HookSat H "memcpy" sessionMemcpyRegionBudgetSpec →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
    (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
    (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpec C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s0.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s0 s' ∧
        ((∃ G₁ st, VStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s') ∨
         (∃ G₁ st, MStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  HookSat H "memcpy" sessionMemcpyRegionBudgetSpec →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
    (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
    (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
    (withLsCodeLoaded lsmpl
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s → rootStack ≤ s0.sp.toNat →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', JStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         (∃ st', FStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegMismatchPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
    (withLsCodeLoaded lsmpl
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', FStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegTailPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec →
  HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false) →
  H lsHandleErrorSym = some Rust.panicked →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      FStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', JStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegExitPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      JStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
          recExitPlaced (x, st_init) R s0 s'

theorem rootStack_le_of_recordPlacedPre [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {x : RecordDecryptGhost} {st_init : M.σ} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (recordDecryptPlacedSpec C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) :
    rootStack ≤ s0.sp.toNat := by
  dsimp only [recordDecryptPlacedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact CryptoVerification.Cli.LibsignalTripleRatchet.Record.rootStack_le_of_recordPlacedPre hpre.2

theorem recordDecrypt_placed_region_ok_of_seams [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hclosure : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 462)
      (withLsCodeLoaded lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)))
    (hclone : SegClonePlacedSpec C A lim ctl parse S tdEnv H)
    (hdec : SegDecryptPlacedSpec C A lim ctl parse S tdEnv H)
    (hmis : SegMismatchPlacedSpec C A lim ctl parse S tdEnv H)
    (htail : SegTailPlacedSpec C A lim ctl parse S tdEnv H)
    (hexit : SegExitPlacedSpec C A lim ctl parse S tdEnv H) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpec C A lim ctl parse S tdEnv) := by
  apply region_ok_of_reaches
  rintro ⟨x, st_init⟩ R s0 hpc hst hpre hL
  have hstk := rootStack_le_of_recordPlacedPre hpre
  have hJ : ∀ st s, JStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpec C A lim ctl parse S tdEnv) recExitPlaced (x, st_init) R s0 s :=
    fun st s hs hLs => hexit hdealloc x st_init st R s0 s hs hLs
  have hF : ∀ st s, FStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (recordDecryptPlacedSpec C A lim ctl parse S tdEnv) recExitPlaced (x, st_init) R s0 s := by
    intro st s hs hLs
    obtain ⟨s', hst', ⟨st', hj⟩ | hout⟩ := htail hshim halloc hpanic hdrop2 x st_init st R s0 s hs hLs
    · exact region_reaches_steps hst' (hJ st' s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', ⟨G₁, st₁, hv⟩ | ⟨G₁, st₁, hm⟩ | hout⟩ :=
    hclone hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 x st_init R s0 hpc hst hpre hL
  · obtain ⟨s'', hst'', ⟨st₂, hj⟩ | ⟨st₂, hf⟩ | hout⟩ :=
      hdec hmemcpy htd hset hdrop2 hgrow hclosure x st_init st₁ G₁ R s0 s' hv hstk (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hJ st₂ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF st₂ s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · obtain ⟨s'', hst'', ⟨st₂, hf⟩ | hout⟩ :=
      hmis hgrow hclosure x st_init st₁ G₁ R s0 s' hm (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hF st₂ s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

def SegDecryptFullPlacedSpec [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  HookSat H "memcpy" sessionMemcpyRegionBudgetSpec →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
    (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
    (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s → rootStack ≤ s0.sp.toNat →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', JStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         (∃ st', FStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegMismatchFullPlacedSpec [CryptoVerification.LibsignalFullPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s →
      CryptoVerification.LibsignalFrozen lsmpl s.mem →
      ((blkPC_463).rebase (blkPl_463).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_463).rebase (blkPl_463).base H) s s' ∧
        ((∃ st', FStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

theorem recordDecrypt_full_placed_region_ok_of_seams [CryptoVerification.LibsignalFullPlacement]
    {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State))
    (hshim : HookSat H lsRustNoAllocShimSym sessionShimBudgetSpec)
    (halloc : HookSat H lsRustAllocSym (rustCliAllocBudgetSpec M A lim false))
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat H "memcpy" sessionMemcpyRegionBudgetSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hcc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsc : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 468)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (htd : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 434)
      (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)))
    (hset : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 442)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_463).rebase (blkPl_463).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hclone : SegClonePlacedSpec C A lim ctl parse S tdEnv H)
    (hdec : SegDecryptFullPlacedSpec C A lim ctl parse S tdEnv H)
    (hmis : SegMismatchFullPlacedSpec C A lim ctl parse S tdEnv H)
    (htail : SegTailPlacedSpec C A lim ctl parse S tdEnv H)
    (hexit : SegExitPlacedSpec C A lim ctl parse S tdEnv H) :
    region_ok ((blkPC_463).rebase (blkPl_463).base H) recEntryPlaced recExitPlaced
      (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
        (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)) := by
  apply region_ok_of_reaches
  rintro ⟨x, st_init⟩ R s0 hpc hst hpre0 hL
  obtain ⟨hFroz0, hpre⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsFrozen hpre0
  have hstk := rootStack_le_of_recordPlacedPre hpre
  have hJ : ∀ st s, JStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpec C A lim ctl parse S tdEnv))
        recExitPlaced (x, st_init) R s0 s :=
    fun st s hs hLs => hexit hdealloc x st_init st R s0 s hs hLs
  have hF : ∀ st s, FStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_463).rebase (blkPl_463).base H)
        (CryptoVerification.LibsignalTripleRatchet.withLsFrozen lsmpl
          (recordDecryptPlacedSpec C A lim ctl parse S tdEnv))
        recExitPlaced (x, st_init) R s0 s := by
    intro st s hs hLs
    obtain ⟨s', hst', ⟨st', hj⟩ | hout⟩ := htail hshim halloc hpanic hdrop2 x st_init st R s0 s hs hLs
    · exact region_reaches_steps hst' (hJ st' s' hj) hLs
    · exact ⟨s', hst', hout⟩
  obtain ⟨s', hst', ⟨G₁, st₁, hv⟩ | ⟨G₁, st₁, hm⟩ | hout⟩ :=
    hclone hshim halloc hdealloc hmemcpy hpanic hcc hsc hdrop1 x st_init R s0 hpc hst hpre hL
  · have hFroz' :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz0 hst'.keepsFrozen
    obtain ⟨s'', hst'', ⟨st₂, hj⟩ | ⟨st₂, hf⟩ | hout⟩ :=
      hdec hmemcpy htd hset hdrop2 hgrow x st_init st₁ G₁ R s0 s' hv hstk hFroz' (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hJ st₂ s'' hj) hL
    · exact region_reaches_steps (hst'.trans hst'') (hF st₂ s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · have hFroz' :=
      CryptoVerification.libsignalFrozen_of_keepsFrozen hFroz0 hst'.keepsFrozen
    obtain ⟨s'', hst'', ⟨st₂, hf⟩ | hout⟩ :=
      hmis hgrow x st_init st₁ G₁ R s0 s' hm hFroz' (hst'.codeLoaded hL)
    · exact region_reaches_steps (hst'.trans hst'') (hF st₂ s'' hf) hL
    · exact ⟨s'', hst'.trans hst'', hout⟩
  · exact ⟨s', hst', hout⟩

end LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlacedBudget
