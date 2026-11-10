/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# Budget-Threaded Seam States and Segment Specifications for `try_decrypt_from_record`

Defines `SeamBudget` combinators, per-seam remaining-allocation envelopes (`SegCloneEnv`, `FromVEnv`,
`FromMEnv`, `FromFEnv`), and `RustCliAllocBudget`-threaded seam and segment contracts for the
relocatable `try_decrypt_from_record` region.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (
  Crypto SessionState SignalMessage MessageType
)
open CryptoVerification (
  LibsignalPlacement lsmpl withLsCodeLoaded
  lsRustNoAllocShimSym lsRustAllocSym lsRustDeallocSym lsHandleErrorSym
)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser AddrGhost SessionGhost SignalMessageGhost TailVecGhost
)
open CryptoVerification.LibsignalTripleRatchet (
  SpqrModel TryDecryptGhost RecordDecryptGhost rootStack region_ok
)
open CryptoVerification.LibsignalTripleRatchet.Record (
  blkPC_197 blkPl_197
  recEntryPlaced recVPCPlaced recMPCPlaced recFPCPlaced recJPCPlaced recExitPlaced
  CloneRel regionOutcome region_reaches region_reaches_steps region_ok_of_reaches
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
  FitsEvents FitsEnv FreeOnlyEvs SeqEnv fitsEvents_append
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionShimBudgetSpec sessionMemcpyRegionBudgetSpec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  GrowOneSpeEnv growOneSpeSpec setSessionStateSpec
  dropSessionStructureLocal1Spec dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneEvents senderChainCloneEvents chainCloneSpec senderChainCloneSpec
)

/-! ## `SeamBudget` threading combinators -/

/-- At an intermediate seam with current cost-model state `st`, some `evs_pre` has already been
    emitted from `st_init` (`st = M.stepEvents evs_pre st_init`), every event sequence in `remEnv`
    fits from `st`, and prepending `evs_pre` to any `evs_rem` in `remEnv` lands in `fullEnv`. -/
def SeamBudget (M : AllocCostModel) (lim : BudgetLimits)
    (fullEnv : List AllocEvent → Prop) (st_init st : M.σ)
    (remEnv : List AllocEvent → Prop) : Prop :=
  FitsEnv M lim st remEnv ∧
  ∃ evs_pre : List AllocEvent,
    st = M.stepEvents evs_pre st_init ∧
    ∀ evs_rem, remEnv evs_rem → fullEnv (evs_pre ++ evs_rem)

/-- Initialize `SeamBudget` at region entry (`evs_pre = []`). -/
theorem SeamBudget.init {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv : List AllocEvent → Prop} {st_init : M.σ}
    (h : FitsEnv M lim st_init fullEnv) :
    SeamBudget M lim fullEnv st_init st_init fullEnv :=
  ⟨h, [], rfl, fun _ hrem => hrem⟩

/-- Monotonically narrow the remaining-events envelope `remEnv`. -/
theorem SeamBudget.weaken {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv rem₁ rem₂ : List AllocEvent → Prop} {st_init st : M.σ}
    (hs : SeamBudget M lim fullEnv st_init st rem₁)
    (hsub : ∀ evs, rem₂ evs → rem₁ evs) :
    SeamBudget M lim fullEnv st_init st rem₂ := by
  rcases hs with ⟨hfits, evs_pre, hst, hfull⟩
  exact ⟨fun evs h2 => hfits evs (hsub evs h2),
    evs_pre, hst, fun evs h2 => hfull evs (hsub evs h2)⟩

/-- Extract `FitsEnv` for the next segment/callee envelope `segEnv` when `rem₂` is inhabited. -/
theorem SeamBudget.fitsSeg {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv rem₁ segEnv rem₂ : List AllocEvent → Prop} {st_init st : M.σ}
    (hs : SeamBudget M lim fullEnv st_init st rem₁)
    (hseq : ∀ e1 e2, segEnv e1 → rem₂ e2 → rem₁ (e1 ++ e2))
    (hne : ∃ e2, rem₂ e2) :
    FitsEnv M lim st segEnv := by
  rcases hne with ⟨e2, he2⟩
  intro e1 he1
  have h12 := hs.1 (e1 ++ e2) (hseq e1 e2 he1 he2)
  exact ((fitsEvents_append M lim e1 e2 st).mp h12).1

/-- Advance `SeamBudget` across an emitted segment/callee event list `evs_seg`. -/
theorem SeamBudget.step {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv rem₁ segEnv rem₂ : List AllocEvent → Prop} {st_init st : M.σ}
    {evs_seg : List AllocEvent}
    (hs : SeamBudget M lim fullEnv st_init st rem₁)
    (hseq : ∀ e1 e2, segEnv e1 → rem₂ e2 → rem₁ (e1 ++ e2))
    (hseg : segEnv evs_seg) :
    SeamBudget M lim fullEnv st_init (M.stepEvents evs_seg st) rem₂ := by
  rcases hs with ⟨hfits, evs_pre, rfl, hfull⟩
  refine ⟨fun e2 he2 => ?_, evs_pre ++ evs_seg,
    (M.stepEvents_append evs_pre evs_seg st_init).symm,
    fun e2 he2 => ?_⟩
  · exact ((fitsEvents_append M lim evs_seg e2 _).mp
      (hfits (evs_seg ++ e2) (hseq evs_seg e2 hseg he2))).2
  · rw [List.append_assoc]
    exact hfull (evs_seg ++ e2) (hseq evs_seg e2 hseg he2)

/-- Close `SeamBudget` at region exit with a final `evs_exit` in `remEnv`. -/
theorem SeamBudget.finish {M : AllocCostModel} {lim : BudgetLimits}
    {fullEnv remEnv : List AllocEvent → Prop} {st_init st : M.σ}
    {evs_exit : List AllocEvent}
    (hs : SeamBudget M lim fullEnv st_init st remEnv)
    (hexit : remEnv evs_exit) :
    ∃ evs_total : List AllocEvent,
      M.stepEvents evs_exit st = M.stepEvents evs_total st_init ∧
      fullEnv evs_total := by
  rcases hs with ⟨_, evs_pre, rfl, hfull⟩
  exact ⟨evs_pre ++ evs_exit,
    (M.stepEvents_append evs_pre evs_exit st_init).symm,
    hfull evs_exit hexit⟩

/-! ## Stack-independent `TryDecrypt` and per-seam event envelopes -/

/-- Stack-pointer-independent projection of `TryDecryptGhost` carrying all logical and ghost-layout
    inputs on which `try_decrypt_with_state`'s allocation envelope may depend. -/
structure TryDecryptEnvArgs where
  G : SessionGhost
  st : SessionState (List (BitVec 8))
  rem : AddrGhost
  loc : AddrGhost
  msgG : SignalMessageGhost
  msg : SignalMessage
  msgType : MessageType
  rest : List (BitVec 8)

/-- Project `TryDecryptGhost` to its stack-pointer-independent `TryDecryptEnvArgs`. -/
def tryDecryptEnvArgs (x : TryDecryptGhost) : TryDecryptEnvArgs where
  G := x.G
  st := x.st
  rem := x.rem
  loc := x.loc
  msgG := x.msgG
  msg := x.msg
  msgType := x.msgType
  rest := x.rest

/-- `TryDecryptEnvArgs` at the `try_decrypt_from_record` call site for clone `G₁`
    (`tryDecryptEnvArgs (mkTryDecryptGhost sp x G₁) = recordTryDecryptEnvArgs x G₁` by `rfl`). -/
def recordTryDecryptEnvArgs (x : RecordDecryptGhost) (G₁ : SessionGhost) : TryDecryptEnvArgs where
  G := G₁
  st := x.st
  rem := x.rem
  loc := x.loc
  msgG := x.msgG
  msg := x.msg
  msgType := .whisper
  rest := x.rest

/-- Event envelope for `Vec<u8>::clone` on a ghost `VecGhost`. -/
def vecCloneEvents (v : VecGhost) : List AllocEvent :=
  if v.bytes.length = 0 then [] else rustAllocEvents v.bytes.length 1

/-- Event envelope for `Option<{ Vec<u8>, tail }>::clone` (`PendingPreKey` / `PendingKyberPreKey`). -/
def optTailCloneEvents : Option TailVecGhost → List AllocEvent
  | none => []
  | some g => vecCloneEvents g.vec

/-- Event envelope for `SegTail` (`F → J`): drop local `SessionStructure` (`FreeOnlyEvs`) followed
    by allocating the 17-byte `"decryption failed"` message (`rustAllocEvents 17 1`). -/
def SegTailEnv : List AllocEvent → Prop :=
  SeqEnv FreeOnlyEvs (fun evs => evs = rustAllocEvents 17 1)

/-- Remaining-events envelope from seam `F` to region exit (`F → J → exit`). -/
def FromFEnv : List AllocEvent → Prop :=
  SeqEnv SegTailEnv FreeOnlyEvs

/-- Remaining-events envelope from seam `M` to region exit (`M → F → J → exit`). -/
def FromMEnv : List AllocEvent → Prop :=
  SeqEnv (GrowOneSpeEnv 0#64) FromFEnv

/-- Remaining-events envelope after `try_decrypt_with_state` inside `SegDecrypt`:
    either `Ok` / `duplicatedMessage` (`→ J → exit`, only `.free` events) or non-duplicate error
    (`grow_one` at `cap = 0` → `F → J → exit`, i.e., `FromMEnv`). -/
def FromVPostTdEnv (evs : List AllocEvent) : Prop :=
  FreeOnlyEvs evs ∨ FromMEnv evs

/-- Remaining-events envelope from seam `V` to region exit (`V → J/F → exit`) for clone `G₁`. -/
def FromVEnv (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (G₁ : SessionGhost) : List AllocEvent → Prop :=
  SeqEnv (tdEnv (recordTryDecryptEnvArgs x G₁)) FromVPostTdEnv

/-- Exact allocator event sequence emitted by `SessionStructure::clone` in `SegClone`
    (`+0x1fc..+0x638`), in binary execution order (`localIk`, `remoteIk`, `rootKey`,
    `senderChain`, `receiverChains`, `pendingPreKey`, `pendingKyber`, `aliceBaseKey`,
    `pqRatchetState`). -/
def segCloneEvents (G : SessionGhost) (st : SessionState (List (BitVec 8))) : List AllocEvent :=
  vecCloneEvents G.localIk ++
  vecCloneEvents G.remoteIk ++
  rustAllocEvents 32 1 ++
  (match G.sender, st.senderChain with
   | some gs, some sc => senderChainCloneEvents gs sc
   | _, _ => []) ++
  (if st.receiverChains = [] then []
   else rustAllocEvents (104 * st.receiverChains.length) 8 ++
     (G.chains.zip st.receiverChains).flatMap chainCloneEvents) ++
  optTailCloneEvents G.pending ++
  optTailCloneEvents G.kyber ++
  vecCloneEvents G.alice ++
  (if st.pqRatchetState.length = 0 then [] else rustAllocEvents st.pqRatchetState.length 1)

/-- Event envelope for `SegClone` (`entry → V / M`). -/
def SegCloneEnv (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (evs : List AllocEvent) : Prop :=
  evs = segCloneEvents G st

/-- Full allocator event envelope of the `try_decrypt_from_record` region (`+0x1a8 → +0x1f50`),
    parameterized by the `try_decrypt_with_state` callee envelope `tdEnv`. -/
def RecordDecryptEnv (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (evs : List AllocEvent) : Prop :=
  if x.st.version.toNat = x.msg.messageVersion.toNat then
    ∃ G₁ : SessionGhost, CloneRel x.G G₁ ∧
      SeqEnv (SegCloneEnv x.G x.st) (FromVEnv tdEnv x G₁) evs
  else
    SeqEnv (SegCloneEnv x.G x.st) FromMEnv evs

/-! ## Budget-threaded callee, region, and seam specifications -/

/-- Budget-threaded `[LibsignalPlacement]` `try_decrypt_with_state` callee contract, reusing
    `Record.tryDecryptPlacedSpec` via `A.atState` and dropping `allocFailedIn` from `onPanic`. -/
def tryDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (TryDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (tdEnv (tryDecryptEnvArgs x))⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜tdEnv (tryDecryptEnvArgs x) evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Record.tryDecryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Budget-threaded `[LibsignalPlacement]` `try_decrypt_from_record` region contract, reusing
    `Record.recordDecryptPlacedSpec` via `A.atState` and dropping `allocFailedIn` from `onPanic`. -/
def recordDecryptPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    Spec (RecordDecryptGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜FitsEnv M lim st (RecordDecryptEnv tdEnv x)⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C (A.atState lim st s) ctl uuidParse S).pre x s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent, ⌜RecordDecryptEnv tdEnv x evs⌝ ∗
      (CryptoVerification.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec
        C (A.atState lim (M.stepEvents evs st) sf) ctl uuidParse S).post x s0 sf
  onPanic := fun (x, _) s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨
        (x.st.version.toNat = x.msg.messageVersion.toNat ∧
          S.recvPanics x.st.pqRatchetState x.msg.pqRatchet)) ∧
      s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Seam `V` (`+0x69c`) with budget state `st` and `SeamBudget` for `FromVEnv tdEnv x G₁`. -/
def VStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st (FromVEnv tdEnv x G₁) ∧
  CryptoVerification.LibsignalTripleRatchet.Record.VStatePlaced
    (A.atState lim st s) ctl x G₁ R s0 s

/-- Seam `M` (`+0x7e4`) with budget state `st` and `SeamBudget` for `FromMEnv`. -/
def MStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FromMEnv ∧
  CryptoVerification.LibsignalTripleRatchet.Record.MStatePlaced
    (A.atState lim st s) ctl x G₁ R s0 s

/-- Seam `F` (`+0x850`) with budget state `st` and `SeamBudget` for `FromFEnv`. -/
def FStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FromFEnv ∧
  CryptoVerification.LibsignalTripleRatchet.Record.FStatePlaced
    C (A.atState lim st s) ctl parse S x R s0 s

/-- Seam `J` (`+0x1e8c`) with budget state `st` and `SeamBudget` for `FreeOnlyEvs`. -/
def JStatePlaced [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : RecordDecryptGhost) (st_init st : M.σ)
    (R : SepProp) (s0 s : State) : Prop :=
  SeamBudget M lim (RecordDecryptEnv tdEnv x) st_init st FreeOnlyEvs ∧
  CryptoVerification.LibsignalTripleRatchet.Record.JStatePlaced
    C (A.atState lim st s) ctl parse S x R s0 s

/-! ## Budget-threaded segment specifications and composition -/

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
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
    (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
    (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init : M.σ) (R : SepProp) (s0 : State),
      s0.pc = recEntryPlaced → s0.status = .Running →
      (s0.mem ⊨ (recordDecryptPlacedSpec C A lim ctl parse S tdEnv).pre (x, st_init) s0 ∗ R) →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s0.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s0 s' ∧
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
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
    (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
    (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
    (withLsCodeLoaded lsmpl
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      VStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s → rootStack ≤ s0.sp.toNat →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
        ((∃ st', JStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         (∃ st', FStatePlaced C A lim ctl parse S tdEnv x st_init st' R s0 s') ∨
         regionOutcome (recordDecryptPlacedSpec C A lim ctl parse S tdEnv)
           recExitPlaced (x, st_init) R s0 s')

def SegMismatchPlacedSpec [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
    (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)) →
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
    (withLsCodeLoaded lsmpl
      (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (G₁ : SessionGhost) (R : SepProp) (s0 s : State),
      MStatePlaced A lim ctl tdEnv x st_init st G₁ R s0 s →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
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
  subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
    (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)) →
    ∀ (x : RecordDecryptGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State),
      FStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
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
      ((blkPC_197).rebase (blkPl_197).base H).CodeLoaded s.mem →
      ∃ s', Steps ((blkPC_197).rebase (blkPl_197).base H) s s' ∧
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
  exact CryptoVerification.LibsignalTripleRatchet.Record.rootStack_le_of_recordPlacedPre hpre.2

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
    (hcc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (chainCloneSpec M A lim)))
    (hsc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 161)
      (withLsCodeLoaded lsmpl (senderChainCloneSpec M A lim)))
    (hdrop1 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 6)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec M A lim)))
    (htd : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 131)
      (withLsCodeLoaded lsmpl (tryDecryptPlacedSpec C A lim ctl parse S tdEnv)))
    (hset : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 48)
      (withLsCodeLoaded lsmpl (setSessionStateSpec M A lim)))
    (hdrop2 : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 139)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (hgrow : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 42)
      (withLsCodeLoaded lsmpl (growOneSpeSpec M A lim)))
    (hclosure : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsmpl.base 159)
      (withLsCodeLoaded lsmpl
        (withVmPreserved CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.logClosurePlacedSpec)))
    (hclone : SegClonePlacedSpec C A lim ctl parse S tdEnv H)
    (hdec : SegDecryptPlacedSpec C A lim ctl parse S tdEnv H)
    (hmis : SegMismatchPlacedSpec C A lim ctl parse S tdEnv H)
    (htail : SegTailPlacedSpec C A lim ctl parse S tdEnv H)
    (hexit : SegExitPlacedSpec C A lim ctl parse S tdEnv H) :
    region_ok ((blkPC_197).rebase (blkPl_197).base H) recEntryPlaced recExitPlaced
      (recordDecryptPlacedSpec C A lim ctl parse S tdEnv) := by
  apply region_ok_of_reaches
  rintro ⟨x, st_init⟩ R s0 hpc hst hpre hL
  have hstk := rootStack_le_of_recordPlacedPre hpre
  have hJ : ∀ st s, JStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
        (recordDecryptPlacedSpec C A lim ctl parse S tdEnv) recExitPlaced (x, st_init) R s0 s :=
    fun st s hs hLs => hexit hdealloc x st_init st R s0 s hs hLs
  have hF : ∀ st s, FStatePlaced C A lim ctl parse S tdEnv x st_init st R s0 s →
      region_reaches ((blkPC_197).rebase (blkPl_197).base H)
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

end LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
