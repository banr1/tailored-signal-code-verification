/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.FsTrace
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.MallocngBridgeBudget
public import LibsignalBinary.Heap.RustStdAllocBudgetBridge
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalPublicApi
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Hooks
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr

/-!
# Budget-Threaded Hook and Callee Specifications

Budget-threaded (`RustCliAllocBudget M`) counterparts of the `RustAlloc`-parameterized external
hook and subroutine contracts in `LibsignalBinary.Specifications`: Prost `DecodeError`,
AES-256-CBC, `core::fmt`, public-API session/identity store and time hooks, SPQR V1 ML-KEM-768 and
`libcrux_hmac`, and `signal_session_io` CLI I/O hooks (`CliExternsBudgetOk`).

Unlike `CliExternsOk`, `CliExternsBudgetOk` omits `poolEmp : emp ⊢ A.pool`: under `mallocng`,
`A.pool lim st s` owns initialized allocator globals, `StdErrnoCell`, and `StaticMappedCover`
established at startup, so `emp ⊢ A.pool lim st s` does not hold. Instead, `CliExternsBudgetOk`
threads `A.pool lim st s` explicitly and records `vmKept` (`VmPreserved` on non-allocating hooks)
so the pool transports via `hookSat_withVmPreserved`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Heap.SpecBudget

open Arm64 Arm64.Process ProofLib
open CryptoGames CryptoGames.CBC CryptoGames.HKDF CryptoGames.HMAC
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.E2E (PEParams)
open CryptoVerification.SignalSession
open LibsignalBinary.Heap
  (VmPreserved AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
   FitsEnv rustAllocEvents rustDeallocEvents rustReallocEvents
   rustCliAllocBudgetSpec rustCliDeallocBudgetSpec rustCliReallocBudgetSpec
   RustCliAllocBudgetHooks coarseCostModel coarseCostModelIface
   MallocngCostModelIface MallocngCostModelSound mallocngRustCliAllocBudget)
open LibsignalBinary.Heap.RustStdAllocBudgetBridge
  (StringCloneEnv stringCloneBudgetSpec)
open CryptoVerification (LibsignalPlacement)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

/-! ## `withVmPreserved` Combinator -/

/-- Strengthen `spec`'s normal-return postcondition with `⌜VmPreserved s0 sf⌝` while preserving
    `pre`, `onPanic`, `onExit`, and `onOom` verbatim. -/
def withVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Any hook in `hooks` satisfying `spec` and preserving `VmPreserved` also satisfies
    `withVmPreserved spec`. -/
theorem hookSat_withVmPreserved {α : Type} {hooks : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (h : HookSat hooks name spec)
    (hvm : ∀ f : State → State, hooks name = some f → ∀ s, VmPreserved s (f s)) :
    HookSat hooks name (withVmPreserved spec) := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm f hf s0, hpost⟩
  · right; exact hrest

theorem hookSat_of_withVmPreserved {α : Type} {hooks : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (h : HookSat hooks name (withVmPreserved spec)) :
    HookSat hooks name spec := by
  rcases h with ⟨f, hf, hsat⟩
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hsat x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · right; exact hrest

theorem subroutine_ok_of_withVmPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α}
    (h : subroutine_ok prog entry (withVmPreserved spec)) :
    subroutine_ok prog entry spec := by
  refine subroutine_ok_mono h (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
  dsimp only [withVmPreserved] at hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  exact hq.2

/-! ## Allocator Hook Bundle at Fixed `lim` -/

/-- Hook-mode bundle for conditional-OOM budget-threaded allocator contracts at a fixed `lim`,
    mirroring `AllocHooks A hooks` (`ProofLib/Abi/Rust/Heap/Alloc.lean`). -/
structure AllocHooksBudget [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hooks : String → Option (State → State)) : Prop where
  alloc : HookSat hooks "__rustc::__rust_alloc" (rustCliAllocBudgetSpec M A lim false)
  dealloc : HookSat hooks "__rustc::__rust_dealloc" (rustCliDeallocBudgetSpec M A lim)
  realloc : HookSat hooks "__rustc::__rust_realloc" (rustCliReallocBudgetSpec M A lim)

theorem RustCliAllocBudgetHooks.atLim [LibsignalPlacement] {M : AllocCostModel} {A : RustCliAllocBudget M}
    {hooks : String → Option (State → State)}
    (h : RustCliAllocBudgetHooks M A hooks) (lim : BudgetLimits) :
    AllocHooksBudget M A lim hooks :=
  ⟨h.alloc lim, h.dealloc lim, h.realloc lim⟩

/-- Budget-threaded counterpart of `rustAllocZeroedSpec` (`rustCliAllocBudgetSpec M A lim true`). -/
abbrev rustAllocZeroedBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (Nat × Nat × M.σ) :=
  rustCliAllocBudgetSpec M A lim true

/-! ## Prost `DecodeError` Budget Specs -/

/-- Allocator event envelope of `<DecodeError as From<DecodeErrorKind>>::from` (`Box::new` of 72-byte, 8-aligned `Inner`). -/
def DecodeErrorFromEnv (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents 72 8

/-- Budget-threaded counterpart of `decodeErrorFromSpec`. -/
def decodeErrorFromBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (k, w, st) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w ∧ FitsEnv M lim st DecodeErrorFromEnv⌝ ∗
      (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (k, _, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorFromEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeErrorHookStack

/-- Allocator event envelope of `<DecodeError>::push` on a stack of length `n`. -/
def DecodeErrorPushEnv (n : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (n = 0 ∧ ∃ c : Nat, 0 < c ∧ c * 32 < 2 ^ 63 ∧ evs = rustAllocEvents (c * 32) 8) ∨
  (∃ c c' : Nat, 0 < c ∧ c ≤ n ∧ n < c' ∧ c' * 32 < 2 ^ 63 ∧
    evs = rustReallocEvents (c * 32) (c' * 32) 8)

/-- Budget-threaded counterpart of `decodeErrorPushSpec`. -/
def decodeErrorPushBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp decodeErrorHookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp decodeErrorHookStack

def decodeErrorFromBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × M.σ) where
  pre := fun (k, w, st) s =>
    ⌜s.readReg64 .x0 = k ∧ KindNoHeap w ∧ FitsEnv M lim st DecodeErrorFromEnv⌝ ∗
      (k ↦₆₄ w) ∗ memRegion (k + 8#64) 40 ∗
      A.pool lim st s ∗ stackAt s.sp hookStack
  post := fun (k, _, st) s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗
      decodeErrorAtStackLen A.repAlloc (sf.readReg64 .x0) 0 ∗
      memRegion k 48 ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorFromEnv evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp hookStack

def decodeErrorPushBudgetSpecWithStack (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (hookStack : Nat := extHookStack) :
    Spec (BitVec 64 × BitVec 64 × Nat × M.σ) where
  pre := fun (d, e, n, st) s =>
    ⌜s.readReg64 .x0 = d ∧ n < 2 ^ 32 ∧ FitsEnv M lim st (DecodeErrorPushEnv n)⌝ ∗
      (d ↦₆₄ e) ∗ decodeErrorAtStackLen A.repAlloc e n ∗
      A.pool lim st s ∗ stackAt s.sp hookStack
  post := fun (d, e, n, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (d ↦₆₄ e) ∗
      decodeErrorAtStackLen A.repAlloc e (n + 1) ∗
      (∃∗ evs : List AllocEvent, ⌜DecodeErrorPushEnv n evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp hookStack

/-! ## AES-256-CBC Budget Envelopes and Contracts -/

/-- Allocator event envelope of `signal_crypto::aes_cbc::aes_256_cbc_encrypt`: one alignment-1 allocation of PKCS#7-padded length `(x.input.length / 16 + 1) * 16`. -/
def AesEncEnv (x : AesCall) (evs : List AllocEvent) : Prop :=
  evs = rustAllocEvents ((x.input.length / 16 + 1) * 16) 1

/-- Allocator event envelope of `signal_crypto::aes_cbc::aes_256_cbc_decrypt`: `[]` when `ctLen = 0 ∨ ctLen % 16 ≠ 0`, else `alloc(ctLen, 1)` (`Ok`) or `alloc(ctLen, 1) ++ dealloc(ctLen, 1)` (`Err`). -/
def AesDecEnv (x : AesCall) (evs : List AllocEvent) : Prop :=
  if x.input.length = 0 ∨ x.input.length % 16 ≠ 0 then
    evs = []
  else
    evs = rustAllocEvents x.input.length 1 ∨
    evs = rustAllocEvents x.input.length 1 ++ rustDeallocEvents x.input.length 1

/-- Common budget-threaded precondition of the two AES-256-CBC hooks, mirroring `AesCall.pre`
    (`Specifications/LibsignalTripleRatchet.lean:361`). -/
def aesCallPreBudget (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : AesCall → List AllocEvent → Prop) (x : AesCall) (st : M.σ) (s : State) : SepProp :=
  ⌜s.readReg64 .x0 = x.inA ∧ (s.readReg64 .x1).toNat = x.input.length ∧ s.readReg64 .x2 = x.keyA ∧
    s.readReg64 .x3 = 32#64 ∧ s.readReg64 .x4 = x.ivA ∧ s.readReg64 .x5 = 16#64 ∧
    s.readReg64 .x8 = x.ret ∧ x.key.length = 32 ∧ x.iv.length = 16 ∧ x.input.length < 2 ^ 40 ∧
    FitsEnv M lim st (Env x)⌝ ∗
    (x.inA ↦ₛ x.input) ∗ (x.keyA ↦ₛ x.key) ∗ (x.ivA ↦ₛ x.iv) ∗ memRegion x.ret 24 ∗
    A.pool lim st s ∗ stackAt s.sp extHookStack

/-- Function-parameterized AES-256-CBC encrypt budget contract, mirroring `aesEncFnSpec`
    (`Proofs/TripleRatchet/Hooks2.lean:1576`). -/
def aesEncFnBudgetSpec
    (encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8))
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s => aesCallPreBudget M A lim AesEncEnv x st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AesEncEnv x evs⌝ ∗ x.frame ∗
      vecU8 A.repAlloc x.ret (encFn x.input x.key x.iv) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Budget-threaded counterpart of `aesEncSpec`
    (`Specifications/LibsignalTripleRatchet.lean:375`), definitionally equal (`rfl`) to
    `aesEncFnBudgetSpec (fun pt k iv => aesCbcEncrypt E (bytesToKey32 k) (bytesToBlock iv) pt)`. -/
def aesEncBudgetSpec (E : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s => aesCallPreBudget M A lim AesEncEnv x st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AesEncEnv x evs⌝ ∗ x.frame ∗
      vecU8 A.repAlloc x.ret (aesCbcEncrypt E (bytesToKey32 x.key) (bytesToBlock x.iv) x.input) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

theorem aesEncFnBudgetSpec_block_eq (E : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    aesEncFnBudgetSpec (fun pt k iv => aesCbcEncrypt E (bytesToKey32 k) (bytesToBlock iv) pt)
        M A lim =
      aesEncBudgetSpec E M A lim :=
  rfl

/-- Budget-threaded counterpart of `aesDecSpec`
    (`Specifications/LibsignalTripleRatchet.lean:388`). -/
def aesDecBudgetSpec (D : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s => aesCallPreBudget M A lim AesDecEnv x st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AesDecEnv x evs⌝ ∗ x.frame ∗
      (match aesCbcDecrypt D (bytesToKey32 x.key) (bytesToBlock x.iv) x.input with
       | some pt => vecU8 A.repAlloc x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗
           (∃∗ p : BitVec 64, ⌜p ≠ 0⌝ ∗ ((x.ret + 8#64) ↦₆₄ p)) ∗ memRegion (x.ret + 16#64) 8) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Function-parameterized AES-256-CBC decrypt budget contract (`.none` layout with unconstrained
    `memRegion (x.ret + 8#64) 16`), mirroring `aesDecFnSpec` (`Proofs/TripleRatchet/Hooks2.lean:1619`). -/
def aesDecFnBudgetSpec
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) where
  pre := fun (x, st) s => aesCallPreBudget M A lim AesDecEnv x st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ AesDecEnv x evs⌝ ∗ x.frame ∗
      (match decFn x.input x.key x.iv with
       | some pt => vecU8 A.repAlloc x.ret pt
       | none => (x.ret ↦₆₄ errTag) ∗ memRegion (x.ret + 8#64) 16) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Block-cipher specialization of `aesDecFnBudgetSpec`, mirroring `aesDecWeakSpec`
    (`Proofs/TripleRatchet/Hooks2.lean:1632`). -/
abbrev aesDecWeakBudgetSpec (D : AesKey → Block → Block)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (AesCall × M.σ) :=
  aesDecFnBudgetSpec
    (fun ct k iv => aesCbcDecrypt D (bytesToKey32 k) (bytesToBlock iv) ct) M A lim

/-! ## Formatting Hooks and `TripleRatchetHooksBudget` -/

/-- Default allocator event envelope of `alloc::fmt::format::format_inner` (`formatInnerHook0`
    writes an empty `String` `{0, 1, 0}` with `0` allocations, `HooksCommon.lean:198`). -/
def FormatInnerEnv (evs : List AllocEvent) : Prop :=
  evs = []

/-- Envelope-parametric budget contract for `alloc::fmt::format::format_inner`, defaulting to
    `FormatInnerEnv`, mirroring `formatInnerSpec` (`Specifications/LibsignalTripleRatchet.lean:490`). -/
def formatInnerBudgetEnvSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : List AllocEvent → Prop := FormatInnerEnv) :
    Spec (BitVec 64 × M.σ) where
  pre := fun (ret, st) s =>
    ⌜s.readReg64 .x8 = ret ∧ FitsEnv M lim st Env⌝ ∗
      memRegion ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (ret, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜sf.trace = s0.trace ∧ Env evs⌝ ∗
      (∃∗ bs : List (BitVec 8), vecU8 A.repAlloc ret bs) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Budget-threaded counterpart of `formatInnerSpec` (`Specifications/LibsignalTripleRatchet.lean:490`). -/
abbrev formatInnerBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × M.σ) :=
  formatInnerBudgetEnvSpec M A lim FormatInnerEnv

/-- Default allocator event envelope of `core::fmt::write` (`fmtWriteHook0` returns `Ok` with `0`
    allocations, `HooksCommon.lean:202`). -/
def FmtWriteEnv (evs : List AllocEvent) : Prop :=
  evs = []

/-- Envelope-parametric budget contract for `core::fmt::write`, defaulting to `FmtWriteEnv`,
    mirroring `fmtWriteSpec` (`Specifications/LibsignalTripleRatchet.lean:508`). -/
def fmtWriteBudgetEnvSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (Env : List AllocEvent → Prop := FmtWriteEnv) :
    Spec (BitVec 64 × List (BitVec 8) × M.σ) where
  pre := fun (v, bs, st) s =>
    ⌜s.readReg64 .x0 = v ∧ FitsEnv M lim st Env⌝ ∗
      vecU8 A.repAlloc v bs ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (v, _, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace ∧ Env evs⌝ ∗
      (∃∗ bs' : List (BitVec 8), vecU8 A.repAlloc v bs') ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack

/-- Budget-threaded counterpart of `fmtWriteSpec` (`Specifications/LibsignalTripleRatchet.lean:508`). -/
abbrev fmtWriteBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (BitVec 64 × List (BitVec 8) × M.σ) :=
  fmtWriteBudgetEnvSpec M A lim FmtWriteEnv

/-- Budget-threaded counterpart of `TripleRatchetHooks`
    (`Specifications/LibsignalTripleRatchet.lean:535`). -/
structure TripleRatchetHooksBudget [LibsignalPlacement] (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop where
  alloc : AllocHooksBudget M A lim abs
  allocZeroed : HookSat abs allocZeroedName (rustAllocZeroedBudgetSpec M A lim)
  aesEnc : HookSat abs aesEncName (aesEncBudgetSpec C.E M A lim)
  aesDec : HookSat abs aesDecName (aesDecBudgetSpec C.D M A lim)
  formatInner : HookSat abs formatInnerName (formatInnerBudgetSpec M A lim)
  fmtWrite : HookSat abs fmtWriteName (fmtWriteBudgetSpec M A lim)

/-! ## Public-API Store, Time, and `PublicApiHooksBudget` Contracts -/

/-- Default zero-allocation store-hook envelopes (parametric overrides supplied via
    `PublicApiStoreEnv`). -/
def LoadSessionEnv (_ : LoadCall) (evs : List AllocEvent) : Prop := evs = []
def StoreSessionEnv (_ : StoreSessionCall) (evs : List AllocEvent) : Prop := evs = []
def IsTrustedEnv (_ : IdentityCall) (_ : Direction) (evs : List AllocEvent) : Prop := evs = []
def SaveIdentityEnv (_ : IdentityCall) (evs : List AllocEvent) : Prop := evs = []

/-- Store-hook allocation envelope bundle for `PublicApiHooksBudget`. -/
structure PublicApiStoreEnv where
  loadEnv : LoadCall → List AllocEvent → Prop := LoadSessionEnv
  storeEnv : StoreSessionCall → List AllocEvent → Prop := StoreSessionEnv
  trustEnv : IdentityCall → Direction → List AllocEvent → Prop := IsTrustedEnv
  saveEnv : IdentityCall → List AllocEvent → Prop := SaveIdentityEnv

def defaultPublicApiStoreEnv : PublicApiStoreEnv := {}

/-- Budget-threaded counterpart of `loadSessionSpec`
    (`Specifications/LibsignalPublicApi.lean:189`). -/
def loadSessionBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (Env : LoadCall → List AllocEvent → Prop := LoadSessionEnv) :
    Spec (LoadCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.out ∧
      FitsEnv M lim st (Env x)⌝ ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      memRegion x.out 368 ∗ A.pool lim st s ∗ stackAt s.sp storeHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x evs⌝ ∗
      (∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
        ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (loadClass ans) ∧
          sf.trace = s0.trace ++ [loadEvent encRecord x.addr.val ans]⌝ ∗
        (match ans with
         | .ok (some r) => ⌜RecordInScope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A.repAlloc x.out g r
         | _ => memRegion x.out 368)) ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp storeHookStack

/-- Budget-threaded counterpart of `storeSessionSpec`
    (`Specifications/LibsignalPublicApi.lean:214`). -/
def storeSessionBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (Env : StoreSessionCall → List AllocEvent → Prop := StoreSessionEnv) :
    Spec (StoreSessionCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.recA ∧
      FitsEnv M lim st (Env x)⌝ ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      sessionRecordAt A.repAlloc x.recA x.g x.record ∗
      A.pool lim st s ∗ stackAt s.sp storeHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x evs⌝ ∗
      (∃∗ ans : Except Unit Unit,
        ⌜StoreStatusIs ((sf.readReg64 .x0).setWidth 32) ans ∧
          sf.trace = s0.trace ++ [storeSessionEvent encRecord x.addr.val x.record ans]⌝ ∗
        protocolAddressAt A.repAlloc x.addr x.addrA ∗
        sessionRecordAt A.repAlloc x.recA x.g x.record) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp storeHookStack

/-- Budget-threaded counterpart of `isTrustedSpec`
    (`Specifications/LibsignalPublicApi.lean:238`). -/
def isTrustedBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : IdentityCall → Direction → List AllocEvent → Prop := IsTrustedEnv) :
    Spec (IdentityCall × Direction × M.σ) where
  pre := fun (x, d, st) s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.keyA ∧
      (s.readReg64 .x2).setWidth 32 = (directionByte d).setWidth 32 ∧
      FitsEnv M lim st (Env x d)⌝ ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp storeHookStack
  post := fun (x, d, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x d evs⌝ ∗
      (∃∗ ans : Except Unit Bool,
        ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (exceptClass id ans) ∧
          sf.trace = s0.trace ++ [trustEvent x.addr.val x.key d ans]⌝ ∗
        protocolAddressAt A.repAlloc x.addr x.addrA ∗
        (x.keyA ↦ₛ x.key.publicKey.bytes.toList)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp storeHookStack

/-- Budget-threaded counterpart of `saveIdentitySpec`
    (`Specifications/LibsignalPublicApi.lean:253`). -/
def saveIdentityBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (Env : IdentityCall → List AllocEvent → Prop := SaveIdentityEnv) :
    Spec (IdentityCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.addrA ∧ s.readReg64 .x1 = x.keyA ∧
      FitsEnv M lim st (Env x)⌝ ∗
      protocolAddressAt A.repAlloc x.addr x.addrA ∗
      (x.keyA ↦ₛ x.key.publicKey.bytes.toList) ∗
      A.pool lim st s ∗ stackAt s.sp storeHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜Env x evs⌝ ∗
      (∃∗ ans : Except Unit IdentityChange,
        ⌜StatusIs ((sf.readReg64 .x0).setWidth 32) (exceptClass (· == .replacedExisting) ans) ∧
          sf.trace = s0.trace ++ [saveEvent x.addr.val x.key ans]⌝ ∗
        protocolAddressAt A.repAlloc x.addr x.addrA ∗
        (x.keyA ↦ₛ x.key.publicKey.bytes.toList)) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp storeHookStack

/-- Budget-threaded counterpart of `timeAddSpec`: strengthens `post` with `⌜VmPreserved s0 sf⌝` while keeping the `t.checkedAddSecs secs = none` overflow panic. -/
def timeAddBudgetSpec : Spec (SystemTime × Nat) :=
  withVmPreserved timeAddSpec

/-- Budget-threaded counterpart of `durationSinceSpec`, strengthening `post` with `⌜VmPreserved s0 sf⌝`. -/
def durationSinceBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved durationSinceSpec

/-- Store-free subset of `PublicApiHooksBudget`: `TripleRatchetHooksBudget` plus `timeAdd`,
    `durationSince`, and `stringClone` (sufficient for all inner session functions that do not
    invoke the 4 async store shims directly). -/
structure PublicApiHooksNoSessionStoreBudget [LibsignalPlacement] (C : Crypto) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State)) : Prop
    extends TripleRatchetHooksBudget C M A lim S abs where
  timeAdd : HookSat abs timeAddHookName timeAddBudgetSpec
  durationSince : HookSat abs durationSinceHookName durationSinceBudgetSpec
  stringClone : HookSat abs stringCloneHookName (stringCloneBudgetSpec M A lim)

/-- Budget-threaded counterpart of `PublicApiHooks` (`Specifications/LibsignalPublicApi.lean:335`),
    parameterized by `storeEnv : PublicApiStoreEnv := defaultPublicApiStoreEnv`. -/
structure PublicApiHooksBudget [LibsignalPlacement] (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (storeEnv : PublicApiStoreEnv := defaultPublicApiStoreEnv) : Prop
    extends PublicApiHooksNoSessionStoreBudget C M A lim S abs where
  loadSession : HookSat abs loadSessionHookName
    (loadSessionBudgetSpec M A lim encRecord storeEnv.loadEnv)
  storeSession : HookSat abs storeSessionHookName
    (storeSessionBudgetSpec M A lim encRecord storeEnv.storeEnv)
  isTrusted : HookSat abs isTrustedHookName
    (isTrustedBudgetSpec M A lim storeEnv.trustEnv)
  saveIdentity : HookSat abs saveIdentityHookName
    (saveIdentityBudgetSpec M A lim storeEnv.saveEnv)

/-! ## `libcrux_hmac` and `SpqrHooksBudget` -/

/-- Exact 7-call allocator sequence of `libcrux_hmac::hmac` (`Algorithm::Sha256`) on valid input
    lengths `< 2 ^ 32` (`HooksMallocng.lean:280–292`): three 64-byte SHA-256 state allocations,
    three 64-byte deallocations, and one 32-byte tag `Vec<u8>` allocation. -/
def libcruxHmacSha256Events : List AllocEvent :=
  rustAllocEvents 64 1 ++ rustAllocEvents 64 1 ++ rustAllocEvents 64 1 ++
  rustDeallocEvents 64 1 ++ rustDeallocEvents 64 1 ++ rustDeallocEvents 64 1 ++
  rustAllocEvents 32 1

/-- Exact allocator event envelope of `libcrux_hmac::hmac`: `libcruxHmacSha256Events` when
    `x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32`, and `[]` on the `u32::try_from` overflow
    panic path (`2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length`, `HooksMallocng.lean:274`). -/
def LibcruxHmacEnv (x : LibcruxHmacCall) (evs : List AllocEvent) : Prop :=
  if x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 then
    evs = libcruxHmacSha256Events
  else
    evs = []

/-- Budget-threaded counterpart of `libcruxHmacSpec`
    (`Specifications/LibsignalSpqrV1/Hooks.lean:385`): drops the `allocFailedIn s0 sf` disjunct from
    `onPanic` while keeping the real `2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length` panic. -/
def libcruxHmacBudgetSpec (F : ShaState → List (BitVec 8) → ShaState)
    (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec (LibcruxHmacCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ (s.readReg64 .x0).setWidth 32 = 0#32 ∧
      s.readReg64 .x1 = x.keyA ∧ (s.readReg64 .x2).toNat = x.key.length ∧
      s.readReg64 .x3 = x.dataA ∧ (s.readReg64 .x4).toNat = x.data.length ∧
      (s.readReg64 .x5).setWidth 32 = 1#32 ∧ s.readReg64 .x6 = 32#64 ∧
      FitsEnv M lim st (LibcruxHmacEnv x)⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      memRegion x.ret 24 ∗ A.pool lim st s ∗ stackAt s.sp extHookStack
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜x.key.length < 2 ^ 32 ∧ x.data.length < 2 ^ 32 ∧
        sf.trace = s0.trace ∧ LibcruxHmacEnv x evs⌝ ∗
      (x.keyA ↦ₛ x.key) ∗ (x.dataA ↦ₛ x.data) ∗
      vecU8 A.repAlloc x.ret (hmacWith F x.key x.data) ∗
      A.pool lim (M.stepEvents evs st) sf ∗ stackAt s0.sp extHookStack
  onPanic := fun (x, _) s0 sf =>
    ⌜(2 ^ 32 ≤ x.key.length ∨ 2 ^ 32 ≤ x.data.length) ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Budget-threaded counterpart of `SpqrHooks` (`Specifications/LibsignalSpqrV1/Hooks.lean`):
    the 7 pure ML-KEM-768 incremental hooks carry `withVmPreserved` so `A.pool lim st` transports
    directly across each call, and `hmac` uses `libcruxHmacBudgetSpec`. -/
structure SpqrHooksBudget (C : Crypto) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (K : MlKem) (abs : String → Option (State → State)) : Prop where
  fromSeed : HookSat abs mlkemFromSeedName (withVmPreserved (mlkemFromSeedSpec K))
  pk1 : HookSat abs mlkemPk1Name (withVmPreserved mlkemPk1Spec)
  pk2 : HookSat abs mlkemPk2Name (withVmPreserved mlkemPk2Spec)
  encaps1 : HookSat abs mlkemEncaps1Name (withVmPreserved (mlkemEncaps1Spec K))
  encaps2 : HookSat abs mlkemEncaps2Name (withVmPreserved (mlkemEncaps2Spec K))
  decaps : HookSat abs mlkemDecapsName (withVmPreserved (mlkemDecapsSpec K))
  validatePk : HookSat abs mlkemValidatePkName (withVmPreserved (mlkemValidatePkSpec K))
  hmac : HookSat abs libcruxHmacName (libcruxHmacBudgetSpec C.F M A lim)

theorem SpqrHooksBudget.fromSeed_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemFromSeedName (mlkemFromSeedSpec K) :=
  hookSat_of_withVmPreserved h.fromSeed

theorem SpqrHooksBudget.pk1_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemPk1Name mlkemPk1Spec :=
  hookSat_of_withVmPreserved h.pk1

theorem SpqrHooksBudget.pk2_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemPk2Name mlkemPk2Spec :=
  hookSat_of_withVmPreserved h.pk2

theorem SpqrHooksBudget.encaps1_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemEncaps1Name (mlkemEncaps1Spec K) :=
  hookSat_of_withVmPreserved h.encaps1

theorem SpqrHooksBudget.encaps2_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemEncaps2Name (mlkemEncaps2Spec K) :=
  hookSat_of_withVmPreserved h.encaps2

theorem SpqrHooksBudget.decaps_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemDecapsName (mlkemDecapsSpec K) :=
  hookSat_of_withVmPreserved h.decaps

theorem SpqrHooksBudget.validatePk_raw {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)} (h : SpqrHooksBudget C M A lim K abs) :
    HookSat abs mlkemValidatePkName (mlkemValidatePkSpec K) :=
  hookSat_of_withVmPreserved h.validatePk

theorem SpqrHooksBudget.fromSeed_pk1 {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)}
    (_ : SpqrHooksBudget C M A lim K abs) (seed : List.Vector (BitVec 8) 64) :
    ((K.fromSeed seed).2.2.toList.drop 2304).take 64 = (K.fromSeed seed).1.toList :=
  K.fromSeed_pk1 seed

theorem SpqrHooksBudget.fromSeed_pk2 {C : Crypto} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {K : MlKem}
    {abs : String → Option (State → State)}
    (_ : SpqrHooksBudget C M A lim K abs) (seed : List.Vector (BitVec 8) 64) :
    ((K.fromSeed seed).2.2.toList.drop 1152).take 1152 = (K.fromSeed seed).2.1.toList :=
  K.fromSeed_pk2 seed

/-! ## CLI I/O and `CliExternsBudgetOk` -/

/-- Allocator event list for returning a fresh `Vec<u8>` holding `bs` (`vecOk`, `CliRun.lean:230`):
    `[]` when `bs` is empty, else `rustAllocEvents bs.length 1`. -/
def allocBytes1Events (bs : List (BitVec 8)) : List AllocEvent :=
  if bs.length = 0 then [] else rustAllocEvents bs.length 1

/-- The `j`-th `Vec<u8>` buffer capacity (`4096 * 2^j`) in `signal_session_io`'s doubling schedule. -/
def cliIoCap (j : Nat) : Nat := 4096 * 2 ^ j

/-- Index `j ∈ [0, K]` of the final capacity `4096 * 2^j` reached on `r > 0` input bytes. -/
def cliIoCapIdx : Nat → Nat → Nat
  | 0, _ => 0
  | K + 1, r => if r ≤ cliIoCap K then cliIoCapIdx K r else K + 1

/-- Doubling `Vec<u8>` capacity schedule of `signal_session_io::{read_stdin, read_file}` (`K = 8` up to `1 MiB` for `read_stdin`, `K = 9` up to `2 MiB` for `read_file`). -/
def cliIoReadScheduleCaps (K r : Nat) : List Nat :=
  if r = 0 then []
  else (List.range (cliIoCapIdx K r + 1)).map cliIoCap

/-- Allocator event sequence for a capacity growth schedule starting from `prev` bytes (`align = 1`):
    initial `rustAllocEvents c 1` from `prev = 0`, followed by `rustReallocEvents prev c 1` steps. -/
def cliIoCapsEvents : Nat → List Nat → List AllocEvent
  | _, [] => []
  | 0, c :: cs => rustAllocEvents c 1 ++ cliIoCapsEvents c cs
  | prev + 1, c :: cs => rustReallocEvents (prev + 1) c 1 ++ cliIoCapsEvents c cs

/-- Allocator event envelope of `signal_session_io::read_file`: doubling `Vec<u8>` growth up to `2 MiB` (`K = 9`), plus `rustDeallocEvents 2097152 1` on over-capacity rejection. -/
def ReadFileEnv (files : String → Option FsEntry) (path : List (BitVec 8))
    (evs : List AllocEvent) : Prop :=
  match CliExt.readFileResult files path with
  | .ok bs =>
    evs = allocBytes1Events bs ∨
    ((4096 ≤ path.length ∨ 0#8 ∈ path) ∧ evs = []) ∨
    (bs.length ≤ 2097152 ∧ evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length)) ∨
    (2097152 < bs.length ∧
      evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 2097152) ++ rustDeallocEvents 2097152 1)
  | .error () => evs = []

/-- Hook-level `allocBytes1Events` witnesses satisfy `ReadFileEnv`. -/
theorem readFileEnv_of_hook (files : String → Option FsEntry) (path : List (BitVec 8))
    {evs : List AllocEvent}
    (h : match CliExt.readFileResult files path with
         | .ok bs => evs = allocBytes1Events bs
         | .error () => evs = []) :
    ReadFileEnv files path evs := by
  unfold ReadFileEnv
  cases hr : CliExt.readFileResult files path with
  | ok bs => simp only [hr] at h; exact Or.inl h
  | error u => cases u; simp only [hr] at h; exact h

/-- Doubling-schedule (`cliIoReadScheduleCaps 9`) witnesses satisfy `ReadFileEnv`, including over-capacity deallocation and early-reject `[]`. -/
theorem readFileEnv_cliIoCaps9 (files : String → Option FsEntry) (path : List (BitVec 8)) :
    (∀ bs, CliExt.readFileResult files path = .ok bs → bs.length ≤ 2097152 →
      ReadFileEnv files path (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length))) ∧
    (∀ bs, CliExt.readFileResult files path = .ok bs → 2097152 < bs.length →
      ReadFileEnv files path
        (cliIoCapsEvents 0 (cliIoReadScheduleCaps 9 bs.length) ++ rustDeallocEvents 2097152 1)) ∧
    ((4096 ≤ path.length ∨ 0#8 ∈ path) → ReadFileEnv files path []) ∧
    (CliExt.readFileResult files path = .error () → ReadFileEnv files path []) := by
  refine ⟨fun bs hr hle => ?_, fun bs hr hgt => ?_, fun hbad => ?_, fun herr => ?_⟩
  · unfold ReadFileEnv; rw [hr]; exact Or.inr (Or.inr (Or.inl ⟨hle, rfl⟩))
  · have h9 : cliIoCapIdx 9 bs.length = 9 := by
      unfold cliIoCapIdx
      simp only [show ¬ bs.length ≤ cliIoCap 8 by change ¬ bs.length ≤ 1048576; omega, ↓reduceIte]
    have hcap : cliIoReadScheduleCaps 9 bs.length = cliIoReadScheduleCaps 9 2097152 := by
      unfold cliIoReadScheduleCaps; simp only [show bs.length ≠ 0 by omega, h9, ↓reduceIte]; rfl
    unfold ReadFileEnv; rw [hr, hcap]; exact Or.inr (Or.inr (Or.inr ⟨hgt, rfl⟩))
  · unfold ReadFileEnv
    cases CliExt.readFileResult files path with
    | ok _ => exact Or.inr (Or.inl ⟨hbad, rfl⟩)
    | error u => cases u; rfl
  · unfold ReadFileEnv; rw [herr]

def readFileBudgetCoreSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (CliExt.ReadFileCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x8 = x.ret ∧ x.path.length < 2 ^ 32 ∧ CliExt.cliPathOk x.path ∧
      FitsEnv M lim st (ReadFileEnv s.fs.files x.path)⌝ ∗
      CliExt.bytesAt x.ro x.pathA x.path ∗ memRegion x.ret 24 ∗
      stackAt s.sp extHookStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadFileEnv s0.fs.files x.path evs⌝ ∗
      (∃∗ r : Except Unit (List (BitVec 8)),
        ⌜sf.fs.files = s0.fs.files ∧ r = CliExt.readFileResult s0.fs.files x.path ∧
          sf.trace = s0.trace⌝ ∗
          CliExt.ioVecAt A.repAlloc x.ret r) ∗
      CliExt.bytesAt x.ro x.pathA x.path ∗ stackAt s0.sp extHookStack ∗
      A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded counterpart of `CliExt.readFileSpec`
    (`Proofs/SpecLemmas/SignalSession/CliExternsFixed.lean:332`). -/
def readFileBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (img : Obj.Image) : Spec (CliExt.ReadFileCall × M.σ) :=
  Spec.inImage (readFileBudgetCoreSpec M A lim) img

/-- Allocator event envelope of `signal_session_io::read_stdin`: doubling `Vec<u8>` growth up to `1 MiB` (`K = 8`), plus `rustDeallocEvents 1048576 1` on over-capacity rejection. -/
def ReadStdinEnv (bs : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  evs = allocBytes1Events bs ∨
  (bs.length ≤ 1048576 ∧ evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) ∨
  (1048576 < bs.length ∧
    evs = cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 1048576) ++ rustDeallocEvents 1048576 1)

/-- Hook-level `allocBytes1Events` witnesses satisfy `ReadStdinEnv`. -/
theorem readStdinEnv_of_hook (bs : List (BitVec 8)) {evs : List AllocEvent}
    (h : evs = allocBytes1Events bs) : ReadStdinEnv bs evs :=
  Or.inl h

theorem readStdinEnv_cliIoCaps8_ok {bs : List (BitVec 8)} (hle : bs.length ≤ 1048576) :
    ReadStdinEnv bs (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length)) :=
  Or.inr (Or.inl ⟨hle, rfl⟩)

theorem readStdinEnv_cliIoCaps8_overCap {bs : List (BitVec 8)} (hgt : 1048576 < bs.length) :
    ReadStdinEnv bs
      (cliIoCapsEvents 0 (cliIoReadScheduleCaps 8 bs.length) ++ rustDeallocEvents 1048576 1) := by
  have h8 : cliIoCapIdx 8 bs.length = 8 := by
    unfold cliIoCapIdx
    simp only [show ¬ bs.length ≤ cliIoCap 7 by change ¬ bs.length ≤ 524288; omega, ↓reduceIte]
  have hcap : cliIoReadScheduleCaps 8 bs.length = cliIoReadScheduleCaps 8 1048576 := by
    unfold cliIoReadScheduleCaps; simp only [show bs.length ≠ 0 by omega, h8, ↓reduceIte]; rfl
  rw [hcap]; exact Or.inr (Or.inr ⟨hgt, rfl⟩)

def readStdinBudgetCoreSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (CliExt.ReadStdinCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.ret ∧ CliExt.stdinBytes s.fs = some x.bs ∧
      FitsEnv M lim st (ReadStdinEnv x.bs) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.ret 24 ∗ stackAt s.sp extHookStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜ReadStdinEnv x.bs evs⌝ ∗
      (∃∗ r : Except Unit (List (BitVec 8)),
        ⌜sf.fs.files = s0.fs.files ∧ r = CryptoVerification.SignalSession.readStdinResult x.bs ∧ sf.trace = s0.trace⌝ ∗
          CliExt.ioVecAt A.repAlloc x.ret r) ∗
      stackAt s0.sp extHookStack ∗ A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded counterpart of `CliExt.readStdinSpec`
    (`Proofs/SpecLemmas/SignalSession/CliExternsFixed.lean:353`). -/
def readStdinBudgetSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (img : Obj.Image) : Spec (CliExt.ReadStdinCall × M.σ) :=
  Spec.inImage (readStdinBudgetCoreSpec M A lim) img

/-- Allocator event envelope of `signal_session_io::write_file`: `[]` on stack-buffered/C-ABI writes, or `alloc(len + 1, 1) ++ dealloc(len + 1, 1)` when `384 ≤ len` (`CString` heap fallback). -/
def WriteFileEnv (len : Nat) (evs : List AllocEvent) : Prop :=
  evs = [] ∨
  (384 ≤ len ∧ evs = rustAllocEvents (len + 1) 1 ++ rustDeallocEvents (len + 1) 1)

theorem writeFileEnv_nil (len : Nat) : WriteFileEnv len [] :=
  Or.inl rfl

theorem writeFileEnv_allocDealloc {len : Nat} (hle : 384 ≤ len) :
    WriteFileEnv len (rustAllocEvents (len + 1) 1 ++ rustDeallocEvents (len + 1) 1) :=
  Or.inr ⟨hle, rfl⟩

def writeFileBudgetCoreSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (CliExt.WriteFileCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.pathA ∧ (s.readReg64 .x1).toNat = x.path.length ∧
      s.readReg64 .x2 = x.buf ∧ (s.readReg64 .x3).toNat = x.bs.length ∧
      x.path.length < 2 ^ 32 ∧ CliExt.cliPathOk x.path ∧
      FitsEnv M lim st (WriteFileEnv x.path.length)⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s.sp extHookStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteFileEnv x.path.length evs ∧
        (match CliExt.writeFileResult s0.fs.files x.path x.bs with
         | some F' => sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = F'
         | none => sf.readReg64 .x0 = 1#64 ∧ sf.fs.files = s0.fs.files) ∧
        s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace⌝ ∗
      (x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack ∗
      A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded counterpart of `CliExt.writeFileSpec`
    (`Proofs/SpecLemmas/SignalSession/CliExternsFixed.lean:376`). -/
def writeFileBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (img : Obj.Image) : Spec (CliExt.WriteFileCall × M.σ) :=
  Spec.inImage (writeFileBudgetCoreSpec M A lim) img

/-- Allocator event envelope of `signal_session_io::write_stdout`: `[]` or a one-time 1024-byte `LineWriter` buffer allocation. -/
def WriteStdoutEnv (evs : List AllocEvent) : Prop :=
  evs = [] ∨ evs = rustAllocEvents 1024 1

theorem writeStdoutEnv_nil : WriteStdoutEnv [] :=
  Or.inl rfl

theorem writeStdoutEnv_init1024 : WriteStdoutEnv (rustAllocEvents 1024 1) :=
  Or.inr rfl

def writeStdoutBudgetCoreSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (CliExt.WriteStdoutCall × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.buf ∧ (s.readReg64 .x1).toNat = x.bs.length ∧
      FitsEnv M lim st WriteStdoutEnv⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s.sp extHookStack ∗ A.pool lim st s
  post := fun (x, st) s0 sf =>
    ∃∗ evs : List AllocEvent,
      ⌜WriteStdoutEnv evs ∧
        sf.readReg64 .x0 = 0#64 ∧ sf.fs.files = s0.fs.files ∧ s0.trace <+: sf.trace ∧
        ProcessOutcome.traceStreamBytes .stdout sf.trace =
          ProcessOutcome.traceStreamBytes .stdout s0.trace ++ x.bs⌝ ∗
      (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack ∗ A.pool lim (M.stepEvents evs st) sf

/-- Budget-threaded counterpart of `CliExt.writeStdoutSpec`
    (`Proofs/SpecLemmas/SignalSession/CliExternsFixed.lean:399`). -/
def writeStdoutBudgetSpec (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (img : Obj.Image) : Spec (CliExt.WriteStdoutCall × M.σ) :=
  Spec.inImage (writeStdoutBudgetCoreSpec M A lim) img

private theorem vmPreserved_unmodelled (msg : String) (s : State) :
    VmPreserved s (unmodelled msg s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

private theorem vmPreserved_unitResult (ok : Bool) (s : State) :
    VmPreserved s (unitResult ok s) :=
  ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩

/-- `writeFileHook` preserves `VmPreserved` (for `CliExternsBudgetOk` hook-table instantiation). -/
theorem vmPreserved_writeFileHook (s : State) : VmPreserved s (writeFileHook s) := by
  unfold writeFileHook
  dsimp only []
  split_ifs
  · exact vmPreserved_unmodelled _ s
  · exact vmPreserved_unitResult false s
  · exact vmPreserved_unmodelled _ s
  · have htr : VmPreserved s
        (s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))]) :=
      ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
    generalize s.appendTrace [.fileChanged (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1))] =
      s1 at htr ⊢
    cases blockingAncestor? s1.fs (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
    | some _ => exact htr.trans (vmPreserved_unitResult false s1)
    | none =>
      cases s1.fs.files (readPath s.mem (s.readReg64 .x0) (s.readReg64 .x1)) with
      | none =>
        exact htr.trans (VmPreserved.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
          (vmPreserved_unitResult true _))
      | some entry =>
        cases entry with
        | file _ =>
          exact htr.trans (VmPreserved.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
            (vmPreserved_unitResult true _))
        | dir => exact htr.trans (vmPreserved_unitResult false s1)

/-- `writeStdoutHook` preserves `VmPreserved` (for `CliExternsBudgetOk` hook-table instantiation). -/
theorem vmPreserved_writeStdoutHook (s : State) : VmPreserved s (writeStdoutHook s) := by
  unfold writeStdoutHook
  dsimp only []
  split_ifs
  · exact vmPreserved_unmodelled _ s
  · exact VmPreserved.trans ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
      (vmPreserved_unitResult true _)

/-- Hook-table `HookSat` lift from `CliExt.writeFileSpec` to `writeFileBudgetSpec` via `evs := []` when `writeFileName` preserves `VmPreserved`. -/
theorem hookSat_writeFileBudget_of_hookSat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {img : Obj.Image} {ext : String → Option (State → State)}
    (hSat : HookSat ext writeFileName (CliExt.writeFileSpec img))
    (hVm : ∀ f, ext writeFileName = some f → ∀ s, VmPreserved s (f s)) :
    HookSat ext writeFileName (writeFileBudgetSpec M A lim img) := by
  rcases hSat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨x, st⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [writeFileBudgetSpec, Spec.inImage, writeFileBudgetCoreSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨ (CliExt.writeFileSpec img).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [CliExt.writeFileSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hx3, hlen, hpOk⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨c, hex, he⟩ | ⟨hoom_s, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CliExt.writeFileSpec, Spec.inImage] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeFileBudgetSpec, Spec.inImage, writeFileBudgetCoreSpec]
    have hpool : A.pool lim (M.stepEvents [] st) (f s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (f s0) (hVm f hf s0)
    have hrest' : (f s0).mem ⊨
        ((x.pathA ↦ₛ x.path) ∗ (x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeFileEnv_nil x.path.length, hres⟩ (Entails.refl _)
  · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CliExt.writeFileSpec, Spec.inImage] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Hook-table `HookSat` lift from `CliExt.writeStdoutSpec` to `writeStdoutBudgetSpec` via `evs := []` when `writeStdoutName` preserves `VmPreserved`. -/
theorem hookSat_writeStdoutBudget_of_hookSat {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) {img : Obj.Image} {ext : String → Option (State → State)}
    (hSat : HookSat ext writeStdoutName (CliExt.writeStdoutSpec img))
    (hVm : ∀ f, ext writeStdoutName = some f → ∀ s, VmPreserved s (f s)) :
    HookSat ext writeStdoutName (writeStdoutBudgetSpec M A lim img) := by
  rcases hSat with ⟨f, hf, hok⟩
  refine ⟨f, hf, fun ⟨x, st⟩ R s0 hrun hpre hsp => ?_⟩
  dsimp only [writeStdoutBudgetSpec, Spec.inImage, writeStdoutBudgetCoreSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨himg, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, _⟩, hmem⟩
  have hpre0 : s0.mem ⊨ (CliExt.writeStdoutSpec img).pre x s0 ∗ (A.pool lim st s0 ∗ R) := by
    dsimp only [CliExt.writeStdoutSpec, Spec.inImage]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himg, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hok x (A.pool lim st s0 ∗ R) s0 hrun hpre0 hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcs, hpost⟩ | ⟨hpan, hp⟩ | ⟨c, hex, he⟩ | ⟨hoom_s, hoom⟩
  · refine Or.inl ⟨hret, hcs, ?_⟩
    dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rcases hpost with ⟨hres, hrest⟩
    dsimp only [writeStdoutBudgetSpec, Spec.inImage, writeStdoutBudgetCoreSpec]
    have hpool : A.pool lim (M.stepEvents [] st) (f s0) = A.pool lim st s0 :=
      A.pool_transport lim st s0 (f s0) (hVm f hf s0)
    have hrest' : (f s0).mem ⊨
        ((x.buf ↦ₛ x.bs) ∗ stackAt s0.sp extHookStack ∗ A.pool lim st s0) ∗ R := by
      simpa only [sepConj_assoc] using hrest
    refine Satisfies.mono (sepConj_mono_left (Entails.sepExists_right ([] : List AllocEvent) ?_)) hrest'
    rw [hpool]
    exact Entails.pure_right ⟨writeStdoutEnv_nil, hres⟩ (Entails.refl _)
  · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hp
    rw [satisfies_pure_sepConj] at hp; exact False.elim hp.1
  · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at he
    rw [satisfies_pure_sepConj] at he; exact False.elim he.1
  · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Budget-threaded counterpart of `CliExt.durationSinceEpochSpec`
    (`Proofs/SpecLemmas/SignalSession/CliExternsFixed.lean:413`), strengthening `post` with
    `⌜VmPreserved s0 sf⌝`. -/
def durationSinceEpochBudgetSpec : Spec (BitVec 64 × BitVec 64) :=
  withVmPreserved CliExt.durationSinceEpochSpec

/-- Extern symbol names in `CliExternsBudgetOk` whose contracts thread allocator events explicitly; all other externs preserve `VmPreserved` (`CliExternsBudgetOk.liftVm`). -/
def cliAllocNames : List String :=
  ["__rustc::__rust_alloc", "__rustc::__rust_dealloc", "__rustc::__rust_realloc", allocZeroedName,
   readFileName, writeFileName, readStdinName, writeStdoutName,
   stringCloneHookName, fmtWriteName, formatInnerName,
   aesEncName, aesDecName, libcruxHmacName]

open CliExt in
/-- Budget-threaded counterpart of `CliExternsOk`, replacing `poolEmp` with `vmKept` on non-allocating externs. -/
structure CliExternsBudgetOk [LibsignalPlacement] (P : PEParams) (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop where
  tpidr : ∀ n f, ext n = some f → ∀ s, (f s).tpidrEl0 = s.tpidrEl0
  noExec : ∀ n f, ext n = some f → ∀ s a, ((f s).mem.perm a).x → (s.mem.perm a).x
  fsTraced : ∀ n f, ext n = some f → HookFsTraced (fun e => e.isFsChange = true) f
  fsKept : ∀ n f, ext n = some f → n ∉ ioNames → ∀ s, (f s).fs = s.fs
  vmKept : ∀ n f, ext n = some f → n ∉ cliAllocNames → ∀ s, VmPreserved s (f s)
  -- The allocator.
  shim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" shimSpec
  alloc : AllocHooksBudget M A lim ext
  allocZeroed : HookSat ext allocZeroedName (rustAllocZeroedBudgetSpec M A lim)
  -- libc.
  memset : HookSat ext "memset" memsetSpec
  memmove : HookSat ext "memmove" memmoveSpec
  memcpy : HookSat ext "memcpy" memcpySpec
  memcpyRO : HookSat ext "memcpy" memcpyROSpec
  bcmp : HookSat ext "bcmp" bcmpSpec
  strlen : HookSat ext "strlen" strlenSpec
  -- The I/O crate.
  readFile : ∀ img, HookSat ext readFileName (readFileBudgetSpec M A lim img)
  writeFile : ∀ img, HookSat ext writeFileName (writeFileBudgetSpec M A lim img)
  readStdin : ∀ img, HookSat ext readStdinName (readStdinBudgetSpec M A lim img)
  writeStdout : ∀ img, HookSat ext writeStdoutName (writeStdoutBudgetSpec M A lim img)
  -- `core` / `std`.
  memrchr : HookSat ext "core::slice::memchr::memrchr" memrchrSpec
  fromUtf8 : HookSat ext "core::str::converts::from_utf8" fromUtf8Spec
  fmtWrite : HookSat ext fmtWriteName (fmtWriteBudgetSpec M A lim)
  formatInner : HookSat ext formatInnerName (formatInnerBudgetSpec M A lim)
  durationSince : HookSat ext durationSinceHookName durationSinceEpochBudgetSpec
  timeAdd : HookSat ext timeAddHookName timeAddBudgetSpec
  blackBox : HookSat ext "subtle::black_box::<u8>" blackBoxSpec
  -- The session primitives `P.C`.
  compress256 : HookSat ext "sha2::sha256::compress256" (compress256Spec P.C)
  aesEnc : HookSat ext aesEncName (aesEncBudgetSpec P.C.E M A lim)
  aesDec : HookSat ext aesDecName (aesDecBudgetSpec P.C.D M A lim)
  pubFromSecret : HookSat ext pubFromSecretName (pubFromSecretSpec P.C)
  dh : HookSat ext dhName (dhSpec P.C)
  staticDrop : HookSat ext staticDropName zeroizeSpec
  sharedDrop : HookSat ext sharedDropName zeroizeSpec
  -- The PQXDH primitives `P.Q`.
  compress512 : HookSat ext CryptoVerification.E2E.compress512Name (compress512Spec P.Q)
  toEdwards : HookSat ext CryptoVerification.E2E.toEdwardsName (toEdwardsSpec P.Q)
  compress : HookSat ext CryptoVerification.E2E.compressName (pureByteFunctionSpec P.Q.compress false)
  edNeg : HookSat ext CryptoVerification.E2E.edNegName (pureByteFunctionSpec P.Q.edNeg true)
  torsionFree : HookSat ext CryptoVerification.E2E.torsionFreeName (torsionFreeSpec P.Q)
  dsmb : HookSat ext CryptoVerification.E2E.dsmbName (dsmbSpec P.Q)
  scalarMod : HookSat ext CryptoVerification.E2E.scalarModName (pureByteFunctionSpec P.Q.scalarMod true)
  scalarWide : HookSat ext CryptoVerification.E2E.scalarWideName (pureByteFunctionSpec P.Q.scalarWide false)
  kemEncaps : HookSat ext CryptoVerification.E2E.kemEncapsName (kemEncapsSpec P.Q)
  kemDecaps : HookSat ext CryptoVerification.E2E.kemDecapsName (kemDecapsSpec P.Q)
  -- SPQR V1's ML-KEM-768 and helpers (`P.Q.K`, HMAC over `P.C.F`).
  spqr : SpqrHooksBudget P.C M A lim P.Q.K ext

/-- Lift any non-allocating `HookSat` witness under `CliExternsBudgetOk` to `withVmPreserved`. -/
theorem CliExternsBudgetOk.liftVm [LibsignalPlacement] {P : PEParams} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    {name : String} {α : Type} {spec : Spec α}
    (hExt : CliExternsBudgetOk P M A lim ext)
    (hNotAlloc : name ∉ cliAllocNames)
    (hSat : HookSat ext name spec) :
    HookSat ext name (withVmPreserved spec) :=
  hookSat_withVmPreserved hSat (fun f hf => hExt.vmKept name f hf hNotAlloc)

theorem CliExternsBudgetOk.toTripleRatchetHooksBudget [LibsignalPlacement]
    {P : PEParams} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ext : String → Option (State → State)}
    (hExt : CliExternsBudgetOk P M A lim ext) (S : SpqrModel) :
    TripleRatchetHooksBudget P.C M A lim S ext where
  alloc := hExt.alloc
  allocZeroed := hExt.allocZeroed
  aesEnc := hExt.aesEnc
  aesDec := hExt.aesDec
  formatInner := hExt.formatInner
  fmtWrite := hExt.fmtWrite

/-! ## Instantiation Checks -/

section MallocngInstantiationSanity
variable [LibsignalPlacement]

theorem mallocng_tripleRatchetHooksBudget_proj
    (J : VerifiedLibraries.Mallocng.MallocngIface)
    (hS : MallocngCostModelSound coarseCostModel (coarseCostModelIface J))
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (C : Crypto) (lim : BudgetLimits) (S : SpqrModel)
    (abs : String → Option (State → State))
    (h : TripleRatchetHooksBudget C coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim S abs) :
    AllocHooksBudget coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim abs :=
  h.alloc

theorem mallocng_publicApiHooksBudget_proj
    (J : VerifiedLibraries.Mallocng.MallocngIface)
    (hS : MallocngCostModelSound coarseCostModel (coarseCostModelIface J))
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (C : Crypto) (lim : BudgetLimits) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (abs : String → Option (State → State))
    (h : PublicApiHooksBudget C coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim S encRecord abs) :
    TripleRatchetHooksBudget C coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim S abs :=
  h.toTripleRatchetHooksBudget

omit [LibsignalPlacement] in
theorem mallocng_spqrHooksBudget_proj
    (J : VerifiedLibraries.Mallocng.MallocngIface)
    (hS : MallocngCostModelSound coarseCostModel (coarseCostModelIface J))
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (C : Crypto) (lim : BudgetLimits) (K : MlKem)
    (abs : String → Option (State → State))
    (h : SpqrHooksBudget C coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim K abs) :
    HookSat abs libcruxHmacName
      (libcruxHmacBudgetSpec C.F coarseCostModel
        (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
        lim) :=
  h.hmac

theorem mallocng_cliExternsBudgetOk_proj
    (J : VerifiedLibraries.Mallocng.MallocngIface)
    (hS : MallocngCostModelSound coarseCostModel (coarseCostModelIface J))
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (P : PEParams) (lim : BudgetLimits) (S : SpqrModel)
    (ext : String → Option (State → State))
    (h : CliExternsBudgetOk P coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim ext) :
    TripleRatchetHooksBudget P.C coarseCostModel
      (mallocngRustCliAllocBudget coarseCostModel (coarseCostModelIface J) hS γ mpl tp brkStart)
      lim S ext :=
  h.toTripleRatchetHooksBudget S

end MallocngInstantiationSanity

end LibsignalBinary.Heap.SpecBudget
