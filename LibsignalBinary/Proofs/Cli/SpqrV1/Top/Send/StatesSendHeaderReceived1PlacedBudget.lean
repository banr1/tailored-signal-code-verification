/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
public import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendHeaderReceived1
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.headerReceived` Arm (Part 1: `+1312..+1680`, Block `427`)

Threads `RustCliAllocBudget` through ML-KEM encapsulation, `ct1` / `info` allocation,
HKDF derivation, and authenticator update (`+1312..+1680`) in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.RustHeap (RustAlloc allocHookStack vecU8 vecU8Buf)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded extHookStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalSpqrV1
  (Authenticator Bytes Header HkdfFn MlKem MlkemEncaps1Call hkdfToVecUnchecked mlkemEncaps1Spec
   sckaKeyInfoPrefix)
open CryptoVerification.SpqrV1.Alloc
  (spqrRustAllocSym spqrRustNoAllocShimSym spqr_hook_ok_of_mem)
open CryptoVerification.SpqrV1.Auth
  (AuthUpdateGhost AuthenticatorGhost authUpdateStackX authenticatorAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt)
open CryptoVerification.SpqrV1.Kdf (HkdfToVecGhost spqrRustAllocZeroedSym)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt epochBeBytes epochBeBytes_length exists_words4_of_len32
   fold_authenticatorAt_of_inline_local infoSlots_entails_pointsToBytes
   live_pointsTo_entails_vecU8Buf memRegion_32_16_eq_words2 memRegion_32_eq_words4
   memRegion_32_split_24_8 memRegion_41_eq_infoSlots memRegion_48_eq_words6
   pointsTo8_and_ct1_entails_memRegion_961 sckaInfoW0 sckaInfoW1 sckaInfoW2 sckaInfoW3
   sp_add_4704_orr_1_eq spqrSendCalleeStack stackAt_spqrSendCallee_from_allocHook
   stackAt_spqrSendCallee_from_extHook stackAt_spqrSendCallee_to_allocHook
   stackAt_spqrSendCallee_to_extHook vecU8_len32_expose_7536 words4At words4At_entails_memRegion)
open CryptoVerification.Cli.SpqrV1.Top.Send
  (rodata_sckaKeyInfoPrefix_placed rodata_zeros32_send_placed sckaKeyInfoPrefix_ro_split
   spqrCoinsAfterPlaced spqrCoinsAtPlaced spqrCoinsAtPlaced_entails_after_zero
   spqrMlkemEncaps1Sym)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FitsStep FitsTrace FitsTraceOf
   RustCliAllocBudget RustLayoutOk SeqEnv VmPreserved coarseCostModel fitsEvents_append
   fitsEvents_of_prefix_fitsTrace rustAllocEvents rustCliAllocNoOomSpec
   subroutine_ok_allocNoOom_of_budget)
open LibsignalBinary.Heap.SpecBudget (rustAllocZeroedBudgetSpec withVmPreserved)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced CoinsFillPlacedOkX spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget (seq_vm_lscro)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SeamSpecsPlacedBudget
  (spqrCoinsFillAtPlaced_of_after0_cro spqrCoinsFillAtSpecPlaced)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (spqrSend_encapsulate1_ok_placed)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (call_lscro_calleeStack_evs_sepWP call_lscro_calleeStack_sepWP finish_sepWP_lscro_plain
   of_sepWP_lscro_plain spqrSend_allocNoOom_ok_placed spqrSend_alloc_ok_placed
   spqrSend_session_memcpy_region_ok_placed spqrSend_shim_ok_placed)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)
open LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudget
  (AuthUpdateEnv AuthUpdateLenEnv authUpdatePinnedEvents
   authUpdatePinnedEvents_mem_authUpdateLenEnv authUpdateSpec spqrBoundedEvs_of_authUpdateLenEnv)
open LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToVecBudget
  (HkdfToVecEnv hkdfToVecSpec hkdfToVecSpqrSpec)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.SendCt2EncoderBudgetAux
  (call_memcpy_bytes_budget call_rustAllocNoOom_budget call_sessionShim_budget)
open LibsignalBinary.Proofs.SpqrV1.Top.InitInner.DefsPlacedBudget (SpqrBoundedEvs)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
  (sessionMemcpyRegionBudgetSpec sessionShimBudgetSpec)
open VerifiedLibraries.Mallocng (MallocngMaxAllocSize)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  ] do
    Lean.Attribute.erase nm `arm64_norm

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Callee Contracts, Re-Exports & Zeroed-Allocator Hook Extractors -/

export CryptoVerification.SpqrV1.Kdf (spqrRustAllocZeroedSym)

export CryptoVerification.Cli.SpqrV1.Top.Send
  (rodata_sckaKeyInfoPrefix_placed rodata_zeros32_send_placed sckaKeyInfoPrefix_ro_split)

export LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled1PlacedBudget
  (spqrSend_encapsulate1_ok_placed)

/-- `spqr::kdf::hkdf_to_vec` (Block `378`) meets
    `withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec M A lim HkdfFn)` on `spqrSendPlacedProg ext`. -/
def HkdfToVecPlacedOkX (M : AllocCostModel) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (HkdfFn : Bytes → Bytes → Bytes → Nat → Bytes)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 378)
    (withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec M A lim HkdfFn))

/-- `<Authenticator>::update` (Block `341`) meets
    `withLsCodeRoLoaded lsmpl (authUpdateSpec F M A lim)` on `spqrSendPlacedProg ext`. -/
def AuthUpdatePlacedOkX (F : ShaCompress) (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 341)
    (withLsCodeRoLoaded lsmpl (authUpdateSpec F M A lim))

theorem spqrSend_allocZeroed_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocZeroedSym)
      (rustAllocZeroedBudgetSpec M A lim) :=
  spqr_hook_ok_of_mem hZero

theorem spqrSend_allocZeroedNoOom_ok_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim)) :
    subroutine_ok (spqrSendPlacedProg ext) (lsρ spqrRustAllocZeroedSym)
      (rustCliAllocNoOomSpec M A lim true) :=
  subroutine_ok_allocNoOom_of_budget (spqrSend_allocZeroed_ok_placed hZero)

/-! ## 2. Exact Allocator Event Sequences & Envelopes (`+1312 -> +1680`) -/

/-- Exact allocator event sequence of `.headerReceived` Sub-step 1a (`+1312 -> +1504`):
    `__rust_alloc_zeroed(2080, 1)` for `es` followed by `__rust_alloc_zeroed(32, 1)` for `ss`. -/
def headerReceived1aEvents : List AllocEvent :=
  rustAllocEvents 2080 1 ++ rustAllocEvents 32 1

/-- Exact allocator event envelope for `.headerReceived` Sub-step 1a (`+1312 -> +1504`). -/
def HeaderReceived1aEnv (evs : List AllocEvent) : Prop :=
  evs = headerReceived1aEvents

theorem headerReceived1aEnv_nonempty : ∃ evs, HeaderReceived1aEnv evs :=
  ⟨headerReceived1aEvents, rfl⟩

@[simp]
theorem fitsEnv_headerReceived1a_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st HeaderReceived1aEnv ↔ FitsEvents M lim st headerReceived1aEvents :=
  FitsEnv.eq_iff

theorem fitsEvents_headerReceived1aEvents_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEvents M lim st headerReceived1aEvents) :
    FitsEvents M lim st (rustAllocEvents 2080 1) ∧
    FitsEvents M lim (M.stepEvents (rustAllocEvents 2080 1) st) (rustAllocEvents 32 1) ∧
    M.stepEvents headerReceived1aEvents st =
      M.stepEvents (rustAllocEvents 32 1) (M.stepEvents (rustAllocEvents 2080 1) st) := by
  unfold headerReceived1aEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨h2080, h32⟩
  refine ⟨h2080, h32, ?_⟩
  unfold headerReceived1aEvents
  rw [M.stepEvents_append]

/-- Exact allocator event prefix of `.headerReceived` Sub-step 2 before `<Authenticator>::update`:
    `__rust_alloc(960, 1)` (`ct1`), `__rust_alloc(41, 1)` (`info`), and `hkdf_to_vec` (`alloc(32, 1)`). -/
def headerReceived1bPreEvents : List AllocEvent :=
  rustAllocEvents 960 1 ++ (rustAllocEvents 41 1 ++ rustAllocEvents 32 1)

/-- Exact envelope for the pre-`update` prefix of `.headerReceived` Sub-step 2. -/
def HeaderReceived1bPreEnv (evs : List AllocEvent) : Prop :=
  evs = headerReceived1bPreEvents

@[simp]
theorem fitsEnv_headerReceived1bPre_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ} :
    FitsEnv M lim st HeaderReceived1bPreEnv ↔ FitsEvents M lim st headerReceived1bPreEvents :=
  FitsEnv.eq_iff

theorem fitsEvents_headerReceived1bPreEvents_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} (h : FitsEvents M lim st headerReceived1bPreEvents) :
    FitsEvents M lim st (rustAllocEvents 960 1) ∧
    FitsEvents M lim (M.stepEvents (rustAllocEvents 960 1) st) (rustAllocEvents 41 1) ∧
    FitsEvents M lim
      (M.stepEvents (rustAllocEvents 41 1) (M.stepEvents (rustAllocEvents 960 1) st))
      (rustAllocEvents 32 1) ∧
    M.stepEvents headerReceived1bPreEvents st =
      M.stepEvents (rustAllocEvents 32 1)
        (M.stepEvents (rustAllocEvents 41 1) (M.stepEvents (rustAllocEvents 960 1) st)) := by
  unfold headerReceived1bPreEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨h960, hrest⟩
  rcases (fitsEvents_append M lim _ _ _).mp hrest with ⟨h41, h32⟩
  refine ⟨h960, h41, h32, ?_⟩
  unfold headerReceived1bPreEvents
  rw [M.stepEvents_append, M.stepEvents_append]

/-- Allocator event envelope for `.headerReceived` Sub-step 2 (`+1504 -> +1680`), parameterized
    only by `auth.rootKey.length` (no unguarded existentials or `ValidRustAllocEv` universal). -/
def HeaderReceived1bEnv (rkLen : Nat) : List AllocEvent → Prop :=
  SeqEnv HeaderReceived1bPreEnv (AuthUpdateLenEnv rkLen 32)

/-- Combined allocator event envelope for `.headerReceived` Part 1 (`+1312 -> +1680`). -/
def HeaderReceived1Env (rkLen : Nat) : List AllocEvent → Prop :=
  SeqEnv HeaderReceived1aEnv (HeaderReceived1bEnv rkLen)

theorem headerReceived1bEnv_nonempty (g : AuthenticatorGhost) (rkLen : Nat) :
    ∃ evs, HeaderReceived1bEnv rkLen evs :=
  ⟨headerReceived1bPreEvents ++ authUpdatePinnedEvents g rkLen 32,
   SeqEnv.append rfl (authUpdatePinnedEvents_mem_authUpdateLenEnv g rkLen 32)⟩

theorem headerReceived1Env_nonempty (g : AuthenticatorGhost) (rkLen : Nat) :
    ∃ evs, HeaderReceived1Env rkLen evs := by
  obtain ⟨evs2, h2⟩ := headerReceived1bEnv_nonempty g rkLen
  exact ⟨headerReceived1aEvents ++ evs2, SeqEnv.append rfl h2⟩

private theorem spqrBoundedEvs_rustAlloc1 (n maxReq : Nat)
    (hpos : 0 < n) (hmax : n ≤ MallocngMaxAllocSize) (hreq : n ≤ maxReq) :
    SpqrBoundedEvs 1 maxReq (rustAllocEvents n 1) := by
  have hc : (1 : Nat) ≤ 16 ∧ 1 ≤ n := ⟨by decide, hpos⟩
  unfold rustAllocEvents
  simp only [hc, and_self, ↓reduceIte]
  refine ⟨Nat.le_refl 1, fun ev hev => ?_⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨hmax, hreq, (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

theorem spqrBoundedEvs_of_headerReceived1aEnv {evs : List AllocEvent}
    (h : HeaderReceived1aEnv evs) :
    SpqrBoundedEvs 2 2080 evs := by
  subst h
  unfold headerReceived1aEvents
  have h1 :=
    (spqrBoundedEvs_rustAlloc1 2080 2080 (by decide) (by decide) (Nat.le_refl 2080)).append
      (spqrBoundedEvs_rustAlloc1 32 2080 (by decide) (by decide) (by decide))
  rw [Nat.max_self] at h1
  exact h1

theorem spqrBoundedEvs_of_headerReceived1bPreEnv {evs : List AllocEvent}
    (h : HeaderReceived1bPreEnv evs) :
    SpqrBoundedEvs 3 960 evs := by
  subst h
  unfold headerReceived1bPreEvents
  have h1 :=
    (spqrBoundedEvs_rustAlloc1 960 960 (by decide) (by decide) (Nat.le_refl 960)).append
      ((spqrBoundedEvs_rustAlloc1 41 960 (by decide) (by decide) (by decide)).append
        (spqrBoundedEvs_rustAlloc1 32 960 (by decide) (by decide) (by decide)))
  rw [Nat.max_self, Nat.max_self] at h1
  exact h1

theorem spqrBoundedEvs_of_headerReceived1bEnv {rkLen : Nat} {evs : List AllocEvent}
    (hmax : rkLen + 32 ≤ MallocngMaxAllocSize)
    (h : HeaderReceived1bEnv rkLen evs) :
    SpqrBoundedEvs 8 (max 960 (rkLen + 96)) evs := by
  rcases h with h1 | ⟨evs1, evs2, rfl, h1, h2⟩
  · exact (spqrBoundedEvs_of_headerReceived1bPreEnv h1).mono (by decide) (Nat.le_max_left _ _)
  · have hb1 := spqrBoundedEvs_of_headerReceived1bPreEnv h1
    have hb2 : SpqrBoundedEvs 5 (rkLen + 96) evs2 := by
      simpa only [Nat.add_assoc] using spqrBoundedEvs_of_authUpdateLenEnv hmax h2
    exact hb1.append hb2

theorem spqrBoundedEvs_of_headerReceived1Env {rkLen : Nat} {evs : List AllocEvent}
    (hmax : rkLen + 32 ≤ MallocngMaxAllocSize)
    (h : HeaderReceived1Env rkLen evs) :
    SpqrBoundedEvs 10 (max 2080 (max 960 (rkLen + 96))) evs := by
  rcases h with h1 | ⟨evs1, evs2, rfl, h1, h2⟩
  · exact (spqrBoundedEvs_of_headerReceived1aEnv h1).mono (by decide) (Nat.le_max_left _ _)
  · exact (spqrBoundedEvs_of_headerReceived1aEnv h1).append
      (spqrBoundedEvs_of_headerReceived1bEnv hmax h2)

-- Non-vacuity witness under `coarseCostModel`: `headerReceived1aEvents` fits concrete limits.
example :
    FitsEvents coarseCostModel
      { staticCount := 16, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      coarseCostModel.init
      headerReceived1aEvents :=
  fitsEvents_of_prefix_fitsTrace (pre := []) (List.prefix_refl _)
    (show FitsTraceOf coarseCostModel
        { staticCount := 16, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
        headerReceived1aEvents by
      unfold FitsTraceOf FitsTrace FitsStep; decide)

-- Non-vacuity witness under `coarseCostModel`: a canonical `HeaderReceived1bEnv 32` trace fits
-- concrete limits.
example :
    FitsEvents coarseCostModel
      { staticCount := 16, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
      coarseCostModel.init
      (headerReceived1bPreEvents ++
        authUpdatePinnedEvents { rootKey := ⟨32, 1⟩, macKey := ⟨32, 1⟩ } 32 32) :=
  fitsEvents_of_prefix_fitsTrace (pre := []) (List.prefix_refl _)
    (show FitsTraceOf coarseCostModel
        { staticCount := 16, staticBytes := 2 ^ 24, physCap := 2 ^ 30 }
        (headerReceived1bPreEvents ++
          authUpdatePinnedEvents { rootKey := ⟨32, 1⟩, macKey := ⟨32, 1⟩ } 32 32) by
      unfold FitsTraceOf FitsTrace FitsStep; decide)


/-! ## 3. Local Pool-Sync & Subroutine Call Helpers -/

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_setMem_local (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg128_local (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg64_local (s : State) (i : BitVec 5) (v : BitVec 64) :
    (s.writeVReg64 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
private theorem tpidrEl0_writeVReg32_local (s : State) (i : BitVec 5) (v : BitVec 32) :
    (s.writeVReg32 i v).tpidrEl0 = s.tpidrEl0 := by
  cases s; rfl

omit [LibsignalPlacement] in
private theorem sepWP_seg_vm_427 {P : Program} {b : BitVec 64}
    {Hk : String → Option (State → State)}
    {mid target : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop}
    (hseg : SepWP
      ((P.rebase b LibsignalBinary.Proofs.Placed.BudgetVmSteps.trapHooks).withSvc noSyscalls)
      mid s Pre (fun sm Pm => sm.tpidrEl0 = s.tpidrEl0 ∧
        (VmPreserved s sm → SepWP (P.rebase b Hk) target sm Pm post))) :
    SepWP (P.rebase b Hk) target s Pre post := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvm, hcont⟩ | ⟨_, hoom⟩⟩ :=
    SepWP.to_reaches_pc
      (LibsignalBinary.Proofs.Placed.BudgetVmSteps.sepWP_rebase_vmPreserved (Hk := Hk) hseg) hm hL
  · obtain ⟨sf, hsteps', hout⟩ := SepWP.to_reaches_pc (hcont hvm) hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

local syntax "by_vm_seg_427 " term:max ppSpace "(" tacticSeq ")" : tactic
local elab_rules : tactic
  | `(tactic| by_vm_seg_427 $mid:term ($tac:tacticSeq)) => do
    Lean.Elab.Tactic.evalTactic (← `(tactic| apply sepWP_seg_vm_427 (mid := $mid)))
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let initLCtx ← Lean.getLCtx
      let ty := (← Lean.instantiateMVars (← g.getType)).consumeMData
      let e2 := ty.getArg! 0
      let e1 := e2.getArg! 0
      let ty1 := Lean.mkAppN ty.getAppFn #[e1, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5]
      let g1 ← Lean.Meta.mkFreshExprMVar ty1
      let savedGoals ← Lean.Elab.Tactic.getGoals
      Lean.Elab.Tactic.setGoals [g1.mvarId!]
      Lean.Elab.Tactic.evalTactic (← `(tactic| ($tac)))
      let rem ← Lean.Elab.Tactic.getGoals
      let mut revData : Array (Lean.MVarId × Nat × Lean.Expr) := #[]
      for r in rem do
        let rLCtx ← r.withContext Lean.getLCtx
        let mut newFVars : Array Lean.FVarId := #[]
        for ldecl in rLCtx do
          if !ldecl.isImplementationDetail && !initLCtx.contains ldecl.fvarId then
            newFVars := newFVars.push ldecl.fvarId
        let (reverted, rRev) ← r.revert newFVars true
        let revTy ← rRev.getType
        revData := revData.push (rRev, reverted.size, revTy)
      let rec instWithDummies :
          List (Lean.MVarId × Nat × Lean.Expr) → Array Lean.Expr →
            Lean.MetaM (Lean.Expr × Array Lean.Expr)
        | [], dummies => do
          let savedMCtx ← Lean.getMCtx
          let prf ← try
            for j in [:revData.size] do
              revData[j]!.1.assign dummies[j]!
            Lean.instantiateMVars g1
          finally
            Lean.setMCtx savedMCtx
          return (prf, dummies)
        | (_, _, revTy) :: rest, dummies =>
          Lean.Meta.withLocalDeclD (`_vm_cont) revTy fun fv =>
            instWithDummies rest (dummies.push fv)
      let (prf1, dummies) ← instWithDummies revData.toList #[]
      let nArgs := e1.getAppNumArgs
      let hk := (e1.getArg! 2).consumeMData
      let e2Fn := e2.getAppFn
      let e2Args := e2.getAppArgs
      let prf2 := prf1.replace fun sub =>
        match dummies.findIdx? (fun d => d == sub) with
        | some j => some (Lean.mkMVar revData[j]!.1)
        | none =>
          if sub.isAppOfArity ``Arm64.Program.withSvc e2Args.size then
            some sub
          else if sub.isAppOfArity ``Arm64.Program.rebase nArgs &&
              (sub.getArg! 2).consumeMData.eqv hk then
            some (Lean.mkAppN e2Fn (e2Args.set! 0 sub))
          else
            none
      g.assign prf2
      let mut newRem : List Lean.MVarId := []
      for (rRev, nRev, _) in revData do
        let (_, rIntro) ← rRev.introNP nRev
        newRem := newRem ++ [rIntro]
      Lean.Elab.Tactic.setGoals (newRem ++ savedGoals.tail!)

local macro "wp_steps_427 " mid:term : tactic =>
  `(tactic|
    by_vm_seg_427 $mid (
      wp_steps
      refine ProofLib.SepWP.done (by wp_norm_lhs) (by wp_norm_lhs)
        ⟨by first | wp_norm_lhs | simp only [wp_norm, arm64_norm],
         fun _hvm => ProofLib.SepWP.transport_budgetPool _hvm (hnext := ?_)⟩))

attribute [local simp, local arm64_norm, local wp_norm]
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_advancePC
  LibsignalBinary.Heap.RustCliAllocBudget.pool_setPState
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg32
  LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem pc_setMem_pre (s : State) (m : Memory) : (s.setMem m).pc = s.pc := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem status_setMem_pre (s : State) (m : Memory) : (s.setMem m).status = s.status := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem trace_setMem_pre (s : State) (m : Memory) : (s.setMem m).trace = s.trace := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem sp_setMem_pre (s : State) (m : Memory) : (s.setMem m).sp = s.sp := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem readReg64_setMem_pre (s : State) (m : Memory) (r : Reg) :
    (s.setMem m).readReg64 r = s.readReg64 r := by
  cases s; rfl

@[local simp, local arm64_norm ↓, local wp_norm ↓]
private theorem calleeSavedVRegs_setMem_pre (s : State) (m : Memory) :
    calleeSavedVRegs (s.setMem m) = calleeSavedVRegs s := by
  cases s; rfl

private theorem call_shim_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionShimBudgetSpec)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hsplit : P = A.pool lim st s ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf (A.pool lim st sf ∗ Frame) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  exact call_sessionShim_budget hcall st hpc hrun hsp hsp_align hlr htrace hsplit
    fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

private theorem call_allocNoOom_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim false))
    (size : Nat) (st : M.σ) (hlay : RustLayoutOk size 1)
    (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗ memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine call_rustAllocNoOom_budget hcall size 1 st hlay hfit
    hpc hrun hsp hsp_align hlr htrace hx0 hx1 (by sep_focus)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf hne0 => ?_) hlr_ls
  simp only [Reg.x0] at hne0 ⊢
  refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
  exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
    SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
      (hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf hne0 (beq_false_of_ne hne0) htr_sf)

private theorem call_allocZeroedNoOom_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (rustCliAllocNoOomSpec M A lim true))
    (size : Nat) (st : M.σ) (hlay : RustLayoutOk size 1)
    (hfit : FitsEvents M lim st (rustAllocEvents size 1))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 .x0).toNat = size) (hx1 : (s.readReg64 .x1).toNat = 1)
    (hsplit : P = (A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0#64 → (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗ memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool lim (M.stepEvents (rustAllocEvents size 1) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post)
    (hlr_ls : LsRetAddr624 ret_pc := by
      first | assumption | simp (config := { decide := true }) only [Reg.x30, Reg.lr, arm64_norm, wp_norm]) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall (x := (size, 1, st))
    (F := memRegion (sp_call - 123008#64) 118912 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [rustCliAllocNoOomSpec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hlay, hfit, by rw [hlr]; exact hlr_ls⟩, by ac_nf at hm ⊢⟩
  · simp only [rustCliAllocNoOomSpec, ↓reduceIte]
    rw [hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨hacp, hne0, _⟩ => ?_
    simp only [Reg.x0] at hne0 ⊢
    have hzero_mem :
        (sf.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ⊢
        memRegion (sf.readReg64 (Reg.gpr 0#5)) size := by
      have h := pointsToBytes_entails_memRegion (sf.readReg64 (Reg.gpr 0#5)) (List.replicate size 0#8)
      rwa [List.length_replicate] at h
    refine SepWP.fold hzero_mem (by sep_focus) ?_
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf
          hne0 (beq_false_of_ne hne0) (hacp.2.1.trans htrace))

private theorem call_memcpy_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    (dst src : BitVec 64) (bs : Bytes) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hsplit : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  exact call_memcpy_bytes_budget hcall dst src bs st hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    hsplit fun sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf =>
      SepWP.done hpc_sf hrun_sf fun hcrl1 => hnext sf hcrl1 hpc_sf hrun_sf hsp_sf hcs_sf htr_sf

private theorem call_mlkemEncaps1_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {K : MlKem} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withVmPreserved (mlkemEncaps1Spec K)))
    (retA hdrA randA esA ssA : BitVec 64) (hdr : Bytes) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 hdr rand = some (ct1, es, ss)) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = retA) (hx0 : s.readReg64 .x0 = hdrA)
    (hx1 : (s.readReg64 .x1).toNat = hdr.length) (hx2 : s.readReg64 .x2 = randA)
    (hx3 : s.readReg64 .x3 = esA) (hx4 : s.readReg64 .x4 = 2080#64)
    (hx5 : s.readReg64 .x5 = ssA) (hx6 : s.readReg64 .x6 = 32#64)
    (hsplit : P = ((hdrA ↦ₛ hdr) ∗ (randA ↦ₛ rand.toList) ∗ memRegion retA 961 ∗
      memRegion esA 2080 ∗ memRegion ssA 32 ∗ A.pool lim st s ∗
      stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.trace = s0.trace →
      SepWP prog tgt sf
        (((hdrA ↦ₛ hdr) ∗ (randA ↦ₛ rand.toList) ∗ (retA ↦₈ 0#8) ∗
          ((retA + 1#64) ↦ₛ ct1.toList) ∗ (esA ↦ₛ es.toList) ∗ (ssA ↦ₛ ss.toList) ∗
          A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall
    (x := ({ ret := retA, hdrA := hdrA, hdr := hdr, randA := randA, rand := rand,
             esA := esA, ssA := ssA } : MlkemEncaps1Call))
    (F := memRegion (sp_call - 123008#64) 106624 ∗ A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [withVmPreserved, mlkemEncaps1Spec]
    rw [hsp]; simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6⟩, by ac_nf at hm ⊢⟩
  · dsimp only [withVmPreserved, mlkemEncaps1Spec]
    rw [hencaps, hsp]; dsimp only; rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm1 => SepWP.pure_elim fun htr1 => ?_
    rw [← A.pool_of_vmPreserved hvm1]
    refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp_call) (by sep_focus) ?_
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf (htr1.trans htrace))

private theorem sepWP_intro_rodata {prog : Program} {tgt : BitVec 64} {s : State}
    {Ro P : SepProp} {post : State → SepProp → Prop}
    (hro : ∀ {Q : SepProp}, s.mem ⊨ Q → s.mem ⊨ Ro ∗ Q)
    (h : SepWP prog tgt s (Ro ∗ P) post) :
    SepWP prog tgt s P post := by
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  have hm' : s.mem ⊨ (Ro ∗ P) ∗ R := by rw [sepConj_assoc]; exact hro hm
  exact SepWP.to_reaches_pc h hm' hL

private theorem finish_sepWP_lscro_drop_ro_plain {prog : Program} {mid tgt : BitVec 64}
    {s : State} {P P' Ro : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : LibsignalCodeRoLoaded lsmpl s.mem → SepWP prog tgt s P' post)
    (himp : P ⊢ Ro ∗ P') :
    SepWP prog mid s P (fun sf P_f => LibsignalCodeRoLoaded lsmpl sf.mem → SepWP prog tgt sf P_f post) := by
  refine SepWP.fold himp (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  apply SepWP.done hpc hrun
  intro hinv
  refine SepWP.of_reaches_pc fun R hsat hL => ?_
  rw [sepConj_assoc] at hsat
  exact SepWP.to_reaches_pc (hnext hinv) (Satisfies.of_sep_right hsat) hL

private theorem call_coinsFill32_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    {ctl cur : BitVec 64} {tape : List (BitVec 8)}
    (hcall : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (spqrCoinsFillAtSpecPlaced spqrSendCalleeStack cur tape)))
    (h32 : 32 ≤ tape.length)
    (dstA : BitVec 64) (rand : List.Vector (BitVec 8) 32) (hrand_val : rand.toList = tape.take 32)
    (st : M.σ) {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dstA) (hx1 : (s.readReg64 .x1).toNat = 32)
    (hsplit : P = (memRegion dstA 32 ∗ spqrCoinsAfterPlaced ctl cur tape 0 ∗
      A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → sf.trace = s0.trace →
      SepWP prog tgt sf
        (((dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  have hcoins0 : spqrCoinsAfterPlaced ctl cur tape 0 = spqrCoinsAfterPlaced 0#64 cur tape 0 := rfl
  rw [hsplit, hcoins0]
  refine call_lscro_calleeStack_sepWP (x := (dstA, 32))
    sp_call spqrSendCalleeStack (by decide)
    (T_pre := memRegion dstA 32 ∗ spqrCoinsAfterPlaced 0#64 cur tape 0)
    (T_post := fun sf => ⌜sf.trace = s.trace⌝ ∗
      (dstA ↦ₛ (tape ++ List.replicate 32 0#8).take 32) ∗
      spqrCoinsAfterPlaced 0#64 cur tape (min 32 tape.length))
    (F := A.pool lim st s ∗ Frame)
    (φ_pre := s.readReg64 .x0 = dstA ∧ (s.readReg64 .x1).toNat = 32)
    (φ_post := fun sf => VmPreserved s sf)
    hcall hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl)
    ⟨hx0, hx1⟩ (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [spqrCoinsFillAtSpecPlaced, CryptoVerification.Cli.SpqrV1.Top.Send.spqrCoinsFillAtSpecPlaced, withVmPreserved]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf hvm_sf hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  have hcoins_ctl : spqrCoinsAfterPlaced 0#64 cur tape 32 = spqrCoinsAfterPlaced ctl cur tape 32 := rfl
  rw [List.take_append_of_le_length h32, Nat.min_eq_left h32, hcoins_ctl, ← hrand_val,
      ← A.pool_of_vmPreserved hvm_sf]
  have hpure :
      ((stackAt sp_call spqrSendCalleeStack ∗
        (⌜sf.trace = s.trace⌝ ∗ (dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32)) ∗
        (A.pool lim st sf ∗ Frame)) =
      ⌜sf.trace = s.trace⌝ ∗
        (((dstA ↦ₛ rand.toList) ∗ spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim st sf ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by sep_ac_rfl
  rw [hpure]
  exact SepWP.pure_elim fun htr_sf =>
    hnext sf hcrl_sf hpc_sf hrun_sf hsp_sf
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs (htr_sf.trans htrace)

/-! ## 4. Budget-Threaded Sub-Step 1a (`+1312 -> +1504`, `K.encaps1 = some (ct1, es, ss)`) -/

private theorem sp_add_4704_add_1 (sp : BitVec 64) :
    (sp + 4704#64) + 1#64 = sp + 4705#64 := by bv_omega

private theorem fold_end_1a {M : AllocCostModel} (A : RustCliAllocBudget M) (sp es_ptr : BitVec 64)
    (rw0 rw1 rw2 rw3 : BitVec 64) (rand : List.Vector (BitVec 8) 32)
    (es : List.Vector (BitVec 8) 2080) (hne0 : es_ptr ≠ 0) :
    words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗
    ((sp + 7536#64) ↦ₛ rand.toList) ∗
    A.live es_ptr 2080 1 ∗
    (es_ptr ↦ₛ es.toList) ⊢
    memRegion (sp + 7136#64) 32 ∗
    memRegion (sp + 7536#64) 32 ∗
    vecU8Buf A.repAlloc 2080#64 es_ptr es.toList := by
  have h7536 := pointsToBytes_entails_memRegion (sp + 7536#64) rand.toList
  rw [List.Vector.toList_length] at h7536
  have hes_buf := live_pointsTo_entails_vecU8Buf (A := A.repAlloc)
    es_ptr es.toList 2080 (List.Vector.toList_length es) (by decide) (by decide) hne0
  have hassoc :
      words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
        A.live es_ptr 2080 1 ∗ (es_ptr ↦ₛ es.toList) =
      words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
        (A.live es_ptr 2080 1 ∗ (es_ptr ↦ₛ es.toList)) := by sep_ac_rfl
  rw [hassoc]
  exact sepConj_mono (words4At_entails_memRegion (sp + 7136#64) rw0 rw1 rw2 rw3)
    (sepConj_mono h7536 hes_buf)

set_option maxHeartbeats 3200000 in
theorem step_headerReceived_1312_to_1504_sepWP_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ctl tgt : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32)
    (hrand_val : rand.toList = tape.take 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 hdr rand = some (ct1, es, ss))
    (d4056 : BitVec 64)
    (st : M.σ) (hfit : FitsEnv M lim st HeaderReceived1aEnv)
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
      ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
      (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗
      memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (es_ptr ss_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      es_ptr ≠ 0 → (es_ptr == 0#64) = false →
      ss_ptr ≠ 0 → (ss_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 1504#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = hdr_cap →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length →
      sf.readReg64 .x28 = sp + 4192#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((authInlineWordsAt g (sp + 4192#64) auth ∗
          authHeapBufs A.repAlloc g auth ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
          ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
          ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
          (hdr_ptr ↦ₛ hdr) ∗
          ((sp + 2464#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ((sp + 4704#64) ↦₈ 0#8) ∗
          ((sp + 4705#64) ↦ₛ ct1.toList) ∗
          vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
          A.live ss_ptr 32 1 ∗
          (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim (M.stepEvents headerReceived1aEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have ⟨hfit_2080, hfit_32, hstep_1a⟩ :=
    fitsEvents_headerReceived1aEvents_split (fitsEnv_headerReceived1a_iff.mp hfit)
  let st1 := M.stepEvents (rustAllocEvents 2080 1) st
  let st2 := M.stepEvents (rustAllocEvents 32 1) st1
  have hshim := spqrSend_shim_ok_placed hA
  have hallocz := spqrSend_allocZeroedNoOom_ok_placed hZero
  have hrng_call := spqrCoinsFillAtPlaced_of_after0_cro (cur := cur) (rest := tape) hcoinsFill
  have henc1_call := spqrSend_encapsulate1_ok_placed henc1
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  have hes_len : es.toList.length = 2080 := List.Vector.toList_length _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim hallocz hrng_call henc1_call hnext ⊢
  subst hP
  simp only [Reg.x24, Reg.x26, Reg.x28] at hx24 hx26 hx28
  apply of_sepWP_lscro_plain (mid := lsmpl.base 618) hinv
  rw [memRegion_48_eq_words6 (sp + 4192#64),
      memRegion_32_eq_words4 (sp + 7136#64),
      memRegion_32_eq_words4 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  wp_steps_427 (lsmpl.base 618)
  refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _)
    (by dsimp only [words4At]; sep_focus) ?_
  refine SepWP.fold (spqrCoinsAtPlaced_entails_after_zero ctl cur tape)
    (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_rng
  refine call_coinsFill32_lscro (ctl := ctl) hrng_call h32 (sp + 7136#64) rand hrand_val st
    (s0 := s0) (sp_call := sp) hinv_rng
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, BitVec.add_assoc, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    fun sr1 hinv_sr1 hpc_sr1 hrun_sr1 hsp_sr1
      hx19_r1 hx20_r1 hx21_r1 hx22_r1 hx23_r1 hx24_r1 hx25_r1 hx26_r1 hx27_r1 hx28_r1 hvregs_r1 htr_sr1 => ?_
  simp only [Reg.lr, Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sr1 hx19_r1 hx20_r1 hx21_r1 hx22_r1 hx23_r1 hx24_r1 hx25_r1 hx26_r1 hx27_r1 hx28_r1 hvregs_r1
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv_sr1
  wp_steps_427 (lsρ spqrRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_sh1
  refine call_shim_lscro hshim st (s0 := s0) (sp_call := sp) hinv_sh1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
    fun sh1 hinv_sh1' hpc_sh1 hrun_sh1 hsp_sh1 hcs_sh1 htr_sh1 => ?_
  rcases hcs_sh1 with ⟨hx19_s1, hx20_s1, hx21_s1, hx22_s1, hx23_s1, hx24_s1, hx25_s1, hx26_s1, hx27_s1, hx28_s1, _, hvregs_s1⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh1 hx19_s1 hx20_s1 hx21_s1 hx22_s1 hx23_s1 hx24_s1 hx25_s1 hx26_s1 hx27_s1 hx28_s1 hvregs_s1
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocZeroedSym) hinv_sh1'
  wp_steps_427 (lsρ spqrRustAllocZeroedSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_az1
  refine call_allocZeroedNoOom_lscro hallocz 2080 st ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_2080
    (s0 := s0) (ret_pc := (blkPl_427).base + 1400#64) (sp_call := sp) hinv_az1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv_ok1
  wp_steps_427 (lsρ spqrRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_sh2
  refine call_shim_lscro hshim st1 (s0 := s0) (sp_call := sp) hinv_sh2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
    fun sh2 hinv_sh2' hpc_sh2 hrun_sh2 hsp_sh2 hcs_sh2 htr_sh2 => ?_
  rcases hcs_sh2 with ⟨hx19_s2, hx20_s2, hx21_s2, hx22_s2, hx23_s2, hx24_s2, hx25_s2, hx26_s2, hx27_s2, hx28_s2, _, hvregs_s2⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh2 hx19_s2 hx20_s2 hx21_s2 hx22_s2 hx23_s2 hx24_s2 hx25_s2 hx26_s2 hx27_s2 hx28_s2 hvregs_s2
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocZeroedSym) hinv_sh2'
  wp_steps_427 (lsρ spqrRustAllocZeroedSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_az2
  refine call_allocZeroedNoOom_lscro hallocz 32 st1 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_32
    (s0 := s0) (ret_pc := (blkPl_427).base + 1424#64) (sp_call := sp) hinv_az2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩
  simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  apply of_sepWP_lscro_plain (mid := lsρ spqrMlkemEncaps1Sym) hinv_ok2
  obtain ⟨rw0, rw1, rw2, rw3, hrand_words⟩ :=
    exists_words4_of_len32 rand.toList (List.Vector.toList_length rand)
  wp_conv_pre => rw [hrand_words (sp + 7136#64)]; dsimp only [words4At]
  wp_steps_427 (lsρ spqrMlkemEncaps1Sym)
  have hfold_rand_7536 :
      words4At (sp + 7536#64) rw0 rw1 rw2 rw3 ⊢ ((sp + 7536#64) ↦ₛ rand.toList) := by
    rw [hrand_words (sp + 7536#64)]; exact Entails.refl _
  refine SepWP.fold hfold_rand_7536 (by dsimp only [words4At]; sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_enc
  refine call_mlkemEncaps1_lscro henc1_call
    (sp + 4704#64) hdr_ptr (sp + 7536#64)
    (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5))
    hdr rand hencaps st2 (s0 := s0) (sp_call := sp) hinv_enc
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x8, BitVec.add_assoc, arm64_norm, *]) (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, hhdr_toNat, arm64_norm, *]) (by simp only [Reg.x2, BitVec.add_assoc, arm64_norm, *])
    (by simp only [Reg.x3, arm64_norm, *]) (by simp only [Reg.x4, arm64_norm, *])
    (by simp only [Reg.x5, arm64_norm, *]) (by simp only [Reg.x6, arm64_norm, *])
    (by sep_focus)
    fun se1 hinv_se1 hpc_se1 hrun_se1 hsp_se1 hcs_se1 htr_se1 => ?_
  rcases hcs_se1 with ⟨hx19_e1, hx20_e1, hx21_e1, hx22_e1, hx23_e1, hx24_e1, hx25_e1, hx26_e1, hx27_e1, hx28_e1, _, hvregs_e1⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_se1 hx19_e1 hx20_e1 hx21_e1 hx22_e1 hx23_e1 hx24_e1 hx25_e1 hx26_e1 hx27_e1 hx28_e1 hvregs_e1
  rw [sp_add_4704_add_1 sp]
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 1504#64) hinv_se1
  wp_steps_427 ((blkPl_427).base + 1504#64)
  refine SepWP.fold
    (fold_end_1a A sp (sf1.readReg64 (Reg.gpr 0#5)) rw0 rw1 rw2 rw3 rand es hne0_1)
    (by dsimp only [words4At]; sep_focus) ?_
  dsimp only [st2, st1]
  rw [← hstep_1a]
  refine finish_sepWP_lscro_plain (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (fun hinv3 => hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5))
      hinv3 hne0_1 h0b_1 hne0_2 h0b_2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *])
      (by simp only [Reg.x19, arm64_norm, *])
      (by simp only [Reg.x20, arm64_norm, *])
      (by simp only [Reg.x21, arm64_norm, *])
      (by simp only [Reg.x22, arm64_norm, *])
      (by simp only [Reg.x23, arm64_norm, *])
      (by simp only [Reg.x24, arm64_norm, *])
      (by simp only [Reg.x25, arm64_norm, *])
      (by simp only [Reg.x26, arm64_norm, *])
      (by simp only [Reg.x27, arm64_norm, *])
      (by simp only [Reg.x28, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]))
    (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by sep_ac_rfl))

/-- Panic-aware (`SepWPp`) wrapper for `step_headerReceived_1312_to_1504_sepWP_placed`,
    generalized over arbitrary `post` and `Qp`. -/
theorem step_headerReceived_1312_to_1504_placed
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedBudgetSpec M A lim))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (withVmPreserved (mlkemEncaps1Spec K)))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32)
    (hrand_val : rand.toList = tape.take 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 hdr rand = some (ct1, es, ss))
    (d4056 : BitVec 64)
    (st : M.σ) (hfit : FitsEnv M lim st HeaderReceived1aEnv)
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
      ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
      (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗
      memRegion (sp + 7536#64) 32 ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (es_ptr ss_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      es_ptr ≠ 0 → (es_ptr == 0#64) = false →
      ss_ptr ≠ 0 → (ss_ptr == 0#64) = false →
      sf.pc = spqrSendPlacedEntry + 1504#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = hdr_cap →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length →
      sf.readReg64 .x28 = sp + 4192#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((authInlineWordsAt g (sp + 4192#64) auth ∗
          authHeapBufs A.repAlloc g auth ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
          ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
          ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
          (hdr_ptr ↦ₛ hdr) ∗
          ((sp + 2464#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ((sp + 4704#64) ↦₈ 0#8) ∗
          ((sp + 4705#64) ↦ₛ ct1.toList) ∗
          vecU8Buf A.repAlloc 2080#64 es_ptr es.toList ∗
          A.live ss_ptr 32 1 ∗
          (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          spqrCoinsAfterPlaced ctl cur tape 32 ∗
          A.pool lim (M.stepEvents headerReceived1aEvents st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 1504#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_headerReceived_1312_to_1504_sepWP_placed hA hZero hcoinsFill henc1
    g auth epoch hdr_cap hdr_ptr hdr hhdr_lt sp cur tape h32 rand hrand_val hencaps
    d4056 st hfit hinv hsp_align hpc hrun hsp hx24 hx26 hx28 htrace hP
    fun sf es_ptr ss_ptr hcrl_sf hne1 h0b1 hne2 h0b2 hpc_sf hrun_sf hsp_sf
      hx19 hx20 hx21 hx22 hx23 hx24' hx25 hx26' hx27 hx28' htr hvregs =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf es_ptr ss_ptr hcrl_sf hne1 h0b1 hne2 h0b2 hpc_sf hrun_sf hsp_sf
          hx19 hx20 hx21 hx22 hx23 hx24' hx25 hx26' hx27 hx28' htr hvregs

/-! ## 5. Budget-Threaded Sub-Step 2 (`+1504 -> +1680`) -/

private theorem bytesAt_true (a : BitVec 64) (bs : Bytes) : bytesAt true a bs = (a ↦ᵣ bs) := rfl

private theorem bytesAt_false (a : BitVec 64) (bs : Bytes) : bytesAt false a bs = (a ↦ₛ bs) := rfl

private theorem call_hkdfToVec32_lscro {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {HkdfFn : HkdfFn} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec M A lim HkdfFn)))
    (outVec saltA ikmA infoA : BitVec 64) (salt ikm info : Bytes)
    (st : M.σ) (hfit : FitsEnv M lim st (HkdfToVecEnv 32))
    (hsalt_lt : salt.length < 2 ^ 63) (hikm_lt : ikm.length < 2 ^ 63)
    (hinfo_ge : 32 ≤ info.length) (hinfo_lt : info.length < 55)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 .x8 = outVec)
    (hx0 : s.readReg64 .x0 = saltA) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 salt.length)
    (hx2 : s.readReg64 .x2 = ikmA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 ikm.length)
    (hx4 : s.readReg64 .x4 = infoA) (hx5 : s.readReg64 .x5 = BitVec.ofNat 64 info.length)
    (hx6 : s.readReg64 .x6 = 32#64)
    (hsplit : P = (memRegion outVec 24 ∗ (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗
      A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      (HkdfFn salt ikm info 32).length = 32 →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((vecU8 A.repAlloc outVec (HkdfFn salt ikm info 32) ∗
          (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗
          A.pool lim (M.stepEvents (rustAllocEvents 32 1) st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  let xg : HkdfToVecGhost := {
    outVec := outVec, saltRO := true, saltA := saltA, salt := salt,
    ikmRO := false, ikmA := ikmA, ikm := ikm,
    infoRO := false, infoA := infoA, info := info, okmLen := 32 }
  refine call_lscro_calleeStack_sepWP (x := (xg, st))
    sp_call extHookStack (by decide)
    (T_pre := memRegion outVec 24 ∗ (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗ A.pool lim st s)
    (T_post := fun sf => vecU8 A.repAlloc outVec (HkdfFn salt ikm info 32) ∗
      (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗
      (∃∗ evs : List AllocEvent, ⌜HkdfToVecEnv 32 evs⌝ ∗ A.pool lim (M.stepEvents evs st) sf))
    (F := Frame)
    (φ_pre := s.readReg64 .x8 = outVec ∧
      s.readReg64 .x0 = saltA ∧ s.readReg64 .x1 = BitVec.ofNat 64 salt.length ∧
      s.readReg64 .x2 = ikmA ∧ s.readReg64 .x3 = BitVec.ofNat 64 ikm.length ∧
      s.readReg64 .x4 = infoA ∧ s.readReg64 .x5 = BitVec.ofNat 64 info.length ∧
      s.readReg64 .x6 = BitVec.ofNat 64 32 ∧
      salt.length < 2 ^ 63 ∧ ikm.length < 2 ^ 63 ∧
      32 ≤ info.length ∧ info.length < 55 ∧
      ((32 : Nat) = 32 ∨ (32 : Nat) = 64 ∨ (32 : Nat) = 96) ∧
      FitsEnv M lim st (HkdfToVecEnv 32))
    (φ_post := fun sf => (HkdfFn salt ikm info 32).length = 32 ∧ sf.trace = s.trace)
    hcall hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [hkdfToVecSpqrSpec, hkdfToVecSpec, xg]; rw [bytesAt_true, bytesAt_false, bytesAt_false]; sep_ac_rfl)
    ⟨hx8, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hsalt_lt, hikm_lt, hinfo_ge, hinfo_lt, Or.inl rfl, hfit⟩
    (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf; dsimp only [hkdfToVecSpqrSpec, hkdfToVecSpec, xg]; rw [bytesAt_true, bytesAt_false, bytesAt_false]; sep_ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf ⟨hlen_sf, htr_sf⟩ hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro evs_hkdf
  have hpure :
      ((stackAt sp_call spqrSendCalleeStack ∗
        (vecU8 A.repAlloc outVec (HkdfFn salt ikm info 32) ∗
          (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗
          (⌜HkdfToVecEnv 32 evs_hkdf⌝ ∗ A.pool lim (M.stepEvents evs_hkdf st) sf))) ∗ Frame) =
      ⌜HkdfToVecEnv 32 evs_hkdf⌝ ∗
        ((vecU8 A.repAlloc outVec (HkdfFn salt ikm info 32) ∗
          (saltA ↦ᵣ salt) ∗ (ikmA ↦ₛ ikm) ∗ (infoA ↦ₛ info) ∗
          A.pool lim (M.stepEvents evs_hkdf st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by sep_ac_rfl
  rw [hpure]
  refine SepWP.pure_elim fun hevs_hkdf => ?_
  rw [show evs_hkdf = rustAllocEvents 32 1 from hevs_hkdf]
  exact hnext sf hcrl_sf hlen_sf hpc_sf hrun_sf hsp_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs (htr_sf.trans htrace)

private theorem call_authUpdate_lscro {F : ShaCompress} {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl (authUpdateSpec F M A lim)))
    (selfA epoch kA : BitVec 64) (auth : Authenticator) (k : Bytes)
    (hroot_lt : auth.rootKey.length + k.length < 2 ^ 63)
    (st : M.σ)
    (hfit : FitsEnv M lim st (AuthUpdateLenEnv auth.rootKey.length k.length))
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = selfA) (hx1 : s.readReg64 .x1 = epoch)
    (hx2 : s.readReg64 .x2 = kA) (hx3 : s.readReg64 .x3 = BitVec.ofNat 64 k.length)
    (hsplit : P = (authenticatorAt A.repAlloc selfA auth ∗ (kA ↦ₛ k) ∗
      A.pool lim st s ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (evs : List AllocEvent),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      AuthUpdateLenEnv auth.rootKey.length k.length evs →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      calleeSavedVRegs sf = calleeSavedVRegs s → sf.trace = s0.trace →
      SepWP prog tgt sf
        ((authenticatorAt A.repAlloc selfA (auth.update F epoch k) ∗ (kA ↦ₛ k) ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp_call spqrSendCalleeStack) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  let xg : AuthUpdateGhost := { selfA := selfA, auth := auth, ep := epoch, kRO := false, kA := kA, k := k }
  refine call_lscro_calleeStack_evs_sepWP (x := (xg, st))
    sp_call authUpdateStackX (by decide)
    (T_pre := authenticatorAt A.repAlloc selfA auth ∗ (kA ↦ₛ k) ∗ A.pool lim st s)
    (T_post := fun evs sf => authenticatorAt A.repAlloc selfA (auth.update F epoch k) ∗
      (kA ↦ₛ k) ∗ A.pool lim (M.stepEvents evs st) sf)
    (F := Frame)
    (φ_pre := s.readReg64 .x0 = selfA ∧ s.readReg64 .x1 = epoch ∧
      s.readReg64 .x2 = kA ∧ s.readReg64 .x3 = BitVec.ofNat 64 k.length ∧
      auth.rootKey.length + k.length < 2 ^ 63 ∧
      FitsEnv M lim st (AuthUpdateEnv xg))
    (φ_post := fun evs sf => sf.trace = s.trace ∧ AuthUpdateEnv xg evs)
    hcall hcrl hpc hrun hsp hsp_align hlr
    (by dsimp only [authUpdateSpec, LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdateSpec,
          LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdateSpecAt, xg]
        rw [bytesAt_false]; sep_ac_rfl)
    ⟨hx0, hx1, hx2, hx3, hroot_lt, hfit⟩
    (by sep_ac_rfl) (fun _ _ => rfl) (fun _ => Entails.refl _)
    (by intro sf
        dsimp only [authUpdateSpec, LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdateSpec,
          LibsignalBinary.Proofs.SpqrV1.Auth.UpdateBudgetAux.authUpdateSpecAt, xg]
        rw [bytesAt_false]
        congr 1; funext evs; sep_ac_rfl) ?_
  intro sf evs hpc_sf hrun_sf hsp_sf ⟨htr_sf, hevs⟩ hcrl_sf
    hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs
  exact SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
    (hnext sf evs hcrl_sf hevs hpc_sf hrun_sf hsp_sf
      hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hvregs (htr_sf.trans htrace))

set_option maxHeartbeats 1600000 in
theorem step_headerReceived_1504_to_1680_sepWP_placed
    {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {tgt : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (hkdfToVecUnchecked F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ss_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (hdr : Header)
    (ct1 : List.Vector (BitVec 8) 960)
    (ss : List.Vector (BitVec 8) 32)
    (hroot_len : auth.rootKey.length + 32 < 2 ^ 63)
    (st : M.σ) (hfit : FitsEnv M lim st (HeaderReceived1bEnv auth.rootKey.length))
    {s0 s : State} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr)
    (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = hdr_cap)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      memRegion (sp + 32#64) 16 ∗ authInlineWordsAt g (sp + 4192#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 4704#64) ↦₈ 0#8) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 32 ∗ A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (ct1_ptr info_ptr secret_cap secret_ptr : BitVec 64)
      (evs : List AllocEvent),
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := auth.update F epoch secret
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceived1bEnv auth.rootKey.length evs →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      info_ptr ≠ 0 → (info_ptr == 0#64) = false →
      secret_ptr ≠ 0 → (secret_cap == 0#64) = false →
      32 ≤ secret_cap.toNat → secret_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 1680#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length → sf.readReg64 .x28 = info_ptr →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A.repAlloc (sp + 4192#64) auth' ∗ memRegion (sp + 4704#64) 961 ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hfit_pre : FitsEvents M lim st headerReceived1bPreEvents :=
    fitsEnv_headerReceived1bPre_iff.mp hfit.seq_left
  have ⟨hfit_960, hfit_41, hfit_hkdf32, hstep_pre⟩ := fitsEvents_headerReceived1bPreEvents_split hfit_pre
  let st1 := M.stepEvents (rustAllocEvents 960 1) st
  let st2 := M.stepEvents (rustAllocEvents 41 1) st1
  let st3 := M.stepEvents (rustAllocEvents 32 1) st2
  have hfit_hkdf_env : FitsEnv M lim st2 (HkdfToVecEnv 32) := FitsEnv.eq_iff.mpr hfit_hkdf32
  have hfit_upd_len : FitsEnv M lim st3 (AuthUpdateLenEnv auth.rootKey.length 32) := by
    dsimp only [st3, st2, st1]
    rw [← hstep_pre]
    exact hfit.seq_right (rfl : HeaderReceived1bPreEnv headerReceived1bPreEvents)
  have hshim := spqrSend_shim_ok_placed hA
  have halloc := spqrSend_allocNoOom_ok_placed hA
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
  have hhkdf_call : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 378) (withLsCodeRoLoaded lsmpl (hkdfToVecSpqrSpec M A lim (hkdfToVecUnchecked F))) := hhkdf
  have hupd_call : subroutine_ok ((blkPC_427).rebase (blkPl_427).base (Rust.withPanics ext))
      (lsmpl.base 341) (withLsCodeRoLoaded lsmpl (authUpdateSpec F M A lim)) := hupd
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hshim halloc hmemcpy hnext ⊢
  subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx27
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv
  rw [memRegion_32_16_eq_words2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 2 (apply SepWP.exists_elim; intro _)
  wp_steps_427 (lsρ spqrRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_sh1
  refine call_shim_lscro hshim st (s0 := s0) (sp_call := sp) hinv_sh1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
    fun sh1 hinv_sh1' hpc_sh1 hrun_sh1 hsp_sh1 hcs_sh1 htr_sh1 => ?_
  rcases hcs_sh1 with ⟨hx19_s1, hx20_s1, hx21_s1, hx22_s1, hx23_s1, hx24_s1, hx25_s1, hx26_s1, hx27_s1, hx28_s1, _, hvregs_s1⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh1 hx19_s1 hx20_s1 hx21_s1 hx22_s1 hx23_s1 hx24_s1 hx25_s1 hx26_s1 hx27_s1 hx28_s1 hvregs_s1
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocSym) hinv_sh1'
  wp_steps_427 (lsρ spqrRustAllocSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_al1
  refine call_allocNoOom_lscro halloc 960 st ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_960
    (s0 := s0) (ret_pc := (blkPl_427).base + 1524#64) (sp_call := sp) hinv_al1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hvregs_1⟩
  simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hvregs_1
  apply of_sepWP_lscro_plain (mid := lsρ "memcpy") hinv_ok1
  have hct1_mem : memRegion (sf1.readReg64 (Reg.gpr 0#5)) 960 =
      memRegion (sf1.readReg64 (Reg.gpr 0#5)) ct1.toList.length := by rw [hct1_len]
  wp_conv_pre => rw [hct1_mem, ← sp_add_4704_orr_1_eq hsp_align]
  wp_steps_427 (lsρ "memcpy")
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_mc
  refine call_memcpy_lscro hmemcpy (sf1.readReg64 (Reg.gpr 0#5)) ((sp + 4704#64) ||| 1#64)
    ct1.toList st1 (s0 := s0) (sp_call := sp) hinv_mc
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by simp only [Reg.x2, hct1_len, arm64_norm, *]) (by sep_focus)
    fun smc hinv_smc hpc_smc hrun_smc hsp_smc hcs_smc htr_smc => ?_
  rcases hcs_smc with ⟨hx19_mc, hx20_mc, hx21_mc, hx22_mc, hx23_mc, hx24_mc, hx25_mc, hx26_mc, hx27_mc, hx28_mc, _, hvregs_mc⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_smc hx19_mc hx20_mc hx21_mc hx22_mc hx23_mc hx24_mc hx25_mc hx26_mc hx27_mc hx28_mc hvregs_mc
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustNoAllocShimSym) hinv_smc
  wp_conv_pre => rw [sp_add_4704_orr_1_eq hsp_align]
  refine SepWP.fold (pointsTo8_and_ct1_entails_memRegion_961 sp 0#8 ct1) (by sep_focus) ?_
  wp_steps_427 (lsρ spqrRustNoAllocShimSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_sh2
  refine call_shim_lscro hshim st1 (s0 := s0) (sp_call := sp) hinv_sh2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align rfl
    (by simp only [wp_norm, arm64_norm, *]) (by sep_focus)
    fun sh2 hinv_sh2' hpc_sh2 hrun_sh2 hsp_sh2 hcs_sh2 htr_sh2 => ?_
  rcases hcs_sh2 with ⟨hx19_s2, hx20_s2, hx21_s2, hx22_s2, hx23_s2, hx24_s2, hx25_s2, hx26_s2, hx27_s2, hx28_s2, _, hvregs_s2⟩
  simp only [Reg.lr, BitVec.add_assoc, wp_norm, arm64_norm, *] at hpc_sh2 hx19_s2 hx20_s2 hx21_s2 hx22_s2 hx23_s2 hx24_s2 hx25_s2 hx26_s2 hx27_s2 hx28_s2 hvregs_s2
  apply of_sepWP_lscro_plain (mid := lsρ spqrRustAllocSym) hinv_sh2'
  wp_steps_427 (lsρ spqrRustAllocSym)
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv_al2
  refine call_allocNoOom_lscro halloc 41 st1 ⟨⟨by decide, ⟨0, rfl⟩, by decide⟩, by decide⟩ hfit_41
    (s0 := s0) (ret_pc := (blkPl_427).base + 1572#64) (sp_call := sp) hinv_al2
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, _, hvregs_2⟩
  simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hvregs_2
  apply sepWP_intro_rodata (rodata_sckaKeyInfoPrefix_placed hinv_ok2.2)
  apply sepWP_intro_rodata (rodata_zeros32_send_placed hinv_ok2.2)
  apply of_sepWP_lscro_plain (mid := lsmpl.base 378) hinv_ok2
  rw [sckaKeyInfoPrefix_ro_split (lsρ "libsignal_cli_ratchet:.rodata..Lanon.29"),
      memRegion_41_eq_infoSlots (sf2.readReg64 (Reg.gpr 0#5)),
      memRegion_32_split_24_8 (sp + 7536#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 6 (apply SepWP.exists_elim; intro _)
  wp_conv_pre => simp only [BitVec.add_assoc, arm64_norm]
  wp_steps_427 ((blkPl_427).base + 1576#64)
  apply CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced.blkPC_427_pairStep_0x628
    (blkPl_427).base _ rfl (by wp_norm_lhs) (by wp_norm_lhs)
  wp_conv_pre =>
    rw [← LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64 (A := A) lim _ _ (Reg.gpr 9#5)
          (blkPl_427.ρ "libsignal_cli_ratchet:.rodata..Lanon.29"),
        ← LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC (A := A) lim _ _
          (blkPl_427.base + 1584#64)]
  wp_steps_427 ((blkPl_427).base + 1624#64)
  apply CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced.blkPC_427_pairStep_0x658
    (blkPl_427).base _ rfl (by wp_norm_lhs) (by wp_norm_lhs)
  wp_conv_pre =>
    rw [← LibsignalBinary.Heap.RustCliAllocBudget.pool_writeReg64 (A := A) lim _ _ (Reg.gpr 0#5)
          (blkPl_427.ρ "libsignal_cli_ratchet:.rodata.cst32+0x0"),
        ← LibsignalBinary.Heap.RustCliAllocBudget.pool_setPC (A := A) lim _ _
          (blkPl_427.base + 1632#64)]
  wp_steps_427 (lsmpl.base 378)
  refine SepWP.fold (infoSlots_entails_pointsToBytes (sf2.readReg64 (Reg.gpr 0#5)) epoch)
    (by sep_focus) ?_
  refine finish_sepWP_lscro_drop_ro_plain (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (Ro := ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29") ↦₆₄ᵣ sckaInfoW0) ∗
           ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 8#64) ↦₆₄ᵣ sckaInfoW1) ∗
           ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 16#64) ↦₆₄ᵣ sckaInfoW2) ∗
           ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 24#64) ↦₆₄ᵣ sckaInfoW3) ∗
           ((lsρ "libsignal_cli_ratchet:.rodata..Lanon.29" + 32#64) ↦₈ᵣ 0x79#8))
    (P' := _ ∗ (((lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8) ∗
      ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A.repAlloc g auth ∗
      memRegion (sp + 4704#64) 961 ∗
      A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
      A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗
      ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (sckaKeyInfoPrefix ++ epochBeBytes epoch)) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 24 ∗ memRegion (sp + 7560#64) 8 ∗
      stackAt sp spqrSendCalleeStack ∗ Frame))
    (fun hinv3 => ?_) (Entails.of_eq (by sep_ac_rfl))
  have hpre_len : sckaKeyInfoPrefix.length = 33 := rfl
  have hinfo_len : (sckaKeyInfoPrefix ++ epochBeBytes epoch).length = 41 := by
    rw [List.length_append, hpre_len, epochBeBytes_length]
  let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
  let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
  refine call_hkdfToVec32_lscro hhkdf_call
    (sp + 7536#64) (lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ss_ptr (sf2.readReg64 (Reg.gpr 0#5))
    (List.replicate 32 0#8) ss.toList info st2 hfit_hkdf_env
    (by simp) (by rw [hss_len]; decide) (by dsimp only [info]; rw [hinfo_len]; decide)
    (by dsimp only [info]; rw [hinfo_len]; decide)
    (s0 := s0) (ret_pc := (blkPl_427).base + 1656#64) (sp_call := sp) hinv3
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x8, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, List.length_replicate, arm64_norm, *])
    (by simp only [Reg.x2, arm64_norm, *]) (by rw [hss_len]; simp only [Reg.x3, arm64_norm, *])
    (by simp only [Reg.x4, arm64_norm, *]) (by dsimp only [info]; rw [hinfo_len]; simp only [Reg.x5, arm64_norm, *])
    (by simp only [Reg.x6, arm64_norm, *]) (by sep_focus)
    fun sm1 hinv_sm1 hsec_len hpc_sm1 hrun_sm1 hsp_sm1
      hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1 htr_sm1 => ?_
  simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    wp_norm, arm64_norm, *] at hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
  apply of_sepWP_lscro_plain (mid := lsmpl.base 341) hinv_sm1
  refine SepWP.fold (vecU8_len32_expose_7536 (A := A.repAlloc) sp secret hsec_len) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro secret_cap
  apply SepWP.exists_elim; intro secret_ptr
  rw [sepConj_assoc]
  refine SepWP.pure_elim fun ⟨hsec_cap_ge, hsec_cap_lt, hsec_ptr_ne, hsec_cap_b⟩ => ?_
  refine SepWP.fold (fold_authenticatorAt_of_inline_local A.repAlloc g (sp + 4192#64) auth)
    (by sep_focus) ?_
  wp_steps_427 (lsmpl.base 341)
  refine finish_sepWP_lscro_drop_ro_plain (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (Ro := (lsρ "libsignal_cli_ratchet:.rodata.cst32+0x0") ↦ᵣ List.replicate 32 0#8)
    (P' := _ ∗ (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
      authenticatorAt A.repAlloc (sp + 4192#64) auth ∗ memRegion (sp + 4704#64) 961 ∗
      A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
      A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
      A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
      memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
      memRegion (sp + 7560#64) 8 ∗ stackAt sp spqrSendCalleeStack ∗ Frame))
    (fun hinv4 => ?_) (Entails.of_eq (by sep_ac_rfl))
  have hroot_sec_lt : auth.rootKey.length + secret.length < 2 ^ 63 := by rw [hsec_len]; exact hroot_len
  have hfit_upd_sec : FitsEnv M lim st3 (AuthUpdateLenEnv auth.rootKey.length secret.length) := by
    rw [hsec_len]; exact hfit_upd_len
  refine call_authUpdate_lscro hupd_call (sp + 4192#64) epoch secret_ptr auth secret
    hroot_sec_lt st3 hfit_upd_sec
    (s0 := s0) (ret_pc := (blkPl_427).base + 1680#64) (sp_call := sp) hinv4
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by simp only [Reg.x2, arm64_norm, *]) (by rw [hsec_len]; simp only [Reg.x3, arm64_norm, *])
    (by sep_focus)
    fun sm2 evs_upd hinv_sm2 hevs_upd hpc_sm2 hrun_sm2 hsp_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2 htr_sm2 => ?_
  simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
    wp_norm, arm64_norm, *] at hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
  have hevs_upd32 : AuthUpdateLenEnv auth.rootKey.length 32 evs_upd := by
    rwa [hsec_len] at hevs_upd
  have hevs_all : HeaderReceived1bEnv auth.rootKey.length (headerReceived1bPreEvents ++ evs_upd) :=
    SeqEnv.append rfl hevs_upd32
  have hstep_all :
      M.stepEvents evs_upd st3 = M.stepEvents (headerReceived1bPreEvents ++ evs_upd) st := by
    dsimp only [st3, st2, st1]
    rw [M.stepEvents_append, hstep_pre]
  rw [hstep_all]
  apply of_sepWP_lscro_plain (mid := (blkPl_427).base + 1680#64) hinv_sm2
  refine finish_sepWP_lscro_plain hpc_sm2 hrun_sm2
    (fun hinv5 => hnext sm2 (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5))
      secret_cap secret_ptr (headerReceived1bPreEvents ++ evs_upd)
      hinv5 hevs_all hne0_1 h0b_1 hne0_2 h0b_2 hsec_ptr_ne hsec_cap_b hsec_cap_ge hsec_cap_lt
      hpc_sm2 hrun_sm2 hsp_sm2
      hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 htr_sm2
      (by simp only [wp_norm, arm64_norm, *]))
    (Entails.of_eq (by sep_ac_rfl))

/-- Panic-aware (`SepWPp`) wrapper for `step_headerReceived_1504_to_1680_sepWP_placed`,
    generalized over arbitrary `post` and `Qp`. -/
theorem step_headerReceived_1504_to_1680_placed
    {F : ShaCompress} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hhkdf : HkdfToVecPlacedOkX M A lim (hkdfToVecUnchecked F) ext)
    (hupd : AuthUpdatePlacedOkX F M A lim ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ss_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (hdr : Header)
    (ct1 : List.Vector (BitVec 8) 960)
    (ss : List.Vector (BitVec 8) 32)
    (hroot_len : auth.rootKey.length + 32 < 2 ^ 63)
    (st : M.σ) (hfit : FitsEnv M lim st (HeaderReceived1bEnv auth.rootKey.length))
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp} {post Qp : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 1504#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr)
    (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = hdr_cap)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      memRegion (sp + 32#64) 16 ∗ authInlineWordsAt g (sp + 4192#64) auth ∗
      authHeapBufs A.repAlloc g auth ∗
      ((sp + 4704#64) ↦₈ 0#8) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 32 ∗ A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (ct1_ptr info_ptr secret_cap secret_ptr : BitVec 64)
      (evs : List AllocEvent),
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := auth.update F epoch secret
      LibsignalCodeRoLoaded lsmpl sf.mem →
      HeaderReceived1bEnv auth.rootKey.length evs →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false →
      info_ptr ≠ 0 → (info_ptr == 0#64) = false →
      secret_ptr ≠ 0 → (secret_cap == 0#64) = false →
      32 ≤ secret_cap.toNat → secret_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 1680#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length → sf.readReg64 .x28 = info_ptr →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A.repAlloc (sp + 4192#64) auth' ∗ memRegion (sp + 4704#64) 961 ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗
          A.pool lim (M.stepEvents evs st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 1680#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_headerReceived_1504_to_1680_sepWP_placed hA hhkdf hupd
    sp epoch hdr_cap hdr_ptr es_ptr ss_ptr g auth hdr ct1 ss hroot_len st hfit
    hinv hsp_align hpc hrun hsp hx20 hx21 hx22 hx24 hx25 hx26 hx27 htrace hP
    fun sf ct1_ptr info_ptr secret_cap secret_ptr evs hcrl_sf hevs
      hne1 h0b1 hne2 h0b2 hsec_ne hsec_b hsec_ge hsec_lt hpc_sf hrun_sf hsp_sf
      hx19 hx20' hx21' hx22' hx23 hx24' hx25' hx26' hx27' hx28 htr hvregs =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf ct1_ptr info_ptr secret_cap secret_ptr evs hcrl_sf hevs
          hne1 h0b1 hne2 h0b2 hsec_ne hsec_b hsec_ge hsec_lt hpc_sf hrun_sf hsp_sf
          hx19 hx20' hx21' hx22' hx23 hx24' hx25' hx26' hx27' hx28 htr hvregs

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1PlacedBudget
