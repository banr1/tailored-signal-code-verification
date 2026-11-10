/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
public import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib
meta import LibsignalBinary.Proofs.Common.SharedHelpers

/-!
# Entry-Precondition and `SubroutineOutcome` Pool Swaps for Blocks `85` and `111`

Establishes stripped/unstripped entry-precondition pool swaps and all four `(s0', uf')`
`SubroutineOutcome` back-transfer lemmas between `mallocngHookRustCliAllocBudget` and
`strippedMallocngBudget` for Block `85` (`tryFromPlacedSpec`) and Block `111` (`pksmSlotSpecPlaced`).
-/

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsSpecSwapRFd

public section

set_option autoImplicit false
set_option linter.dupNamespace false

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement LibsignalRoLoaded libsignalMutatedBlocks
   libsignalSessionLib lsmpl)
open CryptoVerification.E2E.Pqxdh.ResponderWire (preKeyTryFromStack)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalTripleRatchet
  (TryFromGhost logOff smallRootStack withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalTripleRatchet.Wire (tryFromPlacedImg)
open CryptoVerification.LibsignalTripleRatchetRepr (signalMessageResultAt)
open CryptoVerification.SignalSession.Cli.RunCompose (PksmGhost RunSem pksmResAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv MallocngCostModelIface MallocngCostModelSound)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
  (CodeBlocksPermRX mallocngHookBudgetPool mallocngHookRustCliAllocBudget)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
  (CodeBlocksPermStripped satisfies_mallocngPool_of_stripped satisfies_strippedPool_of_mallocng
   sc_mem sc_r64 sc_sp sc_tr stripCodecMem stripCodecPerm stripCodecS strippedMallocngBudget
   strippedMallocngBudget_repAlloc strippedMallocngPool)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.PksmTryFromPlacedBudget
  (pksmSlotSpecPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromBudgetAux
  (TryFromEnvGen tryFromPlacedSpecGen)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromPostBudget (TryFromPostEnv)
open LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromRootBudget (tryFromPlacedSpec)

/-! ## Section 1: `LibsignalCodeRoLoaded` Preservation & Unstripped Pool Identity -/

private theorem stripCodec_isLazyFree' (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).isLazyFree a = m.isLazyFree a := by
  dsimp only [stripCodecMem, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [stripCodecPerm]; split
    · rfl
    · split <;> rfl

private theorem libsignalCodeLoaded_stripCodec [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {m : Memory}
    (hkeep : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
      ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
        keep a = true)
    (hcl : LibsignalCodeLoaded lsmpl m) :
    LibsignalCodeLoaded lsmpl (stripCodecMem keep m) := by
  intro i hi hunmut X O svc
  have hprog := hcl i hi hunmut X O svc
  rw [Program.codeLoaded_iff] at hprog ⊢
  rcases hprog with ⟨hal, hnow, hbytes⟩
  refine ⟨hal, hnow, fun k hk => ?_⟩
  obtain ⟨hr8, hp, hlf⟩ := hbytes k hk
  have hbase_eq : (libsignalSessionLib.blockProgram lsmpl i X O svc).base = lsmpl.base i := rfl
  have hlen_le :
      (libsignalSessionLib.blockProgram lsmpl i X O svc).code.length ≤
        (libsignalSessionLib.blockLib i).text.code.length := by
    change ((libsignalSessionLib.blockLib i).text.patched
      (libsignalSessionLib.blockPlacement lsmpl i)).length ≤
      (libsignalSessionLib.blockLib i).text.code.length
    rw [Obj.CodeBlock.length_patched]
    omega
  have hk_lt_len : k < (libsignalSessionLib.blockLib i).text.code.length :=
    Nat.lt_of_lt_of_le hk hlen_le
  have hin : InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length
      ((libsignalSessionLib.blockProgram lsmpl i X O svc).base + BitVec.ofNat 64 k) := by
    rw [hbase_eq] at hnow ⊢
    unfold InRegion
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  have hka : keep ((libsignalSessionLib.blockProgram lsmpl i X O svc).base + BitVec.ofNat 64 k) = true :=
    hkeep i hi hunmut _ hin
  exact ⟨by rw [CodecCalleesFsPlacedBudgetFd.stripCodec_read8, hr8],
    by rw [CodecCalleesFsPlacedBudgetFd.stripCodec_perm_of_keep hka, hp],
    by rw [stripCodec_isLazyFree', hlf]⟩

private theorem libsignalRoLoaded_stripCodec [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {m : Memory} (hro : LibsignalRoLoaded lsmpl m) :
    LibsignalRoLoaded lsmpl (stripCodecMem keep m) := by
  intro d hd hdro k hk
  obtain ⟨hr8, hp, hlf⟩ := hro d hd hdro k hk
  refine ⟨by rw [CodecCalleesFsPlacedBudgetFd.stripCodec_read8, hr8], ?_,
    by rw [stripCodec_isLazyFree', hlf]⟩
  rw [CodecCalleesFsPlacedBudgetFd.stripCodec_perm, hp]
  cases keep (lsmpl.ρ d.sym + BitVec.ofNat 64 k) <;> rfl

private theorem trCodeRoLoaded_stripCodec [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {m : Memory}
    (hkeep : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
      ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
        keep a = true)
    (h : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl m) :
    CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl (stripCodecMem keep m) :=
  ⟨libsignalCodeLoaded_stripCodec hkeep h.1, libsignalRoLoaded_stripCodec keep h.2⟩

private theorem skCodeRoLoaded_stripCodec [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {m : Memory}
    (hkeep : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
      ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
        keep a = true)
    (h : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl m) :
    CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl (stripCodecMem keep m) :=
  ⟨libsignalCodeLoaded_stripCodec hkeep h.1, libsignalRoLoaded_stripCodec keep h.2⟩

private theorem strippedPool_eq_of_hOut {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    (strippedMallocngBudget keep M I hS γ mmpl tp brkStart).pool lim =
      (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart).pool lim := by
  funext st s
  change strippedMallocngPool keep M I γ mmpl tp brkStart lim st s =
    mallocngHookBudgetPool M I γ mmpl tp brkStart lim st s
  unfold strippedMallocngPool
  rcases hOut with henf | hk
  · simp [henf]
  · by_cases henf : lim.enforced = true
    · simp only [henf, ↓reduceIte]
      unfold mallocngHookBudgetPool
      have hcs_eq : CodeBlocksPermStripped keep mmpl s = CodeBlocksPermRX mmpl s := by
        apply propext
        constructor
        · intro hcs a ha
          have h := hcs a ha
          rw [hk a ha] at h
          exact h
        · intro hrx a ha
          rw [hk a ha]
          exact hrx a ha
      simp only [hcs_eq, henf]
    · simp [henf]

private theorem tryFromSpec_eq_of_hOut [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim) =
      withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim) := by
  unfold withLsCodeRoLoaded tryFromPlacedSpec tryFromPlacedSpecGen
  simp only [strippedPool_eq_of_hOut hOut, strippedMallocngBudget_repAlloc]

private theorem pksmSpec_eq_of_hOut [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true) :
    pksmSlotSpecPlaced M (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S =
      pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S := by
  unfold pksmSlotSpecPlaced CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded
  simp only [strippedPool_eq_of_hOut hOut, strippedMallocngBudget_repAlloc]

private theorem tryFrom_outcome_s0_strip [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {A : LibsignalBinary.Heap.RustCliAllocBudget M}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {R : SepProp} {s0 uf' : State} :
    SubroutineOutcome (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim))
        x R (stripCodecS keep s0) uf' =
      SubroutineOutcome (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim))
        x R s0 uf' := by
  rcases x with ⟨g, st⟩
  cases s0
  rfl

private theorem pksm_outcome_s0_strip [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {A : LibsignalBinary.Heap.RustCliAllocBudget M}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {R : SepProp} {s0 uf' : State} :
    SubroutineOutcome (pksmSlotSpecPlaced M A lim PksmEnv S)
        x R (stripCodecS keep s0) uf' =
      SubroutineOutcome (pksmSlotSpecPlaced M A lim PksmEnv S)
        x R s0 uf' := by
  rcases x with ⟨g, st⟩
  cases s0
  rfl

/-! ## Section 2: Block `85` (`withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A lim)`) -/

/-- Transfers the `tryFromPlacedSpec` precondition (Block `85`) from `s0` at
`mallocngHookRustCliAllocBudget` to `stripCodecS keep s0` at `strippedMallocngBudget`. -/
theorem tryFrom_pre_stripped [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {s0 : State} {R : SepProp}
    (hkeep : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
      ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
        keep a = true)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)).pre
          x s0 ∗ R) :
    (stripCodecS keep s0).mem ⊨
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)).pre
          x (stripCodecS keep s0) ∗ R := by
  rcases x with ⟨g, st⟩
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
  obtain ⟨hclro, hpre0⟩ := CryptoVerification.LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  have hclro' : CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl
      (stripCodecS keep s0).mem := by
    rw [sc_mem]; exact trCodeRoLoaded_stripCodec hkeep hclro
  let preRest : SepProp :=
    ⌜s0.readReg64 .x0 = g.bytesA ∧ (s0.readReg64 .x1).toNat = g.bytes.length ∧
      g.bytes.length < 2 ^ 32 ∧ s0.readReg64 .x8 = g.ret ∧
      FitsEnv M lim st (TryFromEnvGen (fun q => TryFromPostEnv q.bytes) g)⌝ ∗
      (g.bytesA ↦ₛ g.bytes) ∗ memRegion g.ret 120 ∗ logOff tryFromPlacedImg ∗
      stackAt s0.sp smallRootStack ∗ R
  have hEq0 : (tryFromPlacedSpec A0 lim).pre (g, st) s0 ∗ R =
      A0.pool lim st s0 ∗ preRest := by
    dsimp only [tryFromPlacedSpec, tryFromPlacedSpecGen, preRest]
    sep_ac_rfl
  have hSat1 : (stripCodecS keep s0).mem ⊨
      A1.pool lim st (stripCodecS keep s0) ∗ preRest :=
    satisfies_strippedPool_of_mallocng keep (hEq0 ▸ hpre0)
  have hSat1' : (stripCodecS keep s0).mem ⊨
      ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl
        (stripCodecS keep s0).mem⌝ ∗
        (A1.pool lim st (stripCodecS keep s0) ∗ preRest) := by
    rw [ProofLib.satisfies_pure_sepConj]; exact ⟨hclro', hSat1⟩
  have hEq1 : (withLsCodeRoLoaded lsmpl (tryFromPlacedSpec A1 lim)).pre (g, st)
      (stripCodecS keep s0) ∗ R =
      ⌜CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl
        (stripCodecS keep s0).mem⌝ ∗
        (A1.pool lim st (stripCodecS keep s0) ∗ preRest) := by
    dsimp only [withLsCodeRoLoaded, tryFromPlacedSpec, tryFromPlacedSpecGen, preRest]
    simp only [sc_r64, sc_sp]
    sep_ac_rfl
  exact hEq1.symm ▸ hSat1'

/-- Transfers the `tryFromPlacedSpec` precondition (Block `85`) on `s0` from
`mallocngHookRustCliAllocBudget` to `strippedMallocngBudget` under `hOut`. -/
theorem tryFrom_pre_unstripped [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {s0 : State} {R : SepProp}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hpre : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim)).pre
          x s0 ∗ R) :
    s0.mem ⊨
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim)).pre
          x s0 ∗ R := by
  rwa [tryFromSpec_eq_of_hOut hOut]

/-- Block `85` `SubroutineOutcome` back-transfer for `(s0, stripCodecS keep uf)`. -/
theorem tryFrom_outcome_of_unstripped_stripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hout : SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim))
      x R s0 (stripCodecS keep uf)) :
    SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
      x R s0 uf := by
  let _ := hkf
  rcases x with ⟨g, st⟩
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hret0 : Returned s0 uf := by cases uf; exact hret
    have hcc0 : CallingConventionPreserved s0 uf := by cases uf; exact hcc
    refine Or.inl ⟨hret0, hcc0, ?_⟩
    dsimp only [withLsCodeRoLoaded, tryFromPlacedSpec, tryFromPlacedSpecGen] at hpost ⊢
    rw [sc_tr, strippedMallocngBudget_repAlloc] at hpost
    simp only [sepExists_sepConj_right, sepExists_sepConj_left, satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hevs⟩ := hpost
    refine ⟨evs, ?_⟩
    let postRest : SepProp :=
      ⌜uf.trace = s0.trace⌝ ∗
        ⌜TryFromEnvGen (fun q => TryFromPostEnv q.bytes) g evs⌝ ∗
        signalMessageResultAt A0.repAlloc [] g.ret (SignalMessage.tryFrom protoSignalCodec g.bytes) ∗
        (g.bytesA ↦ₛ g.bytes) ∗ logOff tryFromPlacedImg ∗ stackAt s0.sp smallRootStack ∗ R
    have hEq1 :
        (⌜uf.trace = s0.trace⌝ ∗
          (⌜TryFromEnvGen (fun q => TryFromPostEnv q.bytes) g evs⌝ ∗
            signalMessageResultAt A0.repAlloc [] g.ret
              (SignalMessage.tryFrom protoSignalCodec g.bytes) ∗
            (g.bytesA ↦ₛ g.bytes) ∗ logOff tryFromPlacedImg ∗ stackAt s0.sp smallRootStack ∗
            A1.pool lim (M.stepEvents evs st) (stripCodecS keep uf))) ∗ R =
          A1.pool lim (M.stepEvents evs st) (stripCodecS keep uf) ∗ postRest := by
      dsimp only [postRest]
      sep_ac_rfl
    have hSat0 : uf.mem ⊨ A0.pool lim (M.stepEvents evs st) uf ∗ postRest :=
      satisfies_mallocngPool_of_stripped keep hrx_uf (hEq1 ▸ hevs)
    have hEq0 :
        (⌜uf.trace = s0.trace⌝ ∗
          (⌜TryFromEnvGen (fun q => TryFromPostEnv q.bytes) g evs⌝ ∗
            signalMessageResultAt A0.repAlloc [] g.ret
              (SignalMessage.tryFrom protoSignalCodec g.bytes) ∗
            (g.bytesA ↦ₛ g.bytes) ∗ logOff tryFromPlacedImg ∗ stackAt s0.sp smallRootStack ∗
            A0.pool lim (M.stepEvents evs st) uf)) ∗ R =
          A0.pool lim (M.stepEvents evs st) uf ∗ postRest := by
      dsimp only [postRest]
      sep_ac_rfl
    exact hEq0.symm ▸ hSat0
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Block `85` `SubroutineOutcome` back-transfer for `(stripCodecS keep s0, stripCodecS keep uf)`. -/
theorem tryFrom_outcome_of_stripped_stripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hout : SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim))
      x R (stripCodecS keep s0) (stripCodecS keep uf)) :
    SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
      x R s0 uf := by
  rw [tryFrom_outcome_s0_strip] at hout
  exact tryFrom_outcome_of_unstripped_stripped keep hrx_uf hkf hout

/-- Block `85` `SubroutineOutcome` back-transfer for `(s0, uf)` under `hOut`. -/
theorem tryFrom_outcome_of_unstripped_unstripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hout : SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim))
      x R s0 uf) :
    SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
      x R s0 uf := by
  let _ := hrx_uf
  let _ := hkf
  rwa [tryFromSpec_eq_of_hOut hOut] at hout

/-- Block `85` `SubroutineOutcome` back-transfer for `(stripCodecS keep s0, uf)` under `hOut`. -/
theorem tryFrom_outcome_of_stripped_unstripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {x : TryFromGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hout : SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim))
      x R (stripCodecS keep s0) uf) :
    SubroutineOutcome
      (withLsCodeRoLoaded lsmpl
        (tryFromPlacedSpec (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim))
      x R s0 uf := by
  rw [tryFrom_outcome_s0_strip] at hout
  exact tryFrom_outcome_of_unstripped_unstripped keep hrx_uf hkf hOut hout

/-! ## Section 3: Block `111` (`pksmSlotSpecPlaced M A lim PksmEnv S`) -/

/-- Transfers the `pksmSlotSpecPlaced` precondition (Block `111`) from `s0` at
`mallocngHookRustCliAllocBudget` to `stripCodecS keep s0` at `strippedMallocngBudget`. -/
theorem pksm_pre_stripped [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {s0 : State} {R : SepProp}
    (hkeep : ∀ i, i < 624 → (i ∈ libsignalMutatedBlocks) = false →
      ∀ a, InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a →
        keep a = true)
    (hpre : s0.mem ⊨
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S).pre
          x s0 ∗ R) :
    (stripCodecS keep s0).mem ⊨
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S).pre
          x (stripCodecS keep s0) ∗ R := by
  rcases x with ⟨g, st⟩
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
  obtain ⟨hclro, hpre0⟩ :=
    CryptoVerification.LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hpre
  have hclro' :
      CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl
        (stripCodecS keep s0).mem := by
    rw [sc_mem]; exact skCodeRoLoaded_stripCodec hkeep hclro
  let preRest : SepProp :=
    ⌜s0.readReg64 .x0 = g.ptr ∧ (s0.readReg64 .x1).toNat = g.bytes.length ∧
      g.bytes.length < 2 ^ 32 ∧ s0.readReg64 .x8 = g.ret ∧
      preKeyTryFromStack ≤ s0.sp.toNat ∧
      FitsEnv M lim st (PksmEnv g)⌝ ∗
      (g.ptr ↦ₛ g.bytes) ∗ memRegion g.ret 248 ∗ lsLogOff ∗
      stackAt s0.sp preKeyTryFromStack ∗ R
  have hEq0 :
      (⌜s0.readReg64 .x0 = g.ptr ∧ (s0.readReg64 .x1).toNat = g.bytes.length ∧
          g.bytes.length < 2 ^ 32 ∧ s0.readReg64 .x8 = g.ret ∧
          preKeyTryFromStack ≤ s0.sp.toNat ∧ FitsEnv M lim st (PksmEnv g)⌝ ∗
        (g.ptr ↦ₛ g.bytes) ∗ memRegion g.ret 248 ∗ lsLogOff ∗
        stackAt s0.sp preKeyTryFromStack ∗ A0.pool lim st s0) ∗ R =
      A0.pool lim st s0 ∗ preRest := by
    dsimp only [preRest]
    sep_ac_rfl
  have hSat1 : (stripCodecS keep s0).mem ⊨
      A1.pool lim st (stripCodecS keep s0) ∗ preRest :=
    satisfies_strippedPool_of_mallocng keep (hEq0 ▸ hpre0)
  have hSat1' : (stripCodecS keep s0).mem ⊨
      ⌜CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl
        (stripCodecS keep s0).mem⌝ ∗
        (A1.pool lim st (stripCodecS keep s0) ∗ preRest) := by
    rw [ProofLib.satisfies_pure_sepConj]; exact ⟨hclro', hSat1⟩
  have hEq1 : (pksmSlotSpecPlaced M A1 lim PksmEnv S).pre (g, st) (stripCodecS keep s0) ∗ R =
      ⌜CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl
        (stripCodecS keep s0).mem⌝ ∗
        (A1.pool lim st (stripCodecS keep s0) ∗ preRest) := by
    dsimp only [pksmSlotSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, preRest]
    simp only [sc_r64, sc_sp]
    sep_ac_rfl
  exact hEq1.symm ▸ hSat1'

/-- Transfers the `pksmSlotSpecPlaced` precondition (Block `111`) on `s0` from
`mallocngHookRustCliAllocBudget` to `strippedMallocngBudget` under `hOut`. -/
theorem pksm_pre_unstripped [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {s0 : State} {R : SepProp}
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hpre : s0.mem ⊨
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S).pre
          x s0 ∗ R) :
    s0.mem ⊨
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S).pre
          x s0 ∗ R := by
  rwa [pksmSpec_eq_of_hOut hOut]

/-- Block `111` `SubroutineOutcome` back-transfer for `(s0, stripCodecS keep uf)`. -/
theorem pksm_outcome_of_unstripped_stripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hout : SubroutineOutcome
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 (stripCodecS keep uf)) :
    SubroutineOutcome
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 uf := by
  let _ := hkf
  rcases x with ⟨g, st⟩
  let A0 := mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart
  let A1 := strippedMallocngBudget keep M I hS γ mmpl tp brkStart
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩
  · have hret0 : Returned s0 uf := by cases uf; exact hret
    have hcc0 : CallingConventionPreserved s0 uf := by cases uf; exact hcc
    refine Or.inl ⟨hret0, hcc0, ?_⟩
    dsimp only [pksmSlotSpecPlaced,
      CryptoVerification.LibsignalPublicApi.StoreKit.withLsCodeRoLoaded] at hpost ⊢
    simp only [sc_tr, strippedMallocngBudget_repAlloc, sepExists_sepConj_left,
      satisfies_sepExists] at hpost ⊢
    obtain ⟨evs, hevs⟩ := hpost
    refine ⟨evs, ?_⟩
    let postRest : SepProp :=
      ⌜uf.trace = s0.trace ∧ PksmEnv g evs⌝ ∗
        pksmResAt A0.repAlloc g.ret (S.pksmParse g.bytes) ∗ (g.ptr ↦ₛ g.bytes) ∗
        lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗ R
    have hEq1 :
        (⌜uf.trace = s0.trace ∧ PksmEnv g evs⌝ ∗
          pksmResAt A0.repAlloc g.ret (S.pksmParse g.bytes) ∗ (g.ptr ↦ₛ g.bytes) ∗
          lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
          A1.pool lim (M.stepEvents evs st) (stripCodecS keep uf)) ∗ R =
          A1.pool lim (M.stepEvents evs st) (stripCodecS keep uf) ∗ postRest := by
      dsimp only [postRest]
      sep_ac_rfl
    have hSat0 : uf.mem ⊨ A0.pool lim (M.stepEvents evs st) uf ∗ postRest :=
      satisfies_mallocngPool_of_stripped keep hrx_uf (hEq1 ▸ hevs)
    have hEq0 :
        (⌜uf.trace = s0.trace ∧ PksmEnv g evs⌝ ∗
          pksmResAt A0.repAlloc g.ret (S.pksmParse g.bytes) ∗ (g.ptr ↦ₛ g.bytes) ∗
          lsLogOff ∗ stackAt s0.sp preKeyTryFromStack ∗
          A0.pool lim (M.stepEvents evs st) uf) ∗ R =
          A0.pool lim (M.stepEvents evs st) uf ∗ postRest := by
      dsimp only [postRest]
      sep_ac_rfl
    exact hEq0.symm ▸ hSat0
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

/-- Block `111` `SubroutineOutcome` back-transfer for `(stripCodecS keep s0, stripCodecS keep uf)`. -/
theorem pksm_outcome_of_stripped_stripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hout : SubroutineOutcome
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R (stripCodecS keep s0) (stripCodecS keep uf)) :
    SubroutineOutcome
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 uf := by
  rw [pksm_outcome_s0_strip] at hout
  exact pksm_outcome_of_unstripped_stripped keep hrx_uf hkf hout

/-- Block `111` `SubroutineOutcome` back-transfer for `(s0, uf)` under `hOut`. -/
theorem pksm_outcome_of_unstripped_unstripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hout : SubroutineOutcome
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 uf) :
    SubroutineOutcome
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 uf := by
  let _ := hrx_uf
  let _ := hkf
  rwa [pksmSpec_eq_of_hOut hOut] at hout

/-- Block `111` `SubroutineOutcome` back-transfer for `(stripCodecS keep s0, uf)` under `hOut`. -/
theorem pksm_outcome_of_stripped_unstripped [LibsignalPlacement] (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mmpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {PksmEnv : PksmGhost → List AllocEvent → Prop} {S : RunSem}
    {x : PksmGhost × M.σ} {R : SepProp} {s0 uf : State}
    (hrx_uf : lim.enforced = true → CodeBlocksPermRX mmpl uf)
    (hkf : s0.mem.KeepsFrozen uf.mem)
    (hOut : lim.enforced = false ∨
      ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mmpl a).isSome = true → keep a = true)
    (hout : SubroutineOutcome
      (pksmSlotSpecPlaced M
        (strippedMallocngBudget keep M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R (stripCodecS keep s0) uf) :
    SubroutineOutcome
      (pksmSlotSpecPlaced M
        (mallocngHookRustCliAllocBudget M I hS γ mmpl tp brkStart) lim PksmEnv S)
      x R s0 uf := by
  rw [pksm_outcome_s0_strip] at hout
  exact pksm_outcome_of_unstripped_unstripped keep hrx_uf hkf hOut hout

end

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsSpecSwapRFd
