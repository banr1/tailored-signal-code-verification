/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Record.Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.SignedPreKeyStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentitySelfStoreKit
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Store-Kit Contracts

Layout-independent `[LibsignalPlacement]` poll output predicates, `.rodata` vtable slot bundles
under `LibsignalRoLoaded lsmpl`, and caller-block-polymorphic `subroutine_ok` bundles at
`b := 0#64` for `SessionStore`, `IdentityKeyStore`, `PreKeyStore`, `SignedPreKeyStore`,
`KyberPreKeyStore`, and `IdentitySelfStore`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.StoreKit

open Arm64 Arm64.Obj ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity

/-! ## 1. Frozen Code + `.rodata` Wrappers & Cross-Block Call Transfer -/

/-- Both unmutated code blocks (`LibsignalCodeLoaded`) and `.rodata` (`LibsignalRoLoaded`) are
    loaded in `m` (re-exported from `Record.LibsignalCodeRoLoaded`). -/
abbrev LibsignalCodeRoLoaded (pl : MultiPlacement) (m : Memory) : Prop :=
  CryptoVerification.LibsignalTripleRatchet.Record.LibsignalCodeRoLoaded pl m

/-- Add `⌜LibsignalCodeRoLoaded pl s0.mem⌝` to `spec`'s precondition. -/
abbrev withLsCodeRoLoaded {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded pl s0.mem⌝ }

/-- Wrap `spec` with `⌜LibsignalCodeRoLoaded pl ·.mem⌝` in both precondition and postcondition so
    `wp_apply` / `wp_call` automatically discharges `LibsignalCodeRoLoaded` before an indirect or
    cross-block call and restores `LibsignalCodeRoLoaded pl sf.mem` in the local context afterward. -/
abbrev withLsRoCl {α : Type} (pl : MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeRoLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜LibsignalCodeRoLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

theorem extract_withLsCodeRoLoaded {α : Type} {pl : MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsCodeRoLoaded pl spec).pre x s0 ∗ R) :
    LibsignalCodeRoLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsCodeRoLoaded] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem extract_withLsRoCl {α : Type} {pl : MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsRoCl pl spec).pre x s0 ∗ R) :
    LibsignalCodeRoLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsRoCl] at hpre
  rwa [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre

theorem subroutine_ok_withLsCodeRoLoaded_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => (extract_withLsCodeRoLoaded hp).2) (fun _ _ _ _ hq => hq)

theorem subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded {α : Type} {prog : Program}
    {entry : BitVec 64} {pl : MultiPlacement} {spec : Spec α}
    (h : subroutine_ok prog entry (withLsCodeLoaded pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := extract_withLsCodeRoLoaded hp
      dsimp only [withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Lift `subroutine_ok prog entry (withLsCodeRoLoaded pl spec)` to `withLsRoCl pl spec` using
    `Steps.keepsFrozen` and `LibsignalCodeRoLoaded.of_keepsFrozen`. -/
theorem subroutine_ok_rocl_of_withLsCodeRoLoaded {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (hcallee : subroutine_ok prog entry (withLsCodeRoLoaded pl spec)) :
    subroutine_ok prog entry (withLsRoCl pl spec) := by
  refine Arm64.subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl0, _⟩ := extract_withLsRoCl hpre
  obtain ⟨sf, hsteps, hout, -⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hL
  have hcrlf : LibsignalCodeRoLoaded pl sf.mem := hcrl0.of_keepsFrozen hsteps.keepsFrozen
  refine Arm64.reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrlf, hpost⟩
  · exact Or.inr hrest

theorem subroutine_ok_rocl_of_plain {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (hcallee : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withLsRoCl pl spec) :=
  subroutine_ok_rocl_of_withLsCodeRoLoaded (subroutine_ok_withLsCodeRoLoaded_of_plain hcallee)

theorem subroutine_ok_withLsCodeRoLoaded_of_rocl {α : Type} {prog : Program} {entry : BitVec 64}
    {pl : MultiPlacement} {spec : Spec α}
    (hcallee : subroutine_ok prog entry (withLsRoCl pl spec)) :
    subroutine_ok prog entry (withLsCodeRoLoaded pl spec) :=
  subroutine_ok_mono hcallee (fun _ _ _ hp => hp) (fun _ _ _ _ hq => by
    dsimp only [withLsRoCl] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2)

/-- Cross-block transfer from `calleeProg` (block `j`) to any `callerProg` (block `i`) carrying
    `withLsRoCl lsmpl spec`. -/
theorem ls_subroutine_ok_rocl_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeRoLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [hbj : LsBlockBound bj]
    (_hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcrl0, _⟩ := extract_withLsRoCl hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸
      hcrl0.1 j (Nat.lt_of_lt_of_le hj hbj.le_blocks) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hcrlf : LibsignalCodeRoLoaded lsmpl sf.mem := hcrl0.of_keepsFrozen hstepsQ.keepsFrozen
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  refine Arm64.reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsRoCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcrlf, hpost⟩
  · exact Or.inr hrest

theorem ls_subroutine_ok_rocl_of_cl [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl spec) :=
  ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee) hi hj hj_unmut

theorem ls_subroutine_ok_rocl_of_plain [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl spec) :=
  ls_subroutine_ok_rocl_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeRoLoaded_of_plain hcallee) hi hj hj_unmut

/-- Cross-block `futDropSpec` transfer across any two blocks `j` and `i`. -/
theorem ls_futDrop_ok_of_block [LibsignalPlacement]
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64}
    (hcallee : subroutine_ok calleeProg entry futDropSpec)
    {bi bj : Nat} [LsBlockBound bi] [LsBlockBound bj]
    (hi : i < bi := by decide) (hj : j < bj := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsRoCl lsmpl futDropSpec) :=
  ls_subroutine_ok_rocl_of_plain (callerProg := callerProg) hcallee hi hj hj_unmut

/-- Sequence two `SepWP` segments while threading `LibsignalCodeRoLoaded pl ·.mem` across stores. -/
theorem sepWP_seq_lscro {prog : Program} {mid tgt : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWP prog tgt sm Pm post)) :
    SepWP prog tgt s P post :=
  SepWP.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcrl h

/-- Sequence `SepWP` into `SepWPp` while threading `LibsignalCodeRoLoaded pl ·.mem` across stores. -/
theorem sepWPp_seq_lscro {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcrl h

/-- Add `FromRecordCallees.lsLogOff` (`lsLogFilterAddr ↦₆₄ 0#64`) to `spec`'s precondition and
    postcondition. -/
abbrev withLsLogOff [LibsignalPlacement] {α : Type} (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s => spec.pre x s ∗ FromRecordCallees.lsLogOff
    post := fun x s0 sf => spec.post x s0 sf ∗ FromRecordCallees.lsLogOff }

/-- Frame `FromRecordCallees.lsLogOff` onto a `subroutine_ok` contract whose `onPanic` absorbs it. -/
theorem subroutine_ok_withLsLogOff [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α}
    (h : subroutine_ok prog entry spec)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ FromRecordCallees.lsLogOff ⊢ spec.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog entry (withLsLogOff spec) := by
  refine Arm64.subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hsp => ?_
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (FromRecordCallees.lsLogOff ∗ R) := by
    rw [← sepConj_assoc]; exact hp
  refine (h.to_outcome x (FromRecordCallees.lsLogOff ∗ R) s0 hpc hrun hp' hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    show sf.mem ⊨ (spec.post x s0 sf ∗ FromRecordCallees.lsLogOff) ∗ R
    rw [sepConj_assoc]; exact hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    show sf.mem ⊨ spec.onPanic x s0 sf ∗ R
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

/-! ## 2. Layout-Independent Placed Poll Output Predicates -/

/-- Layout-independent `ApplicationCallbackError("store hook", Box<HookStoreError>)` payload tail:
    `strPtr` and `vt` are existentialized at the poll boundary, matching `apiErrAt A e (.store ())`. -/
def errTailPlacedAt (strPtr vt out : BitVec 64) : SepProp :=
  ((out + 0x10#64) ↦₆₄ 10#64) ∗ ((out + 0x18#64) ↦₆₄ 1#64) ∗
    ((out + 0x20#64) ↦₆₄ vt) ∗ (strPtr ↦ᵣ storeHookStr)

/-- Layout-independent 368-byte `Poll<Result<Option<SessionRecord>, SPE>>` written by `load_session`.
    Definitionally equal to `loadPollOutAtS` on `.ok (some r)` and `.ok none`. -/
def loadPollPlacedOutAtS (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc)
    (out : BitVec 64) :
    Except Unit (Option (SessionRecord (List (BitVec 8)))) → SepProp
  | .ok (some r) => ⌜Scope r⌝ ∗ ∃∗ g : RecordGhost, sessionRecordAt A out g r
  | .ok none => (out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (out + 8#64) 360
  | .error () =>
    ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
      (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₆₄ 0x800000000000001A#64) ∗
      ((out + 0x10#64) ↦₆₄ strPtr) ∗ ((out + 0x18#64) ↦₆₄ 10#64) ∗
      ((out + 0x20#64) ↦₆₄ 1#64) ∗ ((out + 0x28#64) ↦₆₄ vt) ∗
      (strPtr ↦ᵣ storeHookStr) ∗ memRegion (out + 0x30#64) 320

/-- Layout-independent 48-byte `Poll<Result<(), SPE>>` written by `store_session`.
    Definitionally equal to `storePollOutAt` on `.ok ()`. -/
def storePollPlacedOutAt (out : BitVec 64) : Except Unit Unit → SepProp
  | .ok () => (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ memRegion (out + 8#64) 40
  | .error () =>
    ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
      (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ strPtr) ∗
      errTailPlacedAt strPtr vt out ∗ memRegion (out + 0x28#64) 8

/-- Layout-independent 48-byte `Poll<Result<bool, SPE>>` written by `is_trusted_identity`.
    Definitionally equal to `trustPollOutAt` on `.ok t`. -/
def trustPollPlacedOutAt (out : BitVec 64) : Except Unit Bool → SepProp
  | .ok t =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗ ((out + 8#64) ↦₈ (if t then 1#8 else 0#8)) ∗
      memRegion (out + 9#64) 39
  | .error () =>
    ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
      (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ strPtr) ∗
      errTailPlacedAt strPtr vt out ∗ memRegion (out + 0x28#64) 8

/-- Layout-independent 48-byte `Poll<Result<IdentityChange, SPE>>` written by `save_identity`.
    Definitionally equal to `savePollOutAt` on `.ok c`. -/
def savePollPlacedOutAt (out : BitVec 64) : Except Unit IdentityChange → SepProp
  | .ok c =>
    (out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
      ((out + 8#64) ↦₃₂ (if c == .replacedExisting then 1#32 else 0#32)) ∗
      memRegion (out + 0xc#64) 36
  | .error () =>
    ∃∗ strPtr : BitVec 64, ∃∗ vt : BitVec 64,
      (out ↦₆₄ 0x800000000000001A#64) ∗ ((out + 8#64) ↦₆₄ strPtr) ∗
      errTailPlacedAt strPtr vt out ∗ memRegion (out + 0x28#64) 8

/-! ## 3. Generic Placed Poll Contracts (`b := 0#64`) -/

/-- Relocatable `load_session` poll spec parameterized by `kit : SessionStoreSpec A 0#64`
    (code/rodata loadedness is carried outside by `withLsRoCl lsmpl` in the kit bundle). -/
def kitLoadPollPlacedSpecS {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState) where
  pre := fun (x, self, st0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.addrOk x.addr.val⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 0#8 ∗ kit.storeAt self st0 ∗ memRegion x.out 368 ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s.sp kit.loadPollStack
  post := fun (x, self, st0) s0 sf =>
    ∃∗ ans : Except Unit (Option (SessionRecord (List (BitVec 8)))),
      ⌜kit.loadRel st0 x.addr.val ans ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.addr.val ans⌝ ∗
      kit.loadBoxAt x.fut self x.addrA 1#8 ∗ kit.storeAt self st0 ∗
      loadPollPlacedOutAtS Scope A x.out ans ∗
      protocolAddressAt A x.addr x.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kitLoadPollPlacedSpecSE {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (LoadPollCall × BitVec 64 × kit.StoreState) :=
  withEnvPre (kitLoadPollPlacedSpecS kit Scope encRecord) fun s => kit.envOk s.fs.files

/-- Relocatable `store_session` poll spec parameterized by `kit : SessionStoreSpec A 0#64`. -/
def kitStorePollPlacedSpec {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState) where
  pre := fun (x, self, st0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ kit.RecOk x.call.record ∧
      kit.addrOk x.call.addr.val⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 0#8 ∗
      kit.storeAt self st0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗
      A.pool ∗ stackAt s.sp kit.storePollStack
  post := fun (x, self, st0) s0 sf =>
    ∃∗ ans : Except Unit Unit,
      ⌜kit.storeRel st0 x.call.addr.val x.call.record ans ∧
        sf.trace = s0.trace ++ kit.storeEvs encRecord x.call.addr.val x.call.record ans⌝ ∗
      kit.storeBoxAt x.fut self x.call.addrA x.call.recA 1#8 ∗
      kit.storeAt self (kit.storeUpdate st0 x.call.addr.val x.call.record ans) ∗
      storePollPlacedOutAt x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      sessionRecordAt A x.call.recA x.call.g x.call.record ∗
      A.pool ∗ stackAt s0.sp kit.storePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kitStorePollPlacedSpecE {A : RustAlloc} (kit : SessionStoreSpec A 0#64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (StorePollCall × BitVec 64 × kit.StoreState) :=
  withEnvPre (kitStorePollPlacedSpec kit encRecord) fun s => kit.envOk s.fs.files

/-- Relocatable `is_trusted_identity` poll spec parameterized by `ikit : IdentityStoreSpec A 0#64`. -/
def kitTrustPollPlacedSpec {A : RustAlloc} (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState) where
  pre := fun (x, d, self, ist0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 0#8 (directionByte d) ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp ikit.trustPollStack
  post := fun (x, d, self, ist0) s0 sf =>
    ∃∗ ans : Except Unit Bool,
      ⌜ikit.trustRel ist0 x.call.addr.val x.call.key d ans ∧
        sf.trace = s0.trace ++ ikit.trustEvs x.call.addr.val x.call.key d ans⌝ ∗
      ikit.trustBoxAt x.fut self x.call.addrA x.call.keyA 1#8 (directionByte d) ∗
      ikit.identityAt self (ikit.trustUpdate ist0 x.call.addr.val x.call.key d ans) ∗
      trustPollPlacedOutAt x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp ikit.trustPollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kitTrustPollPlacedSpecE {A : RustAlloc} (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitTrustPollPlacedSpec ikit) fun s => ikit.envOk s.fs.files

abbrev kitTrustPollPlacedSpecI [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × Direction × BitVec 64 × ikit.IdState) :=
  withLsLogOff (kitTrustPollPlacedSpecE ikit)

/-- Relocatable `save_identity` poll spec parameterized by `ikit : IdentityStoreSpec A 0#64`. -/
def kitSavePollPlacedSpec {A : RustAlloc} (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState) where
  pre := fun (x, self, ist0) s =>
    ⌜s.readReg64 .x0 = x.fut ∧ s.readReg64 .x8 = x.out ∧ ikit.addrOk x.call.addr.val⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 0#8 ∗
      ikit.identityAt self ist0 ∗ memRegion x.out 48 ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s.sp ikit.savePollStack
  post := fun (x, self, ist0) s0 sf =>
    ∃∗ ans : Except Unit IdentityChange,
      ⌜ikit.saveRel ist0 x.call.addr.val x.call.key ans ∧
        sf.trace = s0.trace ++ ikit.saveEvs x.call.addr.val x.call.key ans⌝ ∗
      ikit.saveBoxAt x.fut self x.call.addrA x.call.keyA 1#8 ∗
      ikit.identityAt self (ikit.saveUpdate ist0 x.call.addr.val x.call.key ans) ∗
      savePollPlacedOutAt x.out ans ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      (x.call.keyA ↦ₛ x.call.key.publicKey.bytes.toList) ∗ A.pool ∗
      stackAt s0.sp ikit.savePollStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

abbrev kitSavePollPlacedSpecE {A : RustAlloc} (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState) :=
  withEnvPre (kitSavePollPlacedSpec ikit) fun s => ikit.envOk s.fs.files

abbrev kitSavePollPlacedSpecI [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) :
    Spec (IdentityPollCall × BitVec 64 × ikit.IdState) :=
  withLsLogOff (kitSavePollPlacedSpecE ikit)

abbrev kitKpPollPlacedSpecI [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelf.IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withLsLogOff (IdentitySelf.kitKpPollSpecE skit)

abbrev kitRegIdPollPlacedSpecI [LibsignalPlacement] {A : RustAlloc}
    {ikit : IdentityStoreSpec A 0#64} (skit : IdentitySelf.IdentitySelfStoreSpec ikit) :
    Spec (BitVec 64 × BitVec 64 × BitVec 64 × ikit.IdState) :=
  withLsLogOff (IdentitySelf.kitRegIdPollSpecE skit)

/-! ## 4. Read-Only `.rodata` Vtable Slot Bundles under `LibsignalRoLoaded lsmpl` -/

/-- Read-only `.rodata` vtable slots for `kit : SessionStoreSpec A 0#64` under `LibsignalRoLoaded lsmpl`.
    Target addresses are written `0#64 + kit.*Off` so they match `decLoadVtableAtV kit` and
    `decStoreVtableAtV kit` definitionally (`rfl`). -/
structure SessionOnlyVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) : Prop where
  loadSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.ss_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadShimOff)) ∗ P
  storeSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.ss_vt + 0x20#64) ↦₆₄ᵣ (0#64 + kit.storeShimOff)) ∗ P
  loadFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.loadFutVtOff) ↦₆₄ᵣ (0#64 + kit.loadFutDropOff)) ∗ P
  loadFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.loadFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.loadBoxSize) ∗ P
  loadFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.loadFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  loadFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.loadFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.loadPollOff)) ∗ P
  storeFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.storeFutVtOff) ↦₆₄ᵣ (0#64 + kit.storeFutDropOff)) ∗ P
  storeFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.storeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.storeBoxSize) ∗ P
  storeFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.storeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  storeFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.storeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.storePollOff)) ∗ P

/-- Read-only `.rodata` vtable slots for `ikit : IdentityStoreSpec A 0#64` under `LibsignalRoLoaded lsmpl`. -/
structure IdentityVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) : Prop where
  saveSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((ikit.id_vt + 0x28#64) ↦₆₄ᵣ (0#64 + ikit.saveShimOff)) ∗ P
  trustSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((ikit.id_vt + 0x30#64) ↦₆₄ᵣ (0#64 + ikit.trustShimOff)) ∗ P
  saveFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.saveFutVtOff) ↦₆₄ᵣ (0#64 + ikit.saveFutDropOff)) ∗ P
  saveFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.saveFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.saveBoxSize) ∗ P
  saveFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.saveFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  saveFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.saveFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.savePollOff)) ∗ P
  trustFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.trustFutVtOff) ↦₆₄ᵣ (0#64 + ikit.trustFutDropOff)) ∗ P
  trustFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.trustFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 ikit.trustBoxSize) ∗ P
  trustFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.trustFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  trustFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + ikit.trustFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + ikit.trustPollOff)) ∗ P

/-- Read-only `.rodata` vtable slots for `kit : PreKeyStoreSpec A 0#64` under `LibsignalRoLoaded lsmpl`. -/
structure PreKeyVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : PreKeyStoreSpec A 0#64) : Prop where
  getSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.pk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getShimOff)) ∗ P
  removeSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.pk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kit.removeShimOff)) ∗ P
  getFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff) ↦₆₄ᵣ (0#64 + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getPollOff)) ∗ P
  removeFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.removeFutVtOff) ↦₆₄ᵣ (0#64 + kit.removeFutDropOff)) ∗ P
  removeFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.removeFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.removeBoxSize) ∗ P
  removeFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.removeFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  removeFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.removeFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.removePollOff)) ∗ P

/-- Read-only `.rodata` vtable slots for `kit : SignedPreKeyStoreSpec A 0#64` under `LibsignalRoLoaded lsmpl`. -/
structure SignedPreKeyVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : SignedPreKeyStoreSpec A 0#64) : Prop where
  getSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.spk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getShimOff)) ∗ P
  getFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff) ↦₆₄ᵣ (0#64 + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getPollOff)) ∗ P

/-- Read-only `.rodata` vtable slots for `kit : KyberPreKeyStoreSpec A 0#64` under `LibsignalRoLoaded lsmpl`. -/
structure KyberPreKeyVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : KyberPreKeyStoreSpec A 0#64) : Prop where
  getSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.kpk_vt + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getShimOff)) ∗ P
  markSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((kit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kit.markShimOff)) ∗ P
  getFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff) ↦₆₄ᵣ (0#64 + kit.getFutDropOff)) ∗ P
  getFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.getBoxSize) ∗ P
  getFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  getFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.getFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.getPollOff)) ∗ P
  markFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.markFutVtOff) ↦₆₄ᵣ (0#64 + kit.markFutDropOff)) ∗ P
  markFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.markFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 kit.markBoxSize) ∗ P
  markFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.markFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  markFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + kit.markFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + kit.markPollOff)) ∗ P

/-- Read-only `.rodata` vtable slots for `skit : IdentitySelfStoreSpec ikit` under `LibsignalRoLoaded lsmpl`. -/
structure IdentitySelfVtablesPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (skit : IdentitySelf.IdentitySelfStoreSpec ikit) : Prop where
  kpSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((ikit.id_vt + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpShimOff)) ∗ P
  regIdSlot : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((ikit.id_vt + 0x20#64) ↦₆₄ᵣ (0#64 + skit.regIdShimOff)) ∗ P
  kpFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.kpFutVtOff) ↦₆₄ᵣ (0#64 + skit.kpFutDropOff)) ∗ P
  kpFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.kpFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.kpBoxSize) ∗ P
  kpFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.kpFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  kpFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.kpFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.kpPollOff)) ∗ P
  regIdFutDrop : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.regIdFutVtOff) ↦₆₄ᵣ (0#64 + skit.regIdFutDropOff)) ∗ P
  regIdFutSize : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.regIdFutVtOff + 8#64) ↦₆₄ᵣ BitVec.ofNat 64 skit.regIdBoxSize) ∗ P
  regIdFutAlign : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.regIdFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P
  regIdFutPoll : ∀ {m : Memory} {P : SepProp}, LibsignalRoLoaded lsmpl m → (m ⊨ P) →
    m ⊨ ((0#64 + skit.regIdFutVtOff + 0x18#64) ↦₆₄ᵣ (0#64 + skit.regIdPollOff)) ∗ P

/-! ## 5. Caller-Block-Polymorphic `subroutine_ok` Bundles (`b := 0#64`) -/

/-- Relocatable `SessionOnlyKitOkSE`: provides `subroutine_ok` on any `callerProg` with
    `[IsLsBlockProg callerProg callerBlk H]` (`callerBlk < 619`), carrying `withLsRoCl lsmpl`
    across the shims and polls. -/
structure SessionOnlyKitPlacedOkSE [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  loadShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadShimOff) (withLsRoCl lsmpl (kitLoadShimSpec kit))
  loadPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadPollOff)
      (withLsRoCl lsmpl (kitLoadPollPlacedSpecSE kit Scope encRecord))
  loadFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.loadFutDropOff) (withLsRoCl lsmpl futDropSpec)
  storeShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeShimOff) (withLsRoCl lsmpl (kitStoreShimSpec kit))
  storePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storePollOff)
      (withLsRoCl lsmpl (kitStorePollPlacedSpecE kit encRecord))
  storeFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.storeFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Relocatable `IdentityStoreKitOkI` (`trust` and `save` shims, polls with `withLsLogOff`, and
    future drops). -/
structure IdentityStoreKitPlacedOkI [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  trustShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustShimOff) (withLsRoCl lsmpl (kitTrustShimSpec ikit))
  trustPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustPollOff)
      (withLsRoCl lsmpl (kitTrustPollPlacedSpecI ikit))
  trustFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.trustFutDropOff) (withLsRoCl lsmpl futDropSpec)
  saveShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveShimOff) (withLsRoCl lsmpl (kitSaveShimSpec ikit))
  savePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.savePollOff)
      (withLsRoCl lsmpl (kitSavePollPlacedSpecI ikit))
  saveFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + ikit.saveFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Relocatable `PreKeyStoreKitOkImg` (`get_pre_key` and `remove_pre_key`). -/
structure PreKeyStoreKitPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : PreKeyStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff) (withLsRoCl lsmpl (kitPreKeyGetShimSpec kit))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff) (withLsRoCl lsmpl (kitPreKeyGetPollSpecE kit))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff) (withLsRoCl lsmpl futDropSpec)
  removeShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removeShimOff)
      (withLsRoCl lsmpl (kitPreKeyRemoveShimSpec kit))
  removePoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removePollOff)
      (withLsRoCl lsmpl (kitPreKeyRemovePollSpecE kit))
  removeFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.removeFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Relocatable `SignedPreKeyStoreKitOkImg` (`get_signed_pre_key`). -/
structure SignedPreKeyStoreKitPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : SignedPreKeyStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff) (withLsRoCl lsmpl (kitSpkGetShimSpec kit))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff) (withLsRoCl lsmpl (kitSpkGetPollSpecE kit))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Relocatable `KyberPreKeyStoreKitOkImg` (`get_kyber_pre_key` and `mark_kyber_pre_key_used`). -/
structure KyberPreKeyStoreKitPlacedOk [LibsignalPlacement] {A : RustAlloc}
    (kit : KyberPreKeyStoreSpec A 0#64) (H : LibsignalHooks) : Prop where
  getShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getShimOff) (withLsRoCl lsmpl (kitKpkGetShimSpec kit))
  getPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getPollOff) (withLsRoCl lsmpl (kitKpkGetPollSpecE kit))
  getFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.getFutDropOff) (withLsRoCl lsmpl futDropSpec)
  markShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markShimOff) (withLsRoCl lsmpl (kitKpkMarkShimSpec kit))
  markPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markPollOff) (withLsRoCl lsmpl (kitKpkMarkPollSpecE kit))
  markFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + kit.markFutDropOff) (withLsRoCl lsmpl futDropSpec)

/-- Relocatable `IdentitySelfStoreKitOkI` (`get_identity_key_pair` and `get_local_registration_id`). -/
structure IdentitySelfStoreKitPlacedOkI [LibsignalPlacement] {A : RustAlloc}
    (ikit : IdentityStoreSpec A 0#64)
    (skit : IdentitySelf.IdentitySelfStoreSpec ikit) (H : LibsignalHooks) : Prop where
  kpShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpShimOff)
      (withLsRoCl lsmpl (IdentitySelf.kitKpShimSpec skit))
  kpPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpPollOff)
      (withLsRoCl lsmpl (kitKpPollPlacedSpecI skit))
  kpFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.kpFutDropOff) (withLsRoCl lsmpl futDropSpec)
  regIdShim : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdShimOff)
      (withLsRoCl lsmpl (IdentitySelf.kitRegIdShimSpec skit))
  regIdPoll : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdPollOff)
      (withLsRoCl lsmpl (kitRegIdPollPlacedSpecI skit))
  regIdFutDrop : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
    callerBlk < 619 →
    subroutine_ok callerProg (0#64 + skit.regIdFutDropOff) (withLsRoCl lsmpl futDropSpec)

end CryptoVerification.LibsignalPublicApi.StoreKit
