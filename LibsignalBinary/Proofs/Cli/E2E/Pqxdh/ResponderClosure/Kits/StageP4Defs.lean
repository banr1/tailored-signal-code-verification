/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKit
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Stage P4 Stack Budgets, Poll Layouts, and Callee Helpers

Shared stack budgets (`saveIdCallStack`, `markKyberCallStack`, `removePreKeyCallStack`,
`storeSessionCallStack`, `stageP4CallStack`), poll/staging slot cell bijections (`pollCellsAt`,
`stagingCellsAt`), and deallocation-only contract bundle `StageP4Alloc` for Stage P4 (`+0x34dc → exit`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

set_option maxRecDepth 200000

/-! ## Stack budgets and splitting lemmas -/

/-- Stack budget for error-unwind tails in Stage P4 (`__rust_dealloc` and
    `drop_glue::<SessionStructure>`; `futDropSpec` uses `emp` stack). -/
def stageP4ErrUnwindStack : Nat :=
  max allocHookStack dropSessionStructureLocal2Stack

/-- Stack budget for Substage `P4.1` (`save_identity` shim, poll, future drop, dealloc, and
    error unwind). -/
def saveIdCallStack {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b) : Nat :=
  max ikit.saveShimStack (max ikit.savePollStack stageP4ErrUnwindStack)

/-- Stack budget for Substage `P4.2` (`mark_kyber_pre_key_used` shim, poll, future drop,
deallocation, and refusal error unwind). -/
def markKyberCallStack {A : RustAlloc} {b : BitVec 64} (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max kpkKit.markShimStack (max kpkKit.markPollStack stageP4ErrUnwindStack)

/-- Stack budget for Substage `P4.3` (`remove_pre_key` shim, poll, future drop, dealloc, and
    error unwind). -/
def removePreKeyCallStack {A : RustAlloc} {b : BitVec 64} (pkKit : PreKeyStoreSpec A b) : Nat :=
  max pkKit.removeShimStack (max pkKit.removePollStack stageP4ErrUnwindStack)

/-- Stack budget for Substage `P4.4` (`store_session` shim, poll, future drop, dealloc,
    `drop_glue::<SessionStructure>`, and error unwind). -/
def storeSessionCallStack {A : RustAlloc} {b : BitVec 64} (kit : SessionStoreSpec A b) : Nat :=
  max kit.storeShimStack (max kit.storePollStack stageP4ErrUnwindStack)

/-- Unified stack budget for Stage P4 across `save_identity`, `mark_kyber_pre_key_used`,
    `remove_pre_key`, `store_session`, and all error-unwind tails. -/
def stageP4CallStack {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) : Nat :=
  max (saveIdCallStack ikit)
    (max (markKyberCallStack kpkKit)
      (max (removePreKeyCallStack pkKit) (storeSessionCallStack kit)))

theorem allocHookStack_le_errUnwind : allocHookStack ≤ stageP4ErrUnwindStack :=
  Nat.le_max_left _ _

theorem dropSS3Stack_le_errUnwind : dropSessionStructureLocal2Stack ≤ stageP4ErrUnwindStack :=
  Nat.le_max_right _ _

theorem stack_errUnwind_to_alloc (sp : BitVec 64) (hn : stageP4ErrUnwindStack ≤ 2 ^ 64) :
    stackAt sp stageP4ErrUnwindStack =
      memRegion (sp - BitVec.ofNat 64 stageP4ErrUnwindStack)
        (stageP4ErrUnwindStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_sub_eq sp stageP4ErrUnwindStack allocHookStack allocHookStack_le_errUnwind hn

theorem stack_errUnwind_to_dropSS3 (sp : BitVec 64) (hn : stageP4ErrUnwindStack ≤ 2 ^ 64) :
    stackAt sp stageP4ErrUnwindStack =
      memRegion (sp - BitVec.ofNat 64 stageP4ErrUnwindStack)
        (stageP4ErrUnwindStack - dropSessionStructureLocal2Stack) ∗
        stackAt sp dropSessionStructureLocal2Stack :=
  stackAt_sub_eq sp stageP4ErrUnwindStack dropSessionStructureLocal2Stack
    dropSS3Stack_le_errUnwind hn

theorem stack_saveId_to_shim {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : saveIdCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (saveIdCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (saveIdCallStack ikit))
        (saveIdCallStack ikit - ikit.saveShimStack) ∗
        stackAt sp ikit.saveShimStack :=
  stackAt_sub_eq sp (saveIdCallStack ikit) ikit.saveShimStack (Nat.le_max_left _ _) hn

theorem stack_saveId_to_poll {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : saveIdCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (saveIdCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (saveIdCallStack ikit))
        (saveIdCallStack ikit - ikit.savePollStack) ∗
        stackAt sp ikit.savePollStack :=
  stackAt_sub_eq sp (saveIdCallStack ikit) ikit.savePollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_saveId_to_errUnwind {A : RustAlloc} {b : BitVec 64} (ikit : IdentityStoreSpec A b)
    (sp : BitVec 64) (hn : saveIdCallStack ikit ≤ 2 ^ 64) :
    stackAt sp (saveIdCallStack ikit) =
      memRegion (sp - BitVec.ofNat 64 (saveIdCallStack ikit))
        (saveIdCallStack ikit - stageP4ErrUnwindStack) ∗
        stackAt sp stageP4ErrUnwindStack :=
  stackAt_sub_eq sp (saveIdCallStack ikit) stageP4ErrUnwindStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_markKyber_to_shim {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : markKyberCallStack kpkKit ≤ 2 ^ 64) :
    stackAt sp (markKyberCallStack kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (markKyberCallStack kpkKit))
        (markKyberCallStack kpkKit - kpkKit.markShimStack) ∗
        stackAt sp kpkKit.markShimStack :=
  stackAt_sub_eq sp (markKyberCallStack kpkKit) kpkKit.markShimStack (Nat.le_max_left _ _) hn

theorem stack_markKyber_to_poll {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : markKyberCallStack kpkKit ≤ 2 ^ 64) :
    stackAt sp (markKyberCallStack kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (markKyberCallStack kpkKit))
        (markKyberCallStack kpkKit - kpkKit.markPollStack) ∗
        stackAt sp kpkKit.markPollStack :=
  stackAt_sub_eq sp (markKyberCallStack kpkKit) kpkKit.markPollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_markKyber_to_errUnwind {A : RustAlloc} {b : BitVec 64}
    (kpkKit : KyberPreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : markKyberCallStack kpkKit ≤ 2 ^ 64) :
    stackAt sp (markKyberCallStack kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (markKyberCallStack kpkKit))
        (markKyberCallStack kpkKit - stageP4ErrUnwindStack) ∗
        stackAt sp stageP4ErrUnwindStack :=
  stackAt_sub_eq sp (markKyberCallStack kpkKit) stageP4ErrUnwindStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_removePreKey_to_shim {A : RustAlloc} {b : BitVec 64}
    (pkKit : PreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : removePreKeyCallStack pkKit ≤ 2 ^ 64) :
    stackAt sp (removePreKeyCallStack pkKit) =
      memRegion (sp - BitVec.ofNat 64 (removePreKeyCallStack pkKit))
        (removePreKeyCallStack pkKit - pkKit.removeShimStack) ∗
        stackAt sp pkKit.removeShimStack :=
  stackAt_sub_eq sp (removePreKeyCallStack pkKit) pkKit.removeShimStack (Nat.le_max_left _ _) hn

theorem stack_removePreKey_to_poll {A : RustAlloc} {b : BitVec 64}
    (pkKit : PreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : removePreKeyCallStack pkKit ≤ 2 ^ 64) :
    stackAt sp (removePreKeyCallStack pkKit) =
      memRegion (sp - BitVec.ofNat 64 (removePreKeyCallStack pkKit))
        (removePreKeyCallStack pkKit - pkKit.removePollStack) ∗
        stackAt sp pkKit.removePollStack :=
  stackAt_sub_eq sp (removePreKeyCallStack pkKit) pkKit.removePollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_removePreKey_to_errUnwind {A : RustAlloc} {b : BitVec 64}
    (pkKit : PreKeyStoreSpec A b) (sp : BitVec 64)
    (hn : removePreKeyCallStack pkKit ≤ 2 ^ 64) :
    stackAt sp (removePreKeyCallStack pkKit) =
      memRegion (sp - BitVec.ofNat 64 (removePreKeyCallStack pkKit))
        (removePreKeyCallStack pkKit - stageP4ErrUnwindStack) ∗
        stackAt sp stageP4ErrUnwindStack :=
  stackAt_sub_eq sp (removePreKeyCallStack pkKit) stageP4ErrUnwindStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem stack_storeSession_to_shim {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - kit.storeShimStack) ∗
        stackAt sp kit.storeShimStack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) kit.storeShimStack (Nat.le_max_left _ _) hn

theorem stack_storeSession_to_poll {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - kit.storePollStack) ∗
        stackAt sp kit.storePollStack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) kit.storePollStack
    (Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) hn

theorem stack_storeSession_to_errUnwind {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (sp : BitVec 64)
    (hn : storeSessionCallStack kit ≤ 2 ^ 64) :
    stackAt sp (storeSessionCallStack kit) =
      memRegion (sp - BitVec.ofNat 64 (storeSessionCallStack kit))
        (storeSessionCallStack kit - stageP4ErrUnwindStack) ∗
        stackAt sp stageP4ErrUnwindStack :=
  stackAt_sub_eq sp (storeSessionCallStack kit) stageP4ErrUnwindStack
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) hn

theorem saveIdStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    saveIdCallStack ikit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.le_max_left _ _

theorem markKyberStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    markKyberCallStack kpkKit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

theorem removePreKeyStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    removePreKeyCallStack pkKit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.le_trans (Nat.le_max_left _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem storeSessionStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    storeSessionCallStack kit ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.le_trans (Nat.le_max_right _ _)
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

theorem errUnwindStack_le_stageP4 {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b) :
    stageP4ErrUnwindStack ≤ stageP4CallStack kit ikit pkKit kpkKit :=
  Nat.le_trans
    (Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))
    (saveIdStack_le_stageP4 kit ikit pkKit kpkKit)

theorem stack_stageP4_to_saveId {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - saveIdCallStack ikit) ∗
        stackAt sp (saveIdCallStack ikit) :=
  stackAt_sub_eq sp _ _ (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hn

theorem stack_stageP4_to_markKyber {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - markKyberCallStack kpkKit) ∗
        stackAt sp (markKyberCallStack kpkKit) :=
  stackAt_sub_eq sp _ _ (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hn

theorem stack_stageP4_to_removePreKey {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - removePreKeyCallStack pkKit) ∗
        stackAt sp (removePreKeyCallStack pkKit) :=
  stackAt_sub_eq sp _ _ (removePreKeyStack_le_stageP4 kit ikit pkKit kpkKit) hn

theorem stack_stageP4_to_storeSession {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (sp : BitVec 64) (hn : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64) :
    stackAt sp (stageP4CallStack kit ikit pkKit kpkKit) =
      memRegion (sp - BitVec.ofNat 64 (stageP4CallStack kit ikit pkKit kpkKit))
        (stageP4CallStack kit ikit pkKit kpkKit - storeSessionCallStack kit) ∗
        stackAt sp (storeSessionCallStack kit) :=
  stackAt_sub_eq sp _ _ (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hn

/-! ## Callee contract abbreviation and `SepWPp` combinators -/

/-- `core::ptr::drop_glue::<SessionStructure> [local#5]` contract on `tripleRatchetProgAtExt`. -/
abbrev DropSessionStructure3OkExt (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
    (dropSessionStructureLocal2Spec A)

theorem allocFailedIn_of_trace_prefix {s0 s sf : State}
    (htr : s0.trace <+: s.trace) (ha : allocFailedIn s sf) :
    allocFailedIn s0 sf := by
  unfold allocFailedIn at ha ⊢
  obtain ⟨d, hd⟩ := htr
  rw [← hd, List.length_append, ← List.drop_drop] at ha
  exact List.mem_of_mem_drop ha

theorem allowPanic_oom_of_trace_prefix {s0 s sf : State} {F : SepProp}
    (htr : s0.trace <+: s.trace) :
    PanicOomProp s0 sf ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  intro R hm
  have himp : allocFailedIn s sf ∧ s.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    rintro ⟨ha, hp⟩
    exact ⟨allocFailedIn_of_trace_prefix htr ha, htr.trans hp⟩
  exact allowPanic_frame himp hm

theorem SepWPp.with_steps {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P (fun sf Pf => Steps prog s sf ∧ Q sf Pf) Qp := by
  intro R hm hL
  obtain ⟨sf, hst, ⟨hpc, hrun, Pf, hmf, hQ⟩ | hpan | hex⟩ := h R hm hL
  · exact ⟨sf, hst, Or.inl ⟨hpc, hrun, Pf, hmf, hst, hQ⟩⟩
  · exact ⟨sf, hst, Or.inr (Or.inl hpan)⟩
  · exact ⟨sf, hst, Or.inr (Or.inr hex)⟩

theorem SepWPp.call_frame_frozen_oom_prefix {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s0 s : State} {φ : Prop}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s0.trace <+: s.trace)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hpan_eq : ∀ sf, spec.onPanic x s sf =
      (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) := by intro _; rfl)
    (hexit_false : ∀ code sf, spec.onExit x code s sf = ⌜False⌝ := by intro _ _; rfl)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      Steps prog s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q (PanicOomProp s0))
    (hoom_false : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by
      intro sf; first | rfl | simp only [Spec.inImage]) :
    SepWPp prog ret s P Q (PanicOomProp s0) := by
  intro R hm hL
  have hm' : s.mem ⊨ spec.pre x s ∗ (F ∗ R) := by
    rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
    exact ⟨hφ, hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hm' hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ |
    ⟨_hoom_st, _hoom_post⟩
  rotate_right; · rw [hoom_false] at _hoom_post; exact (not_satisfies_false_sepConj _hoom_post).elim
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    have hsp_alm : sm.spAligned = true := by simpa [State.spAligned, hspm] using hsp
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hsp_alm hcsm
        (hF.of_keepsFrozen hsteps.keepsFrozen) (hsteps.symtab_eq.trans hsym) hsteps
        R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [hpan_eq, ← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, _, hpost, allowPanic_oom_of_trace_prefix htr⟩)⟩
  · rw [hexit_false] at hpost
    exact (allowPanic_not_exited hpost).elim

/-! ## Poll cell bijections and `StageP4Alloc` -/

private theorem extractLsb'_lo32 (hi lo : BitVec 32) (k : Nat) (hk : k + 8 ≤ 32) :
    (hi ++ lo).extractLsb' k 8 = lo.extractLsb' k 8 := by
  ext i hi'
  have hlt : k + i < 32 := by omega
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_append]
  simp [hlt]

private theorem extractLsb'_hi32 (hi lo : BitVec 32) (k : Nat) :
    (hi ++ lo).extractLsb' (k + 32) 8 = hi.extractLsb' k 8 := by
  ext i hi'
  have hlt : ¬(k + 32 + i < 32) := by omega
  have hsub : k + 32 + i - 32 = k + i := by omega
  simp only [BitVec.getElem_extractLsb']
  rw [BitVec.getLsbD_append]
  simp [hlt, hsub]

theorem pointsTo32_pair_eq (a : BitVec 64) (lo hi : BitVec 32) :
    ((a ↦₃₂ lo) ∗ ((a + 4#64) ↦₃₂ hi)) = (a ↦₆₄ (hi ++ lo)) := by
  simp only [pointsTo64, pointsTo32, sepConj_assoc, BitVec.add_zero, BitVec.add_assoc,
    extractLsb'_lo32 hi lo 0 (by decide), extractLsb'_lo32 hi lo 8 (by decide),
    extractLsb'_lo32 hi lo 16 (by decide), extractLsb'_lo32 hi lo 24 (by decide),
    extractLsb'_hi32 hi lo 0, extractLsb'_hi32 hi lo 8,
    extractLsb'_hi32 hi lo 16, extractLsb'_hi32 hi lo 24]
  rfl

theorem extract_hi_lo_append64 (w : BitVec 64) :
    w.extractLsb' 32 32 ++ w.extractLsb' 0 32 = w := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  by_cases h32 : i < 32
  · simp [h32, hi]
  · have hi32 : i - 32 < 32 := by omega
    have hadd : 32 + (i - 32) = i := by omega
    simp [h32, hi32, hadd, hi]

theorem pointsTo64_split32_eq (a w : BitVec 64) :
    (a ↦₆₄ w) = ((a ↦₃₂ w.extractLsb' 0 32) ∗ ((a + 4#64) ↦₃₂ w.extractLsb' 32 32)) := by
  rw [pointsTo32_pair_eq, extract_hi_lo_append64]

/-- 24-byte `Vec<u8>` header bijection between aligned `(w0, w1, w2)` and the unaligned
`(head32, mid0_64, mid1_64, tail32)` layout read/written by the closure (`+0x351c`, `+0x45c`). -/
theorem words3_eq_head_mid_tail (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) =
      (a ↦₃₂ w0.extractLsb' 0 32) ∗
      ((a + 0x4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
      ((a + 0xc#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
      ((a + 0x14#64) ↦₃₂ w2.extractLsb' 32 32) := by
  have ha8 : (a + 0x4#64) + 4#64 = a + 0x8#64 := by bv_omega
  have ha10 : (a + 0xc#64) + 4#64 = a + 0x10#64 := by bv_omega
  have ha14 : (a + 0x10#64) + 4#64 = a + 0x14#64 := by bv_omega
  have ha8c : (a + 0x8#64) + 4#64 = a + 0xc#64 := by bv_omega
  rw [pointsTo64_split32_eq a w0,
      pointsTo64_split32_eq (a + 0x8#64) w1, ha8c,
      pointsTo64_split32_eq (a + 0x10#64) w2, ha14,
      ← pointsTo32_pair_eq (a + 0x4#64), ha8,
      ← pointsTo32_pair_eq (a + 0xc#64), ha10]
  ac_rfl

/-- Unaligned 48-byte poll/sret cell layout `(w0, o1, o2, o3, o4, o5, o6)` read from `sp + 0x3e0`
and written to `outPtr` by the closure's store-poll dispatch and exit tail. -/
def pollCellsAt (p w0 : BitVec 64) (o1 : BitVec 32)
    (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) : SepProp :=
  (p ↦₆₄ w0) ∗
  ((p + 0x8#64) ↦₃₂ o1) ∗
  ((p + 0xc#64) ↦₆₄ o2) ∗
  ((p + 0x14#64) ↦₆₄ o3) ∗
  ((p + 0x1c#64) ↦₆₄ o4) ∗
  ((p + 0x24#64) ↦₆₄ o5) ∗
  ((p + 0x2c#64) ↦₃₂ o6)

/-- 36-byte error-tail staging slot layout (`sp + 0x2b0` / `0x2e0` / `0x310` / `0x340` / `0x370`). -/
def stagingCellsAt (slot o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) : SepProp :=
  (slot ↦₆₄ o2) ∗
  ((slot + 0x8#64) ↦₆₄ o3) ∗
  ((slot + 0x10#64) ↦₆₄ o4) ∗
  ((slot + 0x18#64) ↦₆₄ o5) ∗
  ((slot + 0x20#64) ↦₃₂ o6)

/-- Exact 48-byte cell bijection between `speWordsAt` (6 aligned u64s) and `pollCellsAt`. -/
theorem speWordsAt_eq_pollCellsAt (p w0 w1 w2 w3 w4 w5 : BitVec 64) :
    speWordsAt p w0 w1 w2 w3 w4 w5 =
      pollCellsAt p w0
        (w1.extractLsb' 0 32)
        (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
        (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
        (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
        (w5.extractLsb' 0 32 ++ w4.extractLsb' 32 32)
        (w5.extractLsb' 32 32) := by
  unfold speWordsAt pollCellsAt
  have h8c : (p + 0x8#64) + 4#64 = p + 0xc#64 := by bv_omega
  have hc10 : (p + 0xc#64) + 4#64 = p + 0x10#64 := by bv_omega
  have h1014 : (p + 0x10#64) + 4#64 = p + 0x14#64 := by bv_omega
  have h1418 : (p + 0x14#64) + 4#64 = p + 0x18#64 := by bv_omega
  have h181c : (p + 0x18#64) + 4#64 = p + 0x1c#64 := by bv_omega
  have h1c20 : (p + 0x1c#64) + 4#64 = p + 0x20#64 := by bv_omega
  have h2024 : (p + 0x20#64) + 4#64 = p + 0x24#64 := by bv_omega
  have h2428 : (p + 0x24#64) + 4#64 = p + 0x28#64 := by bv_omega
  have h282c : (p + 0x28#64) + 4#64 = p + 0x2c#64 := by bv_omega
  rw [pointsTo64_split32_eq (p + 0x08#64) w1, h8c,
      pointsTo64_split32_eq (p + 0x10#64) w2, h1014,
      pointsTo64_split32_eq (p + 0x18#64) w3, h181c,
      pointsTo64_split32_eq (p + 0x20#64) w4, h2024,
      pointsTo64_split32_eq (p + 0x28#64) w5, h282c,
      ← pointsTo32_pair_eq (p + 0xc#64), hc10,
      ← pointsTo32_pair_eq (p + 0x14#64), h1418,
      ← pointsTo32_pair_eq (p + 0x1c#64), h1c20,
      ← pointsTo32_pair_eq (p + 0x24#64), h2428]
  ac_rfl

theorem stagingCellsAt_entails_memRegion36 (slot o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    stagingCellsAt slot o2 o3 o4 o5 o6 ⊢ memRegion slot 36 := by
  unfold stagingCellsAt
  rw [ProofLib.memRegion_split' (b := slot) (n := 8) (k := 28)
        (b' := slot + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x8#64) (n := 8) (k := 20)
        (b' := slot + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x10#64) (n := 8) (k := 12)
        (b' := slot + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x18#64) (n := 8) (k := 4)
        (b' := slot + 0x20#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (pointsTo32_entails_memRegion _ _))))

theorem memRegion36_eq_exists_stagingCells (slot : BitVec 64) :
    memRegion slot 36 =
      ∃∗ o6 : BitVec 32, ∃∗ o5 : BitVec 64, ∃∗ o4 : BitVec 64,
      ∃∗ o3 : BitVec 64, ∃∗ o2 : BitVec 64,
        stagingCellsAt slot o2 o3 o4 o5 o6 := by
  unfold stagingCellsAt
  rw [ProofLib.memRegion_split' (b := slot) (n := 8) (k := 28)
        (b' := slot + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x8#64) (n := 8) (k := 20)
        (b' := slot + 0x10#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x10#64) (n := 8) (k := 12)
        (b' := slot + 0x18#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := slot + 0x18#64) (n := 8) (k := 4)
        (b' := slot + 0x20#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight slot,
      ProofLib.memRegion_eight (slot + 0x8#64),
      ProofLib.memRegion_eight (slot + 0x10#64),
      ProofLib.memRegion_eight (slot + 0x18#64),
      ProofLib.memRegion_four (slot + 0x20#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem pollCellsAt_entails_memRegion48 (p w0 : BitVec 64) (o1 : BitVec 32)
    (o2 o3 o4 o5 : BitVec 64) (o6 : BitVec 32) :
    pollCellsAt p w0 o1 o2 o3 o4 o5 o6 ⊢ memRegion p 48 := by
  unfold pollCellsAt
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 40)
        (b' := p + 0x8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 0x8#64) (n := 4) (k := 36)
        (b' := p + 0xc#64) rfl (by bv_omega) (by decide)]
  have h36 := stagingCellsAt_entails_memRegion36 (p + 0xc#64) o2 o3 o4 o5 o6
  unfold stagingCellsAt at h36
  have hc14 : (p + 0xc#64) + 0x8#64 = p + 0x14#64 := by bv_omega
  have hc1c : (p + 0xc#64) + 0x10#64 = p + 0x1c#64 := by bv_omega
  have hc24 : (p + 0xc#64) + 0x18#64 = p + 0x24#64 := by bv_omega
  have hc2c : (p + 0xc#64) + 0x20#64 = p + 0x2c#64 := by bv_omega
  rw [hc14, hc1c, hc24, hc2c] at h36
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _) h36)

theorem ptextBuf_dealloc_zero (A : RustAlloc) (ptPtr : BitVec 64) (pt : List (BitVec 8))
    (hpt_le : pt.length ≤ (0#64 : BitVec 64).toNat) :
    (ptPtr ↦ₛ pt) ∗
      (if (0#64 : BitVec 64) = 0#64 then emp
       else A.live ptPtr (0#64 : BitVec 64).toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) ((0#64 : BitVec 64).toNat - pt.length)) ⊢
      emp := by
  have hnil : pt = [] := List.eq_nil_of_length_eq_zero (by simpa using hpt_le)
  subst hnil
  simp only [↓reduceIte, pointsToBytes_nil, sepConj_emp]
  exact Entails.refl _

theorem ptextBuf_dealloc_nonzero (A : RustAlloc) (ptCap ptPtr : BitVec 64) (pt : List (BitVec 8))
    (hcap_ne : ptCap ≠ 0#64) (hpt_le : pt.length ≤ ptCap.toNat) :
    (ptPtr ↦ₛ pt) ∗
      (if ptCap = 0#64 then emp
       else A.live ptPtr ptCap.toNat 1 ∗
         memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ⊢
      A.live ptPtr ptCap.toNat 1 ∗ memRegion ptPtr ptCap.toNat := by
  simp only [hcap_ne, ↓reduceIte]
  have hsplit : memRegion ptPtr ptCap.toNat =
      memRegion ptPtr pt.length ∗
        memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length) :=
    ProofLib.memRegion_split' (b := ptPtr) (n := pt.length) (k := ptCap.toNat - pt.length)
      (b' := ptPtr + BitVec.ofNat 64 pt.length) (by omega) rfl (by omega)
  rw [hsplit]
  refine Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (sepConj_mono_left (ProofLib.pointsToBytes_entails_memRegion ptPtr pt)))

/-- Minimal deallocation-only contract bundle for Stage P4 (`__rust_dealloc` meeting
`rustDeallocSpec A` with `allocHookStack = 4096` bytes). -/
structure StageP4Alloc (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  dealloc :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr deallocName) (rustDeallocSpec A)

namespace StageP4Alloc

variable {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}

theorem dealloc_ok_at (hA : StageP4Alloc b A ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff deallocName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) (rustDeallocSpec A) :=
  sub_ok_at_of_fnAddr hA.dealloc name k hk

theorem of_allocContracts (hA : AllocContracts b A ext) : StageP4Alloc b A ext :=
  ⟨hA.dealloc⟩

theorem of_allocHooks (b : BitVec 64) (hAlloc : AllocHooks A ext) : StageP4Alloc b A ext :=
  ⟨by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      dealloc_ok_at_ext b A ext hAlloc deallocName 0 (Nat.add_zero _)⟩

end StageP4Alloc

theorem dealloc_at_closure_p4 {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : StageP4Alloc b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
      (rustDeallocSpec A) := by
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  exact hA.dealloc_ok_at
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
    (by
      dsimp only [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName]
      rw [hfn]
      simp only [arm64_norm])

theorem dealloc_at_closure_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
      (rustDeallocSpec A) :=
  dealloc_at_closure_p4 (.of_allocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
