/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
public import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.LoopBudget
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2Budget
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Budget-Threaded Stage P2 Matched-Session Basic Blocks: Part B

`VmPreserved` and pool-threaded `p2_matched_to_dealloc_*_wp` / `p2_matched_to_remote_ik_*_wp`
segments, plus the budget-threaded `<str as ToOwned>::to_owned` envelope `StrToOwnedEnv` and
contracts `strToOwnedLocal2Spec` / `strToOwnedLocal2SpecWithStack`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoVerification (libsignalSessionCode)
open CryptoVerification.RustHeap (allocHookStack vecU8)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetProgAtExt)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  strToOwnedLocal2Name strToOwnedLocal2Stack strToOwnedLocal2StackWith
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents
  RustCliAllocBudget VmPreserved rustAllocEvents
)

export CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  strToOwnedLocal2Name strToOwnedLocal2Stack strToOwnedLocal2StackWith
  stackAt_strToOwnedLocal2 stackAt_strToOwnedLocal2With memRegion24_cells3
)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")

private theorem cond_eq_adds_1_false_m2_budget {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

/-- `VmPreserved`-strengthened `+0x08c0 → __rustc::__rust_dealloc` on
`tripleRatchetProgAtExt b ext`. -/
theorem p2_matched_to_dealloc_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = serPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x930#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x910 0x92c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp_all [arm64_norm], rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], rfl⟩

private theorem sepWP_frame_pool {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) {prog : Program} {target_pc : BitVec 64} {s : State}
    {Pre Post : SepProp} {Q : State → Prop}
    (hwp : SepWP prog target_pc s Pre
      (fun s1 P_f => (P_f ⊢ Post) ∧ VmPreserved s s1 ∧ Q s1)) :
    SepWP prog target_pc s (Pre ∗ A.pool lim st s)
      (fun s1 P_f => (P_f ⊢ Post ∗ A.pool lim st s1) ∧ Q s1) := by
  apply SepWP.of_reaches_pc
  intro R hm hL
  rw [sepConj_assoc] at hm
  obtain ⟨s1, hsteps, hout⟩ := SepWP.to_reaches_pc hwp hm hL
  rcases hout with ⟨hpc1, hrun1, P_f, hPf, hent, hvm, hQ⟩ | ⟨_, hoom⟩
  · refine ⟨s1, hsteps, Or.inl ⟨hpc1, hrun1, P_f ∗ A.pool lim st s, ?_, ?_, hQ⟩⟩
    · rwa [sepConj_assoc]
    · rw [A.pool_of_vmPreserved hvm]
      exact sepConj_mono_left hent
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Pool-threaded `+0x08c0 → __rustc::__rust_dealloc` on `tripleRatchetProgAtExt b ext`. -/
theorem p2_matched_to_dealloc_wp {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (st : M.σ)
    (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = serPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = 1#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x930#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  rw [← sepConj_assoc]
  refine SepWP.mono
    (sepWP_frame_pool A lim st
      (p2_matched_to_dealloc_vm_wp b ext s coroPtr serPtr hpc hrun hsp_align hx19 hx21 hx26))
    (fun s1 _ _ _ ⟨hent, hrest⟩ => ?_)
    (fun _ _ _ hf => hf)
  rw [sepConj_assoc] at hent
  exact ⟨hent, hrest⟩

/-- `VmPreserved`-strengthened `+0x0930 → <SessionState>::remote_identity_key` on
`tripleRatchetProgAtExt b ext`. -/
theorem p2_matched_to_remote_ik_vm_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr locCap : BitVec 64)
    (hcap : locCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x930#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ locCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
               ((coroPtr + 0xf8#64) ↦₆₄ locCap)) ∧
        VmPreserved s s1 ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x94c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcmn := cond_eq_adds_1_false_m2_budget hcap
  closure_fetches_range_cli b (Rust.withPanics ext) 0x930 0x948
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, by simp_all [arm64_norm], rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    rfl⟩

/-- Pool-threaded `+0x0930 → <SessionState>::remote_identity_key` on
`tripleRatchetProgAtExt b ext`. -/
theorem p2_matched_to_remote_ik_wp {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} (st : M.σ)
    (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr locCap : BitVec 64)
    (hcap : locCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x930#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ locCap) ∗ A.pool lim st s)
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
               ((coroPtr + 0xf8#64) ↦₆₄ locCap) ∗ A.pool lim st s1) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = s.sp + 0x370#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x94c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  rw [← sepConj_assoc]
  refine SepWP.mono
    (sepWP_frame_pool A lim st
      (p2_matched_to_remote_ik_vm_wp b ext s coroPtr locCap hcap hpc hrun hx19))
    (fun s1 _ _ _ ⟨hent, hrest⟩ => ?_)
    (fun _ _ _ hf => hf)
  rw [sepConj_assoc] at hent
  exact ⟨hent, hrest⟩

/-- Exact binary allocator event trace of `<str as alloc::borrow::ToOwned>::to_owned` on a
non-empty string slice (`0 < bs.length`): a single `__rust_alloc(bs.length, 1)` call. -/
abbrev strToOwnedEvents (bs : List (BitVec 8)) : List AllocEvent :=
  rustAllocEvents bs.length 1

/-- Exact singleton event envelope for `<str as alloc::borrow::ToOwned>::to_owned`
(`0 < bs.length`). -/
def StrToOwnedEnv (bs : List (BitVec 8)) : List AllocEvent → Prop :=
  fun evs => evs = strToOwnedEvents bs

theorem fitsEnv_strToOwnedEnv_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {bs : List (BitVec 8)} :
    FitsEnv M lim st (StrToOwnedEnv bs) ↔ FitsEvents M lim st (strToOwnedEvents bs) :=
  ⟨fun h => h _ rfl, fun h _ heq => heq ▸ h⟩

/-- Stack-parametric budget-threaded contract of `<str as alloc::borrow::ToOwned>::to_owned`
(`onPanic = ⌜False⌝`, `onOom = ⌜False⌝` under `FitsEvents M lim st (strToOwnedEvents bs)`). -/
def strToOwnedLocal2SpecWithStack (hookStack : Nat) {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) where
  pre := fun ((outPtr, srcPtr, bs), st) s =>
    ⌜s.readReg64 .x0 = outPtr ∧
     s.readReg64 .x1 = srcPtr ∧
     s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
     0 < bs.length ∧
     bs.length < 2 ^ 63 ∧
     FitsEvents M lim st (strToOwnedEvents bs)⌝ ∗
    memRegion outPtr 24 ∗
    (srcPtr ↦ᵣ bs) ∗
    A.pool lim st s ∗
    stackAt s.sp (strToOwnedLocal2StackWith hookStack)
  post := fun ((outPtr, srcPtr, bs), st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A.repAlloc outPtr bs ∗
    (srcPtr ↦ᵣ bs) ∗
    A.pool lim (M.stepEvents (strToOwnedEvents bs) st) sf ∗
    stackAt s0.sp (strToOwnedLocal2StackWith hookStack)

/-- Budget-threaded contract of `<str as alloc::borrow::ToOwned>::to_owned` at `allocHookStack`
(`strToOwnedLocal2Stack = 48 + allocHookStack`). -/
abbrev strToOwnedLocal2Spec {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) :
    Spec ((BitVec 64 × BitVec 64 × List (BitVec 8)) × M.σ) :=
  strToOwnedLocal2SpecWithStack allocHookStack A lim

theorem vecU8_of_exact_alloc {M : AllocCostModel} (A : RustCliAllocBudget M)
    (outPtr p : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp : p ≠ 0#64) :
    (outPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((outPtr + 8#64) ↦₆₄ p) ∗
    ((outPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live p bs.length 1 ∗
    (p ↦ₛ bs) ⊢
      vecU8 A.repAlloc outPtr bs :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched.vecU8_of_exact_alloc
    A.repAlloc outPtr p bs hpos hlt hp

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBBudget
