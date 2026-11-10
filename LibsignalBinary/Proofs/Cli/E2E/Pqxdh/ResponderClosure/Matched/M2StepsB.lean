/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import ProofLib.SepLogic.WP
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P2 Matched-Session Basic Blocks: Part B

`tripleRatchetProgAtExt b ext` basic-block lemmas `p2_matched_to_dealloc_wp` and
`p2_matched_to_remote_ik_wp`, plus `<str as ToOwned>::to_owned` contracts `strToOwnedLocal2Spec` and
`strToOwnedLocal2SpecWithStack`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

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

/-- Symbol name of `<str as alloc::borrow::ToOwned>::to_owned` called on the
remote-identity mismatch error path (`+0x130c`). -/
abbrev strToOwnedLocal2Name : String :=
  "<str as alloc::borrow::ToOwned>::to_owned"

private theorem cond_eq_adds_1_false_m2 {c : BitVec 64} (hc : c.toNat < 2 ^ 63) :
    ConditionHolds CondCode.EQ (addsPState64 c 1#64) = false := by
  rw [conditionHolds_eq_addsPState64, beq_eq_false_iff_ne]
  intro heq
  have hnat := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at hnat
  omega

/-- `+0x08c0 → __rustc::__rust_dealloc` on the `Ok(true)` branch of `promote_matching_session`:
reads `[sp + 0x3e0] = 0#64` and `[sp + 0x3e8] = 1#8`, sets `x25 = sp + 0x210`, and calls
`__rust_dealloc(serPtr, 33, 1)` returning to `entry + 0x930`. -/
theorem p2_matched_to_dealloc_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 1#8)) ∧
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
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x930#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x910 0x92c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], rfl⟩

/-- `+0x0930 → <SessionState>::remote_identity_key`: loads `x0 = coroPtr + 0xe0`, advances `x0`
to `coroPtr + 0xf8` checking `locCap ≠ -1`, sets `x8 = sp + 0x3e0` and `x21 = sp + 0x370`, and calls
`remote_identity_key` returning to `entry + 0x94c`. -/
theorem p2_matched_to_remote_ik_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr locCap : BitVec 64)
    (hcap : locCap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x930#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% ((2 ^ 64 + ls_off% "<libsignal_protocol::state::session::SessionState>::remote_identity_key" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64)) s
      (((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ locCap))
      (fun s1 P_f =>
        (P_f ⊢ ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
               ((coroPtr + 0xf8#64) ↦₆₄ locCap)) ∧
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
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x94c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcmn := cond_eq_adds_1_false_m2 hcap
  closure_fetches_range_cli b (Rust.withPanics ext) 0x930 0x948
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    rfl⟩

/-- Stack budget of `<str as ToOwned>::to_owned` (`48` bytes local frame + `allocHookStack`). -/
abbrev strToOwnedLocal2Stack : Nat := 48 + allocHookStack

/-- Contract of `<str as alloc::borrow::ToOwned>::to_owned` (`0x8da5c`) for a non-empty
read-only string slice `(srcPtr ↦ᵣ bs)` (`0 < bs.length`, `bs.length < 2 ^ 63`), writing an owned
`String` (`vecU8 A outPtr bs`) at `outPtr` (`x0`) or panicking via `handle_alloc_error` on OOM. -/
def strToOwnedLocal2Spec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  ({ pre := fun (outPtr, srcPtr, bs) s =>
        ⌜s.readReg64 .x0 = outPtr ∧
         s.readReg64 .x1 = srcPtr ∧
         s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
         0 < bs.length ∧
         bs.length < 2 ^ 63⌝ ∗
        memRegion outPtr 24 ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s.sp strToOwnedLocal2Stack
     post := fun (outPtr, srcPtr, bs) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        vecU8 A outPtr bs ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s0.sp strToOwnedLocal2Stack } : Spec _).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

theorem stackAt_strToOwnedLocal2 (sp : BitVec 64) :
    stackAt sp strToOwnedLocal2Stack =
      stackAt (sp - 48#64) allocHookStack ∗ cells (sp - 48#64) 6 := by
  exact ProofLib.stackAt_split_cells sp allocHookStack 6 (by decide)

/-- Stack budget of `<str as ToOwned>::to_owned` (`48` bytes local frame + `hookStack`). -/
abbrev strToOwnedLocal2StackWith (hookStack : Nat) : Nat := 48 + hookStack

/-- Stack-parametric contract of `<str as alloc::borrow::ToOwned>::to_owned`. -/
def strToOwnedLocal2SpecWithStack (hookStack : Nat) (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) :=
  ({ pre := fun (outPtr, srcPtr, bs) s =>
        ⌜s.readReg64 .x0 = outPtr ∧
         s.readReg64 .x1 = srcPtr ∧
         s.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
         0 < bs.length ∧
         bs.length < 2 ^ 63⌝ ∗
        memRegion outPtr 24 ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s.sp (strToOwnedLocal2StackWith hookStack)
     post := fun (outPtr, srcPtr, bs) s0 sf =>
        ⌜sf.trace = s0.trace⌝ ∗
        vecU8 A outPtr bs ∗
        (srcPtr ↦ᵣ bs) ∗
        A.pool ∗
        stackAt s0.sp (strToOwnedLocal2StackWith hookStack) } : Spec _).allowPanicWhen
    (fun _ s0 sf => allocFailedIn s0 sf ∧ s0.trace <+: sf.trace)

theorem stackAt_strToOwnedLocal2With (hookStack : Nat) (sp : BitVec 64)
    (h : hookStack ≤ 2 ^ 64 - 48) :
    stackAt sp (strToOwnedLocal2StackWith hookStack) =
      stackAt (sp - 48#64) hookStack ∗ cells (sp - 48#64) 6 := by
  rw [show strToOwnedLocal2StackWith hookStack = hookStack + 8 * 6 by
    unfold strToOwnedLocal2StackWith; omega]
  exact ProofLib.stackAt_split_cells sp hookStack 6 (by omega)

theorem memRegion24_cells3 (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) := by
  rw [show (24 : Nat) = 8 * 3 by decide, ProofLib.memRegion_cells a 3 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]

theorem vecU8_of_exact_alloc (A : RustAlloc) (outPtr p : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp : p ≠ 0#64) :
    (outPtr ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    ((outPtr + 8#64) ↦₆₄ p) ∗
    ((outPtr + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    A.live p bs.length 1 ∗
    (p ↦ₛ bs) ⊢
      vecU8 A outPtr bs := by
  refine Entails.sepExists_right (BitVec.ofNat 64 bs.length) (Entails.sepExists_right p ?_)
  have hcap_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hcap_nz : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h0
    have ht : (BitVec.ofNat 64 bs.length).toNat = (0 : BitVec 64).toNat :=
      congrArg BitVec.toNat h0
    rw [hcap_toNat] at ht
    change bs.length = 0 at ht
    omega
  have _hp' : p ≠ 0 := hp
  unfold vecU8At vecHeader
  simp only [hcap_toNat, hcap_nz, ↓reduceIte, Nat.sub_self, memRegion_zero, sepConj_emp]
  sep_frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
