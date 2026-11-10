/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Chain.AddEpoch
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage P2 Basic Blocks — Substage P2.6

`regIdBoxSize`-generic `SepWP` basic-block lemmas on `tripleRatchetProgAtExt b ext` for Substage
P2.6 (`+0x125c → +0x1778`: `SessionState` staging, `get_local_registration_id` shim/poll/drop,
`SessionRecord::promote_state`, `process_prekey_impl` drop, and Stage P3 entry setup).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

attribute [local wp_norm] p2Memcpy4KSpec libcMemcpySpec

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

set_option maxHeartbeats 1000000 in
/-- Segment P2.6a (`+0x125c -> getLocalRegIdShimAddr`, 4K-stacked `memcpy` via `StageP2ClosureHooks`). -/
theorem p2_seg6a_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
    ss0 ss1 ss2 ss3 ss4 ss5 ss6
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650 : BitVec 64)
    (ssRest : List (BitVec 8))
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hssRest_len : ssRest.length = 288)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext) getLocalRegIdShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
       ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
       ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
       ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
       ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
       memRegion (s.sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((coroPtr + 0x508#64) ↦₆₄ u_508) ∗
       ((coroPtr + 0x510#64) ↦₆₄ u_510) ∗
       ((coroPtr + 0x518#64) ↦₆₄ u_518) ∗
       ((coroPtr + 0x520#64) ↦₆₄ u_520) ∗
       ((coroPtr + 0x528#64) ↦₆₄ u_528) ∗
       memRegion (coroPtr + 0x530#64) 288 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr) ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
          ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
          ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
          ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
          ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x500#64) ↦₆₄ ss1) ∗
          ((coroPtr + 0x508#64) ↦₆₄ ss2) ∗
          ((coroPtr + 0x510#64) ↦₆₄ ss3) ∗
          ((coroPtr + 0x518#64) ↦₆₄ ss4) ∗
          ((coroPtr + 0x520#64) ↦₆₄ ss5) ∗
          ((coroPtr + 0x528#64) ↦₆₄ ss6) ∗
          ((coroPtr + 0x530#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = ss1 ∧
        s1.readReg64 .x21 = ss0 ∧
        s1.readReg64 .x22 = ss4 ∧
        s1.readReg64 .x23 = ss2 ∧
        s1.readReg64 .x24 = ss3 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = ss5 ∧
        s1.readReg64 .x27 = ss6 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x12d8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := hH.memcpy4K
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x125c 0x12d4
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hmemcpy (s.sp + 0xa90#64, s.sp + 0x418#64, ssRest)
  wp_steps
  wp_call hmemcpy (coroPtr + 0x530#64, s.sp + 0xa90#64, ssRest)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev p2_seg6a_4k_wp := @p2_seg6a_hooks_wp

set_option maxHeartbeats 1000000 in
/-- Segment P2.6a (`+0x125c -> getLocalRegIdShimAddr`):
Copies the 344-byte `SessionState` returned by `initialize_bob_session` at `sp + 0x3e0..0x538`
into `coroPtr + 0x4f8..0x650`, stores `coroPtr + 0x4f8` at `[coroPtr + 0x650]`, loads
`getLocalRegIdShimAddr` from `[idStoreVt + 0x20]`, sets `x0 = idStorePtr`, and calls `blr x8` at
`+0x12d4`. -/
theorem p2_seg6a_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s : State) (coroPtr idStorePtr idStoreVt getLocalRegIdShimAddr
    ss0 ss1 ss2 ss3 ss4 ss5 ss6
    u_4f8 u_500 u_508 u_510 u_518 u_520 u_528 u_650 : BitVec 64)
    (ssRest : List (BitVec 8))
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hssRest_len : ssRest.length = 288)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x125c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext) getLocalRegIdShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
       ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
       ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
       ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
       ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
       memRegion (s.sp + 0xa90#64) 288 ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((coroPtr + 0x508#64) ↦₆₄ u_508) ∗
       ((coroPtr + 0x510#64) ↦₆₄ u_510) ∗
       ((coroPtr + 0x518#64) ↦₆₄ u_518) ∗
       ((coroPtr + 0x520#64) ↦₆₄ u_520) ∗
       ((coroPtr + 0x528#64) ↦₆₄ u_528) ∗
       memRegion (coroPtr + 0x530#64) 288 ∗
       ((coroPtr + 0x650#64) ↦₆₄ u_650) ∗
       ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
       ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
       ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ ss0) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ss1) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ ss2) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ ss3) ∗
          ((s.sp + 0x400#64) ↦₆₄ ss4) ∗
          ((s.sp + 0x408#64) ↦₆₄ ss5) ∗
          ((s.sp + 0x410#64) ↦₆₄ ss6) ∗
          ((s.sp + 0x418#64) ↦ₛ ssRest) ∗
          ((s.sp + 0xa90#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x500#64) ↦₆₄ ss1) ∗
          ((coroPtr + 0x508#64) ↦₆₄ ss2) ∗
          ((coroPtr + 0x510#64) ↦₆₄ ss3) ∗
          ((coroPtr + 0x518#64) ↦₆₄ ss4) ∗
          ((coroPtr + 0x520#64) ↦₆₄ ss5) ∗
          ((coroPtr + 0x528#64) ↦₆₄ ss6) ∗
          ((coroPtr + 0x530#64) ↦ₛ ssRest) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
          ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
          ((idStoreVt + 0x20#64) ↦₆₄ᵣ getLocalRegIdShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = idStorePtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = ss1 ∧
        s1.readReg64 .x21 = ss0 ∧
        s1.readReg64 .x22 = ss4 ∧
        s1.readReg64 .x23 = ss2 ∧
        s1.readReg64 .x24 = ss3 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = ss5 ∧
        s1.readReg64 .x27 = ss6 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x12d8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := p2_memcpy_at_closure_ext hA
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x125c 0x12d4
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hmemcpy (s.sp + 0xa90#64, s.sp + 0x418#64, ssRest)
  wp_steps
  wp_call hmemcpy (coroPtr + 0x530#64, s.sp + 0xa90#64, ssRest)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Segment P2.6b (`+0x12d8 -> localRegIdPollAddr`):
Restores `x26, x23, x27, x21`, stores `regIdFutPtr, regIdFutVt` at `coroPtr + 0x788..0x790`,
branches (`b -2316`) to `+0x09e0`, loads `localRegIdPollAddr` from `[regIdFutVt + 0x18]`,
sets `x8 = sp + 0x3e0`, `x1 = ctxPtr`, and calls `blr x9` (`localRegIdPollAddr`) at `+0x09f0`. -/
theorem p2_seg6b_ext_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr regIdFutPtr regIdFutVt localRegIdPollAddr
    v_98 v_a0 v_b0 u_788 u_790 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x12d8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = regIdFutPtr)
    (hx1 : s.readReg64 .x1 = regIdFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext) localRegIdPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x788#64) ↦₆₄ u_788) ∗
       ((coroPtr + 0x790#64) ↦₆₄ u_790) ∗
       ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x18#64) ↦₆₄ᵣ localRegIdPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x1 = ctxPtr ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = ctxPtr ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x9f4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x12d8 0x12ec
  closure_fetches_range_cli b (Rust.withPanics ext) 0x9e0 0x9f0
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = regIdFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = regIdFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Segment P2.6c (`+0x09f4 -> localRegIdDropAddr`):
Checks `[sp + 0x3e0] = -2 ≠ -3`, branches to `+0x0af8`, loads `w23 = localRegId` from
`[sp + 0x3e8]`, saves registers to `sp + 0x88..0xd0`, loads `localRegIdDropAddr` from
`[regIdFutVt + 0x0]`, sets `x0 = regIdFutPtr`, and calls `blr x8` (`localRegIdDropAddr`) at
`+0x0b38`. -/
theorem p2_seg6c_ext_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr regIdFutPtr regIdFutVt localRegIdDropAddr
    v_98 v_a0 v_b0 u_88 u_98 u_a0 u_a8 u_b0 u_b8 u_d0
    u_3f0 u_3f8 u_400 u_408 : BitVec 64)
    (localRegId u_3ec : BitVec 32)
    (hdrop_nz : localRegIdDropAddr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x9f4#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAtExt b ext) localRegIdDropAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
       ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
       ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
       ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
       ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
       ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
       ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
       ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x3e8#64) ↦₃₂ localRegId) ∗
          ((s.sp + 0x3ec#64) ↦₃₂ u_3ec) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0x3f8#64) ↦₆₄ u_3f8) ∗
          ((s.sp + 0x400#64) ↦₆₄ u_400) ∗
          ((s.sp + 0x408#64) ↦₆₄ u_408) ∗
          ((coroPtr + 0x788#64) ↦₆₄ regIdFutPtr) ∗
          ((coroPtr + 0x790#64) ↦₆₄ regIdFutVt) ∗
          ((regIdFutVt + 0x0#64) ↦₆₄ᵣ localRegIdDropAddr) ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xa8#64) ↦₆₄ u_400) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ u_3f0) ∗
          ((s.sp + 0xd0#64) ↦₆₄ u_3f8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = regIdFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = regIdFutPtr ∧
        s1.readReg64 .x22 = u_3ec.zeroExtend 64 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_98 ∧
        s1.readReg64 .x27 = u_408 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb3c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdrop_beq : (localRegIdDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0x9f4 0x9fc
  closure_fetches_range_cli b (Rust.withPanics ext) 0xaf8 0xb38
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Segment P2.6d1 (`+0x0b3c -> +0x0b80`, generic `regIdBoxSize`):
Deallocates `regIdFutPtr` (`regIdBoxSize` bytes, align `8`), checks `[sp + 0x88] = -2 ≠ -1`,
writes `localRegId` to `[coroPtr + 0x64c]` and `remoteRegId` (`[msgPtr + 0xe8]`) to
`[coroPtr + 0x648]`, sets `x0 = sp + 0x3e0`, `x1 = coroPtr + 0x4f8`, `w2 = 0x158`,
`x21 = coroPtr + 0xe0`, and stops at `+0x0b80`. -/
theorem p2_seg6d1_gen_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr regIdFutPtr regIdFutVt : BitVec 64)
    (localRegId remoteRegId u_648 u_64c : BitVec 32)
    (regIdBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb3c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hbs_nz : BitVec.ofNat 64 regIdBoxSize ≠ 0#64)
    (hbs_lt : regIdBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = regIdFutPtr)
    (hx23 : s.readReg64 .x23 = localRegId.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = regIdFutVt) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb80#64) s
      (((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
       ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live regIdFutPtr regIdBoxSize 8 ∗
       memRegion regIdFutPtr regIdBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       ((coroPtr + 0x648#64) ↦₃₂ u_648) ∗
       ((coroPtr + 0x64c#64) ↦₃₂ u_64c) ∗
       ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
       ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId))
      (fun s1 P_f =>
        (P_f ⊢
          ((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
          ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((coroPtr + 0x648#64) ↦₃₂ remoteRegId) ∗
          ((coroPtr + 0x64c#64) ↦₃₂ localRegId) ∗
          ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
          ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = coroPtr + 0x4f8#64 ∧
        s1.readReg64 .x2 = 344#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
        s1.readReg64 .x24 = regIdFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hbs_beq : (BitVec.ofNat 64 regIdBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 regIdBoxSize).toNat = regIdBoxSize := Nat.mod_eq_of_lt hbs_lt
  closure_fetches_range_cli b (Rust.withPanics ext) 0xb3c 0xb7c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = regIdFutPtr := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = localRegId.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = regIdFutVt := hx24
  wp_steps
  wp_call hdealloc (regIdFutPtr, regIdBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev p2_seg6d1_gen_4k_wp := @p2_seg6d1_gen_hooks_wp

theorem p2_seg6d1_gen_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    ∀ (s : State) (coroPtr msgPtr regIdFutPtr regIdFutVt : BitVec 64)
      (localRegId remoteRegId u_648 u_64c : BitVec 32)
      (regIdBoxSize : Nat),
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb3c#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      BitVec.ofNat 64 regIdBoxSize ≠ 0#64 →
      regIdBoxSize < 2 ^ 64 →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x21 = regIdFutPtr →
      s.readReg64 .x23 = localRegId.zeroExtend 64 →
      s.readReg64 .x24 = regIdFutVt →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb80#64) s
        (((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
         ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
         A.live regIdFutPtr regIdBoxSize 8 ∗
         memRegion regIdFutPtr regIdBoxSize ∗
         A.pool ∗
         stackAt s.sp allocHookStack ∗
         ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
         ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
         ((coroPtr + 0x648#64) ↦₃₂ u_648) ∗
         ((coroPtr + 0x64c#64) ↦₃₂ u_64c) ∗
         ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
         ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId))
        (fun s1 P_f =>
          (P_f ⊢
            ((regIdFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 regIdBoxSize) ∗
            ((regIdFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
            A.pool ∗
            stackAt s.sp allocHookStack ∗
            ((s.sp + 0x88#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((coroPtr + 0x648#64) ↦₃₂ remoteRegId) ∗
            ((coroPtr + 0x64c#64) ↦₃₂ localRegId) ∗
            ((coroPtr + 0x650#64) ↦₆₄ (coroPtr + 0x4f8#64)) ∗
            ((msgPtr + 0xe8#64) ↦₃₂ remoteRegId)) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
          s1.readReg64 .x1 = coroPtr + 0x4f8#64 ∧
          s1.readReg64 .x2 = 344#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
          s1.readReg64 .x22 = s.readReg64 .x22 ∧
          s1.readReg64 .x23 = localRegId.zeroExtend 64 ∧
          s1.readReg64 .x24 = regIdFutVt ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = s.readReg64 .x26 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg6d1_gen_hooks_wp b ext (StageP2ClosureHooks.of_allocContracts hA)

set_option maxHeartbeats 1000000 in
/-- Segment P2.6d2 (`+0x0b80 -> SessionRecord::promote_state`, 4K-stacked `memcpy` via `StageP2ClosureHooks`). -/
theorem p2_seg6d2_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb80#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = s.sp + 0x3e0#64)
    (hx1 : s.readReg64 .x1 = coroPtr + 0x4f8#64)
    (hx2 : s.readReg64 .x2 = 344#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0xe0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr "<libsignal_protocol::state::session::SessionRecord>::promote_state") s
      (((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344 ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes) ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb90#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := hH.memcpy4K
  have htarget :
      (tripleRatchetProgAtExt b ext).fnAddr "<libsignal_protocol::state::session::SessionRecord>::promote_state" =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) := by
    simp [tripleRatchetProgAtExt, Program.fnAddr,
      ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state",
      ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]
  rw [htarget]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xb80 0xb8c
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = s.sp + 0x3e0#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr + 0x4f8#64 := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = 344#64 := hx2
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0xe0#64 := hx21
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, coroPtr + 0x4f8#64, ssBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

abbrev p2_seg6d2_4k_wp := @p2_seg6d2_hooks_wp

set_option maxHeartbeats 1000000 in
/-- Segment P2.6d2 (`+0x0b80 -> SessionRecord::promote_state`):
Copies the 344-byte `SessionState` from `coroPtr + 0x4f8..0x650` to `sp + 0x3e0..0x538`,
sets `x0 = coroPtr + 0xe0`, `x1 = sp + 0x3e0`, and calls `SessionRecord::promote_state` at
`+0x0b8c`. -/
theorem p2_seg6d2_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s : State) (coroPtr : BitVec 64) (ssBytes : List (BitVec 8))
    (hss_len : ssBytes.length = 344)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb80#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = s.sp + 0x3e0#64)
    (hx1 : s.readReg64 .x1 = coroPtr + 0x4f8#64)
    (hx2 : s.readReg64 .x2 = 344#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = coroPtr + 0xe0#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr "<libsignal_protocol::state::session::SessionRecord>::promote_state") s
      (((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
       memRegion (s.sp + 0x3e0#64) 344)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x4f8#64) ↦ₛ ssBytes) ∗
          ((s.sp + 0x3e0#64) ↦ₛ ssBytes)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb90#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hmemcpy := p2_memcpy_at_closure_ext hA
  have htarget :
      (tripleRatchetProgAtExt b ext).fnAddr "<libsignal_protocol::state::session::SessionRecord>::promote_state" =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) := by
    simp [tripleRatchetProgAtExt, Program.fnAddr,
      ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state",
      ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]
  rw [htarget]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xb80 0xb8c
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = s.sp + 0x3e0#64 := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = coroPtr + 0x4f8#64 := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = 344#64 := hx2
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = coroPtr + 0xe0#64 := hx21
  wp_steps
  wp_call hmemcpy (s.sp + 0x3e0#64, coroPtr + 0x4f8#64, ssBytes)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
/-- Segment P2.6e (`+0x0b90 -> drop_glue::<process_prekey_impl>`, `1568`/`3168` Kyber KeyPair):
Reads `(opkIdIsSome, opkId)`, `kyberPreKeyId`, `signedPreKeyId` from `msgPtr`, deallocates
`kyberKpPubPtr` (`1568, 1`) and `kyberKpSecPtr` (`3168, 1`), sets `[coroPtr + 0x4f1] = 0#8` and
`[coroPtr + 0x4f2] = 1#8`, packs `x22` and `x24`, sets `x0 = coroPtr + 0x398`, and calls
`drop_glue::<process_prekey_impl>` at `+0x1694`. -/
theorem p2_seg6e_1568_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr
    v_c8 u_a8 u_d0 : BitVec 64)
    (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_4f1 b_4f2 : BitVec 8)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb90#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") s
      (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
       ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
       ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
       ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
       ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
       A.live kyberKpSecPtr 3168 1 ∗ memRegion kyberKpSecPtr 3168 ∗
       A.pool ∗
       stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
          ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
          ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
          ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
          ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 ∧
        s1.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ∧
        s1.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_c8 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hkyber_beq : (kyberCtCap - 0#64 == 0#64) = false := by
    rw [BitVec.sub_zero]; exact beq_eq_false_iff_ne.mpr hkyber_nz
  have htarget :
      (tripleRatchetProgAtExt b ext).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) := by
    simp [tripleRatchetProgAtExt, Program.fnAddr,
      ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>",
      ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]
  rw [htarget]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xb90 0xbf0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1678 0x1694
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  wp_call hdealloc (kyberKpPubPtr, 1568, 1)
  wp_steps
  wp_call hdealloc (kyberKpSecPtr, 3168, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_slice,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

abbrev p2_seg6e_1568_4k_wp := @p2_seg6e_1568_hooks_wp

theorem p2_seg6e_1568_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    ∀ (s : State) (coroPtr msgPtr kyberCtCap kyberKpPubPtr kyberKpSecPtr
      v_c8 u_a8 u_d0 : BitVec 64)
      (opkIdIsSome opkId kyberPreKeyId signedPreKeyId : BitVec 32)
      (b_4f1 b_4f2 : BitVec 8),
      kyberCtCap ≠ 0#64 →
      s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xb90#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s.readReg64 .x19 = coroPtr →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr
          "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") s
        (((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
         ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
         ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
         ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
         ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
         ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
         ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
         ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
         ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
         ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
         ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
         ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
         ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
         ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
         ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
         ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
         ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
         A.live kyberKpPubPtr 1568 1 ∗ memRegion kyberKpPubPtr 1568 ∗
         A.live kyberKpSecPtr 3168 1 ∗ memRegion kyberKpSecPtr 3168 ∗
         A.pool ∗
         stackAt s.sp allocHookStack)
        (fun s1 P_f =>
          (P_f ⊢
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x718#64) ↦₆₄ kyberKpPubPtr) ∗
            ((coroPtr + 0x720#64) ↦₆₄ 0x620#64) ∗
            ((coroPtr + 0x728#64) ↦₆₄ kyberKpSecPtr) ∗
            ((coroPtr + 0x730#64) ↦₆₄ 0xc60#64) ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((msgPtr + 0x78#64) ↦₃₂ opkIdIsSome) ∗
            ((msgPtr + 0x7c#64) ↦₃₂ opkId) ∗
            ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
            ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
            ((msgPtr + 0xec#64) ↦₃₂ signedPreKeyId) ∗
            ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
            ((s.sp + 0xa8#64) ↦₆₄ 0#64) ∗
            ((s.sp + 0xc8#64) ↦₆₄ v_c8) ∗
            ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
            A.pool ∗
            stackAt s.sp allocHookStack) ∧
          s1.sp = s.sp ∧
          s1.trace = s.trace ∧
          s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
          s1.readReg64 .x19 = coroPtr ∧
          s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
          s1.readReg64 .x21 = 0#64 ∧
          s1.readReg64 .x22 = (kyberPreKeyId.zeroExtend 64 <<< 32) ||| 1#64 ∧
          s1.readReg64 .x23 = opkIdIsSome.zeroExtend 64 ∧
          s1.readReg64 .x24 = opkIdIsSome.zeroExtend 64 ||| (opkId.zeroExtend 64 <<< 32) ∧
          s1.readReg64 .x25 = s.readReg64 .x25 ∧
          s1.readReg64 .x26 = v_c8 ∧
          s1.readReg64 .x27 = s.readReg64 .x27 ∧
          s1.readReg64 .x28 = s.readReg64 .x28 ∧
          s1.readReg64 .x29 = s.readReg64 .x29 ∧
          s1.readReg64 .x30 =
            (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1698#64 ∧
          calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg6e_1568_hooks_wp b ext (StageP2ClosureHooks.of_allocContracts hA)

set_option maxHeartbeats 1000000 in
/-- Segment P2.6f (`+0x1698 -> +0x1778`):
Stores `process_prekey_impl` `Result::Ok((opkId?, kyberPreKeyId?, signedPreKeyId))` into
`coroPtr + 0x250..0x278`, copies `(opkId?, kyberPreKeyId?, signedPreKeyId)` into
`coroPtr + 0x298..0x2a8`, sets up the Stage P3 decryption loop frame on the stack
(`sp + 0x80..0xb8` and `sp + 0x3a0..0x3d8`), checks `[coroPtr + 0xf8] = ss0 ≠ -1`,
and reaches `+0x1778`. -/
theorem p2_seg6f_ext_wp (b : BitVec 64)
    (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    opkPacked kyberPacked ss0 v_330 v_388
    u_250 u_258 u_260 u_270 u_278 u_298 u_2a0
    u_80 u_88 u_90 u_a0 u_a8 u_b0
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (opkIdIsSome signedPreKeyId u_268 u_26c u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_390 b_3ac : BitVec 8)
    (hss0_ne : ss0 + 1#64 ≠ 0#64)
    (hpack_lo : (opkPacked &&& 0xff#64) = (opkIdIsSome.zeroExtend 64 &&& 0xff#64))
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0xfffffffffffffffe#64)
    (hx22 : s.readReg64 .x22 = kyberPacked)
    (hx23 : s.readReg64 .x23 = opkIdIsSome.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = opkPacked) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1778#64) s
      (((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗
       ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗
       ((coroPtr + 0x268#64) ↦₃₂ u_268) ∗
       ((coroPtr + 0x26c#64) ↦₃₂ u_26c) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗
       ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((s.sp + 0x80#64) ↦₆₄ u_80) ∗
       ((s.sp + 0x88#64) ↦₆₄ u_88) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
       ((s.sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((s.sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3b0#64 - (s.sp + 0x3b0#64) + u_3b0)) ∗
       ((s.sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((s.sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((s.sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((s.sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ u_3d8))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
          ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
          ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
          ((coroPtr + 0xf8#64) ↦₆₄ ss0) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x260#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x268#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x26c#64) ↦₃₂ (s.readReg64 (Reg.gpr 11#5)).truncate 32) ∗
          ((coroPtr + 0x270#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x278#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x298#64) ↦₆₄ opkPacked) ∗
          ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
          ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
          ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
          ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
          ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
          ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
          ((s.sp + 0x90#64) ↦₆₄ v_388) ∗
          ((s.sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
          ((s.sp + 0xa8#64) ↦₆₄ v_330) ∗
          ((s.sp + 0xb0#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
          ((s.sp + 0xd0#64) ↦₆₄ signedPreKeyId.zeroExtend 64) ∗
          ((s.sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
          ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
          ((s.sp + 0x3b0#64) ↦₆₄ (s.sp + 0x3ac#64)) ∗
          ((s.sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
          ((s.sp + 0x3c0#64) ↦₆₄ (s.sp + 0x3a0#64)) ∗
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d0#64) ↦₆₄ 8#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x8 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x9 = 8#64 ∧
        s1.readReg64 .x10 = msgVerByte.zeroExtend 64 ∧
        s1.readReg64 .x11 = coroPtr + 0xf8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0xfffffffffffffffe#64 ∧
        s1.readReg64 .x22 = kyberPacked ∧
        s1.readReg64 .x23 = opkPacked ∧
        s1.readReg64 .x24 = opkPacked ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = v_330 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hss0_beq : (ss0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hss0_ne
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1698 0x16b0
  closure_fetches_range_cli b (Rust.withPanics ext) 0x16c8 0x1774
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0xfffffffffffffffe#64 := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = kyberPacked := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = opkIdIsSome.zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = opkPacked := hx24
  have hu3b0 : s.sp + 0x3b0#64 - (s.sp + 0x3b0#64) + u_3b0 = u_3b0 := by bv_omega
  rw [hu3b0]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  have hbfm1 : ((opkIdIsSome.zeroExtend 64 &&& 255#64) |||
    ((opkPacked >>> 8 &&& 72057594037927935#64) <<< 8)) = opkPacked := by
    revert hpack_lo; clear * -; bv_slice
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  rw [hbfm1]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
