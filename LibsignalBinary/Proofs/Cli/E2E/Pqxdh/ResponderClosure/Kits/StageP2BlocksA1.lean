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
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderIntoPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage P2 Basic Blocks — Substages P2.1 and P2.2

Capacity-generic `SepWP` basic-block lemmas on `tripleRatchetProgAtExt b ext` (`+0x0868 → +0x145c`)
for Substages P2.1 (`PublicKey::serialize`, `promote_matching_session`, `get_signed_pre_key` shim)
and P2.2 (`get_signed_pre_key` poll, future drop/dealloc, Curve25519 keypair serde, and
`get_kyber_pre_key` shim).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")

/-! ## 1. Substage P2.1 Basic Blocks (`+0x868 -> spkLoadShimAddr`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg1a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (b_4f1 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x868#64)
    (hrun : s.status = .Running)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_core::curve::PublicKey>::serialize" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8))
      (fun s1 P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = msgPtr + 0xa8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8a0#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x868 0x89c
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx8' : s.readReg64 (Reg.gpr 8#5) = kyberStorePtr := hx8
  have hx9' : s.readReg64 (Reg.gpr 9#5) = msgPtr := hx9
  have hx10' : s.readReg64 (Reg.gpr 10#5) = kyberStoreVt := hx10
  have hx11' : s.readReg64 (Reg.gpr 11#5) = preKeyStorePtr := hx11
  have hx12' : s.readReg64 (Reg.gpr 12#5) = remoteAddrPtr := hx12
  have hx13' : s.readReg64 (Reg.gpr 13#5) = preKeyStoreVt := hx13
  have hx14' : s.readReg64 (Reg.gpr 14#5) = localAddrPtr := hx14
  have hx15' : s.readReg64 (Reg.gpr 15#5) = idStorePtr := hx15
  have hx16' : s.readReg64 (Reg.gpr 16#5) = idStoreVt := hx16
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      cells, BitVec.add_assoc, BitVec.reduceAdd,
      sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  repeat (refine SepWP.exists_elim fun _ => ?_)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩
  dsimp only [processPrekeyActive10At]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 800000 in
theorem p2_seg1b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr serPtr spkStorePtr spkStoreVt : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8a0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx25 : s.readReg64 .x25 = 4#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64)) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x1 = 4#64 ∧
        s1.readReg64 .x2 = serPtr ∧
        s1.readReg64 .x3 = 33#64 ∧
        s1.readReg64 .x8 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = coroPtr + 0xe0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = 4#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8a0 0x8bc
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = coroPtr + 0xe0#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 4#64 := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1000000 in
theorem p2_seg1c_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr : BitVec 64)
    (spkId : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) spkLoadShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗
       memRegion serPtr 33 ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
       ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗
          ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkStorePtr ∧
        s1.readReg64 .x1 = spkId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧
        s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf14#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  closure_fetches_range_cli b (Rust.withPanics ext) 0x8c0 0x8c4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x910 0x914
  closure_fetches_range_cli b (Rust.withPanics ext) 0xa08 0xa2c
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf04 0xf10
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = serPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkStorePtr := hx22
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkStoreVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 33#64 := hx26
  wp_steps
  wp_call hdealloc (serPtr, 33, 1)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p2_seg1c_ext_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext)
    (s : State) (coroPtr msgPtr serPtr spkStorePtr spkStoreVt spkLoadShimAddr : BitVec 64)
    (spkId : BitVec 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx26 : s.readReg64 .x26 = 33#64) :
    SepWP (tripleRatchetProgAtExt b ext) spkLoadShimAddr s
      (((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
       A.live serPtr 33 1 ∗ memRegion serPtr 33 ∗ A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
       ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3e0#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3e8#64) ↦₈ 0#8) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0xec#64) ↦₃₂ spkId) ∗
          ((msgPtr + 0xf0#64) ↦₈ 4#8) ∗ ((spkStoreVt + 0x18#64) ↦₆₄ᵣ spkLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkStorePtr ∧
        s1.readReg64 .x1 = spkId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = serPtr ∧ s1.readReg64 .x22 = spkStorePtr ∧
        s1.readReg64 .x23 = 0#64 ∧ s1.readReg64 .x24 = spkStoreVt ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧ s1.readReg64 .x26 = 33#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧ s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf14#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg1c_hooks_wp b ext (.of_allocContracts hA) s coroPtr msgPtr serPtr spkStorePtr
    spkStoreVt spkLoadShimAddr spkId hpc hrun hsp_align hx19 hx21 hx22 hx24 hx26

/-! ## 2. Substage P2.2 Basic Blocks (`+0xf14 -> kyberLoadShimAddr`) -/

set_option maxHeartbeats 800000 in
theorem p2_seg2a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr ctxPtr spkFutPtr spkFutVt spkPollAddr
    v_98 v_a0 v_b0 u_4f8 u_500 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf14#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = spkFutPtr)
    (hx1 : s.readReg64 .x1 = spkFutVt)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext) spkPollAddr s
      (((s.sp + 0x98#64) ↦₆₄ v_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ u_4f8) ∗
       ((coroPtr + 0x500#64) ↦₆₄ u_500) ∗
       ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x18#64) ↦₆₄ᵣ spkPollAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
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
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf38#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf14 0xf34
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx0' : s.readReg64 (Reg.gpr 0#5) = spkFutPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = spkFutVt := hx1
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
theorem p2_seg2b_gen_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr spkFutPtr spkFutVt spkDropAddr
    spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    v_98 v_a0 v_b0 u_90 u_98 u_a0 u_b0 u_b8 u_d0 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf38#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg2 : spkPubCap ≠ 0xfffffffffffffffe#64)
    (hdrop_nz : spkDropAddr ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = v_b0)
    (hx23 : s.readReg64 .x23 = v_a0)
    (hx26 : s.readReg64 .x26 = v_98) :
    SepWP (tripleRatchetProgAtExt b ext) spkDropAddr s
      (preKeyRecordOut64At (s.sp + 0x3e0#64)
         spkPubCap spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
       ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
       ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
       ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
       ((s.sp + 0x90#64) ↦₆₄ u_90) ∗
       ((s.sp + 0x98#64) ↦₆₄ u_98) ∗
       ((s.sp + 0xa0#64) ↦₆₄ u_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ u_b8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0))
      (fun s1 P_f =>
        (P_f ⊢
          preKeyRecordOut64At (s.sp + 0x3e0#64)
            spkPubCap spkPubPtr 33#64 spkPrivCap spkPrivPtr 32#64 spkSigCap spkSigPtr ∗
          ((coroPtr + 0x4f8#64) ↦₆₄ spkFutPtr) ∗
          ((coroPtr + 0x500#64) ↦₆₄ spkFutVt) ∗
          ((spkFutVt + 0x0#64) ↦₆₄ᵣ spkDropAddr) ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ v_98) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkFutPtr ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = spkFutPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x24 = spkFutVt ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = spkPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf98#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ne2 : ConditionHolds CondCode.NE (addsPState64 spkPubCap 2#64) = true :=
    p2_cond_ne_adds64_of_ne_neg2 hpub_ne_neg2
  have hcond_eq2 : ConditionHolds CondCode.EQ (addsPState64 spkPubCap 2#64) = false := by
    rw [conditionHolds_eq_addsPState64]; exact beq_eq_false_iff_ne.mpr (by bv_omega)
  have hdrop_beq : (spkDropAddr == 0#64) = false := beq_eq_false_iff_ne.mpr hdrop_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf38 0xf40
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf54 0xf94
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx21' : s.readReg64 (Reg.gpr 21#5) = v_b0 := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = v_a0 := hx23
  have hx26' : s.readReg64 (Reg.gpr 26#5) = v_98 := hx26
  dsimp only [preKeyRecordOut64At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1000000 in
theorem p2_seg2c_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr spkFutPtr spkFutVt spkPubCap spkPubPtr spkPrivPtr spkSigPtr : BitVec 64)
    (spkBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg1 : spkPubCap ≠ 0xffffffffffffffff#64)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64)
    (hbs_lt : spkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx23 : s.readReg64 .x23 = 33#64)
    (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = 32#64)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
       ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗
       memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr))
      (fun s1 P_f =>
        (P_f ⊢
          ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗
          ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = spkPubPtr ∧
        s1.readReg64 .x1 = 33#64 ∧
        s1.readReg64 .x2 = spkPrivPtr ∧
        s1.readReg64 .x3 = 32#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = spkPubCap ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hcond_eq1 : ConditionHolds CondCode.EQ (addsPState64 spkPubCap 1#64) = false :=
    p2_cond_eq_adds64_of_ne_neg1 hpub_ne_neg1
  have hcond_ne1 : ConditionHolds CondCode.NE (addsPState64 spkPubCap 1#64) = true := by
    rw [conditionHolds_ne_addsPState64]; exact bne_iff_ne.mpr (by bv_omega)
  have hbs_beq : (BitVec.ofNat 64 spkBoxSize == 0#64) = false := beq_eq_false_iff_ne.mpr hbs_nz
  have hbs_toNat : (BitVec.ofNat 64 spkBoxSize).toNat = spkBoxSize := Nat.mod_eq_of_lt hbs_lt
  have htarget :
      (tripleRatchetProgAtExt b ext).fnAddr
        "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" =
      (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2^64) := by
    simp [tripleRatchetProgAtExt, Program.fnAddr,
      ls_lemma% fnOff "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private",
      ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"]
  rw [htarget]
  closure_fetches_range_cli b (Rust.withPanics ext) 0xf98 0xfc8
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = spkFutPtr := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = 33#64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = spkFutVt := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = 32#64 := hx26
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  wp_steps
  wp_call hdealloc (spkFutPtr, spkBoxSize, 8)
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p2_seg2c_gen_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr spkFutPtr spkFutVt spkPubCap spkPubPtr spkPrivPtr spkSigPtr : BitVec 64)
    (spkBoxSize : Nat)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xf98#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_ne_neg1 : spkPubCap ≠ 0xffffffffffffffff#64)
    (hbs_nz : BitVec.ofNat 64 spkBoxSize ≠ 0#64) (hbs_lt : spkBoxSize < 2 ^ 64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx21 : s.readReg64 .x21 = spkFutPtr) (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx23 : s.readReg64 .x23 = 33#64) (hx24 : s.readReg64 .x24 = spkFutVt)
    (hx26 : s.readReg64 .x26 = 32#64) (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") s
      (((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗ ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
       A.live spkFutPtr spkBoxSize 8 ∗ memRegion spkFutPtr spkBoxSize ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr))
      (fun s1 P_f =>
        (P_f ⊢ ((spkFutVt + 0x8#64) ↦₆₄ᵣ BitVec.ofNat 64 spkBoxSize) ∗ ((spkFutVt + 0x10#64) ↦₆₄ᵣ 8#64) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = spkPubPtr ∧
        s1.readReg64 .x1 = 33#64 ∧ s1.readReg64 .x2 = spkPrivPtr ∧ s1.readReg64 .x3 = 32#64 ∧
        s1.readReg64 .x8 = s.sp + 0xa90#64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧ s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = 33#64 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = 32#64 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = spkPubCap ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg2c_hooks_wp b ext (.of_allocContracts hA) s coroPtr spkFutPtr spkFutVt spkPubCap spkPubPtr
    spkPrivPtr spkSigPtr spkBoxSize hpc hrun hsp_align hpub_ne_neg1 hbs_nz hbs_lt
    hx19 hx20 hx21 hx22 hx23 hx24 hx26 hx28

set_option maxHeartbeats 1200000 in
theorem p2_seg2d_sig0_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64)
    (hpriv_nz : spkPrivCap ≠ 0#64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1460#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hpub_beq : (spkPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hpriv_beq : (spkPrivCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpriv_nz
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0xfcc 0xfd4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x138c 0x145c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (spkPubPtr, spkPubCap.toNat, 1)
  wp_steps
  wp_call hdealloc (spkPrivPtr, spkPrivCap.toNat, 1)
  wp_steps
  rw [hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem p2_seg2d_sig0_gen_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64) (hpriv_nz : spkPrivCap ≠ 0#64) (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr) (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗ ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧ s1.readReg64 .x21 = v_b0 ∧ s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1460#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg2d_sig0_hooks_wp b ext (.of_allocContracts hA) s coroPtr msgPtr spkPubCap spkPubPtr
    spkPrivCap spkPrivPtr spkSigPtr kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 kyberPreKeyId
    b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c63 b_3e8
    w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6
    hpc hrun hsp_align hpub_nz hpriv_nz hkyber_nz hx19 hx20 hx22 hx28

set_option maxHeartbeats 1200000 in
theorem p2_seg2d_sigNz_hooks_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State))
    (hH : StageP2ClosureHooks A b ext)
    (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63
     s0 s1_b s2 s3 s4 s5 s6
     c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6
     cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64)
    (hpriv_nz : spkPrivCap ≠ 0#64)
    (hsig_nz : spkSigCap ≠ 0#64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr)
    (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt
         (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
       ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
       ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
       ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗
       ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.live spkSigPtr spkSigCap.toNat 1 ∗ memRegion spkSigPtr spkSigCap.toNat ∗
       A.pool ∗
       stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
       ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
       ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗
          ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗
          ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗
          ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗
          stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
          ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗
          ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧
        s1.readReg64 .x21 = v_b0 ∧
        s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1460#64 ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hdealloc := hH.dealloc
  have hpub_beq : (spkPubCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpub_nz
  have hpriv_beq : (spkPrivCap == 0#64) = false := beq_eq_false_iff_ne.mpr hpriv_nz
  have hsig_beq : (spkSigCap == 0#64) = false := beq_eq_false_iff_ne.mpr hsig_nz
  have hkyber_beq : (kyberCtCap == 0#64) = false := beq_eq_false_iff_ne.mpr hkyber_nz
  closure_fetches_range_cli b (Rust.withPanics ext) 0xfcc 0xfd4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x138c 0x145c
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = spkSigPtr := hx20
  have hx22' : s.readReg64 (Reg.gpr 22#5) = spkPubPtr := hx22
  have hx28' : s.readReg64 (Reg.gpr 28#5) = spkPubCap := hx28
  dsimp only [keyPair64UnalignedAt, bytes7At]
  conv =>
    arg 4
    simp (config := { maxSteps := 1000000 }) only [
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_call hdealloc (spkPubPtr, spkPubCap.toNat, 1)
  wp_steps
  wp_call hdealloc (spkPrivPtr, spkPrivCap.toNat, 1)
  wp_steps
  rw [hsp_sf]
  wp_call hdealloc (spkSigPtr, spkSigCap.toNat, 1)
  wp_steps
  rw [hsp_sf_1, hsp_sf]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem p2_seg2d_sigNz_gen_wp {A : RustAlloc} (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s : State) (coroPtr msgPtr spkPubCap spkPubPtr spkPrivCap spkPrivPtr spkSigCap spkSigPtr
    kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr v_a0 v_b0 u_3e0 : BitVec 64)
    (kyberPreKeyId : BitVec 32)
    (b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c63 b_3e8 : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0xfcc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hpub_nz : spkPubCap ≠ 0#64) (hpriv_nz : spkPrivCap ≠ 0#64) (hsig_nz : spkSigCap ≠ 0#64)
    (hkyber_nz : kyberCtCap ≠ 0#64)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = spkSigPtr)
    (hx22 : s.readReg64 .x22 = spkPubPtr) (hx28 : s.readReg64 .x28 = spkPubCap) :
    SepWP (tripleRatchetProgAtExt b ext) kyberLoadShimAddr s
      (((s.sp + 0xa90#64) ↦₈ 0#8) ∗
       keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
       bytes7At (s.sp + 0x930#64) s0 s1_b s2 s3 s4 s5 s6 ∗
       keyPair64UnalignedAt (coroPtr + 0x398#64) c0 c1 c2 c3 c4 c5 c6 cw0 cw1 cw2 cw3 cw4 cw5 cw6 c63 ∗
       ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
       ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ u_3e0) ∗ ((s.sp + 0x3e8#64) ↦₈ b_3e8) ∗
       A.live spkPubPtr spkPubCap.toNat 1 ∗ memRegion spkPubPtr spkPubCap.toNat ∗
       A.live spkPrivPtr spkPrivCap.toNat 1 ∗ memRegion spkPrivPtr spkPrivCap.toNat ∗
       A.live spkSigPtr spkSigCap.toNat 1 ∗ memRegion spkSigPtr spkSigCap.toNat ∗
       A.pool ∗ stackAt s.sp allocHookStack ∗
       ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
       ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr))
      (fun s1 P_f =>
        (P_f ⊢ ((s.sp + 0xa90#64) ↦₈ 0#8) ∗
          keyPair64UnalignedAt (s.sp + 0xa91#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          bytes7At (s.sp + 0x930#64) b0 b1 b2 b3 b4 b5 b6 ∗
          keyPair64UnalignedAt (coroPtr + 0x398#64) b0 b1 b2 b3 b4 b5 b6 w0 w1 w2 w3 w4 w5 w6 b63 ∗
          ((s.sp + 0x90#64) ↦₆₄ spkSigCap) ∗ ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ v_a0) ∗ ((s.sp + 0xb0#64) ↦₆₄ v_b0) ∗
          ((s.sp + 0xb8#64) ↦₆₄ spkPrivCap) ∗ ((s.sp + 0xd0#64) ↦₆₄ spkPrivPtr) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ w6) ∗ ((s.sp + 0x3e8#64) ↦₈ b63) ∗
          A.pool ∗ stackAt s.sp allocHookStack ∗
          ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗ ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗ ((msgPtr + 0x90#64) ↦₆₄ kyberCtCap) ∗
          ((msgPtr + 0xa0#64) ↦₃₂ kyberPreKeyId) ∗ ((kyberStoreVt + 0x18#64) ↦₆₄ᵣ kyberLoadShimAddr)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.readReg64 .x0 = kyberStorePtr ∧
        s1.readReg64 .x1 = kyberPreKeyId.zeroExtend 64 ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = spkSigPtr ∧ s1.readReg64 .x21 = v_b0 ∧ s1.readReg64 .x22 = spkPubPtr ∧
        s1.readReg64 .x23 = v_a0 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = coroPtr + 0x398#64 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.sp + 0xa90#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1460#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) :=
  p2_seg2d_sigNz_hooks_wp b ext (.of_allocContracts hA) s coroPtr msgPtr spkPubCap spkPubPtr
    spkPrivCap spkPrivPtr spkSigCap spkSigPtr kyberCtCap kyberStorePtr kyberStoreVt kyberLoadShimAddr
    v_a0 v_b0 u_3e0 kyberPreKeyId
    b0 b1 b2 b3 b4 b5 b6 b63 s0 s1_b s2 s3 s4 s5 s6 c0 c1 c2 c3 c4 c5 c6 c63 b_3e8
    w0 w1 w2 w3 w4 w5 w6 cw0 cw1 cw2 cw3 cw4 cw5 cw6
    hpc hrun hsp_align hpub_nz hpriv_nz hsig_nz hkyber_nz hx19 hx20 hx22 hx28

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
