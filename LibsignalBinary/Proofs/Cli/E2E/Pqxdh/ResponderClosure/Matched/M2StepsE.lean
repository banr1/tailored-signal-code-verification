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
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1UntrustedAux
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P2 Matched-Session Mismatch Funnel Blocks

`tripleRatchetProgAtExt b ext` basic blocks `+0x1310 → drop_process_prekey_impl_state1` and
`+0x1698 → +0x3588` specialized to `InvalidMessage(.preKey)` (`errTag = 0x8000000000000018#64`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_cap_lo32_lsr8 (cap : BitVec 64) :
    ((cap.extractLsb' 0 32).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_setWidth32_lsr8 (cap : BitVec 64) :
    ((BitVec.setWidth 32 cap).zeroExtend 64 &&& 255#64 |||
      (cap >>> 8 &&& 72057594037927935#64) <<< 8) = cap := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem setWidth32_hi_lo_append (w : BitVec 64) :
    BitVec.setWidth 32 (w >>> 32) ++ BitVec.setWidth 32 w = w := by
  bv_bits

@[local simp, local wp_norm, local arm64_norm]
private theorem bfi_3_zero :
    ((3#64 : BitVec 64) &&& 255#64 |||
      ((0#64 : BitVec 64) &&& 72057594037927935#64) <<< 8) = 3#64 := by
  decide

private theorem coro_268_split32_m2e (coroPtr w : BitVec 64) :
    (coroPtr + 0x268#64) ↦₆₄ w =
    ((coroPtr + 0x268#64) ↦₃₂ w.extractLsb' 0 32) ∗
    ((coroPtr + 0x26c#64) ↦₃₂ w.extractLsb' 32 32) := by
  rw [pointsTo64_split32, BitVec.add_assoc]; rfl

private theorem coro_268_pair32_m2e (coroPtr : BitVec 64) (lo hi : BitVec 32) :
    ((coroPtr + 0x268#64) ↦₃₂ lo) ∗ ((coroPtr + 0x26c#64) ↦₃₂ hi) =
    (coroPtr + 0x268#64) ↦₆₄ (hi ++ lo) := by
  have hlo : (hi ++ lo).extractLsb' 0 32 = lo := by bv_bits
  have hhi : (hi ++ lo).extractLsb' 32 32 = hi := by bv_bits
  rw [coro_268_split32_m2e coroPtr (hi ++ lo), hlo, hhi]

/-- `+0x1310 → drop_process_prekey_impl_state1` on the mismatch error path
(`errTag = speWord 24`). -/
theorem p2_seg_1310_to_drop_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr cap ptr len u_a8 u_c8 u_d0 : BitVec 64)
    (b_4f2 : BitVec 8)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1310#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((s.sp + 0xc8#64) ↦₆₄ u_c8) ∗
       ((s.sp + 0xd0#64) ↦₆₄ u_d0) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
       ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
       ((s.sp + 0x3f0#64) ↦₆₄ len))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((s.sp + 0x3e0#64) ↦₆₄ cap) ∗
          ((s.sp + 0x3e8#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x3f0#64) ↦₆₄ len)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ s1.vregs = s.vregs ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = 0x8000000000000018#64 ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = ptr ∧
        s1.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x24 = cap ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 3#64) = true :=
    cond_ne_adds64_of_ne_neg3_std3 (by decide)
  have hsplit_cap :
      ((s.sp + 0x3e0#64) ↦₆₄ cap) =
        ((s.sp + 0x3e0#64) ↦₃₂ cap.extractLsb' 0 32) ∗
        ((s.sp + 0x3e4#64) ↦₃₂ cap.extractLsb' 32 32) := by
    rw [pointsTo64_split32 (s.sp + 0x3e0#64) cap]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1310 0x1340
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1678 0x1694
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1694#64 + bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 5780)) % 2 ^ 64) =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") := by
    rw [hentry]; simp only [BitVec.add_assoc]; rfl
  rw [← htarget]
  clear hentry htarget
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  apply SepWP.fold (Entails.of_eq hsplit_cap) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq hsplit_cap.symm) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm],
    by simp_all [arm64_norm]; clear * -; bv_bits,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

set_option maxHeartbeats 1200000 in
/-- `+0x1698 → +0x3588` on the mismatch error path at generic `ext`. -/
theorem p2_seg_1698_mismatch_to_3588_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr cap ptr len
    u_250 u_258 u_260 u_268 u_270 u_278
    u_a90 u_a98 u_aa0 u_aa8 u_ab0 u_ab8
    u_370 u_378 u_380 u_388 : BitVec 64)
    (u_390 : BitVec 32) (b_390 : BitVec 8)
    (hb : b &&& 0xfff#64 = 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = 0x8000000000000018#64)
    (hx21 : s.readReg64 .x21 = 0#64)
    (hx22 : s.readReg64 .x22 = ptr)
    (hx23 : s.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64)
    (hx24 : s.readReg64 .x24 = cap)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = s.sp + 0xa90#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3588#64) s
      (((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0xd0#64) ↦₆₄ len) ∗
       ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x250#64) ↦₆₄ u_250) ∗ ((coroPtr + 0x258#64) ↦₆₄ u_258) ∗
       ((coroPtr + 0x260#64) ↦₆₄ u_260) ∗ ((coroPtr + 0x268#64) ↦₆₄ u_268) ∗
       ((coroPtr + 0x270#64) ↦₆₄ u_270) ∗ ((coroPtr + 0x278#64) ↦₆₄ u_278) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((s.sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((s.sp + 0xa98#64) ↦₆₄ u_a98) ∗
       ((s.sp + 0xaa0#64) ↦₆₄ u_aa0) ∗ ((s.sp + 0xaa8#64) ↦₆₄ u_aa8) ∗
       ((s.sp + 0xab0#64) ↦₆₄ u_ab0) ∗ ((s.sp + 0xab8#64) ↦₆₄ u_ab8) ∗
       ((s.sp + 0x370#64) ↦₆₄ u_370) ∗ ((s.sp + 0x378#64) ↦₆₄ u_378) ∗
       ((s.sp + 0x380#64) ↦₆₄ u_380) ∗ ((s.sp + 0x388#64) ↦₆₄ u_388) ∗
       ((s.sp + 0x390#64) ↦₃₂ u_390))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xa8#64) ↦₆₄ 3#64) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0xd0#64) ↦₆₄ len) ∗
          ((b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          ((coroPtr + 0x250#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((coroPtr + 0x258#64) ↦₆₄ cap) ∗ ((coroPtr + 0x260#64) ↦₆₄ ptr) ∗
          ((coroPtr + 0x268#64) ↦₆₄ len) ∗ ((coroPtr + 0x270#64) ↦₆₄ 3#64) ∗
          ((coroPtr + 0x278#64) ↦₆₄ s.readReg64 .x27) ∗ ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((s.sp + 0xa90#64) ↦₆₄ 0x8000000000000018#64) ∗
          ((s.sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
          ((s.sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0xaac#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0xab4#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((s.sp + 0xabc#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32) ∗
          ((s.sp + 0x370#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
          ((s.sp + 0x378#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
          ((s.sp + 0x380#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
          ((s.sp + 0x388#64) ↦₆₄ ((s.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
          ((s.sp + 0x390#64) ↦₃₂ (s.readReg64 .x27).extractLsb' 32 32)) ∧
        s1.sp = s.sp ∧ s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x22 = (cap.extractLsb' 0 32).zeroExtend 64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x28 = 0x8000000000000018#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = s.readReg64 .x30) := by
  have hcond : ConditionHolds CondCode.NE (addsPState64 0x8000000000000018#64 2#64) = true :=
    cond_ne_adds64_of_ne_neg2_std3 (by decide)
  have hrealign_a98 := realign_40 (s.sp + 0xa98#64) cap ptr len 3#64 (s.readReg64 (Reg.gpr 27#5))
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrealign_a98
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1698 0x169c
  closure_fetches_range_cli b (Rust.withPanics ext) 0x16b4 0x16f4
  closure_fetches_range_cli b (Rust.withPanics ext) 0x17b8 0x17d8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1898 0x18b4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_logLevel_0x17bc_std3 hb hentry).1
  have hadrp := (adrp_logLevel_0x17bc_std3 hb hentry).2
  have h5b810 :
      (b + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256))) +
        bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
    bv_arith
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = 0x8000000000000018#64 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = 0#64 := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = ptr := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = (cap.extractLsb' 0 32).zeroExtend 64 := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = cap := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = s.sp + 0x210#64 := hx25
  have hx28' : s.readReg64 (Reg.gpr 28#5) = s.sp + 0xa90#64 := hx28
  apply SepWP.fold (Entails.of_eq (coro_268_split32_m2e coroPtr u_268)) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  apply SepWP.fold (Entails.of_eq (coro_268_pair32_m2e coroPtr _ _)) (by sep_focus)
  wp_simp_pre [sepConj_assoc, setWidth32_hi_lo_append]
  wp_steps
  apply SepWP.fold (Entails.of_eq hrealign_a98) (by sep_focus)
  wp_simp_pre [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by dsimp only [Reg.x27]; sep_frame,
    rfl, rfl, by simp [calleeSavedVRegs, arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
