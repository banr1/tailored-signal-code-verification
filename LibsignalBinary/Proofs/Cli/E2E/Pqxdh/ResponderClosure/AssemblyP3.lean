/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.StageP2a
import LibsignalBinary.Proofs.Cli.ShardFill.DropGlueErrorSignalProtocolErrorL3
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.MessageKey.Common
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.Entry

/-!
# Responder Closure Stage P3 Jump-Table & OOM-Aware `__rust_alloc` Wrappers

`.rodata` jump-table resolution, OOM panic tails (`+0x375c`, `+0x3768`, `+0x3774`, `+0x3798`),
and OOM-aware `__rust_alloc` wrappers (`+0x179c`, `+0x18fc`, `+0x1938`, `+0x1b48`, `+0x2eac`,
`+0x33b0`) for `message_decrypt_prekey::<Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap

open CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open CryptoVerification.LibsignalSession

open CryptoVerification.E2E.Pqxdh.ResponderStore

open DropGlueFacts

set_option maxRecDepth 200000

set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

/-! ## 1. `.rodata` Jump-Table Resolution for `drop_glue::<SignalProtocolError>` -/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.rodata_5a520_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) - num% (ls_xref% 0x2440 0x2444))).take 28 = speJumpTable := by
  rfl_kernel

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.rodata_5a526_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 0x1b#8) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) (secLen := 28) (dataOff := num% (ls_xref% 0x2440 0x2444))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rw [CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.rodata_5a520_eq] at h
  have hsplit : ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable) =
      ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take 6) ∗
        ((((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 6) ↦₈ᵣ 0x1b#8) ∗
         (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) + BitVec.ofNat 64 6 + 1#64) ↦ᵣ speJumpTable.drop 7)) := by
    conv_lhs =>
      rw [show speJumpTable = speJumpTable.take 6 ++ (0x1b#8 :: speJumpTable.drop 7) from rfl]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons,
        show (speJumpTable.take 6).length = 6 from rfl]
  have hadd : img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44)) + BitVec.ofNat 64 6 = img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6) := by
    rw [BitVec.add_assoc]; rfl
  rw [hsplit, hadd] at h
  have hdrop :
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take 6) ∗
        (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 0x1b#8) ∗
         (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) + 1#64) ↦ᵣ speJumpTable.drop 7))) ∗ P =
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44))) ↦ᵣ speJumpTable.take 6) ∗
        (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) + 1#64) ↦ᵣ speJumpTable.drop 7)) ∗
      (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 0x1b#8) ∗ P) := by ac_rfl
  rw [hdrop] at h
  exact Satisfies.of_sep_right h

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWP.intro_rodata_5a526 {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {target_pc : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop}
    (hro : img.RoDataLoaded s.mem)
    (h : SepWP prog target_pc s (((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 0x1b#8) ∗ P) post) :
    SepWP prog target_pc s P post := by
  unfold SepWP at h ⊢
  intro R hm
  have hR := h R
  rw [sepConj_assoc] at hR
  exact hR (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.rodata_5a526_intro himg hro hm)

/-- The `adrp` at `drop_glue::<SignalProtocolError> [local#3] + 40` resolves to the `speJumpTable` page. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.speJumpTable_adrp_eq {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))) :
    (entry + 40#64 &&& 18446744073709547520#64) = base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) := by
  subst he
  have hadd : base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) + 40#64 = base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40)) := by
    rw [BitVec.add_assoc]; rfl
  rw [hadd, adrp_page_of_aligned hb]
  rfl

set_option maxHeartbeats 1200000 in
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.drop_spe2_ver_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (img.base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")))
      ((dropSpeVerSpec A).inImage img) := by
  simp only [Spec.inImage, dropSpeVerSpec, pure_sepConj_pure_assoc]
  have hfn_eq :
      (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.dropSpe2Name = img.base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")) := by
    simp only [trTrapProgAt, CryptoVerification.Cli.dropSpe2Name, Program.fnAddr_rebase,
      (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")]
  rw [← hfn_eq]
  clear hfn_eq
  code_fetches libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBinCli img.base
    (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") 184
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hadp : (
      ((libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C abs))).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" +
        40#64) &&&
      18446744073709547520#64) = img.base + (bv% (page% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40))) :=
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.speJumpTable_adrp_eq hb (fnAddr_rebase_eq_add_of_fnOff (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]"))
  dsimp only [trTrapProgAt, CryptoVerification.Cli.dropSpe2Name, BitVec.ofNat_eq_ofNat] at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" = entry
  examples_hide_fetches
  wp_init x s0
  obtain ⟨a, msgVer⟩ := x
  dsimp only at *
  subst h
  have hro : img.RoDataLoaded s0.mem := (Obj.Image.frozenLoaded_iff.mp h_2).2.1
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.SepWP.intro_rodata_5a526 himg hro ?_
  nth_rw 1 [stackAt_dropSpe_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i fp lr x20 x19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨fun hm => ?_, by simp_all [arm64_norm], by simp_all [CalleeSavedPreserved, arm64_norm]⟩
  rw [satisfies_pure_sepConj]
  refine ⟨by simp_all [arm64_norm], ?_⟩
  have ha := spe_ver_entails_48 (s0.readReg64 (Reg.gpr 0#5)) msgVer
  have hst := cells4_entails_dropSpeStack s0.sp
    (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
    (s0.readReg64 (Reg.gpr 20#5)) (s0.readReg64 (Reg.gpr 19#5))
  rw [sepConj_assoc ((img.base + bv% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]" + 44) + 6)) ↦₈ᵣ 27#8)] at hm
  have hm1 := Satisfies.of_sep_right hm
  have hent :
      (s0.readReg64 (Reg.gpr 0#5) ↦₆₄ 9223372036854775814#64 ∗
        (s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₃₂ msgVer ∗
          memRegion (s0.readReg64 (Reg.gpr 0#5) + 12#64) 36 ∗
            A.pool ∗
              stackAt (s0.sp - 32#64) allocHookStack ∗
                (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
                  (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
                    (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
                      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ⊢
      memRegion (s0.readReg64 (Reg.gpr 0#5)) 48 ∗ A.pool ∗ stackAt s0.sp dropSpeStack :=
    Entails.trans
      (Q := (((s0.readReg64 (Reg.gpr 0#5)) ↦₆₄ 0x8000000000000006#64) ∗
             ((s0.readReg64 (Reg.gpr 0#5) + 8#64) ↦₃₂ msgVer) ∗
             memRegion (s0.readReg64 (Reg.gpr 0#5) + 12#64) 36) ∗
            A.pool ∗
            (stackAt (s0.sp - 32#64) allocHookStack ∗
             ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
             ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5)) ∗
             ((s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))))
      (Entails.of_eq (by ac_rfl))
      (sepConj_mono ha (sepConj_mono (Entails.refl A.pool) hst))
  have hm2 := Satisfies.mono (sepConj_mono_left hent) hm1
  simpa only [sepConj_assoc] using hm2

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.drop_spe2_ver_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (img.base + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")))
      ((dropSpeVerSpec A).inImage img) :=
  subroutine_ok_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.drop_spe2_ver_ok_trap himg)

/-!
## 2. OOM-Aware `__rust_alloc` Wrappers (`+0x179c`, `+0x18fc`, `+0x1938`, `+0x1b48`, `+0x2eac`, `+0x33b0`)
-/

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error_trap (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State)) :
    (trTrapProgAt b C abs).externAt?
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_norm_trap (b := b) (C := C) (abs := abs)
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))

/-- `alloc::raw_vec::handle_error` stub at `decryptPrekeyClosureName + 0x6a54` (`0x78a60`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).externAt?
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) =
      some Rust.panicked :=
  panic_at_handle_error_norm (b := b) (C := C) (ctl := ctl) (abs := abs)
    (name := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName) (k := num% (ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")))

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_375c_ok_trap (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x375c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicOomProp s0) := by
  have hpanic := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error_trap b C abs
  have hstep : SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x375c 0x3764
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/-- OOM panic tail at `+0x375c` (`+14172..0x7576c`): `mov w0, #1; mov x1, x26; bl handle_error`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_375c_ok (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x375c#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_375c_ok_trap img b C abs s0 s ret P Q hF hsym hpc hrun htr)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3768_ok_trap (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3768#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicOomProp s0) := by
  have hpanic := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error_trap b C abs
  have hstep : SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3768 0x3770
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/-- OOM panic tail at `+0x3768` (`+14184..0x75778`): `mov w0, #1; mov x1, x24; bl handle_error`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3768_ok (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3768#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3768_ok_trap img b C abs s0 s ret P Q hF hsym hpc hrun htr)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3774_ok_trap (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s0 s : State) (ret v_d0 : BitVec 64) (F : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3774#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s
      (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) Q (PanicOomProp s0) := by
  have hpanic := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error_trap b C abs
  have hstep : SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s
      ((s.sp + 0xd0#64) ↦₆₄ v_d0)
      (fun s1 P_f => (P_f ⊢ (s.sp + 0xd0#64) ↦₆₄ v_d0) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3774 0x377c
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine SepWPp.bind_sepWP_frame hF hsym hstep rfl
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/-- OOM panic tail at `+0x3774` (`+14196..0x75784`):
`ldr x1, [sp, #0xd0]; mov w0, #1; bl handle_error`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3774_ok (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s0 s : State) (ret v_d0 : BitVec 64) (F : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3774#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s
      (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) Q (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3774_ok_trap img b C abs s0 s ret v_d0 F Q hF hsym hpc hrun hsp_align htr)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3798_ok_trap (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3798#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (trTrapProgAt b C abs) ret s P Q (PanicOomProp s0) := by
  have hpanic := CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.decryptPrekeyClosure_panic_at_handle_error_trap b C abs
  have hstep : SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "alloc::raw_vec::handle_error" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x3798 0x37a0
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

/-- OOM panic tail at `+0x3798` (`+14232..0x757a8`): `mov w0, #1; mov w1, #0x11; bl`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3798_ok (img : Obj.Image) (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x3798#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3798_ok_trap img b C abs s0 s ret P Q hF hsym hpc hrun htr)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧
        s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 =
          (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off))
    (hcbz : ∀ s2 : State,
      s2.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off →
      s2.status = .Running →
      s2.readReg64 .x0 = 0#64 →
      SepWP (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace))
    (hoom_tail : ∀ s3 : State,
      img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off →
      s3.status = .Running →
      s3.sp = s.sp →
      s3.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (trTrapProgAt b C abs)
        ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s3
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (PanicOomProp s0)) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine SepWPp.bind_sepWP_frame hF hsym hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : LayoutOk sz 1 := ⟨hsz_pos, ⟨0, rfl⟩, by omega⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk sz 1 :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay⟩
  refine SepWPp.call_frame_frozen_nopanic (spec := rustAllocSpec A) (x := (sz, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hF1 hsym1 (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_alloc_ok_trap hA) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]
  rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine SepWPp.bind_sepWP_frame hF2 hsym2 (hcbz s2 hpc2 hrun2 hoom) (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact hoom_tail s3 hF3 hsym3 hpc3 hrun3 (hsp3.trans hsp2) (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hF2, hsym2⟩

/-- Generic OOM-aware `__rust_alloc(sz, 1)` call wrapper for `decryptPrekeyClosure`. -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧
        s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off))
    (hcbz : ∀ s2 : State,
      s2.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off →
      s2.status = .Running →
      s2.readReg64 .x0 = 0#64 →
      SepWP (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace))
    (hoom_tail : ∀ s3 : State,
      img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + oom_off →
      s3.status = .Running →
      s3.sp = s.sp →
      s3.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (tripleRatchetProgAt b C ctl abs)
        ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s3
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine SepWPp.bind_sepWP_frame hF hsym hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : LayoutOk sz 1 := ⟨hsz_pos, ⟨0, rfl⟩, by omega⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk sz 1 :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay⟩
  refine SepWPp.call_frame_frozen_nopanic (spec := rustAllocSpec A) (x := (sz, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hF1 hsym1 (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosure_alloc_ok hA) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]
  rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine SepWPp.bind_sepWP_frame hF2 hsym2 (hcbz s2 hpc2 hrun2 hoom) (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact hoom_tail s3 hF3 hsym3 hpc3 hrun3 (hsp3.trans hsp2) (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hF2, hsym2⟩

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_179c_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (v_d0 : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F))
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F)) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x17a0#64 0x3774#64 sz
    (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x179c 0x179c
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x17a0 0x17a0
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 hsp3 htr3
    have halign3 : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
    rw [show (A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F) =
      ((s3.sp + 0xd0#64) ↦₆₄ v_d0) ∗ ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F) by
      rw [hsp3]; ac_rfl]
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3774_ok_trap img b C abs s0 s3 _ v_d0 _ _ hF3 hsym3 hpc3 hrun3 halign3 htr3

/-- OOM-aware `__rust_alloc(sz, 1)` at `+0x179c -> +0x17a0` (OOM jumps to `+0x3774`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_179c_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (v_d0 : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x179c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x17a0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F))
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ (((s.sp + 0xd0#64) ↦₆₄ v_d0) ∗ F)) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_179c_ok_trap img b C abs hA s0 s v_d0 sz F hsz_pos hsz_lt hF hsym hpc hrun hsp_align htr hx0 hx1)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_18fc_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x1900#64 0x3768#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x18fc 0x18fc
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1900 0x1900
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3768_ok_trap img b C abs s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

/-- OOM-aware `__rust_alloc(sz, 1)` at `+0x18fc -> +0x1900` (OOM jumps to `+0x3768`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_18fc_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x18fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1900#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_18fc_ok_trap img b C abs hA s0 s sz F hsz_pos hsz_lt hF hsym hpc hrun hsp_align htr hx0 hx1)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1938_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x193c#64 0x375c#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1938 0x1938
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x193c 0x193c
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_375c_ok_trap img b C abs s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

/-- OOM-aware `__rust_alloc(sz, 1)` at `+0x1938 -> +0x193c` (OOM jumps to `+0x375c`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1938_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1938#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x193c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1938_ok_trap img b C abs hA s0 s sz F hsz_pos hsz_lt hF hsym hpc hrun hsp_align htr hx0 hx1)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1b48_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x1b4c#64 0x3768#64 sz
    F hsz_pos hsz_lt hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b48 0x1b48
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x1b4c 0x1b4c
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3768_ok_trap img b C abs s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

/-- OOM-aware `__rust_alloc(sz, 1)` at `+0x1b48 -> +0x1b4c` (OOM jumps to `+0x3768`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1b48_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b48#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 sz)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1b4c#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_1b48_ok_trap img b C abs hA s0 s sz F hsz_pos hsz_lt hF hsym hpc hrun hsp_align htr hx0 hx1)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_2eac_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2eac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2eb0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x2eb0#64 0x3798#64 17
    F (by decide) (by decide) hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x2eac 0x2eac
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x2eb0 0x2eb0
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3798_ok_trap img b C abs s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

/-- OOM-aware `__rust_alloc(17, 1)` at `+0x2eac -> +0x2eb0` (OOM jumps to `+0x3798`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_2eac_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2eac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x2eb0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_2eac_ok_trap img b C abs hA s0 s F hF hsym hpc hrun hsp_align htr hx0 hx1)

theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_33b0_ok_trap {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  refine CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_call_ok_trap img b C abs hA s0 s 0x33b4#64 0x3798#64 17
    F (by decide) (by decide) hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x33b0 0x33b0
    dsimp only [trTrapProgAt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics (trTrapExterns C abs)) 0x33b4 0x33b4
    dsimp only [trTrapProgAt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b
      (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_oom_tail_3798_ok_trap img b C abs s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

/-- OOM-aware `__rust_alloc(17, 1)` at `+0x33b0 -> +0x33b4` (OOM jumps to `+0x3798`). -/
theorem _root_.CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_33b0_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64) (C : Crypto)
    (ctl : BitVec 64) (abs : String → Option (State → State))
    (hA : AllocHooks A abs)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64)
    (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (PanicOomProp s0) := by
  simp only [← trTrapProgAt_fnAddr_eq b C ctl abs] at hpc ⊢
  exact SepWPp_kit_of_trTrap
    (CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.P3P4.p3_alloc_33b0_ok_trap img b C abs hA s0 s F hF hsym hpc hrun hsp_align htr hx0 hx1)

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
