/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSessionStructure3
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.DropSpe2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Fetch
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3GenBlocks
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.TripleRatchet.Alloc.FinishGrow
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Version-Mismatch Closure Constants and Allocator Bridges

Symbol aliases, program equivalences (`contractProg = tripleRatchetProgAtExt`), the `.bss`
`MAX_LOG_LEVEL_FILTER` cell (`pqLogLevelCell`), and 4 KiB-to-16 KiB external-contract bridges
(`AllocContractsMem4K` to `AllocContractsX`) for the CLI PQXDH responder closure
`message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}` on the `msgVer ≠ 4` path.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

abbrev closureSymName : String :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName

abbrev pqxdhLogClosureSym : String :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.pqxdhLogClosureName

abbrev growOneSpeSym : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"

abbrev dropSessionStructure3Sym : String :=
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name

abbrev dropSpe2Sym : String :=
  CryptoVerification.Cli.dropSpe2Name

theorem contractProg_eq_tripleRatchetProgAtExt (b : BitVec 64)
    (ext : String → Option (State → State)) :
    contractProg b ext = tripleRatchetProgAtExt b ext :=
  rfl

theorem sp2Ext_eq_tripleRatchetProgAtExt (b : BitVec 64)
    (ext : String → Option (State → State)) :
    Proofs.libsignal.Hooks2.SP2Ext b ext = tripleRatchetProgAtExt b ext :=
  rfl

/-- CLI `.bss` `MAX_LOG_LEVEL_FILTER` 8-byte zero cell (`WHITESPACE_MAP + 256`). -/
def pqLogLevelCell (b : BitVec 64) : SepProp :=
  (b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64

theorem logOff_eq_pqLogLevelCell (img : Obj.Image) :
    logOff img = pqLogLevelCell img.base :=
  rfl

theorem fnAddr_closure_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]

theorem fnAddr_pqxdhLogClosure_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr pqxdhLogClosureSym =
      b + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}") := by
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")]

theorem fnAddr_growOneSpe_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr growOneSpeSym =
      b + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one") := by
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")]

theorem fnAddr_dropSs3_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructure3Sym =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]") := by
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")]

theorem fnAddr_dropSpe2_eq (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr dropSpe2Sym =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]") := by
  rw [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#2]")]

theorem allocContractsX_of_allocContracts {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) :
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext :=
  CryptoVerification.LibsignalTripleRatchet.AllocContractsX.of_AllocContracts hA

/-! ## 4 KiB-stack closure stub and OOM-alloc bridges -/

theorem closure_alloc_ok_of_mem4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_alloc" -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustAllocSpec A) :=
  hA.alloc_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_alloc" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))

theorem closure_dealloc_ok_of_mem4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      (rustDeallocSpec A) :=
  hA.dealloc_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_dealloc" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))

theorem closure_shim_ok_of_mem4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName +
        bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))
      sessionShimSpec :=
  hA.shim_ok_at decryptPrekeyClosureName
    (num% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64))

theorem drop_session_structure3_ok_of_mem4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructure3Name)
      (CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Spec A) :=
  drop_session_structure3_of_dealloc_ext hA.dealloc

theorem finish_grow_ok_of_mem4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContractsMem4K b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowName)
      (finishGrowSpec A) := by
  open SepProp in
  refine subroutine_ok_of_optNone
    (finish_grow_ok_of_hooks_opt (by decide) ?_ ?_ ?_)
  · apply subroutine_ok_to_optNone
    have h := subroutine_ok_withStack_of_subroutine_ok
      (hA.shim_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
      allocHookStack
    refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
    have hpre' : s0.mem ⊨ (withStack sessionShimSpec allocHookStack).pre x s0 ∗ R := by
      dsimp only [withStack, sessionShimSpec, shimSpecWithStack] at hpre ⊢
      simpa only [emp_sepConj, sepConj_assoc] using hpre
    exact h.mono_outcome x R s0 hpc hrun hpre' hal fun _ hout => hout
  · exact subroutine_ok_to_optNone
      (hA.alloc_ok_at finishGrowName
        (num% (ls_off% "__rustc::__rust_alloc" -
          ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
  · exact subroutine_ok_to_optNone
      (rustReallocExternWithStack_of_rustRealloc
        (hA.realloc_ok_at finishGrowName
          (num% (ls_off% "__rustc::__rust_realloc" -
            ls_off% "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]")))
        (by decide) (by decide))

section Alloc33b0

open SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")

theorem p3_alloc_call_mem4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) % 2^64)) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off))
    (hcbz : ∀ s2 : State,
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off →
      s2.status = .Running → s2.readReg64 .x0 = 0#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + oom_off) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace))
    (hoom_tail : ∀ s3 : State,
      img.FrozenLoaded s3 → s3.symtab = img.symtab →
      s3.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + oom_off →
      s3.status = .Running → s3.sp = s.sp → s3.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off) s3
        ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
        (fun s2 P_f =>
          (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                  A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
          s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
          CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
        (P3P4.PanicOomProp s0)) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hbl (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hF1 hsym1 ⟨hsp1, htr1, hx0_1, hx1_1, hcs1, hlr1⟩ => ?_
  have hsp1_al : s1.spAligned = true := by simpa [State.spAligned, hsp1] using hsp_align
  have hsz_nat : (BitVec.ofNat 64 sz).toNat = sz := Nat.mod_eq_of_lt (by omega)
  have hlay : LayoutOk sz 1 := ⟨hsz_pos, ⟨0, rfl⟩, by omega⟩
  have hφ : (s1.readReg64 .x0).toNat = sz ∧ (s1.readReg64 .x1).toNat = 1 ∧ LayoutOk sz 1 :=
    ⟨by rw [hx0_1, hsz_nat], by rw [hx1_1]; rfl, hlay⟩
  refine P3P4.SepWPp.call_frame_frozen_nopanic (spec := rustAllocSpec A) (x := (sz, 1))
    (T := A.pool ∗ stackAt s.sp allocHookStack) (F := F)
    hF1 hsym1 (closure_alloc_ok_of_mem4k hA) hpc1 hrun1 hsp1_al hlr1
    (by dsimp only [rustAllocSpec]; rw [hsp1])
    hφ (emp_sepConj _) (hnext := fun s2 hpc2 hrun2 hsp2_1 _ hcs2 hF2 hsym2 => ?_)
  have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
  have hcs : CalleeSavedPreserved s s2 := hcs1.trans hcs2
  dsimp only [rustAllocSpec]
  rw [hsp1]
  by_cases hoom : s2.readReg64 .x0 = 0#64
  · have hoom0 : (s2.readReg64 .x0 = 0) = True := eq_true hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
    refine SepWPp.pure_elim fun htr2 => ?_
    refine P3P4.SepWPp.bind_sepWP_frame hF2 hsym2 (hcbz s2 hpc2 hrun2 hoom) (emp_sepConj _).symm
      fun s3 hpc3 hrun3 hF3 hsym3 ⟨hsp3, htr3⟩ => ?_
    rw [emp_sepConj, ← sepConj_assoc]
    exact hoom_tail s3 hF3 hsym3 hpc3 hrun3 (hsp3.trans hsp2) (by rw [htr3, htr2, htr1, htr])
  · have hoom0 : (s2.readReg64 .x0 = 0) = False := eq_false hoom
    simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_ok]
    refine SepWPp.pure_elim fun ⟨_, htr2⟩ => ?_
    refine SepWPp.done hpc2 hrun2
      ⟨Entails.of_eq (by ac_rfl), hoom, hsp2, htr2.trans htr1, hcs, hF2, hsym2⟩

set_option maxHeartbeats 800000 in
theorem p3_alloc_33b0_mem4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x33b0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x33b4#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine p3_alloc_call_mem4k_ok img b ext hA s0 s 0x33b4#64 0x3798#64 17
    F (by decide) (by decide) hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x33b0 0x33b0
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x33b4 0x33b4
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact p3_oom_tail_3798_ext_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

end Alloc33b0

section Mem4KToX

open SepProp CryptoGames.LibsignalSession CryptoVerification.LibsignalSessionRepr

private theorem subroutine_ok_conseq_pure {α : Type} {P : Program} {addr : BitVec 64}
    {s1 s2 : Spec α} (h : subroutine_ok P addr s1)
    (hpre : ∀ x R s0, s0.mem ⊨ s2.pre x s0 ∗ R → s0.mem ⊨ s1.pre x s0 ∗ R)
    (hpost : ∀ x R s0 sf, sf.mem ⊨ s1.post x s0 sf ∗ R → sf.mem ⊨ s2.post x s0 sf ∗ R)
    (hpan : ∀ x s0 sf, s1.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, s1.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, s1.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr s2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hal => ?_
  refine h.mono_outcome x R s0 hpc hrun (hpre x R s0 hp) hal ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨_, hp'⟩ | ⟨code, _, he'⟩ | ⟨_, ho'⟩)
  · exact Or.inl ⟨hret, hcc, hpost x R s0 sf hq⟩
  · rw [hpan x s0 sf, satisfies_pure_sepConj] at hp'; exact False.elim hp'.1
  · rw [hex x code s0 sf, satisfies_pure_sepConj] at he'; exact False.elim he'.1
  · rw [hoom x s0 sf, satisfies_pure_sepConj] at ho'; exact False.elim ho'.1

private theorem subroutine_ok_stack_mono {α : Type} {P : Program} {addr : BitVec 64}
    {base : Spec α} {s1 s2 : Nat} (h : subroutine_ok P addr (withStack base s1))
    (hle : s1 ≤ s2) (hmax : s2 ≤ 2 ^ 64)
    (hpan : ∀ x s0 sf, base.onPanic x s0 sf = ⌜False⌝ := by intros; rfl)
    (hex : ∀ x code s0 sf, base.onExit x code s0 sf = ⌜False⌝ := by intros; rfl)
    (hoom : ∀ x s0 sf, base.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok P addr (withStack base s2) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  have hsplit : stackAt s0.sp s2 =
      memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ stackAt s0.sp s1 := by
    have h1 := stackAt_split_bottom s0.sp s1 (s2 - s1) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 s2) (s2 - s1) ∗ R
  have hpre' : s0.mem ⊨ (withStack base s1).pre x s0 ∗ R' := by
    dsimp only [withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine h.mono_outcome x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨code, _, he⟩ | ⟨_, ho⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [withStack] at hp; rw [hpan x s0 sf, satisfies_pure_sepConj] at hp
    exact False.elim hp.1
  · dsimp only [withStack] at he; rw [hex x code s0 sf, satisfies_pure_sepConj] at he
    exact False.elim he.1
  · dsimp only [withStack] at ho; rw [hoom x s0 sf, satisfies_pure_sepConj] at ho
    exact False.elim ho.1

private theorem sessionMemcpy_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemcpySpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemcpySpec stk) := by
  have h1 : subroutine_ok P addr (withStack sessionMemcpyRegionSpec allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
        sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
        sessionMemcpyRegionSpec, sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
      sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
      sessionMemcpyRegionSpec, sepConj_assoc] using hq)

private theorem libcMemcpy_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemcpySpec stk)) :
    subroutine_ok P addr (libcMemcpySpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemcpySpec, libcMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

private theorem sessionMemmove_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemmoveSpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemmoveSpec stk) := by
  let base : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat × Nat) :=
    { pre := fun (b, buf, dst, src, len) s0 =>
        ⌜s0.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧
         s0.readReg64 .x1 = b + BitVec.ofNat 64 src ∧
         (s0.readReg64 .x2).toNat = len ∧
         dst + len ≤ buf.length ∧ src + len ≤ buf.length⌝ ∗ (b ↦ₛ buf)
      post := fun (b, buf, dst, src, len) s0 sf =>
        ⌜sf.readReg64 .x0 = b + BitVec.ofNat 64 dst ∧ sf.trace = s0.trace⌝ ∗
          (b ↦ₛ listMove buf dst src len) }
  have h1 : subroutine_ok P addr (withStack base allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
        sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemmoveSpec, libcMemmoveSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemmoveSpec, withStack, base,
      sepConj_assoc] using hq)

private theorem libcMemmove_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemmoveSpec stk)) :
    subroutine_ok P addr (libcMemmoveSpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemmoveSpec, libcMemmoveSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

private theorem sessionMemset_mono {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemsetSpec allocHookStack))
    (hle : allocHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    subroutine_ok P addr (sessionMemsetSpec stk) := by
  let base : Spec (BitVec 64 × BitVec 8 × Nat) :=
    { pre := fun (ptr, c, len) s0 =>
        ⌜s0.readReg64 .x0 = ptr ∧ (s0.readReg32 .x1).truncate 8 = c ∧
         (s0.readReg64 .x2).toNat = len⌝ ∗ memRegion ptr len
      post := fun (ptr, c, len) s0 sf =>
        ⌜sf.readReg64 .x0 = ptr ∧ sf.trace = s0.trace⌝ ∗ (ptr ↦ₛ List.replicate len c) }
  have h1 : subroutine_ok P addr (withStack base allocHookStack) :=
    subroutine_ok_conseq_pure hh
      (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
        sepConj_assoc] using hp)
      (fun _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
        sepConj_assoc] using hq)
  have h2 := subroutine_ok_stack_mono h1 hle hmax
  exact subroutine_ok_conseq_pure h2
    (fun _ _ _ hp => by simpa only [sessionMemsetSpec, libcMemsetSpec, withStack, base,
      sepConj_assoc] using hp)
    (fun _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack, base,
      sepConj_assoc] using hq)

private theorem libcMemset_of_session {P : Program} {addr : BitVec 64} {stk : Nat}
    (hh : subroutine_ok P addr (sessionMemsetSpec stk)) :
    subroutine_ok P addr (libcMemsetSpec stk) :=
  subroutine_ok_conseq_pure hh
    (fun _ _ _ hp => hp)
    (fun _ _ _ _ hq => by
      simp only [sessionMemsetSpec, libcMemsetSpec, sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
      exact ⟨hq.1.1, hq.2⟩)

/-- Lifts 4 KiB-stack `AllocContractsMem4K` to 16 KiB-stack `LibsignalTripleRatchet.AllocContractsX`. -/
theorem allocContractsX_of_mem4k {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K img.base A ext) :
    CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext where
  alloc := subroutine_ok_inImage_of_subroutine_ok img (rustAllocWithStack_of_rustAlloc hA.alloc)
  dealloc := subroutine_ok_inImage_of_subroutine_ok img (rustDeallocExternWithStack_of_rustDealloc hA.dealloc)
  realloc := subroutine_ok_inImage_of_subroutine_ok img (rustReallocExternWithStack_of_rustRealloc hA.realloc)
  shim := fun hookStack _ _ =>
    subroutine_ok_inImage_of_subroutine_ok img (subroutine_ok_withStack_of_subroutine_ok hA.shim hookStack)
  memcpy := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (libcMemcpy_of_session
        (sessionMemcpy_mono hA.session_memcpy
          (by unfold allocHookStack extHookStack at *; omega) hmax))
  session_memcpy := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (sessionMemcpy_mono hA.session_memcpy
        (by unfold allocHookStack extHookStack at *; omega) hmax)
  memcpy_region := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_conseq_pure
        (libcMemcpy_of_session
          (sessionMemcpy_mono hA.session_memcpy
            (by unfold allocHookStack extHookStack at *; omega) hmax))
        (fun _ _ _ hp => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
          sepConj_assoc] using hp)
        (fun _ _ _ _ hq => by simpa only [libcMemcpySpec, withStack, memcpyRegionSpec,
          sepConj_assoc] using hq))
  session_memcpy_region := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_conseq_pure
        (sessionMemcpy_mono hA.session_memcpy
          (by unfold allocHookStack extHookStack at *; omega) hmax)
        (fun _ _ _ hp => by simpa only [sessionMemcpySpec, libcMemcpySpec, withStack,
          sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc] using hp)
        (fun _ _ _ _ hq => by simpa only [sessionMemcpySpec, withStack,
          sessionMemcpyRegionSpec, sepConj_assoc] using hq))
  memmove := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (libcMemmove_of_session
        (sessionMemmove_mono hA.session_memmove
          (by unfold allocHookStack extHookStack at *; omega) hmax))
  session_memmove := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (sessionMemmove_mono hA.session_memmove
        (by unfold allocHookStack extHookStack at *; omega) hmax)
  memset := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (libcMemset_of_session
        (sessionMemset_mono hA.session_memset
          (by unfold allocHookStack extHookStack at *; omega) hmax))
  session_memset := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (sessionMemset_mono hA.session_memset
        (by unfold allocHookStack extHookStack at *; omega) hmax)
  memset_region := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_conseq_pure
        (libcMemset_of_session
          (sessionMemset_mono hA.session_memset
            (by unfold allocHookStack extHookStack at *; omega) hmax))
        (fun _ _ _ hp => by
          simp only [libcMemsetSpec, withStack, memsetRegionSpec, sepConj_assoc,
            satisfies_pure_sepConj] at hp ⊢
          exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
        (fun _ _ _ _ hq => by simpa only [libcMemsetSpec, withStack, memsetRegionSpec,
          sepConj_assoc] using hq))
  session_memset_region := fun hookStack hstack hmax =>
    subroutine_ok_inImage_of_subroutine_ok img
      (subroutine_ok_conseq_pure
        (sessionMemset_mono hA.session_memset
          (by unfold allocHookStack extHookStack at *; omega) hmax)
        (fun _ _ _ hp => by
          simp only [sessionMemsetSpec, libcMemsetSpec, withStack, sessionMemsetRegionSpec,
            memsetRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hp ⊢
          exact ⟨⟨hp.1.1, hp.1.2.1, hp.1.2.2.1⟩, hp.2⟩)
        (fun _ _ _ _ hq => by simpa only [sessionMemsetSpec, withStack,
          sessionMemsetRegionSpec, sepConj_assoc] using hq))

end Mem4KToX

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.VerNe
