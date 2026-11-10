/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClosureStubs4K
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.ErrExit
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P3 General-`ext` Basic-Block & Call Steps

Generalizes the post-`cloneExitPC` closure segments (`+0x1cd4`, `+0x1cd8 → +0x34dc` / `ErrExit`)
to `tripleRatchetProgAtExt b ext` under `AllocContractsMem4K` / `AllocContracts`, tracking `x27`
preservation across `Ok pt` (`+0x1cd8 → +0x34dc`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] sessionMemcpySpec libcMemcpySpec

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")

/-! ## 1. 1-Instruction `bl try_decrypt_with_state` at `+0x1cd4` -/

theorem p3_bl_tryDecrypt_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd4#64)
    (hrun : s.status = .Running) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.readReg64 .x0 ∧
        s1.readReg64 .x1 = s.readReg64 .x1 ∧
        s1.readReg64 .x2 = s.readReg64 .x2 ∧
        s1.readReg64 .x3 = s.readReg64 .x3 ∧
        s1.readReg64 .x4 = s.readReg64 .x4 ∧
        s1.readReg64 .x5 = s.readReg64 .x5 ∧
        s1.readReg64 .x6 = s.readReg64 .x6 ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1cd4 0x1cd4
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x1cd4#64 + bv% ((2^64 + ls_off% "libsignal_protocol::session_management::try_decrypt_with_state::<libsignal_cli_handshake::Coins>" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7380)) % 2^64) =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
        CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptName := by
    rw [hentry, htry]; bv_omega
  clear hentry htry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## 2. OOM-Aware `__rust_alloc` Wrappers (`+0x2eac`, `+0x33b0`, OOM tail `+0x3798`) -/

theorem p3_oom_tail_3798_ext_ok (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x3798#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (tripleRatchetProgAtExt b ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hpanic := decryptPrekeyClosure_panic_at_handle_error_ext b ext
  have hstep : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureHandleErrorRelOff) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    closure_fetches_range_cli b (Rust.withPanics ext) 0x3798 0x37a0
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine P3P4.SepWPp.bind_sepWP_frame hF hsym hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic) fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

theorem p3_alloc_call_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp)
    (hsz_pos : 0 < sz) (hsz_lt : sz < 2 ^ 63)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hbl : SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureAllocRelOff) s emp
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
    hF1 hsym1 (decryptPrekeyClosure_alloc_ok_ext_4k hA) hpc1 hrun1 hsp1_al hlr1
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

theorem p3_alloc_call_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State))
    (hA : AllocContracts b A ext) :
    ∀ (s0 s : State) (ret_off oom_off : BitVec 64) (sz : Nat) (F : SepProp),
    (0 < sz) → (sz < 2 ^ 63) →
    img.FrozenLoaded s → s.symtab = img.symtab →
    (s.sp &&& 15#64 == 0#64) = true → s.trace = s0.trace →
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + closureAllocRelOff) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace ∧
        s1.readReg64 .x0 = BitVec.ofNat 64 sz ∧ s1.readReg64 .x1 = 1#64 ∧
        CalleeSavedPreserved s s1 ∧
        s1.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off) →
    (∀ s2 : State,
      s2.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off →
      s2.status = .Running → s2.readReg64 .x0 = 0#64 →
      SepWP (tripleRatchetProgAtExt b ext)
        ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + oom_off) s2 emp
        (fun s3 P_f => (P_f ⊢ emp) ∧ s3.sp = s2.sp ∧ s3.trace = s2.trace)) →
    (∀ s3 : State,
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
        (P3P4.PanicOomProp s0)) →
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + ret_off) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) sz 1 ∗ memRegion (s2.readReg64 .x0) sz ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) :=
  p3_alloc_call_ext_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)

set_option maxHeartbeats 800000 in
theorem p3_alloc_2eac_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContractsMem4K b A ext)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eb0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) := by
  refine p3_alloc_call_ext_4k_ok img b ext hA s0 s 0x2eb0#64 0x3798#64 17
    F (by decide) (by decide) hF hsym hsp_align htr ?_ ?_ ?_
  · closure_fetches_range_cli b (Rust.withPanics ext) 0x2eac 0x2eac
    dsimp only [tripleRatchetProgAtExt] at hpc ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
    examples_hide_fetches
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
    refine ⟨Entails.refl _, rfl, rfl,
      by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, by simp_all [arm64_norm]⟩
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro s2 hpc2 hrun2 hx0_2
    closure_fetches_range_cli b (Rust.withPanics ext) 0x2eb0 0x2eb0
    dsimp only [tripleRatchetProgAtExt] at hpc2 ⊢
    generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
    examples_hide_fetches
    have hx0_g : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      ⟨Entails.refl _, rfl, rfl⟩
  · intro s3 hF3 hsym3 hpc3 hrun3 _ htr3
    exact p3_oom_tail_3798_ext_ok img b ext s0 s3 _ _ _ hF3 hsym3 hpc3 hrun3 htr3

theorem p3_alloc_2eac_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
    (s0 s : State) (F : SepProp)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eac#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2eb0#64) s
      ((A.pool ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool ∗ stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ img.FrozenLoaded s2 ∧ s2.symtab = img.symtab)
      (P3P4.PanicOomProp s0) :=
  p3_alloc_2eac_ext_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)
    s0 s F hF hsym hpc hrun hsp_align htr hx0 hx1

set_option maxHeartbeats 800000 in
theorem p3_alloc_33b0_ext_4k_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
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
  refine p3_alloc_call_ext_4k_ok img b ext hA s0 s 0x33b4#64 0x3798#64 17
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

theorem p3_alloc_33b0_ext_ok {A : RustAlloc} (img : Obj.Image) (b : BitVec 64)
    (ext : String → Option (State → State)) (hA : AllocContracts b A ext)
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
      (P3P4.PanicOomProp s0) :=
  p3_alloc_33b0_ext_4k_ok img b ext (AllocContractsMem4K.of_AllocContracts hA)
    s0 s F hF hsym hpc hrun hsp_align htr hx0 hx1

/-! ## 3. Layout-Independent `.rodata` & `adrp` Helpers for Closure Error/Ok Blocks -/

set_option maxRecDepth 2000000 in
private theorem rodata_dec_failed_lo_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964)) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 0x6974707972636564#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ObjectLoad in
private theorem rodata_dec_failed_lo_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗ P := by
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) (n := 8) (bs := unpack64 0x6974707972636564#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_dec_failed_lo_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

set_option maxRecDepth 2000000 in
private theorem rodata_dec_failed_hi_eq :
    (libsignalSessionImage.data.drop (num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8) - libsignalSessionImage.dataOff)).take 8 =
      unpack64 0x656c696166206e6f#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
open ProofLib.ObjectLoad in
private theorem rodata_dec_failed_hi_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P := by
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) (n := 8) (bs := unpack64 0x656c696166206e6f#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_dec_failed_hi_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

theorem intro_rodata_dec_failed {img : Obj.Image} {b : BitVec 64}
    (himg : Obj.Loads libsignalSessionImage img) (hb : b = img.base)
    {prog : Program} {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s)
    (h : SepWPp prog ret s
      (((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  subst hb
  intro R hm hL
  have hm1 := rodata_dec_failed_hi_intro himg hF hm
  have hm2 := rodata_dec_failed_lo_intro himg hF hm1
  have hm3 : s.mem ⊨
      (((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964))) ↦₆₄ᵣ 0x6974707972636564#64) ∗
       ((img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11960) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11964) + 8)) ↦₆₄ᵣ 0x656c696166206e6f#64) ∗ P) ∗ R := by
    simpa only [sepConj_assoc] using hm2
  exact h R hm3 hL

theorem adrp_closure_rodata_nondupA {b entry : BitVec 64}
    (hb : b &&& 0xfff#64 = 0#64)
    (he : entry = b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))) :
    (((entry + 0x2d78#64) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11640))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) ∧
    ((((bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) + (b + 0x2d78#64)) &&& 0xfffffffffffff000#64) +
      bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) -
        (page% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11640))) =
      b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) := by
  refine ⟨?_, ?_⟩
  · rw [he, BitVec.add_assoc, ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]; rfl
  · rw [← BitVec.add_assoc, BitVec.add_comm _ b, BitVec.add_assoc,
        ProofLib.adrp_page_of_aligned hb, BitVec.add_assoc]
    rfl

/-! ## 4. Stage P3 Post-`tryDecrypt` Closure Blocks (`Ok` and `Err` Paths) -/

theorem p3_seg7b_x24_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1dfc#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64) s
      emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧ s1.sp = s.sp ∧
        s1.trace = s.trace ∧ s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧ s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧ s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0xfffffffffffffffe#64 ∧ s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1dfc 0x1e00
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_dup_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]"))) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ 0x8000000000000017#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x34dc#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1cd8 0x1ce8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2d58 0x2d68
  closure_fetches_range_cli b (Rust.withPanics ext) 0x34d4 0x34d8
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x34d8#64 + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 13528)) % 2^64) =
      b + (bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#4]")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

theorem p3_err_nondup_a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr outPtr errTag e1 e2 e3 e4 e5
    u930 u938 u940 u948 u950 u958 : BitVec 64)
    (hb : b &&& 0xfff#64 = 0#64) (herr_ne_ok : errTag ≠ 0xfffffffffffffffe#64)
    (herr_ne_dup : errTag ≠ 0x8000000000000017#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x1cd8#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}"))) s
      (((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
       ((s.sp + 0x278#64) ↦₆₄ e1) ∗
       ((s.sp + 0x280#64) ↦₆₄ e2) ∗
       ((s.sp + 0x288#64) ↦₆₄ e3) ∗
       ((s.sp + 0x290#64) ↦₆₄ e4) ∗
       ((s.sp + 0x298#64) ↦₆₄ e5) ∗
       ((s.sp + 0x930#64) ↦₆₄ u930) ∗
       ((s.sp + 0x938#64) ↦₆₄ u938) ∗
       ((s.sp + 0x940#64) ↦₆₄ u940) ∗
       ((s.sp + 0x948#64) ↦₆₄ u948) ∗
       ((s.sp + 0x950#64) ↦₆₄ u950) ∗
       ((s.sp + 0x958#64) ↦₆₄ u958))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((s.sp + 0x270#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x278#64) ↦₆₄ e1) ∗
          ((s.sp + 0x280#64) ↦₆₄ e2) ∗
          ((s.sp + 0x288#64) ↦₆₄ e3) ∗
          ((s.sp + 0x290#64) ↦₆₄ e4) ∗
          ((s.sp + 0x298#64) ↦₆₄ e5) ∗
          ((s.sp + 0x930#64) ↦₆₄ errTag) ∗
          ((s.sp + 0x938#64) ↦₆₄ e1) ∗
          ((s.sp + 0x940#64) ↦₆₄ e2) ∗
          ((s.sp + 0x948#64) ↦₆₄ e3) ∗
          ((s.sp + 0x950#64) ↦₆₄ e4) ∗
          ((s.sp + 0x958#64) ↦₆₄ e5)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3b0#64 ∧
        s1.readReg64 .x1 = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) ∧
        s1.readReg64 .x2 = 7#64 ∧
        s1.readReg64 .x3 = s.sp + 0xa90#64 ∧
        s1.readReg64 .x4 = s.sp + 0x930#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x24 = s.sp + 0x370#64 ∧
        s1.readReg64 .x25 = s.sp + 0x210#64 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 0x8000000000000017#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2d9c#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond_ok := cond_ne_adds64_of_ne_neg2 herr_ne_ok
  have hcond_dup := cond_eq_subs64_of_ne_dup herr_ne_dup
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1cd8 0x1ce8
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2d58 0x2d98
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have hadrp0 := (adrp_closure_rodata_nondupA hb hentry).1
  have hadrp := (adrp_closure_rodata_nondupA hb hentry).2
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x2d98#64 + bv% ((2^64 + ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11672)) % 2^64) =
      b + (bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx24' : s.readReg64 (Reg.gpr 24#5) = s.sp + 0x370#64 := hx24
  have hro : (b + bv% (page% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)))) + bv% ((ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) % 4096) = b + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7688) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 7692)) := by bv_arith
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem p3_err_nondup_b_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr : BitVec 64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2d9c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + (bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one"))) s
      (((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
       ((s.sp + 0x3d8#64) ↦₆₄ 0#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
          ((s.sp + 0x3d8#64) ↦₆₄ 0#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3c8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x24 = s.readReg64 .x24 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = s.readReg64 .x26 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr decryptPrekeyClosureName + 0x2db4#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2d9c 0x2db0
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName =
      b + (bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")) := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName +
      0x2db0#64 + bv% ((2^64 + ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one" - (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 11696)) % 2^64) =
      b + (bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::error::SignalProtocolError>>::grow_one")) := by
    rw [hentry]; bv_omega
  clear hentry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  wp_steps
  refine SepWP.done (by rw [← htarget]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
