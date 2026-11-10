/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Fetch
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.RoDataReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes
import LibsignalBinary.Proofs.TripleRatchet.Hooks

/-!
# Stage 2 Shared Normalization, Vtable, Model, and Callee Helpers

Provides state/`BitVec` normalization rules (`CliStage2Norm`), `SepWPp` + `TraceFsSound`
combinators, `StaticSecret::drop` and panic extern contracts, `.rodata` vtable lemmas, X25519 scalar
clamping lemmas, and the `Stage2CalleesExt` bundle for Stage 2 of `initiate`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

/-! ## Normalization rules (`CliStage2Norm`) -/

namespace CliStage2Norm

theorem sp_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

theorem sp_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

theorem sp_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).sp = s.sp := by cases s; rfl

theorem fs_setPC_pre (s : State) (pc : BitVec 64) :
    (s.setPC pc).fs = s.fs := by cases s; rfl

theorem fs_setMem_pre (s : State) (m : Memory) :
    (s.setMem m).fs = s.fs := by cases s; rfl

theorem fs_setPState_pre (s : State) (ps : PState) :
    (s.setPState ps).fs = s.fs := by cases s; rfl

theorem fs_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by cases s; cases r <;> rfl

theorem fs_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).fs = s.fs := by cases s; cases r <;> rfl

theorem fs_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).fs = s.fs := by cases s; cases w <;> cases r <;> rfl

theorem fs_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).fs = s.fs := by cases s; rfl

theorem trace_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 idx v).trace = s.trace := by cases s; rfl

theorem trace_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) :
    (s.writeReg32 r v).trace = s.trace := by cases s; cases r <;> rfl

theorem trace_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64) :
    (s.writeReg w r v).trace = s.trace := by cases s; cases w <;> cases r <;> rfl

theorem readReg64_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

theorem readReg64_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

theorem readReg64_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg64 r = s.readReg64 r := by
  cases s; cases r <;> rfl

theorem readReg32_setPC_pre (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg32_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

theorem readReg32_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128) (r : Reg) :
    (s.writeVReg128 idx v).readReg32 r = s.readReg32 r := by
  cases s; cases r <;> rfl

theorem readReg_setPC_pre (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem readReg_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

theorem readReg_writeVReg128_pre (s : State) (idx : BitVec 5) (v : BitVec 128)
    (w : RegWidth) (r : Reg) :
    (s.writeVReg128 idx v).readReg w r = s.readReg w r := by
  cases s; cases w <;> cases r <;> rfl

theorem readVReg128_setPC_pre (s : State) (pc : BitVec 64) (idx : BitVec 5) :
    (s.setPC pc).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

theorem readVReg128_setMem_setPC_pre (s : State) (pc : BitVec 64) (m : Memory) (idx : BitVec 5) :
    ((s.setPC pc).setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

theorem readVReg128_setMem_pre (s : State) (m : Memory) (idx : BitVec 5) :
    (s.setMem m).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

theorem readVReg128_setPState_pre (s : State) (ps : PState) (idx : BitVec 5) :
    (s.setPState ps).readVReg128 idx = s.readVReg128 idx := by
  cases s; rfl

theorem readVReg128_writeReg64_pre (s : State) (r : Reg) (v : BitVec 64) (idx : BitVec 5) :
    (s.writeReg64 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

theorem readVReg128_writeReg32_pre (s : State) (r : Reg) (v : BitVec 32) (idx : BitVec 5) :
    (s.writeReg32 r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases r <;> rfl

theorem readVReg128_writeReg_pre (s : State) (w : RegWidth) (r : Reg) (v : BitVec 64)
    (idx : BitVec 5) :
    (s.writeReg w r v).readVReg128 idx = s.readVReg128 idx := by
  cases s; cases w <;> cases r <;> rfl

theorem extractLsb_append_lo (hi lo : BitVec 64) :
    BitVec.extractLsb' 0 64 (hi ++ lo) = lo := by
  bv_bits

theorem extractLsb_append_hi (hi lo : BitVec 64) :
    BitVec.extractLsb' 64 64 (hi ++ lo) = hi := by
  bv_bits

theorem extractLsb_pack32_0 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 8 (a ++ b ++ c ++ d) = d := by
  bv_bits

theorem extractLsb_pack32_8 (a b c d : BitVec 8) :
    BitVec.extractLsb' 8 8 (a ++ b ++ c ++ d) = c := by
  bv_bits

theorem extractLsb_pack32_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 8 (a ++ b ++ c ++ d) = b := by
  bv_bits

theorem extractLsb_pack32_24 (a b c d : BitVec 8) :
    BitVec.extractLsb' 24 8 (a ++ b ++ c ++ d) = a := by
  bv_bits

theorem extractLsb_pack32_0_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 0 16 (a ++ b ++ c ++ d) = c ++ d := by
  bv_bits

theorem extractLsb_pack32_16_16 (a b c d : BitVec 8) :
    BitVec.extractLsb' 16 16 (a ++ b ++ c ++ d) = a ++ b := by
  bv_bits

end CliStage2Norm

/-! ## `SepWPp` and `TraceFsSound` combinators -/

theorem imgCallInv_of_keepsFrozen {img : Obj.Image} {s sm : State}
    (hinv : ImgCallInv img s) (hkf : s.mem.KeepsFrozen sm.mem) (hsym : sm.symtab = s.symtab) :
    ImgCallInv img sm :=
  ⟨hinv.1.of_keepsFrozen hkf, hsym.trans hinv.2⟩

theorem sepWPp_of_sepWP_fs {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hFs : TraceFsSound prog)
    (h : SepWP prog mid s P
      (fun sm Pm =>
        sm.trace = s.trace ∧
          (s.mem.KeepsFrozen sm.mem → sm.fs.files = s.fs.files →
            SepWPp prog ret sm Pm Q Qp oom))
      oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, htr, hcont⟩ | hoom⟩
  · have hfiles : sm.fs.files = s.fs.files :=
      hFs.files_eq hsteps (evs := []) (by simpa using htr) NoFsEv.nil
    obtain ⟨sf, hsteps', hout⟩ := hcont hsteps.keepsFrozen hfiles R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_call_fs {α : Type} {prog : Program}
    {entry ret_pc target_pc : BitVec 64} {spec : Spec α}
    (hFs : TraceFsSound prog)
    (hcall : subroutine_ok prog entry spec)
    {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = entry)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : P ⊢ spec.pre x s ∗ F)
    (hpan : ∀ sf, Qp sf (spec.onPanic x s sf ∗ F))
    (hexit : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hoom : ∀ sf, spec.onOom x s sf ∗ F ⊢ oom sf)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf → s.mem.KeepsFrozen sf.mem →
      (sf.trace = s.trace → sf.fs.files = s.fs.files) →
      SepWPp prog target_pc sf (spec.post x s sf ∗ F) Q Qp oom) :
    SepWPp prog target_pc s P Q Qp oom := by
  have h1 : SepWPp prog ret_pc s P
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post x s sm ∗ F) Qp oom := by
    refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp_align hlr
      (fun R' hm => by
        rw [← sepConj_assoc]
        exact Arm64.Satisfies.mono (sepConj_mono_left hpre) hm)
      (fun _ code _ _ hpost => by
        rw [hexit] at hpost
        exact not_satisfies_false_sepConj hpost)
      (fun sf _ => hpan sf)
      (fun sm hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf _ _ hpost => by
        rw [← sepConj_assoc] at hpost
        exact Arm64.Satisfies.mono (sepConj_mono_left (hoom sf)) hpost)
  intro R' hm hL
  rcases h1 R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, Pm, hpost, hspm, hcsm, rfl⟩ | hpan_out | hoom_out⟩
  · have hf : sm.trace = s.trace → sm.fs.files = s.fs.files := fun htr =>
      hFs.files_eq hsteps (evs := []) (by simpa using htr) NoFsEv.nil
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm hsteps.keepsFrozen hf R' hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan_out)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom_out)⟩

theorem initPanicPost_of_allocFailed (A : RustAlloc) (img : Obj.Image) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 s sf : State} (htr : s.trace = s0.trace) (F : SepProp) :
    InitPanicPost A img S x stk s0 sf
      ((⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) := by
  dsimp only [InitPanicPost, initSlotSpec, Spec.inImage]
  rw [sepConj_assoc]
  refine Entails.pure_left fun ⟨hfail, _⟩ => ?_
  have hfail0 : allocFailedIn s0 sf := by simpa [allocFailedIn, htr] using hfail
  exact Entails.pure_right (Or.inr hfail0) (entails_anyHeap _)

theorem initPanicPost_of_panicked (A : RustAlloc) (img : Obj.Image) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 s : State} (hfail : allocFailedIn s0 s) (P : SepProp) :
    InitPanicPost A img S x stk s0 (Rust.panicked s) P := by
  dsimp only [InitPanicPost, initSlotSpec, Spec.inImage]
  have hfail' : allocFailedIn s0 (Rust.panicked s) := by
    simpa [Rust.panicked, allocFailedIn] using hfail
  exact Entails.pure_right (Or.inr hfail') (entails_anyHeap P)

/-! ## Panic extern and `StaticSecret::drop` hook contracts -/

set_option maxRecDepth 2000000 in
theorem handleError_externAt (img : Obj.Image) (W : CliHooks) :
    (initProg img W).externAt? ((initProg img W).fnAddr handleErrorName) = some Rust.panicked := by
  have hp := panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base)
    (hooks := cliExterns W) (hname := handleErrorName) (k := 0) handleError_stub
    (Nat.add_zero _) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by rfl_kernel)
  simpa only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, handleError_stub,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hp

theorem staticSecretDrop_row (W : CliHooks) :
    (staticSecretDropName, zeroizeSecretHook) ∈ cliHookTable W := by
  simp [cliHookTable, staticSecretDropName]

set_option maxRecDepth 2000000 in
theorem staticSecretDrop_cli_ok (W : CliHooks) (img : Obj.Image) :
    subroutine_ok (initProg img W)
      ((initProg img W).fnAddr staticSecretDropName)
      zeroizeSecretSpec :=
  cli_stub_ok W img staticSecretDrop_stub (by decide)
    (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
    (by rfl_kernel) (staticSecretDrop_row W) zeroizeSecretHook_ok

/-! ## Layout-independent vtable `.rodata` lemmas -/

set_option maxRecDepth 2000000 in
private theorem rodata_idKeyPairFutSize_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 16#64 := by rfl_kernel

set_option maxRecDepth 2000000 in
private theorem rodata_idKeyPairFutAlign_eq :
    (libsignalSessionImage.data.drop
      (num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8) -
        libsignalSessionImage.dataOff)).take 8 =
      unpack64 8#64 := by rfl_kernel

theorem idVt_eq_cliIdVtOff (img : Obj.Image) :
    idVt img = img.base + KitInst.cliIdVtOff := rfl

theorem rodata_idVt_getKeyPairShim {img : Obj.Image} (W : CliHooks) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((idVt img + 0x18#64) ↦₆₄ᵣ (initProg img W).fnAddr idKeyPairShimName) ∗ P := by
  have hfn : (initProg img W).fnAddr idKeyPairShimName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") := by
    simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairShim_fnOff]
  rw [idVt_eq_cliIdVtOff, hfn]
  dsimp only [KitInst.cliIdVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) + 0x18#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem rodata_idKeyPairFutDrop {img : Obj.Image} (W : CliHooks) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff) ↦₆₄ᵣ
      (initProg img W).fnAddr KitInst.cliIdFutDropName) ∗ P := by
  have hfn : (initProg img W).fnAddr KitInst.cliIdFutDropName =
      img.base + KitInst.cliIdFutDropOff := by
    simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, KitInst.cliIdFutDrop_fnOff]
  rw [hfn]
  dsimp only [idKeyPairFutVtOff, KitInst.cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem rodata_idKeyPairFutSize {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 8#64) ↦₆₄ᵣ 16#64) ∗ P := by
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) + 8#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 16))
    (n := 8) (bs := unpack64 16#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_idKeyPairFutSize_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

theorem rodata_idKeyPairFutAlign {img : Obj.Image} {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 0x10#64) ↦₆₄ᵣ 8#64) ∗ P := by
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) + 0x10#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8) by bv_omega]
  have hh := loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 8))
    (n := 8) (bs := unpack64 8#64)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel)
    (unpack64_length _) rodata_idKeyPairFutAlign_eq
  obtain ⟨hRO, hread⟩ := holdsBytes_ro hh
  rw [unpack64_length] at hRO hread
  exact Satisfies.rodata64_intro hRO (Memory.read64_of_readBytes_eq_unpack64 _ _ _ hread) hP

theorem rodata_idKeyPairFutPoll {img : Obj.Image} (W : CliHooks) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 0x18#64) ↦₆₄ᵣ
      (initProg img W).fnAddr idKeyPairPollName) ∗ P := by
  have hfn : (initProg img W).fnAddr idKeyPairPollName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") := by
    simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairPoll_fnOff]
  rw [hfn]
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) + 0x18#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-! ## Pure model, `storesAt`, and `InitOk₀` lemmas -/

def storesRestAt (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) : SepProp :=
  dirAt A (a + 0x28#64) g.identity.peers ∗
    dirAt A (a + 0x50#64) g.signed ∗ dirAt A (a + 0x78#64) g.kyber.oneTime ∗
    dirAt A (a + 0xa0#64) g.kyber.lastResort ∗ dirAt A (a + 0xc8#64) g.oneTime ∗
    dirAt A (a + 0xf0#64) g.sessions ∗ dirAt A (a + 0x118#64) g.pub

theorem storesAt_eq_own_sep (A : RustAlloc) (a : BitVec 64) (g : StoresGhost) :
    storesAt A a g = dirAt A a g.identity.own ∗ storesRestAt A a g := by
  simp only [storesAt, storesRestAt]

theorem idKeyPairPoll_own_facts {W : PEParams} {F : FsFiles} {peer me : AddrVal}
    (hok : InitOk₀ W F peer me) :
    StoresGhost.opened.identity.own.path.length < 2 ^ 32 ∧
      cliWrOk (pathOf StoresGhost.opened.identity.own.path (utf8 "identity-key-pair")) ∧
      (∀ bs, StoresGhost.opened.identity.own.get cliIo.rd F (utf8 "identity-key-pair") = .ok bs →
        bs.length < 2 ^ 32) ∧
      (IdGhost.mk StoresGhost.opened.identity.own (.new [])).keyPair cliIo.rd F =
        StoresGhost.opened.identity.keyPair cliIo.rd F := by
  exact ⟨by decide, cliWrOk_ownFile (List.Mem.tail _ (List.Mem.head _)), hok.keyPairLt, rfl⟩

theorem distinctSid_of_not_sameServiceId {peer me : AddrVal}
    (h : ¬ SameServiceId peer me) :
    ∀ sid1 sid2,
      serviceIdParse uuidTryParse me.name = some sid1 →
      serviceIdParse uuidTryParse peer.name = some sid2 →
      sid1 ≠ sid2 := by
  intro sid1 sid2 h1 h2 heq
  subst heq
  exact h ⟨sid1, h2, h1⟩

theorem bundleEOf_kpk_len {b : BundleV} {be : PreKeyBundleFields} (hb : bundleEOf? b = some be) :
    b.spkSig.length = 64 ∧ b.kpkSig.length = 64 ∧ b.kpk.length = 1568 ∧
      b.idKey.publicKey.bytes.toList = be.idPub.toList ∧
      b.spk.bytes.toList = be.spkPub.toList := by
  unfold bundleEOf? at hb
  split at hb <;> try contradiction
  split at hb <;> try contradiction
  split at hb <;> try contradiction
  injection hb with hb'
  subst hb'
  exact ⟨‹_›, ‹_›, ‹_›, rfl, rfl⟩

theorem initDef_eq_some_none_of_keyPair_err (X : UnreachedPqxdhPrimitives) (W : PEParams) (F : FsFiles)
    (peer me : AddrVal) (b : BundleV) (coins : List (BitVec 8))
    (herr : StoresGhost.opened.identity.keyPair cliIo.rd F = .error ()) :
    initDef X W F peer me b coins = some none := by
  unfold initDef
  dsimp only
  cases bundleEOf? b with
  | none => rfl
  | some be =>
    cases StoresGhost.opened.identity.trusted cliIo.rd F peer b.idKey with
    | error _ => rfl
    | ok t =>
      cases t with
      | false => rfl
      | true => simp [herr]

theorem keyPairOf_eq (C : Crypto) (raw : List.Vector (BitVec 8) 32) :
    (keyPairOf C raw).privateKey.bytes = Ratchet.clampScalar raw ∧
    (keyPairOf C raw).publicKey.bytes = C.pubKey (Ratchet.clampScalar raw) :=
  ⟨rfl, rfl⟩

/-! ## X25519 scalar clamping -/

private theorem set_last_eq : ∀ (mid : List (BitVec 8)) (x y : BitVec 8),
    (mid ++ [x]).set mid.length y = mid ++ [y]
  | [], _, _ => rfl
  | a :: tl, x, y => congrArg (a :: ·) (set_last_eq tl x y)

private theorem getElem_last_eq : ∀ (mid : List (BitVec 8)) (x : BitVec 8)
    (h : mid.length < (mid ++ [x]).length),
    (mid ++ [x])[mid.length]'h = x
  | [], _, _ => rfl
  | _ :: tl, x, h => getElem_last_eq tl x (Nat.lt_of_succ_lt_succ h)

theorem clampScalar_split (v : List.Vector (BitVec 8) 32) :
    ∃ (b0 b31 : BitVec 8) (mid : List (BitVec 8)),
      mid.length = 30 ∧
      v.toList = [b0] ++ mid ++ [b31] ∧
      (Ratchet.clampScalar v).toList =
        [b0 &&& 0xf8#8] ++ mid ++ [(b31 &&& 0x7f#8) ||| 0x40#8] := by
  rcases v with ⟨bs, hlen⟩
  cases bs with
  | nil => simp at hlen
  | cons b0 rest =>
    have hrest : rest.length = 31 := by simpa using hlen
    have hdrop30 : (rest.drop 30).length = 1 := by simp [hrest]
    cases hlast : rest.drop 30 with
    | nil => simp [hlast] at hdrop30
    | cons b31 tail =>
      have htail : tail = [] := by
        have ht : tail.length = 0 := by simpa [hlast] using hdrop30
        exact List.eq_nil_of_length_eq_zero ht
      subst htail
      let mid := rest.take 30
      have hmid : mid.length = 30 := by simp [mid, hrest]
      have hrest_eq : rest = mid ++ [b31] := by
        have h := (List.take_append_drop 30 rest).symm
        simpa [mid, hlast] using h
      refine ⟨b0, b31, mid, hmid, ?_, ?_⟩
      · change b0 :: rest = b0 :: (mid ++ [b31])
        rw [← hrest_eq]
      · dsimp only [Ratchet.clampScalar, List.Vector.toList]
        have hg0 : List.Vector.get ⟨b0 :: rest, hlen⟩ 0 = b0 := rfl
        have hg31 : List.Vector.get ⟨b0 :: rest, hlen⟩ 31 = b31 := by
          change (b0 :: rest)[31]'(by omega) = b31
          have hidx : (31 : Nat) = mid.length + 1 := by omega
          simp only [hrest_eq, hidx, List.getElem_cons_succ]
          exact getElem_last_eq mid b31 _
        rw [hg0, hg31]
        change ((b0 &&& 0xf8#8) :: rest).set 31 ((b31 &&& 0x7f#8) ||| 0x40#8) =
          (b0 &&& 0xf8#8) :: (mid ++ [(b31 &&& 0x7f#8) ||| 0x40#8])
        have hidx : (31 : Nat) = mid.length + 1 := by omega
        rw [hrest_eq, hidx, List.set_cons_succ, set_last_eq]

/-! ## Extern-parameterized hooks, `.rodata`, and `Stage2CalleesExt` -/

set_option maxRecDepth 2000000 in
theorem handleError_externAt_ext (img : Obj.Image) (ext : String → Option (State → State)) :
    (initProgExt img ext).externAt? ((initProgExt img ext).fnAddr handleErrorName) =
      some Rust.panicked := by
  have hp := panic_at_panicSymbol (P := libsignalSessionCode) (b := img.base)
    (hooks := cliExternsWith ext) (hname := handleErrorName) (k := 0) handleError_stub
    (Nat.add_zero _) (by decide) (ls_hook% "alloc::raw_vec::handle_error") (by rfl_kernel)
  simpa only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, handleError_stub,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hp

set_option maxRecDepth 2000000 in
theorem staticSecretDrop_ext_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr staticSecretDropName)
      ((LibsignalTripleRatchet.withStack zeroizeSecretSpec extHookStack).inImage img) := by
  have hraw : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr staticSecretDropName) CliExt.zeroizeSpec :=
    ext_stub_ok img staticSecretDrop_stub (by decide)
      (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
      (by rfl_kernel) hOk.staticDrop
  exact subroutine_ok_inImage_of_subroutine_ok img hraw

set_option maxRecDepth 2000000 in
theorem staticSecretDrop_ext_stack_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image)
    {hookStack : Nat} (hstack : extHookStack ≤ hookStack) (hstack_le : hookStack ≤ 2 ^ 64) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr staticSecretDropName)
      ((LibsignalTripleRatchet.withStack zeroizeSecretSpec hookStack).inImage img) := by
  have hraw : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr staticSecretDropName) CliExt.zeroizeSpec :=
    ext_stub_ok img staticSecretDrop_stub (by decide)
      (ls_hook% "<x25519_dalek::x25519::StaticSecret as core::ops::drop::Drop>::drop")
      (by rfl_kernel) hOk.staticDrop
  refine subroutine_ok_inImage_of_subroutine_ok img ?_
  apply subroutine_ok_outcome_intro
  intro a R s0 hpc hrun hpre hal
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗
        stackAt s0.sp extHookStack := by
    have h1 := stackAt_split_bottom s0.sp extHookStack (hookStack - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstack] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
  have hpre' : s0.mem ⊨ CliExt.zeroizeSpec.pre a s0 ∗ R' := by
    dsimp only [LibsignalTripleRatchet.withStack, zeroizeSecretSpec,
      CliExt.zeroizeSpec, CliExt.withStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome hraw a R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [LibsignalTripleRatchet.withStack, zeroizeSecretSpec,
      CliExt.zeroizeSpec, CliExt.withStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [CliExt.zeroizeSpec, CliExt.withStack] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [CliExt.zeroizeSpec, CliExt.withStack] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [CliExt.zeroizeSpec, CliExt.withStack] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

set_option maxRecDepth 2000000 in
theorem derivePubKeyBytes_ext_ok {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (hOk : CliExternsOk P A ext) (img : Obj.Image) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
      ((derivePublicKeyBytesStackSpec P.C.pubKey extHookStack).inImage img) := by
  have hpub_fnOff : libsignalSessionCode.fnOff pubFromSecretName =
      num% (ls_off% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from") :=
    ls_stub% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from"
  have hpub_raw : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr pubFromSecretName) (CliExt.pubFromSecretSpec P.C) :=
    ext_stub_ok img hpub_fnOff (by decide)
      (ls_hook% "<x25519_dalek::x25519::PublicKey as core::convert::From<&x25519_dalek::x25519::StaticSecret>>::from")
      (by rfl_kernel) hOk.pubFromSecret
  have hpub_img := subroutine_ok_inImage_of_subroutine_ok img hpub_raw
  refine derive_public_key_bytes_ok_of_contract_stack_inImage extHookStack ?_
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ ((CliExt.pubFromSecretSpec P.C).inImage img).pre
      (x.secret, x.sec, x.out) s0 ∗ R := by
    dsimp only [Spec.inImage, CliExt.pubFromSecretSpec, CliExt.withStack,
      derivePublicKeyBytesStackSpec] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine subroutine_ok.mono_outcome hpub_img (x.secret, x.sec, x.out) R s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, CliExt.pubFromSecretSpec, CliExt.withStack,
      derivePublicKeyBytesStackSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem rodata_idVt_getKeyPairShim_ext {img : Obj.Image}
    (ext : String → Option (State → State)) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((idVt img + 0x18#64) ↦₆₄ᵣ (initProgExt img ext).fnAddr idKeyPairShimName) ∗ P := by
  have hfn : (initProgExt img ext).fnAddr idKeyPairShimName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair") := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairShim_fnOff]
  rw [idVt_eq_cliIdVtOff, hfn]
  dsimp only [KitInst.cliIdVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x28) + 0x18#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::save_identity") - 0x10))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem rodata_idKeyPairFutDrop_ext {img : Obj.Image}
    (ext : String → Option (State → State)) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff) ↦₆₄ᵣ
      (initProgExt img ext).fnAddr KitInst.cliIdFutDropName) ∗ P := by
  have hfn : (initProgExt img ext).fnAddr KitInst.cliIdFutDropName =
      img.base + KitInst.cliIdFutDropOff := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase,
      KitInst.cliIdFutDrop_fnOff]
  rw [hfn]
  dsimp only [idKeyPairFutVtOff, KitInst.cliIdFutDropOff]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18))
    (target := num% (ls_off% "core::ptr::drop_glue::<<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity::{closure#0}>"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

theorem rodata_idKeyPairFutPoll_ext {img : Obj.Image}
    (ext : String → Option (State → State)) {s : State} {P : SepProp}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + idKeyPairFutVtOff + 0x18#64) ↦₆₄ᵣ
      (initProgExt img ext).fnAddr idKeyPairPollName) ∗ P := by
  have hfn : (initProgExt img ext).fnAddr idKeyPairPollName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") := by
    simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, idKeyPairPoll_fnOff]
  rw [hfn]
  dsimp only [idKeyPairFutVtOff]
  rw [show img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}") - 0x18) + 0x18#64 =
      img.base + bv% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")) by bv_omega]
  exact CryptoProofLib.RoDataReloc.Satisfies.of_reloc64 himg hF
    (off := num% (ls_reloc% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}")))
    (target := num% (ls_off% "<libsignal_cli::stores::IdentityFiles as libsignal_protocol::storage::traits::IdentityKeyStore>::get_identity_key_pair::{closure#0}"))
    (by decide) (by rfl_kernel) (by rfl_kernel) hP

/-- Stack-parameterized `<IdentityKey>::is_same_account` distinct-account specification. -/
def isSameAccountDistinctAtSpec (A : RustAlloc) (parse : UuidParser) (isaStk : Nat) :
    Spec Pqxdh.WireEntries.IsSameAccountDistinctGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.localIkA ∧
      s.readReg64 .x1 = g.locA ∧
      s.readReg64 .x2 = g.remoteIkA ∧
      s.readReg64 .x3 = g.remA ∧
      (g.localIk ≠ g.remoteIk ∨
        Pqxdh.WireEntries.DistinctSid parse g.loc.name.bytes g.rem.name.bytes)⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s.sp isaStk
  post := fun g s0 sf =>
    ⌜(sf.readReg64 .x0).setWidth 32 = 0#32 ∧ sf.trace = s0.trace⌝ ∗
    (g.localIkA ↦ₛ g.localIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.loc g.locA ∗
    (g.remoteIkA ↦ₛ g.remoteIk.publicKey.bytes.toList) ∗
    protocolAddressAt A g.rem g.remA ∗
    stackAt s0.sp isaStk

/-- Stage 2 callee bundle on `initProgExt img ext` (`StaticSecret::drop`, `derive_public_key_bytes`, and `is_same_account`). -/
structure Stage2CalleesExt (img : Obj.Image) (P : PEParams) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop where
  staticSecretDrop : ∀ {hookStack : Nat}, extHookStack ≤ hookStack → hookStack ≤ 2 ^ 64 →
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr staticSecretDropName)
      ((LibsignalTripleRatchet.withStack zeroizeSecretSpec hookStack).inImage img)
  derivePubKeyBytes :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
      ((derivePublicKeyBytesStackSpec P.C.pubKey extHookStack).inImage img)
  isSameAccount : ∃ isaStk ≤ 516880,
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      ((isSameAccountDistinctAtSpec A uuidTryParse isaStk).inImage img)

/-- Builds `Stage2CalleesExt` from `CliExternsOk P A ext` and `<IdentityKey>::is_same_account` at `isaStk ≤ 516880`. -/
theorem stage2CalleesExt_of_externsOk {img : Obj.Image} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {isaStk : Nat}
    (hOk : CliExternsOk P A ext)
    (hisa : isaStk ≤ 516880)
    (hSameAcct : subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      ((isSameAccountDistinctAtSpec A uuidTryParse isaStk).inImage img)) :
    Stage2CalleesExt img P A ext :=
  { staticSecretDrop := fun hs1 hs2 => staticSecretDrop_ext_stack_ok hOk img hs1 hs2
    derivePubKeyBytes := derivePubKeyBytes_ext_ok hOk img
    isSameAccount := ⟨isaStk, hisa, hSameAcct⟩ }

/-- Instantiates `Stage2CalleesExt` at `cliHookExterns W` from `InitLocalCallees`. -/
theorem stage2CalleesExt_of_localCallees {img : Obj.Image} {A : RustAlloc} {W : CliHooks}
    {stk : Nat} (hLocal : InitLocalCallees img A W stk) :
    Stage2CalleesExt img ⟨W.C, W.Q⟩ A (cliHookExterns W) :=
  { staticSecretDrop := fun {hookStack} _ _ =>
      subroutine_ok_inImage_of_subroutine_ok img
        (subroutine_ok_withStack_of_subroutine_ok (staticSecretDrop_cli_ok W img) hookStack)
    derivePubKeyBytes :=
      subroutine_ok_inImage_of_subroutine_ok img
        (derivePublicKeyBytesStack_of_spec extHookStack hLocal.derivePubKeyBytes)
    isSameAccount := ⟨Pqxdh.WireEntries.isSameAccountDistinctStack, by decide,
      subroutine_ok_inImage_of_subroutine_ok img hLocal.isSameAccount⟩ }

/-- Lifts `Stage2CalleesExt.derivePubKeyBytes` to any residual stack `extHookStack ≤ hookStack ≤ 2 ^ 64`. -/
theorem Stage2CalleesExt.derivePubKeyBytes_withStack {img : Obj.Image} {P : PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLocal : Stage2CalleesExt img P A ext)
    {hookStack : Nat} (hstack : extHookStack ≤ hookStack) (hstack_le : hookStack ≤ 2 ^ 64) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliDerivePubKeyBytesName)
      ((derivePublicKeyBytesStackSpec P.C.pubKey hookStack).inImage img) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hal
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗
        stackAt s0.sp extHookStack := by
    have h1 := stackAt_split_bottom s0.sp extHookStack (hookStack - extHookStack) (by omega)
    rwa [Nat.add_sub_of_le hstack] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - extHookStack) ∗ R
  have hpre' : s0.mem ⊨ ((derivePublicKeyBytesStackSpec P.C.pubKey extHookStack).inImage img).pre
      x s0 ∗ R' := by
    dsimp only [Spec.inImage, derivePublicKeyBytesStackSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome hLocal.derivePubKeyBytes x R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, derivePublicKeyBytesStackSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [Spec.inImage, derivePublicKeyBytesStackSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [Spec.inImage, derivePublicKeyBytesStackSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [Spec.inImage, derivePublicKeyBytesStackSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

/-- Lifts `Stage2CalleesExt.isSameAccount` to any residual stack `516880 ≤ hookStack ≤ 2 ^ 64`. -/
theorem Stage2CalleesExt.isSameAccount_withStack {img : Obj.Image} {P : PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hLocal : Stage2CalleesExt img P A ext)
    {hookStack : Nat} (hstack : 516880 ≤ hookStack) (hstack_le : hookStack ≤ 2 ^ 64) :
    subroutine_ok (initProgExt img ext)
      ((initProgExt img ext).fnAddr cliIsSameAccountName)
      ((isSameAccountDistinctAtSpec A uuidTryParse hookStack).inImage img) := by
  obtain ⟨isaStk, hisa, hraw⟩ := hLocal.isSameAccount
  have hle : isaStk ≤ hookStack := by omega
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hal
  have hsplit : stackAt s0.sp hookStack =
      memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - isaStk) ∗
        stackAt s0.sp isaStk := by
    have h1 := stackAt_split_bottom s0.sp isaStk (hookStack - isaStk) (by omega)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 hookStack) (hookStack - isaStk) ∗ R
  have hpre' : s0.mem ⊨ ((isSameAccountDistinctAtSpec A uuidTryParse isaStk).inImage img).pre
      g s0 ∗ R' := by
    dsimp only [Spec.inImage, isSameAccountDistinctAtSpec, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine subroutine_ok.mono_outcome hraw g R' s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, isSameAccountDistinctAtSpec, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [Spec.inImage, isSameAccountDistinctAtSpec] at hpan
    rw [satisfies_pure_sepConj] at hpan; exact False.elim hpan.1
  · dsimp only [Spec.inImage, isSameAccountDistinctAtSpec] at hex
    rw [satisfies_pure_sepConj] at hex; exact False.elim hex.1
  · dsimp only [Spec.inImage, isSameAccountDistinctAtSpec] at hoom
    rw [satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
