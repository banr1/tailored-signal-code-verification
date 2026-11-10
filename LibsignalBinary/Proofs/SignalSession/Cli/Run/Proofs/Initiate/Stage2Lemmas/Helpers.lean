/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Fetch
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Common

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Process ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.E2E
open CryptoVerification.LibsignalSession CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open CryptoVerification.LibsignalPublicApi.StoreSession

theorem w0_low_byte_zero {v : BitVec 64} (h : v.setWidth 32 = 0#32) :
    (v.setWidth 32).setWidth 8 = 0#8 ∧
      v.setWidth 8 = 0#8 ∧
      BitVec.extractLsb' 0 8 (v.setWidth 32) = 0#8 := by
  refine ⟨?_, ?_, ?_⟩ <;> bv_bits

theorem clamp_b31_eq_bfi (b31 : BitVec 8) :
    ((64#8) ||| (b31 &&& 63#8)) = ((b31 &&& 0x7f#8) ||| 0x40#8) := by
  bv_bits

theorem initFreshRecAt_eq_fsp (fsp : BitVec 64) :
    initFreshRecAt fsp =
      ((fsp + 296#64) ↦₆₄ 0#64) ∗ ((fsp + 304#64) ↦₆₄ 8#64) ∗
      ((fsp + 312#64) ↦₆₄ 0#64) ∗ ((fsp + 320#64) ↦₆₄ (0#64 - 1#64)) :=
  rfl

theorem pointsToBytes_ends (a : BitVec 64) (b0 b31 : BitVec 8) (mid : List (BitVec 8))
    (hmid : mid.length = 30) :
    (a ↦ₛ ([b0] ++ mid ++ [b31])) =
      (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ mid) ∗ ((a + 31#64) ↦₈ b31) := by
  have hb31 : ∀ p : BitVec 64, (p ↦ₛ [b31]) = (p ↦₈ b31) := fun p => by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  have hb0 : (a ↦ₛ ([b0] ++ mid)) = (a ↦₈ b0) ∗ ((a + 1#64) ↦ₛ mid) := by
    simp only [List.singleton_append, pointsToBytes_cons]
  rw [pointsToBytes_append, hb0, hb31]
  have hlen : ([b0] ++ mid).length = 31 := by simp [hmid]
  rw [hlen, sepConj_assoc]

theorem sepWP_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog tgt s P post oom) :
    SepWP prog tgt s (cell ∗ P) post oom :=
  SepWP.weaken_pre_frame (fun _ hm => Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) h

theorem sepWPp_drop_left {prog : Program} {tgt : BitVec 64} {s : State}
    {cell P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWPp prog tgt s P Q Qp oom) :
    SepWPp prog tgt s (cell ∗ P) Q Qp oom := fun R hm hL =>
  h R (Satisfies.of_sep_right (by rwa [sepConj_assoc] at hm)) hL

theorem sepWPp_with_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {P R0 : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hro : ∀ Q0, s.mem ⊨ Q0 → s.mem ⊨ R0 ∗ Q0)
    (h : SepWPp prog ret s (R0 ∗ P) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  h R (by rw [sepConj_assoc]; exact hro (P ∗ R) hm) hL

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (himp : P ⊢ P') (h : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := fun R hm hL =>
  h R (Arm64.Satisfies.mono (sepConj_mono_left himp) hm) hL

theorem sepWPp_pure_left {prog : Program} {ret : BitVec 64} {s : State}
    {φ : Prop} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (⌜φ⌝ ∗ P) Q Qp oom := fun R hm hL => by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact h hm.1 R hm.2 hL

theorem sepWPp_exists_left {α : Type} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a : α, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom :=
  SepWPp.exists_elim h

theorem sepWPp_panic_handleError {img : Obj.Image} {W : CliHooks}
    {target_pc : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (initProg img W).fnAddr handleErrorName)
    (hrun : s.status = .Running)
    (hpan : Qp (Rust.panicked s) P) :
    SepWPp (initProg img W) target_pc s P Q Qp oom :=
  SepWPp.panic hrun (hpc ▸ handleError_externAt img W) hpan

theorem initPanicPost_of_false (A : RustAlloc) (img : Obj.Image) (S : RunSem)
    (x : InitGhost) (stk : Nat) {s0 sf : State} (F : SepProp) :
    InitPanicPost A img S x stk s0 sf (⌜False⌝ ∗ F) :=
  Entails.pure_left False.elim

theorem fnAddr_cliInitiate_eq (img : Obj.Image) (W : CliHooks) :
    (initProg img W).fnAddr cliInitiateName =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) := by
  simp only [initProg, tripleRatchetProgAtExt, Program.fnAddr_rebase, cliInitiate_fnOff]

theorem inInitiate_after_call {img : Obj.Image} {W : CliHooks} {s0 s sm sf : State} {k0 k1 : Nat}
    (hctrl : InInitiate img W s0 s k0)
    (hsp1 : sm.sp = s.sp)
    (hfp1 : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19_1 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hsym1 : sm.symtab = s.symtab)
    (hvregs1 : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf1 : s.mem.KeepsFrozen sm.mem)
    (hfiles1 : sm.fs.files = s.fs.files)
    (hpc2 : sf.pc = initPc img W k1)
    (hrun2 : sf.status = .Running)
    (hsp2 : sf.sp = sm.sp)
    (hcs2 : CalleeSavedPreserved sm sf)
    (hkf2 : sm.mem.KeepsFrozen sf.mem)
    (hsym2 : sf.symtab = sm.symtab)
    (hfiles2 : sf.fs.files = sm.fs.files) :
    InInitiate img W s0 sf k1 := by
  rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hvregs2⟩
  exact
    { pc := hpc2
      run := hrun2
      sp := hsp2.trans (hsp1.trans hctrl.sp)
      fp := hfp2.trans (hfp1.trans hctrl.fp)
      x19 := hx19_2.trans (hx19_1.trans hctrl.x19)
      files0 := hfiles2.trans (hfiles1.trans hctrl.files0)
      inv := imgCallInv_of_keepsFrozen (imgCallInv_of_keepsFrozen hctrl.inv hkf1 hsym1) hkf2 hsym2
      vregs := hvregs2.trans (hvregs1.trans hctrl.vregs)
      spAligned := hctrl.spAligned }

theorem InInitiate.toExt {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiate img W s0 s k) :
    InInitiateExt img (cliHookExterns W) s0 s k :=
  ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

theorem InInitiateExt.toLegacy {img : Obj.Image} {W : CliHooks} {s0 s : State} {k : Nat}
    (h : InInitiateExt img (cliHookExterns W) s0 s k) :
    InInitiate img W s0 s k :=
  ⟨h.pc, h.run, h.sp, h.fp, h.x19, h.files0, h.inv, h.vregs, h.spAligned⟩

theorem sepWPp_panic_handleError_ext {img : Obj.Image}
    {ext : String → Option (State → State)}
    {target_pc : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hpc : s.pc = (initProgExt img ext).fnAddr handleErrorName)
    (hrun : s.status = .Running)
    (hpan : Qp (Rust.panicked s) P) :
    SepWPp (initProgExt img ext) target_pc s P Q Qp oom :=
  SepWPp.panic hrun (hpc ▸ handleError_externAt_ext img ext) hpan

theorem fnAddr_cliInitiate_ext_eq (img : Obj.Image)
    (ext : String → Option (State → State)) :
    (initProgExt img ext).fnAddr cliInitiateName =
      img.base + BitVec.ofNat 64 (num% (ls_off% "libsignal_cli_handshake::initiate")) := by
  simp only [initProgExt, tripleRatchetProgAtExt, Program.fnAddr_rebase, cliInitiate_fnOff]

theorem inInitiateExt_after_call {img : Obj.Image} {ext : String → Option (State → State)}
    {s0 s sm sf : State} {k0 k1 : Nat}
    (hctrl : InInitiateExt img ext s0 s k0)
    (hsp1 : sm.sp = s.sp)
    (hfp1 : sm.readReg64 .fp = s.readReg64 .fp)
    (hx19_1 : sm.readReg64 (.gpr 19#5) = s.readReg64 (.gpr 19#5))
    (hsym1 : sm.symtab = s.symtab)
    (hvregs1 : calleeSavedVRegs sm = calleeSavedVRegs s)
    (hkf1 : s.mem.KeepsFrozen sm.mem)
    (hfiles1 : sm.fs.files = s.fs.files)
    (hpc2 : sf.pc = initPcExt img ext k1)
    (hrun2 : sf.status = .Running)
    (hsp2 : sf.sp = sm.sp)
    (hcs2 : CalleeSavedPreserved sm sf)
    (hkf2 : sm.mem.KeepsFrozen sf.mem)
    (hsym2 : sf.symtab = sm.symtab)
    (hfiles2 : sf.fs.files = sm.fs.files) :
    InInitiateExt img ext s0 sf k1 := by
  rcases hcs2 with ⟨hx19_2, _, _, _, _, _, _, _, _, _, hfp2, hvregs2⟩
  exact
    { pc := hpc2
      run := hrun2
      sp := hsp2.trans (hsp1.trans hctrl.sp)
      fp := hfp2.trans (hfp1.trans hctrl.fp)
      x19 := hx19_2.trans (hx19_1.trans hctrl.x19)
      files0 := hfiles2.trans (hfiles1.trans hctrl.files0)
      inv := imgCallInv_of_keepsFrozen (imgCallInv_of_keepsFrozen hctrl.inv hkf1 hsym1) hkf2 hsym2
      vregs := hvregs2.trans (hvregs1.trans hctrl.vregs)
      spAligned := hctrl.spAligned }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

