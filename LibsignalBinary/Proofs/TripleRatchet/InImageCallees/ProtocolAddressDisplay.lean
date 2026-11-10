/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
public import LibsignalBinary.Proofs.CodeLayout
public import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `<ProtocolAddress as Display>::fmt`

Proves that `<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt` constructs
its 4-word format-argument array on the stack and delegates to `core::fmt::write`, satisfying
`addrDisplaySpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ProtocolAddressDisplay

theorem stackAt_addrDisplay (sp : BitVec 64) :
    stackAt sp addrDisplayStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 :=
  stackAt_split_cells sp extHookStack 6 (by decide)

theorem fmtWrite_tripleRatchetExterns_trap (C : Crypto)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    HookSat (Rust.withPanics (trTrapExterns C abs)) fmtWriteName (fmtWriteSpec A) := by
  have habs := tripleRatchetExterns_abs C 0#64 abs
  have h4 : Rust.withPanics (trTrapExterns C abs) fmtWriteName =
      abs fmtWriteName := by
    rw [withPanics_trTrap_eq_kit C 0#64 abs (n := fmtWriteName) (by decide)]
    exact Option.some.inj (congrArg (·[3]?) habs)
  simpa [HookSat, h4] using hW

theorem fmtWrite_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (A : RustAlloc) (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    HookSat (Rust.withPanics (tripleRatchetExterns C ctl abs)) fmtWriteName (fmtWriteSpec A) := by
  have habs := tripleRatchetExterns_abs C ctl abs
  have h4 : Rust.withPanics (tripleRatchetExterns C ctl abs) fmtWriteName =
      abs fmtWriteName := Option.some.inj (congrArg (·[3]?) habs)
  simpa [HookSat, h4] using hW

theorem fmtWrite_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff fmtWriteName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) :=
  hook_ok_at_raw (hname := fmtWriteName) rfl hk (by fnoff_eq)
    (by fnoff_eq)
    (fmtWrite_tripleRatchetExterns_trap C A abs hW)

theorem fmtWrite_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff fmtWriteName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) (fmtWriteSpec A) := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (fmtWrite_ok_at_trap (b := b) (C := C) (abs := abs) hW hk)

theorem allocFailedIn_trans {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  simpa only [allocFailedIn, htr] using h

open ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree bin [(ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt") → (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt" + 68)]

end ProtocolAddressDisplay

open ProtocolAddressDisplay

attribute [local irreducible] Program.fnAddr Program.fnOff
ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt") (ls_stub% "core::fmt::write")

theorem addrDisplay_ok_of_contract (b : BitVec 64) (A : RustAlloc)
    (H : String → Option (State → State))
    (hwrite : subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr addrDisplayName + bv% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) (fmtWriteSpec A)) :
    subroutine_ok (libsignalSessionCode.rebase b H)
      ((libsignalSessionCode.rebase b H).fnAddr addrDisplayName)
      (addrDisplaySpec A) := by
  simp only [addrDisplaySpec, stackAt_addrDisplay]
  cells_unfold
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff addrDisplayName = num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt") :=
    (ls_lemma% fnOff "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")
  code_fetches CryptoVerification.libsignalSessionCode
    bin b H hfn (num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) 72
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b H).fnAddr addrDisplayName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b H).fnAddr addrDisplayName = entry
  examples_hide_fetches
  obtain ⟨f, v, vt, bs⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt"))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (v, bs))
    (ret_pc := entry + bv% (60)) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  simp only [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps
  wp_done

theorem addrDisplay_ok_ext (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (ext : String → Option (State → State))
    (hC : Stage2Contracts b C A ctl uuidTryParse S ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext) ((tripleRatchetProgAtExt b ext).fnAddr addrDisplayName)
      (addrDisplaySpec A) :=
  addrDisplay_ok_of_contract b A (Rust.withPanics ext)
    (hC.fmt_write_ok_at addrDisplayName (num% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")))

private abbrev ImgCallInv (img : Obj.Image) (s : State) : Prop :=
  img.FrozenLoaded s ∧ s.symtab = img.symtab

private theorem ImgCallInv.of_steps {img : Obj.Image} {prog : Program} {s s' : State}
    (h : ImgCallInv img s) (hs : Steps prog s s') : ImgCallInv img s' :=
  ⟨h.1.of_keepsFrozen hs.keepsFrozen, hs.symtab_eq.trans h.2⟩

private theorem SepWPp.of_sepWP_inImage {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => ImgCallInv img sm → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, hoom⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext (hinv.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact (not_satisfies_false_sepConj hoom).elim

private theorem call_frame_inImage {prog : Program} {img : Obj.Image} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    {α : Type} {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hinv : ImgCallInv img s)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) → (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  dsimp only [Spec.inImage]
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hinv, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

theorem addrDisplay_ok_of_contract_inImage (img : Obj.Image) (A : RustAlloc)
    (H : String → Option (State → State))
    (hwrite : subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr addrDisplayName + bv% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt"))
      ((fmtWriteSpec A).inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase img.base H)
      ((libsignalSessionCode.rebase img.base H).fnAddr addrDisplayName)
      ((addrDisplaySpec A).inImage img) := by
  unfold Spec.inImage
  simp only [addrDisplaySpec, stackAt_addrDisplay]
  cells_unfold
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff addrDisplayName = num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt") :=
    (ls_lemma% fnOff "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")
  code_fetches CryptoVerification.libsignalSessionCode
    bin img.base H hfn (num% (ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) 72
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base H).fnAddr addrDisplayName := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base H).fnAddr addrDisplayName = entry
  examples_hide_fetches
  obtain ⟨f, v, vt, bs⟩ := x
  dsimp only at *
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  apply SepWPp.of_sepWP_inImage (mid := entry + bv% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) hinv0
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv1
  refine call_frame_inImage (spec := fmtWriteSpec A) (x := (v, bs))
    (ret_pc := entry + bv% (60)) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    hinv1
    (by simp only [fmtWriteSpec, arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  simp only [fmtWriteSpec, sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps
  wp_done

theorem addrDisplay_ok_ext_x {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext) ((tripleRatchetProgAtExt img.base ext).fnAddr addrDisplayName)
      ((addrDisplaySpec A).inImage img) :=
  addrDisplay_ok_of_contract_inImage img A (Rust.withPanics ext)
    (hC.fmt_write_ok_at addrDisplayName (num% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")))

theorem addrDisplay_ok_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    subroutine_ok (trTrapProgAt b C abs) ((trTrapProgAt b C abs).fnAddr addrDisplayName)
      (addrDisplaySpec A) :=
  addrDisplay_ok_of_contract b A (Rust.withPanics (trTrapExterns C abs))
    (fmtWrite_ok_at_trap (b := b) (C := C)
      (name := addrDisplayName) (k := num% (ls_off% "core::fmt::write" - ls_off% "<libsignal_core::address::ProtocolAddress as core::fmt::Display>::fmt")) hW)

theorem addrDisplay_ok (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hW : HookSat abs fmtWriteName (fmtWriteSpec A)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr addrDisplayName)
      (addrDisplaySpec A) := by
  simp only [← trTrapProgAt_fnAddr_eq]
  exact subroutine_ok_kit_of_trTrap (addrDisplay_ok_trap b C A abs hW)

/-! ## Relocatable per-block proofs (`[LibsignalPlacement]`) -/

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) parameterized by `hwrite`. -/
theorem addrDisplay_placed_ok_of_contract [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hwrite : subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (lsρ lsFmtWriteSym) (fmtWriteSpec A)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplaySpec A) := by
  simp only [addrDisplaySpec, stackAt_addrDisplay]
  cells_unfold
  wpp_init x s0
  obtain ⟨f, v, vt, bs⟩ := x
  dsimp only at *
  apply SepWPp.of_sepWP (mid := lsρ lsFmtWriteSym)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (v, bs))
    (ret_pc := (blkPl_215).base + bv% (60)) hwrite
    (by simp only [arm64_norm]) (by simp only [arm64_norm, hrun])
    (by simp only [State.spAligned, arm64_norm]; exact hsp_align)
    (by simp only [arm64_norm])
    (by simp only [arm64_norm]; rfl)
    (rfl : v = v)
    (by sep_focus)
    (fun _ _ _ _ hex => allowPanic_not_exited hex)
    (fun sf _ hpan => allowPanic_frame (allocFailedIn_trans (by simp only [arm64_norm])) hpan) ?_
  intro sm hpcm hrunm hspm hcsm
  simp only [CalleeSavedPreserved] at hcsm
  obtain ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩ := hcsm
  simp (config := { decide := true }) only [arm64_norm] at hpcm hspm hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp hvregs
  apply SepWPp.of_sepWP_ret
  simp only [sepExists_sepConj_left, sepConj_assoc, arm64_norm]
  apply SepWP.exists_elim; intro bs'
  apply SepWP.pure_elim; rintro ⟨hw0, htr⟩
  wp_steps
  wp_done

/-- Relocatable `<ProtocolAddress as Display>::fmt` (Block `215`) meets `addrDisplaySpec A`. -/
theorem addrDisplay_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hW : HookSat H lsFmtWriteSym (fmtWriteSpec A)) :
    subroutine_ok ((blkPC_215).rebase (blkPl_215).base H)
      (blkPl_215).base
      (addrDisplaySpec A) :=
  addrDisplay_placed_ok_of_contract A H (ls_hook_ok_of_mem hW)

end CryptoVerification.LibsignalTripleRatchet
