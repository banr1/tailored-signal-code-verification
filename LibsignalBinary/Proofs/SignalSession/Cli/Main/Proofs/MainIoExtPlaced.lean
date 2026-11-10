/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.IoHooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.MainWrapIo
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliExternsFixed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 2000000

/-!
# Placed `MainIoPlaced` Bundle from `CliExternsOk`

Derives `MainIoPlaced A H cliIo stk` from `ExtIoLookup` and `CliExternsOk P A ext`.
-/
namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 Arm64.Obj ProofLib CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Main.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

private theorem stackAt_split_ext_io {sp : BitVec 64} {stk : Nat}
    (hle : extHookStack ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk = memRegion (sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ stackAt sp extHookStack := by
  have h1 := stackAt_split_bottom sp extHookStack (stk - extHookStack) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

structure ExtIoLookup (img : Obj.Image) (ext : String → Option (State → State)) (H : LibsignalHooks) : Prop where
  readStdin : H lsReadStdinSym = (ext SignalSession.readStdinName).map (wrapIoHook img)
  readFile : H lsReadFileSym = (ext SignalSession.readFileName).map (wrapIoHook img)
  writeFile : H lsWriteFileSym = (ext SignalSession.writeFileName).map (wrapIoHook img)
  writeStdout : H lsWriteStdoutSym = (ext SignalSession.writeStdoutName).map (wrapIoHook img)

theorem mainIoPlaced_of_lookup [LibsignalPlacement]
    {P : E2E.PEParams} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {H : LibsignalHooks}
    (hal : img.base.toNat % 4 = 0) (hL : ExtIoLookup img ext H) (hOk : CliExternsOk P A ext)
    (stk : Nat := extHookStack) (hle : extHookStack ≤ stk := by decide) (hmax : stk ≤ 2 ^ 64 := by decide) :
    MainIoPlaced A H cliIo stk where
  readStdin := by
    let img0 := symtabOnlyImage img; rcases hOk.readStdin img0 with ⟨f, hf, hh⟩
    have hh_in : HookOk f ((readStdinSpecPlaced cliIo A stk).inImage img0) := fun x R s0 hrun hpre hsp => by
      have hsplit := stackAt_split_ext_io (sp := s0.sp) hle hmax
      have h_stdin : cliIo.stdin = CliExt.stdinBytes := rfl
      have h_iov : CliExt.ioVecAt = ioVecAt := rfl
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.ret, x.bs⟩ R' s0 hrun
        (by
          dsimp only [readStdinSpecPlaced, CliExt.readStdinSpec, Spec.inImage, R'] at hpre ⊢
          rw [hsplit, h_stdin] at hpre; ac_nf at hpre ⊢) hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hs, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [readStdinSpecPlaced, CliExt.readStdinSpec, Spec.inImage, R'] at hpost ⊢
        rw [h_iov] at hpost; rw [hsplit]; ac_nf at hpost ⊢
      · refine Or.inr (Or.inl ⟨hs, ?_⟩); dsimp only [readStdinSpecPlaced, CliExt.readStdinSpec, Spec.inImage, R'] at hpan ⊢
        exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) (by ac_nf at hpan ⊢ :
          (f s0).mem ⊨ (⌜allocFailedIn s0 (f s0) ∧ s0.trace <+: (f s0).trace⌝ ∗
            (anyHeap ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R)
      · dsimp only [CliExt.readStdinSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.readStdinSpec, Spec.inImage] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim
    exact subroutine_ok_rocl_of_plain <| ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨wrapIoHook img f, by rw [hL.readStdin, hf]; rfl, hookOk_wrapIoHook_of_inImage hal (rfl_specSymtabFree _) hh_in⟩ (by decide)
  readFile := by
    let img0 := symtabOnlyImage img; rcases hOk.readFile img0 with ⟨f, hf, hh⟩
    have hh_in : HookOk f ((readFileLitSpecPlaced cliIo A stk).inImage img0) := fun x R s0 hrun hpre hsp => by
      have hsplit := stackAt_split_ext_io (sp := s0.sp) hle hmax
      have h_bytesAt : CliExt.bytesAt true x.pathA x.path = (x.pathA ↦ᵣ x.path) := rfl
      have h_pathOk : cliIo.pathOk = CliExt.cliPathOk := rfl
      have h_rd : cliIo.rd = CliExt.readFileResult := rfl
      have h_iov : CliExt.ioVecAt = ioVecAt := rfl
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.pathA, true, x.path, x.ret⟩ R' s0 hrun
        (by dsimp only [readFileLitSpecPlaced, CliExt.readFileSpec, Spec.inImage, R'] at hpre ⊢
            rw [hsplit, h_pathOk] at hpre; rw [h_bytesAt]; ac_nf at hpre ⊢) hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hs, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [readFileLitSpecPlaced, CliExt.readFileSpec, Spec.inImage, R'] at hpost ⊢
        rw [h_bytesAt, ← h_rd, h_iov] at hpost; rw [hsplit]; ac_nf at hpost ⊢
      · refine Or.inr (Or.inl ⟨hs, ?_⟩); dsimp only [readFileLitSpecPlaced, CliExt.readFileSpec, Spec.inImage, R'] at hpan ⊢
        exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (entails_anyHeap _))) (by ac_nf at hpan ⊢ :
          (f s0).mem ⊨ (⌜allocFailedIn s0 (f s0) ∧ s0.trace <+: (f s0).trace⌝ ∗
            (anyHeap ∗ memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack))) ∗ R)
      · dsimp only [CliExt.readFileSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.readFileSpec, Spec.inImage] at hoom; rw [satisfies_pure_sepConj] at hoom; exact hoom.1.elim
    exact subroutine_ok_rocl_of_plain <| ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨wrapIoHook img f, by rw [hL.readFile, hf]; rfl, hookOk_wrapIoHook_of_inImage hal (rfl_specSymtabFree _) hh_in⟩ (by decide)
  writeFile := by
    let img0 := symtabOnlyImage img; rcases hOk.writeFile img0 with ⟨f, hf, hh⟩
    have hh_in : HookOk f ((writeFileSpecPlaced cliIo stk).inImage img0) := fun x R s0 hrun hpre hsp => by
      have hsplit := stackAt_split_ext_io (sp := s0.sp) hle hmax
      have h_pathOk : cliIo.pathOk = CliExt.cliPathOk := rfl
      have h_wr : cliIo.wr = CliExt.writeFileResult := rfl
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.pathA, x.path, x.buf, x.bs⟩ R' s0 hrun
        (by dsimp only [writeFileSpecPlaced, CliExt.writeFileSpec, Spec.inImage, R'] at hpre ⊢
            rw [hsplit, h_pathOk] at hpre; ac_nf at hpre ⊢) hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hex⟩ | ⟨_, _, hex⟩ | ⟨_, hex⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [writeFileSpecPlaced, CliExt.writeFileSpec, Spec.inImage, R'] at hpost ⊢
        rw [← h_wr] at hpost; rw [hsplit]; ac_nf at hpost ⊢
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeFileSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
    exact subroutine_ok_rocl_of_plain <| ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨wrapIoHook img f, by rw [hL.writeFile, hf]; rfl, hookOk_wrapIoHook_of_inImage hal (rfl_specSymtabFree _) hh_in⟩ (by decide)
  writeStdout := by
    let img0 := symtabOnlyImage img; rcases hOk.writeStdout img0 with ⟨f, hf, hh⟩
    have hh_in : HookOk f ((writeStdoutSpecPlaced stk).inImage img0) := fun x R s0 hrun hpre hsp => by
      have hsplit := stackAt_split_ext_io (sp := s0.sp) hle hmax
      let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - extHookStack) ∗ R
      obtain ⟨hkf, hsym, hout⟩ := hh ⟨x.buf, x.bs⟩ R' s0 hrun
        (by dsimp only [writeStdoutSpecPlaced, CliExt.writeStdoutSpec, Spec.inImage, R'] at hpre ⊢
            rw [hsplit] at hpre; ac_nf at hpre ⊢) hsp
      refine ⟨hkf, hsym, ?_⟩
      rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hex⟩ | ⟨_, _, hex⟩ | ⟨_, hex⟩
      · refine Or.inl ⟨hret, hcc, ?_⟩
        dsimp only [writeStdoutSpecPlaced, CliExt.writeStdoutSpec, Spec.inImage, R'] at hpost ⊢
        rw [hsplit]; ac_nf at hpost ⊢
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
      · dsimp only [CliExt.writeStdoutSpec, Spec.inImage] at hex; rw [satisfies_pure_sepConj] at hex; exact hex.1.elim
    exact subroutine_ok_rocl_of_plain <| ls_hook_ok_ultra_of_mem (prog := lsProg_617 H) (i := 617)
      ⟨wrapIoHook img f, by rw [hL.writeStdout, hf]; rfl, hookOk_wrapIoHook_of_inImage hal (rfl_specSymtabFree _) hh_in⟩ (by decide)

end CryptoVerification.SignalSession.Cli.MainHops
