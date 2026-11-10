/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliImgPlacement

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.MainHops.CliImgLift

open Arm64 ProofLib
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.MainHops.CliImgPlacement
open CryptoVerification.LibsignalPublicApi.StoreKit

theorem nonRunning_steps_eq {prog : Program} {s1 s2 : State}
    (h : s1.status ≠ .Running) (hs : Steps prog s1 s2) : s2 = s1 := by
  cases hs with
  | refl => rfl
  | step h1 _ =>
    cases h1 with
    | exec hr _ => exact absurd hr h
    | halt_unmapped hr _ _ => exact absurd hr h
    | extern hr _ _ _ => exact absurd hr h
    | extern_fault hr _ _ => exact absurd hr h

theorem steps_trans {prog : Program} {s1 s2 s3 : State}
    (h1 : Steps prog s1 s2) (h2 : Steps prog s2 s3) : Steps prog s1 s3 := by
  induction h1 with
  | refl => exact h2
  | step hs _ ih => exact Steps.step hs (ih h2)

private theorem findSome_symbols_none (L : List (String × Nat)) (off : Nat) :
    (L.findSome? fun x =>
      if (x.2 == off) = true then (none : Option (State → State)) else none) = none := by
  induction L with
  | nil => rfl
  | cons hd _ ih =>
    cases h : hd.2 == off
    · simp only [List.findSome?_cons, h, Bool.false_eq_true, ↓reduceIte, ih]
    · simp only [List.findSome?_cons, h, ↓reduceIte, ih]

theorem externAt?_ofImage_eq (img : Obj.Image) (Y : String → Option (State → State))
    (pc : BitVec 64) :
    (Program.ofImage img Y).externAt? pc =
      img.stubs.findSome? fun (n, o) => if o == (pc - img.base).toNat then Y n else none := by
  dsimp only [Program.externAt?, Program.hookAtOff?, Program.ofImage]
  rw [findSome_symbols_none, Option.or_none]

private theorem findSome_stubs_isSome {Y Z : String → Option (State → State)}
    (hDom : ∀ n, (Y n).isSome = (Z n).isSome) (L : List (String × Nat)) (off : Nat) :
    (L.findSome? fun (n, o) => if o == off then Y n else none).isSome =
      (L.findSome? fun (n, o) => if o == off then Z n else none).isSome := by
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    by_cases ho : o == off
    · simp only [List.findSome?_cons, ho, ↓reduceIte]
      have hd_eq := hDom n
      cases hY : Y n <;> cases hZ : Z n
      · exact ih
      · simp [hY, hZ] at hd_eq
      · simp [hY, hZ] at hd_eq
      · rfl
    · simp only [List.findSome?_cons, ho, Bool.false_eq_true, ↓reduceIte]
      exact ih

private theorem findSome_stubs_some {img : Obj.Image} {Y Z : String → Option (State → State)}
    (hDom : ∀ n, (Y n).isSome = (Z n).isSome)
    (hApp : ∀ n fY s, Y n = some fY → img.CallInv s → ∃ fZ, Z n = some fZ ∧ fZ s = fY s)
    (L : List (String × Nat)) (off : Nat) {fY : State → State} {s : State}
    (h : (L.findSome? fun (n, o) => if o == off then Y n else none) = some fY)
    (hinv : img.CallInv s) :
    ∃ fZ, (L.findSome? fun (n, o) => if o == off then Z n else none) = some fZ ∧ fZ s = fY s := by
  induction L with
  | nil => simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    by_cases ho : o == off
    · have hd_eq := hDom n
      cases hY : Y n with
      | none =>
        cases hZ : Z n with
        | none =>
          simp only [List.findSome?_cons, ho, ↓reduceIte, hY] at h
          simp only [List.findSome?_cons, ho, ↓reduceIte, hZ]
          exact ih h
        | some _ => simp [hY, hZ] at hd_eq
      | some gY =>
        simp only [List.findSome?_cons, ho, ↓reduceIte, hY] at h
        cases h
        obtain ⟨fZ, hZ, heval⟩ := hApp n fY s hY hinv
        exact ⟨fZ, by simp only [List.findSome?_cons, ho, ↓reduceIte, hZ], heval⟩
    · simp only [List.findSome?_cons, ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h

private theorem mProgPlaced_svc [LibsignalPlacement] (H : LibsignalHooks) :
    (mProgPlaced H).svc = Syscall.standard := by
  rw [(inferInstance : IsLsBlockProg (mProgPlaced H) 617 H).eq_blockProgram]
  rfl

theorem steps_lift_placed {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {H : LibsignalHooks} {Y Z : String → Option (State → State)}
    (hH : ∀ pc,
      (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement H).externAt? pc =
        (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
          (liftHooksToPlaced Y)).externAt? pc)
    (hDom : ∀ n, (Y n).isSome = (Z n).isSome)
    (hApp : ∀ n fY s, Y n = some fY → img.CallInv s → ∃ fZ, Z n = some fZ ∧ fZ s = fY s)
    {s sf : State} (hinv : img.CallInv s)
    (hOut : sf.status = .Running ∨ sf.status = .Panicked ∨ sf.status = .OutOfMemory)
    (hs : Steps (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement H) s sf) :
    Steps (Program.ofImage img Z) s sf ∧ img.CallInv sf := by
  let _ : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  induction hs with
  | refl => exact ⟨Steps.refl _, hinv⟩
  | @step s1 s2 sf h1 h2 ih =>
    cases h1 with
    | halt_unmapped _ _ _ =>
      have hsf : sf = { s1 with status := .Halted } := nonRunning_steps_eq (by simp) h2
      rcases hOut with h | h | h <;> simp [hsf] at h
    | extern_fault _ _ _ =>
      have hsf := nonRunning_steps_eq (by simp) h2
      rcases hOut with h | h | h <;> simp [hsf] at h
    | @exec inst hr hfetch =>
      by_cases hdead : lsDeadImgStubOffs.any (· == (s1.pc - img.base).toNat) = true
      · have hcl0 : (Program.ofImageWithSvc noSyscalls img).CodeLoaded s1.mem :=
          hinv.1.codeLoaded.of_base_code rfl rfl
        obtain ⟨_, hfetch_none⟩ := mProgPlaced_dead_stub_none himg Y s1.pc hcl0 hdead
        have hfH : (mProgPlaced H).fetchMem s1.mem s1.pc =
            (mProgPlaced (liftHooksToPlaced Y)).fetchMem s1.mem s1.pc := by
          simp only [Program.fetchMem, hH s1.pc]
        rw [hfH, hfetch_none] at hfetch
        cases hfetch
      · have hnd : lsDeadImgStubOffs.any (· == (s1.pc - img.base).toNat) = false :=
          Bool.eq_false_iff.mpr hdead
        have hextY : (mProgPlaced H).externAt? s1.pc = (Program.ofImage img Y).externAt? s1.pc :=
          (hH s1.pc).trans (mProgPlaced_externAt_eq_of_not_dead himg Y s1.pc hnd)
        have hisSome : ((mProgPlaced H).externAt? s1.pc).isSome =
            ((Program.ofImage img Z).externAt? s1.pc).isSome := by
          rw [hextY, externAt?_ofImage_eq, externAt?_ofImage_eq]
          exact findSome_stubs_isSome hDom img.stubs (s1.pc - img.base).toNat
        have hfetchZ : (Program.ofImage img Z).fetchMem s1.mem s1.pc = some inst := by
          simpa only [Program.fetchMem, ← hisSome] using hfetch
        have hevalZ : (mProgPlaced H).evalInst inst s1 =
            (Program.ofImage img Z).evalInst inst s1 := by
          simp only [Program.evalInst, mProgPlaced_svc]
          rfl
        have hstepZ : Step (Program.ofImage img Z) s1 ((mProgPlaced H).evalInst inst s1) :=
          hevalZ ▸ Step.exec hr hfetchZ
        have hinv2 : img.CallInv ((mProgPlaced H).evalInst inst s1) :=
          hinv.of_steps (Steps.step hstepZ (Steps.refl _))
        obtain ⟨hrestZ, hinv_f⟩ := ih hinv2 hOut
        exact ⟨Steps.step hstepZ hrestZ, hinv_f⟩
    | @extern f hr hext hkeep hsym =>
      by_cases hdead : lsDeadImgStubOffs.any (· == (s1.pc - img.base).toNat) = true
      · have hcl0 : (Program.ofImageWithSvc noSyscalls img).CodeLoaded s1.mem :=
          hinv.1.codeLoaded.of_base_code rfl rfl
        obtain ⟨hext_none, _⟩ := mProgPlaced_dead_stub_none himg Y s1.pc hcl0 hdead
        rw [hH s1.pc, hext_none] at hext
        cases hext
      · have hnd : lsDeadImgStubOffs.any (· == (s1.pc - img.base).toNat) = false :=
          Bool.eq_false_iff.mpr hdead
        have hextY : (Program.ofImage img Y).externAt? s1.pc = some f := by
          rw [← mProgPlaced_externAt_eq_of_not_dead himg Y s1.pc hnd, ← hH s1.pc]
          exact hext
        rw [externAt?_ofImage_eq] at hextY
        obtain ⟨fZ, hfindZ, heval⟩ := findSome_stubs_some hDom hApp img.stubs
          (s1.pc - img.base).toNat hextY hinv
        have hextZ : (Program.ofImage img Z).externAt? s1.pc = some fZ := by
          rw [externAt?_ofImage_eq]; exact hfindZ
        have hstepZ : Step (Program.ofImage img Z) s1 (f s1) := by
          rw [← heval]
          exact Step.extern hr hextZ (heval.symm ▸ hkeep) (heval.symm ▸ hsym)
        have hinv2 : img.CallInv (f s1) := hinv.of_keepsFrozen hsym hkeep
        obtain ⟨hrestZ, hinv_f⟩ := ih hinv2 hOut
        exact ⟨Steps.step hstepZ hrestZ, hinv_f⟩

theorem sepWPp_lift_placed {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {H : LibsignalHooks} {Y Z : String → Option (State → State)}
    (hH : ∀ pc,
      (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement H).externAt? pc =
        (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement
          (liftHooksToPlaced Y)).externAt? pc)
    (hDom : ∀ n, (Y n).isSome = (Z n).isSome)
    (hApp : ∀ n fY s, Y n = some fY → img.CallInv s → ∃ fZ, Z n = some fZ ∧ fZ s = fY s)
    {ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hinv : img.CallInv s)
    (hwp : SepWPp (@mProgPlaced (instLibsignalFullPlacementOfLoads img himg).toLibsignalPlacement H)
      ret s P Q Qp oom) :
    SepWPp (Program.ofImage img Z) ret s P
      (fun sf Pf => Q sf Pf ∧ img.CallInv sf)
      (fun sf Pf => Qp sf Pf ∧ img.CallInv sf) oom := by
  let _ : LibsignalFullPlacement := instLibsignalFullPlacementOfLoads img himg
  let _ : LsCodeInv (LibsignalFrozen (imgMultiPlacement img)) := instLsCodeInvFrozen
  intro R hmem _hclZ
  have hclP : (mProgPlaced H).CodeLoaded s.mem :=
    LsCodeInv.codeLoaded_mProgPlaced (img_libsignalFrozen himg hinv.1) H
  obtain ⟨sf, hstepsP, hPost⟩ := hwp R hmem hclP
  have hOut : sf.status = .Running ∨ sf.status = .Panicked ∨ sf.status = .OutOfMemory := by
    rcases hPost with ⟨_, hr, _⟩ | ⟨hp, _⟩ | ⟨ho, _⟩
    · exact Or.inl hr
    · exact Or.inr (Or.inl hp)
    · exact Or.inr (Or.inr ho)
  obtain ⟨hstepsZ, hinv_f⟩ := steps_lift_placed himg hH hDom hApp hinv hOut hstepsP
  refine ⟨sf, hstepsZ, ?_⟩
  rcases hPost with ⟨hpc, hr, Pf, hm, hq⟩ | ⟨hp, Pf, hm, hqp⟩ | ⟨ho, hm⟩
  · exact Or.inl ⟨hpc, hr, Pf, hm, hq, hinv_f⟩
  · exact Or.inr (Or.inl ⟨hp, Pf, hm, hqp, hinv_f⟩)
  · exact Or.inr (Or.inr ⟨ho, hm⟩)

theorem sepWPp_bind_running {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q1 Q2 Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h1 : SepWPp prog mid s P Q1 Qp oom)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running → Q1 sm Pm →
      SepWPp prog ret sm Pm Q2 Qp oom) :
    SepWPp prog ret s P Q2 Qp oom := by
  intro R hmem hcl
  obtain ⟨sm, hsteps1, hPost1⟩ := h1 R hmem hcl
  rcases hPost1 with ⟨hpc, hr, Pm, hm, hq1⟩ | ⟨hp, Pm, hm, hqp⟩ | ⟨ho, hm⟩
  · have hcl_m : prog.CodeLoaded sm.mem := hsteps1.codeLoaded hcl
    obtain ⟨sf, hsteps2, hPost2⟩ := h2 sm Pm hpc hr hq1 R hm hcl_m
    exact ⟨sf, steps_trans hsteps1 hsteps2, hPost2⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inl ⟨hp, Pm, hm, hqp⟩)⟩
  · exact ⟨sm, hsteps1, Or.inr (Or.inr ⟨ho, hm⟩)⟩

end CryptoVerification.SignalSession.Cli.MainHops.CliImgLift
