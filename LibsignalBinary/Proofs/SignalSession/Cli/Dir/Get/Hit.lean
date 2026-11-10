/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Decode
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Shared Epilogues, Panic Exit, and Cache-Hit Exit for `<signal_session::stores::Dir>::get`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.Get.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Alloc
open DoReserveNorm

/-- Callee-saved state not saved on `Dir::get`'s frame (`x25..x28` and `v8..v15`). -/
def HighCalleeSaved (s0 s : State) : Prop :=
  s.readReg64 (.gpr 25#5) = s0.readReg64 (.gpr 25#5) ∧
  s.readReg64 (.gpr 26#5) = s0.readReg64 (.gpr 26#5) ∧
  s.readReg64 (.gpr 27#5) = s0.readReg64 (.gpr 27#5) ∧
  s.readReg64 (.gpr 28#5) = s0.readReg64 (.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

theorem HighCalleeSaved.refl (s0 : State) : HighCalleeSaved s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem HighCalleeSaved.of_calleeSaved {s0 s sf : State}
    (h0 : HighCalleeSaved s0 s) (hcs : CalleeSavedPreserved s sf) :
    HighCalleeSaved s0 sf := by
  obtain ⟨_, _, _, _, _, _, c25, c26, c27, c28, _, cv⟩ := hcs
  exact ⟨c25.trans h0.1, c26.trans h0.2.1, c27.trans h0.2.2.1,
         c28.trans h0.2.2.2.1, cv.trans h0.2.2.2.2⟩

theorem HighCalleeSaved.of_steps {s0 s s' : State}
    (h0 : HighCalleeSaved s0 s)
    (h25 : s'.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5))
    (h26 : s'.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (h27 : s'.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5))
    (h28 : s'.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5))
    (hv : calleeSavedVRegs s' = calleeSavedVRegs s) :
    HighCalleeSaved s0 s' :=
  ⟨h25.trans h0.1, h26.trans h0.2.1, h27.trans h0.2.2.1,
   h28.trans h0.2.2.2.1, hv.trans h0.2.2.2.2⟩

theorem HighCalleeSaved.of_step_call {s0 s s_pre sf : State}
    (h0 : HighCalleeSaved s0 s)
    (hcs : CalleeSavedPreserved s_pre sf)
    (h25 : s_pre.readReg64 (.gpr 25#5) = s.readReg64 (.gpr 25#5))
    (h26 : s_pre.readReg64 (.gpr 26#5) = s.readReg64 (.gpr 26#5))
    (h27 : s_pre.readReg64 (.gpr 27#5) = s.readReg64 (.gpr 27#5))
    (h28 : s_pre.readReg64 (.gpr 28#5) = s.readReg64 (.gpr 28#5))
    (hv : calleeSavedVRegs s_pre = calleeSavedVRegs s) :
    HighCalleeSaved s0 sf :=
  (h0.of_steps h25 h26 h27 h28 hv).of_calleeSaved hcs

theorem spAligned_of_sp_eq {s sf : State} (h : s.spAligned = true) (hsp : sf.sp = s.sp) :
    sf.spAligned = true := by
  simpa only [State.spAligned, hsp] using h

structure FrozenEq {α : Type _} (a b : α) : Prop where
  eq : a = b

theorem sepWPp_weaken_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : P ⊢ P') (hwp : SepWPp prog ret s P' Q Qp oom) :
    SepWPp prog ret s P Q Qp oom :=
  fun R hm hL => hwp R (Satisfies.mono (sepConj_mono_left h) hm) hL

theorem sepWPp_exists_left {α : Type _} {prog : Program} {ret : BitVec 64} {s : State}
    {P : α → SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ a, SepWPp prog ret s (P a) Q Qp oom) :
    SepWPp prog ret s (∃∗ a, P a) Q Qp oom := by
  intro R hm hL
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨a, hm⟩
  exact h a R hm hL

theorem seq_frozen_state {img : Obj.Image} {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hfz : img.FrozenLoaded s)
    (h : SepWP prog mid s P (fun sm Pm => img.FrozenLoaded sm → SepWPp prog ret sm Pm Q Qp oom) oom) :
    SepWPp prog ret s P Q Qp oom :=
  SepWPp.seq_frozen (Φ := fun m => img.FrozenLoaded { s with mem := m })
    (fun m m' hf hkf => Obj.Image.FrozenLoaded.of_keepsFrozen
      (s := { s with mem := m }) (s' := { s with mem := m' }) hf hkf)
    hfz
    (SepWP.mono h fun sm Pm _ _ hcont hf =>
      hcont (Obj.Image.FrozenLoaded.of_keepsFrozen
        (s := { s with mem := sm.mem }) (s' := sm) hf (Memory.KeepsFrozen.refl sm.mem)))

theorem pure_true_sepConj (P : SepProp) : ⌜True⌝ ∗ P = P :=
  Entails.antisymm (Entails.pure_left fun _ => Entails.refl P)
    (Entails.pure_right trivial (Entails.refl P))

theorem pure_sepConj_pure_assoc (P Q : Prop) (R : SepProp) :
    ⌜P⌝ ∗ (⌜Q⌝ ∗ R) = ⌜P ∧ Q⌝ ∗ R := by
  rw [← sepConj_assoc, pure_sepConj_pure]

theorem ite_true_eq {α : Sort _} {p : Prop} [Decidable p] (h : p) (a b : α) :
    (if p then a else b) = a := by
  split <;> [rfl; exact absurd h ‹_›]

theorem ite_false_eq {α : Sort _} {p : Prop} [Decidable p] (h : ¬ p) (a b : α) :
    (if p then a else b) = b := by
  split <;> [exact absurd ‹_› h; rfl]

theorem vecBuf_dirEntry_expose (A : RustAlloc) (cap ptr : BitVec 64)
    (xs : List (List (BitVec 8) × List (BitVec 8))) :
    RustHeap.vecBuf A 48 8 (dirEntryAt A) cap ptr xs =
      ⌜xs.length ≤ cap.toNat ∧ cap.toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        RustHeap.arrayAt (dirEntryAt A) 48 ptr xs ∗
        (if cap = 0 then emp
         else A.live ptr (cap.toNat * 48) 8 ∗
           memRegion (ptr + BitVec.ofNat 64 (xs.length * 48)) ((cap.toNat - xs.length) * 48)) := by
  unfold RustHeap.vecBuf
  by_cases hcap : cap = 0
  · subst hcap
    by_cases hnil : xs = []
    · subst hnil
      simp only [↓reduceIte, RustHeap.arrayAt, sepConj_emp]
    · have hfalse : ¬ (xs.length ≤ (0 : BitVec 64).toNat ∧
          (0 : BitVec 64).toNat * 48 < 2 ^ 63 ∧ ptr ≠ 0) := by
        rcases List.exists_cons_of_ne_nil hnil with ⟨_, _, rfl⟩
        simp
      apply Entails.antisymm
      · exact Entails.pure_left fun h => False.elim (hfalse h)
      · exact Entails.pure_left fun h => False.elim (hfalse h)
  · simp only [hcap, ↓reduceIte]
    ac_rfl

theorem vecU8_eq_exists (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs = ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs := rfl

theorem sepWPp_unfold_vecU8 {prog : Program} {ret : BitVec 64} {s : State}
    {A : RustAlloc} {v : BitVec 64} {bs : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : ∀ cap ptr : BitVec 64,
      bs.length ≤ cap.toNat → cap.toNat < 2 ^ 63 → ptr ≠ 0 →
      SepWPp prog ret s
        (((v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗
             memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ∗ F)
        Q Qp oom) :
    SepWPp prog ret s (vecU8 A v bs ∗ F) Q Qp oom := by
  rw [vecU8_eq_exists]
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_left fun cap => sepWPp_exists_left fun ptr => ?_
  rw [vecU8At_expose, sepConj_assoc]
  exact SepWPp.pure_left fun ⟨h1, h2, h3⟩ => h cap ptr h1 h2 h3

theorem sepWPp_pure_mid2 {prog : Program} {ret : BitVec 64} {s : State}
    {P1 P2 P3 : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : φ → SepWPp prog ret s (P1 ∗ P2 ∗ P3) Q Qp oom) :
    SepWPp prog ret s (P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3) Q Qp oom := by
  have heq : P1 ∗ P2 ∗ ⌜φ⌝ ∗ P3 = ⌜φ⌝ ∗ P1 ∗ P2 ∗ P3 := by ac_rfl
  rw [heq]
  exact SepWPp.pure_left h

theorem arrayAt_dirEntry_cons (A : RustAlloc) (ptr : BitVec 64)
    (nm bs : List (BitVec 8)) (rest : List (List (BitVec 8) × List (BitVec 8))) :
    RustHeap.arrayAt (dirEntryAt A) 48 ptr ((nm, bs) :: rest) =
      vecU8 A ptr nm ∗ vecU8 A (ptr + 24#64) bs ∗
        RustHeap.arrayAt (dirEntryAt A) 48 (ptr + 48#64) rest := by
  dsimp only [RustHeap.arrayAt, dirEntryAt]
  ac_rfl

/-- Normal return postcondition matching `subroutine_ok_of_sepWPp` for `dirGetSpec`. -/
def dirGetPostQ (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) (x : DirGetGhost) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (dirGetSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

/-- Panic postcondition matching `subroutine_ok_of_sepWPp` for `dirGetSpec`. -/
def dirGetPanicQp (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (A : RustAlloc)
    (img : Obj.Image) (stk : Nat) (x : DirGetGhost) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (dirGetSpec rd pathOk A img stk).onPanic x s0 sf ∗ R)

theorem dirGetPanicQp_false {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {Fr R F' : SepProp} :
    dirGetPanicQp rd pathOk A img stk x s0 Fr R sf (⌜False⌝ ∗ F') := by
  intro hm
  exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hm))

theorem dirGetPanicQp_of_ok {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {Fr_any R P_f : SepProp}
    (haf : allocFailedIn s0 sf) (hpfx : s0.trace <+: sf.trace) :
    dirGetPanicQp rd pathOk A img stk x s0 (Fr_any ∗ R) R sf P_f := by
  intro hm
  rw [← sepConj_assoc] at hm
  exact Satisfies.mono
    (sepConj_mono_left (Entails.pure_right ⟨haf, hpfx⟩ (entails_anyHeap (P_f ∗ Fr_any)))) hm

/-- Lifts `readFileSpec.onPanic` at a call state preserving the entry trace into `dirGetPanicQp`. -/
theorem dirGetPanicQp_of_readPanic {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat} {x : DirGetGhost} {s0 sc sf : State}
    {Fr_any R F' : SepProp} (htr : sc.trace = s0.trace) :
    dirGetPanicQp rd pathOk A img stk x s0 (Fr_any ∗ R) R sf
      ((⌜allocFailedIn sc sf ∧ sc.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F') := by
  intro hm
  have hm' := hm
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hm'
  obtain ⟨⟨haf, hpfx⟩, -⟩ := hm'
  unfold allocFailedIn at haf
  rw [htr] at haf hpfx
  exact dirGetPanicQp_of_ok haf hpfx hm

theorem allocFailed_after_append {s0 s_pre sf : State}
    (hpfx : s0.trace <+: s_pre.trace)
    (htr : sf.trace = s_pre.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases hpfx with ⟨evs0, hevs0⟩
  refine ⟨?_, ⟨evs0 ++ [allocFailedEvent], by rw [htr, ← hevs0, List.append_assoc]⟩⟩
  unfold allocFailedIn
  rw [htr, ← hevs0, List.append_assoc]
  simp

theorem dirGetPanicQp_of_panicked {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat} {x : DirGetGhost}
    {s0 s_pre sf2 s_call : State} {Fr_any R P_f : SepProp}
    (hpfx : s0.trace <+: s_pre.trace)
    (htr2 : sf2.trace = s_pre.trace ++ [allocFailedEvent])
    (hcall : s_call.trace = sf2.trace) :
    dirGetPanicQp rd pathOk A img stk x s0 (Fr_any ∗ R) R (Rust.panicked s_call) P_f := by
  have hpan : (Rust.panicked s_call).trace = s_pre.trace ++ [allocFailedEvent] := by
    simpa only [Rust.panicked, hcall] using htr2
  have h := allocFailed_after_append hpfx hpan
  exact dirGetPanicQp_of_ok h.1 h.2

theorem dirGetPostQ_of_ret {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {cstk stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {r : Except Unit (List (BitVec 8))} {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    dirGetPostQ rd pathOk A img stk x s0
      (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R sf
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗ A.pool) ∗ Extra) := by
  refine ⟨fun hm => ?_, hsp, hcs⟩
  have hex : getResultAt A x.ret r ⊢
      ∃∗ r' : Except Unit (List (BitVec 8)),
        ⌜r' = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace⌝ ∗
          getResultAt A x.ret r' :=
    Entails.trans (Entails.pure_right hres (Entails.refl _))
      (Entails.sepExists_intro
        (P := fun r' =>
          ⌜r' = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace⌝ ∗
            getResultAt A x.ret r') r)
  have hperm :
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗ A.pool) ∗ Extra) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) =
      (getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗
          stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112) ∗ A.pool) ∗
      (Extra ∗ R) := by ac_rfl
  rw [hperm] at hm
  have hm1 := Satisfies.drop_mid hm
  have hjoin := stackAt_dirGet_join s0.sp hstk hfull
  exact Satisfies.mono
    (sepConj_mono_left (sepConj_mono hex
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hjoin))))) hm1

ls_attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
ls_attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Shared 6-instruction epilogue at `+284..+304` (`LDP`×4, `ADD SP, SP, #112`, `RET`). -/
theorem step_epilogue_284
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 284 24
  clear hfn
  revert hpc
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  intro hpc
  examples_hide_fetches
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hperm_f :
      (memRegion (s0.sp - 112#64) 112 ∗ getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ A.pool ∗ Extra) =
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗ A.pool) ∗ Extra) := by
    ac_rfl
  rw [hperm_f]
  refine dirGetPostQ_of_ret hstk hfull ?_ (by simp only [wp_norm, arm64_norm]) ?_
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2]⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs.2.2.2.2⟩

/-- Deallocate non-empty `path` buffer and run epilogue at `+464..+496`. -/
theorem step_dealloc_epilogue_464
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr pathLenW : BitVec 64} {Extra R : SepProp}
    (hC : AllocContractsX img A ext)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 464#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx1 : s.readReg64 .x1 = pathCap)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hcap_ne : pathCap ≠ 0#64) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗
        A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗ A.pool) ∗ Extra)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hdealloc := hC.dealloc_ok_at dirGetName
    (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_dealloc")
    (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
  have hfn : libsignalSessionCode.fnOff dirGetName =
      ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
  code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 464 36
  dsimp only [tripleRatchetProgAtExt] at hdealloc
  clear hfn hC
  revert hpc
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, subroutine_ok]
  intro hpc
  examples_hide_fetches
  have hcap_pos : 0 < pathCap.toNat := by
    by_contra h0
    have hz : pathCap.toNat = 0 := by omega
    exact hcap_ne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have hlay : LayoutOk pathCap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  refine seq_frozen_state
    (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_dealloc"))
    hfz ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hfz1
  refine SepWPp.call_inImage_frame (x := (pathPtr, pathCap.toNat, 1))
    (T := A.pool ∗ A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
      stackAt (s0.sp - 112#64) extHookStack)
    hdealloc hfz1 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs) (by simp only [rustDeallocExternSpecWithStack, wp_norm, hsp]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm],
                hlay⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQp_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 _ _ => ?_)
  simp only [rustDeallocExternSpecWithStack, wp_norm, hsp, sepConj_assoc]
  refine SepWPp.pure_left fun htr1 => ?_
  have hhcs1 : HighCalleeSaved s0 sf1 :=
    hhcs.of_step_call hcs1
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [wp_norm, arm64_norm])
      (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
  have hsp1_eq : sf1.sp = s0.sp - 112#64 := by
    rw [hsp1]; simp only [wp_norm, arm64_norm, *]
  have htr1_s : sf1.trace = s.trace := by
    rw [htr1]
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ pathLenW) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  unfold savedRegsAt
  apply SepWPp.of_sepWP_ret
  wp_steps
  apply SepWP.fold hp24 (by sep_frame)
  apply SepWP.fold hcstk_join (by sep_frame)
  apply SepWP.fold (frame_0x70_join (s0.sp - 112#64) s0) (by unfold savedRegsAt; sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  have hperm_f :
      (memRegion (s0.sp - 112#64) 112 ∗ stackAt (s0.sp - 112#64) cstk ∗
        A.pool ∗ getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ Extra) =
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗ memRegion (s0.sp - 112#64) 112 ∗ A.pool) ∗ Extra) := by
    ac_rfl
  rw [hperm_f]
  refine dirGetPostQ_of_ret hstk hfull ?_ (by simp only [wp_norm, arm64_norm]) ?_
  · exact ⟨hres.1, by simp only [wp_norm, arm64_norm, htr1_s, hres.2]⟩
  · exact ⟨by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simp only [wp_norm, arm64_norm],
           by simpa only [wp_norm, arm64_norm] using hhcs1.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.1,
           by simpa only [wp_norm, arm64_norm] using hhcs1.2.2.2.1,
           by simp only [wp_norm, arm64_norm],
           by simpa only [calleeSavedVRegs, wp_norm, arm64_norm] using hhcs1.2.2.2.2⟩

/-- Cache-hit exit from `+112` without read-only `memcpy` (`bs` is heap-owned): clones `bs` into
    `x.ret`, restores `dirAt`, and returns via `+284` (or panics at `+520` on OOM). -/
theorem step_hit_exit_noRO
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {bs : List (BitVec 8)} {Extra R : SepProp}
    (hC : AllocContractsX img A ext)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hchanged : x.dir.changed = pre ++ ((x.name, bs) :: rest))
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 112#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx23 : s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        RustHeap.arrayAt (dirEntryAt A) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hget : x.dir.get rd s0.fs.files x.name = .ok bs := by
    cases hdir : x.dir with | mk p ch =>
    simp only [hdir] at hchanged ⊢
    rw [hchanged, dirGhost_get_append_of_ne pre ((x.name, bs) :: rest) p rd s0.fs.files x.name hne,
        dirGhost_get_cons_eq]
  have hrepack_dir :
      (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        RustHeap.arrayAt (dirEntryAt A) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
        strRefAt (x.self + 24#64) x.dir.path ⊢
      dirAt A x.self x.dir := by
    have hentry_eq :
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest =
        RustHeap.arrayAt (dirEntryAt A) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
          ((x.name, bs) :: rest) := by
      dsimp only [RustHeap.arrayAt, dirEntryAt]
      ac_rfl
    have happ_eq :
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          RustHeap.arrayAt (dirEntryAt A) 48 (changedPtr + BitVec.ofNat 64 (48 * pre.length))
            ((x.name, bs) :: rest) =
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr x.dir.changed := by
      rw [hchanged, arrayAt_dirEntry_append]
    have hlhs_eq :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) =
        vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr x.dir.changed ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48)) := by
      rw [← happ_eq, ← hentry_eq]; ac_rfl
    unfold dirAt RustHeap.vecOf RustHeap.vecAt
    refine sepConj_mono ?_ (Entails.refl _)
    refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
    refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
    rw [vecBuf_dirEntry_expose, hlhs_eq]
    exact sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _))
  refine SepWPp.perm
    (P' := vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        RustHeap.arrayAt (dirEntryAt A) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra))
    ?_ (by sep_frame)
  refine sepWPp_unfold_vecU8 fun valCap valPtr hbs_le hvcap_lt hvptr_ne => ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hbs_lt63 : bs.length < 2 ^ 63 := by omega
  have hbs_lt64 : bs.length < 2 ^ 64 := by omega
  have hv24_32 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 8#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  have hv24_40 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) + 16#64 =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by bv_omega
  have hx23_sub8 : (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-8#64) =
      changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64 := by bv_omega
  rw [hv24_32, hv24_40]
  have hrepack_val :
      ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) ↦₆₄ valCap) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 32#64) ↦₆₄ valPtr) ∗
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (valPtr ↦ₛ bs) ∗
        (if valCap = 0 then emp
         else A.live valPtr valCap.toNat 1 ∗
           memRegion (valPtr + BitVec.ofNat 64 bs.length) (valCap.toNat - bs.length)) ⊢
      vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro valCap)
    refine Entails.trans ?_ (Entails.sepExists_intro valPtr)
    rw [vecU8At_expose, hv24_32, hv24_40]
    exact Entails.pure_right ⟨hbs_le, hvcap_lt, hvptr_ne⟩ (Entails.refl _)
  have hbs_cases : bs = [] ∨ 0 < bs.length := by cases bs <;> simp
  rcases hbs_cases with rfl | hbs_pos
  · -- Empty cached value (`bs = []`)
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 112 8
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 268 16
    clear hfn hC
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state (mid := fnStart + 284#64) hfz ?_
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at *
    wp_steps
    have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
    have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
    have hvec0 :
        ((x.ret + 8#64) ↦₆₄ 0#64) ∗ ((x.ret + 16#64) ↦₆₄ 1#64) ∗ ((x.ret + 24#64) ↦₆₄ 0#64) ⊢
        vecU8 A (x.ret + 8#64) [] := by
      have h0 := vecU8_of_zero A (x.ret + 8#64)
      rwa [hret8, hret16] at h0
    apply SepWP.fold hvec0 (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 []) (by sep_frame)
    apply SepWP.fold hrepack_val (by sep_frame)
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _
    rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
    refine SepWPp.perm
      (step_epilogue_284 hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hget.symm, by simp only [wp_norm, arm64_norm, *]⟩)
      (by sep_frame)
  · -- Non-empty cached value (`0 < bs.length`)
    have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      ofNat_beq_zero_false hbs_pos hbs_lt64
    have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt64]
    have hlay : LayoutOk bs.length 1 := ⟨hbs_pos, ⟨0, rfl⟩, by omega⟩
    have hshim := hC.shim_ok_at dirGetName
      (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
    have halloc := hC.alloc_ok_at dirGetName
      (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc")
      (hk := by rw [dirGet_fnOff]; simp only [arm64_norm])
    have hmc := sessionMemcpyBytesAtInImage_ok_at_false hC
    have hpanic := panic_at_handle_error_dirGet img.base ext
    have hfn : libsignalSessionCode.fnOff dirGetName =
        ls_off% "<libsignal_cli::stores::Dir>::get" := dirGet_fnOff
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 112 52
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 272 12
    code_fetches_range CryptoVerification.libsignalSessionCode dirGetBin img.base
      (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_cli::stores::Dir>::get")) 512 12
    dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc
    clear hfn hC
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    generalize hentry_raw :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName = fnStart at *
    generalize hprog_raw :
      libsignalSessionCode.rebase img.base (Rust.withPanics ext) = prog at *
    have he : FrozenEq (prog.fnAddr dirGetName) fnStart := ⟨hentry_raw⟩
    have hp : FrozenEq (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) prog := ⟨hprog_raw⟩
    clear hentry_raw hprog_raw
    examples_hide_fetches
    refine seq_frozen_state
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      hfz ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz1
    refine SepWPp.call_inImage_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      hshim hfz1 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withStack, sessionShimSpec, emp_sepConj, pure_true_sepConj, wp_norm, hsp])
      trivial (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQp_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hfz2 hsym2 => ?_)
    simp only [withStack, sessionShimSpec, wp_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun htr1 => ?_
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm, *] at this; exact this
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have hx22_1 : sf1.readReg64 .x22 = valPtr := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    refine seq_frozen_state
      (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "__rustc::__rust_alloc"))
      hfz2 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hfz3
    refine SepWPp.call_inImage_frame (x := (bs.length, 1))
      (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
      halloc hfz3 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs) (by simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]; rfl)
      (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQp_false)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hfz4 hsym4 => ?_)
    simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]
    have hhcs2 : HighCalleeSaved s0 sf2 :=
      hhcs1.of_step_call hcs2
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp2_al : sf2.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp1_al) hsp2
    have hsp2_eq : sf2.sp = s0.sp - 112#64 := by rw [hsp2]; simp only [wp_norm, arm64_norm, *]
    have hx19_2 : sf2.readReg64 .x19 = x.ret := by
      have := hcs2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_1
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = valPtr := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
    · -- Allocation failure
      have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
      rw [ite_true_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun htr2 => ?_
      have htr2_eq : sf2.trace = s0.trace ++ [allocFailedEvent] := by
        simpa only [wp_norm, arm64_norm, htr1_s0] using htr2
      apply SepWPp.of_sepWP
        (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "alloc::raw_vec::handle_error"))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact dirGetPanicQp_of_panicked List.prefix_rfl htr2_eq (by simp only [wp_norm, arm64_norm])
    · -- Allocation success
      set buf := sf2.readReg64 (Reg.gpr 0#5)
      have hoom_ne : buf ≠ 0#64 := hoom
      have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
      rw [ite_false_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun ⟨_, htr2⟩ => ?_
      have htr2_s0 : sf2.trace = s0.trace := by rw [htr2]; simp only [wp_norm, arm64_norm, *]
      refine seq_frozen_state
        (mid := fnStart + bv% (ls_rel% "<libsignal_cli::stores::Dir>::get" "memcpy"))
        hfz4 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hfz5
      refine SepWPp.call_inImage_frame (x := (buf, valPtr, bs))
        (T := memRegion buf bs.length ∗ (valPtr ↦ₛ bs) ∗
          stackAt (s0.sp - 112#64) extHookStack)
        hmc hfz5 (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp2_al)
        (by wp_norm_lhs)
        (by simp only [withStack, sessionMemcpyBytesAtSpec, SpqrV1.ChainProofs.bytesAt_false,
              sepConj_assoc, wp_norm, hsp2_eq]; rfl)
        (by refine ⟨rfl,
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by omega⟩)
        (by sep_frame)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ => dirGetPanicQp_false)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 hfz6 _ => ?_)
      simp only [withStack, sessionMemcpyBytesAtSpec, SpqrV1.ChainProofs.bytesAt_false,
        wp_norm, hsp2_eq, sepConj_assoc]
      refine SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
      have hhcs3 : HighCalleeSaved s0 sf3 :=
        hhcs2.of_step_call hcs3
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
      have hx19_3 : sf3.readReg64 .x19 = x.ret := by
        have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
      have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 bs.length := by
        have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
      have hx21_3 : sf3.readReg64 .x21 = buf := by
        have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
      have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
      have hcstk_join :
          memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
            stackAt (s0.sp - 112#64) extHookStack ⊢
          stackAt (s0.sp - 112#64) cstk := by
        rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
        exact Entails.refl _
      refine seq_frozen_state
        (mid := fnStart + 284#64)
        hfz6 ?_
      wp_steps
      have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by bv_omega
      have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by bv_omega
      have hvec_pos :
          ((x.ret + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            ((x.ret + 16#64) ↦₆₄ buf) ∗
            ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
            A.live buf bs.length 1 ∗ (buf ↦ₛ bs) ⊢
          vecU8 A (x.ret + 8#64) bs := by
        have hp := vecU8_of_pos A (x.ret + 8#64) buf bs hbs_pos hbs_lt63 hoom
        rwa [hret8, hret16] at hp
      apply SepWP.fold hvec_pos (by sep_frame)
      apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 bs) (by sep_frame)
      apply SepWP.fold hrepack_val (by sep_frame)
      apply SepWP.fold hrepack_dir (by sep_frame)
      apply SepWP.fold hcstk_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _
      rcases he with ⟨rfl⟩; rcases hp with ⟨rfl⟩
      refine SepWPp.perm
        (step_epilogue_284 hstk hfull hsp0_al
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs3.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
          ⟨hget.symm, by simp only [wp_norm, arm64_norm, *]⟩)
        (by sep_frame)

/-- Cache-hit exit from `+112`: clones `bs` into `x.ret`, restores `dirAt`, and returns via `+284`
    (or panics at `+520` on OOM). -/
theorem step_hit_exit
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {bs : List (BitVec 8)} {Extra R : SepProp}
    (hC : AllocContractsX img A ext)
    (_hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hchanged : x.dir.changed = pre ++ ((x.name, bs) :: rest))
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hfz : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr dirGetName + 112#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx23 : s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) :
    SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
      (s0.readReg64 .lr) s
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) x.name ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) bs ∗
        RustHeap.arrayAt (dirEntryAt A) 48
          (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) rest ∗
        (if changedCap = 0 then emp
         else A.live changedPtr (changedCap.toNat * 48) 8 ∗
           memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
             ((changedCap.toNat - x.dir.changed.length) * 48)) ∗
        strRefAt (x.self + 24#64) x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
      (dirGetPostQ rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQp rd pathOk A img stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) :=
  step_hit_exit_noRO hC hcstk hstk hfull hsp0_al hchanged hne hcap_ok hfz hsym hpc hrun
    hsp_al hsp hhcs htr hx19 hx23

end CryptoVerification.SignalSession.Cli.Get.Helpers
