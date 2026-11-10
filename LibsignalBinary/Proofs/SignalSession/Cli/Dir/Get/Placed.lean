/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Dir.Get.Pure
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.ShimCommonPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.CliSessionCodeSymD
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import all Init.Data.String.Defs

/-!
# Relocatable `[LibsignalPlacement]` Proof of `<signal_session::stores::Dir>::get` (Block `589`)

Consolidates `Dir/Get/{RoData,Decode,Loop,LoopAdv,Hit,MissEmpty,MissAfterRead,MissTail,Proof,Top}`
onto `[LibsignalPlacement]`, proving `dirGetSpecPlaced rd pathOk A stk` from `SpecsPlaced.lean`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SignalSession.Cli.Get.PlacedHelpers

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon
open CryptoVerification.SignalSession.Cli.Get.Helpers
open CryptoVerification.SpqrV1.Alloc

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

@[local arm64_norm, local wp_norm]
private theorem spAligned_writeVReg128_local (s : State) (v : BitVec 5) (val : BitVec 128) :
    (s.writeVReg128 v val).spAligned = s.spAligned := rfl

/-! ## 1. `.rodata` Bundle & `LibsignalCodeRoLoaded` Witness for Block `589` -/

abbrev dgUnreadableSym : String := "libsignal_cli:.rodata..Lanon.65"
abbrev dgReadOpSym : String := "libsignal_cli:.rodata.cst4+0xc"

abbrev dgUnreadableAddr [LibsignalPlacement] : BitVec 64 := lsρ dgUnreadableSym
abbrev dgReadOpAddr [LibsignalPlacement] : BitVec 64 := lsρ dgReadOpSym

def dirGetRoBundlePlaced [LibsignalPlacement] (w0 w1 wTail : BitVec 64) : SepProp :=
  (dgUnreadableAddr ↦₆₄ᵣ w0) ∗
  ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
  ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail) ∗
  (dgReadOpAddr ↦ᵣ utf8 "read")

theorem dirGetRoData_of_lscro [LibsignalPlacement] {s : State} {P : SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem) (hP : s.mem ⊨ P) :
    ∃ w0 w1 wTail : BitVec 64,
      s.mem ⊨ P ∗ dirGetRoBundlePlaced w0 w1 wTail := by
  let bs22 : List (BitVec 8) := utf8 "file could not be read"
  let bs0 : List (BitVec 8) := bs22.take 8
  let bs8 : List (BitVec 8) := (bs22.drop 8).take 8
  let bs16 : List (BitVec 8) := bs22.drop 16
  let bsPre14 : List (BitVec 8) := bs22.take 14
  let bs14 : List (BitVec 8) := bs22.drop 14
  have hlen0 : bs0.length = 8 := by decide +kernel
  have hlen8 : bs8.length = 8 := by decide +kernel
  have hlenPre14 : bsPre14.length = 14 := by decide +kernel
  have hlen14 : bs14.length = 8 := by decide +kernel
  have hsplit8 : bs22 = bs0 ++ (bs8 ++ bs16) := by decide +kernel
  have hsplit14 : bs22 = bsPre14 ++ bs14 := by decide +kernel
  have hchk22 : lsroCheck dgUnreadableSym bs22 = true := by decide +kernel
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 hlen0
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 hlen8
  obtain ⟨wTail, hwt⟩ := exists_unpack64_of_length_8 hlen14
  have hp14 : (dgUnreadableAddr ↦ᵣ bs22) =
      (dgUnreadableAddr ↦ᵣ bsPre14) ∗ ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail) := by
    rw [hsplit14, pointsToBytesRO_append, hlenPre14, hwt, ← pointsTo64RO_eq_pointsToBytesRO]
  have hp8 : (dgUnreadableAddr ↦ᵣ bs22) =
      (dgUnreadableAddr ↦₆₄ᵣ w0) ∗ ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
        ((dgUnreadableAddr + 16#64) ↦ᵣ bs16) := by
    rw [hsplit8, pointsToBytesRO_append, hlen0, pointsToBytesRO_append, hlen8,
        hw0, hw1, ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO]
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have s1 := lsro_intro_chk hcrl.2 (sym := dgReadOpSym) (bs := utf8 "read") (by decide +kernel) hP
  have s2 := lsro_intro_chk hcrl.2 (sym := dgUnreadableSym) (bs := bs22) hchk22 s1
  change s.mem ⊨ (dgUnreadableAddr ↦ᵣ bs22) ∗ ((dgReadOpAddr ↦ᵣ utf8 "read") ∗ P) at s2
  rw [hp8] at s2
  have s3 := lsro_intro_chk hcrl.2 (sym := dgUnreadableSym) (bs := bs22) hchk22 s2
  change s.mem ⊨ (dgUnreadableAddr ↦ᵣ bs22) ∗
    (((dgUnreadableAddr ↦₆₄ᵣ w0) ∗ ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
      ((dgUnreadableAddr + 16#64) ↦ᵣ bs16)) ∗ ((dgReadOpAddr ↦ᵣ utf8 "read") ∗ P)) at s3
  rw [hp14] at s3
  refine ⟨w0, w1, wTail, ?_⟩
  have s4 : s.mem ⊨ (P ∗ dirGetRoBundlePlaced w0 w1 wTail) ∗
      (((dgUnreadableAddr ↦ᵣ bsPre14) ∗ ((dgUnreadableAddr + 16#64) ↦ᵣ bs16)) ∗ emp) := by
    unfold dirGetRoBundlePlaced
    exact Satisfies.mono (Entails.of_eq (by ac_rfl)) s3
  have s5 := Satisfies.drop_mid s4
  simpa only [sepConj_emp] using s5

/-! ## 2. Frame & `SepWPp` Combinators on Block `589` -/

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

theorem seq_lscro_state [LibsignalPlacement] {prog : Program} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp oom)
      oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  rcases h.elim hm hL with ⟨sm, hsteps, ⟨-, -, Pm, hmm, hcont⟩ | hoom⟩
  · exact (by
      obtain ⟨sf, hsteps', hout⟩ :=
        hcont (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
      exact ⟨sf, hsteps.trans hsteps', hout⟩)
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

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

theorem subroutine_ok_lscro_withFsInv [LibsignalPlacement] {α : Type} {P : Program} {e : BitVec 64}
    {spec : Spec α}
    (hP : TraceFsSound P) (h : subroutine_ok P e (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (F0 : FsFiles) (T0 : List TraceEvent) :
    subroutine_ok P e (StoreKit.withLsCodeRoLoaded lsmpl (withFsInv spec F0 T0)) := by
  have hfs := subroutine_ok_withFsInv hP h F0 T0
  intro x R s0 hpc hrun hpre hal hcode
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [withFsInv] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  have hpre' : s0.mem ⊨ (withFsInv (StoreKit.withLsCodeRoLoaded lsmpl spec) F0 T0).pre x s0 ∗ R := by
    dsimp only [withFsInv]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre0.1, satisfies_lscro_pre hcrl0 hpre0.2⟩
  exact hfs x R s0 hpc hrun hpre' hal hcode

theorem call_lscro_frame [LibsignalPlacement] {α : Type}
    {prog : Program} {callee ret_pc ret : BitVec 64} {spec : Spec α}
    {x : α} {s : State} {φ : Prop} {P T F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog callee (StoreKit.withLsCodeRoLoaded lsmpl spec))
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = callee)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hpre_eq : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ)
    (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpan : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = ret_pc →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → (sf.mem ⊨ (fun _ => ⌜False⌝) sf ∗ R') := by
      wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.call_lscro (x := x) (F := F) hcall hcrl hpc hrun hsp_al hlr
    (fun R hm => by
      rw [hpre_eq, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hφ, by rwa [← sepConj_assoc, ← hP]⟩)
    hexit hpan hnext
    (fun R' sf ho h => hoom sf R' ho h)

abbrev lsHandleErrorSymCli : String :=
  "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error"

theorem panic_at_handle_error_589 [LibsignalPlacement] {H : LibsignalHooks}
    (hpan : CliPanicHooksPlaced H) :
    (lsProg_589 H).externAt? (lsρ lsHandleErrorSymCli) = some Rust.panicked :=
  ls_panicAt_of_cliPanic hpan (sym := lsHandleErrorSymCli)

theorem bcmp_lscro_ok_at_589 [LibsignalPlacement] {H : LibsignalHooks}
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec) :
    subroutine_ok (lsProg_589 H) (lsρ cliBcmpName)
      (StoreKit.withLsCodeRoLoaded lsmpl cliBcmpSpec) :=
  StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain
    (ls_hook_ok_ultra_of_mem hBcmp (by decide))

theorem memcpy_bytesAt_lscro_ok_at_589 [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hC : AllocContractsXCliPlaced A H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (ro : Bool) :
    subroutine_ok (lsProg_589 H) (lsρ memcpyName)
      (StoreKit.withLsCodeRoLoaded lsmpl
        (withStack (SpqrV1.Alloc.sessionMemcpyBytesAtSpec ro) extHookStack)) := by
  cases ro
  · have hmc := session_memcpy_region_lscro_of_cli (callerProg := lsProg_589 H)
      (stk := extHookStack) hC
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        (StoreKit.withLsCodeRoLoaded lsmpl (withStack sessionMemcpyRegionSpec extHookStack)).pre
          (dst, src, bs) s0 ∗ R := by
      apply satisfies_lscro_pre hcrl0
      simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec, SpqrV1.ChainProofs.bytesAt_false,
        sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨⟨hpre0.1.1, hpre0.1.2.1, hpre0.1.2.2.1⟩, hpre0.2⟩
    rcases hmc (dst, src, bs) R s0 hpc hrun hpre' hal hL with ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simpa only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        sessionMemcpyRegionSpec, memcpyRegionSpec,
        SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc] using hpost
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)
  · have hmc_ro : subroutine_ok (lsProg_589 H) (lsρ memcpyName)
        SpqrV1.Alloc.sessionMemcpyRegionROSpec :=
      ls_hook_ok_ultra_of_mem hRO (by decide)
    intro ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal hL
    obtain ⟨_hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
    have hpre' : s0.mem ⊨
        SpqrV1.Alloc.sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
          (stackAt s0.sp extHookStack ∗ R) := by
      simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpre0 ⊢
      exact ⟨hpre0.1, hpre0.2⟩
    rcases hmc_ro (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hal hL with
      ⟨sf, hs, hout⟩
    refine ⟨sf, hs, ?_⟩
    rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨_, _, hpost⟩ | ⟨_, hpost⟩
    · refine Or.inl ⟨hret, hcc, ?_⟩
      simp only [StoreKit.withLsCodeRoLoaded, withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        SpqrV1.Alloc.sessionMemcpyRegionROSpec,
        SpqrV1.ChainProofs.bytesAt_true, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
      exact ⟨hpost.1, hpost.2⟩
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1
    · simp only [SpqrV1.Alloc.sessionMemcpyRegionROSpec, satisfies_pure_sepConj] at hpost
      exact False.elim hpost.1

/-! ## 3. Postcondition & Panic Helpers for `dirGetSpecPlaced` -/

def dirGetPostQPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) (x : DirGetGhost) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    ((sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (dirGetSpecPlaced rd pathOk A stk).post x s0 sf ∗ R)) ∧
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

def dirGetPanicQpPlaced [LibsignalPlacement] (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (A : RustAlloc) (stk : Nat) (x : DirGetGhost) (s0 : State)
    (Fr R : SepProp) : State → SepProp → Prop :=
  fun sf P_f =>
    (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ (dirGetSpecPlaced rd pathOk A stk).onPanic x s0 sf ∗ R)

theorem dirGetPanicQp_false [LibsignalPlacement] {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {Fr R F' : SepProp} :
    dirGetPanicQpPlaced rd pathOk A stk x s0 Fr R sf (⌜False⌝ ∗ F') := by
  intro hm
  exact False.elim (not_satisfies_false_sepConj (by simpa only [sepConj_assoc] using hm))

theorem dirGetPanicQp_of_ok [LibsignalPlacement] {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {Fr_any R P_f : SepProp}
    (haf : allocFailedIn s0 sf) (hpfx : s0.trace <+: sf.trace) :
    dirGetPanicQpPlaced rd pathOk A stk x s0 (Fr_any ∗ R) R sf P_f := by
  intro hm
  rw [← sepConj_assoc] at hm
  exact Satisfies.mono
    (sepConj_mono_left (Entails.pure_right ⟨haf, hpfx⟩ (entails_anyHeap (P_f ∗ Fr_any)))) hm

theorem dirGetPanicQp_of_readPanic [LibsignalPlacement] {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {stk : Nat} {x : DirGetGhost} {s0 sc sf : State}
    {Fr_any R F' : SepProp} (htr : sc.trace = s0.trace) :
    dirGetPanicQpPlaced rd pathOk A stk x s0 (Fr_any ∗ R) R sf
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

theorem dirGetPanicQp_of_panicked [LibsignalPlacement] {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {stk : Nat} {x : DirGetGhost}
    {s0 s_pre sf2 s_call : State} {Fr_any R P_f : SepProp}
    (hpfx : s0.trace <+: s_pre.trace)
    (htr2 : sf2.trace = s_pre.trace ++ [allocFailedEvent])
    (hcall : s_call.trace = sf2.trace) :
    dirGetPanicQpPlaced rd pathOk A stk x s0 (Fr_any ∗ R) R (Rust.panicked s_call) P_f := by
  have hpan : (Rust.panicked s_call).trace = s_pre.trace ++ [allocFailedEvent] := by
    simpa only [Rust.panicked, hcall] using htr2
  have h := allocFailed_after_append hpfx hpan
  exact dirGetPanicQp_of_ok h.1 h.2

theorem dirGetPostQ_of_ret [LibsignalPlacement] {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {cstk stk : Nat} {x : DirGetGhost} {s0 sf : State}
    {r : Except Unit (List (BitVec 8))} {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ sf.trace = s0.trace)
    (hsp : sf.sp = s0.sp) (hcs : CalleeSavedPreserved s0 sf) :
    dirGetPostQPlaced rd pathOk A stk x s0
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

/-! ## 4. Shared Epilogues (`+284` and `+464`) on Block `589` -/

theorem step_epilogue_284 [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpc : s.pc = (blkPl_589).base + 284#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((getResultAt A x.ret r ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        stackAt (s0.sp - 112#64) cstk ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
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

theorem step_dealloc_epilogue_464 [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State} {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr pathLenW : BitVec 64} {Extra R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 464#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx1 : s.readReg64 .x1 = pathCap)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hcap_ne : pathCap ≠ 0#64) (hcap_lt : pathCap.toNat < 2 ^ 63)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
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
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hdealloc := dealloc_lscro_of_cli (callerProg := lsProg_589 H) hC
  clear hC
  have hcap_pos : 0 < pathCap.toNat := by
    by_contra h0
    have hz : pathCap.toNat = 0 := by omega
    exact hcap_ne (BitVec.eq_of_toNat_eq (by simpa using hz))
  have hlay : LayoutOk pathCap.toNat 1 := ⟨hcap_pos, ⟨0, rfl⟩, by omega⟩
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  refine seq_lscro_state
    (mid := lsρ lsRustDeallocSymCli)
    hcrl ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  refine call_lscro_frame (x := (pathPtr, pathCap.toNat, 1))
    (T := A.pool ∗ A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat ∗
      stackAt (s0.sp - 112#64) extHookStack)
    hdealloc hcrl1 (by wp_norm_lhs)
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
    (fun sf1 hpc1 hrun1 hsp1 hcs1 _ => ?_)
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

/-! ## 5. Cache-Hit Exit (`+112`) on Block `589` -/

theorem step_hit_exit [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {bs : List (BitVec 8)} {Extra R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hchanged : x.dir.changed = pre ++ ((x.name, bs) :: rest))
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 112#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx23 : s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) :
    SepWPp (lsProg_589 H)
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
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
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
  · clear hC hpan hRO
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl ?_
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
  · have hne0 : (BitVec.ofNat 64 bs.length == 0#64) = false :=
      ofNat_beq_zero_false hbs_pos hbs_lt64
    have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbs_lt64]
    have hlay : LayoutOk bs.length 1 := ⟨hbs_pos, ⟨0, rfl⟩, by omega⟩
    have hshim := shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC
    have halloc := alloc_lscro_of_cli (callerProg := lsProg_589 H) hC
    have hmc := memcpy_bytesAt_lscro_ok_at_589 hC hRO false
    have hpanic := panic_at_handle_error_589 hpan
    clear hC hpan hRO
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    refine seq_lscro_state
      (mid := lsρ lsRustNoAllocShimSymCli)
      hcrl ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      hshim hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withStack, sessionShimSpec, emp_sepConj, pure_true_sepConj, wp_norm, hsp])
      trivial (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQp_false)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
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
    refine seq_lscro_state
      (mid := lsρ lsRustAllocSymCli)
      hcrl2 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine call_lscro_frame (x := (bs.length, 1))
      (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
      halloc hcrl3 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs) (by simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]; rfl)
      (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay⟩)
      (by sep_frame)
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ => dirGetPanicQp_false)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
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
    · have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
      rw [ite_true_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun htr2 => ?_
      have htr2_eq : sf2.trace = s0.trace ++ [allocFailedEvent] := by
        simpa only [wp_norm, arm64_norm, htr1_s0] using htr2
      apply SepWPp.of_sepWP
        (mid := lsρ lsHandleErrorSymCli)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact dirGetPanicQp_of_panicked List.prefix_rfl htr2_eq (by simp only [wp_norm, arm64_norm])
    · set buf := sf2.readReg64 (Reg.gpr 0#5)
      have hoom_ne : buf ≠ 0#64 := hoom
      have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
      rw [ite_false_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun ⟨_, htr2⟩ => ?_
      have htr2_s0 : sf2.trace = s0.trace := by rw [htr2]; simp only [wp_norm, arm64_norm, *]
      refine seq_lscro_state
        (mid := lsρ memcpyName)
        hcrl4 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl5
      refine call_lscro_frame (x := (buf, valPtr, bs))
        (T := memRegion buf bs.length ∗ (valPtr ↦ₛ bs) ∗
          stackAt (s0.sp - 112#64) extHookStack)
        hmc hcrl5 (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp2_al)
        (by wp_norm_lhs)
        (by simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
              SpqrV1.ChainProofs.bytesAt_false, sepConj_assoc, wp_norm, hsp2_eq]; rfl)
        (by refine ⟨rfl,
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by omega⟩)
        (by sep_frame)
        (fun _ _ _ _ he => not_satisfies_false_sepConj he)
        (fun _ _ => dirGetPanicQp_false)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 hcrl6 => ?_)
      simp only [withStack, SpqrV1.Alloc.sessionMemcpyBytesAtSpec,
        SpqrV1.ChainProofs.bytesAt_false, wp_norm, hsp2_eq, sepConj_assoc]
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
      refine seq_lscro_state
        (mid := (blkPl_589).base + 284#64)
        hcrl6 ?_
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

/-! ## 6. Loop Advance (`+68`..`+80` / `+164`) on Block `589` -/

theorem cstk_le_pow64 {cstk stk : Nat} (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64) :
    cstk ≤ 2 ^ 64 :=
  Nat.le_trans (Nat.le_add_left cstk 112) (Nat.le_trans hstk hfull)

theorem lt_pow63_of_lt_pow32 {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 63 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 63))

theorem lt_pow64_of_lt_pow32 {n : Nat} (h : n < 2 ^ 32) : n < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 32 < 64))

theorem lt_pow64_of_lt_pow63 {n : Nat} (h : n < 2 ^ 63) : n < 2 ^ 64 :=
  Nat.lt_trans h (Nat.pow_lt_pow_right (by decide : 1 < 2) (by decide : 63 < 64))

theorem ofNat64_toNat_of_lt32 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_pow64_of_lt_pow32 h)]

theorem ofNat64_toNat_of_lt63 {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_pow64_of_lt_pow63 h)]

private theorem sub48_cons_len
    {hd : List (BitVec 8) × List (BitVec 8)}
    {rest : List (List (BitVec 8) × List (BitVec 8))} :
    BitVec.ofNat 64 (48 * (hd :: rest).length) - 48#64 =
      BitVec.ofNat 64 (48 * rest.length) := by
  have hbeq : BitVec.ofNat 64 (48 * (hd :: rest).length) =
      BitVec.ofNat 64 (48 * rest.length) + 48#64 := by
    rw [List.length_cons, Nat.mul_add_one, ← BitVec.ofNat_add]
  rw [hbeq]
  bv_bits

private theorem ofNat48_beq_48_false
    {hd nxt : List (BitVec 8) × List (BitVec 8)}
    {tail : List (List (BitVec 8) × List (BitVec 8))}
    (hlt : 48 * (hd :: nxt :: tail).length < 2 ^ 63) :
    (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length) == 48#64) = false := by
  have hlt64 : 48 * (hd :: nxt :: tail).length < 2 ^ 64 := lt_pow64_of_lt_pow63 hlt
  clear hlt
  apply beq_false_of_ne
  intro h
  have ht : (BitVec.ofNat 64 (48 * (hd :: nxt :: tail).length)).toNat = (48#64).toNat :=
    congrArg BitVec.toNat h
  have h48_nat : (48#64).toNat = 48 := rfl
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64, h48_nat] at ht
  clear hlt64 h48_nat h
  simp only [List.length_cons] at ht
  omega

theorem step_loop_advance [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 sm : State}
    {changedCap changedPtr : BitVec 64}
    {pre rest : List (List (BitVec 8) × List (BitVec 8))}
    {hdName hdBytes : List (BitVec 8)}
    {Extra R : SepProp}
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hchanged : x.dir.changed = pre ++ (hdName, hdBytes) :: rest)
    (hne : ∀ e ∈ pre, e.1 ≠ x.name)
    (hhd_ne : hdName ≠ x.name)
    (hmiss : ∀ sm : State,
      sm.pc = (blkPl_589).base + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sm
        ((dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (ih : ∀ (pre' : List (List (BitVec 8) × List (BitVec 8))) (sn : State),
      rest ≠ [] →
      x.dir.changed = pre' ++ rest →
      (∀ e ∈ pre', e.1 ≠ x.name) →
      StoreKit.LibsignalCodeRoLoaded lsmpl sn.mem →
      sn.pc = (blkPl_589).base + 80#64 →
      sn.status = .Running →
      sn.spAligned = true →
      sn.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sn →
      sn.fs.files = s0.fs.files →
      sn.trace = s0.trace →
      sn.readReg64 .x19 = x.ret →
      sn.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sn.readReg64 .x21 = x.self →
      sn.readReg64 .x22 = x.nameA →
      sn.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre'.length) + 40#64 →
      sn.readReg64 .x24 = BitVec.ofNat 64 (48 * rest.length) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sn
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre' ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre'.length)) rest ∗
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
        (dirGetPostQPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R))
    (hcrl_m : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc_m : sm.pc = (blkPl_589).base + 68#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21_m : sm.readReg64 .x21 = x.self)
    (hx22_m : sm.readReg64 .x22 = x.nameA)
    (hx23_m : sm.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64)
    (hx24_m : sm.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length)) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) sm
      (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
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
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have _ := hstk; have _ := hfull
  have hsuf_lt63 : 48 * ((hdName, hdBytes) :: rest).length < 2 ^ 63 := by
    have hch_len : pre.length + ((hdName, hdBytes) :: rest).length = x.dir.changed.length := by
      rw [hchanged, List.length_append]
    have hle : ((hdName, hdBytes) :: rest).length ≤ changedCap.toNat :=
      Nat.le_trans (hch_len ▸ Nat.le_add_left _ pre.length) hcap_ok.1
    rw [Nat.mul_comm]
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hle) hcap_ok.2.1
  have hne_next : ∀ e ∈ pre ++ [(hdName, hdBytes)], e.1 ≠ x.name := by
    intro e he
    rcases List.mem_append.mp he with he1 | he2
    · exact hne e he1
    · rcases List.mem_singleton.mp he2 with rfl
      exact hhd_ne
  have hrest_cases : rest = [] ∨ ∃ nxt tail, rest = nxt :: tail := by
    cases rest with
    | nil => exact Or.inl rfl
    | cons nxt tail => exact Or.inr ⟨nxt, tail, rfl⟩
  rcases hrest_cases with hr_nil | ⟨nxt, tail, hr_cons⟩
  · clear ih
    rw [hr_nil] at hchanged hx24_m ⊢
    have hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name := by
      simpa [hchanged] using hne_next
    have hrepack_dir :
        (vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64) [] ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + BitVec.ofNat 64 (x.dir.changed.length * 48))
               ((changedCap.toNat - x.dir.changed.length) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A x.self x.dir := by
      unfold dirAt RustHeap.vecOf RustHeap.vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hcap_ok (Entails.refl _)))
      rw [hchanged, arrayAt_dirEntry_append]
      dsimp only [RustHeap.arrayAt, dirEntryAt]
      sep_frame
    refine seq_lscro_state (mid := (blkPl_589).base + 164#64) hcrl_m ?_
    simp only [List.length_singleton, Nat.mul_one] at hx24_m
    wp_steps
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m'
    refine SepWPp.perm
      (hmiss _
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        hcrl_m'
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hall_ne)
      (by sep_frame)
  · clear hmiss
    have hsuf_lt63' : 48 * ((hdName, hdBytes) :: nxt :: tail).length < 2 ^ 63 := by
      rwa [← hr_cons]
    have hsub48 :
        BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) - 48#64 =
          BitVec.ofNat 64 (48 * (nxt :: tail).length) :=
      sub48_cons_len
    have hbeq48 :
        (BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: nxt :: tail).length) == 48#64) = false :=
      ofNat48_beq_48_false hsuf_lt63'
    have hpeel :
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ⊢
        RustHeap.arrayAt (dirEntryAt A) 48 changedPtr (pre ++ [(hdName, hdBytes)]) := by
      rw [arrayAt_dirEntry_append]
      dsimp only [RustHeap.arrayAt, dirEntryAt]
      sep_frame
    have hnext_ptr :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 48#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) := by
      rw [List.length_append, List.length_singleton, Nat.mul_add_one, BitVec.add_assoc, ← BitVec.ofNat_add]
    have hx23_next :
        changedPtr + BitVec.ofNat 64 (48 * pre.length) + 88#64 =
          changedPtr + BitVec.ofNat 64 (48 * (pre ++ [(hdName, hdBytes)]).length) + 40#64 := by
      rw [← hnext_ptr]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
    refine seq_lscro_state (mid := (blkPl_589).base + 80#64) hcrl_m ?_
    wp_step
    wp_step
    wp_step
    simp only [← hr_cons]
    apply SepWP.fold hpeel (by sep_frame)
    rw [hnext_ptr]
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m'
    refine SepWPp.perm
      (ih (pre ++ [(hdName, hdBytes)]) _
        (by rw [hr_cons]; simp)
        (by rw [hchanged, List.append_assoc]; rfl)
        hne_next
        hcrl_m'
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al_m)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs_m.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]))
      (by sep_frame)

/-! ## 7. Entry-Scan Loop (`+80`..`+108`) on Block `589` -/

private theorem false_of_fsInv_false {F0 : FsFiles} {T0 : List TraceEvent} {sf : State}
    {m : Memory} {R : SepProp}
    (h : m ⊨ (⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ R) : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  exact h.2.1

private theorem panicQp_of_fsInv_false [LibsignalPlacement]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {A : RustAlloc}
    {stk : Nat} {x : DirGetGhost} {s0 sf : State} {Fr R : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent} {Frame : SepProp} :
    dirGetPanicQpPlaced rd pathOk A stk x s0 Fr R sf ((⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ Frame) :=
  fun hm => False.elim (false_of_fsInv_false (by rw [sepConj_assoc] at hm; exact hm))

private theorem w32_zext_beq_zero_false {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (((v.truncate 32).zeroExtend 64) == 0#64) = false := by
  apply beq_false_of_ne
  intro hz
  apply hne
  change (v.setWidth 32).setWidth 64 = 0#64 at hz
  bv_bits

theorem step_loop [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 : State}
    {changedCap changedPtr : BitVec 64}
    {Extra R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hFs : TraceFsSound (lsProg_589 H))
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hcap_ok : x.dir.changed.length ≤ changedCap.toNat ∧
      changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0)
    (hmiss : ∀ sm : State,
      sm.pc = (blkPl_589).base + 164#64 →
      sm.status = .Running →
      sm.spAligned = true →
      sm.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 sm →
      StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.fs.files = s0.fs.files →
      sm.trace = s0.trace →
      sm.readReg64 .x19 = x.ret →
      sm.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      sm.readReg64 .x21 = x.self →
      sm.readReg64 .x22 = x.nameA →
      (∀ e ∈ x.dir.changed, e.1 ≠ x.name) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) sm
        ((dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          memRegion x.ret 48 ∗
          stackAt (s0.sp - 112#64) cstk ∗
          memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
          savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗ Extra)
        (dirGetPostQPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)) :
    ∀ (suf pre : List (List (BitVec 8) × List (BitVec 8))) (s : State),
      suf ≠ [] →
      x.dir.changed = pre ++ suf →
      (∀ e ∈ pre, e.1 ≠ x.name) →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_589).base + 80#64 →
      s.status = .Running →
      s.spAligned = true →
      s.sp = s0.sp - 112#64 →
      HighCalleeSaved s0 s →
      s.fs.files = s0.fs.files →
      s.trace = s0.trace →
      s.readReg64 .x19 = x.ret →
      s.readReg64 .x20 = BitVec.ofNat 64 x.name.length →
      s.readReg64 .x21 = x.self →
      s.readReg64 .x22 = x.nameA →
      s.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 →
      s.readReg64 .x24 = BitVec.ofNat 64 (48 * suf.length) →
      SepWPp (lsProg_589 H)
        (s0.readReg64 .lr) s
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          RustHeap.arrayAt (dirEntryAt A) 48
            (changedPtr + BitVec.ofNat 64 (48 * pre.length)) suf ∗
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
        (dirGetPostQPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
        (dirGetPanicQpPlaced rd pathOk A stk x s0
          (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  intro suf
  induction suf with
  | nil =>
    intro _ _ hsuf
    exact False.elim (hsuf rfl)
  | cons hd rest ih =>
    rcases hd with ⟨hdName, hdBytes⟩
    intro pre s _ hchanged hne hcrl hpc hrun hsp_al hsp hhcs hfs htr
      hx19 hx20 hx21 hx22 hx23 hx24
    rw [arrayAt_dirEntry_cons]
    refine SepWPp.perm
      (P' := vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName ∗
        (((vecHeader x.self changedCap changedPtr x.dir.changed.length ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr pre ∗
          vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 24#64) hdBytes ∗
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
    refine sepWPp_unfold_vecU8 fun nmCap nmPtr hnm_le hnm_lt hnm_ne => ?_
    have hrepack_nm :
        ((changedPtr + BitVec.ofNat 64 (48 * pre.length)) ↦₆₄ nmCap) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64) ↦₆₄ nmPtr) ∗
          ((changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64) ↦₆₄
            BitVec.ofNat 64 hdName.length) ∗
          (nmPtr ↦ₛ hdName) ∗
          (if nmCap = 0 then emp
           else A.live nmPtr nmCap.toNat 1 ∗
             memRegion (nmPtr + BitVec.ofNat 64 hdName.length) (nmCap.toNat - hdName.length)) ⊢
        vecU8 A (changedPtr + BitVec.ofNat 64 (48 * pre.length)) hdName := by
      dsimp only [vecU8]
      refine Entails.trans ?_ (Entails.sepExists_intro nmCap)
      refine Entails.trans ?_ (Entails.sepExists_intro nmPtr)
      rw [vecU8At_expose]
      exact Entails.pure_right ⟨hnm_le, hnm_lt, hnm_ne⟩ (Entails.refl _)
    have hx23_sub24 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-24#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 16#64 := by
      simp only [BitVec.add_assoc]; rfl
    have hx23_sub32 :
        (changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64) + (-32#64) =
          changedPtr + BitVec.ofNat 64 (48 * pre.length) + 8#64 := by
      simp only [BitVec.add_assoc]; rfl
    by_cases hlen_eq : hdName.length = x.name.length
    · -- Equal lengths: compare via `bcmp`
      have hbcmp_fs := subroutine_ok_lscro_withFsInv hFs
        (bcmp_lscro_ok_at_589 hBcmp) s0.fs.files s0.trace
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
      have hcstk_join :
          memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
            stackAt (s0.sp - 112#64) extHookStack ⊢
          stackAt (s0.sp - 112#64) cstk := by
        rw [stackAt_sub_split (s0.sp - 112#64) hcstk (cstk_le_pow64 hstk hfull)]
        exact Entails.refl _
      refine seq_lscro_state (mid := lsρ cliBcmpName) hcrl ?_
      rw [hlen_eq]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_b
      have hx2_nat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
        ofNat64_toNat_of_lt32 hname_lt
      refine call_lscro_frame
        (x := CliBcmpCall.mk nmPtr false hdName x.nameA x.nameRo x.name)
        (T := (nmPtr ↦ₛ hdName) ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) extHookStack)
        (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false ho))
        hbcmp_fs hcrl_b (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by wp_norm_lhs)
        (by simp only [withFsInv, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt_false,
              wp_norm, hsp, pure_sepConj_pure_assoc]; rfl)
        (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *]),
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    by simp only [wp_norm, arm64_norm, *],
                    hlen_eq.symm⟩)
        (by sep_frame)
        (fun _ _ _ _ hex => false_of_fsInv_false hex)
        (fun _ _ => panicQp_of_fsInv_false)
        (fun sfb hpcb hrunb hspb hcsb hcrlb => ?_)
      simp only [withFsInv, cliBcmpSpec, SpqrV1.ChainProofs.bytesAt_false, wp_norm, hsp, sepConj_assoc]
      refine SepWPp.pure_left fun hfs_fb => SepWPp.pure_left fun ⟨hw0_iff, htrb⟩ => ?_
      have hhcsb : HighCalleeSaved s0 sfb :=
        hhcs.of_step_call hcsb
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hspb_al : sfb.spAligned = true :=
        spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hspb
      have hspb_eq : sfb.sp = s0.sp - 112#64 := by rw [hspb]; simp only [wp_norm, arm64_norm, *]
      have hx19_b : sfb.readReg64 .x19 = x.ret := by
        have := hcsb.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
      have hx20_b : sfb.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
        have := hcsb.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
      have hx21_b : sfb.readReg64 .x21 = x.self := by
        have := hcsb.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
      have hx22_b : sfb.readReg64 .x22 = x.nameA := by
        have := hcsb.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
      have hx23_b : sfb.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * pre.length) + 40#64 := by
        have := hcsb.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx23
      have hx24_b : sfb.readReg64 .x24 = BitVec.ofNat 64 (48 * ((hdName, hdBytes) :: rest).length) := by
        have := hcsb.2.2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx24
      have htrb_s0 : sfb.trace = s0.trace := by rw [htrb]; simp only [wp_norm, arm64_norm, *]
      have hfiles_b : sfb.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs_fb htrb_s0
      rw [← hlen_eq]
      by_cases hname_eq : hdName = x.name
      · -- Match (`w0 = 0`)
        have hw0_eq : (sfb.readReg64 .x0).setWidth 32 = 0#32 := hw0_iff.mpr hname_eq
        have hw0_zext : ((sfb.readReg64 .x0).truncate 32).zeroExtend 64 = 0#64 := by
          change ((sfb.readReg64 .x0).setWidth 32).zeroExtend 64 = 0#64
          rw [hw0_eq]; rfl
        have hw0_rr : sfb.readReg .W32 .x0 = 0#64 := hw0_zext
        have _ := hw0_eq; have _ := hw0_zext; have _ := hw0_rr
        subst hname_eq
        refine seq_lscro_state (mid := (blkPl_589).base + 112#64) hcrlb ?_
        wp_steps
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_hit
        refine SepWPp.perm
          (step_hit_exit (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
            (pre := pre) (rest := rest) (bs := hdBytes) (Extra := Extra)
            hC hpan hRO hcstk hstk hfull hsp0_al hchanged hne hcap_ok hcrl_hit
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by sep_frame)
      · -- Mismatch (`w0 ≠ 0`)
        have hw0_ne : ((sfb.readReg64 .x0).setWidth 32 == 0#32) = false :=
          beq_false_of_ne (fun h => hname_eq (hw0_iff.mp h))
        have hw0_zext_ne : (((sfb.readReg64 .x0).truncate 32).zeroExtend 64 == 0#64) = false :=
          w32_zext_beq_zero_false (fun h => hname_eq (hw0_iff.mp h))
        have hw0_rr_ne : (sfb.readReg .W32 .x0 == 0#64) = false := hw0_zext_ne
        have _ := hw0_ne; have _ := hw0_zext_ne; have _ := hw0_rr_ne
        refine seq_lscro_state (mid := (blkPl_589).base + 68#64) hcrlb ?_
        wp_steps
        apply SepWP.fold hrepack_nm (by sep_frame)
        apply SepWP.fold hcstk_join (by sep_frame)
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        intro hcrl_adv
        refine SepWPp.perm
          (step_loop_advance (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
            (pre := pre) (rest := rest) (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
            hstk hfull hcap_ok hchanged hne hname_eq hmiss ih
            hcrl_adv
            (by wp_norm_lhs)
            (by simp only [wp_norm, arm64_norm, *])
            (by simpa only [wp_norm, arm64_norm] using hspb_al)
            (by simp only [wp_norm, arm64_norm, *])
            (hhcsb.of_steps
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [wp_norm, arm64_norm])
              (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *])
            (by simp only [wp_norm, arm64_norm, *]))
          (by sep_frame)
    · -- Distinct lengths
      have hbv_ne : BitVec.ofNat 64 hdName.length ≠ BitVec.ofNat 64 x.name.length := by
        intro heq_bv
        have hnat := congrArg BitVec.toNat heq_bv
        rw [ofNat64_toNat_of_lt63 (Nat.lt_of_le_of_lt hnm_le hnm_lt),
            ofNat64_toNat_of_lt32 hname_lt] at hnat
        exact hlen_eq hnat
      have hbne_len : (BitVec.ofNat 64 hdName.length != BitVec.ofNat 64 x.name.length) = true :=
        bne_iff_ne.mpr hbv_ne
      have hbeq_len : (BitVec.ofNat 64 hdName.length == BitVec.ofNat 64 x.name.length) = false :=
        beq_false_of_ne hbv_ne
      have _ := hbv_ne; have _ := hbne_len; have _ := hbeq_len
      have hname_ne : hdName ≠ x.name := fun heq => hlen_eq (congrArg List.length heq)
      refine seq_lscro_state (mid := (blkPl_589).base + 68#64) hcrl ?_
      wp_steps
      apply SepWP.fold hrepack_nm (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl_adv
      refine SepWPp.perm
        (step_loop_advance (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
          (pre := pre) (rest := rest) (hdName := hdName) (hdBytes := hdBytes) (Extra := Extra)
          hstk hfull hcap_ok hchanged hne hname_ne hmiss ih
          hcrl_adv
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by sep_frame)

/-! ## 8. Post-I/O Result Construction (`+336`..`+508`) on Block `589` -/

theorem step_after_read_ok [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {outBs : List (BitVec 8)}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : Except.ok outBs = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((((ioVecAt A (s0.sp - 112#64) (.ok outBs) ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  refine sepWPp_unfold_vecU8 fun outCap outPtr hout_le hout_cap_lt hout_ptr_ne => ?_
  have hcmn : (outCap + 1#64 == 0#64) = false := cap_cmn1_beq_zero_false hout_cap_lt
  have hret8 : (x.ret + 8#64) + 8#64 = x.ret + 16#64 := by simp only [BitVec.add_assoc]; rfl
  have hret16 : (x.ret + 8#64) + 16#64 = x.ret + 24#64 := by simp only [BitVec.add_assoc]; rfl
  have hrepack_out :
      ((x.ret + 8#64) ↦₆₄ outCap) ∗
        ((x.ret + 16#64) ↦₆₄ outPtr) ∗
        ((x.ret + 24#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ∗
        (outPtr ↦ₛ outBs) ∗
        (if outCap = 0 then emp
         else A.live outPtr outCap.toNat 1 ∗
           memRegion (outPtr + BitVec.ofNat 64 outBs.length) (outCap.toNat - outBs.length)) ⊢
      vecU8 A (x.ret + 8#64) outBs := by
    dsimp only [vecU8]
    refine Entails.trans ?_ (Entails.sepExists_intro outCap)
    refine Entails.trans ?_ (Entails.sepExists_intro outPtr)
    rw [vecU8At_expose, hret8, hret16]
    exact Entails.pure_right ⟨hout_le, hout_cap_lt, hout_ptr_ne⟩ (Entails.refl _)
  have hsp0_24 :
      ((s0.sp - 112#64) ↦₆₄ outCap) ∗
        ((s0.sp - 112#64 + 8#64) ↦₆₄ outPtr) ∗
        ((s0.sp - 112#64 + 16#64) ↦₆₄ BitVec.ofNat 64 outBs.length) ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  by_cases hpcap : pathCap = 0
  · subst hpcap
    simp only [↓reduceIte, emp_sepConj]
    refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl ?_
    wp_steps
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.fold hp24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hcrl_epi
    refine SepWPp.perm
      (step_epilogue_284 (r := .ok outBs) (Extra := dirGetRoBundlePlaced w0 w1 wTail)
        hstk hfull hsp0_al
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2]⟩)
      (by sep_frame)
  · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
    simp only [hpcap, ↓reduceIte]
    refine seq_lscro_state (mid := (blkPl_589).base + 464#64) hcrl ?_
    wp_steps
    apply SepWP.fold hrepack_out (by sep_frame)
    apply SepWP.fold (getResultAt_ok_of_vec A x.ret r1 r0 outBs) (by sep_frame)
    apply SepWP.fold hsp0_24 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_d
    refine SepWPp.perm
      (step_dealloc_epilogue_464 (r := .ok outBs)
        (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
        (Extra := dirGetRoBundlePlaced w0 w1 wTail)
        hC hcstk hstk hfull hsp0_al hcrl_d
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        hpcap hpth_cap_lt
        ⟨hres.1, by simp only [wp_norm, arm64_norm, hres.2]⟩)
      (by sep_frame)

theorem step_after_read_err [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {r0 r1 r2 r3 r4 r5 : BitVec 64}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : (Except.error () : Except Unit (List (BitVec 8))) = x.dir.get rd s0.fs.files x.name ∧
      s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((((ioVecAt A (s0.sp - 112#64) (.error ()) ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        ((x.ret ↦₆₄ r5) ∗ ((x.ret + 8#64) ↦₆₄ r4) ∗ ((x.ret + 16#64) ↦₆₄ r3) ∗
         ((x.ret + 24#64) ↦₆₄ r2) ∗ ((x.ret + 32#64) ↦₆₄ r1) ∗ ((x.ret + 40#64) ↦₆₄ r0)) ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  dsimp only [ioVecAt]
  simp only [sepConj_assoc]
  have hsp0_24_err :
      ((s0.sp - 112#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (s0.sp - 112#64 + 8#64) 16 ⊢
      memRegion (s0.sp - 112#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64) 8 16 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)
  have hpfx_s : s0.trace <+: s.trace := ⟨[], by simp [hres.2]⟩
  have hshim := shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC
  have halloc := alloc_lscro_of_cli (callerProg := lsProg_589 H) hC
  have hpanic := panic_at_handle_error_589 hpan
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
  have hcstk_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
        stackAt (s0.sp - 112#64) extHookStack ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk (by omega)]
    exact Entails.refl _
  refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
  wp_steps
  apply SepWP.fold hsp0_24_err (by sep_frame)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  refine call_lscro_frame (x := ())
    (T := stackAt (s0.sp - 112#64) extHookStack)
    hshim hcrl1 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp_al)
    (by wp_norm_lhs)
    (by simp only [withStack, sessionShimSpec, emp_sepConj, pure_true_sepConj, wp_norm, hsp])
    trivial (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQp_false)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
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
    have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
  have hx21_1 : sf1.readReg64 .x21 = pathPtr := by
    have := hcs1.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21
  have htr1_eq : sf1.trace = s.trace := htr1
  have hlay22 : LayoutOk 22 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl3
  refine call_lscro_frame (x := (22, 1))
    (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
    halloc hcrl3 (by wp_norm_lhs)
    (by simp only [wp_norm, arm64_norm, *])
    (by simpa only [wp_norm, arm64_norm] using hsp1_al)
    (by wp_norm_lhs) (by simp only [rustAllocSpecWithStack, wp_norm, hsp1_eq]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], hlay22⟩)
    (by sep_frame)
    (fun _ _ _ _ he => not_satisfies_false_sepConj he)
    (fun _ _ => dirGetPanicQp_false)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
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
  have hx21_2 : sf2.readReg64 .x21 = pathPtr := by
    have := hcs2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx21_1
  by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
    rw [ite_true_eq hoom]
    simp only [sepConj_assoc]
    refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
      fun htr2 => ?_
    have htr2_eq : sf2.trace = sf1.trace ++ [allocFailedEvent] := by
      simpa only [wp_norm, arm64_norm] using htr2
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSymCli)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
    exact dirGetPanicQp_of_panicked
      (by rw [htr1_eq]; exact hpfx_s)
      htr2_eq
      (by simp only [wp_norm, arm64_norm])
  · set buf := sf2.readReg64 (Reg.gpr 0#5)
    have hoom_ne : buf ≠ 0#64 := hoom
    have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
    rw [ite_false_eq hoom]
    simp only [sepConj_assoc]
    refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
      fun ⟨_, htr2⟩ => ?_
    have htr2_eq : sf2.trace = s.trace := by
      rw [htr2]; simp only [wp_norm, arm64_norm, htr1_eq]
    have hmem22 :
        memRegion buf 22 =
          (∃∗ b1 : BitVec 64, ∃∗ b0 : BitVec 64,
            (buf ↦₆₄ b0) ∗ ((buf + 8#64) ↦₆₄ b1) ∗ memRegion (buf + 16#64) 6) := by
      rw [memRegion_split buf 8 14 (by decide),
          memRegion_split (buf + 8#64) 8 6 (by decide),
          ProofLib.memRegion_eight, ProofLib.memRegion_eight]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    rw [hmem22]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun b1 => sepWPp_exists_left fun b0 => ?_
    unfold dirGetRoBundlePlaced
    refine seq_lscro_state (mid := (blkPl_589).base + 424#64) hcrl4 ?_
    wp_steps
    apply SepWP.fold (write_22_overlap_mid buf w1) (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl5
    rw [ProofLib.memRegion_eight (buf + 14#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun bt => ?_
    have herr_len : (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail).length = 22 := by
      simp [unpack64_length]
    by_cases hpcap : pathCap = 0
    · subst hpcap
      simp only [↓reduceIte, emp_sepConj]
      refine seq_lscro_state (mid := (blkPl_589).base + 284#64) hcrl5 ?_
      wp_steps
      apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
      apply SepWP.fold (getResultAt_err_of_ro A x.ret buf dgReadOpAddr
        (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail) herr_len hoom) (by sep_frame)
      apply SepWP.fold hp24 (by sep_frame)
      apply SepWP.fold hcstk_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro _hcrl6
      refine SepWPp.perm
        (step_epilogue_284 (r := .error ())
          (Extra := (dgUnreadableAddr ↦₆₄ᵣ w0) ∗
            ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
            ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail))
          hstk hfull hsp0_al
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs2.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
                exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
          ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2]⟩)
        (by sep_frame)
    · have hpcap_beq : (pathCap == 0#64) = false := beq_false_of_ne hpcap
      simp only [hpcap, ↓reduceIte]
      refine seq_lscro_state (mid := (blkPl_589).base + 464#64) hcrl5 ?_
      wp_steps
      apply SepWP.fold (write_22_overlap_done buf w0 w1 wTail) (by sep_frame)
      apply SepWP.fold (getResultAt_err_of_ro A x.ret buf dgReadOpAddr
        (unpack64 w0 ++ (unpack64 w1).take 6 ++ unpack64 wTail) herr_len hoom) (by sep_frame)
      apply SepWP.fold hcstk_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl6
      refine SepWPp.perm
        (step_dealloc_epilogue_464 (r := .error ())
          (pathCap := pathCap) (pathPtr := pathPtr) (pathLenW := BitVec.ofNat 64 pth.length)
          (Extra := (dgUnreadableAddr ↦₆₄ᵣ w0) ∗
            ((dgUnreadableAddr + 8#64) ↦₆₄ᵣ w1) ∗
            ((dgUnreadableAddr + 14#64) ↦₆₄ᵣ wTail))
          hC hcstk hstk hfull hsp0_al hcrl6
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp2_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs2.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs_setMem, calleeSavedVRegs_setPC, calleeSavedVRegs_writeReg64];
                exact calleeSavedVRegs_writeVReg128 sf2 (0#5) (w1 ++ w0) (by decide)))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          hpcap hpth_cap_lt
          ⟨hres.1, by simp only [wp_norm, arm64_norm, htr2_eq, hres.2]⟩)
        (by sep_frame)

theorem step_after_read [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {cstk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {r : Except Unit (List (BitVec 8))}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hcstk : extHookStack ≤ cstk)
    (hstk : 112 + cstk ≤ stk) (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 336#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx21 : s.readReg64 .x21 = pathPtr)
    (hres : r = x.dir.get rd s0.fs.files x.name ∧ s.trace = s0.trace) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      (((ioVecAt A (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail))
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R) R) := by
  have hdrop := vecU8At_drop_buf A pathCap pathPtr pth hpth_le hpth_cap_lt
  have hpre_drop :
      ((ioVecAt A (s0.sp - 112#64) r ∗
        (pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail) ⊢
      (((ioVecAt A (s0.sp - 112#64) r ∗
        (if pathCap = 0 then emp else A.live pathPtr pathCap.toNat 1 ∗ memRegion pathPtr pathCap.toNat)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) cstk ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail) := by
    simp only [sepConj_assoc]
    rw [← sepConj_assoc (pathPtr ↦ₛ pth)]
    exact sepConj_mono_right (sepConj_mono_left hdrop)
  refine sepWPp_weaken_pre hpre_drop ?_
  rw [memRegion_48_split6 x.ret]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun r0 => sepWPp_exists_left fun r1 =>
    sepWPp_exists_left fun r2 => sepWPp_exists_left fun r3 =>
    sepWPp_exists_left fun r4 => sepWPp_exists_left fun r5 => ?_
  have hp24 :
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ⊢
      memRegion (s0.sp - 112#64 + 24#64) 24 := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))
  cases r with
  | ok outBs =>
    exact step_after_read_ok hC hcstk hstk hfull hsp0_al hpth_cap_lt hp24
      hcrl hpc hrun hsp_al hsp hhcs hx19 hx21 hres
  | error u =>
    cases u
    exact step_after_read_err hC hpan hcstk hstk hfull hsp0_al hpth_cap_lt hp24
      hcrl hpc hrun hsp_al hsp hhcs hx19 hx21 hres

/-! ## 9. Miss Empty-Dir Path (`+164`..`+332` for `dir.path = []`) on Block `589` -/

def PathIoContractPlaced [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks)
    (rd : ReadRule) (pathOk : List (BitVec 8) → Prop) (ioStk : Nat) : Prop :=
  ∀ (s0 s : State) (pathPtr : BitVec 64) (pth : List (BitVec 8)) (F : SepProp)
    (Q : State → SepProp → Prop) (Qp : State → SepProp → Prop),
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
    s.pc = (blkPl_589).base + 332#64 →
    s.status = .Running →
    s.spAligned = true →
    FsInv s0.fs.files s0.trace s →
    s.trace = s0.trace →
    s.readReg64 .x0 = pathPtr →
    (s.readReg64 .x1).toNat = pth.length →
    s.readReg64 .x8 = s.sp →
    pth.length < 2 ^ 32 →
    pathOk pth →
    (∀ (sc sf : State) (F' : SepProp), sc.trace = s0.trace →
      Qp sf ((⌜allocFailedIn sc sf ∧ sc.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F')) →
    (∀ sf : State,
      sf.pc = (blkPl_589).base + 336#64 →
      sf.status = .Running →
      sf.sp = s.sp →
      CalleeSavedPreserved s sf →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp (lsProg_589 H) (s0.readReg64 .x30) sf
        (((∃∗ r : Except Unit (List (BitVec 8)),
            ⌜r = rd s0.fs.files pth ∧ sf.trace = s0.trace⌝ ∗
            ioVecAt A s.sp r) ∗
          (pathPtr ↦ₛ pth) ∗ stackAt s.sp ioStk ∗ A.pool) ∗ F)
        Q Qp (fun _ => ⌜False⌝)) →
    SepWPp (lsProg_589 H) (s0.readReg64 .x30) s
      (((pathPtr ↦ₛ pth) ∗ memRegion s.sp 24 ∗ stackAt s.sp ioStk ∗ A.pool) ∗ F)
      Q Qp (fun _ => ⌜False⌝)

def stateOfLscroMiss [LibsignalPlacement] {st : State}
    (_ : StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) : State := st

theorem false_of_fsInv_false_miss {F0 : FsFiles} {T0 : List TraceEvent} {sf : State}
    {m : Memory} {R : SepProp}
    (h : m ⊨ (⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ R) : False := by
  rw [sepConj_assoc, satisfies_pure_sepConj, satisfies_pure_sepConj] at h
  exact h.2.1

theorem panicQp_of_fsInv_false_miss [LibsignalPlacement]
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {A : RustAlloc}
    {stk : Nat} {x : DirGetGhost} {s0 sf : State} {Fr R : SepProp}
    {F0 : FsFiles} {T0 : List TraceEvent} {Frame : SepProp} :
    dirGetPanicQpPlaced rd pathOk A stk x s0 Fr R sf ((⌜FsInv F0 T0 sf⌝ ∗ ⌜False⌝) ∗ Frame) :=
  fun hm => False.elim (false_of_fsInv_false_miss (by rw [sepConj_assoc] at hm; exact hm))

theorem step_miss_call_io [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 sm : State}
    {pathCap pathPtr : BitVec 64} {pth : List (BitVec 8)}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hIoCall : PathIoContractPlaced A H rd pathOk ioStk)
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hget_eq : x.dir.get rd s0.fs.files x.name = rd s0.fs.files (pathOf x.dir.path x.name))
    (hpth_eq : pth = pathOf x.dir.path x.name)
    (hpth_le : pth.length ≤ pathCap.toNat)
    (hpth_cap_lt : pathCap.toNat < 2 ^ 63)
    (hpth_lt32 : pth.length < 2 ^ 32)
    (hcrl_m : StoreKit.LibsignalCodeRoLoaded lsmpl sm.mem)
    (hpc_m : sm.pc = (blkPl_589).base + 320#64)
    (hrun_m : sm.status = .Running)
    (hsp_al_m : sm.spAligned = true)
    (hsp_m : sm.sp = s0.sp - 112#64)
    (hhcs_m : HighCalleeSaved s0 sm)
    (hfs_m : sm.fs.files = s0.fs.files)
    (htr_m : sm.trace = s0.trace)
    (hx19_m : sm.readReg64 .x19 = x.ret)
    (hx20_m : sm.readReg64 .x20 = BitVec.ofNat 64 pth.length)
    (hx21_m : sm.readReg64 .x21 = pathPtr) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) sm
      (((pathPtr ↦ₛ pth) ∗
        (if pathCap = 0 then emp
         else A.live pathPtr pathCap.toNat 1 ∗
           memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
        ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
        ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
        ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
        dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hcstk_io : ioStk ≤ cstk :=
    Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64 hstk hfull)]
  have hcstk_io_join :
      memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
        stackAt (s0.sp - 112#64) ioStk ⊢
      stackAt (s0.sp - 112#64) cstk := by
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_io (cstk_le_pow64 hstk hfull)]
    exact Entails.refl _
  have hpth_fz : FrozenEq pth (pathOf x.dir.path x.name) := ⟨hpth_eq⟩
  clear hpth_eq
  refine seq_lscro_state (mid := (blkPl_589).base + 332#64) hcrl_m ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl_io
  rcases hpth_fz with ⟨hpth_eq⟩
  let s_io := stateOfLscroMiss hcrl_io
  have hpth_nat : (BitVec.ofNat 64 pth.length).toNat = pth.length :=
    ofNat64_toNat_of_lt32 hpth_lt32
  have hsp_cur : s_io.sp = s0.sp - 112#64 := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hpc_cur : s_io.pc = (blkPl_589).base + 332#64 := by
    dsimp only [s_io, stateOfLscroMiss]; wp_norm_lhs
  have hrun_cur : s_io.status = ExecStatus.Running := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hsp_al_cur : s_io.spAligned = true := by simpa only [s_io, stateOfLscroMiss, wp_norm, arm64_norm] using hsp_al_m
  have hinv_cur : FsInv s0.fs.files s0.trace s_io :=
    fsInv_of_files_trace_eq (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *])
  have htr_cur : s_io.trace = s0.trace := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx0_cur : s_io.readReg64 .x0 = pathPtr := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx1_cur : (s_io.readReg64 .x1).toNat = pth.length := by
    simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, hpth_nat]
  have hx8_cur : s_io.readReg64 .x8 = s_io.sp := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hhcs_cur : HighCalleeSaved s0 s_io :=
    hhcs_m.of_steps
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm])
      (by simp only [s_io, stateOfLscroMiss, calleeSavedVRegs, wp_norm, arm64_norm])
  have hx19_cur : s_io.readReg64 .x19 = x.ret := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  have hx21_cur : s_io.readReg64 .x21 = pathPtr := by simp only [s_io, stateOfLscroMiss, wp_norm, arm64_norm, *]
  let F_io : SepProp :=
    ((if pathCap = 0 then emp
      else A.live pathPtr pathCap.toNat 1 ∗
        memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
     ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
     ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
     ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
     dirAt A x.self x.dir ∗
     SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
     memRegion x.ret 48 ∗
     memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
     savedRegsAt (s0.sp - 112#64) s0) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  refine SepWPp.perm
    (P' := ((pathPtr ↦ₛ pth) ∗ memRegion s_io.sp 24 ∗
      stackAt s_io.sp ioStk ∗ A.pool) ∗ F_io) ?_ (by rw [hsp_cur]; dsimp only [F_io]; sep_frame)
  refine hIoCall s0 s_io pathPtr pth F_io _ _ hcrl_io
    hpc_cur hrun_cur hsp_al_cur hinv_cur htr_cur
    hx0_cur hx1_cur hx8_cur hpth_lt32 (by rwa [hpth_eq])
    (fun _ _ _ hsc => dirGetPanicQp_of_readPanic hsc)
    (fun sf_r hpc_r hrun_r hsp_r hcs_r hcrl_r => ?_)
  have hsp_r_al : sf_r.spAligned = true := spAligned_of_sp_eq hsp_al_cur hsp_r
  rw [hsp_cur] at hsp_r ⊢
  dsimp only [F_io]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWPp_exists_left fun r_io => SepWPp.pure_left fun hres_io => ?_
  have hhcs_r : HighCalleeSaved s0 sf_r := hhcs_cur.of_calleeSaved hcs_r
  have hx19_r : sf_r.readReg64 .x19 = x.ret := hcs_r.1.trans hx19_cur
  have hx21_r : sf_r.readReg64 .x21 = pathPtr := hcs_r.2.2.1.trans hx21_cur
  let P_ar : SepProp :=
    (ioVecAt A (s0.sp - 112#64) r_io ∗
      (pathPtr ↦ₛ pth) ∗
      (if pathCap = 0 then emp
       else A.live pathPtr pathCap.toNat 1 ∗
         memRegion (pathPtr + BitVec.ofNat 64 pth.length) (pathCap.toNat - pth.length)) ∗
      ((s0.sp - 112#64 + 24#64) ↦₆₄ pathCap) ∗
      ((s0.sp - 112#64 + 32#64) ↦₆₄ pathPtr) ∗
      ((s0.sp - 112#64 + 40#64) ↦₆₄ BitVec.ofNat 64 pth.length) ∗
      dirAt A x.self x.dir ∗
      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  refine SepWPp.perm
    (P' := (memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - ioStk) ∗
      stackAt (s0.sp - 112#64) ioStk) ∗ P_ar) ?_
    (by dsimp only [P_ar]; sep_frame)
  refine sepWPp_weaken_pre (sepConj_mono hcstk_io_join (Entails.refl P_ar)) ?_
  refine SepWPp.perm
    (step_after_read (cstk := cstk) (r := r_io)
      (pathCap := pathCap) (pathPtr := pathPtr) (pth := pth)
      (w0 := w0) (w1 := w1) (wTail := wTail)
      hC hpan hcstk_ext hstk hfull hsp0_al hpth_le hpth_cap_lt
      hcrl_r hpc_r hrun_r hsp_r_al hsp_r hhcs_r hx19_r hx21_r
      ⟨by rw [hres_io.1, hpth_eq, hget_eq], hres_io.2⟩)
    (by dsimp only [P_ar]; sep_frame)

theorem step_miss_empty [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hIoCall : PathIoContractPlaced A H rd pathOk ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hdir_nil : x.dir.path = [])
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hget_eq : x.dir.get rd s0.fs.files x.name =
      rd s0.fs.files (pathOf x.dir.path x.name) := by
    cases hd : x.dir with | mk p ch =>
    simp only [hd] at hall_ne ⊢
    have h1 := dirGhost_get_append_of_ne ch [] p rd s0.fs.files x.name hall_ne
    simpa [dirGhost_get_nil] using h1
  unfold dirAt strRefAt
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun dirPathPtr => ?_
  have hself32 : (x.self + 24#64) + 8#64 = x.self + 32#64 := by simp only [BitVec.add_assoc]; rfl
  rw [hself32]
  have hrepack_dir :
      RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
        ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
        ((x.self + 32#64) ↦₆₄ BitVec.ofNat 64 x.dir.path.length) ∗
        (dirPathPtr ↦ᵣ x.dir.path) ⊢
      dirAt A x.self x.dir := by
    unfold dirAt strRefAt
    refine sepConj_mono (Entails.refl _) ?_
    refine Entails.trans ?_ (Entails.sepExists_intro dirPathPtr)
    rw [hself32]
    exact Entails.refl _
  have hbit63 : (BitVec.ofNat 64 x.name.length)[63] = false :=
    ofNat_getElem_63_false (lt_pow63_of_lt_pow32 hname_lt)
  have hbit63_lsb : (BitVec.ofNat 64 x.name.length).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (lt_pow63_of_lt_pow32 hname_lt)
  have _ := hbit63; have _ := hbit63_lsb
  have hsp24_split :
      memRegion (s0.sp - 112#64 + 24#64) 24 =
        (∃∗ p2 : BitVec 64, ∃∗ p1 : BitVec 64, ∃∗ p0 : BitVec 64,
          ((s0.sp - 112#64 + 24#64) ↦₆₄ p0) ∗
          ((s0.sp - 112#64 + 32#64) ↦₆₄ p1) ∗
          ((s0.sp - 112#64 + 40#64) ↦₆₄ p2)) := by
    rw [memRegion_split (s0.sp - 112#64 + 24#64) 8 16 (by decide),
        memRegion_split (s0.sp - 112#64 + 24#64 + 8#64) 8 8 (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
  rw [hsp24_split]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine sepWPp_exists_left fun p2 => sepWPp_exists_left fun p1 =>
    sepWPp_exists_left fun p0 => ?_
  have hnm_cases : x.name = [] ∨ 0 < x.name.length := by cases x.name <;> simp
  rcases hnm_cases with hnm_nil | hnm_pos
  · refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl ?_
    simp only [hdir_nil, hnm_nil, List.length_nil] at hx20 ⊢
    wp_steps
    have hrepack_dir0 :
        RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl_m
    have heq_emp : ((1#64 : BitVec 64) ↦ₛ ([] : List (BitVec 8))) = emp := pointsToBytes_nil _
    rw [← emp_sepConj (dirAt A x.self x.dir), ← heq_emp]
    refine SepWPp.perm
      (step_miss_call_io (pathStk := pathStk)
        hC hpan hIoCall hstk hfull hsp0_al hpOk hget_eq
        (pathCap := 0#64) (pathPtr := 1#64) (pth := [])
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (by simp [hdir_nil, hnm_nil, pathOf]) (by simp) (by decide) (by decide)
        hcrl_m
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm]))
      (by
        have h0_ite :
            (if (0#64 : BitVec 64) = 0 then emp
             else A.live 1#64 (0#64).toNat 1 ∗
               memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
                 ((0#64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
        have h0_len : BitVec.ofNat 64 ([] : List (BitVec 8)).length = 0#64 := rfl
        rw [hnm_nil, h0_ite, h0_len]
        simp only [emp_sepConj, sepConj_emp]
        ac_rfl)
  · have hnm_ne0 : (BitVec.ofNat 64 x.name.length == 0#64) = false :=
      ofNat_beq_zero_false hnm_pos (lt_pow64_of_lt_pow32 hname_lt)
    have _ := hnm_ne0
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32 hname_lt
    have hlay_nm : LayoutOk x.name.length 1 :=
      ⟨hnm_pos, ⟨0, rfl⟩, Nat.succ_le_of_lt (lt_pow63_of_lt_pow32 hname_lt)⟩
    have hshim_fs := subroutine_ok_lscro_withFsInv hFs
      (shim_lscro_of_cli (callerProg := lsProg_589 H) (stk := extHookStack) hC) s0.fs.files s0.trace
    have halloc_fs := subroutine_ok_lscro_withFsInv hFs
      (alloc_lscro_of_cli (callerProg := lsProg_589 H) hC) s0.fs.files s0.trace
    have hmc_fs := subroutine_ok_lscro_withFsInv hFs
      (memcpy_bytesAt_lscro_ok_at_589 hC hRO x.nameRo) s0.fs.files s0.trace
    have hpanic := panic_at_handle_error_589 hpan
    have _ := hpanic
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64 hstk hfull)]
    have hcstk_ext_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - extHookStack) ∗
          stackAt (s0.sp - 112#64) extHookStack ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_ext (cstk_le_pow64 hstk hfull)]
      exact Entails.refl _
    refine seq_lscro_state (mid := lsρ lsRustNoAllocShimSymCli) hcrl ?_
    simp only [hdir_nil, List.length_nil]
    wp_steps
    have hrepack_dir0 :
        RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ 0#64) ∗
          (dirPathPtr ↦ᵣ []) ⊢
        dirAt A x.self x.dir := by
      simpa [hdir_nil] using hrepack_dir
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    refine call_lscro_frame (x := ())
      (T := stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      hshim_fs hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, withStack, sessionShimSpec, emp_sepConj, wp_norm, hsp]; rfl)
      (fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *]))
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun _ _ => panicQp_of_fsInv_false_miss)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    simp only [withFsInv, withStack, sessionShimSpec, wp_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun hfs1_inv => SepWPp.pure_left fun htr1 => ?_
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
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have hx20_1 : sf1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs1.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20
    have hx22_1 : sf1.readReg64 .x22 = x.nameA := by
      have := hcs1.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22
    have htr1_s0 : sf1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    refine seq_lscro_state (mid := lsρ lsRustAllocSymCli) hcrl2 ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine call_lscro_frame (x := (x.name.length, 1))
      (T := A.pool ∗ stackAt (s0.sp - 112#64) extHookStack)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      halloc_fs hcrl3 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp1_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, rustAllocSpecWithStack, wp_norm, hsp1_eq, pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  by simp only [wp_norm, arm64_norm, *],
                  by simp only [wp_norm, arm64_norm],
                  hlay_nm⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun _ _ => panicQp_of_fsInv_false_miss)
      (fun sf2 hpc2 hrun2 hsp2 hcs2 hcrl4 => ?_)
    simp only [withFsInv, rustAllocSpecWithStack, wp_norm, hsp1_eq, sepConj_assoc]
    refine SepWPp.pure_left fun hfs2_inv => ?_
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
    have hx20_2 : sf2.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
      have := hcs2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_1
    have hx22_2 : sf2.readReg64 .x22 = x.nameA := by
      have := hcs2.2.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx22_1
    by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
    · have hoom64 : sf2.readReg64 .x0 = 0#64 := hoom
      have _ := hoom64
      rw [ite_true_eq hoom]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun htr2 => ?_
      have htr2_eq : sf2.trace = s0.trace ++ [allocFailedEvent] := by
        simpa only [wp_norm, arm64_norm, htr1_s0] using htr2
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSymCli)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) ?_
      exact dirGetPanicQp_of_panicked List.prefix_rfl htr2_eq (by simp only [wp_norm, arm64_norm])
    · set buf := sf2.readReg64 (Reg.gpr 0#5)
      have hoom_ne : buf ≠ 0#64 := hoom
      have hoom_beq : (buf == 0#64) = false := beq_false_of_ne hoom_ne
      have _ := hoom_beq
      rw [ite_false_eq hoom]
      simp only [sepConj_assoc]
      refine sepWPp_pure_mid2 (P1 := A.pool) (P2 := stackAt (s0.sp - 112#64) extHookStack)
        fun ⟨_, htr2⟩ => ?_
      have htr2_s0 : sf2.trace = s0.trace := by rw [htr2]; simp only [wp_norm, arm64_norm, *]
      have hfs2 : sf2.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs2_inv htr2_s0
      refine seq_lscro_state (mid := lsρ memcpyName) hcrl4 ?_
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl5
      refine call_lscro_frame (x := (buf, x.nameA, x.name))
        (T := memRegion buf x.name.length ∗
          SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
          stackAt (s0.sp - 112#64) extHookStack)
        (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
        hmc_fs hcrl5 (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp2_al)
        (by wp_norm_lhs)
        (by simp only [withFsInv, withStack, sessionMemcpyBytesAtSpec, wp_norm, hsp2_eq,
              sepConj_assoc, pure_sepConj_pure_assoc]; rfl)
        (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                      (by simp only [wp_norm, arm64_norm, *]),
                    rfl, trivial, hnm_toNat,
                    Nat.le_of_lt (lt_pow64_of_lt_pow32 hname_lt)⟩)
        (by sep_frame)
        (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
        (fun _ _ => panicQp_of_fsInv_false_miss)
        (fun sf3 hpc3 hrun3 hsp3 hcs3 hcrl6 => ?_)
      simp only [withFsInv, withStack, sessionMemcpyBytesAtSpec, wp_norm, hsp2_eq, sepConj_assoc]
      refine SepWPp.pure_left fun hfs3_inv => SepWPp.pure_left fun ⟨_, htr3⟩ => ?_
      have hhcs3 : HighCalleeSaved s0 sf3 :=
        hhcs2.of_step_call hcs3
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
      have hsp3_eq : sf3.sp = s0.sp - 112#64 := by rw [hsp3]; simp only [wp_norm, arm64_norm, *]
      have hsp3_al : sf3.spAligned = true :=
        spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp2_al) hsp3
      have hx19_3 : sf3.readReg64 .x19 = x.ret := by
        have := hcs3.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19_2
      have hx20_3 : sf3.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by
        have := hcs3.2.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx20_2
      have hx21_3 : sf3.readReg64 .x21 = buf := by
        have := hcs3.2.2.1; simp only [wp_norm, arm64_norm] at this; exact this
      have htr3_s0 : sf3.trace = s0.trace := by rw [htr3]; simp only [wp_norm, arm64_norm, *]
      have hfs3 : sf3.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs3_inv htr3_s0
      have hcap_ne : BitVec.ofNat 64 x.name.length ≠ 0 := by
        intro h0
        have ht : (BitVec.ofNat 64 x.name.length).toNat = (0 : BitVec 64).toNat :=
          congrArg BitVec.toNat h0
        rw [hnm_toNat] at ht
        exact Nat.ne_of_gt hnm_pos ht
      refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl6 ?_
      wp_steps
      apply SepWP.fold hcstk_ext_join (by sep_frame)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcrl7
      have hrem_zero :
          memRegion (buf + BitVec.ofNat 64 x.name.length)
            ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) = emp := by
        rw [hnm_toNat, Nat.sub_self, memRegion_zero]
      rw [← sepConj_emp (A.live buf x.name.length 1), ← hrem_zero]
      have hlive_eq :
          A.live buf x.name.length 1 ∗
            memRegion (buf + BitVec.ofNat 64 x.name.length)
              ((BitVec.ofNat 64 x.name.length).toNat - x.name.length) =
          (if BitVec.ofNat 64 x.name.length = 0 then emp
           else A.live buf (BitVec.ofNat 64 x.name.length).toNat 1 ∗
             memRegion (buf + BitVec.ofNat 64 x.name.length)
               ((BitVec.ofNat 64 x.name.length).toNat - x.name.length)) := by
        rw [ite_false_eq hcap_ne, hnm_toNat]
      rw [hlive_eq]
      refine SepWPp.perm
        (step_miss_call_io (pathStk := pathStk)
          hC hpan hIoCall hstk hfull hsp0_al hpOk hget_eq
          (pathCap := BitVec.ofNat 64 x.name.length) (pathPtr := buf) (pth := x.name)
          (w0 := w0) (w1 := w1) (wTail := wTail)
          (by simp [hdir_nil, pathOf]) (by rw [hnm_toNat])
          (by rw [hnm_toNat]; exact lt_pow63_of_lt_pow32 hname_lt) hname_lt
          hcrl7
          (by wp_norm_lhs)
          (by simp only [wp_norm, arm64_norm, *])
          (by simpa only [wp_norm, arm64_norm] using hsp3_al)
          (by simp only [wp_norm, arm64_norm, *])
          (hhcs3.of_steps
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [wp_norm, arm64_norm])
            (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by sep_frame)

/-! ## 10. Miss Path Dispatch & Non-Empty `path` Branch (`+164`..`+332`) on Block `589` -/

theorem step_miss_tail [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {pathStk ioStk stk : Nat}
    {x : DirGetGhost} {s0 s : State}
    {w0 w1 wTail : BitVec 64} {R : SepProp}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hPath : subroutine_ok (lsProg_589 H) (lsmpl.base 596)
      (pathSpecPlaced A pathStk))
    (hIoCall : PathIoContractPlaced A H rd pathOk ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 112 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hfull : stk ≤ 2 ^ 64)
    (hsp0_al : s0.spAligned = true)
    (hname_lt : x.name.length < 2 ^ 32)
    (hdir_lt : x.dir.path.length < 2 ^ 32)
    (hpOk : pathOk (pathOf x.dir.path x.name))
    (hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32)
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_589).base + 164#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = s0.sp - 112#64)
    (hhcs : HighCalleeSaved s0 s)
    (hfs : s.fs.files = s0.fs.files)
    (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.name.length)
    (hx21 : s.readReg64 .x21 = x.self)
    (hx22 : s.readReg64 .x22 = x.nameA)
    (hall_ne : ∀ e ∈ x.dir.changed, e.1 ≠ x.name) :
    SepWPp (lsProg_589 H)
      (s0.readReg64 .lr) s
      ((dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion x.ret 48 ∗
        stackAt (s0.sp - 112#64) (dirGetCalleeStk pathStk ioStk) ∗
        memRegion (s0.sp - 112#64) 24 ∗ memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        savedRegsAt (s0.sp - 112#64) s0 ∗ A.pool) ∗
        dirGetRoBundlePlaced w0 w1 wTail)
      (dirGetPostQPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R)
      (dirGetPanicQpPlaced rd pathOk A stk x s0
        (memRegion (s0.sp - BitVec.ofNat 64 stk)
          (stk - (112 + dirGetCalleeStk pathStk ioStk)) ∗ R) R) := by
  have hdir_cases : x.dir.path = [] ∨ (x.dir.path ≠ [] ∧ 0 < x.dir.path.length) := by
    cases x.dir.path <;> simp
  rcases hdir_cases with hdir_nil | ⟨hdir_ne, hdir_pos⟩
  · exact step_miss_empty hC hpan hRO hIoCall hFs hstk hfull hsp0_al
      hname_lt hpOk hdir_nil hcrl hpc hrun hsp_al hsp hhcs hfs htr
      hx19 hx20 hx21 hx22 hall_ne
  · let cstk := dirGetCalleeStk pathStk ioStk
    have hcstk_path : pathStk ≤ cstk :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_max_left _ _)
    have hget_eq : x.dir.get rd s0.fs.files x.name =
        rd s0.fs.files (pathOf x.dir.path x.name) := by
      cases hd : x.dir with | mk p ch =>
      simp only [hd] at hall_ne ⊢
      have h1 := dirGhost_get_append_of_ne ch [] p rd s0.fs.files x.name hall_ne
      simpa [dirGhost_get_nil] using h1
    unfold dirAt strRefAt
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine sepWPp_exists_left fun dirPathPtr => ?_
    have hself32 : (x.self + 24#64) + 8#64 = x.self + 32#64 := by simp only [BitVec.add_assoc]; rfl
    rw [hself32]
    have hrepack_dir :
        RustHeap.vecOf A 48 8 (dirEntryAt A) x.self x.dir.changed ∗
          ((x.self + 24#64) ↦₆₄ dirPathPtr) ∗
          ((x.self + 32#64) ↦₆₄ BitVec.ofNat 64 x.dir.path.length) ∗
          (dirPathPtr ↦ᵣ x.dir.path) ⊢
        dirAt A x.self x.dir := by
      unfold dirAt strRefAt
      refine sepConj_mono (Entails.refl _) ?_
      refine Entails.trans ?_ (Entails.sepExists_intro dirPathPtr)
      rw [hself32]
      exact Entails.refl _
    have hdir_ne0 : (BitVec.ofNat 64 x.dir.path.length == 0#64) = false :=
      ofNat_beq_zero_false hdir_pos (lt_pow64_of_lt_pow32 hdir_lt)
    have hdir_toNat : (BitVec.ofNat 64 x.dir.path.length).toNat = x.dir.path.length :=
      ofNat64_toNat_of_lt32 hdir_lt
    have hnm_toNat : (BitVec.ofNat 64 x.name.length).toNat = x.name.length :=
      ofNat64_toNat_of_lt32 hname_lt
    have _ := hdir_ne0; have _ := hdir_toNat; have _ := hnm_toNat
    have hpth_lt32 : (x.dir.path ++ [0x2f#8] ++ x.name).length < 2 ^ 32 := by
      rw [(pathOf_eq_path hdir_ne x.name).symm]
      exact hpth_len_lt
    have hpath_fs := subroutine_ok_lscro_withFsInv hFs hPath s0.fs.files s0.trace
    rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
    have hcstk_path_join :
        memRegion (s0.sp - 112#64 - BitVec.ofNat 64 cstk) (cstk - pathStk) ∗
          stackAt (s0.sp - 112#64) pathStk ⊢
        stackAt (s0.sp - 112#64) cstk := by
      rw [stackAt_sub_split (s0.sp - 112#64) hcstk_path (cstk_le_pow64 hstk hfull)]
      exact Entails.refl _
    refine seq_lscro_state (mid := lsmpl.base 596) hcrl ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    have htr_call : (stateOfLscroMiss hcrl1).trace = s0.trace := by
      simp only [stateOfLscroMiss, wp_norm, arm64_norm, *]
    dsimp only [stateOfLscroMiss] at htr_call
    refine call_lscro_frame
      (x := PathGhost.mk dirPathPtr x.dir.path true x.nameA x.name x.nameRo
        (s0.sp - 112#64 + 24#64))
      (T := (dirPathPtr ↦ᵣ x.dir.path) ∗
        SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
        memRegion (s0.sp - 112#64 + 24#64) 24 ∗
        stackAt (s0.sp - 112#64) pathStk ∗ A.pool)
      (hoom := fun _ _ _ ho => False.elim (false_of_fsInv_false_miss ho))
      hpath_fs hcrl1 (by wp_norm_lhs)
      (by simp only [wp_norm, arm64_norm, *])
      (by simpa only [wp_norm, arm64_norm] using hsp_al)
      (by wp_norm_lhs)
      (by simp only [withFsInv, SpqrV1.ChainProofs.bytesAt_true, wp_norm, hsp,
            pure_sepConj_pure_assoc]; rfl)
      (by refine ⟨fsInv_of_files_trace_eq (by simp only [wp_norm, arm64_norm, *])
                    (by simp only [wp_norm, arm64_norm, *]),
                  trivial, trivial, hdir_toNat, trivial, hnm_toNat,
                  hdir_lt, hname_lt⟩)
      (by sep_frame)
      (fun _ _ _ _ hex => false_of_fsInv_false_miss hex)
      (fun sf_pan _ hm_pan => by
        have htmp := hm_pan
        dsimp only [withFsInv] at htmp
        simp only [sepConj_assoc, satisfies_pure_sepConj] at htmp
        rcases htmp with ⟨_, ⟨haf_p, hpfx_p⟩, _⟩
        rw [htr_call] at hpfx_p
        exact dirGetPanicQp_of_ok
          (by simpa only [allocFailedIn, htr_call] using haf_p) hpfx_p hm_pan)
      (fun sf1 hpc1 hrun1 hsp1 hcs1 hcrl2 => ?_)
    simp only [withFsInv, SpqrV1.ChainProofs.bytesAt_true, wp_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_left fun hfs1_inv => SepWPp.pure_left fun htr1 => ?_
    refine sepWPp_unfold_vecU8 fun pathCap pathPtr hpth_le hpth_cap_lt _ => ?_
    have hhcs1 : HighCalleeSaved s0 sf1 :=
      hhcs.of_step_call hcs1
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [calleeSavedVRegs, wp_norm, arm64_norm])
    have hsp1_eq : sf1.sp = s0.sp - 112#64 := by rw [hsp1]; simp only [wp_norm, arm64_norm, *]
    have hsp1_al : sf1.spAligned = true :=
      spAligned_of_sp_eq (by simpa only [wp_norm, arm64_norm] using hsp_al) hsp1
    have hx19_1 : sf1.readReg64 .x19 = x.ret := by
      have := hcs1.1; simp only [wp_norm, arm64_norm] at this; exact this.trans hx19
    have htr1_s0 : sf1.trace = s0.trace := htr1.trans htr
    have hfs1 : sf1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfs1_inv htr1_s0
    simp only [arm64_norm]
    refine seq_lscro_state (mid := (blkPl_589).base + 320#64) hcrl2 ?_
    wp_steps
    apply SepWP.fold hrepack_dir (by sep_frame)
    apply SepWP.fold hcstk_path_join (by sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl3
    refine SepWPp.perm
      (step_miss_call_io (pathStk := pathStk)
        hC hpan hIoCall hstk hfull hsp0_al hpOk hget_eq
        (pathCap := pathCap) (pathPtr := pathPtr) (pth := x.dir.path ++ [0x2f#8] ++ x.name)
        (w0 := w0) (w1 := w1) (wTail := wTail)
        (pathOf_eq_path hdir_ne x.name).symm hpth_le hpth_cap_lt hpth_lt32
        hcrl3
        (by wp_norm_lhs)
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa only [wp_norm, arm64_norm] using hsp1_al)
        (by simp only [wp_norm, arm64_norm, *])
        (hhcs1.of_steps
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [wp_norm, arm64_norm])
          (by simp only [calleeSavedVRegs, wp_norm, arm64_norm]))
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm])
        (by simp only [wp_norm, arm64_norm]))
      (by simp only [arm64_norm]; sep_frame)

/-! ## 11. Isolated `read_file` Call Site & Entry Prologue (`+0`..`+68`) on Block `589` -/

private theorem lscro_of_mem_eq [LibsignalPlacement] {s1 s2 : State}
    (h : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem) (hm : s1.mem = s2.mem) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem :=
  hm ▸ h

theorem step_read_file_call [LibsignalPlacement]
    {A : RustAlloc} {H : LibsignalHooks}
    {rd : ReadRule} {pathOk : List (BitVec 8) → Prop} {readStk : Nat}
    (hRead : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk))) :
    PathIoContractPlaced A H rd pathOk readStk := by
  intro s0 s pathPtr pth F Q Qp hcrl hpc hrun hsp hinv htr
    hx0 hx1 hx8 hlt hpOk hQp_false hnext
  have hfiles : s.fs.files = s0.fs.files :=
    hinv.files_eq (evs := []) (by simp [htr]) NoFsEv.nil
  refine SepWPp.seq_frozen
    (mid := lsρ lsReadFileSym)
    (Φ := fun m => StoreKit.LibsignalCodeRoLoaded lsmpl m)
    (fun m m' hf hkf => hf.of_keepsFrozen hkf)
    hcrl ?_
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcrl1
  refine call_lscro_frame (x := ReadFileGhost.mk pathPtr pth s.sp)
    (T := (pathPtr ↦ₛ pth) ∗ memRegion s.sp 24 ∗ stackAt s.sp readStk ∗ A.pool)
    (F := F)
    hRead (lscro_of_mem_eq hcrl1 (by simp only [wp_norm]))
    (by wp_norm_lhs)
    (by simp only [wp_norm, *])
    (by simpa only [arm64_norm] using hsp)
    (by wp_norm_lhs)
    (by dsimp only [readFileSpecPlaced]; simp only [wp_norm]; rfl)
    (by refine ⟨by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                by simp only [wp_norm, arm64_norm, *],
                hlt, hpOk⟩)
    (by simp only [wp_norm])
    (fun _ _ _ _ hex => not_satisfies_false_sepConj hex)
    (fun sf _ => hQp_false _ sf F (by simp only [wp_norm, arm64_norm, *]))
    (fun sf hpc_f hrun_f hsp_f hcs hcrl_f => ?_)
  have hcs' : CalleeSavedPreserved s sf := ⟨
    by simpa only [wp_norm] using hcs.1,
    by simpa only [wp_norm] using hcs.2.1,
    by simpa only [wp_norm] using hcs.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.1,
    by simpa only [wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.1,
    by simpa only [calleeSavedVRegs, wp_norm] using hcs.2.2.2.2.2.2.2.2.2.2.2⟩
  have hsp_f' : sf.sp = s.sp := by rw [hsp_f]; simp only [wp_norm]
  dsimp only [readFileSpecPlaced]
  have hh := hnext sf hpc_f hrun_f hsp_f' hcs' hcrl_f
  simpa [allocFailedIn, wp_norm, arm64_norm, hfiles, htr, sepExists_sepConj_left, sepConj_assoc] using hh

private def stateOfLscro [LibsignalPlacement] {st : State}
    (_ : StoreKit.LibsignalCodeRoLoaded lsmpl st.mem) : State := st

private theorem setup_x24_48_eq (n : Nat) :
    (BitVec.ofNat 64 n + (BitVec.ofNat 64 n <<< 1)) <<< 4 =
      BitVec.ofNat 64 (48 * n) := by
  have hb : ∀ v : BitVec 64, (v + (v <<< 1)) <<< 4 = 48#64 * v := by intro v; bv_bits
  rw [hb, Nat.mul_comm 48 n, BitVec.ofNat_mul, BitVec.mul_comm]

private theorem sub112_aligned {sp : BitVec 64} (hm : sp &&& 15#64 = 0#64) :
    (sp - 112#64) &&& 15#64 = 0#64 := by
  bv_bits

theorem dirGet_placed_ok_of_ioCall [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk ioStk stk : Nat}
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    (hPath : subroutine_ok (lsProg_589 H) (lsmpl.base 596) (pathSpecPlaced A pathStk))
    (hIoCall : PathIoContractPlaced A H rd pathOk ioStk)
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + dirGetCalleeStk pathStk ioStk ≤ stk)
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A stk) := by
  let cstk := dirGetCalleeStk pathStk ioStk
  have hcstk_ext : extHookStack ≤ cstk := Nat.le_max_right _ _
  have hstk112 : 112 + cstk ≤ stk := hstk
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre halign
  have hsp0_mask : (s0.sp &&& 15#64 == 0#64) = true := halign
  have hsp_sub_al : ({ s0 with sp := s0.sp - 112#64 } : State).spAligned = true :=
    beq_iff_eq.mpr (sub112_aligned (eq_of_beq hsp0_mask))
  obtain ⟨hcrl0, hpre0⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  dsimp only [dirGetSpecPlaced] at hpre0
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre0
  rcases hpre0 with ⟨⟨hx0, hx1, hx2, hx3, hname_lt, hdir_lt, hpOk⟩, hsat0⟩
  have hpth_len_lt : (pathOf x.dir.path x.name).length < 2 ^ 32 := hpathLen _ hpOk
  have hx3_bv : s0.readReg64 .x3 = BitVec.ofNat 64 x.name.length := by
    apply BitVec.eq_of_toNat_eq
    rw [hx3, ofNat64_toNat_of_lt32 hname_lt]
  have hfull : stk ≤ 2 ^ 64 :=
    stk_le_of_memRegion_sep (r := x.ret) (sp0 := s0.sp) (stk := stk)
      (F := dirAt A x.self x.dir ∗ SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗ A.pool ∗ R)
      (Satisfies.mono (Entails.of_eq (by sep_frame)) hsat0)
  obtain ⟨w0, w1, wTail, hsat_ro⟩ := dirGetRoData_of_lscro hcrl0 hsat0
  rw [stackAt_dirGet_split s0.sp hstk112 hfull] at hsat_ro
  let P0 : SepProp :=
    (dirAt A x.self x.dir ∗
      SpqrV1.ChainProofs.bytesAt x.nameRo x.nameA x.name ∗
      memRegion x.ret 48 ∗
      stackAt (s0.sp - 112#64) cstk ∗
      memRegion (s0.sp - 112#64) 112 ∗
      A.pool) ∗
    dirGetRoBundlePlaced w0 w1 wTail
  let Fr : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - (112 + cstk)) ∗ R
  refine ⟨P0, Fr, Satisfies.mono (Entails.of_eq (by dsimp only [P0, Fr]; sep_frame)) hsat_ro, ?_⟩
  dsimp only [P0, Fr] at hpc ⊢
  rw [frame_0x70_split (s0.sp - 112#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, arm64_norm]
  refine sepWPp_exists_left fun v0 => sepWPp_exists_left fun v1 =>
    sepWPp_exists_left fun v2 => sepWPp_exists_left fun v3 =>
    sepWPp_exists_left fun v4 => sepWPp_exists_left fun v5 =>
    sepWPp_exists_left fun v6 => sepWPp_exists_left fun v7 => ?_
  unfold dirAt RustHeap.vecOf RustHeap.vecAt
  simp only [sepExists_sepConj_left]
  refine sepWPp_exists_left fun changedCap => sepWPp_exists_left fun changedPtr => ?_
  rw [vecBuf_dirEntry_expose]
  simp only [sepConj_assoc]
  rw [← sepConj_assoc, sepConj_comm (vecHeader _ _ _ _) ⌜_⌝, sepConj_assoc]
  refine SepWPp.pure_left fun hcap_ok => ?_
  unfold vecHeader
  have hch_cases : x.dir.changed = [] ∨ (x.dir.changed ≠ [] ∧ 0 < x.dir.changed.length) := by
    cases x.dir.changed <;> simp
  rcases hch_cases with hch_nil | ⟨hch_ne, hch_pos⟩
  · have hrepack_dir0 :
        ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
          ((x.self + 16#64) ↦₆₄ 0#64) ∗
          RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
          (if changedCap = 0 then emp
           else A.live changedPtr (changedCap.toNat * 48) 8 ∗
             memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) ∗
          strRefAt (x.self + 24#64) x.dir.path ⊢
        dirAt A x.self x.dir := by
      unfold dirAt RustHeap.vecOf RustHeap.vecAt
      refine sepConj_mono ?_ (Entails.refl _)
      refine Entails.trans ?_ (Entails.sepExists_intro changedCap)
      refine Entails.trans ?_ (Entails.sepExists_intro changedPtr)
      rw [vecBuf_dirEntry_expose]
      unfold vecHeader
      simp only [hch_nil, List.length_nil, sepConj_assoc]
      have hpure_r :
          (x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
            ((x.self + 16#64) ↦₆₄ 0#64) ∗
            ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
            (if changedCap = 0 then emp
             else A.live changedPtr (changedCap.toNat * 48) 8 ∗
               memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48)) =
          ⌜(0 : Nat) ≤ changedCap.toNat ∧ changedCap.toNat * 48 < 2 ^ 63 ∧ changedPtr ≠ 0⌝ ∗
            ((x.self ↦₆₄ changedCap) ∗ ((x.self + 8#64) ↦₆₄ changedPtr) ∗
              ((x.self + 16#64) ↦₆₄ 0#64) ∗
              RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] ∗
              (if changedCap = 0 then emp
               else A.live changedPtr (changedCap.toNat * 48) 8 ∗
                 memRegion (changedPtr + 0#64) ((changedCap.toNat - 0) * 48))) := by ac_rfl
      rw [hpure_r]
      exact Entails.pure_right (by simpa [hch_nil] using hcap_ok) (Entails.refl _)
    have hpc0 : s0.pc = (blkPl_589).base := hpc
    refine seq_lscro_state (mid := (blkPl_589).base + 164#64) hcrl0 ?_
    simp only [hch_nil, List.length_nil]
    wp_steps
    apply SepWP.fold hrepack_dir0 (by sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    let st1 := stateOfLscro hcrl1
    have hpc1 : st1.pc = (blkPl_589).base + 164#64 := by dsimp only [st1, stateOfLscro]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfLscro, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, calleeSavedVRegs, wp_norm, arm64_norm])
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    refine SepWPp.perm
      (step_miss_tail (w0 := w0) (w1 := w1) (wTail := wTail)
        hC hpan hRO hPath hIoCall hFs hstk112 hfull halign
        hname_lt hdir_lt hpOk hpth_len_lt hcrl1 hpc1 hrun1 hsp1_al hsp1 hhcs1
        hfs1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
        (fun _ hm => False.elim (List.not_mem_nil (hch_nil ▸ hm))))
      (by simp only [wp_norm, arm64_norm]; sep_frame)
  · have hch_lt48 : x.dir.changed.length * 48 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 48 hcap_ok.1) hcap_ok.2.1
    have hch_lt63 : x.dir.changed.length < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right _ (by decide : 0 < 48)) hch_lt48
    have hch_ne0 : (BitVec.ofNat 64 x.dir.changed.length == 0#64) = false :=
      ofNat_beq_zero_false hch_pos (lt_pow64_of_lt_pow63 hch_lt63)
    have hx24_init :
        (BitVec.ofNat 64 x.dir.changed.length + (BitVec.ofNat 64 x.dir.changed.length <<< 1)) <<< 4 =
          BitVec.ofNat 64 (48 * x.dir.changed.length) :=
      setup_x24_48_eq x.dir.changed.length
    have hpc0 : s0.pc = (blkPl_589).base := hpc
    refine seq_lscro_state (mid := (blkPl_589).base + 80#64) hcrl0 ?_
    wp_steps
    apply SepWP.fold (Entails.refl (vecHeader x.self changedCap changedPtr x.dir.changed.length))
      (by unfold vecHeader; sep_frame)
    apply SepWP.fold (Entails.refl (savedRegsAt (s0.sp - 112#64) s0))
      (by unfold savedRegsAt; simp only [wp_norm, arm64_norm]; sep_frame)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcrl1
    let st1 := stateOfLscro hcrl1
    have harr_emp : RustHeap.arrayAt (dirEntryAt A) 48 changedPtr [] = emp := rfl
    rw [← emp_sepConj (RustHeap.arrayAt (dirEntryAt A) 48 changedPtr x.dir.changed),
        ← harr_emp]
    have hpc1 : st1.pc = (blkPl_589).base + 80#64 := by dsimp only [st1, stateOfLscro]; wp_norm_lhs
    have hrun1 : st1.status = ExecStatus.Running := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hsp1_al : st1.spAligned = true := by simpa only [st1, stateOfLscro, State.spAligned, wp_norm, arm64_norm] using hsp_sub_al
    have hsp1 : st1.sp = s0.sp - 112#64 := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hhcs1 : HighCalleeSaved s0 st1 :=
      (HighCalleeSaved.refl s0).of_steps
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, wp_norm, arm64_norm])
        (by simp only [st1, stateOfLscro, calleeSavedVRegs, wp_norm, arm64_norm])
    have hfs1 : st1.fs.files = s0.fs.files := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have htr1 : st1.trace = s0.trace := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx19_1 : st1.readReg64 .x19 = x.ret := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx20_1 : st1.readReg64 .x20 = BitVec.ofNat 64 x.name.length := by simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    have hx21_1 : st1.readReg64 .x21 = x.self := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx22_1 : st1.readReg64 .x22 = x.nameA := by simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx23_1 : st1.readReg64 .x23 = changedPtr + BitVec.ofNat 64 (48 * ([] : List (List (BitVec 8) × List (BitVec 8))).length) + 40#64 := by
      simp only [st1, stateOfLscro, wp_norm, arm64_norm, *]
    have hx24_1 : st1.readReg64 .x24 = BitVec.ofNat 64 (48 * x.dir.changed.length) := by
      simp only [st1, stateOfLscro, wp_norm, arm64_norm]
    refine SepWPp.perm
      (step_loop (cstk := cstk) (changedCap := changedCap) (changedPtr := changedPtr)
        (Extra := dirGetRoBundlePlaced w0 w1 wTail)
        hC hpan hRO hBcmp hFs hcstk_ext hstk112 hfull halign hname_lt hcap_ok
        (fun sm hpcm hrunm hsp_alm hspm hhcsm hcrlm hfsm htrm hx19m hx20m hx21m hx22m hall_ne =>
          step_miss_tail (w0 := w0) (w1 := w1) (wTail := wTail)
            hC hpan hRO hPath hIoCall hFs hstk112 hfull halign
            hname_lt hdir_lt hpOk hpth_len_lt hcrlm hpcm hrunm hsp_alm hspm hhcsm
            hfsm htrm hx19m hx20m hx21m hx22m hall_ne)
        x.dir.changed [] st1 hch_ne rfl (fun _ hm => False.elim (List.not_mem_nil hm))
        hcrl1 hpc1 hrun1 hsp1_al hsp1 hhcs1 hfs1 htr1
        hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1)
      (by simp only [List.length_nil, Nat.mul_zero, BitVec.add_zero,
            wp_norm, arm64_norm]; sep_frame)

theorem dirGet_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596) (pathSpecPlaced A pathStk))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A stk) := by
  have hPath589 : subroutine_ok (lsProg_589 H) (lsmpl.base 596) (pathSpecPlaced A pathStk) :=
    ls_transfer_lscro (callerProg := lsProg_589 H) (calleeProg := pathProg) (i := 589) (j := jPath)
      hPath (by decide) hjPath hjPath_unmut
  have hRead589 : subroutine_ok (lsProg_589 H) (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)) :=
    ls_transfer_lscro (callerProg := lsProg_589 H) (calleeProg := readProg) (i := 589) (j := jRead)
      hRead (by decide) hjRead hjRead_unmut
  exact dirGet_placed_ok_of_ioCall hC hpan hRO hBcmp hPath589
    (step_read_file_call hRead589) hFs hstk hpathLen

theorem dirGet_placed_caller_ok_of_deps [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {A : RustAlloc} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596) (pathSpecPlaced A pathStk))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A stk) :=
  ls_transfer_lscro (callerProg := callerProg) (calleeProg := lsProg_589 H) (i := i) (j := 589)
    (dirGet_placed_ok_of_deps hpathLen hC hpan hRO hBcmp
      hjPath hjPath_unmut hPath hjRead hjRead_unmut hRead hFs hstk) hi

end CryptoVerification.SignalSession.Cli.Get.PlacedHelpers

namespace CryptoVerification.SignalSession.Cli.Get

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession
open CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.Placed
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.Store.PlacedCommon

/-- `Dir::get` satisfies `dirGetSpecPlaced rd pathOk A stk` on Block 589 under `[LibsignalPlacement]`. -/
theorem dirGet_placed_ok_of_deps [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596) (pathSpecPlaced A pathStk))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk) :
    subroutine_ok (lsProg_589 H) (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A stk) :=
  PlacedHelpers.dirGet_placed_ok_of_deps hpathLen hC hpan hRO hBcmp
    hjPath hjPath_unmut hPath hjRead hjRead_unmut hRead hFs hstk

/-- Caller-transferable `[LibsignalPlacement]` `Dir::get` contract for any block `< 619`. -/
theorem dirGet_placed_caller_ok_of_deps [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    {A : RustAlloc} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {pathStk readStk stk : Nat}
    (hpathLen : ∀ p, pathOk p → p.length < 2 ^ 32)
    (hC : AllocContractsXCliPlaced A H)
    (hpan : CliPanicHooksPlaced H)
    (hRO : HookSat H memcpyName SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hBcmp : HookSat H cliBcmpName cliBcmpSpec)
    {pathProg : Program} {jPath : Nat} [IsLsBlockProg pathProg jPath H]
    (hjPath : jPath < 619 := by decide)
    (hjPath_unmut : (jPath ∈ libsignalMutatedBlocks) = false := by decide)
    (hPath : subroutine_ok pathProg (lsmpl.base 596) (pathSpecPlaced A pathStk))
    {readProg : Program} {jRead : Nat} [IsLsBlockProg readProg jRead H]
    (hjRead : jRead < 619 := by decide)
    (hjRead_unmut : (jRead ∈ libsignalMutatedBlocks) = false := by decide)
    (hRead : subroutine_ok readProg (lsρ lsReadFileSym)
      (StoreKit.withLsCodeRoLoaded lsmpl (readFileSpecPlaced rd pathOk A readStk)))
    (hFs : TraceFsSound (lsProg_589 H))
    (hstk : 0x70 + max (max pathStk readStk) extHookStack ≤ stk)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 589)
      (dirGetSpecPlaced rd pathOk A stk) :=
  PlacedHelpers.dirGet_placed_caller_ok_of_deps hpathLen hC hpan hRO hBcmp
    hjPath hjPath_unmut hPath hjRead hjRead_unmut hRead hFs hstk hi

end CryptoVerification.SignalSession.Cli.Get
