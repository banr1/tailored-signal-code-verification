/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFinishFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stepping and Result-Relocation Helpers for `segFinish_ok`

Basic-block `SepWP` stepping lemmas for `+0xe88..+0xf9c` and separation-logic relocation of
`apiEncResultAt A (sp + 0x370#64) (.ok m)` into `ResStaged`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

macro "messageEncryptFinish_fetches " b:term:max H:term:max hfn:ident k0:num len:num : tactic =>
  `(tactic| messageEncrypt_code_fetches_from CryptoVerification.libsignalSessionCode segFinishBin $b $H
    $hfn 0x3cbd8 $k0 $len)

/-! ## Stepping Lemmas (`+0xe88..+0xf9c`) -/

set_option maxHeartbeats 800000 in
theorem finish_stage_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp cap w0 w1 w2 w3 : BitVec 64} {b469 : BitVec 8}
    {bws dws : List (BitVec 64)}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hcap : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xe88#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xef0#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗
        words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
        words64At (sp + 0x390#64) bws ∗
        ((sp + 0x469#64) ↦₈ b469) ∗
        words64At (sp + 0x9d0#64) dws)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w2 ∧
        sf.readReg64 .x22 = w0 ∧
        sf.readReg64 .x23 = w3 ∧
        sf.readReg64 .x26 = sp + 0x9d0#64 ∧
        sf.readReg64 .x27 = w1 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗
          words64At (sp + 0x370#64) [w0, w1, w2, w3] ∗
          words64At (sp + 0x390#64) bws ∗
          ((sp + 0x469#64) ↦₈ 0#8) ∗
          words64At (sp + 0x9d0#64) bws)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_0x3cbd8
  have hne : (cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap
  have hne' : cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3720 104
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  rw [words64At_27 (s.sp + 0x390#64) hbws,
      words64At_27 (s.sp + 0x9d0#64) hdws]
  simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  refine ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, hx26, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [words64At_27 (s.sp + 0x9d0#64) hbws]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem finish_dropSs_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hdrop : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xef0#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xef8#64) s
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_0x3cbd8
  have hdrop' := dropSs_ok_at b C A ctl abs hdrop
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3824 8
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dropSs (sp := s.sp) (entry + 3832#64) hdrop' rfl
    (F := (s.sp + 80#64) ↦₆₄ (s.sp + 296#64))
    (by ac_rfl)
    rfl (by dsimp only [State.setPC, State.writeReg64, State.pc]; bv_omega)
    hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, hx22_sf, hx23_sf, _, _, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx22_sf hx23_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx22_sf, hx23_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

theorem finish_prev_zero_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp prevPtr : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xef8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xf58#64) s
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_0x3cbd8
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3832 8
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3900 28
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem finish_prev_nz_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp prevCap prevPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xef8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xf58#64) s
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64) ∗
       A.pool ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24) ∗
       stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_0x3cbd8
  have hdealloc := dealloc_ok_at b C A ctl abs hA encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - 0x3cbd8)) rfl
  have hmul24 := mul24_shift_toNat hcap_lt
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3832 8
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3900 28
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dealloc (sp := s.sp) (entry + 3928#64) hdealloc rfl
    (F := ((s.sp + 272#64) ↦₆₄ prevCap) ∗ ((s.sp + 280#64) ↦₆₄ prevPtr) ∗ ((s.sp + 288#64) ↦₆₄ 0#64))
    (by ac_rfl)
    rfl hmul24 rfl rfl hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, hx22_sf, hx23_sf, _, _, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx22_sf hx23_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx22_sf, hx23_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

set_option maxHeartbeats 800000 in
theorem finish_copyAtF58_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {sp w0 : BitVec 64}
    {bws dws : List (BitVec 64)} {s : State}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hw0_ne : (w0 + 2#64 == 0#64) = false)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0xf58#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx22 : s.readReg64 .x22 = w0)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName + 0x5f8#64) s
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws)
      (fun sf P_f =>
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        sf.readReg64 .x22 = w0 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) bws)) := by
  subst hsp
  have hfn := libsignalSessionCode_fnOff_0x3cbd8
  have hw0_ne' : w0 + 2#64 ≠ 0#64 := beq_eq_false_iff_ne.mp hw0_ne
  messageEncryptFinish_fetches b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 3928 72
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encryptWithStoresName = entry
  examples_hide_fetches
  rw [words64At_27 (s.sp + 0x9d0#64) hbws,
      words64At_27 (s.sp + 0x4a0#64) hdws]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  refine ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, hx28, hx22, rfl, rfl, rfl, rfl, ?_⟩
  rw [words64At_27 (s.sp + 0x4a0#64) hbws]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

/-! ## Relocation of `apiEncResultAt` to `ResStaged` -/

def RelocBytes (f : BitVec 64 → BitVec 64) (n : Nat) (F : List (BitVec 8) → SepProp)
    (b : BitVec 64) : SepProp :=
  ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (f b ↦ₛ bs) ∗ F bs

def Reloc (f : BitVec 64 → BitVec 64) (n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∃ F : List (BitVec 8) → SepProp, ∀ b, (P b ⊢ RelocBytes f n F b) ∧ (RelocBytes f n F b ⊢ P b)

namespace Reloc

theorem of_eq {f : BitVec 64 → BitVec 64} {n : Nat} {P Q : BitVec 64 → SepProp}
    (h : Reloc f n P) (e : ∀ b, Q b = P b) : Reloc f n Q := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun b => by rw [e b]; exact hF b⟩

theorem bytes (f : BitVec 64 → BitVec 64) (cs : List (BitVec 8)) :
    Reloc f cs.length (fun b => f b ↦ₛ cs) := by
  refine ⟨fun bs => ⌜bs = cs⌝, fun b => ⟨?_, ?_⟩⟩
  · unfold RelocBytes
    exact Entails.sepExists_right cs (Entails.pure_right rfl
      (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
        (sepConj_mono_right (Entails.pure_right_only rfl (Entails.refl _)))))
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun _ => ?_
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) (Entails.pure_left fun h => ?_)
    subst h
    exact Entails.refl _

theorem pt64 (f : BitVec 64 → BitVec 64) (v : BitVec 64) : Reloc f 8 (fun b => f b ↦₆₄ v) :=
  (bytes f (unpack64 v)).of_eq fun _ => pointsTo64_eq_pointsToBytes _ v

theorem pt32 (f : BitVec 64 → BitVec 64) (v : BitVec 32) : Reloc f 4 (fun b => f b ↦₃₂ v) :=
  (bytes f (unpack32 v)).of_eq fun _ => pointsTo32_eq_pointsToBytes _ v

theorem pt8 (f : BitVec 64 → BitVec 64) (v : BitVec 8) : Reloc f 1 (fun b => f b ↦₈ v) :=
  (bytes f [v]).of_eq fun _ => (pointsToBytes_singleton _ v).symm

theorem region (f : BitVec 64 → BitVec 64) (k : Nat) (hk : k ≤ 2 ^ 64 := by decide) :
    Reloc f k (fun b => memRegion (f b) k) := by
  refine ⟨fun _ => emp, fun b => ?_⟩
  unfold RelocBytes
  simp only [memRegion_eq_exists_bytes _ _ hk, sepConj_emp]
  exact ⟨Entails.refl _, Entails.refl _⟩

theorem frameR {f : BitVec 64 → BitVec 64} {n : Nat} {P : BitVec 64 → SepProp}
    (h : Reloc f n P) (K : SepProp) : Reloc f n (fun b => P b ∗ K) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨fun bs => F bs ∗ K, fun b => ⟨?_, ?_⟩⟩
  · refine Entails.trans (sepConj_mono_left (hF b).1) ?_
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepConj_assoc]
    exact Entails.refl _
  · refine Entails.trans ?_ (sepConj_mono_left (hF b).2)
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepConj_assoc]
    exact Entails.refl _

theorem frameL {f : BitVec 64 → BitVec 64} {n : Nat} {P : BitVec 64 → SepProp}
    (h : Reloc f n P) (K : SepProp) : Reloc f n (fun b => K ∗ P b) :=
  (h.frameR K).of_eq fun _ => sepConj_comm _ _

theorem sepEx {α : Type} {f : BitVec 64 → BitVec 64} {n : Nat} {P : α → BitVec 64 → SepProp}
    (h : ∀ x, Reloc f n (P x)) : Reloc f n (fun b => ∃∗ x, P x b) := by
  have hF := fun x => Classical.choose_spec (h x)
  refine ⟨fun bs => ∃∗ x, Classical.choose (h x) bs, fun b => ⟨?_, ?_⟩⟩
  · refine Entails.sepExists_elim fun x => Entails.trans (hF x b).1 ?_
    unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    exact sepConj_mono_right (sepConj_mono_right
      (Entails.sepExists_intro (P := fun y => Classical.choose (h y) bs) x))
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun x => Entails.trans ?_
      (Entails.trans (hF x b).2 (Entails.sepExists_intro (P := fun y => P y b) x))
    unfold RelocBytes
    exact Entails.sepExists_intro
      (P := fun bs => ⌜bs.length = n⌝ ∗ (f b ↦ₛ bs) ∗ Classical.choose (h x) bs) bs

theorem sep {f g : BitVec 64 → BitVec 64} {n m : Nat} {P Q : BitVec 64 → SepProp}
    (hP : Reloc f n P) (hQ : Reloc g m Q)
    (hg : ∀ b, g b = f b + BitVec.ofNat 64 n := by intro b; (try dsimp only) <;> bv_omega) :
    Reloc f (n + m) (fun b => P b ∗ Q b) := by
  obtain ⟨F, hF⟩ := hP
  obtain ⟨G, hG⟩ := hQ
  refine ⟨fun bs => F (bs.take n) ∗ G (bs.drop n), fun b => ⟨?_, ?_⟩⟩
  · refine Entails.trans (sepConj_mono (hF b).1 (hG b).1) ?_
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs2 => Entails.sepExists_elim fun bs1 => ?_
    refine Entails.trans (Entails.of_eq (Q := ⌜bs1.length = n⌝ ∗ ⌜bs2.length = m⌝ ∗
      (f b ↦ₛ bs1) ∗ (g b ↦ₛ bs2) ∗ F bs1 ∗ G bs2)) ?_
    refine Entails.pure_left fun h1 => Entails.pure_left fun h2 => ?_
    refine Entails.sepExists_right (bs1 ++ bs2)
      (Entails.pure_right (by rw [List.length_append, h1, h2]) ?_)
    rw [List.take_left' h1, List.drop_left' h1, pointsToBytes_append, h1, ← hg b]
    exact Entails.of_eq
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hl => ?_
    refine Entails.trans ?_ (sepConj_mono (hF b).2 (hG b).2)
    unfold RelocBytes
    have e : (f b ↦ₛ bs) = (f b ↦ₛ bs.take n) ∗ (g b ↦ₛ bs.drop n) := by
      conv_lhs => rw [← List.take_append_drop n bs]
      rw [pointsToBytes_append, List.length_take, Nat.min_eq_left (by omega), hg b]
    rw [e]
    dsimp only
    refine Entails.trans (Entails.of_eq (Q := ((f b ↦ₛ bs.take n) ∗ F (bs.take n)) ∗
      ((g b ↦ₛ bs.drop n) ∗ G (bs.drop n)))) ?_
    exact sepConj_mono
      (Entails.sepExists_right (bs.take n)
        (Entails.pure_right (by rw [List.length_take]; omega) (Entails.refl _)))
      (Entails.sepExists_right (bs.drop n)
        (Entails.pure_right (by rw [List.length_drop]; omega) (Entails.refl _)))

def vecU8Tail (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

theorem vecU8At_split_cap (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (a ↦₆₄ cap) ∗ vecU8Tail A a cap ptr bs := by
  simp only [vecU8At, vecHeader, vecU8Tail]
  ac_rfl

theorem vecU8TailR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Reloc (fun b => f b + 8#64) 16 (fun b => vecU8Tail A (f b) cap ptr bs) := by
  unfold vecU8Tail
  exact sep (pt64 (fun b => f b + 8#64) ptr)
    ((pt64 (fun b => f b + 16#64) (BitVec.ofNat 64 bs.length)).frameR _)

theorem vecU8AtR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Reloc f 24 (fun b => vecU8At A (f b) cap ptr bs) := by
  have h := (sep (pt64 f cap) (vecU8TailR A f cap ptr bs)).frameL
    ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝
  exact h.of_eq fun b => vecU8At_split_cap A (f b) cap ptr bs

theorem boxU8AtR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    Reloc f 16 (fun b => boxU8At A (f b) ptr bs) := by
  unfold boxU8At
  exact sep (pt64 f ptr) ((pt64 (fun b => f b + 8#64) (BitVec.ofNat 64 bs.length)).frameR _)

theorem optBoxU8AtR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (ptr : BitVec 64)
    (o : Option (List (BitVec 8))) :
    Reloc f 16 (fun b => optBoxU8At A (f b) ptr o) := by
  cases o with
  | none => exact sep (pt64 f 0#64) (region (fun b => f b + 8#64) 8)
  | some bs => exact boxU8AtR A f ptr bs

theorem vec32R (f : BitVec 64 → BitVec 64) (v : List.Vector (BitVec 8) 32) :
    Reloc f 32 (fun b => f b ↦ₛ v.toList) := by
  have h := bytes f v.toList
  rwa [List.Vector.toList_length] at h

def signalMessageTailAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8Tail A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x68#64) ↦₃₂ m.counter) ∗ ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_split_cap (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ⌜m.pqRatchet.length ≤ g.pqCap.toNat ∧ g.pqCap.toNat < 2 ^ 63 ∧ g.pqPtr ≠ 0⌝ ∗
      (a ↦₆₄ g.pqCap) ∗ signalMessageTailAt A g a m := by
  unfold signalMessageAt signalMessageTailAt
  rw [vecU8At_split_cap]
  ac_rfl

theorem signalMessageTailR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (g : SignalMessageGhost)
    (m : SignalMessage) :
    Reloc (fun b => f b + 8#64) 112 (fun b => signalMessageTailAt A g (f b) m) := by
  unfold signalMessageTailAt
  exact (sep (vecU8TailR A f g.pqCap g.pqPtr m.pqRatchet)
    (sep (boxU8AtR A (fun b => f b + 0x18#64) g.ctPtr m.ciphertext)
      (sep (boxU8AtR A (fun b => f b + 0x28#64) g.serPtr m.serialized)
        (sep (vec32R (fun b => f b + 0x38#64) m.senderRatchetKey.bytes)
          (sep (optBoxU8AtR A (fun b => f b + 0x58#64) g.addrPtr m.addresses)
            (sep (pt32 (fun b => f b + 0x68#64) m.counter)
              (sep (pt32 (fun b => f b + 0x6c#64) m.previousCounter)
                (sep (pt8 (fun b => f b + 0x70#64) m.messageVersion)
                  (region (fun b => f b + 0x71#64) 7))))))))).frameL _

theorem signalMessageAtR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (g : SignalMessageGhost)
    (m : SignalMessage) :
    Reloc f 120 (fun b => signalMessageAt A g (f b) m) := by
  have h := (sep (pt64 f g.pqCap) (signalMessageTailR A f g m)).frameL
    ⌜m.pqRatchet.length ≤ g.pqCap.toNat ∧ g.pqCap.toNat < 2 ^ 63 ∧ g.pqPtr ≠ 0⌝
  exact h.of_eq fun b => signalMessageAt_split_cap A g (f b) m

theorem optU32AtR (f : BitVec 64 → BitVec 64) (o : Option (BitVec 32)) :
    Reloc f 8 (fun b => optU32At (f b) o) := by
  cases o with
  | none => exact sep (pt32 f 0#32) (region (fun b => f b + 4#64) 4)
  | some v => exact sep (pt32 f 1#32) (pt32 (fun b => f b + 4#64) v)

theorem optKyberAtR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (ptr : BitVec 64)
    (o : Option KyberPayload) :
    Reloc f 24 (fun b => optKyberAt A (f b) ptr o) := by
  cases o with
  | none => exact sep (pt64 f 0#64) (region (fun b => f b + 8#64) 16)
  | some k =>
    exact sep (boxU8AtR A f ptr k.ciphertext)
      (sep (pt32 (fun b => f b + 0x10#64) k.preKeyId) (region (fun b => f b + 0x14#64) 4))

def preKeyMsgTailAt (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) : SepProp :=
  signalMessageTailAt A g.msg a m.message ∗ optU32At (a + 0x78#64) m.preKeyId ∗
    boxU8At A (a + 0x80#64) g.serPtr m.serialized ∗ optKyberAt A (a + 0x90#64) g.kyberPtr m.kyberPayload ∗
    ((a + 0xa8#64) ↦ₛ m.baseKey.bytes.toList) ∗
    ((a + 0xc8#64) ↦ₛ m.identityKey.publicKey.bytes.toList) ∗
    ((a + 0xe8#64) ↦₃₂ m.registrationId) ∗ ((a + 0xec#64) ↦₃₂ m.signedPreKeyId) ∗
    ((a + 0xf0#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0xf1#64) 7

theorem preKeyMsgAt_split_cap (A : RustAlloc) (g : PreKeyMsgGhost) (a : BitVec 64)
    (m : PreKeySignalMessage) :
    preKeyMsgAt A g a m =
      ⌜m.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗
      (a ↦₆₄ g.msg.pqCap) ∗ preKeyMsgTailAt A g a m := by
  unfold preKeyMsgAt preKeyMsgTailAt
  rw [signalMessageAt_split_cap]
  ac_rfl

theorem preKeyMsgTailR (A : RustAlloc) (g : PreKeyMsgGhost) (m : PreKeySignalMessage) :
    Reloc (fun b => b + 8#64) 240 (fun b => preKeyMsgTailAt A g b m) := by
  unfold preKeyMsgTailAt
  exact sep (signalMessageTailR A (fun b => b) g.msg m.message)
    (sep (optU32AtR (fun b => b + 0x78#64) m.preKeyId)
      (sep (boxU8AtR A (fun b => b + 0x80#64) g.serPtr m.serialized)
        (sep (optKyberAtR A (fun b => b + 0x90#64) g.kyberPtr m.kyberPayload)
          (sep (vec32R (fun b => b + 0xa8#64) m.baseKey.bytes)
            (sep (vec32R (fun b => b + 0xc8#64) m.identityKey.publicKey.bytes)
              (sep (pt32 (fun b => b + 0xe8#64) m.registrationId)
                (sep (pt32 (fun b => b + 0xec#64) m.signedPreKeyId)
                  (sep (pt8 (fun b => b + 0xf0#64) m.messageVersion)
                    (region (fun b => b + 0xf1#64) 7)))))))))

theorem signalMsgOkTailR (A : RustAlloc) (m : SignalMessage) :
    Reloc (fun b => b + 8#64) 240
      (fun b => (∃∗ g : SignalMessageGhost, signalMessageAt A g (b + 8#64) m) ∗
        memRegion (b + 0x80#64) 120) :=
  sep (sepEx fun g => signalMessageAtR A (fun b => b + 8#64) g m)
    (region (fun b => b + 0x80#64) 120)

end Reloc

theorem cap_add_two_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  bv_omega

theorem extract_ok_cm {A : RustAlloc} {a ret : BitVec 64} {m : CiphertextMessage}
    {mem : Memory} {R : SepProp}
    (hm : mem ⊨ apiEncResultAt A a (.ok m) ∗ R) :
    ∃ (w0 w1 w2 w3 : BitVec 64) (bws : List (BitVec 64)) (H : SepProp),
      bws.length = 27 ∧
      (w0 + 2#64 == 0#64) = false ∧
      ResStaged A ret (.ok m) [w0, w1, w2, w3] (unpack64List bws) H ∧
      (mem ⊨ words64At a [w0, w1, w2, w3] ∗ words64At (a + 0x20#64) bws ∗ H ∗ R) := by
  have hrel : ∃ (w0 : BitVec 64) (bs : List (BitVec 8)) (H : SepProp),
      (w0 + 2#64 == 0#64) = false ∧ bs.length = 240 ∧
      ((ret ↦₆₄ w0) ∗ ((ret + 8#64) ↦ₛ bs) ∗ H ⊢ apiEncResultAt A ret (.ok m)) ∧
      (mem ⊨ (a ↦₆₄ w0) ∗ ((a + 8#64) ↦ₛ bs) ∗ H ∗ R) := by
    cases m with
    | signalMessage sm =>
      obtain ⟨F, hF⟩ := Reloc.signalMsgOkTailR A sm
      have hm0 : mem ⊨ ((∃∗ g : SignalMessageGhost, signalMessageAt A g (a + 8#64) sm) ∗
          memRegion (a + 0x80#64) 120) ∗ ((a ↦₆₄ ctSignalTag) ∗ R) := by
        rw [apiEncResultAt] at hm
        have heq : (((a ↦₆₄ ctSignalTag) ∗
            (∃∗ g : SignalMessageGhost, signalMessageAt A g (a + 8#64) sm) ∗
            memRegion (a + 0x80#64) 120) ∗ R) =
          (((∃∗ g : SignalMessageGhost, signalMessageAt A g (a + 8#64) sm) ∗
            memRegion (a + 0x80#64) 120) ∗ ((a ↦₆₄ ctSignalTag) ∗ R)) := by ac_rfl
        rwa [← heq]
      have hm1 : mem ⊨ RelocBytes (fun b => b + 8#64) 240 F a ∗ ((a ↦₆₄ ctSignalTag) ∗ R) :=
        Satisfies.mono (sepConj_mono_left (hF a).1) hm0
      unfold RelocBytes at hm1
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
      obtain ⟨bs, hm1⟩ := hm1
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm1
      rcases hm1 with ⟨hbs, hm1⟩
      refine ⟨ctSignalTag, bs, F bs, by decide, hbs, ?_, ?_⟩
      · rw [apiEncResultAt]
        refine sepConj_mono_right (Entails.trans ?_ (hF ret).2)
        unfold RelocBytes
        exact Entails.sepExists_right bs (Entails.pure_right hbs (Entails.refl _))
      · have heq : (((a + 8#64) ↦ₛ bs) ∗ (F bs ∗ ((a ↦₆₄ ctSignalTag) ∗ R))) =
            ((a ↦₆₄ ctSignalTag) ∗ ((a + 8#64) ↦ₛ bs) ∗ F bs ∗ R) := by ac_rfl
        rwa [← heq]
    | preKeySignalMessage psm =>
      rw [apiEncResultAt, sepExists_sepConj_left, satisfies_sepExists] at hm
      obtain ⟨g, hm⟩ := hm
      obtain ⟨F, hF⟩ := Reloc.preKeyMsgTailR A g psm
      rw [Reloc.preKeyMsgAt_split_cap, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm
      rcases hm with ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hm⟩
      have hm0 : mem ⊨ Reloc.preKeyMsgTailAt A g a psm ∗ ((a ↦₆₄ g.msg.pqCap) ∗ R) := by
        have heq : ((a ↦₆₄ g.msg.pqCap) ∗ (Reloc.preKeyMsgTailAt A g a psm ∗ R)) =
            (Reloc.preKeyMsgTailAt A g a psm ∗ ((a ↦₆₄ g.msg.pqCap) ∗ R)) := by ac_rfl
        rwa [← heq]
      have hm1 : mem ⊨ RelocBytes (fun b => b + 8#64) 240 F a ∗ ((a ↦₆₄ g.msg.pqCap) ∗ R) :=
        Satisfies.mono (sepConj_mono_left (hF a).1) hm0
      unfold RelocBytes at hm1
      rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
      obtain ⟨bs, hm1⟩ := hm1
      rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hm1
      rcases hm1 with ⟨hbs, hm1⟩
      refine ⟨g.msg.pqCap, bs,
        ⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗ F bs,
        cap_add_two_beq_zero_eq_false hcap_lt, hbs, ?_, ?_⟩
      · rw [apiEncResultAt]
        refine Entails.trans ?_ (Entails.sepExists_intro g)
        rw [Reloc.preKeyMsgAt_split_cap]
        have heq1 : ((ret ↦₆₄ g.msg.pqCap) ∗ ((ret + 8#64) ↦ₛ bs) ∗
            (⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗ F bs)) =
            (⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗
              (ret ↦₆₄ g.msg.pqCap) ∗ (((ret + 8#64) ↦ₛ bs) ∗ F bs)) := by ac_rfl
        rw [heq1]
        refine sepConj_mono_right (sepConj_mono_right (Entails.trans ?_ (hF ret).2))
        unfold RelocBytes
        exact Entails.sepExists_right bs (Entails.pure_right hbs (Entails.refl _))
      · have heq : ((a ↦₆₄ g.msg.pqCap) ∗ ((a + 8#64) ↦ₛ bs) ∗
            (⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗ F bs) ∗ R) =
            (⌜psm.message.pqRatchet.length ≤ g.msg.pqCap.toNat ∧ g.msg.pqCap.toNat < 2 ^ 63 ∧ g.msg.pqPtr ≠ 0⌝ ∗
              (((a + 8#64) ↦ₛ bs) ∗ (F bs ∗ ((a ↦₆₄ g.msg.pqCap) ∗ R)))) := by ac_rfl
        rw [heq, satisfies_pure_sepConj]
        exact ⟨⟨hcap_le, hcap_lt, hptr_nz⟩, hm1⟩
  rcases hrel with ⟨w0, bs, H, hw0_ne, hbs_len, hent, hm_bs⟩
  obtain ⟨ws30, hws30_len, rfl⟩ := exists_unpack64List 30 (by omega : bs.length = 8 * 30)
  rcases ws30 with _ | ⟨w1, _ | ⟨w2, _ | ⟨w3, bws⟩⟩⟩ <;> try (simp at hws30_len; done)
  have hbws : bws.length = 27 := by simp at hws30_len; omega
  have hsplit : ∀ b : BitVec 64,
      (b ↦₆₄ w0) ∗ ((b + 8#64) ↦ₛ unpack64List (w1 :: w2 :: w3 :: bws)) =
        words64At b [w0, w1, w2, w3] ∗ words64At (b + 0x20#64) bws := fun b => by
    rw [← words64At_eq_pointsToBytes]
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine ⟨w0, w1, w2, w3, bws, H, hbws, hw0_ne, ?_, ?_⟩
  · refine ⟨by nofun, rfl, by simp [hbws], ?_⟩
    rw [← words64At_eq_pointsToBytes (ret + 0x20#64), ← sepConj_assoc, ← hsplit ret, sepConj_assoc]
    exact hent
  · rw [← sepConj_assoc (words64At a _), ← hsplit a, sepConj_assoc]
    exact hm_bs

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFinish
