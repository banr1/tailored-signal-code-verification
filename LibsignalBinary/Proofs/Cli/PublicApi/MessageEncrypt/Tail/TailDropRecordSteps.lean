/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.Common
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.Common
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFetch
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecordSteps
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.RegChain

/-!
# Basic-Block Step and Frame Weakening Lemmas for T1 Record Drop (`+0x46c..+0x564`)

Proves `SepWP` basic-block steppers (in normal and trap modes) and representation weakening lemmas
for `sessionRecordAt`, `otrAt`, and `vecU8At` along the T1 record-drop path.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.libsignalSessionCode_fnOff_dropSsLocal2 :
    libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name = (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]") := by
  exact (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]")

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropSs_ok_at_trap (b : BitVec 64) (C : Crypto) (A : RustAlloc)
    (abs : String → Option (State → State))
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A (trTrapExterns C abs)) :
    subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      (FromRecordCallees.dropSessionStructureLocal2Spec A) := by
  have heq :
      (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
        (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name := by
    unfold trTrapProgAt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.libsignalSessionCode_fnOff_dropSsLocal2]
    bv_omega
  rw [heq]
  exact hdrop

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropSs_ok_at (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      (FromRecordCallees.dropSessionStructureLocal2Spec A) := by
  have heq :
      (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + bv% ((2^64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#3]" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) =
        (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.dropSessionStructureLocal2Name := by
    unfold tripleRatchetProgAt
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.libsignalSessionCode_fnOff_dropSsLocal2]
    bv_omega
  rw [heq]
  exact hdrop

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordDropSs_sepWP_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2OkExt b A (trTrapExterns C abs))
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hdrop' := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropSs_ok_at_trap b C A abs hdrop
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1372 8
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dropSs (sp := s.sp) (entry + bv% (1380)) hdrop' rfl
    (F := (s.sp + 80#64) ↦₆₄ (s.sp + 296#64))
    (by ac_rfl)
    rfl (by dsimp only [State.setPC, State.writeReg64, State.pc])
    hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

/-! ## Session state cap unfolding and `ADDS XZR, X8, #1` helper -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordDropSs_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {G : SessionGhost} {st : SessionState (List (BitVec 8))}
    (hdrop : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hdrop' := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropSs_ok_at b C A ctl abs hdrop
  messageEncryptTail_fetches_cli b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 1372 8
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dropSs (sp := s.sp) (entry + bv% (1380)) hdrop' rfl
    (F := (s.sp + 80#64) ↦₆₄ (s.sp + 296#64))
    (by ac_rfl)
    rfl (by dsimp only [State.setPC, State.writeReg64, State.pc])
    hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_none_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold noneCap
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1356 16
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_none_sepWP_trap (C := C) (abs := abs) hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_some_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1356 16
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_some_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_some_sepWP_trap (C := C) (abs := abs) hcap_lt hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_none_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  unfold noneCap
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1160 20
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64} {b469 : BitVec 8}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x564#64) s
      (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_none_sepWP_trap (C := C) (abs := abs) hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_some_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hcmn := cap_add_one_beq_zero_eq_false hcap_lt
  have hcmn_ne := cap_add_one_ne_zero hcap_lt
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1160 20
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

/-! ## Stepper lemmas from `+0x46c` (`1132`) -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_some_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp cap : BitVec 64} {b469 : BitVec 8}
    (hcap_lt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x55c#64) s
      (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ b469))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x128#64) ↦₆₄ cap) ∗ ((sp + 0x469#64) ↦₈ 0#8))) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordAfterDealloc_some_sepWP_trap (C := C) (abs := abs) hcap_lt hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_none_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      ((sp + 0x469#64) ↦₈ 0#8)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x469#64) ↦₈ 0#8)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1132 8
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_none_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      ((sp + 0x469#64) ↦₈ 0#8)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = ((sp + 0x469#64) ↦₈ 0#8)) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_none_sepWP_trap (C := C) (abs := abs) hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_zero_sepWP_trap
    {b : BitVec 64} {C : Crypto}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1132 16
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  apply SepWP.done (by rfl) (by exact hrun)
  exact ⟨rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by ac_rfl⟩

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_zero_sepWP
    {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x54c#64) s
      (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ 0#64) ∗ ((sp + 0x469#64) ↦₈ 1#8))) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_zero_sepWP_trap (C := C) (abs := abs) hpc hrun hsp_al hsp)

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_nz_sepWP_trap
    {b : BitVec 64} {C : Crypto} {A : RustAlloc}
    {abs : String → Option (State → State)}
    {s : State} {sp pqCap pqPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hpq_nz : pqCap ≠ 0#64)
    (hpc : s.pc = (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64) s
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  subst hsp
  have hfn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.libsignalSessionCode_fnOff_sym_3caf4
  have hdealloc := dealloc_ok_at_trap b C A abs hA CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName (num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "libsignal_cli_ratchet::encrypt"))
    (by rw [hfn]; exact (ls_stub% "__rustc::__rust_dealloc").symm)
  messageEncryptTail_fetches_cli b (Rust.withPanics (trTrapExterns C abs)) hfn 1132 28
  generalize_entry (trTrapProgAt b C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  wp_steps
  refine sepWP_call_dealloc (sp := s.sp) (entry + bv% (1160)) hdealloc rfl
    (F := ((s.sp + 648#64) ↦₆₄ pqCap) ∗ ((s.sp + 656#64) ↦₆₄ pqPtr) ∗ ((s.sp + 1129#64) ↦₈ 1#8))
    (by ac_rfl)
    rfl rfl rfl rfl hrun hsp_al rfl ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs_sf htr_sf
  obtain ⟨hx19_sf, _, hx21_sf, _, hx23_sf, _, hx25_sf, hx26_sf, hx27_sf, hx28_sf, hx29_sf, hvregs_sf⟩ := hcs_sf
  dsimp only [State.setPC, State.writeReg64, State.sp, State.trace] at hsp_sf htr_sf
  simp only [State.readReg64_setPC, State.readReg64_writeReg64, Reg.fp, Reg.gpr.injEq,
    reduceCtorEq, BitVec.reduceEq, or_self, ite_false] at hx19_sf hx21_sf hx23_sf hx25_sf hx26_sf hx27_sf hx28_sf hx29_sf
  have hsp_al_sf : sf.spAligned = true := by
    unfold State.spAligned at hsp_al ⊢
    rw [hsp_sf]; exact hsp_al
  apply SepWP.done hpc_sf hrun_sf
  refine ⟨hsp_sf, hsp_al_sf, htr_sf, hx19_sf, hx21_sf, hx23_sf, hx25_sf, hx26_sf,
    hx27_sf, hx28_sf, hx29_sf, hvregs_sf, ?_⟩
  ac_rfl

/-! ## Weakening lemmas for `sessionRecordAt`, `otrAt`, and `vecU8At` -/

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_nz_sepWP
    {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    {s : State} {sp pqCap pqPtr : BitVec 64}
    (hA : AllocHooks A abs)
    (hpq_nz : pqCap ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x46c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x488#64) s
      (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        A.pool ∗ A.live pqPtr pqCap.toNat 1 ∗ memRegion pqPtr pqCap.toNat ∗ stackAt sp allocHookStack)
      (fun sf P_f =>
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x288#64) ↦₆₄ pqCap) ∗ ((sp + 0x290#64) ↦₆₄ pqPtr) ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗ A.pool ∗ stackAt sp allocHookStack)) := by
  exact SepWP.of_trapsOnly (trapsOnly_trTrap_kit b C ctl abs) (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecord_otr_nz_sepWP_trap (C := C) (abs := abs) hA hpq_nz hpc hrun hsp_al hsp)

open CryptoVerification.LibsignalPublicApi.StoreKit

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordAt55c_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x55c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
  change s.mem ⊨
    (scratch sp ∗
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateAt A (sp + 0x128#64) G st ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  rw [hscr_eq] at hmem
  let F := S50 ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
    memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
    encSavedRegs s0.sp s0 ∗ R
  have hmem_re : s.mem ⊨
      (((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
        A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F := by
    have heq :
        (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G st ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ sessionStateAt A (sp + 0x128#64) G st ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) := by
      unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
      change (((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G st ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
        stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R) = _
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordDropSs_sepWP (G := G) (st := st) env.callees.dropSs hpc hrun hsp_al hsp
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hsp1, hsp1_al, htr1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64 := by
    rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
  refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
    hsteps1.frozenLoaded hfl, hsteps1.symtab_eq.trans hsym, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
  have hmf2 : s1.mem ⊨
      (S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
       memRegion (sp + 0x128#64) 0x158 ∗
       memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
    have heq :
        ((((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          A.pool ∗ stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack) ∗ F) =
        ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon
      change _ = ((S50 ∗ ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
         memRegion (sp + 0x128#64) 0x158 ∗
         memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          nowAt s0.sp x.now ∗ CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (x.draws S answers) ∗ logOff img ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool) ∗ R))
      rw [stackAt_encSubStack_dropSs sp]
      dsimp only [F]
      ac_rfl
    rwa [← heq]
  have hmf3 := Satisfies.mono (sepConj_mono_left hscr_weaken) hmf2
  have heq2 :
      (memRegion sp 0x58 ∗
       (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
        encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
      ((memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
  rwa [← heq2]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordCur_ok (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (b469 : BitVec 8)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x54c#64) (tailRegs w0 w1 w2)
      (fun sp => scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hfl, hsym, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads] at hpc
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R at hmem
  unfold sessionRecordAt at hmem
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  have h130 : sp + 0x110#64 + 0x20#64 = sp + 0x130#64 := by bv_omega
  rcases g with ⟨prevCap, prevPtr, _ | G⟩ <;> rcases hcur : rec.currentSession with _ | sess
  · rw [hcur, h128, h130] at hmem
    rcases scratch_has_50 hscr sp with ⟨S50, hscr_eq, hscr_weaken⟩
    have hscr_mem : scratch sp ⊢ memRegion sp 0x58 := hscr_eq ▸ hscr_weaken
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x130#64) 336 ∗ memRegion (sp + 0x280#64) 0x1e9 ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ (((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336)) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗ F) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_none_sepWP (b469 := b469) hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem_re hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x564#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions.tailFreePrevSessions_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf2 : s1.mem ⊨
        (scratch sp ∗
          (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
        (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x128#64) ↦₆₄ noneCap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗ F) =
          ((scratch sp ∗
            (((sp + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x130#64) 336) ∗
            (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8))) ∗
           (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]; ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono hscr_mem
        (sepConj_mono (cur_none_weaken sp) (flag_memRegion_weaken sp 0#8)))) hmf2
    have heq2 :
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea) ∗
         (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    have hfalse : s.mem ⊨ ⌜False⌝ ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗ ⌜False⌝) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜False⌝ ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hfalse
    exact hfalse.1.elim
  · rw [hcur] at hmem
    dsimp only at hmem
    unfold sessionStateReprAt at hmem
    rw [h128, sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state] at hmem
    let P_sess_pure : Prop :=
      PendingRel G.pending sess.pendingPreKey ∧ KyberRel G.kyber sess.pendingKyberPreKey ∧
        G.alice.bytes = sess.aliceBaseKey ∧
        G.regIds.take 4 = leBytes 4 sess.remoteRegistrationId.toNat ∧
        (G.regIds.drop 4).take 4 = leBytes 4 sess.localRegistrationId.toNat
    let P_ik_pure : Prop :=
      G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0
    let F := scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      ⌜P_ik_pure⌝ ∗ sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R
    have hmem_re : s.mem ⊨ ⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R))) := by
      have heq :
          ((scratch sp ∗
            (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
              (⌜P_sess_pure⌝ ∗
                (⌜P_ik_pure⌝ ∗
                  (((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗
                    sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state)))) ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) =
          (⌜P_sess_pure⌝ ∗ (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ b469)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)))) := by
        dsimp only [P_sess_pure, P_ik_pure]; ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨_, h_ik, hmem2⟩
    have hcap_lt : G.localIk.cap.toNat < 2 ^ 63 := h_ik.2.1
    have hwp := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.dropRecordCur_some_sepWP (b469 := b469) hcap_lt hpc hrun hsp_al hsp
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr.segExit_of_sepWP hmem2 hwp ?_
    intro s1 P_f hsteps1 hpc1 hrun1 hmf1
      ⟨hsp1, hsp1_al, htr1, hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
    subst hPf
    have hpc1' : s1.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x55c#64 := by
      rw [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon.entryOf_encEntry (C := C) (ctl := ctl) (abs := abs) env.loads, hpc1]
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps.tailDropRecordAt55c_ok env x R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H scratch hscr
      prevCap prevPtr G sess.state hm1 hst ?_
    refine ⟨hpc1', ⟨hrun1, hsp1, hsp0_al, hsp1_al, by reg_chain, by reg_chain,
      hsteps1.frozenLoaded hfl, by reg_chain, hvregs1.trans hvregs⟩, by reg_chain, hstack_le, ?_⟩
    have hmf1' : s1.mem ⊨ ⌜P_ik_pure⌝ ∗
        ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
          (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
            sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
            memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
            encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
            CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
      rw [satisfies_pure_sepConj]
      exact ⟨h_ik, hmf1⟩
    have hmf2 : s1.mem ⊨
        (memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
        (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by
      have heq :
          (⌜P_ik_pure⌝ ∗
            ((((sp + 0x128#64) ↦₆₄ G.localIk.cap) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
              (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
                sessionStateAfterLocalIk A (sp + 0x128#64) G sess.state ∗
                memRegion (sp + 0x280#64) 0x1e9 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
                encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
                CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R))) =
          ((memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
           (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
             sessionStateAt A (sp + 0x128#64) G sess.state ∗
             pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) := by
        rw [sessionStateAt_unfold_cap A (sp + 0x128#64) G sess.state]
        dsimp only [P_ik_pure]
        ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (flag_memRegion_weaken sp 0#8)) hmf2
    have heq2 :
        (memRegion (sp + 0x280#64) 0x1ea ∗
         (scratch sp ∗ vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
           sessionStateAt A (sp + 0x128#64) G sess.state ∗
           pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R)) =
        ((scratch sp ∗
          vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
          sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (x.draws S answers) s0 ∗ R) := by ac_rfl
    rwa [← heq2]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailDropRecordSteps
