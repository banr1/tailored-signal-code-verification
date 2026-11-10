/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordClonePV1
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.SpqrV1.M4.RecordCloneExtSteps
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchClone
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneAssemble
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeys
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneAssemble
import ProofLib.RegChain

/-!
# 4K-Stack Contract-Backed `SegClone` Assembly

Proves `segClone_ok_4k_P` on `tripleRatchetProgAtExt img.base ext` under `recordDecryptSpecP` from
4K-stack subroutine contracts (`sessionShimSpec`, `rustAllocSpec A`, and
`withStack sessionMemcpyRegionSpec allocHookStack`), stepping `SessionState` fields 8–9
(`alice_base_key`, `pq_ratchet_state`) and combining with fields 1–7 from `RecordCloneExtSteps`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.SignalSession.Coins (coinsAt)
open RecordCloneExtSteps

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero


/-! ## 1. Fields 8–9 (`alice_base_key`, `pq_ratchet_state`) and Top-Level Assembly -/

private theorem rce_segClone_aliceBaseKey_444_pos_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (halice : 0 < x.G.alice.bytes.length) (hlen_le : x.G.alice.bytes.length ≤ x.G.alice.cap.toNat)
    (hcap_lt : x.G.alice.cap.toNat < 2 ^ 63) (hptr : x.G.alice.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x444#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x46c#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes → alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ (s.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗ (s.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
        (s.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗ (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
        A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
        memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length) (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hshim := rce_segClone_shim_ok_at hC.shim_ok
  have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok
  dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2628
    (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  have halice_lt : x.G.alice.bytes.length < 2 ^ 63 := by omega
  have halice_le63 : x.G.alice.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have halice_le64 : x.G.alice.bytes.length ≤ 2 ^ 64 := by omega
  have hlay : LayoutOk x.G.alice.bytes.length 1 := ⟨halice, ⟨0, rfl⟩, halice_le63⟩
  have htoNat : (BitVec.ofNat 64 x.G.alice.bytes.length).toNat = x.G.alice.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x444 40; clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (1112))
  wp_steps; wp_call hshim (); clear hshim; wp_steps
  wp_call halloc (x.G.alice.bytes.length, 1); clear halloc
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9768)); wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    exact hpanic _ _ R (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1132)); wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.ptr, x.G.alice.bytes); clear hmemcpy
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneAssemble_close
    have hsp1_eq : sf_1.sp = s.sp := by segCloneAssemble_close
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨BitVec.ofNat 64 x.G.alice.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.alice.bytes⟩
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) rfl rfl)
    rw [vecGhostAt_eq_of_pos A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.alice.bytes halice halice_lt hoom64,
        segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩]
    simp only [sepConj_assoc, hsp_eq, hsp1_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

private theorem rce_segClone_aliceBaseKey_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v30 : BitVec 64} {w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x56c#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1920#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x430#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (alice' : VecGhost),
      s1.pc = (if x.G.alice.bytes = [] then
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x584#64
      else
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x46c#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = w28c.setWidth 64 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = alice'.cap →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      alice'.bytes = x.G.alice.bytes → alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          ((s.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have h1a0 : s.sp + 0x198#64 + 8#64 = s.sp + 0x1a0#64 := by bv_arith
  have h1a8 : s.sp + 0x198#64 + 16#64 = s.sp + 0x1a8#64 := by bv_arith
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x430 20
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x56c 24
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1920 24; clear hfn
  rcases eq_nil_or_length_pos x.G.alice.bytes with halice | halice
  · simp only [halice, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpc with hpc | hpc | hpc <;> {
      apply SepWPp.of_sepWP (mid := entry + bv% (1412)); wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by simp [halice]) (by simp [halice]))
      rw [vecGhostAt_eq_of_nil A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8,
          vecU8Buf_nil_eq A, segClone_pure_eq_emp ⟨hcap_lt, hptr⟩]
      dsimp only [Reg.x26]; simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
    }
  · have halice_ne_nil : x.G.alice.bytes ≠ [] := List.ne_nil_of_length_pos halice
    simp only [halice_ne_nil, ↓reduceIte] at hnext
    rw [vecGhostAt_eq_of_pos A x.G.alice (s.sp + 0x198#64) halice, h1a0, h1a8]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have halice_ne : BitVec.ofNat 64 x.G.alice.bytes.length ≠ 0#64 := ofNat_ne_zero_of_pos halice (by omega)
    have halice_beq : (BitVec.ofNat 64 x.G.alice.bytes.length == 0#64) = false := beq_ofNat_zero_eq_false halice (by omega)
    have hsub := @rce_segClone_aliceBaseKey_444_pos_4k img C A ctl S ext hC x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_444 : ∀ s_444 : State,
        s_444.pc = entry + bv% (1092) → s_444.status = .Running → s_444.sp = s.sp → s_444.spAligned = true →
        s_444.readReg64 .x19 = s.readReg64 .x19 → s_444.readReg64 .x21 = w288.setWidth 64 →
        s_444.readReg64 .x22 = s.readReg64 .x22 → s_444.readReg64 .x23 = w28c.setWidth 64 →
        s_444.readReg64 .x24 = s.readReg64 .x24 → s_444.readReg64 .x25 = BitVec.ofNat 64 x.G.alice.bytes.length →
        s_444.readReg64 .x26 = s.readReg64 .x26 → s_444.readReg64 .x28 = s.readReg64 .x28 →
        s_444.readReg64 .x29 = s.readReg64 .x29 →
        (s_444.trace = s0.trace ∧ calleeSavedVRegs s_444 = calleeSavedVRegs s0) →
        SepWPp prog ret s_444
          (A.pool ∗ (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗ (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
            (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗ (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
            A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
            memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length) (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
            (s_444.sp + 0x288#64) ↦₃₂ w288 ∗ (s_444.sp + 0x28c#64) ↦₃₂ w28c ∗
            (s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26 ∗ stackAt s_444.sp allocHookStack ∗ F)
          Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) by
      rcases hpc with hpc | hpc | hpc <;> {
        apply SepWPp.of_sepWP (mid := entry + bv% (1092)); wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        dsimp only [Reg.x26] at h_at_444
        exact h_at_444 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      }
    intro s_444 hpc444 hrun444 hsp444 hspA444 hx19_444 hx21_444 hx22_444 hx23_444 hx24_444 hx25_444 hx26_444 hx28_444 hx29_444 htr444
    refine SepWPp.weaken_pre
      (P' := A.pool ∗ (s_444.sp + 0x198#64) ↦₆₄ x.G.alice.cap ∗ (s_444.sp + 0x1a0#64) ↦₆₄ x.G.alice.ptr ∗
              (s_444.sp + 0x1a8#64) ↦₆₄ BitVec.ofNat 64 x.G.alice.bytes.length ∗ (x.G.alice.ptr ↦ₛ x.G.alice.bytes) ∗
              A.live x.G.alice.ptr x.G.alice.cap.toNat 1 ∗
              memRegion (x.G.alice.ptr + BitVec.ofNat 64 x.G.alice.bytes.length) (x.G.alice.cap.toNat - x.G.alice.bytes.length) ∗
              stackAt s_444.sp allocHookStack ∗
              (((s_444.sp + 0x288#64) ↦₃₂ w288) ∗ ((s_444.sp + 0x28c#64) ↦₃₂ w28c) ∗
                ((s_444.sp + 0x30#64) ↦₆₄ s.readReg64 .x26) ∗ F))
      (Entails.of_eq (by ac_rfl)) ?_
    refine hsub halice hlen_le hcap_lt hptr hpc444 hrun444 hspA444 hx25_444 htr444
      fun s1 alice' hpc1 hrun1 hsp1 hspA1 hx19_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hbytes' hcap' => ?_
    rw [hsp444]
    exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext s1 alice' hpc1 hrun1 (by reg_chain) hspA1 (by reg_chain) (by reg_chain) (by reg_chain)
        (by reg_chain) (by reg_chain) hx25_1 (by reg_chain) hx27_1 (by reg_chain) (by reg_chain) htr1 hbytes' hcap')

private theorem rce_segClone_pqRatchet_478_pos_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpq : 0 < x.st.pqRatchetState.length) (hlen_le : x.st.pqRatchetState.length ≤ x.G.pq.cap.toNat)
    (hcap_lt : x.G.pq.cap.toNat < 2 ^ 63) (hptr : x.G.pq.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x478#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x594#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ (s.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗ (s.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
        (s.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗ (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
        A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
        memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length) (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hshim := rce_segClone_shim_ok_at hC.shim_ok
  have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok
  dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x25f8
    (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpq_lt : x.st.pqRatchetState.length < 2 ^ 63 := by omega
  have hpq_le63 : x.st.pqRatchetState.length + 1 ≤ 2 ^ 63 := by omega
  have hpq_le64 : x.st.pqRatchetState.length ≤ 2 ^ 64 := by omega
  have hlay : LayoutOk x.st.pqRatchetState.length 1 := ⟨hpq, ⟨0, rfl⟩, hpq_le63⟩
  have htoNat : (BitVec.ofNat 64 x.st.pqRatchetState.length).toNat = x.st.pqRatchetState.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x478 48; clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (1164))
  wp_steps; wp_call hshim (); clear hshim; wp_steps
  wp_call halloc (x.st.pqRatchetState.length, 1); clear halloc
  refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9720)); wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    exact hpanic _ _ R (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1428)); wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.pq.ptr, x.st.pqRatchetState)
    clear hmemcpy; wp_steps
    refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 x.st.pqRatchetState.length) (sf_1.readReg64 (Reg.gpr 0#5))
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
        (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) rfl)
    rw [vecU8At_eq_of_pos A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq, h1b8, h1c0,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.st.pqRatchetState hpq hpq_lt hoom64,
        segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩]
    have hsp_eq : sf.sp = s.sp := by segCloneAssemble_close
    have hsp1_eq : sf_1.sp = s.sp := by segCloneAssemble_close
    simp only [sepConj_assoc, hsp_eq, hsp1_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

private theorem rce_segClone_pqRatchet_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (if x.G.alice.bytes = [] then
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x584#64
    else
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x46c#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x594#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = s.readReg64 .x19 → s1.readReg64 .x20 = pqCap' →
      s1.readReg64 .x21 = s.readReg64 .x21 → s1.readReg64 .x22 = pqPtr' →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x22 →
      s1.readReg64 .x27 = s.readReg64 .x27 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have h1b8 : s.sp + 0x1b0#64 + 8#64 = s.sp + 0x1b8#64 := by bv_arith
  have h1c0 : s.sp + 0x1b0#64 + 16#64 = s.sp + 0x1c0#64 := by bv_arith
  have hpcs : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x584#64 ∨
              s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x46c#64 := by
    by_cases h : x.G.alice.bytes = [] <;> simp only [h, ↓reduceIte] at hpc <;> [exact Or.inl hpc; exact Or.inr hpc]
  clear hpc
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x46c 12
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x584 16; clear hfn
  rcases eq_nil_or_length_pos x.st.pqRatchetState with hpq | hpq
  · rw [hpq, vecU8At_eq_of_nil A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    rcases hpcs with hpc | hpc <;> {
      apply SepWPp.of_sepWP (mid := entry + bv% (1428)); wp_steps
      refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0#64 1#64 (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by simp [hpq]))
      rw [hpq, vecU8At_eq_of_nil A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr, h1b8, h1c0,
          vecU8Buf_nil_eq A, segClone_pure_eq_emp ⟨hcap_lt, hptr⟩]
      simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
    }
  · rw [vecU8At_eq_of_pos A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState hpq, h1b8, h1c0]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hpq_ne : BitVec.ofNat 64 x.st.pqRatchetState.length ≠ 0#64 := ofNat_ne_zero_of_pos hpq (by omega)
    have hpq_beq : (BitVec.ofNat 64 x.st.pqRatchetState.length == 0#64) = false := beq_ofNat_zero_eq_false hpq (by omega)
    have hsub := @rce_segClone_pqRatchet_478_pos_4k img C A ctl S ext hC x R s0
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    suffices h_at_478 : ∀ s_478 : State,
        s_478.pc = entry + bv% (1144) → s_478.status = .Running → s_478.sp = s.sp → s_478.spAligned = true →
        s_478.readReg64 .x19 = s.readReg64 .x19 → s_478.readReg64 .x20 = BitVec.ofNat 64 x.st.pqRatchetState.length →
        s_478.readReg64 .x21 = s.readReg64 .x21 → s_478.readReg64 .x23 = s.readReg64 .x23 →
        s_478.readReg64 .x25 = s.readReg64 .x25 → s_478.readReg64 .x26 = s.readReg64 .x22 →
        s_478.readReg64 .x27 = s.readReg64 .x27 → s_478.readReg64 .x28 = s.readReg64 .x28 →
        s_478.readReg64 .x29 = s.readReg64 .x29 →
        (s_478.trace = s0.trace ∧ calleeSavedVRegs s_478 = calleeSavedVRegs s0) →
        SepWPp prog ret s_478
          (A.pool ∗ (s_478.sp + 0x1b0#64) ↦₆₄ x.G.pq.cap ∗ (s_478.sp + 0x1b8#64) ↦₆₄ x.G.pq.ptr ∗
            (s_478.sp + 0x1c0#64) ↦₆₄ BitVec.ofNat 64 x.st.pqRatchetState.length ∗ (x.G.pq.ptr ↦ₛ x.st.pqRatchetState) ∗
            A.live x.G.pq.ptr x.G.pq.cap.toNat 1 ∗
            memRegion (x.G.pq.ptr + BitVec.ofNat 64 x.st.pqRatchetState.length) (x.G.pq.cap.toNat - x.st.pqRatchetState.length) ∗
            stackAt s_478.sp allocHookStack ∗ F)
          Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) by
      rcases hpcs with hpc | hpc <;> {
        apply SepWPp.of_sepWP (mid := entry + bv% (1144)); wp_steps
        refine SepWP.done (by segCloneAssemble_close) (by segCloneAssemble_close) ?_
        exact h_at_478 _ (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
          (by segCloneAssemble_close) (by segCloneAssemble_close) (by segCloneAssemble_close)
      }
    intro s_478 hpc478 hrun478 hsp478 hspA478 hx19_478 hx20_478 hx21_478 hx23_478 hx25_478 hx26_478 hx27_478 hx28_478 hx29_478 htr478
    refine hsub hpq hlen_le hcap_lt hptr hpc478 hrun478 hspA478 hx20_478 htr478
      fun s1 pqCap' pqPtr' hpc1 hrun1 hsp1 hspA1 hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 htr1 hcap' => ?_
    rw [hsp478] at hx24_1 ⊢
    exact hnext s1 pqCap' pqPtr' hpc1 hrun1 (by reg_chain) hspA1
      (by reg_chain) hx20_1 (by reg_chain) hx22_1 (by reg_chain) hx24_1
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr1 hcap'

private theorem rce_setWidth_64_truncate_32 (w : BitVec 32) :
    (w.setWidth 64).truncate 32 = w := by bv_kernel

private theorem rce_segClone_fields_5_to_9_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 v08 v18 v30 : BitVec 64} {v14 v24 v28 v2c v3c w288 w28c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x544#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x300#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx24 : s.readReg64 .x24 = s.sp + 0xca0#64) (hx25 : s.readReg64 .x25 = x.st.sessionVersion.setWidth 64)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost)
      (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32)
      (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32) (alice' : VecGhost) (pqCap' pqPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x594#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' → s1.readReg64 .x20 = pqCap' → s1.readReg64 .x21 = w288.setWidth 64 →
      s1.readReg64 .x22 = pqPtr' → s1.readReg64 .x23 = w28c.setWidth 64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x25 = alice'.cap → s1.readReg64 .x26 = pendCap' → s1.readReg64 .x27 = alice'.ptr →
      s1.readReg64 .x28 = chainsPtr' → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      chains'.length = x.st.receiverChains.length → chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      alice'.bytes = x.G.alice.bytes → alice'.cap = BitVec.ofNat 64 x.G.alice.bytes.length →
      pqCap' = BitVec.ofNat 64 x.st.pqRatchetState.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
          optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
          ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗ ((s.sp + 0x08#64) ↦₆₄ v08') ∗ ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s.sp + 0x24#64) ↦₃₂ v24') ∗ ((s.sp + 0x28#64) ↦₃₂ v28') ∗
          ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s.sp + 0x30#64) ↦₆₄ chainsCap') ∗ ((s.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecAt A 104 8 (chainAt A) (s.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
        optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗
        (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗ ((s.sp + 0x14#64) ↦₃₂ v14) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        ((s.sp + 0x30#64) ↦₆₄ v30) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecAt_0x180_chains_eq A s.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
            vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗
            (((s.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗ ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              vecGhostAt A x.G.alice (s.sp + 0x198#64) ∗ vecU8At A (s.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
              ((s.sp + 0x288#64) ↦₃₂ w288) ∗ ((s.sp + 0x28c#64) ↦₃₂ w28c) ∗ (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x08#64) ↦₆₄ v08) ∗
              ((s.sp + 0x14#64) ↦₃₂ v14) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
              ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₆₄ v30) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_receiverChains_4k hC hchainClone x R s0 s ret Q _ hpc hrun hsp hx26 htr hchains_len
    fun s1 chainsCap' chainsPtr' chains' hchains_l hchains_c hpc1 hrun1 hsp1 hspA1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗
            ((s1.sp + 0x08#64) ↦₆₄ v08) ∗ ((s1.sp + 0x18#64) ↦₆₄ v18) ∗
            ((s1.sp + 0x24#64) ↦₃₂ v24) ∗ ((s1.sp + 0x28#64) ↦₃₂ v28) ∗ ((s1.sp + 0x2c#64) ↦₃₂ v2c) ∗
            stackAt s1.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s1.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗ vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗ ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ v00) ∗ ((s1.sp + 0x14#64) ↦₃₂ v14) ∗ ((s1.sp + 0x30#64) ↦₆₄ v30) ∗ ((s1.sp + 0x3c#64) ↦₃₂ v3c) ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗ memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains hchains_len,
            stackAt_chainClone_eq_alloc s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_pendingPreKey_4k hC hpc1 hrun1 hspA1 htr1
    fun s2 pendCap' pendPtr' v08' v24' v28' v2c' hpc2 hrun2 hsp2 hspA2 hx22_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            (s2.sp ↦₆₄ v00) ∗ ((s2.sp + 0x14#64) ↦₃₂ v14) ∗ ((s2.sp + 0x3c#64) ↦₃₂ v3c) ∗ stackAt s2.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
              vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗ vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
              ((s2.sp + 0x08#64) ↦₆₄ v08') ∗ ((s2.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s2.sp + 0x24#64) ↦₃₂ v24') ∗
              ((s2.sp + 0x28#64) ↦₃₂ v28') ∗ ((s2.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s2.sp + 0x30#64) ↦₆₄ v30) ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗ memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_pendingKyber_4k hC hpc2 hrun2 hspA2 htr2
    fun s3 kybCap' kybPtr' v14' hpc3 hrun3 hsp3 hspA3 hx19_3 hx22_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  have hx25_2' : (s2.readReg64 .x25).truncate 32 = x.st.sessionVersion := by
    rw [hx25_2, hx25_1, hx25, rce_setWidth_64_truncate_32]
  rw [hx25_2', ← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗ ((s3.sp + 0x288#64) ↦₃₂ w288) ∗
            ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗ ((s3.sp + 0x30#64) ↦₆₄ v30) ∗ stackAt s3.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
              optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
              vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              (s3.sp ↦₆₄ kybPtr') ∗ ((s3.sp + 0x08#64) ↦₆₄ v08') ∗ ((s3.sp + 0x14#64) ↦₃₂ v14') ∗
              ((s3.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s3.sp + 0x24#64) ↦₃₂ v24') ∗ ((s3.sp + 0x28#64) ↦₃₂ v28') ∗
              ((s3.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s3.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗
              memRegion (s3.sp + 0x5f0#64) 104 ∗ memRegion (s3.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_aliceBaseKey_4k hC hpc3 hrun3 hspA3 htr3
    fun s4 alice' hpc4 hrun4 hsp4 hspA4 hx19_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 hx29_4 htr4 halice_b halice_c => ?_
  have hx26_3' : s3.readReg64 .x26 = chainsCap' := by reg_chain
  rw [hx26_3', ← hsp4]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecU8At A (s4.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗ stackAt s4.sp allocHookStack ∗
            (vecAt A 104 8 (chainAt A) (s4.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s4.sp + 0x198#64) ∗ optTailVecAt A 48 (s4.sp + 0x230#64) x.G.pending ∗
              optTailVecAt A 32 (s4.sp + 0x260#64) x.G.kyber ∗ ((s4.sp + 0x288#64) ↦₃₂ w288) ∗ ((s4.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗ (s4.sp ↦₆₄ kybPtr') ∗ ((s4.sp + 0x08#64) ↦₆₄ v08') ∗
              ((s4.sp + 0x14#64) ↦₃₂ v14') ∗ ((s4.sp + 0x18#64) ↦₆₄ pendPtr') ∗ ((s4.sp + 0x24#64) ↦₃₂ v24') ∗
              ((s4.sp + 0x28#64) ↦₃₂ v28') ∗ ((s4.sp + 0x2c#64) ↦₃₂ v2c') ∗ ((s4.sp + 0x30#64) ↦₆₄ chainsCap') ∗
              ((s4.sp + 0x3c#64) ↦₃₂ x.st.sessionVersion) ∗ memRegion (s4.sp + 0x5f0#64) 104 ∗
              memRegion (s4.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  have hx24_4' : s4.readReg64 .x24 = s4.sp + 0xca0#64 := by reg_chain
  refine rce_segClone_pqRatchet_4k hC hpc4 hrun4 hspA4 hx24_4' htr4
    fun s5 pqCap' pqPtr' hpc5 hrun5 hsp5 hspA5 hx19_5 hx20_5 hx21_5 hx22_5 hx23_5 hx24_5 hx25_5 hx26_5 hx27_5 hx28_5 hx29_5 htr5 hpq_c => ?_
  have hsp_eq : s4.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx24_5 ⊢
  refine SepWPp.weaken_pre (by rw [stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl))
    (hnext s5 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr' hpc5 hrun5 (by reg_chain) hspA5
      (by reg_chain) hx20_5 (by reg_chain) hx22_5 (by reg_chain) hx24_5
      (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain)
      htr5 hchains_l hchains_c halice_b halice_c hpq_c)

set_option linter.unusedVariables false in
private def rce_clonePost (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : RecordDecryptGhost) (s0 sf : State) (P_f : SepProp) : Prop :=
  sf.sp = s0.sp ∧ sf.spAligned = true ∧ sf.readReg64 .x29 = s0.readReg64 .x29 ∧
    (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
    sf.readReg64 .x9 = x.msg.messageVersion.setWidth 64 ∧
    (P_f ⊢ ∃∗ G₁ : SessionGhost, ⌜CloneRel x.G G₁⌝ ∗ recFrame A img x s0.sp ∗
      sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗ sessionStateAt A (s0.sp + 0xca0#64) G₁ x.st ∗
      errsAt A (s0.sp + 0x5d8#64) [] ∗ memRegion (s0.sp + 0x4b0#64) 48 ∗
      CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest)

private theorem rce_segClone_wp_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64)
    (hrun : s0.status = .Running) (hsp : s0.spAligned = true)
    (h27 : s0.readReg64 .x27 = x.sret) (h19 : s0.readReg64 .x19 = x.remA)
    (h23 : s0.readReg64 .x23 = s0.sp + 0x5f0#64) (h24 : s0.readReg64 .x24 = s0.sp + 0xca0#64)
    (hrc32 : x.st.receiverChains.length < 2 ^ 32) :
    SepWPp (tripleRatchetProgAtExt img.base ext)
      (if x.st.version.toNat = x.msg.messageVersion.toNat then
         (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x69c#64
       else
         (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x7e4#64)
      s0
      (memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
        sessionStateAt A (s0.sp + 0x138#64) x.G x.st ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool)
      (rce_clonePost A ctl img x s0)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hrc_lt : x.st.receiverChains.length < 2 ^ 63 := by omega
  rw [segClone_sessionStateAt_0x138_eq A s0.sp x.G x.st]
  refine SepWPp.weaken_pre
    (P' := ⌜PublicKey.deserialize x.G.localIk.bytes = .ok x.st.localIdentity.publicKey ∧
            (match x.st.remoteIdentity with
             | none => x.G.remoteIk.bytes = []
             | some ik => PublicKey.deserialize x.G.remoteIk.bytes = .ok ik.publicKey) ∧
            x.G.chains.length = x.st.receiverChains.length ∧
            x.G.pending.isSome = x.st.pendingPreKey ∧ x.G.regIds.length = 8 ∧
            x.G.localIk.bytes.length = 33 ∧
            (x.st.remoteIdentity.isSome → x.G.remoteIk.bytes.length = 33)⌝ ∗
          (memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦ₛ x.G.regIds) ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗ A.pool))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨h_loc_deser, h_rem_deser, h_chains_len, h_pend_some, h_reg_len, h_loc_len, h_rem_len⟩ => ?_
  obtain ⟨w288, w28c, _, h_reg_pts⟩ := exists_unpack32_pair_of_length_8 h_reg_len
  have h28c : s0.sp + 0x288#64 + 4#64 = s0.sp + 0x28c#64 := by bv_arith
  rw [h_reg_pts (s0.sp + 0x288#64), h28c]
  refine SepWPp.weaken_pre
    (P' := memRegion s0.sp 0xa0 ∗ ((s0.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s0.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s0.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s0.sp + 0x130#64) ↦₆₄ 0#64) ∗
            vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ memRegion (s0.sp + 0x4b0#64) 0x950 ∗
            protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
            CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗
            (A.pool ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
              vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
              ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s0.sp + 0x288#64) ↦₃₂ w288) ∗ ((s0.sp + 0x28c#64) ↦₃₂ w28c)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_entry_combined hpc hrun hsp h19 h27 h23 h24 ⟨rfl, rfl⟩
    fun s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  rw [← hsp1] at hx23_1 hx24_1 ⊢
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
            vecU8At A (s1.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s1.sp + 0x5f0#64) 104 ∗
            ((s1.sp + 0x40#64) ↦₆₄ sv.v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ sv.v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ sv.v54) ∗
            ((s1.sp + 0x58#64) ↦₆₄ sv.v58) ∗ ((s1.sp + 0x60#64) ↦₆₄ sv.v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ sv.v68) ∗
            ((s1.sp + 0x70#64) ↦₆₄ sv.v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ sv.v78) ∗
            ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s1.sp chainCloneStack ∗
            (((s1.sp + 0x180#64) ↦₆₄ x.G.chainsCap) ∗ ((s1.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
              vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s1.sp + 0x198#64) ∗ vecU8At A (s1.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optTailVecAt A 48 (s1.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s1.sp + 0x260#64) x.G.kyber ∗
              ((s1.sp + 0x288#64) ↦₃₂ w288) ∗ ((s1.sp + 0x28c#64) ↦₃₂ w28c) ∗
              (s1.sp ↦₆₄ sv.v00) ∗ ((s1.sp + 0x08#64) ↦₆₄ sv.v08) ∗ ((s1.sp + 0x14#64) ↦₃₂ sv.v14) ∗
              ((s1.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s1.sp + 0x24#64) ↦₃₂ sv.v24) ∗ ((s1.sp + 0x28#64) ↦₃₂ sv.v28) ∗
              ((s1.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((s1.sp + 0x30#64) ↦₆₄ sv.v30) ∗ ((s1.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
              memRegion (s1.sp + 0x10#64) 4 ∗ memRegion (s1.sp + 0x20#64) 4 ∗ memRegion (s1.sp + 0x38#64) 4 ∗
              memRegion (s1.sp + 0x50#64) 4 ∗ dstSlotsAt s1.sp dv ∗
              ((s1.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s1.sp))
    (by unfold spillSlotsAt
        rw [segClone_vecAt_0x180_chains_eq A s1.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len,
            stackAt_chainClone_eq_alloc s1.sp]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_fields_1_to_4_4k hC hsenderClone hpc1 hrun1 hspA1 hx23_1 htr1 hrc_lt
    fun s2 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc2 hrun2 hsp2 hspA2 hx23_2 hx24_2 hx25_2 hx26_2 hx29_2 htr2 hloc_b hloc_c hrem_b hrem_c hinl => ?_
  rw [← hsp2] at hx23_2 ⊢
  have hx24_2' : s2.readReg64 .x24 = s2.sp + 0xca0#64 := by reg_chain
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecAt A 104 8 (chainAt A) (s2.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s2.sp + 0x198#64) ∗ vecU8At A (s2.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optTailVecAt A 48 (s2.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s2.sp + 0x260#64) x.G.kyber ∗
            ((s2.sp + 0x288#64) ↦₃₂ w288) ∗ ((s2.sp + 0x28c#64) ↦₃₂ w28c) ∗
            (s2.sp ↦₆₄ sv.v00) ∗ ((s2.sp + 0x08#64) ↦₆₄ sv.v08) ∗ ((s2.sp + 0x14#64) ↦₃₂ sv.v14) ∗
            ((s2.sp + 0x18#64) ↦₆₄ sv.v18) ∗ ((s2.sp + 0x24#64) ↦₃₂ sv.v24) ∗ ((s2.sp + 0x28#64) ↦₃₂ sv.v28) ∗
            ((s2.sp + 0x2c#64) ↦₃₂ sv.v2c) ∗ ((s2.sp + 0x30#64) ↦₆₄ sv.v30) ∗ ((s2.sp + 0x3c#64) ↦₃₂ sv.v3c) ∗
            memRegion (s2.sp + 0x5f0#64) 104 ∗ stackAt s2.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗ optSenderChainHeap A sender' x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
              ((s2.sp + 0x40#64) ↦₆₄ scCap') ∗ ((s2.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s2.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗ ((s2.sp + 0x58#64) ↦₆₄ 32#64) ∗
              ((s2.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗ ((s2.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
              ((s2.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗ ((s2.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp + 0x10#64) 4 ∗ memRegion (s2.sp + 0x20#64) 4 ∗ memRegion (s2.sp + 0x38#64) 4 ∗
              memRegion (s2.sp + 0x50#64) 4 ∗ dstSlotsAt s2.sp dv ∗
              ((s2.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s2.sp))
    (by rw [segClone_vecAt_0x180_chains_eq A s2.sp x.G.chainsCap x.G.chainsPtr x.G.chains x.st.receiverChains h_chains_len]
        exact Entails.of_eq (by ac_rfl)) ?_
  refine rce_segClone_fields_5_to_9_4k hC hchainClone hpc2 hrun2 hspA2 hx24_2' hx25_2 hx26_2 htr2 h_chains_len
    fun s3 chainsCap' chainsPtr' chains' pendCap' pendPtr' v08' v24' v28' v2c'
      kybCap' kybPtr' v14' alice' pqCap' pqPtr'
      hpc3 hrun3 hsp3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hx29_3 htr3
      hchains_l hchains_c halice_b halice_c hpq_c => ?_
  rw [← hsp3] at hx24_3 ⊢
  refine SepWPp.weaken_pre
    (P' := dstSlotsAt s3.sp dv ∗ chunks96_6QAt (s3.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
            spillSlotsAt s3.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
            ((s3.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            (A.pool ∗ vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecAt A 104 8 (chainAt A) (s3.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
              vecGhostAt A x.G.alice (s3.sp + 0x198#64) ∗ vecU8At A (s3.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
              optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              optTailVecAt A 48 (s3.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s3.sp + 0x260#64) x.G.kyber ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              ((s3.sp + 0x288#64) ↦₃₂ w288) ∗ ((s3.sp + 0x28c#64) ↦₃₂ w28c) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
              vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
              optSenderChainHeap A sender' x.st.senderChain ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
              OptKybClone A x.G.kyber kybCap' kybPtr' ∗ memRegion (s3.sp + 0x5f0#64) 104 ∗ stackAt s3.sp chainCloneStack ∗
              CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s3.sp))
    (by unfold spillSlotsAt; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fields_10_to_11 dv localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
    pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 kybCap' kybPtr' v08' v14' pendCap' pendPtr' v24' v28' v2c' w288 w28c _
    hpc3 hrun3 hspA3 hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 htr3
    fun s4 hpc4 hrun4 hsp4 hspA4 hx9_4 hx29_4 htr4 => ?_
  have hsp_eq : s3.sp = s0.sp := by reg_chain
  rw [hsp_eq]
  refine SepWPp.done hpc4 hrun4 ⟨by reg_chain, hspA4, by reg_chain, htr4, hx9_4, ?_⟩
  have hdst := segClone_dstSlotsWrittenAt_entails_sessionStateAt A s0.sp x localIk' remoteIk' rootPtr'
    chainsCap' chainsPtr' chains' alice' pqCap' pqPtr' sender' scCap'
    sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24' kybCap' kybPtr' v14' w288 w28c
    h_loc_deser h_rem_deser h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
    hloc_b hloc_c hrem_b hrem_c hchains_l hchains_c halice_b halice_c hpq_c hinl
  have hsrc := segClone_srcSessionState_reassemble A s0.sp x w288 w28c
    h_loc_deser h_rem_deser h_chains_len h_pend_some h_reg_len h_loc_len h_rem_len h_reg_pts
  have hrest := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest_reassemble A ctl img x s0.sp
    sq0 sq1 sq2 sq3 sq4 sq5 kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
    scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap
  rw [stackAt_chainClone_eq_alloc s0.sp]
  refine Entails.trans
    (Q := (segClone_dstSlotsWrittenAt s0.sp localIk' remoteIk' rootPtr' chainsCap' chainsPtr' alice'
              pqCap' pqPtr' scCap' sq0 sq1 sq2 sq3 sq4 sq5 pendCap' pendPtr' v28' v2c' v08' v24'
              kybCap' kybPtr' v14' x.st.sessionVersion x.st.previousCounter w288 w28c ∗
            vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
            vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
            vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
            vecU8Buf A alice'.cap alice'.ptr alice'.bytes ∗ vecU8Buf A pqCap' pqPtr' x.st.pqRatchetState ∗
            optSenderChainHeap A sender' x.st.senderChain ∗ OptPendClone A x.G.pending pendCap' pendPtr' ∗
            OptKybClone A x.G.kyber kybCap' kybPtr') ∗
          (vecGhostAt A x.G.localIk (s0.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s0.sp + 0x150#64) ∗
            vecU8At A (s0.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            vecAt A 104 8 (chainAt A) (s0.sp + 0x180#64) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
            vecGhostAt A x.G.alice (s0.sp + 0x198#64) ∗ vecU8At A (s0.sp + 0x1b0#64) x.G.pq.cap x.G.pq.ptr x.st.pqRatchetState ∗
            optSenderChainAt A (s0.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            optTailVecAt A 48 (s0.sp + 0x230#64) x.G.pending ∗ optTailVecAt A 32 (s0.sp + 0x260#64) x.G.kyber ∗
            ((s0.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s0.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            ((s0.sp + 0x288#64) ↦₃₂ w288) ∗ ((s0.sp + 0x28c#64) ↦₃₂ w28c)) ∗
          (spillSlotsAt s0.sp kybPtr' v08' v14' pendPtr' v24' v28' v2c' chainsCap' x.st.sessionVersion
              scCap' rootPtr' x.st.previousCounter 32#64 remoteIk'.ptr remoteIk'.cap localIk'.ptr localIk'.cap ∗
            chunks96_6QAt (s0.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ memRegion (s0.sp + 0x5f0#64) 104 ∗
            ((s0.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
            memRegion (s0.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ stackAt s0.sp allocHookStack ∗ A.pool ∗
            CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s0.sp))
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono hdst (sepConj_mono hsrc hrest)) ?_
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro G₁
  exact Entails.sepExists_right G₁ (Entails.of_eq (by ac_rfl))

/-- Contract-backed `SegClone` under `recordDecryptSpecP` from 4K-stack subroutine contracts
(`sessionShimSpec`, `rustAllocSpec A`, `withStack sessionMemcpyRegionSpec allocHookStack`). -/
theorem segClone_ok_4k_P
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hshim_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr shimName) sessionShimSpec)
    (halloc_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr allocName) (rustAllocSpec A))
    (hmemcpy_fn : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack))
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 : State)
    (hpc : s0.pc = CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry img)
    (hrun : s0.status = .Running)
    (hpre : s0.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img).pre x s0 ∗ R)
    (hL : (tripleRatchetProgAtExt img.base ext).CodeLoaded s0.mem) :
    ∃ s', Steps (tripleRatchetProgAtExt img.base ext) s0 s' ∧
      ((∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.VStateP A ctl uuidTryParse img x G₁ R s0 s') ∨
       (∃ G₁, CryptoVerification.Cli.LibsignalTripleRatchet.Record.MState A ctl img x G₁ R s0 s') ∨
       regionOutcome (CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP C A ctl uuidTryParse S img)
         (CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionExit img) x R s0 s') := by
  have hentry_eq : entryOf img CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName :=
    entryOf_eq_tripleRatchetProgAtExt ext hloads CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
  have hpc' : s0.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64 := by
    simpa [CryptoVerification.Cli.LibsignalTripleRatchet.recordRegionEntry, hentry_eq] using hpc
  dsimp only [CryptoVerification.Cli.LibsignalTripleRatchet.recordDecryptSpecP, Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre; obtain ⟨⟨hF, hsym⟩, hpre⟩ := hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hsp, h27, h19, h23, h24, hrem_or_dist, hseeds, hrc32, _⟩, hm⟩ := hpre
  obtain ⟨sf, hsteps, hout⟩ :=
    rce_segClone_wp_4k (C := C) (ctl := ctl) (S := S)
      ⟨hshim_fn, halloc_fn, hmemcpy_fn⟩ hchainClone hsenderClone x R s0
      hpc' hrun hsp h27 h19 h23 h24 hrc32 R hm hL
  rcases hout with ⟨hpcf, hrunf, P_f, hmf, hspf, hspAf, hx29f, ⟨htrf, hvrf⟩, hx9f, hent⟩ |
      ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, hoom⟩
  · have hmeta : recMeta img s0 sf :=
      ⟨hrunf, hspf, hspAf, hx29f, htrf, hF.of_keepsFrozen hsteps.keepsFrozen,
        hsteps.symtab_eq.trans hsym, hvrf⟩
    have hmf' := Satisfies.mono (sepConj_mono_left hent) hmf
    rw [sepExists_sepConj_left, satisfies_sepExists] at hmf'; obtain ⟨G₁, hmf'⟩ := hmf'
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf'; obtain ⟨hclone, hmf'⟩ := hmf'
    simp only [sepConj_assoc] at hmf'
    by_cases hver : x.st.version.toNat = x.msg.messageVersion.toNat
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcV : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC img := by
        simpa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recVPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inl ⟨G₁, hpcV, hmeta, ⟨hrem_or_dist, hseeds, hrc32⟩, hclone, hver, ?_⟩⟩
      simpa only [sepConj_assoc] using hmf'
    · simp only [hver, ↓reduceIte] at hpcf
      have hpcM : sf.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC img := by
        simpa [CryptoVerification.Cli.LibsignalTripleRatchet.Record.recMPC, hentry_eq] using hpcf
      refine ⟨sf, hsteps, Or.inr (Or.inl ⟨G₁, hpcM, hmeta, hver, hx9f, ?_⟩)⟩
      simpa only [sepConj_assoc] using hmf'
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inr ⟨hpan, hqp hmf⟩))⟩
  · exact (not_satisfies_false_sepConj hoom).elim

end CryptoVerification.Cli.LibsignalSpqrV1.M4
