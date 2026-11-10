/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBase
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.Defs
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchClone
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# CLI `SegClone` Entry and Sub-Segments 1–4 (`local_ik`, `remote_ik`, `root_key`, `sender_chain`)

Proves entry frame initialization (`+0x1a8 → +0x1fc`) and cloning of `local_identity_key`,
`remote_identity_key`, `root_key`, and `sender_chain` (`+0x1fc → +0x544 / +0x300`) in CLI
`signal_session_ratchet::decrypt_signal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone

open CryptoVerification.LibsignalTripleRatchet.RawByteMove

open CryptoVerification.LibsignalTripleRatchet.Record

open ProofLib.ProgramReflection

set_option maxRecDepth 200000

set_option maxHeartbeats 400000

set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Entry frame initialization (`+0x1a8 → +0x1fc`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_entry_to_0x1fc {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {v80 v88 v90 : BitVec 64} {v9c : BitVec 32}
    {v5b0 : BitVec 64} {v5bc : BitVec 8} {v5c0 v5c8 v5d0 v5d8 v5e0 v5e8 : BitVec 64}
    {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : x.G.localIk.cap < 2 ^ 63)
    (hnext : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (((s.sp + 0x80#64) ↦₆₄ x.sret) ∗ ((s.sp + 0x88#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x90#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
          ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
          ((s.sp + 0x5b0#64) ↦₆₄ x.remA) ∗
          ((s.sp + 0x5bc#64) ↦₈ msgTypeByte .whisper) ∗
          ((s.sp + 0x5c0#64) ↦₆₄ (s.sp + 0x5bc#64)) ∗
          ((s.sp + 0x5c8#64) ↦₆₄ x.msgA) ∗
          ((s.sp + 0x5d0#64) ↦₆₄ (s.sp + 0x5b0#64)) ∗
          errsAt A (s.sp + 0x5d8#64) [] ∗
          ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
        ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
        ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
        ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
        ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
        ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
        ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hcmn : x.G.localIk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap
  have hcmn_beq : (x.G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1a8 84
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (508))
  wp_steps
  refine SepWP.done (by segCloneKeys_close) hrun ?_
  refine SepWPp.weaken_pre ?_
    (hnext _ (by segCloneKeys_close) hrun rfl hsp h23 h24 rfl htr)
  dsimp only [errsAt, msgTypeByte, BitVec.zeroExtend]
  have h5e0 : s.sp + 0x5d8#64 + 8#64 = s.sp + 0x5e0#64 := by bv_arith
  have h5e8 : s.sp + 0x5d8#64 + 16#64 = s.sp + 0x5e8#64 := by bv_arith
  rw [h5e0, h5e8]
  exact Entails.of_eq (by ac_rfl)

/-- Clone `local_identity_key` (`+0x1fc → +0x504 / +0x238`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_localIk {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x504#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x238#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = localIk'.cap →
      s1.readReg64 .x21 = localIk'.ptr →
      s1.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have h140 : s.sp + 0x138#64 + 8#64 = s.sp + 0x140#64 := by bv_arith
  have h148 : s.sp + 0x138#64 + 16#64 = s.sp + 0x148#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · rw [vecGhostAt_eq_of_nil A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1fc 12
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x4f8 12
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    have hpc_rem :
        (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (568) else entry + bv% (1284)) =
        (if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
        have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
          beq_ofNat_zero_eq_false hrem (by omega)
        simp [hne, hbeq]
    apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568))
    wp_steps
    refine SepWP.done (by segCloneKeys_close) hrun ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneKeys_close) hrun rfl hsp
        rfl rfl rfl rfl rfl rfl rfl htr hloc.symm (by simp [hloc]))
    rw [vecGhostAt_eq_of_nil A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148,
        vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [vecGhostAt_eq_of_pos A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_shim_ok_at hA
    have halloc := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_alloc_ok_at hA
    have hmemcpy := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_memcpy_ok_at hA
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x25f8#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q
          (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) :=
      fun s_p P_p => CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x25f8 x s0 s_p P_p R
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 :=
      ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false :=
      beq_ofNat_zero_eq_false hloc (by omega)
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.localIk.bytes.length 1 := ⟨hloc, hpow2, hloc_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1fc 60
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (540))
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.localIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (9720))
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem :
          (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (1284) else entry + bv% (568)) =
          (if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · have hne : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
          have hbeq : (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrem (by omega)
          simp [hne, hbeq]
      apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by segCloneKeys_close
      simp only [sepConj_assoc, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `remote_identity_key` (`+0x504 / +0x238 → +0x268`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_remoteIk {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = []
      then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x504#64
      else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x238#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x268#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = remoteIk'.cap →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = remoteIk'.ptr →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
        ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have h158 : s.sp + 0x150#64 + 8#64 = s.sp + 0x158#64 := by bv_arith
  have h160 : s.sp + 0x150#64 + 16#64 = s.sp + 0x160#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · simp only [hrem, ↓reduceIte] at hpc
    rw [hrem] at hx22
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x504 12
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (616))
    wp_steps
    refine SepWP.done rfl hrun ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl hrun rfl hsp
        rfl rfl hx22 rfl rfl rfl rfl rfl rfl htr
        hrem.symm (by simp [hrem]))
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160,
        vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]
    exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_shim_ok_at hA
    have halloc := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_alloc_ok_at hA
    have hmemcpy := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_memcpy_ok_at hA
    have hpanic : ∀ (s_p : State) (P_p : SepProp),
        s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2604#64 →
        s_p.status = .Running →
        s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q
          (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) :=
      fun s_p P_p => CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2604 x s0 s_p P_p R
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, hpow2, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x238 48
    clear hfn
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (588))
    wp_steps
    wp_call hshim ()
    clear hshim
    wp_steps
    wp_call halloc (x.G.remoteIk.bytes.length, 1)
    clear halloc
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]
      refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (9732))
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
    · clear hpanic
      have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]
      refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (616))
      wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes)
      clear hmemcpy
      wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) rfl rfl)
      rw [vecGhostAt_eq_of_pos A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp_eq : sf.sp = s.sp := by segCloneKeys_close
      simp only [sepConj_assoc, hsp_eq]
      exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `root_key` (`+0x268 → +0x290`, 32 bytes) and store the new pointer at `[sp + 0x48]`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_rootKey {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v48 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x268#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x290#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = 32#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hshim := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_shim_ok_at hA
  have halloc := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_alloc_ok_at hA
  have hmemcpy := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_memcpy_ok_at hA
  have hpanic : ∀ (s_p : State) (P_p : SepProp),
      s_p.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x2610#64 →
      s_p.status = .Running →
      s_p.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s_p P_p Q
        (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) :=
    fun s_p P_p => CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2610 x s0 s_p P_p R
  have h170 : s.sp + 0x168#64 + 8#64 = s.sp + 0x170#64 := by bv_arith
  have h178 : s.sp + 0x168#64 + 16#64 = s.sp + 0x178#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.st.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.st.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.st.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.st.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos,
      h170, h178]
  simp only [sepConj_assoc]
  refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have h32_pos : 0 < 32 := by decide
  have h32_le63 : 32 + 1 ≤ 2 ^ 63 := by decide
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨h32_pos, hpow2, h32_le63⟩
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x268 40
  clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (636))
  wp_steps
  wp_call hshim ()
  clear hshim
  wp_steps
  wp_call halloc (32, 1)
  clear halloc
  refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9744))
    wp_steps
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    have hmem32 :
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
          memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey).length := by
      rw [hroot_len]
    rw [hmem32]
    apply SepWPp.of_sepWP (mid := entry + bv% (656))
    wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.st.rootKey)
    clear hmemcpy
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close))
    have hbuf32 :
        vecU8Buf A 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey) =
          A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗
            (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.st.rootKey) := by
      have h := vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey)
        hroot_pos hroot_lt hoom64
      rwa [hroot_len] at h
    rw [vecU8At_eq_of_pos A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos,
        h170, h178, hbuf32]
    have hsp_eq : sf.sp = s.sp := by segCloneKeys_close
    simp only [sepConj_assoc, hsp_eq]
    exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

/-- Clone `sender_chain` (`+0x290 → +0x544 / +0x300`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_senderChain {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop}
    {localIk' remoteIk' : VecGhost}
    {v40 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x290#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = localIk'.cap) (hx21 : s.readReg64 .x21 = localIk'.ptr)
    (hx22 : s.readReg64 .x22 = remoteIk'.cap) (hx26 : s.readReg64 .x26 = remoteIk'.ptr)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (hx28 : s.readReg64 .x28 = 32#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x544#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      OptSenderChainInline sender' x.st.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          optSenderChainHeap A sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn := CryptoVerification.Cli.LibsignalTripleRatchet.Record.libsignalSessionCode_fnOff_sym_3a4a8
  have hcall := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_senderChainClone_ok_at hsenderClone
  cases hscG : x.G.sender with
  | none =>
    cases hscM : x.st.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      have hnone_cmn : noneCap + 1#64 = 0#64 := by decide
      segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x290 24
      segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x530 20
      clear hfn hcall
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      have hpc_rc :
          (if ¬(BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = true then entry + bv% (768) else entry + bv% (1348)) =
          (if x.st.receiverChains = [] then entry + bv% (1348) else entry + bv% (768)) := by
        rcases eq_nil_or_length_pos x.st.receiverChains with hrc | hrc
        · simp [hrc]
        · have hne : x.st.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
          have hbeq : (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = false :=
            beq_ofNat_zero_eq_false hrc (by omega)
          simp [hne, hbeq]
      apply SepWPp.of_sepWP (mid := if x.st.receiverChains = [] then entry + bv% (1348) else entry + bv% (768))
      wp_steps
      refine SepWP.done (by segCloneKeys_close) hrun ?_
      have hinl : OptSenderChainInline none x.st.senderChain
          (bytes104OfW6Q noneCap bq0 bq1 bq2 bq3 bq4 bq5) := by
        rw [hscM]
        exact OptSenderChainInline.none_of_chunks96 bq0 bq1 bq2 bq3 bq4 bq5
      refine SepWPp.weaken_pre ?_
        (hnext _ none noneCap bq0 bq1 bq2 bq3 bq4 bq5
          (by segCloneKeys_close) hrun rfl hsp hx23 rfl rfl rfl rfl htr hinl)
      rw [hscG, hscM]
      dsimp only [optSenderChainAt, optSenderChainHeap]
      simp only [emp_sepConj, sepConj_emp, hx20, hx21, hx22, hx26, hx28]
      exact Entails.of_eq (by ac_rfl)
    | some sc =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
  | some sg =>
    cases hscM : x.st.senderChain with
    | none =>
      dsimp only [optSenderChainAt]
      exact sepWPp_pure_2nd fun h => False.elim h
    | some sc =>
      rw [optSenderChainAt_some_eq_cap A (s.sp + 0x1c8#64) sg sc]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcap_ne : sg.srk.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcap_beq : (sg.srk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x290 112
      clear hfn
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% ((2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2 ^ 64))
      wp_steps
      refine SepWP.done rfl hrun ?_
      have h1c8 : s.sp + 160#64 + 296#64 = s.sp + 0x1c8#64 := by bv_arith
      refine SepWPp.weaken_pre
        (P' := (memRegion (s.sp + 0x5f0#64) 104 ∗
            optSenderChainAt A (s.sp + 0x1c8#64) (some sg) (some sc) ∗
            A.pool ∗ stackAt s.sp chainCloneStack) ∗
          (chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            ((s.sp + 0x40#64) ↦₆₄ v40) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
            ((s.sp + 0x58#64) ↦₆₄ v58) ∗
            ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ F))
        ?_ ?_
      · rw [optSenderChainAt_some_eq_cap A (s.sp + 0x1c8#64) sg sc]
        simp only [sepConj_assoc]
        rw [show (memRegion (s.sp + 0x5f0#64) 104 ∗
            ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
            ((s.sp + 0x1c8#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A (s.sp + 0x1c8#64) sg sc ∗
            A.pool ∗ stackAt s.sp chainCloneStack ∗
            chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            ((s.sp + 0x40#64) ↦₆₄ v40) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
            ((s.sp + 0x58#64) ↦₆₄ v58) ∗
            ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ F) =
          (A.pool ∗
            ⌜sg.srk.bytes.length ≤ sg.srk.cap.toNat ∧ sg.srk.cap.toNat < 2 ^ 63 ∧ sg.srk.ptr ≠ 0⌝ ∗
            ((s.sp + 0x1c8#64) ↦₆₄ sg.srk.cap) ∗
            optSenderChainSomeRest A (s.sp + 0x1c8#64) sg sc ∗
            chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s.sp + 0x5f0#64) 104 ∗
            ((s.sp + 0x40#64) ↦₆₄ v40) ∗
            ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
            ((s.sp + 0x58#64) ↦₆₄ v58) ∗
            ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
            ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
            ((s.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s.sp chainCloneStack ∗ F) by ac_rfl]
        exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)
      · refine SepWPp.call_frame (x := ⟨s.sp + 0x5f0#64, s.sp + 0x1c8#64, sg, sc⟩)
          hcall rfl hrun hsp
          (ret_pc := entry + bv% (696)) rfl
          rfl ⟨by segCloneKeys_close, by segCloneKeys_close⟩ rfl
          (fun _ _ _ _ h => allowPanic_not_exited h)
          (fun sf _ hm => CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.onPanic_of_callee_panic htr.1 hm)
          fun sf hpcf hrunf hspf hcsm => ?_
        clear hcall
        obtain ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩ := hcsm
        dsimp only [senderChainCloneSpec]
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun htr_sf => ?_
        rw [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun g' => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun ⟨hsrk', hpriv'⟩ => ?_
        have h_sp_call :
            ((((((((s.writeReg64 (Reg.gpr 9#5) (BitVec.zeroExtend 64 x.st.previousCounter)).writeReg64
              (Reg.gpr 8#5) (s.sp + 160#64)).writeReg64 (Reg.gpr 0#5) (s.sp + 1520#64)).writeReg64
              (Reg.gpr 1#5) (s.sp + 456#64)).writeReg64 (Reg.gpr 30#5) (entry + bv% (696))).setPState
              (addsPState64 sg.srk.cap 1#64)).setPC (entry + bv% ((2 ^ 64 + (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as core::clone::Clone>::clone [local#3]") - (ls_off% "libsignal_cli_ratchet::decrypt_signal")) % 2 ^ 64))).setMem m_1).sp = s.sp := rfl
        rw [h_sp_call]
        have hsf_sp : sf.sp = s.sp := hspf
        have hsf23 : sf.readReg64 (Reg.gpr 23#5) = sf.sp + 0x5f0#64 := by rw [hcs23, hsf_sp]; exact hx23
        have hsf20 : sf.readReg64 (Reg.gpr 20#5) = localIk'.cap := hcs20.trans hx20
        have hsf21 : sf.readReg64 (Reg.gpr 21#5) = localIk'.ptr := hcs21.trans hx21
        have hsf28 : sf.readReg64 (Reg.gpr 28#5) = 32#64 := hcs28.trans hx28
        have hsf24 : sf.readReg64 (Reg.gpr 24#5) = s.readReg64 .x24 := hcs24
        have hsf25 : sf.readReg64 (Reg.gpr 25#5) = s.readReg64 .x25 := hcs25
        have hsf29 : sf.readReg64 Reg.fp = s.readReg64 .x29 := hcs29.1
        have hsf_tr : sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 :=
          ⟨htr_sf.trans htr.1, hcs29.2.trans htr.2⟩
        have hsf_spA : sf.spAligned = true := by
          unfold State.spAligned at hsp ⊢; rw [hsf_sp]; exact hsp
        clear hspf hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29 htr_sf
        refine SepWPp.weaken_pre
          (sepConj_mono_left (optSenderChainAt_entails_chunks104W6Q A (s.sp + 0x5f0#64) (some g') (some sc))) ?_
        simp only [sepExists_sepConj_left]
        refine SepWPp.exists_elim fun scCap' =>
          SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
          SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
          SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 => ?_
        simp only [sepConj_assoc]
        refine SepWPp.pure_elim fun hsc_inl => ?_
        have hinl : OptSenderChainInline (some g') x.st.senderChain
            (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) := by
          rw [hscM]; exact hsc_inl
        rw [chunks104W6QAt_sp_0x5f0 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5,
            chunks96_6QAt_sp_0xb40 s.sp bq0 bq1 bq2 bq3 bq4 bq5]
        simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
        have hpc_rc :
            (if (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = true then entry + bv% (1348) else entry + bv% (768)) =
            (if x.st.receiverChains = [] then entry + bv% (1348) else entry + bv% (768)) := by
          rcases eq_nil_or_length_pos x.st.receiverChains with hrc | hrc
          · simp [hrc]
          · have hne : x.st.receiverChains ≠ [] := List.ne_nil_of_length_pos hrc
            have hne0 : BitVec.ofNat 64 x.st.receiverChains.length ≠ 0#64 :=
              ofNat_ne_zero_of_pos hrc (by omega)
            have hbeq : (BitVec.ofNat 64 x.st.receiverChains.length == 0#64) = false :=
              beq_false_of_ne hne0
            simp [hne, hbeq]
        apply SepWPp.of_sepWP
          (mid := if x.st.receiverChains = [] then entry + bv% (1348) else entry + bv% (768))
        wp_steps
        refine SepWP.done (by segCloneKeys_close) hrunf ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ (some g') scCap' sq0 sq1 sq2 sq3 sq4 sq5
            (by segCloneKeys_close) hrunf hsf_sp hsf_spA (by segCloneKeys_close) hsf24 hsf25 rfl hsf29 hsf_tr hinl)
        simp only [hscG, hscM, hsf23, hsf_sp, hsf20, hsf21, hsf28,
            ← chunks96_6QAt_sp_0xb40 s.sp sq0 sq1 sq2 sq3 sq4 sq5,
            pointsTo128_eq_pointsTo64, cat128_extractLsb, BitVec.add_assoc, BitVec.reduceAdd]
        have h104 : ∀ R_tail : SepProp,
            ((s.sp + 0x5f0#64) ↦₆₄ scCap') ∗
              ((s.sp + 1528#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 1536#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
              ((s.sp + 1544#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 1552#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
              ((s.sp + 1560#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 1568#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
              ((s.sp + 1576#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 1584#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
              ((s.sp + 1592#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 1600#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
              ((s.sp + 1608#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 1616#64) ↦₆₄ sq5.extractLsb' 64 64) ∗
              R_tail ⊢
            memRegion (s.sp + 0x5f0#64) 104 ∗ R_tail := by
          intro R_tail
          have h104_eq := congrArg (· ∗ R_tail) (chunks104W6QAt_sp_0x5f0 s.sp scCap' sq0 sq1 sq2 sq3 sq4 sq5)
          simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] at h104_eq
          rw [← h104_eq]
          exact sepConj_mono_left (chunks104W6QAt_entails_memRegion _ _ _ _ _ _ _ _)
        refine Entails.trans (h104 _) ?_
        exact Entails.of_eq (by
          simp only [chunks96_6QAt_sp_0xb40, pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd]
          ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_entry_combined {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1a8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (h19 : s.readReg64 .x19 = x.remA) (h27 : s.readReg64 .x27 = x.sret)
    (h23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (h24 : s.readReg64 .x24 = s.sp + 0xca0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (sv : SpillVals) (dv : DstVals)
      (bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128),
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fc#64 →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.sp + 0xca0#64 →
      s1.readReg64 .x29 = s.readReg64 .x29 → (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          dstSlotsAt s.sp dv ∗
          spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
            sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
          chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x9c#64) ↦₃₂ x.msg.messageVersion.setWidth 32) ∗
          memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
          stackAt s.sp allocHookStack ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest A ctl img x s.sp ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (memRegion s.sp 0xa0 ∗
        ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
        ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        memRegion (s.sp + 0x4b0#64) 0x950 ∗
        protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
        CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_memRegion_0xa0_eq s.sp, segClone_memRegion_0x4b0_0x950_eq s.sp,
      memRegion_0x5f0_0x6b0_eq s.sp, signalMessageAt_eq_ver A x.msgG x.msgA x.msg,
      stackAt_root_eq_chainClone s.sp, stackAt_chainClone_eq_alloc s.sp,
      segClone_vecGhostAt_0x138_eq A x.G.localIk s.sp,
      vecU8Buf_pure_extract A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes]
  simp only [sepConj_assoc]
  refine SepWPp.weaken_pre
    (sepConj_mono (memRegion_0x80_entails_spillSlotsAt s.sp)
      (sepConj_mono_left (memRegion_0x80_0x20_entails s.sp))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v80 => SepWPp.exists_elim fun v88 =>
    SepWPp.exists_elim fun v90 => SepWPp.exists_elim fun v9c =>
    SepWPp.exists_elim fun sv => ?_
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
              x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
            memRegion (s.sp + 0x5b0#64) 0x40 ∗
            memRegion (s.sp + 0xca0#64) 344 ∗
            memRegion (s.sp + 0xb40#64) 96 ∗
            (((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
              ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
              ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
              ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
              ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
              ((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageRestAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨_, hcap_lt, _⟩ => ?_
  refine SepWPp.weaken_pre
    (sepConj_mono (memRegion_0x5b0_0x40_entails s.sp)
      (sepConj_mono (memRegion_344_entails_dstSlotsAt s.sp)
        (sepConj_mono_left (Entails.of_eq (memRegion_96_eq_exists_chunks96_6QAt (s.sp + 0xb40#64)))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun bq0 => SepWPp.exists_elim fun bq1 =>
    SepWPp.exists_elim fun bq2 => SepWPp.exists_elim fun bq3 =>
    SepWPp.exists_elim fun bq4 => SepWPp.exists_elim fun bq5 =>
    SepWPp.exists_elim fun dv =>
    SepWPp.exists_elim fun v5b0 => SepWPp.exists_elim fun v5bc =>
    SepWPp.exists_elim fun v5c0 => SepWPp.exists_elim fun v5c8 =>
    SepWPp.exists_elim fun v5d0 => SepWPp.exists_elim fun v5d8 =>
    SepWPp.exists_elim fun v5e0 => SepWPp.exists_elim fun v5e8 => ?_
  refine SepWPp.weaken_pre
    (P' := ((s.sp + 0x80#64) ↦₆₄ v80) ∗ ((s.sp + 0x88#64) ↦₆₄ v88) ∗
            ((s.sp + 0x90#64) ↦₆₄ v90) ∗ ((s.sp + 0x9c#64) ↦₃₂ v9c) ∗
            ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
            ((s.sp + 0x138#64) ↦₆₄ x.G.localIk.cap) ∗
            ((s.sp + 0x5b0#64) ↦₆₄ v5b0) ∗ ((s.sp + 0x5bc#64) ↦₈ v5bc) ∗
            ((s.sp + 0x5c0#64) ↦₆₄ v5c0) ∗ ((s.sp + 0x5c8#64) ↦₆₄ v5c8) ∗
            ((s.sp + 0x5d0#64) ↦₆₄ v5d0) ∗ ((s.sp + 0x5d8#64) ↦₆₄ v5d8) ∗
            ((s.sp + 0x5e0#64) ↦₆₄ v5e0) ∗ ((s.sp + 0x5e8#64) ↦₆₄ v5e8) ∗
            ((x.msgA + 0x70#64) ↦₈ x.msg.messageVersion) ∗
            (((s.sp + 0x140#64) ↦₆₄ x.G.localIk.ptr) ∗
              ((s.sp + 0x148#64) ↦₆₄ BitVec.ofNat 64 x.G.localIk.bytes.length) ∗
              vecU8Buf A x.G.localIk.cap x.G.localIk.ptr x.G.localIk.bytes ∗
              dstSlotsAt s.sp dv ∗
              spillSlotsAt s.sp sv.v00 sv.v08 sv.v14 sv.v18 sv.v24 sv.v28 sv.v2c
                sv.v30 sv.v3c sv.v40 sv.v48 sv.v54 sv.v58 sv.v60 sv.v68 sv.v70 sv.v78 ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗
              stackAt s.sp allocHookStack ∗
              memRegion (s.sp + 0x98#64) 4 ∗
              ((s.sp + 0x128#64) ↦₆₄ x.prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
              memRegion (s.sp + 0x4b0#64) 48 ∗ memRegion (s.sp + 0x4e0#64) 0xd0 ∗
              memRegion (s.sp + 0x5b8#64) 4 ∗ memRegion (s.sp + 0x5bd#64) 3 ∗
              memRegion (s.sp + 0x658#64) 0x4e8 ∗ memRegion (s.sp + 0xba0#64) 0x100 ∗
              memRegion (s.sp + 0xdf8#64) 8 ∗
              protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
              signalMessageRestAt A x.msgG x.msgA x.msg ∗
              CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
              memRegion (s.sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_entry_to_0x1fc hpc hrun hsp h19 h27 h23 h24 htr hcap_lt
    fun s1 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1 => ?_
  refine SepWPp.weaken_pre ?_
    (hnext s1 sv dv bq0 bq1 bq2 bq3 bq4 bq5 hpc1 hrun1 hsp1 hspA1 hx23_1 hx24_1 hx29_1 htr1)
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fixedRest
  rw [segClone_vecGhostAt_0x138_eq A x.G.localIk s.sp, signalMessageAt_eq_ver A x.msgG x.msgA x.msg]
  exact Entails.of_eq (by ac_rfl)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_fields_1_to_4 {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hsenderClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State}
    {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128}
    {v40 v48 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1fc#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64)
      (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = []
        then (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x544#64
        else (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 →
      s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes →
      localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes →
      remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.st.senderChain
        (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗
          vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
          vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
          optSenderChainHeap A sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗
          ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗
          ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗
          ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
          ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗
        vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
        vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗
        ((s.sp + 0x54#64) ↦₃₂ v54) ∗
        ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s.sp + 0x68#64) ↦₆₄ v68) ∗
        ((s.sp + 0x70#64) ↦₆₄ v70) ∗
        ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s.sp,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      segClone_vecU8At_0x168_root_eq A s.sp x.G.root.cap x.G.root.ptr x.st.rootKey,
      stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧
              x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
            A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
            ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
            ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
            stackAt s.sp allocHookStack ∗
            (((s.sp + 0x150#64) ↦₆₄ x.G.remoteIk.cap) ∗
              ((s.sp + 0x158#64) ↦₆₄ x.G.remoteIk.ptr) ∗
              vecU8Buf A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
              ((s.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s.sp + 0x5f0#64) 104 ∗
              ((s.sp + 0x40#64) ↦₆₄ v40) ∗ ((s.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s.sp + 0x54#64) ↦₃₂ v54) ∗ ((s.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s.sp + 0x60#64) ↦₆₄ v60) ∗ ((s.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s.sp + 0x70#64) ↦₆₄ v70) ∗ ((s.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_localIk hA hpc hrun hsp htr hrem_lt
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗
            ((s1.sp + 0x178#64) ↦₆₄ 32#64) ∗
            stackAt s1.sp allocHookStack ∗
            (vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s1.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗
              ((s1.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
              vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s1.sp + 0x5f0#64) 104 ∗
              ((s1.sp + 0x40#64) ↦₆₄ v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ v48) ∗
              ((s1.sp + 0x54#64) ↦₃₂ v54) ∗ ((s1.sp + 0x58#64) ↦₆₄ v58) ∗
              ((s1.sp + 0x60#64) ↦₆₄ v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ v68) ∗
              ((s1.sp + 0x70#64) ↦₆₄ v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_remoteIk hA hpc1 hrun1 hspA1 hx22_1 htr1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 hrem_b hrem_c => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
            ((s2.sp + 0x48#64) ↦₆₄ v48) ∗
            stackAt s2.sp allocHookStack ∗
            (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
              chunks96_6QAt (s2.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
              memRegion (s2.sp + 0x5f0#64) 104 ∗
              ((s2.sp + 0x40#64) ↦₆₄ v40) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗
              ((s2.sp + 0x58#64) ↦₆₄ v58) ∗ ((s2.sp + 0x60#64) ↦₆₄ v60) ∗
              ((s2.sp + 0x68#64) ↦₆₄ v68) ∗ ((s2.sp + 0x70#64) ↦₆₄ v70) ∗
              ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
              ((s2.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
              ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
              ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
              memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecU8At_0x168_root_eq A s2.sp x.G.root.cap x.G.root.ptr x.st.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_rootKey hA hpc2 hrun2 hspA2 hx28_2 htr2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  rw [← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗
            optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
            chunks96_6QAt (s3.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗
            memRegion (s3.sp + 0x5f0#64) 104 ∗
            ((s3.sp + 0x40#64) ↦₆₄ v40) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗
            ((s3.sp + 0x58#64) ↦₆₄ v58) ∗ ((s3.sp + 0x60#64) ↦₆₄ v60) ∗
            ((s3.sp + 0x68#64) ↦₆₄ v68) ∗ ((s3.sp + 0x70#64) ↦₆₄ v70) ∗
            ((s3.sp + 0x78#64) ↦₆₄ v78) ∗
            ((s3.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
            ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
            stackAt s3.sp chainCloneStack ∗
            (vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗
              vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
              vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
              vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
              vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
              vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗
              ((s3.sp + 0x48#64) ↦₆₄ rootPtr') ∗
              ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  have hx20_3' : s3.readReg64 .x20 = localIk'.cap := by reg_chain
  have hx21_3' : s3.readReg64 .x21 = localIk'.ptr := by reg_chain
  have hx22_3' : s3.readReg64 .x22 = remoteIk'.cap := by reg_chain
  have hx26_3' : s3.readReg64 .x26 = remoteIk'.ptr := by reg_chain
  have hx23_3' : s3.readReg64 .x23 = s3.sp + 0x5f0#64 := by reg_chain
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_senderChain hsenderClone hpc3 hrun3 hspA3 hx20_3' hx21_3' hx22_3' hx26_3' hx23_3' hx28_3 htr3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hinl => ?_
  have hsp_eq : s3.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx23_4 ⊢
  refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by reg_chain) hspA4 hx23_4
      (by reg_chain)
      (by reg_chain)
      hx26_4
      (by reg_chain)
      htr4 hloc_b hloc_c hrem_b hrem_c hinl)

end CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
