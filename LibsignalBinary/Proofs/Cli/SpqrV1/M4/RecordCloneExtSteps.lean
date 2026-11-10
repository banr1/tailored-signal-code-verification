/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.FetchClone
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneChains
import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.SegCloneKeys
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneChains
import LibsignalBinary.Proofs.TripleRatchet.Record.SegCloneKeys
import ProofLib.RegChain

/-!
# 4K-Stack Contract-Backed `SegClone` Field Helpers (Fields 1–7)

Proves 4K-stack `SepWPp` field-clone lemmas for `SessionState` fields 1–7 (`local_identity_key`,
`remote_identity_key`, `root_key`, `sender_chain`, `receiver_chains`, `pending_pre_key`,
`pending_kyber_pre_key`) on `tripleRatchetProgAtExt img.base ext`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalSpqrV1.M4.RecordCloneExtSteps

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.SignalSession.Coins (coinsAt)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

local notation "trP" => tripleRatchetProgAtExt
local notation "trDecName" => CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName
local notation "CliClonePanic" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost
local notation "CliChainCloneOkExt" => CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt
local notation "CliSenderCloneOkExt" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.SenderChainCloneOkExt
local notation "CliSteps_panic_25f8" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x25f8
local notation "CliSteps_panic_2604" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2604
local notation "CliSteps_panic_2610" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2610
local notation "CliSteps_panic_261c" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x261c
local notation "CliSteps_panic_2628" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2628
local notation "CliSteps_panic_2634" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2634
local notation "CliSteps_senderChain" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_senderChain
local notation "CliSteps_rcLoop" =>
  CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_receiverChains_loop

private theorem rce_hfn : libsignalSessionCode.fnOff trDecName =
    num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
  (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")

local macro "rce_gen" b:term:max e:term:max entry:ident prog:ident : tactic =>
  `(tactic| (
    unfold tripleRatchetProgAtExt at *
    generalize_entry (Program.fnAddr (Program.rebase libsignalSessionCode $b (Rust.withPanics $e))
      CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName) = $entry reverting [libsignalSessionCode]
    generalize_entry (Program.rebase libsignalSessionCode $b (Rust.withPanics $e)) =
      $prog reverting [libsignalSessionCode]
    examples_hide_fetches))

private theorem rce_fnAddr_offset_eq (b : BitVec 64) (ext : String → Option (State → State))
    (src dst : String) (k : BitVec 64)
    (hk : BitVec.ofNat 64 (libsignalSessionCode.fnOff src) + k = BitVec.ofNat 64 (libsignalSessionCode.fnOff dst)) :
    (trP b ext).fnAddr src + k = (trP b ext).fnAddr dst := by
  dsimp only [tripleRatchetProgAtExt]; rw [Program.fnAddr_rebase, Program.fnAddr_rebase, BitVec.add_assoc, hk]

theorem rce_segClone_shim_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hshim_fn : subroutine_ok (trP b ext) ((trP b ext).fnAddr shimName) sessionShimSpec) :
    subroutine_ok (trP b ext) ((trP b ext).fnAddr trDecName +
      bv% ((2^64 + ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      sessionShimSpec := by
  rw [rce_fnAddr_offset_eq b ext trDecName shimName _ (by
    rw [rce_hfn, show libsignalSessionCode.fnOff shimName =
      num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2") by fnoff_eq]; bv_omega)]
  exact hshim_fn

theorem rce_segClone_alloc_ok_at {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (halloc_fn : subroutine_ok (trP b ext) ((trP b ext).fnAddr allocName) (rustAllocSpec A)) :
    subroutine_ok (trP b ext) ((trP b ext).fnAddr trDecName +
      bv% ((2^64 + ls_off% "__rustc::__rust_alloc" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (rustAllocSpec A) := by
  rw [rce_fnAddr_offset_eq b ext trDecName allocName _ (by
    rw [rce_hfn, show libsignalSessionCode.fnOff allocName = num% (ls_off% "__rustc::__rust_alloc") by fnoff_eq]; bv_omega)]
  exact halloc_fn

theorem rce_segClone_memcpy4k_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hmemcpy_fn : subroutine_ok (trP b ext) ((trP b ext).fnAddr memcpyName)
      (withStack sessionMemcpyRegionSpec allocHookStack)) :
    subroutine_ok (trP b ext) ((trP b ext).fnAddr trDecName +
      bv% ((2^64 + ls_off% "memcpy" - ls_off% "libsignal_cli_ratchet::decrypt_signal") % 2^64))
      (withStack sessionMemcpyRegionSpec allocHookStack) := by
  rw [rce_fnAddr_offset_eq b ext trDecName memcpyName _ (by
    rw [rce_hfn, show libsignalSessionCode.fnOff memcpyName = num% (ls_off% "memcpy") by fnoff_eq]; bv_omega)]
  exact hmemcpy_fn

structure RceContracts (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  shim_ok : subroutine_ok (trP b ext) ((trP b ext).fnAddr shimName) sessionShimSpec
  alloc_ok : subroutine_ok (trP b ext) ((trP b ext).fnAddr allocName) (rustAllocSpec A)
  memcpy4k_ok : subroutine_ok (trP b ext) ((trP b ext).fnAddr memcpyName)
    (withStack sessionMemcpyRegionSpec allocHookStack)

/-! ## 1. Fields 1–4 (`local_identity_key`, `remote_identity_key`, `root_key`, `sender_chain`) -/

private theorem rce_seg_localIk_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (trP img.base ext).fnAddr trDecName + 0x1fc#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) (hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' : VecGhost),
      s1.pc = (if x.G.remoteIk.bytes = [] then (trP img.base ext).fnAddr trDecName + 0x504#64
        else (trP img.base ext).fnAddr trDecName + 0x238#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = localIk'.cap → s1.readReg64 .x21 = localIk'.ptr →
      s1.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      s1.readReg64 .x23 = s.readReg64 .x23 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes → localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      SepWPp (trP img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗ vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗
          ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CliClonePanic C A ctl uuidTryParse S img x R s0)) :
    SepWPp (trP img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
        ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CliClonePanic C A ctl uuidTryParse S img x R s0) := by
  have hfn := rce_hfn
  have h140 : s.sp + 0x138#64 + 8#64 = s.sp + 0x140#64 := by bv_arith
  have h148 : s.sp + 0x138#64 + 16#64 = s.sp + 0x148#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.localIk.bytes with hloc | hloc
  · rw [vecGhostAt_eq_of_nil A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]; simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1fc 12
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x4f8 12; clear hfn
    rce_gen img.base ext entry prog
    have hpc_rem : (if ¬(BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (568)
        else entry + bv% (1284)) = (if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)) := by
      rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
      · simp [hrem]
      · simp [List.ne_nil_of_length_pos hrem, beq_ofNat_zero_eq_false hrem (by omega)]
    apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)); wp_steps
    refine SepWP.done (by segCloneKeys_close) hrun (SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ (by segCloneKeys_close) hrun rfl hsp rfl rfl rfl rfl rfl rfl rfl htr hloc.symm (by simp [hloc])))
    rw [vecGhostAt_eq_of_nil A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148, vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · rw [vecGhostAt_eq_of_pos A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148]; simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := rce_segClone_shim_ok_at hC.shim_ok; have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
    have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok; dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp), s_p.pc = (trP img.base ext).fnAddr trDecName + 0x25f8#64 →
        s_p.status = .Running → s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (trP img.base ext) ret s_p P_p Q (CliClonePanic C A ctl uuidTryParse S img x R s0) :=
      fun s_p P_p => CliSteps_panic_25f8 x s0 s_p P_p R
    have hloc_lt : x.G.localIk.bytes.length < 2 ^ 63 := by omega
    have hloc_le63 : x.G.localIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hloc_le64 : x.G.localIk.bytes.length ≤ 2 ^ 64 := by omega
    have hloc_ne : BitVec.ofNat 64 x.G.localIk.bytes.length ≠ 0#64 := ofNat_ne_zero_of_pos hloc (by omega)
    have hloc_beq : (BitVec.ofNat 64 x.G.localIk.bytes.length == 0#64) = false := beq_ofNat_zero_eq_false hloc (by omega)
    have hlay : LayoutOk x.G.localIk.bytes.length 1 := ⟨hloc, ⟨0, rfl⟩, hloc_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.localIk.bytes.length).toNat = x.G.localIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1fc 60; clear hfn
    rce_gen img.base ext entry prog
    apply SepWPp.of_sepWP (mid := entry + bv% (540))
    wp_steps; wp_call hshim (); clear hshim; wp_steps; wp_call halloc (x.G.localIk.bytes.length, 1); clear halloc
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]; refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (9720)); wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
    · clear hpanic; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]; refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      have hpc_rem : (if (BitVec.ofNat 64 x.G.remoteIk.bytes.length == 0#64) = true then entry + bv% (1284)
          else entry + bv% (568)) = (if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)) := by
        rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
        · simp [hrem]
        · simp [List.ne_nil_of_length_pos hrem, beq_ofNat_zero_eq_false hrem (by omega)]
      apply SepWPp.of_sepWP (mid := if x.G.remoteIk.bytes = [] then entry + bv% (1284) else entry + bv% (568)); wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.ptr, x.G.localIk.bytes); clear hmemcpy; wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) (SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.localIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.localIk.bytes⟩
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) rfl rfl))
      rw [vecGhostAt_eq_of_pos A x.G.localIk (s.sp + 0x138#64) hloc, h140, h148,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.localIk.bytes hloc hloc_lt hoom64]
      have hsp1_eq : sf_1.sp = s.sp := by segCloneKeys_close
      simp only [sepConj_assoc, hsp1_eq]; exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

private theorem rce_seg_remoteIk_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop} {F : SepProp}
    (hpc : s.pc = (if x.G.remoteIk.bytes = [] then (trP img.base ext).fnAddr trDecName + 0x504#64
      else (trP img.base ext).fnAddr trDecName + 0x238#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 x.G.remoteIk.bytes.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (remoteIk' : VecGhost),
      s1.pc = (trP img.base ext).fnAddr trDecName + 0x268#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = remoteIk'.cap → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = remoteIk'.ptr → s1.readReg64 .x28 = 32#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      remoteIk'.bytes = x.G.remoteIk.bytes → remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      SepWPp (trP img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CliClonePanic C A ctl uuidTryParse S img x R s0)) :
    SepWPp (trP img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗ ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CliClonePanic C A ctl uuidTryParse S img x R s0) := by
  have hfn := rce_hfn
  have h158 : s.sp + 0x150#64 + 8#64 = s.sp + 0x158#64 := by bv_arith
  have h160 : s.sp + 0x150#64 + 16#64 = s.sp + 0x160#64 := by bv_arith
  rcases eq_nil_or_length_pos x.G.remoteIk.bytes with hrem | hrem
  · simp only [hrem, ↓reduceIte] at hpc; rw [hrem] at hx22
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]; simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x504 12; clear hfn
    rce_gen img.base ext entry prog
    apply SepWPp.of_sepWP (mid := entry + bv% (616)); wp_steps
    refine SepWP.done rfl hrun (SepWPp.weaken_pre ?_
      (hnext _ ⟨0#64, 1#64, []⟩ rfl hrun rfl hsp rfl rfl hx22 rfl rfl rfl rfl rfl rfl htr hrem.symm (by simp [hrem])))
    rw [vecGhostAt_eq_of_nil A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160, vecU8Buf_nil_eq A]
    simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact entails_pure_2nd ⟨hcap_lt, hptr⟩ (by ac_rfl)
  · have hrem_ne_nil : x.G.remoteIk.bytes ≠ [] := List.ne_nil_of_length_pos hrem
    simp only [hrem_ne_nil, ↓reduceIte] at hpc
    rw [vecGhostAt_eq_of_pos A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160]; simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
    have hshim := rce_segClone_shim_ok_at hC.shim_ok; have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
    have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok; dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
    have hpanic : ∀ (s_p : State) (P_p : SepProp), s_p.pc = (trP img.base ext).fnAddr trDecName + 0x2604#64 →
        s_p.status = .Running → s_p.trace = s0.trace ++ [allocFailedEvent] →
        SepWPp (trP img.base ext) ret s_p P_p Q (CliClonePanic C A ctl uuidTryParse S img x R s0) :=
      fun s_p P_p => CliSteps_panic_2604 x s0 s_p P_p R
    have hrem_lt : x.G.remoteIk.bytes.length < 2 ^ 63 := by omega
    have hrem_le63 : x.G.remoteIk.bytes.length + 1 ≤ 2 ^ 63 := by omega
    have hrem_le64 : x.G.remoteIk.bytes.length ≤ 2 ^ 64 := by omega
    have hlay : LayoutOk x.G.remoteIk.bytes.length 1 := ⟨hrem, ⟨0, rfl⟩, hrem_le63⟩
    have htoNat : (BitVec.ofNat 64 x.G.remoteIk.bytes.length).toNat = x.G.remoteIk.bytes.length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x238 48; clear hfn
    rce_gen img.base ext entry prog
    apply SepWPp.of_sepWP (mid := entry + bv% (588))
    wp_steps; wp_call hshim (); clear hshim; wp_steps; wp_call halloc (x.G.remoteIk.bytes.length, 1); clear halloc
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
    · clear hmemcpy hnext; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
      simp only [hoom, ite_true, sepConj_assoc]; refine sepWPp_pure_3rd fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (9732)); wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
      exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
    · clear hpanic; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
      simp only [hoom, ite_false, sepConj_assoc]; refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (616)); wp_steps
      wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.ptr, x.G.remoteIk.bytes); clear hmemcpy; wp_steps
      refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) (SepWPp.weaken_pre ?_
        (hnext _ ⟨BitVec.ofNat 64 x.G.remoteIk.bytes.length, sf_1.readReg64 (Reg.gpr 0#5), x.G.remoteIk.bytes⟩
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
          (by segCloneKeys_close) (by segCloneKeys_close) rfl rfl))
      rw [vecGhostAt_eq_of_pos A x.G.remoteIk (s.sp + 0x150#64) hrem, h158, h160,
          vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) x.G.remoteIk.bytes hrem hrem_lt hoom64]
      have hsp1_eq : sf_1.sp = s.sp := by segCloneKeys_close
      simp only [sepConj_assoc, hsp1_eq]; exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

private theorem rce_seg_rootKey_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64}
    {Q : State → SepProp → Prop} {v48 : BitVec 64} {F : SepProp}
    (hpc : s.pc = (trP img.base ext).fnAddr trDecName + 0x268#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx28 : s.readReg64 .x28 = 32#64) (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (rootPtr' : BitVec 64),
      s1.pc = (trP img.base ext).fnAddr trDecName + 0x290#64 → s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x20 = s.readReg64 .x20 → s1.readReg64 .x21 = s.readReg64 .x21 →
      s1.readReg64 .x22 = s.readReg64 .x22 → s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x28 = 32#64 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (trP img.base ext) ret s1
        (A.pool ∗ vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗ ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CliClonePanic C A ctl uuidTryParse S img x R s0)) :
    SepWPp (trP img.base ext) ret s
      (A.pool ∗ vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        ((s.sp + 0x48#64) ↦₆₄ v48) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CliClonePanic C A ctl uuidTryParse S img x R s0) := by
  have hfn := rce_hfn; have hshim := rce_segClone_shim_ok_at hC.shim_ok; have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok; dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
  have hpanic : ∀ (s_p : State) (P_p : SepProp), s_p.pc = (trP img.base ext).fnAddr trDecName + 0x2610#64 →
      s_p.status = .Running → s_p.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp (trP img.base ext) ret s_p P_p Q (CliClonePanic C A ctl uuidTryParse S img x R s0) :=
    fun s_p P_p => CliSteps_panic_2610 x s0 s_p P_p R
  have h170 : s.sp + 0x168#64 + 8#64 = s.sp + 0x170#64 := by bv_arith
  have h178 : s.sp + 0x168#64 + 16#64 = s.sp + 0x178#64 := by bv_arith
  have hroot_len : (keyToBytes32 x.st.rootKey).length = 32 := by simp [keyToBytes32]
  have hroot_pos : 0 < (keyToBytes32 x.st.rootKey).length := by omega
  have hroot_lt : (keyToBytes32 x.st.rootKey).length < 2 ^ 63 := by omega
  have hroot_le64 : (keyToBytes32 x.st.rootKey).length ≤ 2 ^ 64 := by omega
  rw [vecU8At_eq_of_pos A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos, h170, h178]
  simp only [sepConj_assoc]; refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
  have hlay : LayoutOk 32 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x268 40; clear hfn
  rce_gen img.base ext entry prog
  apply SepWPp.of_sepWP (mid := entry + bv% (636))
  wp_steps; wp_call hshim (); clear hshim; wp_steps; wp_call halloc (32, 1); clear halloc
  refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]; refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9744)); wp_steps
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) ?_
    exact hpanic _ _ (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
  · clear hpanic; have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]; refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    have hmem32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        memRegion (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey).length := by rw [hroot_len]
    rw [hmem32]; apply SepWPp.of_sepWP (mid := entry + bv% (656)); wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), x.G.root.ptr, keyToBytes32 x.st.rootKey); clear hmemcpy
    refine SepWP.done (by segCloneKeys_close) (by segCloneKeys_close) (SepWPp.weaken_pre ?_
      (hnext _ (sf_1.readReg64 (Reg.gpr 0#5))
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
        (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close) (by segCloneKeys_close)
        (by segCloneKeys_close) (by segCloneKeys_close)))
    have hbuf32 : vecU8Buf A 32#64 (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey) =
        A.live (sf_1.readReg64 (Reg.gpr 0#5)) 32 1 ∗ (sf_1.readReg64 (Reg.gpr 0#5) ↦ₛ keyToBytes32 x.st.rootKey) := by
      have h := vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) (keyToBytes32 x.st.rootKey) hroot_pos hroot_lt hoom64
      rwa [hroot_len] at h
    rw [vecU8At_eq_of_pos A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) hroot_pos,
        h170, h178, hbuf32]
    have hsp1_eq : sf_1.sp = s.sp := by segCloneKeys_close
    simp only [sepConj_assoc, hsp1_eq]; exact entails_pure_2nd ⟨hlen_le, hcap_lt, hptr⟩ (by ac_rfl)

theorem rce_segClone_fields_1_to_4_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : RceContracts img.base A ext) (hsenderClone : CliSenderCloneOkExt img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {bq0 bq1 bq2 bq3 bq4 bq5 : BitVec 128} {v40 v48 v58 v60 v68 v70 v78 : BitVec 64} {v54 : BitVec 32} {F : SepProp}
    (hpc : s.pc = (trP img.base ext).fnAddr trDecName + 0x1fc#64) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = s.sp + 0x5f0#64) (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hrc_lt : x.st.receiverChains.length < 2 ^ 63)
    (hnext : ∀ (s1 : State) (localIk' remoteIk' : VecGhost) (rootPtr' : BitVec 64)
      (sender' : Option SenderChainGhost) (scCap' : BitVec 64) (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128),
      s1.pc = (if x.st.receiverChains = [] then (trP img.base ext).fnAddr trDecName + 0x544#64
        else (trP img.base ext).fnAddr trDecName + 0x300#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x23 = s.sp + 0x5f0#64 → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = x.st.sessionVersion.setWidth 64 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      localIk'.bytes = x.G.localIk.bytes → localIk'.cap = BitVec.ofNat 64 x.G.localIk.bytes.length →
      remoteIk'.bytes = x.G.remoteIk.bytes → remoteIk'.cap = BitVec.ofNat 64 x.G.remoteIk.bytes.length →
      OptSenderChainInline sender' x.st.senderChain (bytes104OfW6Q scCap' sq0 sq1 sq2 sq3 sq4 sq5) →
      SepWPp (trP img.base ext) ret s1
        (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
          vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
          optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
          vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
          vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗ optSenderChainHeap A sender' x.st.senderChain ∗
          chunks96_6QAt (s.sp + 0xb40#64) sq0 sq1 sq2 sq3 sq4 sq5 ∗ memRegion (s.sp + 0x5f0#64) 104 ∗
          ((s.sp + 0x40#64) ↦₆₄ scCap') ∗ ((s.sp + 0x48#64) ↦₆₄ rootPtr') ∗
          ((s.sp + 0x54#64) ↦₃₂ x.st.previousCounter) ∗ ((s.sp + 0x58#64) ↦₆₄ 32#64) ∗
          ((s.sp + 0x60#64) ↦₆₄ remoteIk'.ptr) ∗ ((s.sp + 0x68#64) ↦₆₄ remoteIk'.cap) ∗
          ((s.sp + 0x70#64) ↦₆₄ localIk'.ptr) ∗ ((s.sp + 0x78#64) ↦₆₄ localIk'.cap) ∗
          ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
          ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
          stackAt s.sp chainCloneStack ∗ F)
        Q (CliClonePanic C A ctl uuidTryParse S img x R s0)) :
    SepWPp (trP img.base ext) ret s
      (A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s.sp + 0x150#64) ∗
        vecU8At A (s.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗ ((s.sp + 0x48#64) ↦₆₄ v48) ∗ ((s.sp + 0x54#64) ↦₃₂ v54) ∗ ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗ ((s.sp + 0x68#64) ↦₆₄ v68) ∗ ((s.sp + 0x70#64) ↦₆₄ v70) ∗ ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        stackAt s.sp chainCloneStack ∗ F)
      Q (CliClonePanic C A ctl uuidTryParse S img x R s0) := by
  rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s.sp,
      vecU8Buf_pure_extract A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes,
      segClone_vecU8At_0x168_root_eq A s.sp x.G.root.cap x.G.root.ptr x.st.rootKey, stackAt_chainClone_eq_alloc s.sp]
  refine SepWPp.weaken_pre
    (P' := ⌜x.G.remoteIk.bytes.length ≤ x.G.remoteIk.cap.toNat ∧ x.G.remoteIk.cap.toNat < 2 ^ 63 ∧ x.G.remoteIk.ptr ≠ 0⌝ ∗
      A.pool ∗ vecGhostAt A x.G.localIk (s.sp + 0x138#64) ∗
      ((s.sp + 0x160#64) ↦₆₄ BitVec.ofNat 64 x.G.remoteIk.bytes.length) ∗
      ((s.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ stackAt s.sp allocHookStack ∗
      (((s.sp + 0x150#64) ↦₆₄ x.G.remoteIk.cap) ∗ ((s.sp + 0x158#64) ↦₆₄ x.G.remoteIk.ptr) ∗
        vecU8Buf A x.G.remoteIk.cap x.G.remoteIk.ptr x.G.remoteIk.bytes ∗
        ((s.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗ ((s.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗ ((s.sp + 0x178#64) ↦₆₄ 32#64) ∗
        vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s.sp + 0x5f0#64) 104 ∗
        ((s.sp + 0x40#64) ↦₆₄ v40) ∗ ((s.sp + 0x48#64) ↦₆₄ v48) ∗ ((s.sp + 0x54#64) ↦₃₂ v54) ∗ ((s.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s.sp + 0x60#64) ↦₆₄ v60) ∗ ((s.sp + 0x68#64) ↦₆₄ v68) ∗ ((s.sp + 0x70#64) ↦₆₄ v70) ∗ ((s.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ memRegion (s.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.pure_elim fun ⟨hlen_rem, hcap_rem, _⟩ => ?_
  refine rce_seg_localIk_4k hC hpc hrun hsp htr (by omega)
    fun s1 localIk' hpc1 hrun1 hsp1 hspA1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx29_1 htr1 hloc_b hloc_c => ?_
  rw [← hsp1]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecGhostAt A x.G.remoteIk (s1.sp + 0x150#64) ∗ ((s1.sp + 0x178#64) ↦₆₄ 32#64) ∗
      stackAt s1.sp allocHookStack ∗ (vecGhostAt A x.G.localIk (s1.sp + 0x138#64) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ ((s1.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗
        ((s1.sp + 0x168#64) ↦₆₄ x.G.root.cap) ∗ ((s1.sp + 0x170#64) ↦₆₄ x.G.root.ptr) ∗
        vecU8Buf A x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        optSenderChainAt A (s1.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s1.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s1.sp + 0x5f0#64) 104 ∗
        ((s1.sp + 0x40#64) ↦₆₄ v40) ∗ ((s1.sp + 0x48#64) ↦₆₄ v48) ∗ ((s1.sp + 0x54#64) ↦₃₂ v54) ∗ ((s1.sp + 0x58#64) ↦₆₄ v58) ∗
        ((s1.sp + 0x60#64) ↦₆₄ v60) ∗ ((s1.sp + 0x68#64) ↦₆₄ v68) ∗ ((s1.sp + 0x70#64) ↦₆₄ v70) ∗ ((s1.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s1.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s1.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ memRegion (s1.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecGhostAt_0x150_eq A x.G.remoteIk s1.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine rce_seg_remoteIk_4k hC hpc1 hrun1 hspA1 hx22_1 htr1
    fun s2 remoteIk' hpc2 hrun2 hsp2 hspA2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 hrem_b hrem_c => ?_
  rw [← hsp2]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ vecU8At A (s2.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
      ((s2.sp + 0x48#64) ↦₆₄ v48) ∗ stackAt s2.sp allocHookStack ∗
      (vecGhostAt A x.G.localIk (s2.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s2.sp + 0x150#64) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
        optSenderChainAt A (s2.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
        chunks96_6QAt (s2.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s2.sp + 0x5f0#64) 104 ∗
        ((s2.sp + 0x40#64) ↦₆₄ v40) ∗ ((s2.sp + 0x54#64) ↦₃₂ v54) ∗ ((s2.sp + 0x58#64) ↦₆₄ v58) ∗ ((s2.sp + 0x60#64) ↦₆₄ v60) ∗
        ((s2.sp + 0x68#64) ↦₆₄ v68) ∗ ((s2.sp + 0x70#64) ↦₆₄ v70) ∗ ((s2.sp + 0x78#64) ↦₆₄ v78) ∗
        ((s2.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
        ((s2.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ ((s2.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗
        memRegion (s2.sp - BitVec.ofNat 64 chainCloneStack) 208 ∗ F))
    (by rw [segClone_vecU8At_0x168_root_eq A s2.sp x.G.root.cap x.G.root.ptr x.st.rootKey]; exact Entails.of_eq (by ac_rfl)) ?_
  refine rce_seg_rootKey_4k hC hpc2 hrun2 hspA2 hx28_2 htr2
    fun s3 rootPtr' hpc3 hrun3 hsp3 hspA3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx28_3 hx29_3 htr3 => ?_
  rw [← hsp3]
  refine SepWPp.weaken_pre
    (P' := A.pool ∗ optSenderChainAt A (s3.sp + 0x1c8#64) x.G.sender x.st.senderChain ∗
      chunks96_6QAt (s3.sp + 0xb40#64) bq0 bq1 bq2 bq3 bq4 bq5 ∗ memRegion (s3.sp + 0x5f0#64) 104 ∗
      ((s3.sp + 0x40#64) ↦₆₄ v40) ∗ ((s3.sp + 0x54#64) ↦₃₂ v54) ∗ ((s3.sp + 0x58#64) ↦₆₄ v58) ∗ ((s3.sp + 0x60#64) ↦₆₄ v60) ∗
      ((s3.sp + 0x68#64) ↦₆₄ v68) ∗ ((s3.sp + 0x70#64) ↦₆₄ v70) ∗ ((s3.sp + 0x78#64) ↦₆₄ v78) ∗
      ((s3.sp + 0x190#64) ↦₆₄ BitVec.ofNat 64 x.st.receiverChains.length) ∗
      ((s3.sp + 0x284#64) ↦₃₂ x.st.previousCounter) ∗ stackAt s3.sp chainCloneStack ∗
      (vecGhostAt A x.G.localIk (s3.sp + 0x138#64) ∗ vecGhostAt A x.G.remoteIk (s3.sp + 0x150#64) ∗
        vecU8At A (s3.sp + 0x168#64) x.G.root.cap x.G.root.ptr (keyToBytes32 x.st.rootKey) ∗
        vecU8Buf A localIk'.cap localIk'.ptr localIk'.bytes ∗ vecU8Buf A remoteIk'.cap remoteIk'.ptr remoteIk'.bytes ∗
        vecU8Buf A 32#64 rootPtr' (keyToBytes32 x.st.rootKey) ∗ ((s3.sp + 0x48#64) ↦₆₄ rootPtr') ∗
        ((s3.sp + 0x280#64) ↦₃₂ x.st.sessionVersion) ∗ F))
    (by rw [stackAt_chainClone_eq_alloc s3.sp]; exact Entails.of_eq (by ac_rfl)) ?_
  refine CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.seg_senderChain
    (localIk' := localIk') (remoteIk' := remoteIk') hsenderClone hpc3 hrun3 hspA3
    (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) hx28_3 htr3 hrc_lt
    fun s4 sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5 hpc4 hrun4 hsp4 hspA4 hx23_4 hx24_4 hx25_4 hx26_4 hx29_4 htr4 hinl => ?_
  have hsp_eq : s3.sp = s.sp := by reg_chain
  rw [hsp_eq] at hx23_4 ⊢
  exact SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
    (hnext s4 localIk' remoteIk' rootPtr' sender' scCap' sq0 sq1 sq2 sq3 sq4 sq5
      hpc4 hrun4 (by reg_chain) hspA4 hx23_4 (by reg_chain) (by reg_chain) hx26_4 (by reg_chain)
      htr4 hloc_b hloc_c hrem_b hrem_c hinl)

/-! ## 2. Fields 5–7 (`receiver_chains`, `pending_pre_key`, `pending_kyber_pre_key`) -/

theorem rce_segClone_receiverChains_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    (hC : RceContracts img.base A ext)
    (hchainClone : CryptoVerification.Cli.LibsignalTripleRatchet.FromRecordChainClone.ChainCloneOkExt img.base A ext)
    (x : RecordDecryptGhost) (R : SepProp) (s0 s : State)
    (ret : BitVec 64) (Q : State → SepProp → Prop) (F : SepProp)
    (hpc : s.pc = (if x.st.receiverChains = [] then
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x544#64
    else
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x300#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hchains_len : x.G.chains.length = x.st.receiverChains.length)
    (hnext : ∀ (s1 : State) (chainsCap' chainsPtr' : BitVec 64) (chains' : List ChainGhost),
      chains'.length = x.st.receiverChains.length →
      chainsCap' = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.pc = (if x.st.receiverChains = [] then
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x548#64
      else
        (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x390#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = BitVec.ofNat 64 x.st.receiverChains.length →
      s1.readReg64 .x28 = chainsPtr' → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
          vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
          vecBuf A 104 8 (chainAt A) chainsCap' chainsPtr' (chains'.zip x.st.receiverChains) ∗
          memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
        vecBuf A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr (x.G.chains.zip x.st.receiverChains) ∗
        memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hshim := rce_segClone_shim_ok_at hC.shim_ok
  have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x261c
    (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x300 56
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x544 4; clear hfn
  cases hrc_eq : x.st.receiverChains with
  | nil =>
    clear hshim halloc hpanic hchainClone
    simp only [hrc_eq, ↓reduceIte, List.length_nil] at hpc hx26 hchains_len ⊢
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    apply SepWPp.of_sepWP (mid := entry + bv% (1352)); wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    refine SepWPp.weaken_pre ?_
      (hnext _ 0#64 8#64 [] (by simp [hrc_eq]) (by simp [hrc_eq])
        (by simp only [hrc_eq, ↓reduceIte]; segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by simp only [hrc_eq, List.length_nil]; segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close))
    simp only [hrc_eq, List.zip_nil_right, segClone_vecBuf_chain_nil_eq]
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hsub := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_receiverChains_loop
      (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) hchainClone x R s0 ret Q
    clear hchainClone
    have hne : x.st.receiverChains ≠ [] := by simp [hrc_eq]
    simp only [hne, ↓reduceIte] at hpc hnext; rw [hrc_eq] at hx26
    cases hgs_eq : x.G.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose := segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
        ((g :: gs_tl).zip (rc :: rcs_tl))
      refine SepWPp.weaken_pre (sepConj_mono_right (sepConj_mono_right (hexpose _))) ?_
      refine sepWPp_pure_3rd fun hmul_lt => ?_
      have hzip_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by simp [hgs_tl]
      rw [hzip_len] at hmul_lt
      have hpos : 0 < (rc :: rcs_tl).length := by simp
      have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
      have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by simp [List.length_cons] at hmul_lt; omega
      have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by simp [List.length_cons] at hmul_lt ⊢; omega
      have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat = (rc :: rcs_tl).length * 104 :=
        segClone_bv_ofNat_mul_104_toNat hmul_lt
      have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 := ⟨hpos_mul, ⟨3, rfl⟩, hsz_le63⟩
      rw [stackAt_chainClone_eq_alloc s.sp]
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (796))
      wp_steps; wp_call hshim (); clear hshim; wp_steps
      wp_call halloc ((rc :: rcs_tl).length * 104, 8); clear halloc
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
      · clear hsub hnext
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
        simp only [hoom, ite_true, sepConj_assoc]
        refine sepWPp_pure_3rd fun htrace => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (9756)); wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
      · clear hpanic
        have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
        simp only [hoom, ite_false, sepConj_assoc]
        refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (824)); wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        have hsf_sp : sf.sp = s.sp := by segCloneChains_close
        have hsf1_sp : sf_1.sp = s.sp := by segCloneChains_close
        set ptr' := sf_1.readReg64 (Reg.gpr 0#5)
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        refine SepWPp.weaken_pre
          (P' := A.pool ∗ arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (sf_1.sp + 0x5f0#64) 104 ∗ stackAt sf_1.sp chainCloneStack ∗
                  (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                    segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗ F))
          (by rw [hsf1_sp, hsf_sp, hptr_zero, ← hsz_eq, stackAt_chainClone_eq_alloc s.sp]; exact Entails.of_eq (by ac_rfl)) ?_
        refine hsub ptr' rcs_tl _ rc g gs_tl x.G.chainsPtr 0#64 _
          hgs_tl (by simpa [List.length_cons] using hmul_lt) hsz_le
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by dsimp only [ptr']; segCloneChains_close) (by segCloneChains_close)
          fun s2 gs' hgs' hpc2 hrun2 hsp2 hspA2 hx24_2 hx25_2 hx26_2 hx28_2 hx29_2 htr2 => ?_
        clear hsub
        dsimp only [Reg.x24, Reg.x25, Reg.x26, Reg.x29] at hx24_2 hx25_2 hx26_2 hx29_2
        simp (config := { decide := true }) only [State.sp_setPC, State.sp_writeReg64_gpr,
          State.readReg64_setPC, State.readReg64_writeReg64, reduceStateReadReg64] at hsp2 hx24_2 hx25_2 hx26_2 hx29_2
        rw [hptr_zero]
        refine SepWPp.weaken_pre ?_
          (hnext s2 (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' gs'
            (by rw [hrc_eq]; exact hgs') (by rw [hrc_eq]) hpc2 hrun2 (by segCloneChains_close) hspA2
            (by segCloneChains_close) (by segCloneChains_close) (by simp only [hrc_eq]; segCloneChains_close)
            hx28_2 (by segCloneChains_close) htr2)
        dsimp only [State.setPC, State.setPState, State.writeReg64]
        simp only [hgs_eq, hrc_eq, hsf1_sp]
        have hreasm := segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A) x.G.chainsCap x.G.chainsPtr
          ((g :: gs_tl).zip (rc :: rcs_tl))
        have hnew_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by simp [hgs']
        have hnew_pos : 0 < (gs'.zip (rc :: rcs_tl)).length := by rw [hnew_len]; exact hpos
        have hnew_lt : (gs'.zip (rc :: rcs_tl)).length * 104 < 2 ^ 63 := by rw [hnew_len]; exact hmul_lt
        have hnew_buf := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl)) hnew_pos hnew_lt hoom64
        rw [hnew_len] at hnew_buf
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 x.G.chainsCap x.G.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rc :: rcs_tl).length * 104) 8 ∗ arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                A.pool ∗ ((s.sp + 0x188#64) ↦₆₄ x.G.chainsPtr) ∗
                memRegion (s.sp + 0x5f0#64) 104 ∗ stackAt s.sp chainCloneStack ∗ F)
          (Entails.of_eq (by ac_rfl)) ?_
        exact Entails.trans (sepConj_mono hreasm (sepConj_mono_left hnew_buf)) (Entails.of_eq (by ac_rfl))

private theorem rce_segClone_pendingPreKey_39c_pos_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gp : TailVecGhost} {tw0 tw1 tw3 tw4 : BitVec 32} {td2 v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (htail : gp.tail.length = 48 - 24)
    (htail_eq : ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
      (((s.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗
        ((s.sp + 0x250#64) ↦₆₄ td2) ∗ ((s.sp + 0x258#64) ↦₃₂ tw3) ∗ ((s.sp + 0x25c#64) ↦₃₂ tw4)))
    (hpos : 0 < gp.vec.bytes.length) (hlen_le : gp.vec.bytes.length ≤ gp.vec.cap.toNat)
    (hcap_lt : gp.vec.cap.toNat < 2 ^ 63) (hptr : gp.vec.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x39c#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x558#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1904#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x3e8#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ (⌜gp.tail.length = 48 - 24⌝ ∗ vecGhostAt A gp.vec (s.sp + 0x230#64) ∗
          ((s.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail)) ∗
          (⌜pendCap' = BitVec.ofNat 64 gp.vec.bytes.length⌝ ∗ vecU8Buf A pendCap' pendPtr' gp.vec.bytes) ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗ ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗ ((s.sp + 0x28#64) ↦₃₂ v28') ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ ((s.sp + 0x230#64) ↦₆₄ gp.vec.cap) ∗ ((s.sp + 0x238#64) ↦₆₄ gp.vec.ptr) ∗
        ((s.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length) ∗ (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
        A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
        memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length) (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
        ((s.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s.sp + 0x24c#64) ↦₃₂ tw1) ∗ ((s.sp + 0x250#64) ↦₆₄ td2) ∗
        ((s.sp + 0x258#64) ↦₃₂ tw3) ∗ ((s.sp + 0x25c#64) ↦₃₂ tw4) ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hshim := rce_segClone_shim_ok_at hC.shim_ok
  have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok
  dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2604
    (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
  have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
  have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gp.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gp.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false := beq_ofNat_zero_eq_false hpos (by omega)
  have hlay : LayoutOk gp.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gp.vec.bytes.length).toNat = gp.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x39c 76; clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (972))
  wp_steps; wp_call hshim (); clear hshim; wp_steps
  wp_call halloc (gp.vec.bytes.length, 1); clear halloc
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9732)); wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1000)); wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gp.vec.ptr, gp.vec.bytes)
    clear hmemcpy; wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneChains_close
    have hsp1_eq : sf_1.sp = s.sp := by segCloneChains_close
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gp.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) td2 tw3 tw0 tw1
        (Or.inr (Or.inr (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
    rw [vecGhostAt_eq_of_pos A gp.vec (s.sp + 0x230#64) hpos, h238, h240, htail_eq,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gp.vec.bytes hpos hlen_lt hoom64,
        segClone_pure_eq_emp (rfl : BitVec.ofNat 64 gp.vec.bytes.length = BitVec.ofNat 64 gp.vec.bytes.length),
        segClone_pure_eq_emp htail, segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩]
    simp only [sepConj_assoc, hsp_eq, hsp1_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

theorem rce_segClone_pendingPreKey_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v08 v18 : BitVec 64} {v24 v28 v2c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (if x.st.receiverChains = [] then
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x548#64
    else
      (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x390#64))
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (pendCap' pendPtr' v08' : BitVec 64) (v24' v28' v2c' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x558#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1904#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x3e8#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x22 = pendCap' → s1.readReg64 .x24 = s.readReg64 .x24 →
      s1.readReg64 .x25 = s.readReg64 .x25 → s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 → s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
          OptPendClone A x.G.pending pendCap' pendPtr' ∗
          ((s.sp + 0x08#64) ↦₆₄ v08') ∗ ((s.sp + 0x18#64) ↦₆₄ pendPtr') ∗
          ((s.sp + 0x24#64) ↦₃₂ v24') ∗ ((s.sp + 0x28#64) ↦₃₂ v28') ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c') ∗
          stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ optTailVecAt A 48 (s.sp + 0x230#64) x.G.pending ∗
        ((s.sp + 0x08#64) ↦₆₄ v08) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗
        ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗ ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x390 40
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x548 16
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x18f4 16; clear hfn
  cases hpend : x.G.pending with
  | none =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, OptPendClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    by_cases hrc : x.st.receiverChains = [] <;> {
      simp only [hrc, ↓reduceIte] at hpc
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      apply SepWPp.of_sepWP (mid := entry + bv% (1368)); wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v18 v08 v24 v28 v2c
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]; simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
    }
  | some gp =>
    rw [hpend] at hnext
    dsimp only [optTailVecAt, OptPendClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun htail => ?_
    obtain ⟨tw0, tw1, td2, tw3, tw4, _, htail_pts⟩ := exists_tail24_decomp htail
    have h238 : s.sp + 0x230#64 + 8#64 = s.sp + 0x238#64 := by bv_arith
    have h240 : s.sp + 0x230#64 + 16#64 = s.sp + 0x240#64 := by bv_arith
    have h248 : s.sp + 0x230#64 + BitVec.ofNat 64 24 = s.sp + 0x248#64 := by bv_arith
    have h24c : s.sp + 0x248#64 + 4#64 = s.sp + 0x24c#64 := by bv_arith
    have h250 : s.sp + 0x248#64 + 8#64 = s.sp + 0x250#64 := by bv_arith
    have h258 : s.sp + 0x248#64 + 16#64 = s.sp + 0x258#64 := by bv_arith
    have h25c : s.sp + 0x248#64 + 20#64 = s.sp + 0x25c#64 := by bv_arith
    rw [h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
    rcases eq_nil_or_length_pos gp.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gp.vec (s.sp + 0x230#64) hnil, h238, h240]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      by_cases hrc : x.st.receiverChains = [] <;> {
        simp only [hrc, ↓reduceIte] at hpc
        unfold tripleRatchetProgAtExt at *
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
        generalize_entry (libsignalSessionCode.rebase img.base
          (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
        examples_hide_fetches
        apply SepWPp.of_sepWP (mid := entry + bv% (6404)); wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 td2 tw3 tw0 tw1
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gp.vec (s.sp + 0x230#64) hnil, h238, h240,
            h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c, hnil, vecU8Buf_nil_eq A,
            h_rfl, segClone_pure_eq_emp htail, segClone_pure_eq_emp ⟨hcap_lt, hptr⟩]
        simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
      }
    · rw [vecGhostAt_eq_of_pos A gp.vec (s.sp + 0x230#64) hpos, h238, h240]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hcmn : gp.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gp.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      have hlen_lt : gp.vec.bytes.length < 2 ^ 63 := by omega
      have hlen_ne : BitVec.ofNat 64 gp.vec.bytes.length ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
      have hlen_beq : (BitVec.ofNat 64 gp.vec.bytes.length == 0#64) = false := beq_ofNat_zero_eq_false hpos (by omega)
      have hsub := fun (s_39c : State) (htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗ ((s_39c.sp + 0x25c#64) ↦₃₂ tw4))) =>
        rce_segClone_pendingPreKey_39c_pos_4k (img := img) (C := C) (A := A) (ctl := ctl)
          (S := S) (ext := ext) hC (x := x) (R := R) (s0 := s0) (s := s_39c) (ret := ret) (Q := Q)
          (gp := gp) (tw0 := tw0) (tw1 := tw1) (tw3 := tw3) (tw4 := tw4) (td2 := td2)
          (v08 := v08) (v18 := v18) (v24 := v24) (v28 := v28) (v2c := v2c) (F := F)
          htail htail_eq_39c hpos hlen_le hcap_lt hptr
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      suffices h_at_39c : ∀ s_39c : State,
          s_39c.pc = entry + bv% (924) → s_39c.status = .Running → s_39c.sp = s.sp → s_39c.spAligned = true →
          s_39c.readReg64 .x24 = s.readReg64 .x24 → s_39c.readReg64 .x25 = s.readReg64 .x25 →
          s_39c.readReg64 .x26 = s.readReg64 .x26 → s_39c.readReg64 .x28 = s.readReg64 .x28 →
          s_39c.readReg64 .x29 = s.readReg64 .x29 →
          (s_39c.trace = s0.trace ∧ calleeSavedVRegs s_39c = calleeSavedVRegs s0) →
          SepWPp prog ret s_39c
            (A.pool ∗ (s_39c.sp + 0x230#64) ↦₆₄ gp.vec.cap ∗ (s_39c.sp + 0x238#64) ↦₆₄ gp.vec.ptr ∗
              (s_39c.sp + 0x240#64) ↦₆₄ BitVec.ofNat 64 gp.vec.bytes.length ∗ (gp.vec.ptr ↦ₛ gp.vec.bytes) ∗
              A.live gp.vec.ptr gp.vec.cap.toNat 1 ∗
              memRegion (gp.vec.ptr + BitVec.ofNat 64 gp.vec.bytes.length) (gp.vec.cap.toNat - gp.vec.bytes.length) ∗
              (s_39c.sp + 0x248#64) ↦₃₂ tw0 ∗ (s_39c.sp + 0x24c#64) ↦₃₂ tw1 ∗ (s_39c.sp + 0x250#64) ↦₆₄ td2 ∗
              (s_39c.sp + 0x258#64) ↦₃₂ tw3 ∗ (s_39c.sp + 0x25c#64) ↦₃₂ tw4 ∗
              (s_39c.sp + 0x08#64) ↦₆₄ v08 ∗ (s_39c.sp + 0x18#64) ↦₆₄ v18 ∗
              (s_39c.sp + 0x24#64) ↦₃₂ v24 ∗ (s_39c.sp + 0x28#64) ↦₃₂ v28 ∗ (s_39c.sp + 0x2c#64) ↦₃₂ v2c ∗
              stackAt s_39c.sp allocHookStack ∗ F)
            Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) by
        clear hsub
        by_cases hrc : x.st.receiverChains = [] <;> {
          simp only [hrc, ↓reduceIte] at hpc
          apply SepWPp.of_sepWP (mid := entry + bv% (924)); wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          exact h_at_39c _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        }
      intro s_39c hpc39c hrun39c hsp39c hspA39c hx24_39c hx25_39c hx26_39c hx28_39c hx29_39c htr39c
      have htail_eq_39c : ((s_39c.sp + 0x230#64 + BitVec.ofNat 64 24) ↦ₛ gp.tail) =
          (((s_39c.sp + 0x248#64) ↦₃₂ tw0) ∗ ((s_39c.sp + 0x24c#64) ↦₃₂ tw1) ∗
            ((s_39c.sp + 0x250#64) ↦₆₄ td2) ∗ ((s_39c.sp + 0x258#64) ↦₃₂ tw3) ∗ ((s_39c.sp + 0x25c#64) ↦₃₂ tw4)) := by
        rw [hsp39c, h248, htail_pts (s.sp + 0x248#64), h24c, h250, h258, h25c]
      refine hsub s_39c htail_eq_39c hpc39c hrun39c hspA39c htr39c
        fun s1 pendCap' pendPtr' v08' v24' v28' v2c' hpc1 hrun1 hsp1 hspA1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub; rw [hsp39c]
      exact hnext s1 pendCap' pendPtr' v08' v24' v28' v2c' hpc1 hrun1 (by reg_chain) hspA1
        hx22_1 (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr1

private theorem rce_segClone_pendingKyber_3f8_pos_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {gk : TailVecGhost} {kw0 kw1 : BitVec 32} {v00 : BitVec 64} {v14 : BitVec 32} {F : SepProp}
    (htail : gk.tail.length = 32 - 24)
    (htail_pts : ∀ a : BitVec 64, (a ↦ₛ gk.tail) = ((a ↦₃₂ kw0) ∗ ((a + 4#64) ↦₃₂ kw1)))
    (hpos : 0 < gk.vec.bytes.length) (hlen_le : gk.vec.bytes.length ≤ gk.vec.cap.toNat)
    (hcap_lt : gk.vec.cap.toNat < 2 ^ 63) (hptr : gk.vec.ptr ≠ 0)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x3f8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x56c#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1920#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x430#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ (⌜gk.tail.length = 32 - 24⌝ ∗ vecGhostAt A gk.vec (s.sp + 0x260#64) ∗
          ((s.sp + 0x260#64 + BitVec.ofNat 64 24) ↦ₛ gk.tail)) ∗
          (⌜kybCap' = BitVec.ofNat 64 gk.vec.bytes.length⌝ ∗ vecU8Buf A kybCap' kybPtr' gk.vec.bytes) ∗
          (s.sp ↦₆₄ kybPtr') ∗ ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ ((s.sp + 0x260#64) ↦₆₄ gk.vec.cap) ∗ ((s.sp + 0x268#64) ↦₆₄ gk.vec.ptr) ∗
        ((s.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length) ∗ (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
        A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
        memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length) (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
        ((s.sp + 0x278#64) ↦₃₂ kw0) ∗ ((s.sp + 0x27c#64) ↦₃₂ kw1) ∗
        (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x14#64) ↦₃₂ v14) ∗
        ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗ stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  have hshim := rce_segClone_shim_ok_at hC.shim_ok
  have halloc := rce_segClone_alloc_ok_at hC.alloc_ok
  have hmemcpy := rce_segClone_memcpy4k_ok_at hC.memcpy4k_ok
  dsimp only [withStack, sessionMemcpyRegionSpec] at hmemcpy
  have hpanic := CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.segClone_panic_0x2634
    (img := img) (C := C) (A := A) (ctl := ctl) (S := S) (ext := ext) (ret := ret) (Q := Q) x s0
  have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
  have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
  have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
  have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
  have hlen_lt : gk.vec.bytes.length < 2 ^ 63 := by omega
  have hlen_le63 : gk.vec.bytes.length + 1 ≤ 2 ^ 63 := by omega
  have hlen_le64 : gk.vec.bytes.length ≤ 2 ^ 64 := by omega
  have hlen_ne : BitVec.ofNat 64 gk.vec.bytes.length ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
  have hlen_beq : (BitVec.ofNat 64 gk.vec.bytes.length == 0#64) = false := beq_ofNat_zero_eq_false hpos (by omega)
  have hlay : LayoutOk gk.vec.bytes.length 1 := ⟨hpos, ⟨0, rfl⟩, hlen_le63⟩
  have htoNat : (BitVec.ofNat 64 gk.vec.bytes.length).toNat = gk.vec.bytes.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x3f8 56; clear hfn
  unfold tripleRatchetProgAtExt at *
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (1052))
  wp_steps; wp_call hshim (); clear hshim; wp_steps
  wp_call halloc (gk.vec.bytes.length, 1); clear halloc
  refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · clear hmemcpy hnext
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_3rd fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (9780)); wp_steps
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    exact hpanic _ _ R (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
  · clear hpanic
    have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_3rd fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (1072)); wp_steps
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), gk.vec.ptr, gk.vec.bytes)
    clear hmemcpy
    refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
    have hsp_eq : sf.sp = s.sp := by segCloneChains_close
    have hsp1_eq : sf_1.sp = s.sp := by segCloneChains_close
    refine SepWPp.weaken_pre ?_
      (hnext _ (BitVec.ofNat 64 gk.vec.bytes.length) (sf_1.readReg64 (Reg.gpr 0#5)) kw0
        (Or.inr (Or.inr (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        (by segCloneChains_close) (by segCloneChains_close))
    rw [vecGhostAt_eq_of_pos A gk.vec (s.sp + 0x260#64) hpos, h268, h270,
        h278, htail_pts (s.sp + 0x278#64), h27c,
        vecU8Buf_pos_eq A (sf_1.readReg64 (Reg.gpr 0#5)) gk.vec.bytes hpos hlen_lt hoom64,
        segClone_pure_eq_emp (rfl : BitVec.ofNat 64 gk.vec.bytes.length = BitVec.ofNat 64 gk.vec.bytes.length),
        segClone_pure_eq_emp htail, segClone_pure_eq_emp ⟨hlen_le, hcap_lt, hptr⟩]
    dsimp only [Reg.x25]
    simp only [sepConj_assoc, hsp_eq, hsp1_eq, emp_sepConj, sepConj_emp]
    exact Entails.of_eq (by ac_rfl)

theorem rce_segClone_pendingKyber_4k {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)} (hC : RceContracts img.base A ext)
    {x : RecordDecryptGhost} {R : SepProp} {s0 s : State} {ret : BitVec 64} {Q : State → SepProp → Prop}
    {v00 : BitVec 64} {v14 v3c : BitVec 32} {F : SepProp}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x558#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1904#64 ∨
           s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x3e8#64)
    (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnext : ∀ (s1 : State) (kybCap' kybPtr' : BitVec 64) (v14' : BitVec 32),
      (s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x56c#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x1920#64 ∨
       s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName + 0x430#64) →
      s1.status = .Running → s1.sp = s.sp → s1.spAligned = true →
      s1.readReg64 .x19 = kybCap' → s1.readReg64 .x22 = s.readReg64 .x22 →
      s1.readReg64 .x24 = s.readReg64 .x24 → s1.readReg64 .x25 = s.readReg64 .x25 →
      s1.readReg64 .x26 = s.readReg64 .x26 → s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s.readReg64 .x29 →
      (s1.trace = s0.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s0) →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret s1
        (A.pool ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗ OptKybClone A x.G.kyber kybCap' kybPtr' ∗
          (s.sp ↦₆₄ kybPtr') ∗ ((s.sp + 0x14#64) ↦₃₂ v14') ∗
          ((s.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32) ∗ stackAt s.sp allocHookStack ∗ F)
        Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0)) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s
      (A.pool ∗ optTailVecAt A 32 (s.sp + 0x260#64) x.G.kyber ∗
        (s.sp ↦₆₄ v00) ∗ ((s.sp + 0x14#64) ↦₃₂ v14) ∗ ((s.sp + 0x3c#64) ↦₃₂ v3c) ∗
        stackAt s.sp allocHookStack ∗ F)
      Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) := by
  have hfn : libsignalSessionCode.fnOff CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName =
      num% (ls_off% "libsignal_cli_ratchet::decrypt_signal") :=
    (ls_lemma% fnOff "libsignal_cli_ratchet::decrypt_signal")
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x3e8 32
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x558 20
  segClone_fetches_cli img.base (Rust.withPanics ext) hfn 0x1904 28; clear hfn
  cases hkyb : x.G.kyber with
  | none =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, OptKybClone, noneCap] at hnext ⊢
    simp only [sepConj_assoc]
    unfold tripleRatchetProgAtExt at *
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
    examples_hide_fetches
    have h_rfl : (⌜(0xffffffffffffffff#64 : BitVec 64) = 0xffffffffffffffff#64⌝ : SepProp) = emp :=
      segClone_pure_eq_emp rfl
    rcases hpc with hpc | hpc | hpc <;> {
      apply SepWPp.of_sepWP (mid := entry + bv% (1388)); wp_steps
      refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
      refine SepWPp.weaken_pre ?_
        (hnext _ 0xffffffffffffffff#64 v00 v14
          (Or.inl (by segCloneChains_close)) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
          (by segCloneChains_close) (by segCloneChains_close))
      rw [h_rfl]; dsimp only [Reg.x25]; simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
    }
  | some gk =>
    rw [hkyb] at hnext
    dsimp only [optTailVecAt, OptKybClone] at hnext ⊢
    simp only [sepConj_assoc]
    refine sepWPp_pure_2nd fun htail => ?_
    obtain ⟨kw0, kw1, _, htail_pts⟩ := exists_unpack32_pair_of_length_8 htail
    have h268 : s.sp + 0x260#64 + 8#64 = s.sp + 0x268#64 := by bv_arith
    have h270 : s.sp + 0x260#64 + 16#64 = s.sp + 0x270#64 := by bv_arith
    have h278 : s.sp + 0x260#64 + BitVec.ofNat 64 24 = s.sp + 0x278#64 := by bv_arith
    have h27c : s.sp + 0x278#64 + 4#64 = s.sp + 0x27c#64 := by bv_arith
    rw [h278, htail_pts (s.sp + 0x278#64), h27c]
    rcases eq_nil_or_length_pos gk.vec.bytes with hnil | hpos
    · rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hcap_lt, hptr⟩ => ?_
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      have h_rfl : (⌜(0#64 : BitVec 64) = BitVec.ofNat 64 ([] : List (BitVec 8)).length⌝ : SepProp) = emp :=
        segClone_pure_eq_emp rfl
      rcases hpc with hpc | hpc | hpc <;> {
        apply SepWPp.of_sepWP (mid := entry + bv% (6432)); wp_steps
        refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
        refine SepWPp.weaken_pre ?_
          (hnext _ 0#64 1#64 kw0
            (Or.inr (Or.inl (by segCloneChains_close))) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close))
        rw [vecGhostAt_eq_of_nil A gk.vec (s.sp + 0x260#64) hnil, h268, h270,
            h278, htail_pts (s.sp + 0x278#64), h27c, hnil, vecU8Buf_nil_eq A,
            h_rfl, segClone_pure_eq_emp htail, segClone_pure_eq_emp ⟨hcap_lt, hptr⟩]
        dsimp only [Reg.x25]; simp only [sepConj_assoc, emp_sepConj, sepConj_emp]; exact Entails.of_eq (by ac_rfl)
      }
    · rw [vecGhostAt_eq_of_pos A gk.vec (s.sp + 0x260#64) hpos, h268, h270]
      simp only [sepConj_assoc]
      refine sepWPp_pure_2nd fun ⟨hlen_le, hcap_lt, hptr⟩ => ?_
      have hsub : ∀ (s_3f8 : State), _ := fun s_3f8 =>
        rce_segClone_pendingKyber_3f8_pos_4k (img := img) (C := C) (A := A) (ctl := ctl)
          (S := S) (ext := ext) hC (x := x) (R := R) (s0 := s0) (s := s_3f8) (ret := ret) (Q := Q)
          (gk := gk) (kw0 := kw0) (kw1 := kw1) (v00 := v00) (v14 := v14) (F := F)
          htail htail_pts hpos hlen_le hcap_lt hptr
      have hcmn : gk.vec.cap + 1#64 ≠ 0#64 := cap_add_one_ne_zero hcap_lt
      have hcmn_beq : (gk.vec.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hcap_lt
      unfold tripleRatchetProgAtExt at *
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.msgDecryptName = entry reverting [libsignalSessionCode]
      generalize_entry (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)) = prog reverting [libsignalSessionCode]
      examples_hide_fetches
      suffices h_at_3f8 : ∀ s_3f8 : State,
          s_3f8.pc = entry + bv% (1016) → s_3f8.status = .Running → s_3f8.sp = s.sp → s_3f8.spAligned = true →
          s_3f8.readReg64 .x22 = s.readReg64 .x22 → s_3f8.readReg64 .x24 = s.readReg64 .x24 →
          s_3f8.readReg64 .x25 = s.readReg64 .x25 → s_3f8.readReg64 .x26 = s.readReg64 .x26 →
          s_3f8.readReg64 .x28 = s.readReg64 .x28 → s_3f8.readReg64 .x29 = s.readReg64 .x29 →
          (s_3f8.trace = s0.trace ∧ calleeSavedVRegs s_3f8 = calleeSavedVRegs s0) →
          SepWPp prog ret s_3f8
            (A.pool ∗ (s_3f8.sp + 0x260#64) ↦₆₄ gk.vec.cap ∗ (s_3f8.sp + 0x268#64) ↦₆₄ gk.vec.ptr ∗
              (s_3f8.sp + 0x270#64) ↦₆₄ BitVec.ofNat 64 gk.vec.bytes.length ∗ (gk.vec.ptr ↦ₛ gk.vec.bytes) ∗
              A.live gk.vec.ptr gk.vec.cap.toNat 1 ∗
              memRegion (gk.vec.ptr + BitVec.ofNat 64 gk.vec.bytes.length) (gk.vec.cap.toNat - gk.vec.bytes.length) ∗
              (s_3f8.sp + 0x278#64) ↦₃₂ kw0 ∗ (s_3f8.sp + 0x27c#64) ↦₃₂ kw1 ∗
              (s_3f8.sp ↦₆₄ v00) ∗ (s_3f8.sp + 0x14#64) ↦₃₂ v14 ∗
              (s_3f8.sp + 0x3c#64) ↦₃₂ (s.readReg64 .x25).truncate 32 ∗ stackAt s_3f8.sp allocHookStack ∗ F)
            Q (CryptoVerification.Cli.LibsignalTripleRatchet.Record.SegCloneSteps.clonePanicPost C A ctl uuidTryParse S img x R s0) by
        clear hsub
        rcases hpc with hpc | hpc | hpc <;> {
          apply SepWPp.of_sepWP (mid := entry + bv% (1016)); wp_steps
          refine SepWP.done (by segCloneChains_close) (by segCloneChains_close) ?_
          dsimp only [Reg.x25] at h_at_3f8
          exact h_at_3f8 _ (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
            (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close) (by segCloneChains_close)
        }
      intro s_3f8 hpc3f8 hrun3f8 hsp3f8 hspA3f8 hx22_3f8 hx24_3f8 hx25_3f8 hx26_3f8 hx28_3f8 hx29_3f8 htr3f8
      rw [← hx25_3f8]
      refine hsub s_3f8 hpc3f8 hrun3f8 hspA3f8 htr3f8
        fun s1 kybCap' kybPtr' v14' hpc1 hrun1 hsp1 hspA1 hx19_1 hx22_1 hx24_1 hx25_1 hx26_1 hx28_1 hx29_1 htr1 => ?_
      clear hsub; rw [hsp3f8, hx25_3f8]
      exact hnext s1 kybCap' kybPtr' v14' hpc1 hrun1 (by reg_chain) hspA1
        hx19_1 (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) (by reg_chain) htr1

end CryptoVerification.Cli.LibsignalSpqrV1.M4.RecordCloneExtSteps
