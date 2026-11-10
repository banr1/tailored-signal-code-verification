/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCalleesDecode
import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.ConsumeMessageKey.GrowOneProofs.GrowOneCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
import GeneratedLean.LibsignalSession -- shake: keep
import GeneratedLean.LibsignalTripleRatchet -- shake: keep
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.InImageCalleesCodeSym
import ProofLib.SepLogic.WPFrozen
import ProofLib.SepLogic.WPp

/-!
# `SessionState` Construction and Key Serialization Callees

Proves `subroutine_ok` on `tripleRatchetProgAt`, `tripleRatchetProgAtExt`, and
`[LibsignalPlacement]` for `<PrivateKey>::serialize`, `<PublicKey>::serialize`,
`<RawVecInner>::finish_grow [local#1]`, `<RawVec<Chain>>::grow_one`, `<SessionState>::new`,
`<SessionState>::with_sender_chain`, `<SessionState>::with_receiver_chain`, and
`<SessionState>::set_unacknowledged_pre_key_message`.
-/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
namespace CryptoVerification.E2E.Pqxdh.Initiator
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh
attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
private abbrev allocHookStack : Nat := 4096
local macro "cells_unfold_fast" : tactic =>
  `(tactic| simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.reduceSub])
@[local simp, local wp_norm, local arm64_norm]
private theorem bytesToBv8_length (bs : Bytes) : (bytesToBv8 bs).length = bs.length :=
    List.length_map _
def rustDeallocBytesSpec (A : RustAlloc) : Spec (BitVec 64 × List (BitVec 8) × Nat × Nat) where
  pre := fun (p, bs, n, align) s =>
    ⌜s.readReg64 .x0 = p ∧ (s.readReg64 .x1).toNat = n ∧ (s.readReg64 .x2).toNat = align ∧
      bs.length = n⌝ ∗ A.pool ∗ A.live p n align ∗ (p ↦ₛ bs) ∗ stackAt s.sp allocHookStack
  post := fun _ s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ A.pool ∗ stackAt s0.sp allocHookStack
theorem dealloc_bytes_ok_at_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff deallocName := by fnoff_eq) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr name +
        BitVec.ofNat 64 k) (rustDeallocBytesSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨p, bs, n, align⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, n, align) s0 ∗ R := by
    unfold rustDeallocBytesSpec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hpre⟩
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpre ⊢
    refine Satisfies.mono ?_ hpre
    rw [← hlen]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion
      p bs)))
  exact ((dealloc_ok_at_trap b C A absHooks hA name k hk).to_outcome
    (p, n, align) R s0 hpc hrun hpre' hsp).mono_outcome fun _ h => h

theorem dealloc_bytes_ok_at {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff deallocName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr name +
        BitVec.ofNat 64 k) (rustDeallocBytesSpec A) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (dealloc_bytes_ok_at_trap hA hk)

private theorem allocFailedIn_of_trace_eq {s0 sm sf : State} (htr : sm.trace = s0.trace)
    (h : allocFailedIn sm sf ∧ sm.trace <+: sf.trace) :
    allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
  rcases h with ⟨ha, hp⟩
  unfold allocFailedIn at ha ⊢
  rw [← htr]
  exact ⟨ha, hp⟩
private theorem stackAt_privKeySerialize (sp : BitVec 64) :
    memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      stackAt (sp - 32#64) allocHookStack ∗ cells (sp - 32#64) 4 := by
  have h1 := stackAt_split_top sp 32 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp allocHookStack 4 (by decide)
  have h3 : (32 + allocHookStack : Nat) = allocHookStack + 8 * 4 := by decide
  have h4 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 4) = 32#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]
def privKeySerializeSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (privKeyPtr, sk, outVecPtr) s =>
    ⌜s.readReg64 .x0 = privKeyPtr ∧ s.readReg64 .x8 = outVecPtr ∧ sk.length = 32⌝ ∗
      (privKeyPtr ↦ₛ sk) ∗ cells outVecPtr 3 ∗
    (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun (privKeyPtr, sk, outVecPtr) s0 sf =>
    ∃∗ bufPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ bufPtr ≠ 0⌝ ∗ (privKeyPtr ↦ₛ sk) ∗
      (outVecPtr ↦₆₄ 32#64) ∗
      ((outVecPtr + 8#64) ↦₆₄ bufPtr) ∗ ((outVecPtr + 16#64) ↦₆₄ 32#64) ∗ (bufPtr ↦ₛ sk) ∗
        A.live bufPtr 32 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOom img
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0
theorem privKeySerialize_base_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr privKeySerializeSym)
      (privKeySerializeSpec A img) := by
  unfold privKeySerializeSpec rustPanicOnOom
  simp only [stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim := shim_ok_at_trap img.base C absHooks privKeySerializeSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA privKeySerializeSym (num% (ls_off% "__rustc::__rust_alloc" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks privKeySerializeSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff privKeySerializeSym = 0x3e7c0 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initPrivKeySerialize img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x3e7c0 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr privKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr privKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨privKeyPtr, sk, outVecPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  obtain ⟨w0, w1, w2, w3, _, hsk_cells⟩ := exists_unpack64_of_length_32 h
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 36#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e7c0))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm =>
      by simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
          ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    simp only [hoom, ite_false, hm32, cells, sepConj_emp, sepExists_sepConj_left,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    rw [hsk_cells (s0.readReg64 (Reg.gpr 0#5))]
    wp_steps
    simp only [hsk_cells, sepConj_assoc]
    wp_done

theorem privKeySerialize_base_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr privKeySerializeSym)
      (privKeySerializeSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (privKeySerialize_base_ok_trap hA)

private theorem memRegion_33_cells_alloc (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64, ∃∗ u3 : BitVec 64, ∃∗ b0 : BitVec 8,
        (a ↦₈ b0) ∗ ((a + 1#64) ↦₆₄ u3) ∗ ((a + 9#64) ↦₆₄ u2) ∗ ((a + 17#64) ↦₆₄ u1) ∗ ((a +
        25#64) ↦₆₄ u0)) := by
  rw [memRegion_split a 1 32 (by decide), memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide), memRegion_one, memRegion_eight,
      memRegion_eight,
    memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
private theorem bytesToBv8_encodeEC_alloc (bs : Bytes) :
    bytesToBv8 (encodeEC bs) = 5#8 :: bytesToBv8 bs := rfl
def ecPubKeySerializeAllocSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes) where
  pre := fun (keyPtr, keyBytes) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32⌝ ∗ (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
    (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun (keyPtr, keyBytes) s0 sf =>
    ∃∗ outPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = outPtr ∧ sf.readReg64 .x1 =
      33#64 ∧ outPtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (outPtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
        A.live outPtr 33 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOom img
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
theorem ecPubKeySerialize_alloc_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeAllocSpec A img) := by
  unfold ecPubKeySerializeAllocSpec rustPanicOnOom
  simp only [bytesToBv8_encodeEC_alloc, stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim := shim_ok_at_trap img.base C absHooks ecPubKeySerializeSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA ecPubKeySerializeSym (num% (ls_off% "__rustc::__rust_alloc" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks ecPubKeySerializeSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff ecPubKeySerializeSym = 0x3e2c4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x3e2c4 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr ecPubKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr ecPubKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_alloc, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_done

theorem ecPubKeySerialize_alloc_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeAllocSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (ecPubKeySerialize_alloc_ok_trap hA)

abbrev finishGrowSym : String := "<alloc::raw_vec::RawVecInner>::finish_grow [local#1]"
abbrev growOneChainSym : String :=
  "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one"
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x15de4
  CryptoVerification.libsignalSessionCode_fnOff_0x15cac
private theorem umulh_104_eq_zero {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    BitVec.truncate 64 ((104#128 * BitVec.zeroExtend 128 new) >>> 64) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_mul, BitVec.toNat_setWidth]
  have h1 : (104#128 : BitVec 128).toNat = 104 := rfl
  have h2 : new.toNat < 2 ^ 128 := by omega
  have h3 : 104 * new.toNat < 2 ^ 128 := by omega
  rw [h1, Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt h3, Nat.shiftRight_eq_div_pow]
  have hdiv : 104 * new.toNat / 2 ^ 64 = 0 := Nat.div_eq_of_lt (by omega)
  rw [hdiv]
  rfl
private theorem mul_104_toNat {new : BitVec 64} (h : new.toNat * 104 < 2 ^ 64) :
    (104#64 * new).toNat = new.toNat * 104 := by
  rw [BitVec.toNat_mul]
  have : (104#64 : BitVec 64).toNat = 104 := rfl
  rw [this, Nat.mul_comm, Nat.mod_eq_of_lt h]
private theorem mul_104_ne_zero {new : BitVec 64} (h0 : 0 < new.toNat) (h : new.toNat * 104 <
    2 ^ 64) : 104#64 * new ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [mul_104_toNat h] at ht
  change new.toNat * 104 = 0 at ht
  omega
private theorem hi_104_eq_false {new : BitVec 64} (h : new.toNat * 104 ≤ 9223372036854775800) :
    (9223372036854775800#64).ult (104#64 * new) = false := by
  rw [BitVec.ult_eq_decide, decide_eq_false_iff_not, mul_104_toNat (by omega)]
  change ¬ (9223372036854775800 < new.toNat * 104)
  omega
private theorem beq_mul_104_zero_eq_false {new : BitVec 64} (h0 : 0 < new.toNat)
    (h : new.toNat * 104 ≤ 9223372036854775800) : (104#64 * new == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  exact mul_104_ne_zero h0 (by omega)
private theorem SepWP.instantiate_post_exists {α : Type _} {prog : Program} {target_pc : BitVec 64}
    {s : State} {P R : SepProp} {Q : State → α → SepProp} {rest : State → Prop} (w : α)
    (h : SepWP prog target_pc s P (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ Q sf w ∗ R) ∧ rest sf)) :
    SepWP prog target_pc s P (fun sf P_f => (sf.mem ⊨ P_f ∗ R → sf.mem ⊨ (∃∗ a, Q sf a) ∗ R) ∧
      rest sf) :=
  SepWP.mono h fun _ _ _ _ ⟨h1, h2⟩ =>
    ⟨fun hm => Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro w)) (h1 hm), h2⟩
abbrev FinishGrowGhost :=
  BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × BitVec 64 × BitVec
    64 × BitVec 64
def finishGrowZeroSpec (A : RustAlloc) : Spec FinishGrowGhost where
  pre := fun (out, cap, ptr, new, bs, o0, o1, o2, fsp) s =>
    ⌜s.readReg64 .x0 = out ∧ s.readReg64 .x1 = cap ∧ s.readReg64 .x2 = ptr ∧
      s.readReg64 .x3 = new ∧ s.readReg64 .x4 = 8#64 ∧ s.readReg64 .x5 = 104#64 ∧
      s.sp = fsp ∧ cap = 0#64 ∧ bs.length = cap.toNat * 104 ∧ cap.toNat ≤ new.toNat ∧ 0 <
        new.toNat ∧ new.toNat * 104 + 8 ≤ 2 ^ 63⌝ ∗
    (out ↦₆₄ o0) ∗ ((out + 8#64) ↦₆₄ o1) ∗ ((out + 16#64) ↦₆₄ o2) ∗ A.pool ∗ cells (fsp - 48#64) 6 ∗
      stackAt (fsp - 48#64) allocHookStack
  post := fun (out, _cap, _ptr, new, _bs, _o0, _o1, _o2, fsp) s0 sf =>
    ∃∗ tag : BitVec 64, ∃∗ p' : BitVec 64, ∃∗ o2' : BitVec 64, (if tag = 1#64 then
        ⌜sf.trace = s0.trace ++ [allocFailedEvent]⌝
       else ⌜tag = 0#64 ∧ p' ≠ 0#64 ∧ sf.trace = s0.trace⌝ ∗ A.live p' (new.toNat * 104) 8 ∗
        memRegion p' (new.toNat * 104)) ∗
      A.pool ∗ cells (fsp - 48#64) 6 ∗ stackAt (fsp - 48#64) allocHookStack ∗
      (out ↦₆₄ tag) ∗ ((out + 8#64) ↦₆₄ p') ∗ ((out + 16#64) ↦₆₄ o2')
theorem finishGrowZero_ok_trap {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt b C absHooks)
      ((trTrapProgAt b C absHooks).fnAddr finishGrowSym)
      (finishGrowZeroSpec A) := by
  unfold finishGrowZeroSpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowSym = 0x15de4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x15de4
  have hshim := shim_ok_at_trap b C absHooks finishGrowSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15de4))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap b C A absHooks hA finishGrowSym (num% (ls_off% "__rustc::__rust_alloc" - 0x15de4))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x15de4 180
  dsimp only [trTrapProgAt] at hshim halloc ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr finishGrowSym = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics (trTrapExterns C absHooks))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  subst cap
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcbz := beq_mul_104_zero_eq_false h_11 h
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat * 104, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

theorem finishGrowZero_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt b C ctl absHooks)
      ((tripleRatchetProgAt b C ctl absHooks).fnAddr finishGrowSym)
      (finishGrowZeroSpec A) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (finishGrowZero_ok_trap hA)

def growOneChainZeroSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (vecPtr, oldPtr) s =>
    ⌜s.readReg64 .x0 = vecPtr⌝ ∗ (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool ∗
      cells (s.sp - 64#64) 8 ∗
    cells (s.sp - 112#64) 6 ∗ stackAt (s.sp - 112#64) allocHookStack
  post := fun (vecPtr, _oldPtr) s0 sf =>
    ∃∗ newPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗ (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr +
      8#64) ↦₆₄ newPtr) ∗ A.live newPtr 416 8 ∗
      memRegion newPtr 416 ∗ A.pool ∗ cells (s0.sp - 64#64) 8 ∗ cells (s0.sp - 112#64) 6 ∗
        stackAt (s0.sp - 112#64) allocHookStack
  onPanic := rustPanicOnOom img
theorem growOneChain_zero_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr growOneChainSym)
      (growOneChainZeroSpec A img) := by
  unfold growOneChainZeroSpec rustPanicOnOom
  cells_unfold
  have hfn : libsignalSessionCode.fnOff growOneChainSym = 0x15cac :=
    CryptoVerification.libsignalSessionCode_fnOff_0x15cac
  have hpanic := panic_at_handle_error_trap img.base C absHooks growOneChainSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x15cac))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := subroutine_ok_rel_pqxdh_trap
    (finishGrowZero_ok_trap (b := img.base) (C := C) (absHooks := absHooks) hA)
    CryptoVerification.libsignalSessionCode_fnOff_0x15de4 hfn (k := 312) (by decide)
  simp only [finishGrowZeroSpec, cells, sepExists_sepConj_right, sepConj_emp, bv_sub_add_lit',
    BitVec.reduceSub] at hfg0
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x15cac 104
  dsimp only [trTrapProgAt] at hpanic hfg0 ⊢
  clear hfn hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr growOneChainSym = entry
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨vecPtr, oldPtr⟩ := x
  dsimp only at *
  subst h
  apply SepWPp.of_sepWP (mid := entry + 60#64)
  wp_steps
  wp_call hfg0 (s0.sp - 56#64, 0#64, oldPtr, 4#64, [], v_stk_7, v_stk_8, v_stk_9, s0.sp - 64#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases htag : w = 1#64
  · simp only [htag, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x15cac))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm,
        *])) hm
  · simp only [htag, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem growOneChain_zero_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr growOneChainSym)
      (growOneChainZeroSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (growOneChain_zero_ok_trap hA)

section SessionStateNew
abbrev sessionStateNewSym : String := "<libsignal_protocol::state::session::SessionState>::new"
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x125a4
private theorem stackAt_sessionStateNew_entry (sp : BitVec 64) :
    memRegion (sp - 4224#64) 128 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 4224#64) 32 ∗ stackAt (sp - 96#64) allocHookStack) ∗ cells (sp - 96#64) 12 :=
        by
  have h1 := stackAt_split_top sp 128 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 12 (by decide)
  have h3 := stackAt_split_top (sp - 96#64) 32 allocHookStack (by decide)
  have h4 : (128 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 12 := by decide
  have h5 : BitVec.ofNat 64 (128 + allocHookStack) = 4224#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 12) = 96#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h8 : sp - 96#64 - 4128#64 = sp - 4224#64 := by bv_arith
  rw [h5] at h1
  rw [h6] at h2
  rw [h7, h8] at h3
  rw [← h1, h4, h2, ← h3]
private theorem memRegion_344_sessionStateNew_split (outPtr : BitVec 64) :
    memRegion outPtr 344 =
      cells outPtr 19 ∗ memRegion (outPtr + 0x98#64) 96 ∗ (∃∗ u_f8 : BitVec 64, (outPtr +
        0xf8#64) ↦₆₄ u_f8) ∗
      memRegion (outPtr + 0x100#64) 40 ∗ (∃∗ u_128 : BitVec 64, (outPtr + 0x128#64) ↦₆₄ u_128) ∗
        memRegion (outPtr + 0x130#64) 24 ∗
      (∃∗ u_148 : BitVec 32, (outPtr + 0x148#64) ↦₃₂ u_148) ∗ (∃∗ u_14c : BitVec 64, (outPtr +
        0x14c#64) ↦₆₄ u_14c) ∗
      (∃∗ u_154 : BitVec 32, (outPtr + 0x154#64) ↦₃₂ u_154) := by
  rw [memRegion_split outPtr 152 192 (by decide), memRegion_cells outPtr 19 (by decide),
    memRegion_split (outPtr + 152#64) 96 96 (by decide), memRegion_split (outPtr + 152#64 +
      96#64) 8 88 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64), memRegion_split (outPtr + 152#64 + 96#64 +
      8#64) 40 48 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64) 8 40 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64) 24 16 (by decide),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64) 4 12 (by decide),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64),
    memRegion_split (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64) 8 4 (by decide),
    ProofLib.memRegion_eight (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64),
    memRegion_four (outPtr + 152#64 + 96#64 + 8#64 + 40#64 + 8#64 + 24#64 + 4#64 + 8#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
private theorem fnAddr_ecPubKeySerialize_from_sessionStateNew_trap (b : BitVec 64)
    (C : Crypto) (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr sessionStateNewSym + 179488#64 =
      (trTrapProgAt b C absHooks).fnAddr ecPubKeySerializeSym := by
  simp only [trTrapProgAt, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4]
  bv_arith

private theorem fnAddr_ecPubKeySerialize_from_sessionStateNew (b : BitVec 64)
    (C : Crypto) (ctl : BitVec 64) (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr sessionStateNewSym + 179488#64 =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr ecPubKeySerializeSym := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_ecPubKeySerialize_from_sessionStateNew_trap b C absHooks)

structure SessionStateNewGhost where
  outPtr : BitVec 64
  version : BitVec 32
  localIkPtr : BitVec 64
  localIk32 : Bytes
  remoteIkPtr : BitVec 64
  remoteIk32 : Bytes
  rootKeyPtr : BitVec 64
  rootKey32 : Bytes
  baseKeyPtr : BitVec 64
  baseKey32 : Bytes
  spqrVecPtr : BitVec 64
  spqrCap : BitVec 64
  spqrBufPtr : BitVec 64
  spqrLen : BitVec 64
def sessionStateNewSpec (A : RustAlloc) (img : Obj.Image) : Spec SessionStateNewGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg32 .x0 = g.version ∧ s.readReg64 .x1 = g.localIkPtr ∧
      s.readReg64 .x2 = g.remoteIkPtr ∧
      s.readReg64 .x3 = g.rootKeyPtr ∧ s.readReg64 .x4 = g.baseKeyPtr ∧ s.readReg64 .x5 =
        g.spqrVecPtr ∧ g.localIk32.length = 32 ∧
      g.remoteIk32.length = 32 ∧ g.rootKey32.length = 32 ∧ g.baseKey32.length = 32⌝ ∗
        (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗
    (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗ (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
    (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.spqrVecPtr +
      0x10#64) ↦₆₄ g.spqrLen) ∗
    memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4224#64) 128 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64, ∃∗ rootKeyBoxPtr : BitVec 64, ∃∗
      baseKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧
        baseKeyBoxPtr ≠ 0⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
        (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗ (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr +
        0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗
        (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.localIk32)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.remoteIk32)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC g.baseKey32)) ∗ A.live baseKeyBoxPtr 33 1 ∗
        (g.outPtr ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x08#64) ↦₆₄ localIkBoxPtr) ∗ ((g.outPtr + 0x10#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x18#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x20#64) ↦₆₄ remoteIkBoxPtr) ∗ ((g.outPtr + 0x28#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x30#64) ↦₆₄ 32#64) ∗
      ((g.outPtr + 0x38#64) ↦₆₄ rootKeyBoxPtr) ∗ ((g.outPtr + 0x40#64) ↦₆₄ 32#64) ∗ ((g.outPtr +
        0x48#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x50#64) ↦₆₄ 8#64) ∗ ((g.outPtr + 0x58#64) ↦₆₄ 0#64) ∗ ((g.outPtr +
        0x60#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x68#64) ↦₆₄ baseKeyBoxPtr) ∗ ((g.outPtr + 0x70#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x78#64) ↦₆₄ g.spqrCap) ∗
      ((g.outPtr + 0x80#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.outPtr + 0x88#64) ↦₆₄ g.spqrLen) ∗ ((g.outPtr +
        0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.outPtr + 0x98#64) 96 ∗ ((g.outPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        memRegion (g.outPtr + 0x100#64) 40 ∗
      ((g.outPtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x130#64) 24 ∗
      ((g.outPtr + 0x148#64) ↦₃₂ (BitVec.ofNat 32 (g.version.toNat % 256))) ∗ ((g.outPtr +
        0x14c#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x154#64) ↦₃₂ 0#32) ∗ (memRegion (s0.sp - 4224#64) 128 ∗
        stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOom img
theorem sessionStateNew_base_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr sessionStateNewSym)
      (sessionStateNewSpec A img) := by
  unfold sessionStateNewSpec rustPanicOnOom
  simp only [stackAt_sessionStateNew_entry, memRegion_344_sessionStateNew_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr sessionStateNewSym + 179488#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_sessionStateNew_trap img.base C absHooks).symm ▸
      ecPubKeySerialize_alloc_ok_trap (img := img) hA
  have hshim := shim_ok_at_trap img.base C absHooks sessionStateNewSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA sessionStateNewSym (num% (ls_off% "__rustc::__rust_alloc" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks sessionStateNewSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff sessionStateNewSym = 0x125a4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x125a4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.sessionStateNew img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x125a4 252
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr sessionStateNewSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hser hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr sessionStateNewSym = entry
  examples_hide_fetches
  rcases g with ⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4 h_5 h_6 h_7
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by simp [bytesToBv8, h_10]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 179488#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), localIk32)) hser
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := entry + 60#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    h_8 (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
  simp only [arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29⟩
  simp only [arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
  clear hpre
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_local⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 179488#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 2#5), remoteIk32)) hser
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hspm1, hsp_align])
    (ret_pc := entry + 76#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [arm64_norm, hspm1, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    h_9 (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
        htr1]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
  simp only [arm64_norm, hspm1] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29⟩
  simp only [arm64_norm, hcs1_19, hcs1_20, hcs1_21, hcs1_24, hcs1_25]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hspm1, htr1, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
      sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_2, hx1_2, hne_remote⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 100#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    conv =>
      arg 4
      simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x125a4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = sm2.trace›, htr2])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32, cells, sepConj_emp,
        sepExists_sepConj_left,
        sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
    apply SepWPp.of_sepWP (mid := entry + 179488#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 4#5), baseKey32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 128#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
          htrace, ‹sf.trace = sm2.trace›, htr2]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
      hcs3_27, hcs3_28, hcs3_29⟩
    simp only [*, arm64_norm]
      at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr3, hx0_3, hx1_3, hne_base⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [hrk_cells, sepConj_assoc]
    wp_done

theorem sessionStateNew_base_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr sessionStateNewSym)
      (sessionStateNewSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (sessionStateNew_base_ok_trap hA)

end SessionStateNew
section WithSenderChain
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x117e8
theorem fnAddr_ecPubKeySerialize_from_withSenderChain_trap (b : BitVec 64) (C : Crypto)
    (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr ecPubKeySerializeSym =
      (trTrapProgAt b C absHooks).fnAddr withSenderChainSym + 183004#64 := by
  dsimp only [trTrapProgAt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      CryptoVerification.libsignalSessionCode_fnOff_0x117e8]
  bv_omega

theorem fnAddr_ecPubKeySerialize_from_withSenderChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr withSenderChainSym + 183004#64 := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_ecPubKeySerialize_from_withSenderChain_trap b C absHooks)

theorem fnAddr_privKeySerialize_from_withSenderChain_trap (b : BitVec 64) (C : Crypto)
    (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr privKeySerializeSym =
      (trTrapProgAt b C absHooks).fnAddr withSenderChainSym + 184280#64 := by
  dsimp only [trTrapProgAt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      CryptoVerification.libsignalSessionCode_fnOff_0x117e8]
  bv_omega

theorem fnAddr_privKeySerialize_from_withSenderChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr privKeySerializeSym =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr withSenderChainSym + 184280#64 := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_privKeySerialize_from_withSenderChain_trap b C absHooks)

private theorem stackAt_withSenderChain_entry (sp : BitVec 64) :
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack =
      (memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack) ∗ cells (sp -
        128#64) 16 := by
  have h1 := stackAt_split_top sp 160 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (32 + allocHookStack) 16 (by decide)
  have h3 := stackAt_split_top (sp - 128#64) 32 allocHookStack (by decide)
  have h4 : (160 + allocHookStack : Nat) = (32 + allocHookStack) + 8 * 16 := by decide
  have h5 : BitVec.ofNat 64 (160 + allocHookStack) = 4256#64 := rfl
  have h6 : BitVec.ofNat 64 (8 * 16) = 128#64 := rfl
  have h7 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  rw [h5] at h1
  rw [h6] at h2
  rw [h7] at h3
  rw [← h1, h4, h2, ← h3]
private theorem memRegion_92_senderChain_split (ptr : BitVec 64) :
    memRegion (ptr + 0x98#64) 92 =
      cells (ptr + 0x98#64) 11 ∗ (∃∗ v : BitVec 32, (ptr + 0xf0#64) ↦₃₂ v) := by
  have hsplit : memRegion (ptr + 0x98#64) 92 =
      memRegion (ptr + 0x98#64) 88 ∗ memRegion (ptr + 0x98#64 + BitVec.ofNat 64 88) 4 :=
    memRegion_split (ptr + 0x98#64) 88 4 (by decide)
  have haddr : ptr + 0x98#64 + BitVec.ofNat 64 88 = ptr + 0xf0#64 := by bv_omega
  rw [hsplit, memRegion_cells (ptr + 0x98#64) 11 (by decide), haddr, ProofLib.memRegion_four]
def senderChainBytes100 (pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32) : List (BitVec 8) :=
  unpack64 33#64 ++ (unpack64 pubPtr ++ (unpack64 33#64 ++ (unpack64 32#64 ++ (unpack64 privPtr ++
  (unpack64 32#64 ++ (unpack64 0#64 ++ (unpack64 8#64 ++ (unpack64 0#64 ++ (unpack64 32#64 ++
  (unpack64 ckPtr ++ (unpack64 32#64 ++ unpack32 idx)))))))))))
@[simp]
theorem senderChainBytes100_length (pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32) :
    (senderChainBytes100 pubPtr privPtr ckPtr idx).length = 100 := by
  simp [senderChainBytes100, unpack64, unpack32]
def senderChainFieldsAt (ptr pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32) : SepProp :=
  ((ptr + 0x90#64) ↦₆₄ 33#64) ∗ ((ptr + 0x98#64) ↦₆₄ pubPtr) ∗ ((ptr + 0xa0#64) ↦₆₄ 33#64) ∗ ((ptr +
    0xa8#64) ↦₆₄ 32#64) ∗
  ((ptr + 0xb0#64) ↦₆₄ privPtr) ∗ ((ptr + 0xb8#64) ↦₆₄ 32#64) ∗ ((ptr + 0xc0#64) ↦₆₄ 0#64) ∗ ((ptr +
    0xc8#64) ↦₆₄ 8#64) ∗
  ((ptr + 0xd0#64) ↦₆₄ 0#64) ∗ ((ptr + 0xd8#64) ↦₆₄ 32#64) ∗ ((ptr + 0xe0#64) ↦₆₄ ckPtr) ∗ ((ptr +
    0xe8#64) ↦₆₄ 32#64) ∗
  ((ptr + 0xf0#64) ↦₃₂ idx)
theorem senderChainFieldsAt_eq_pointsToBytes
    (ptr pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32) :
    senderChainFieldsAt ptr pubPtr privPtr ckPtr idx =
      ((ptr + 0x90#64) ↦ₛ senderChainBytes100 pubPtr privPtr ckPtr idx) := by
  unfold senderChainFieldsAt senderChainBytes100
  simp only [pointsTo64_eq_pointsToBytes, pointsTo32_eq_pointsToBytes, pointsToBytes_append,
    unpack64_length, BitVec.add_assoc, BitVec.reduceAdd]
theorem withSenderChain_pack344 (ptr pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32)
    (pre144 post100 : List (BitVec 8)) (hpre : pre144.length = 144) :
    (ptr ↦ₛ pre144) ∗ senderChainFieldsAt ptr pubPtr privPtr ckPtr idx ∗ ((ptr +
      0xf4#64) ↦ₛ post100) =
      (ptr ↦ₛ (pre144 ++ (senderChainBytes100 pubPtr privPtr ckPtr idx ++ post100))) := by
  rw [senderChainFieldsAt_eq_pointsToBytes, pointsToBytes_append, pointsToBytes_append, hpre,
    senderChainBytes100_length]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem withSenderChain_pack344_unfolded (ptr pubPtr privPtr ckPtr : BitVec 64) (idx : BitVec 32)
    (pre144 post100 : List (BitVec 8)) (hpre : pre144.length = 144) :
    (ptr ↦ₛ pre144) ∗ ((ptr + 0x90#64) ↦₆₄ 33#64) ∗ ((ptr + 0x98#64) ↦₆₄ pubPtr) ∗ ((ptr +
      0xa0#64) ↦₆₄ 33#64) ∗
    ((ptr + 0xa8#64) ↦₆₄ 32#64) ∗ ((ptr + 0xb0#64) ↦₆₄ privPtr) ∗ ((ptr + 0xb8#64) ↦₆₄ 32#64) ∗
      ((ptr + 0xc0#64) ↦₆₄ 0#64) ∗
    ((ptr + 0xc8#64) ↦₆₄ 8#64) ∗ ((ptr + 0xd0#64) ↦₆₄ 0#64) ∗ ((ptr + 0xd8#64) ↦₆₄ 32#64) ∗ ((ptr +
      0xe0#64) ↦₆₄ ckPtr) ∗
    ((ptr + 0xe8#64) ↦₆₄ 32#64) ∗ ((ptr + 0xf0#64) ↦₃₂ idx) ∗ ((ptr + 0xf4#64) ↦ₛ post100) =
      (ptr ↦ₛ (pre144 ++ (senderChainBytes100 pubPtr privPtr ckPtr idx ++ post100))) := by
  simpa only [senderChainFieldsAt, sepConj_assoc] using
    withSenderChain_pack344 ptr pubPtr privPtr ckPtr idx pre144 post100 hpre
private theorem sepWP_focus {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q : State → SepProp → Prop}
    (hf : P = T ∗ F) (h : SepWP prog ret s (T ∗ F) Q) : SepWP prog ret s P Q :=
  hf ▸ h
private theorem cells_three_entails (sp : BitVec 64) (v0 v1 v2 : BitVec 64) :
    ((sp - 120#64) ↦₆₄ v0 ∗ (sp - 112#64) ↦₆₄ v1 ∗ (sp - 104#64) ↦₆₄ v2) ⊢
      cells (sp - 120#64) 3 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.refl _)))
structure WithSenderChainGhost where
  outPtr              : BitVec 64
  inPtr               : BitVec 64
  senderKeyPairPtr    : BitVec 64
  senderRatchetPub32  : Bytes
  senderRatchetPriv32 : Bytes
  senderChainKeyPtr   : BitVec 64
  senderChainKey32    : Bytes
  senderChainIdx      : BitVec 32
  pre144              : List (BitVec 8)
  post100             : List (BitVec 8)
def withSenderChainNoneSpec (A : RustAlloc) (img : Obj.Image) :
    Spec WithSenderChainGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x1 = g.senderKeyPairPtr ∧
      s.readReg64 .x2 = g.senderChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.senderRatchetPriv32.length = 32 ∧
        g.senderChainKey32.length = 32 ∧ g.pre144.length = 144 ∧
      g.post100.length = 100⌝ ∗ (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
    ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
    ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗ (g.inPtr ↦ₛ g.pre144) ∗ ((g.inPtr +
      0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (g.inPtr + 0x98#64) 92 ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗ memRegion g.outPtr 344 ∗
    (memRegion (s.sp - 4256#64) 160 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ senderRatchetPubBoxPtr : BitVec 64, ∃∗ senderRatchetPrivBoxPtr : BitVec 64, ∃∗
      senderChainKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ senderRatchetPubBoxPtr ≠ 0 ∧ senderRatchetPrivBoxPtr ≠ 0 ∧
        senderChainKeyBoxPtr ≠ 0⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗ ((g.senderKeyPairPtr +
        32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ ((g.senderChainKeyPtr +
        32#64) ↦₃₂ g.senderChainIdx) ∗
      (senderRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
        A.live senderRatchetPubBoxPtr 33 1 ∗
      (senderRatchetPrivBoxPtr ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
        A.live senderRatchetPrivBoxPtr 32 1 ∗
      (senderChainKeyBoxPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ A.live senderChainKeyBoxPtr 32 1 ∗
        (g.outPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.outPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.outPtr + 0xf4#64) ↦ₛ g.post100) ∗
        (g.inPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.inPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (memRegion (s0.sp - 4256#64) 160 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOom img
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_adds_neg1_1 :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide
theorem withSenderChain_none_base_ok_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr withSenderChainSym)
      (withSenderChainNoneSpec A img) := by
  unfold withSenderChainNoneSpec rustPanicOnOom
  simp only [stackAt_withSenderChain_entry, memRegion_92_senderChain_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr withSenderChainSym + 183004#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_withSenderChain_trap img.base C absHooks).symm ▸
      ecPubKeySerialize_alloc_ok_trap (img := img) hA
  have hpser :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr withSenderChainSym + 184280#64)
        (privKeySerializeSpec A img) :=
    (fnAddr_privKeySerialize_from_withSenderChain_trap img.base C absHooks).symm ▸
      privKeySerialize_base_ok_trap (img := img) hA
  have hshim := shim_ok_at_trap img.base C absHooks withSenderChainSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA withSenderChainSym (num% (ls_off% "__rustc::__rust_alloc" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := dealloc_bytes_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    hA (name := withSenderChainSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := session_memcpy_region_ok_at_trap img.base C absHooks withSenderChainSym (num% (ls_off% "memcpy" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks withSenderChainSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff withSenderChainSym = 0x117e8 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initWithSenderChain img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x117e8 524
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr withSenderChainSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hser hpser hshim halloc hdealloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr withSenderChainSym = entry
  rcases g with ⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by simp [bytesToBv8, h_7]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 128#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP (mid := entry + 183004#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h_5
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 144#64)
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [h_5]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP (mid := entry + 184280#64)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by simp [bytesToBv8, h_6]
      refine SepWPp.fold (cells_three_entails s0.sp _ _ _) (by sep_focus) ?_
      refine SepWPp.call_frame
        (x := (s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp -
        120#64)) hpser
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := entry + 176#64) (by wp_norm_lhs)
        (by dsimp only [privKeySerializeSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
        hlen_priv32
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [privKeySerializeSpec, rustPanicOnOom] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_4.trace = sf_3.trace›, htrace2,
            ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [privKeySerializeSpec]
        simp only [*, arm64_norm, bv_sub_add_lit', BitVec.sub_sub, BitVec.reduceAdd,
          sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun privBoxPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_priv⟩ => ?_
      apply SepWPp.of_sepWP (mid := entry + 260#64)
      wp_steps
      wp_call hshim ()
      wp_steps
      wp_call halloc (32, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_true]
        refine sepWPp_pure_mid fun htrace3 => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace3,
            ‹sf_5.trace = sm2.trace›, htr2])) hm
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_false, ‹sf_5.sp = sm2.sp›, hspm2, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod3, htrace3⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [← hlen_priv32]
        wp_call hmemcpy (sf_6.readReg64 (Reg.gpr 0#5), privBoxPtr, bytesToBv8 senderRatchetPriv32)
        simp only [hlen_priv32, h_6]
        wp_steps
        wp_call hdealloc (privBoxPtr, bytesToBv8 senderRatchetPriv32, 32, 1)
        wp_steps
        wp_call hdealloc (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
        wp_steps
        have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
          (sf_3.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
          senderChainIdx pre144 post100 h_8
        have hlen_full : (pre144 ++ (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
            post100)).length = 344 := by
          simp [h_8, h]
        refine sepWP_focus (T :=
          (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_3.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xb0#64) ↦₆₄ sf_6.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xc0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xd0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xf0#64) ↦₃₂ senderChainIdx) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_focus) ?_
        rw [hpack_in, ← hlen_full]
        wp_call hmemcpy (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
          (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
        simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ h_8]
        wp_done

theorem withSenderChain_none_base_ok {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr withSenderChainSym)
      (withSenderChainNoneSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (withSenderChain_none_base_ok_trap hA)

end WithSenderChain
section WithReceiverChain
abbrev withReceiverChainSym : String :=
  "<libsignal_protocol::state::session::SessionState>::with_receiver_chain"
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x11c98
theorem fnAddr_ecPubKeySerialize_from_withReceiverChain_trap
    (b : BitVec 64) (C : Crypto) (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr ecPubKeySerializeSym =
      (trTrapProgAt b C absHooks).fnAddr withReceiverChainSym + 181804#64 := by
  dsimp only [trTrapProgAt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      CryptoVerification.libsignalSessionCode_fnOff_0x11c98]
  bv_omega

theorem fnAddr_ecPubKeySerialize_from_withReceiverChain
    (b : BitVec 64) (C : Crypto) (ctl : BitVec 64) (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr withReceiverChainSym + 181804#64 := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_ecPubKeySerialize_from_withReceiverChain_trap b C absHooks)

theorem fnAddr_growOneChain_from_withReceiverChain_trap (b : BitVec 64) (C : Crypto)
    (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr growOneChainSym =
      (trTrapProgAt b C absHooks).fnAddr withReceiverChainSym + 16404#64 := by
  dsimp only [trTrapProgAt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x15cac,
      CryptoVerification.libsignalSessionCode_fnOff_0x11c98]
  bv_omega

theorem fnAddr_growOneChain_from_withReceiverChain (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr growOneChainSym =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr withReceiverChainSym + 16404#64 := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_growOneChain_from_withReceiverChain_trap b C absHooks)

private theorem stackAt_withReceiverChain_entry (sp : BitVec 64) :
    memRegion (sp - 4576#64) 480 ∗ stackAt sp allocHookStack =
      memRegion (sp - 368#64 - 4208#64) 80 ∗ (memRegion (sp - 368#64 - 4128#64) 32 ∗ stackAt (sp -
        368#64) allocHookStack) ∗
      memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
  have h1 := stackAt_split_top sp 480 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (112 + allocHookStack) 46 (by decide)
  have h3 := stackAt_split_top (sp - 368#64) 112 allocHookStack (by decide)
  have h4 := memRegion_split (sp - 368#64 - 4208#64) 80 32 (by decide)
  have h5 : (480 + allocHookStack : Nat) = (112 + allocHookStack) + 8 * 46 := by decide
  have h6 : BitVec.ofNat 64 (480 + allocHookStack) = 4576#64 := rfl
  have h7 : BitVec.ofNat 64 (8 * 46) = 368#64 := rfl
  have h8 : BitVec.ofNat 64 (112 + allocHookStack) = 4208#64 := rfl
  have h9 : sp - 368#64 - 4208#64 + BitVec.ofNat 64 80 = sp - 368#64 - 4128#64 := by bv_omega
  have hcells46 : cells (sp - 368#64) 46 = memRegion (sp - 368#64) 272 ∗ cells (sp - 96#64) 12 := by
    rw [← memRegion_cells (sp - 368#64) 46 (by decide), memRegion_split (sp - 368#64) 272 96
      (by decide),
        show sp - 368#64 + BitVec.ofNat 64 272 = sp - 96#64 by bv_omega, memRegion_cells (sp -
          96#64) 12 (by decide)]
  rw [h6] at h1
  rw [h7] at h2
  rw [h8] at h3
  rw [h9] at h4
  rw [← h1, h5, h2, h3, h4, hcells46]
  simp only [sepConj_assoc]
private theorem stackAt_growOneChain (sp : BitVec 64) :
    memRegion (sp - 4208#64) 80 ∗ memRegion (sp - 4128#64) 32 ∗ stackAt sp allocHookStack =
      cells (sp - 64#64) 8 ∗ cells (sp - 112#64) 6 ∗ stackAt (sp - 112#64) allocHookStack := by
  have h0 := memRegion_split (sp - 4208#64) 80 32 (by decide)
  have h0a : sp - 4208#64 + BitVec.ofNat 64 80 = sp - 4128#64 := by bv_omega
  rw [h0a] at h0
  rw [← sepConj_assoc, ← h0]
  have h1 := stackAt_split_top sp 112 allocHookStack (by decide)
  have h2 := stackAt_split_cells sp (48 + allocHookStack) 8 (by decide)
  have h3 := stackAt_split_cells (sp - 64#64) allocHookStack 6 (by decide)
  have h4 : (112 + allocHookStack : Nat) = (48 + allocHookStack) + 8 * 8 := by decide
  have h5 : (48 + allocHookStack : Nat) = allocHookStack + 8 * 6 := by decide
  have h6 : BitVec.ofNat 64 (112 + allocHookStack) = 4208#64 := rfl
  have h7 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  have h8 : BitVec.ofNat 64 (8 * 6) = 48#64 := rfl
  have h9 : sp - 64#64 - 48#64 = sp - 112#64 := by bv_omega
  rw [h6] at h1
  rw [h7] at h2
  rw [h8, h9] at h3
  rw [← h1, h4, h2, h5, h3]
  ac_rfl
def growOneChainZeroRegionSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (vecPtr, oldPtr) s =>
    ⌜s.readReg64 .x0 = vecPtr⌝ ∗ (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool ∗
      memRegion (s.sp - 4208#64) 80 ∗
    memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack
  post := fun (vecPtr, _oldPtr) s0 sf =>
    ∃∗ newPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗ (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr +
      8#64) ↦₆₄ newPtr) ∗ A.live newPtr 416 8 ∗
      memRegion newPtr 416 ∗ A.pool ∗ memRegion (s0.sp - 4208#64) 80 ∗ memRegion (s0.sp -
        4128#64) 32 ∗ stackAt s0.sp allocHookStack
  onPanic := rustPanicOnOom img
theorem growOneChain_zero_region_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr growOneChainSym)
      (growOneChainZeroRegionSpec A img) := by
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (growOneChainZeroSpec A img).pre g s0 ∗ R := by
    simpa only [growOneChainZeroRegionSpec, growOneChainZeroSpec, stackAt_growOneChain] using hpre
  refine ((growOneChain_zero_ok_trap (img := img) (C := C) hA).to_outcome
    g R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    simpa only [growOneChainZeroRegionSpec, growOneChainZeroSpec, stackAt_growOneChain] using hpost
  · exact Or.inr hrest

theorem growOneChain_zero_region_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr growOneChainSym)
      (growOneChainZeroRegionSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (growOneChain_zero_region_ok_trap hA)

private theorem memRegion_416_receiverChain_split (ptr : BitVec 64) :
    memRegion ptr 416 =
      cells ptr 12 ∗ (∃∗ v : BitVec 32, (ptr + 0x60#64) ↦₃₂ v) ∗ memRegion (ptr + 0x64#64) 316 := by
  have h1 := memRegion_split ptr 96 320 (by decide)
  have h2 := memRegion_split (ptr + BitVec.ofNat 64 96) 4 316 (by decide)
  have h3 : ptr + BitVec.ofNat 64 96 = ptr + 0x60#64 := by bv_omega
  have h4 : ptr + 0x60#64 + BitVec.ofNat 64 4 = ptr + 0x64#64 := by bv_omega
  rw [h1, memRegion_cells ptr 12 (by decide), h3]
  rw [h3, h4] at h2
  rw [h2, ProofLib.memRegion_four (ptr + 0x60#64)]
def receiverChainElemAt (chainBufPtr pubPtr ckPtr : BitVec 64) (idx : BitVec 32) : SepProp :=
  (chainBufPtr ↦₆₄ 33#64) ∗ ((chainBufPtr + 0x08#64) ↦₆₄ pubPtr) ∗ ((chainBufPtr +
    0x10#64) ↦₆₄ 33#64) ∗
  ((chainBufPtr + 0x18#64) ↦₆₄ 0#64) ∗ ((chainBufPtr + 0x20#64) ↦₆₄ 1#64) ∗ ((chainBufPtr +
    0x28#64) ↦₆₄ 0#64) ∗
  ((chainBufPtr + 0x30#64) ↦₆₄ 0#64) ∗ ((chainBufPtr + 0x38#64) ↦₆₄ 8#64) ∗ ((chainBufPtr +
    0x40#64) ↦₆₄ 0#64) ∗
  ((chainBufPtr + 0x48#64) ↦₆₄ 32#64) ∗ ((chainBufPtr + 0x50#64) ↦₆₄ ckPtr) ∗ ((chainBufPtr +
    0x58#64) ↦₆₄ 32#64) ∗
  ((chainBufPtr + 0x60#64) ↦₃₂ idx)
def receiverChainVecBytes24 (chainBufPtr : BitVec 64) : List (BitVec 8) :=
  unpack64 4#64 ++ (unpack64 chainBufPtr ++ unpack64 1#64)
@[simp]
theorem receiverChainVecBytes24_length (chainBufPtr : BitVec 64) :
    (receiverChainVecBytes24 chainBufPtr).length = 24 := by
  simp [receiverChainVecBytes24, unpack64]
def receiverChainVecFieldsAt (ptr chainBufPtr : BitVec 64) : SepProp :=
  ((ptr + 0x48#64) ↦₆₄ 4#64) ∗ ((ptr + 0x50#64) ↦₆₄ chainBufPtr) ∗ ((ptr + 0x58#64) ↦₆₄ 1#64)
theorem receiverChainVecFieldsAt_eq_pointsToBytes (ptr chainBufPtr : BitVec 64) :
    receiverChainVecFieldsAt ptr chainBufPtr =
      ((ptr + 0x48#64) ↦ₛ receiverChainVecBytes24 chainBufPtr) := by
  unfold receiverChainVecFieldsAt receiverChainVecBytes24
  simp only [pointsTo64_eq_pointsToBytes, pointsToBytes_append, unpack64_length, BitVec.add_assoc,
    BitVec.reduceAdd]
theorem withReceiverChain_pack344 (ptr chainBufPtr : BitVec 64) (pre72 post248 : List (BitVec 8))
    (hpre : pre72.length = 72) :
    (ptr ↦ₛ pre72) ∗ receiverChainVecFieldsAt ptr chainBufPtr ∗ ((ptr + 0x60#64) ↦ₛ post248) =
      (ptr ↦ₛ (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248))) := by
  rw [receiverChainVecFieldsAt_eq_pointsToBytes, pointsToBytes_append, pointsToBytes_append, hpre,
    receiverChainVecBytes24_length]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
theorem withReceiverChain_pack344_unfolded
    (ptr chainBufPtr : BitVec 64) (pre72 post248 : List (BitVec 8)) (hpre : pre72.length = 72) :
    (ptr ↦ₛ pre72) ∗ ((ptr + 0x48#64) ↦₆₄ 4#64) ∗ ((ptr + 0x50#64) ↦₆₄ chainBufPtr) ∗ ((ptr +
      0x58#64) ↦₆₄ 1#64) ∗
    ((ptr + 0x60#64) ↦ₛ post248) =
      (ptr ↦ₛ (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248))) := by
  simpa only [receiverChainVecFieldsAt, sepConj_assoc] using
    withReceiverChain_pack344 ptr chainBufPtr pre72 post248 hpre
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs_0_0 : ConditionHolds CondCode.EQ (subsPState64 0#64 0#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_0_5 : ConditionHolds CondCode.LT (subsPState64 0#64 5#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide
@[local simp, local wp_norm, local arm64_norm]
private theorem madd_zero_104 (ptr : BitVec 64) : ptr + 0#64 * 104#64 = ptr := by simp
structure WithReceiverChainGhost where
  outPtr               : BitVec 64
  inPtr                : BitVec 64
  senderRatchetPubPtr  : BitVec 64
  senderRatchetPub32   : Bytes
  receiverChainKeyPtr  : BitVec 64
  receiverChainKey32   : Bytes
  receiverChainIdx     : BitVec 32
  oldVecPtr            : BitVec 64
  pre72                : List (BitVec 8)
  post248              : List (BitVec 8)
def withReceiverChainEmptySpec (A : RustAlloc) (img : Obj.Image) :
    Spec WithReceiverChainGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x1 =
      g.senderRatchetPubPtr ∧
      s.readReg64 .x2 = g.receiverChainKeyPtr ∧ g.senderRatchetPub32.length = 32 ∧
        g.receiverChainKey32.length = 32 ∧ g.pre72.length = 72 ∧
      g.post248.length = 248⌝ ∗ (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
    (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗ ((g.receiverChainKeyPtr +
      32#64) ↦₃₂ g.receiverChainIdx) ∗
    (g.inPtr ↦ₛ g.pre72) ∗ ((g.inPtr + 0x48#64) ↦₆₄ 0#64) ∗ ((g.inPtr + 0x50#64) ↦₆₄ g.oldVecPtr) ∗
      ((g.inPtr + 0x58#64) ↦₆₄ 0#64) ∗
    ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4576#64) 480 ∗
      stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ receiverRatchetPubBoxPtr : BitVec 64, ∃∗ receiverChainKeyBoxPtr : BitVec 64, ∃∗
      chainBufPtr : BitVec 64, ⌜sf.trace = s0.trace ∧
        receiverRatchetPubBoxPtr ≠ 0 ∧ receiverChainKeyBoxPtr ≠ 0 ∧ chainBufPtr ≠ 0⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
        (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
        (receiverRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      A.live receiverChainKeyBoxPtr 32 1 ∗ A.live chainBufPtr 416 8 ∗
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
        g.receiverChainIdx ∗
      memRegion (chainBufPtr + 0x64#64) 316 ∗ (g.outPtr ↦ₛ g.pre72) ∗
        receiverChainVecFieldsAt g.outPtr chainBufPtr ∗
      ((g.outPtr + 0x60#64) ↦ₛ g.post248) ∗ (g.inPtr ↦ₛ g.pre72) ∗
        receiverChainVecFieldsAt g.inPtr chainBufPtr ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ (memRegion (s0.sp - 4576#64) 480 ∗
        stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOom img
theorem withReceiverChain_empty_base_ok_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr withReceiverChainSym)
      (withReceiverChainEmptySpec A img) := by
  unfold withReceiverChainEmptySpec rustPanicOnOom
  simp only [stackAt_withReceiverChain_entry]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_sub_add_lit',
      BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr withReceiverChainSym + 181804#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_withReceiverChain_trap img.base C absHooks).symm ▸
      ecPubKeySerialize_alloc_ok_trap (img := img) hA
  have hgrow :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr withReceiverChainSym + 16404#64)
        (growOneChainZeroRegionSpec A img) :=
    (fnAddr_growOneChain_from_withReceiverChain_trap img.base C absHooks).symm ▸
      growOneChain_zero_region_ok_trap (img := img) hA
  have hshim := shim_ok_at_trap img.base C absHooks withReceiverChainSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA withReceiverChainSym (num% (ls_off% "__rustc::__rust_alloc" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := dealloc_bytes_ok_at_trap (b := img.base) (C := C) (absHooks := absHooks)
    hA (name := withReceiverChainSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := session_memcpy_region_ok_at_trap img.base C absHooks withReceiverChainSym (num% (ls_off% "memcpy" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks withReceiverChainSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff withReceiverChainSym = 0x11c98 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x11c98
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.withReceiverChain img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x11c98 972
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr withReceiverChainSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hser hgrow hshim halloc hdealloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr withReceiverChainSym = entry
  examples_hide_fetches
  rcases g with ⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by simp [bytesToBv8, h_6]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 368#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP (mid := entry + 181804#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h_5
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 144#64)
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [h_5]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP (mid := entry + 16404#64)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33]
      wp_steps
      wp_call hdealloc (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      conv =>
        arg 4
        simp only [‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1]
      refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr)) hgrow
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := entry + 364#64) (by wp_norm_lhs)
        (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC,
        State.sp_setPState, ite_false, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1, BitVec.sub_sub, BitVec.reduceAdd]; rfl)
        (by wp_norm_lhs)
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [growOneChainZeroRegionSpec, rustPanicOnOom] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_5.trace = sf_4.trace›, ‹sf_4.trace = sf_3.trace›,
            htrace2, ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [growOneChainZeroRegionSpec]
        simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
          sepConj_assoc]
      refine SepWPp.exists_elim fun chainBufPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_buf⟩ => ?_
      conv =>
        arg 4
        simp only [memRegion_416_receiverChain_split chainBufPtr, cells, sepConj_emp,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
          sepConj_assoc]
      repeat (refine SepWPp.exists_elim fun _ => ?_)
      apply SepWPp.of_sepWP_ret
      wp_steps
      have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
        chainBufPtr pre72 post248 h_7
      have hlen_full : (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248)).length = 344 :=
        by
        simp [h_7, h]
      refine sepWP_focus (T :=
        (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
        ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ chainBufPtr) ∗ ((s0.readReg64 (.gpr 0#5) +
        0x58#64) ↦₆₄ 1#64) ∗ ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_focus) ?_
      rw [hpack_in, ← hlen_full]
      wp_call hmemcpy (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre72 ++
        (receiverChainVecBytes24 chainBufPtr ++ post248))
      simp only [← withReceiverChain_pack344 _ _ _ _ h_7]
      wp_steps
      unfold receiverChainElemAt receiverChainVecFieldsAt
      simp only [sepConj_assoc]
      wp_done

theorem withReceiverChain_empty_base_ok {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr withReceiverChainSym)
      (withReceiverChainEmptySpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (withReceiverChain_empty_base_ok_trap hA)

end WithReceiverChain
section SetUnackPreKeyMsg
private theorem memRegion_33_cells_raw (a : BitVec 64) :
    memRegion a 33 =
      (∃∗ b0 : BitVec 8, a ↦₈ b0) ∗ (∃∗ u0 : BitVec 64, (a + 1#64) ↦₆₄ u0) ∗ (∃∗ u1 : BitVec 64,
        (a + 9#64) ↦₆₄ u1) ∗
      (∃∗ u2 : BitVec 64, (a + 17#64) ↦₆₄ u2) ∗ (∃∗ u3 : BitVec 64, (a + 25#64) ↦₆₄ u3) := by
  rw [memRegion_split a 1 32 (by decide), memRegion_split (a + 1#64) 8 24 (by decide),
    memRegion_split (a + 1#64 + 8#64) 8 16 (by decide),
    memRegion_split (a + 1#64 + 8#64 + 8#64) 8 8 (by decide), memRegion_one, memRegion_eight,
      memRegion_eight,
    memRegion_eight, memRegion_eight]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
private theorem bytesToBv8_encodeEC_raw (bs : Bytes) :
    bytesToBv8 (encodeEC bs) = 5#8 :: bytesToBv8 bs := rfl
def ecPubKeySerializeRawSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × Bytes) where
  pre := fun (keyPtr, keyBytes) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32⌝ ∗ (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
      stackAt (s.sp - 32#64) allocHookStack ∗
    cells (s.sp - 32#64) 4 ∗ A.pool
  post := fun (keyPtr, keyBytes) s0 sf =>
    ∃∗ slicePtr : BitVec 64, ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 =
      33#64 ∧ slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
        A.live slicePtr 33 1 ∗
      stackAt (s0.sp - 32#64) allocHookStack ∗ cells (s0.sp - 32#64) 4 ∗ A.pool
  onPanic := rustPanicOnOom img
theorem ecPubKeySerializeRaw_ok_trap {A : RustAlloc} {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeRawSpec A img) := by
  unfold ecPubKeySerializeRawSpec rustPanicOnOom
  simp only [bytesToBv8_encodeEC_raw]
  cells_unfold
  have hshim := shim_ok_at_trap img.base C absHooks ecPubKeySerializeSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA ecPubKeySerializeSym (num% (ls_off% "__rustc::__rust_alloc" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks ecPubKeySerializeSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff ecPubKeySerializeSym = 0x3e2c4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x3e2c4 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr ecPubKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr ecPubKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells keyPtr]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_raw, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 =>
      SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u2 =>
      SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd]
    wp_done

theorem ecPubKeySerializeRaw_ok {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)} (hA : AllocHooks A absHooks) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeRawSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (ecPubKeySerializeRaw_ok_trap hA)

abbrev setUnackPreKeyMsgSym : String :=
  "<libsignal_protocol::state::session::SessionState>::set_unacknowledged_pre_key_message"
abbrev systemTimeDurationSinceStub : String := "<std::time::SystemTime>::duration_since"
structure CryptoLeafCall where
  inPtr   : BitVec 64
  inBytes : Bytes
  outPtr  : BitVec 64
def cryptoLeafStubSpec (fn : Bytes → Bytes) (inLen outLen : Nat) : Spec CryptoLeafCall where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x8 = g.outPtr ∧ g.inBytes.length = inLen⌝ ∗
      (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗ memRegion g.outPtr outLen ∗ stackAt s.sp pqxdhHookStack
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ (g.inPtr ↦ₛ bytesToBv8 g.inBytes) ∗
      (g.outPtr ↦ₛ fitBv8 outLen (fn g.inBytes)) ∗ stackAt s0.sp pqxdhHookStack
ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x12298
  (ls_stub% "<std::time::SystemTime>::duration_since")
  (ls_hook% "<std::time::SystemTime>::duration_since")
theorem systemTimeDurationSince_ok_at_trap {img : Obj.Image} {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hTime : HookSat absHooks systemTimeDurationSinceStub (cryptoLeafStubSpec id 16 16))
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff systemTimeDurationSinceStub := by fnoff_eq) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec id 16 16) := by
  exact hook_ok_at (hname := systemTimeDurationSinceStub) rfl hk
    (by rw [(ls_stub% "<std::time::SystemTime>::duration_since")]; decide) (fun H =>
      by rw [(ls_stub% "<std::time::SystemTime>::duration_since")]; exact (ls_hook% "<std::time::SystemTime>::duration_since") H)
    (by simp [systemTimeDurationSinceStub, Rust.isPanicSymbol]) (hookSat_tripleRatchetExterns'_trap C absHooks rfl hTime)

theorem systemTimeDurationSince_ok_at {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hTime : HookSat absHooks systemTimeDurationSinceStub (cryptoLeafStubSpec id 16 16))
    {name : String} {k : Nat} (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff systemTimeDurationSinceStub := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr name + BitVec.ofNat 64 k)
      (cryptoLeafStubSpec id 16 16) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (systemTimeDurationSince_ok_at_trap hTime hk)

private theorem fnAddr_ecPubKeySerialize_from_setUnack_trap (b : BitVec 64)
    (C : Crypto) (absHooks : String → Option (State → State)) :
    (trTrapProgAt b C absHooks).fnAddr setUnackPreKeyMsgSym + 180268#64 =
      (trTrapProgAt b C absHooks).fnAddr ecPubKeySerializeSym := by
  simp only [trTrapProgAt, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x12298,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4]
  bv_arith

private theorem fnAddr_ecPubKeySerialize_from_setUnack (b : BitVec 64)
    (C : Crypto) (ctl : BitVec 64) (absHooks : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl absHooks).fnAddr setUnackPreKeyMsgSym + 180268#64 =
      (tripleRatchetProgAt b C ctl absHooks).fnAddr ecPubKeySerializeSym := by
  simp only [← trTrapProgAt_fnAddr_eq] at *
  exact (fnAddr_ecPubKeySerialize_from_setUnack_trap b C absHooks)

private def twoWordsToBytes (w0 w1 : BitVec 64) : Bytes :=
  (unpack64 w0 ++ unpack64 w1).map fun b => UInt8.ofNat b.toNat
private theorem twoWordsToBytes_length (w0 w1 : BitVec 64) :
    (twoWordsToBytes w0 w1).length = 16 := by
  simp [twoWordsToBytes, unpack64]
private theorem bytesToBv8_twoWordsToBytes (w0 w1 : BitVec 64) :
    bytesToBv8 (twoWordsToBytes w0 w1) = unpack64 w0 ++ unpack64 w1 := by
  simp only [twoWordsToBytes, bytesToBv8, List.map_map]
  have h_id : ((fun b : UInt8 => BitVec.ofNat 8 b.toNat) ∘ fun b : BitVec 8 =>
    UInt8.ofNat b.toNat) = id := by
    funext x
    apply BitVec.eq_of_toNat_eq
    have hx : x.toNat < 256 := x.isLt
    change (x.toNat % 256) % 256 = x.toNat
    omega
  rw [h_id, List.map_id]
private theorem pointsTo64_pair_eq_twoWords (a w0 w1 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1)) = (a ↦ₛ bytesToBv8 (twoWordsToBytes w0 w1)) := by
  rw [bytesToBv8_twoWordsToBytes, pointsToBytes_append, unpack64_length, ←
    pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes]
private theorem fitBv8_16_twoWords (w0 w1 : BitVec 64) :
    fitBv8 16 (id (twoWordsToBytes w0 w1)) = bytesToBv8 (twoWordsToBytes w0 w1) := by
  have hlen : (bytesToBv8 (twoWordsToBytes w0 w1)).length = 16 := by
    simp [bytesToBv8, twoWordsToBytes_length]
  simp [fitBv8, hlen, List.take_of_length_le (Nat.le_of_eq hlen)]
private theorem pointsTo64_pair_entails_memRegion16 (a u3 u4 : BitVec 64) :
    ((a ↦₆₄ u3) ∗ ((a + 8#64) ↦₆₄ u4)) ⊢ memRegion a 16 := by
  rw [show (16 : Nat) = 8 + 8 by decide, memRegion_split a 8 8 (by decide), memRegion_eight,
    memRegion_eight]
  exact sepConj_mono (Entails.sepExists_intro u3) (Entails.sepExists_intro u4)
private theorem pointsToBytes_entails_memRegion_33 (p : BitVec 64) (bs : List (BitVec 8))
    (h : bs.length = 33) : (p ↦ₛ bs) ⊢ memRegion p 33 := by
  rw [← h]; exact pointsToBytes_entails_memRegion p bs
private theorem memRegion_40_unack_split (statePtr : BitVec 64) :
    memRegion (statePtr + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (statePtr + 0x100#64) ↦₆₄ w100) ∗ (∃∗ w108 : BitVec 64, (statePtr +
        0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 32, (statePtr + 0x110#64) ↦₃₂ w110) ∗ (∃∗ w114 : BitVec 32, (statePtr +
        0x114#64) ↦₃₂ w114) ∗
      (∃∗ w118 : BitVec 64, (statePtr + 0x118#64) ↦₆₄ w118) ∗ (∃∗ w120 : BitVec 32, (statePtr +
        0x120#64) ↦₃₂ w120) ∗
      memRegion (statePtr + 0x124#64) 4 := by
  rw [memRegion_split (statePtr + 0x100#64) 8 32 (by decide), memRegion_split (statePtr + 0x100#64 +
    8#64) 8 24 (by decide), memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x100#64 + 8#64 + 8#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide),
      memRegion_eight, memRegion_eight,
    ProofLib.memRegion_four, ProofLib.memRegion_four, memRegion_eight, ProofLib.memRegion_four]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
private theorem unack_tail24_entails_memRegion (statePtr : BitVec 64)
    (v110 v114 v120 : BitVec 32) (v118 : BitVec 64) : ((statePtr + 0x110#64) ↦₃₂ v110) ∗
    ((statePtr + 0x114#64) ↦₃₂ v114) ∗ ((statePtr + 0x118#64) ↦₆₄ v118) ∗
    ((statePtr + 0x120#64) ↦₃₂ v120) ∗ memRegion (statePtr + 0x124#64) 4 ⊢
      memRegion (statePtr + 0x110#64) 24 := by
  refine Entails.trans
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo32_entails_memRegion _ _))))) ?_
  rw [memRegion_split (statePtr + 0x110#64) 4 20 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64) 4 16 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64) 8 8 (by decide),
    memRegion_split (statePtr + 0x110#64 + 4#64 + 4#64 + 8#64) 4 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.refl _
private theorem stackAt_setUnack_call (sp : BitVec 64) :
    stackAt (sp - 144#64) (allocHookStack + 32) =
      stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 := by
  have h1 := stackAt_split_cells (sp - 144#64) allocHookStack 4 (by decide)
  have h2 : sp - 144#64 - BitVec.ofNat 64 (8 * 4) = sp - 176#64 := by bv_arith
  rw [h2] at h1
  exact h1
private theorem stackAt_setUnack_hooks (sp : BitVec 64) :
    stackAt (sp - 176#64) allocHookStack ∗ cells (sp - 176#64) 4 =
      memRegion (sp - 4272#64) 32 ∗ stackAt (sp - 144#64) allocHookStack := by
  rw [← stackAt_setUnack_call sp]
  have h1 := stackAt_split_top (sp - 144#64) 32 allocHookStack (by decide)
  have h2 : (32 + allocHookStack : Nat) = allocHookStack + 32 := by decide
  have h3 : BitVec.ofNat 64 (32 + allocHookStack) = 4128#64 := rfl
  have h4 : sp - 144#64 - 4128#64 = sp - 4272#64 := by bv_arith
  rw [h3, h4] at h1
  rw [← h2, h1]
@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide
def setUnackPreKeyMsgSpec (A : RustAlloc) (img : Obj.Image) :
    Spec (BitVec 64 × BitVec 64 × Bytes) where
  pre := fun (statePtr, baseKeyPtr, baseKeyBytes) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x4 = baseKeyPtr ∧ baseKeyBytes.length = 32⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗ ((statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (statePtr + 0x100#64) 40 ∗ stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗
    A.pool
  post := fun (statePtr, baseKeyPtr, baseKeyBytes) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗
    vecU8 A (statePtr + 0xf8#64) (bytesToBv8 (encodeEC baseKeyBytes)) ∗
    memRegion (statePtr + 0x110#64) 24 ∗
    stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOom img
theorem setUnackPreKeyMsg_base_ok_trap {A : RustAlloc} {img : Obj.Image}
    {C : Crypto}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks)
    (hTime : HookSat absHooks systemTimeDurationSinceStub (cryptoLeafStubSpec id 16 16)) :
    subroutine_ok (trTrapProgAt img.base C absHooks)
      ((trTrapProgAt img.base C absHooks).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgSpec A img) := by
  unfold setUnackPreKeyMsgSpec rustPanicOnOom
  have hser :
      subroutine_ok (trTrapProgAt img.base C absHooks)
        ((trTrapProgAt img.base C absHooks).fnAddr setUnackPreKeyMsgSym + 180268#64)
        (ecPubKeySerializeRawSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_setUnack_trap img.base C absHooks).symm ▸
      ecPubKeySerializeRaw_ok_trap (img := img) hA
  have hshim := shim_ok_at_trap img.base C absHooks setUnackPreKeyMsgSym (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_trap img.base C A absHooks hA setUnackPreKeyMsgSym (num% (ls_off% "__rustc::__rust_alloc" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_alloc")])
  have hmemcpy := session_memcpy_region_ok_at_trap img.base C absHooks setUnackPreKeyMsgSym (num% (ls_off% "memcpy" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "memcpy")])
  have htime := systemTimeDurationSince_ok_at_trap (img := img) (C := C) hTime
    (name := setUnackPreKeyMsgSym) (k := num% (ls_off% "<std::time::SystemTime>::duration_since" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "<std::time::SystemTime>::duration_since")])
  have hdealloc := dealloc_ok_at_trap img.base C A absHooks hA setUnackPreKeyMsgSym (num% (ls_off% "__rustc::__rust_dealloc" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hpanic := panic_at_handle_error_trap img.base C absHooks setUnackPreKeyMsgSym (num% (ls_off% "alloc::raw_vec::handle_error" - 0x12298))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x12298,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hTime hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff setUnackPreKeyMsgSym = 0x12298 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x12298
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.setUnackPreKeyMsg img.base
    (Rust.withPanics (trTrapExterns C absHooks)) hfn 0x12298 312
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics (trTrapExterns C absHooks))).fnAddr setUnackPreKeyMsgSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [trTrapProgAt] at hser hshim halloc hmemcpy htime hdealloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C absHooks))).fnAddr setUnackPreKeyMsgSym = entry
  examples_hide_fetches
  obtain ⟨statePtr, baseKeyPtr, baseKeyBytes⟩ := g
  dsimp only at *
  subst h_1 h_2
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    rw [bytesToBv8_encodeEC_raw]; simp [bytesToBv8, h]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  rw [memRegion_40_unack_split (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 => SepWPp.exists_elim fun c2 => ?_
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply SepWPp.of_sepWP (mid := entry + 180268#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 4#5), baseKeyBytes)) hser
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := entry + 64#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeRawSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    h
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      dsimp only [ecPubKeySerializeRawSpec, rustPanicOnOom] at hm
      rw [← sepConj_assoc]
      exact allowPanic_frame (by simp only [allocFailedIn, arm64_norm]; exact id) hm)
    (fun sm hpcm hrunm hspm hcsm => ?_)
  simp only [arm64_norm] at hspm
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm
  rcases hcsm with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩
  simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
  clear hpre
  dsimp only [ecPubKeySerializeRawSpec]
  simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd,
    sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun slicePtr => ?_
  refine SepWPp.pure_left fun ⟨htr_sm, hx0_sm, hx1_sm, hne_slice⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 116#64)
  apply SepWP.replace_pre (by sep_focus) (Entails.of_eq (stackAt_setUnack_hooks s0.sp))
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x12298))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm =>
      ⟨allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm]; rw [htrace,
        ‹sf.trace = sm.trace›, htr_sm]),
        Satisfies.mono (sepConj_mono_left (ent_anyHeap _)) hm⟩
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← hlen_enc]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), slicePtr, bytesToBv8 (encodeEC baseKeyBytes))
    wp_steps
    have h128_eq : s0.sp - 128#64 + 4#64 = s0.sp - 124#64 := by bv_arith
    have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
    have h120_eq : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq (h128_eq ▸ pointsTo32_pair (s0.sp - 128#64) _ _))
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq (h136_eq ▸ pointsTo64_pair_eq_twoWords (s0.sp - 136#64) _ _))
    apply SepWP.replace_pre (by sep_focus)
      (h120_eq ▸ pointsTo64_pair_entails_memRegion16 (s0.sp - 120#64) _ _)
    have hlen_tw := twoWordsToBytes_length (s0.readReg64 (.gpr 5#5))
      (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5)))
    wp_call htime ⟨s0.sp - 136#64, twoWordsToBytes (s0.readReg64 (.gpr 5#5))
      (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5))), s0.sp - 120#64⟩
    rw [fitBv8_16_twoWords, ← pointsTo64_pair_eq_twoWords (s0.sp - 136#64),
      ← pointsTo64_pair_eq_twoWords (s0.sp - 120#64), h136_eq, h120_eq]
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (pointsToBytes_entails_memRegion_33 slicePtr _ hlen_enc)
    wp_call hdealloc (slicePtr, 33, 1)
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (unack_tail24_entails_memRegion (s0.readReg64 (.gpr 0#5)) _ _ _ _)
    simp only [*] at *
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq ((stackAt_setUnack_call s0.sp).trans (stackAt_setUnack_hooks s0.sp)).symm)
    dsimp only [vecU8]
    cells_unfold
    wp_done

theorem setUnackPreKeyMsg_base_ok {A : RustAlloc} {img : Obj.Image}
    {C : Crypto} {ctl : BitVec 64}
    {absHooks : String → Option (State → State)}
    (hA : AllocHooks A absHooks)
    (hTime : HookSat absHooks systemTimeDurationSinceStub (cryptoLeafStubSpec id 16 16)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl absHooks)
      ((tripleRatchetProgAt img.base C ctl absHooks).fnAddr setUnackPreKeyMsgSym)
      (setUnackPreKeyMsgSpec A img) := by
  try simp only [← trTrapProgAt_fnAddr_eq] at *
  exact subroutine_ok_kit_of_trTrap (setUnackPreKeyMsg_base_ok_trap hA hTime)

end SetUnackPreKeyMsg

section SessionStateCalleesExt

/-- Memory and allocator extern contracts needed by the `SessionStateCallees` builders on
`tripleRatchetProgAtExt img.base ext` (`shim` at `0` stack, `alloc`/`dealloc`/`realloc` + `memcpy`
at `allocHookStack = CliExt.memHookStack = 4096`). -/
structure SessionMemHooks (A : RustAlloc) (ext : String → Option (State → State)) : Prop where
  shim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec
  alloc : AllocHooks A ext
  memcpy : HookSat ext memcpyName CryptoVerification.SignalSession.CliExt.memcpySpec

theorem SessionMemHooks.of_externsOk {P : CryptoVerification.E2E.PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    SessionMemHooks A ext :=
  ⟨hOk.shim, hOk.alloc, hOk.memcpy⟩

private theorem hookSat_cliExternsWith_session {α : Type} {ext : String → Option (State → State)}
    {n : String} {spec : Spec α}
    (hpan : CryptoVerification.E2E.isImagePanicSymbol n = false)
    (h : HookSat ext n spec) :
    HookSat (CryptoVerification.SignalSession.cliExternsWith ext) n spec := by
  rcases h with ⟨f, hf, hok⟩
  refine ⟨f, ?_, hok⟩
  simp [CryptoVerification.SignalSession.cliExternsWith, CryptoVerification.E2E.withImagePanics,
    hpan, hf]

theorem SessionMemHooks.cliExternsWith {A : RustAlloc} {ext : String → Option (State → State)}
    (h : SessionMemHooks A ext) :
    SessionMemHooks A (CryptoVerification.SignalSession.cliExternsWith ext) where
  shim := hookSat_cliExternsWith_session
    (by simp [CryptoVerification.E2E.isImagePanicSymbol, CryptoVerification.E2E.extraImagePanicNames,
      Rust.isPanicSymbol, shimName]) h.shim
  alloc := {
    alloc := hookSat_cliExternsWith_session
      (by simp [CryptoVerification.E2E.isImagePanicSymbol, CryptoVerification.E2E.extraImagePanicNames,
        Rust.isPanicSymbol]) h.alloc.alloc
    dealloc := hookSat_cliExternsWith_session
      (by simp [CryptoVerification.E2E.isImagePanicSymbol, CryptoVerification.E2E.extraImagePanicNames,
        Rust.isPanicSymbol]) h.alloc.dealloc
    realloc := hookSat_cliExternsWith_session
      (by simp [CryptoVerification.E2E.isImagePanicSymbol, CryptoVerification.E2E.extraImagePanicNames,
        Rust.isPanicSymbol]) h.alloc.realloc
  }
  memcpy := hookSat_cliExternsWith_session
    (by simp [CryptoVerification.E2E.isImagePanicSymbol, CryptoVerification.E2E.extraImagePanicNames,
      Rust.isPanicSymbol, memcpyName]) h.memcpy

theorem SessionMemHooks.of_externsOk_cliExternsWith {P : CryptoVerification.E2E.PEParams}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hOk : CryptoVerification.SignalSession.CliExternsOk P A ext) :
    SessionMemHooks A (CryptoVerification.SignalSession.cliExternsWith ext) :=
  (SessionMemHooks.of_externsOk hOk).cliExternsWith

theorem shim_ok_at_session_ext (b : BitVec 64) {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionShimSpec := by
  have heq : CryptoVerification.SignalSession.CliExt.shimSpec = sessionShimSpec := rfl
  rw [← heq]
  exact hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext) (name := name)
    (hname := shimName) (k := k) rfl hk
    (by rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]; decide)
    (fun H => by
      rw [(ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")]
      exact (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2") H)
    (by decide +kernel)
    hShim

theorem memcpy_ok_at_session_ext (b : BitVec 64) {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext memcpyName CryptoVerification.SignalSession.CliExt.memcpySpec)
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      CryptoVerification.SignalSession.CliExt.memcpySpec :=
  hook_ok_at (P := libsignalSessionCode) (b := b) (hooks := ext) (name := name)
    (hname := memcpyName) (k := k) rfl hk
    (by rw [(ls_stub% "memcpy")]; decide)
    (fun H => by rw [(ls_stub% "memcpy")]; exact (ls_hook% "memcpy") H)
    (by decide +kernel)
    hMemcpy

theorem dealloc_bytes_ok_at_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocHooks A ext) {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k =
      libsignalSessionCode.fnOff deallocName := by fnoff_eq) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (rustDeallocBytesSpec A) := by
  apply subroutine_ok_outcome_intro
  intro ⟨p, bs, n, align⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, n, align) s0 ∗ R := by
    unfold rustDeallocBytesSpec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hpre⟩
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpre ⊢
    refine Satisfies.mono ?_ hpre
    rw [← hlen]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (pointsToBytes_entails_memRegion p bs)))
  exact ((dealloc_ok_at_ext b A ext hA name k hk).to_outcome
    (p, n, align) R s0 hpc hrun hpre' hsp).mono_outcome fun _ h => h

attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0
  CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  CryptoVerification.libsignalSessionCode_fnOff_0x15de4
  CryptoVerification.libsignalSessionCode_fnOff_0x15cac
  CryptoVerification.libsignalSessionCode_fnOff_0x125a4
  CryptoVerification.libsignalSessionCode_fnOff_0x117e8
  CryptoVerification.libsignalSessionCode_fnOff_0x11c98
  CryptoVerification.libsignalSessionCode_fnOff_0x12298

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_adds_neg1_1_ext :
    ConditionHolds CondCode.EQ (addsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, addsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_eq_subs_0_0_ext :
    ConditionHolds CondCode.EQ (subsPState64 0#64 0#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_0_5_ext :
    ConditionHolds CondCode.LT (subsPState64 0#64 5#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

@[local simp, local wp_norm, local arm64_norm]
private theorem madd_zero_104_ext (ptr : BitVec 64) : ptr + 0#64 * 104#64 = ptr := by simp

@[local simp, local wp_norm, local arm64_norm]
private theorem cond_lt_subs_neg1_1_true_ext :
    ConditionHolds CondCode.LT (subsPState64 0xffffffffffffffff#64 1#64) = true := by
  simp only [ConditionHolds, subsPState64]; decide

theorem privKeySerialize_base_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr privKeySerializeSym)
      (privKeySerializeSpec A img) := by
  unfold privKeySerializeSpec rustPanicOnOom
  simp only [stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim := shim_ok_at_session_ext img.base hShim privKeySerializeSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hA privKeySerializeSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_ext img.base ext privKeySerializeSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e7c0))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hShim hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff privKeySerializeSym = 0x3e7c0 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initPrivKeySerialize img.base
    (Rust.withPanics ext) hfn 0x3e7c0 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr privKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr privKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨privKeyPtr, sk, outVecPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  obtain ⟨w0, w1, w2, w3, _, hsk_cells⟩ := exists_unpack64_of_length_32 h
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 36#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e7c0))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm =>
      by simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
          ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    simp only [hoom, ite_false, hm32, cells, sepConj_emp, sepExists_sepConj_left,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    rw [hsk_cells (s0.readReg64 (Reg.gpr 0#5))]
    wp_steps
    simp only [hsk_cells, sepConj_assoc]
    wp_done

theorem ecPubKeySerialize_alloc_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeAllocSpec A img) := by
  unfold ecPubKeySerializeAllocSpec rustPanicOnOom
  simp only [bytesToBv8_encodeEC_alloc, stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim := shim_ok_at_session_ext img.base hShim ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hA ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_ext img.base ext ecPubKeySerializeSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hShim hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff ecPubKeySerializeSym = 0x3e2c4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn 0x3e2c4 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr ecPubKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr ecPubKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_alloc, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_done

theorem finishGrowZero_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr finishGrowSym)
      (finishGrowZeroSpec A) := by
  unfold finishGrowZeroSpec
  cells_unfold
  have hfn : libsignalSessionCode.fnOff finishGrowSym = 0x15de4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x15de4
  have hshim := shim_ok_at_session_ext b hShim finishGrowSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x15de4))
    (by rw [hfn, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext b A ext hA finishGrowSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x15de4))
    (by rw [hfn, (ls_stub% "__rustc::__rust_alloc")])
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalSession.libsignalSessionBin b
    (Rust.withPanics ext) hfn 0x15de4 180
  dsimp only [tripleRatchetProgAtExt] at hshim halloc ⊢
  clear hfn hShim hA
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr finishGrowSym = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  subst cap
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcbz := beq_mul_104_zero_eq_false h_11 h
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (new.toNat * 104, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

theorem growOneChain_zero_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneChainSym)
      (growOneChainZeroSpec A img) := by
  unfold growOneChainZeroSpec rustPanicOnOom
  cells_unfold
  have hfn : libsignalSessionCode.fnOff growOneChainSym = 0x15cac :=
    CryptoVerification.libsignalSessionCode_fnOff_0x15cac
  have hpanic := panic_at_handle_error_ext img.base ext growOneChainSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x15cac))
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  have hfg0 := subroutine_ok_rel_pqxdh_ext
    (finishGrowZero_ok_ext (b := img.base) hShim hA)
    CryptoVerification.libsignalSessionCode_fnOff_0x15de4 hfn (k := 312) (by decide)
  simp only [finishGrowZeroSpec, cells, sepExists_sepConj_right, sepConj_emp, bv_sub_add_lit',
    BitVec.reduceSub] at hfg0
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn 0x15cac 104
  dsimp only [tripleRatchetProgAtExt] at hpanic hfg0 ⊢
  clear hfn hShim hA
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr growOneChainSym = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  obtain ⟨vecPtr, oldPtr⟩ := x
  dsimp only at *
  subst h
  apply SepWPp.of_sepWP (mid := entry + 60#64)
  wp_steps
  wp_call hfg0 (s0.sp - 56#64, 0#64, oldPtr, 4#64, [], v_stk_7, v_stk_8, v_stk_9, s0.sp - 64#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases htag : w = 1#64
  · simp only [htag, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x15cac))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm,
        *])) hm
  · simp only [htag, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

theorem growOneChain_zero_region_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr growOneChainSym)
      (growOneChainZeroRegionSpec A img) := by
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (growOneChainZeroSpec A img).pre g s0 ∗ R := by
    simpa only [growOneChainZeroRegionSpec, growOneChainZeroSpec, stackAt_growOneChain] using hpre
  refine ((growOneChain_zero_ok_ext (img := img) hShim hA).to_outcome
    g R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    simpa only [growOneChainZeroRegionSpec, growOneChainZeroSpec, stackAt_growOneChain] using hpost
  · exact Or.inr hrest

private theorem fnAddr_ecPubKeySerialize_from_sessionStateNew_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAtExt b ext).fnAddr sessionStateNewSym + 179488#64 := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4]
  bv_arith

theorem sessionStateNew_base_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hM : SessionMemHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessionStateNewSym)
      (sessionStateNewSpec A img) := by
  unfold sessionStateNewSpec rustPanicOnOom
  simp only [stackAt_sessionStateNew_entry, memRegion_344_sessionStateNew_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr sessionStateNewSym + 179488#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_sessionStateNew_ext img.base ext) ▸
      ecPubKeySerialize_alloc_ok_ext (img := img) hM.shim hM.alloc
  have hshim := shim_ok_at_session_ext img.base hM.shim sessionStateNewSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hM.alloc sessionStateNewSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_ext img.base ext sessionStateNewSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x125a4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x125a4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hM
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff sessionStateNewSym = 0x125a4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x125a4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.sessionStateNew img.base
    (Rust.withPanics ext) hfn 0x125a4 252
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr sessionStateNewSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hser hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr sessionStateNewSym = entry
  examples_hide_fetches
  rcases g with ⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4 h_5 h_6 h_7
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by simp [bytesToBv8, h_10]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 179488#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), localIk32)) hser
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := entry + 60#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    h_8 (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
  simp only [arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29⟩
  simp only [arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
  clear hpre
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_local⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 179488#64)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 2#5), remoteIk32)) hser
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hspm1, hsp_align])
    (ret_pc := entry + 76#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [arm64_norm, hspm1, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    h_9 (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
        htr1]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
  simp only [arm64_norm, hspm1] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29⟩
  simp only [arm64_norm, hcs1_19, hcs1_20, hcs1_21, hcs1_24, hcs1_25]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocSpec]
    simp only [arm64_norm, hspm1, htr1, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
      sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_2, hx1_2, hne_remote⟩ => ?_
  apply SepWPp.of_sepWP (mid := entry + 100#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    conv =>
      arg 4
      simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x125a4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = sm2.trace›, htr2])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32, cells, sepConj_emp,
        sepExists_sepConj_left,
        sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
    apply SepWPp.of_sepWP (mid := entry + 179488#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 4#5), baseKey32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 128#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
          htrace, ‹sf.trace = sm2.trace›, htr2]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
      hcs3_27, hcs3_28, hcs3_29⟩
    simp only [*, arm64_norm]
      at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr3, hx0_3, hx1_3, hne_base⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [hrk_cells, sepConj_assoc]
    wp_done

private theorem fnAddr_ecPubKeySerialize_from_withSenderChain_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAtExt b ext).fnAddr withSenderChainSym + 183004#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8]
  bv_omega

private theorem fnAddr_privKeySerialize_from_withSenderChain_ext (b : BitVec 64)
    (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr privKeySerializeSym =
      (tripleRatchetProgAtExt b ext).fnAddr withSenderChainSym + 184280#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e7c0,
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8]
  bv_omega

private theorem stackAt_withSenderChain_entry_assoc (sp : BitVec 64) (R : SepProp) :
    memRegion (sp - 4256#64) 160 ∗ (stackAt sp allocHookStack ∗ R) =
      memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack ∗
        cells (sp - 128#64) 16 ∗ R := by
  rw [← sepConj_assoc, stackAt_withSenderChain_entry sp]
  ac_rfl

private theorem cells_sub128_16_entails (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 64) :
    ((sp - 128#64) ↦₆₄ v0 ∗ (sp - 120#64) ↦₆₄ v1 ∗ (sp - 112#64) ↦₆₄ v2 ∗
      (sp - 104#64) ↦₆₄ v3 ∗ (sp - 96#64) ↦₆₄ v4 ∗ (sp - 88#64) ↦₆₄ v5 ∗
      (sp - 80#64) ↦₆₄ v6 ∗ (sp - 72#64) ↦₆₄ v7 ∗ (sp - 64#64) ↦₆₄ v8 ∗
      (sp - 56#64) ↦₆₄ v9 ∗ (sp - 48#64) ↦₆₄ v10 ∗ (sp - 40#64) ↦₆₄ v11 ∗
      (sp - 32#64) ↦₆₄ v12 ∗ (sp - 24#64) ↦₆₄ v13 ∗ (sp - 16#64) ↦₆₄ v14 ∗
      (sp - 8#64) ↦₆₄ v15) ⊢ cells (sp - 128#64) 16 := by
  simp only [cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2
    (Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5
    (Entails.sepExists_right v6 (Entails.sepExists_right v7 (Entails.sepExists_right v8
    (Entails.sepExists_right v9 (Entails.sepExists_right v10 (Entails.sepExists_right v11
    (Entails.sepExists_right v12 (Entails.sepExists_right v13 (Entails.sepExists_right v14
    (Entails.sepExists_right v15 (Entails.refl _))))))))))))))))

private theorem stack_withSenderChain_tail_entails (sp : BitVec 64)
    (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 : BitVec 64) :
    (memRegion (sp - 128#64 - 4128#64) 32 ∗ stackAt (sp - 128#64) allocHookStack ∗
      (sp - 128#64) ↦₆₄ v0 ∗ (sp - 120#64) ↦₆₄ v1 ∗ (sp - 112#64) ↦₆₄ v2 ∗
      (sp - 104#64) ↦₆₄ v3 ∗ (sp - 96#64) ↦₆₄ v4 ∗ (sp - 88#64) ↦₆₄ v5 ∗
      (sp - 80#64) ↦₆₄ v6 ∗ (sp - 72#64) ↦₆₄ v7 ∗ (sp - 64#64) ↦₆₄ v8 ∗
      (sp - 56#64) ↦₆₄ v9 ∗ (sp - 48#64) ↦₆₄ v10 ∗ (sp - 40#64) ↦₆₄ v11 ∗
      (sp - 32#64) ↦₆₄ v12 ∗ (sp - 24#64) ↦₆₄ v13 ∗ (sp - 16#64) ↦₆₄ v14 ∗
      (sp - 8#64) ↦₆₄ v15) ⊢
      memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [stackAt_withSenderChain_entry sp, sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_right
    (cells_sub128_16_entails sp v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15))

set_option maxHeartbeats 1200000 in
theorem withSenderChain_none_base_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hM : SessionMemHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr withSenderChainSym)
      (withSenderChainNoneSpec A img) := by
  unfold withSenderChainNoneSpec rustPanicOnOom
  simp only [memRegion_92_senderChain_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr withSenderChainSym + 183004#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_withSenderChain_ext img.base ext) ▸
      ecPubKeySerialize_alloc_ok_ext (img := img) hM.shim hM.alloc
  have hpser :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr withSenderChainSym + 184280#64)
        (privKeySerializeSpec A img) :=
    (fnAddr_privKeySerialize_from_withSenderChain_ext img.base ext) ▸
      privKeySerialize_base_ok_ext (img := img) hM.shim hM.alloc
  have hshim := shim_ok_at_session_ext img.base hM.shim withSenderChainSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hM.alloc withSenderChainSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := dealloc_bytes_ok_at_ext (b := img.base) (ext := ext)
    hM.alloc (name := withSenderChainSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := memcpy_ok_at_session_ext img.base hM.memcpy withSenderChainSym
    (num% (ls_off% "memcpy" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8, (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_ext img.base ext withSenderChainSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x117e8,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hM
  wpp_init g s0
  conv =>
    arg 4
    simp only [stackAt_withSenderChain_entry_assoc, cells, sepConj_emp, sepExists_sepConj_left,
      sepExists_sepConj_right, bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  have hfn : libsignalSessionCode.fnOff withSenderChainSym = 0x117e8 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x117e8
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initWithSenderChain img.base
    (Rust.withPanics ext) hfn 0x117e8 524
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr withSenderChainSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hser hpser hshim halloc hdealloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr withSenderChainSym = entry
  rcases g with ⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by simp [bytesToBv8, h_7]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 128#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP (mid := entry + 183004#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h_5
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 144#64)
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [h_5]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP (mid := entry + 184280#64)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      conv =>
        arg 4
        simp only [CryptoVerification.SignalSession.CliExt.memHookStack,
          ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by simp [bytesToBv8, h_6]
      refine SepWPp.fold (cells_three_entails s0.sp _ _ _) (by sep_focus) ?_
      refine SepWPp.call_frame
        (x := (s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp -
        120#64)) hpser
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := entry + 176#64) (by wp_norm_lhs)
        (by dsimp only [privKeySerializeSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
        hlen_priv32
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [privKeySerializeSpec, rustPanicOnOom] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_4.trace = sf_3.trace›, htrace2,
            ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [privKeySerializeSpec]
        simp only [*, arm64_norm, bv_sub_add_lit', BitVec.sub_sub, BitVec.reduceAdd,
          sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun privBoxPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_priv⟩ => ?_
      apply SepWPp.of_sepWP (mid := entry + 260#64)
      wp_steps
      wp_call hshim ()
      wp_steps
      wp_call halloc (32, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_true]
        refine sepWPp_pure_mid fun htrace3 => ?_
        apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x117e8))
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace3,
            ‹sf_5.trace = sm2.trace›, htr2])) hm
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_false, ‹sf_5.sp = sm2.sp›, hspm2, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod3, htrace3⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [← hlen_priv32]
        wp_call hmemcpy (sf_6.readReg64 (Reg.gpr 0#5), privBoxPtr, bytesToBv8 senderRatchetPriv32)
        simp only [hlen_priv32, h_6, CryptoVerification.SignalSession.CliExt.memHookStack,
          ‹sf_6.sp = sf_5.sp›, ‹sf_5.sp = sm2.sp›, hspm2]
        wp_steps
        wp_call hdealloc (privBoxPtr, bytesToBv8 senderRatchetPriv32, 32, 1)
        wp_steps
        wp_call hdealloc (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
        wp_steps
        apply SepWP.replace_pre (by sep_focus)
          (stack_withSenderChain_tail_entails s0.sp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
        have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
          (sf_3.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
          senderChainIdx pre144 post100 h_8
        have hlen_full : (pre144 ++ (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
            post100)).length = 344 := by
          simp [h_8, h]
        refine sepWP_focus (T :=
          (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_3.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xb0#64) ↦₆₄ sf_6.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xc0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xd0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xf0#64) ↦₃₂ senderChainIdx) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_focus) ?_
        rw [hpack_in, ← hlen_full]
        wp_call hmemcpy (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
          (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
        simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ h_8,
          CryptoVerification.SignalSession.CliExt.memHookStack, sepConj_assoc]
        wp_done

private theorem fnAddr_ecPubKeySerialize_from_withReceiverChain_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr ecPubKeySerializeSym =
      (tripleRatchetProgAtExt b ext).fnAddr withReceiverChainSym + 181804#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
    CryptoVerification.libsignalSessionCode_fnOff_0x11c98]
  bv_omega

private theorem fnAddr_growOneChain_from_withReceiverChain_ext
    (b : BitVec 64) (ext : String → Option (State → State)) :
    (tripleRatchetProgAtExt b ext).fnAddr growOneChainSym =
      (tripleRatchetProgAtExt b ext).fnAddr withReceiverChainSym + 16404#64 := by
  dsimp only [tripleRatchetProgAtExt]
  rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
    CryptoVerification.libsignalSessionCode_fnOff_0x15cac,
    CryptoVerification.libsignalSessionCode_fnOff_0x11c98]
  bv_omega

theorem withReceiverChain_empty_base_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hM : SessionMemHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr withReceiverChainSym)
      (withReceiverChainEmptySpec A img) := by
  unfold withReceiverChainEmptySpec rustPanicOnOom
  simp only [stackAt_withReceiverChain_entry]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_sub_add_lit',
      BitVec.reduceSub, sepConj_assoc]
  have hser :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr withReceiverChainSym + 181804#64)
        (ecPubKeySerializeAllocSpec A img) :=
    (fnAddr_ecPubKeySerialize_from_withReceiverChain_ext img.base ext) ▸
      ecPubKeySerialize_alloc_ok_ext (img := img) hM.shim hM.alloc
  have hgrow :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr withReceiverChainSym + 16404#64)
        (growOneChainZeroRegionSpec A img) :=
    (fnAddr_growOneChain_from_withReceiverChain_ext img.base ext) ▸
      growOneChain_zero_region_ok_ext (img := img) hM.shim hM.alloc
  have hshim := shim_ok_at_session_ext img.base hM.shim withReceiverChainSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hM.alloc withReceiverChainSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_alloc")])
  have hdealloc := dealloc_bytes_ok_at_ext (b := img.base) (ext := ext)
    hM.alloc (name := withReceiverChainSym) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "__rustc::__rust_dealloc")])
  have hmemcpy := memcpy_ok_at_session_ext img.base hM.memcpy withReceiverChainSym
    (num% (ls_off% "memcpy" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98, (ls_stub% "memcpy")])
  have hpanic := panic_at_handle_error_ext img.base ext withReceiverChainSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x11c98,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hM
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff withReceiverChainSym = 0x11c98 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x11c98
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.withReceiverChain img.base
    (Rust.withPanics ext) hfn 0x11c98 972
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr withReceiverChainSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hser hgrow hshim halloc hdealloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr withReceiverChainSym = entry
  examples_hide_fetches
  rcases g with ⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩
  dsimp only at *
  subst h_1 h_2 h_3 h_4
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by simp [bytesToBv8, h_6]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 68#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 368#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP (mid := entry + 181804#64)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := entry + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      h_5
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocSpec, rustPanicOnOom] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 144#64)
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x11c98))
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) hpanic fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [h_5]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP (mid := entry + 16404#64)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33, CryptoVerification.SignalSession.CliExt.memHookStack,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1]
      wp_steps
      wp_call hdealloc (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      conv =>
        arg 4
        simp only [‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1]
      refine SepWPp.call_frame (x := (s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr)) hgrow
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := entry + 364#64) (by wp_norm_lhs)
        (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC,
        State.sp_setPState, ite_false, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1, BitVec.sub_sub, BitVec.reduceAdd]; rfl)
        (by wp_norm_lhs)
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [growOneChainZeroRegionSpec, rustPanicOnOom] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_5.trace = sf_4.trace›, ‹sf_4.trace = sf_3.trace›,
            htrace2, ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [growOneChainZeroRegionSpec]
        simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
          sepConj_assoc]
      refine SepWPp.exists_elim fun chainBufPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_buf⟩ => ?_
      conv =>
        arg 4
        simp only [memRegion_416_receiverChain_split chainBufPtr, cells, sepConj_emp,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
          sepConj_assoc]
      repeat (refine SepWPp.exists_elim fun _ => ?_)
      apply SepWPp.of_sepWP_ret
      wp_steps
      have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
        chainBufPtr pre72 post248 h_7
      have hlen_full : (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248)).length = 344 :=
        by simp [h_7, h]
      refine sepWP_focus (T :=
        (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
        ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ chainBufPtr) ∗ ((s0.readReg64 (.gpr 0#5) +
        0x58#64) ↦₆₄ 1#64) ∗ ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_focus) ?_
      rw [hpack_in, ← hlen_full]
      wp_call hmemcpy (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre72 ++
        (receiverChainVecBytes24 chainBufPtr ++ post248))
      simp only [← withReceiverChain_pack344 _ _ _ _ h_7,
        CryptoVerification.SignalSession.CliExt.memHookStack, hspm2]
      wp_steps
      unfold receiverChainElemAt receiverChainVecFieldsAt
      simp only [sepConj_assoc]
      wp_done

theorem ecPubKeySerializeRaw_ok_ext {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hShim : HookSat ext shimName CryptoVerification.SignalSession.CliExt.shimSpec)
    (hA : AllocHooks A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ecPubKeySerializeSym)
      (ecPubKeySerializeRawSpec A img) := by
  unfold ecPubKeySerializeRawSpec rustPanicOnOom
  simp only [bytesToBv8_encodeEC_raw]
  cells_unfold
  have hshim := shim_ok_at_session_ext img.base hShim ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  have halloc := alloc_ok_at_ext img.base A ext hA ecPubKeySerializeSym
    (num% (ls_off% "__rustc::__rust_alloc" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "__rustc::__rust_alloc")])
  have hpanic := panic_at_handle_error_ext img.base ext ecPubKeySerializeSym
    (num% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    (by rw [CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4,
      (ls_stub% "alloc::raw_vec::handle_error")])
  clear hShim hA
  wpp_init g s0
  have hfn : libsignalSessionCode.fnOff ecPubKeySerializeSym = 0x3e2c4 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x3e2c4
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.LibsignalTripleRatchet.libsignalTripleRatchetBin img.base
    (Rust.withPanics ext) hfn 0x3e2c4 84
  replace hpc : s0.pc = (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr ecPubKeySerializeSym := by
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr ecPubKeySerializeSym = entry
  examples_hide_fetches
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells keyPtr]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := entry + 32#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" - 0x3e2c4))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_raw, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 =>
      SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u2 =>
      SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd]
    wp_done

end SessionStateCalleesExt

/-! ## Relocatable `[LibsignalPlacement]` Contracts -/

section PlacedSessionStateCallees

private def withLsCl {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with
    pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝
    post := fun x s0 sf => ⌜LibsignalCodeLoaded pl sf.mem⌝ ∗ spec.post x s0 sf }

private theorem ls_subroutine_ok_cl_of_block [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (_hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have ⟨hcl0, _⟩ := extract_withLsCodeLoaded hpre
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j (Nat.lt_of_lt_of_le hj (by decide)) hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre hsp hQL
  have hclf : LibsignalCodeLoaded lsmpl sf.mem := hcl0.of_keepsFrozen hstepsQ.keepsFrozen
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  refine reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withLsCl]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hclf, hpost⟩
  · exact Or.inr hrest

private theorem ls_subroutine_ok_cl_of_plain [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withLsCl lsmpl spec) :=
  ls_subroutine_ok_cl_of_block (callerProg := callerProg)
    (subroutine_ok_withLsCodeLoaded_of_plain hcallee) hi hj hj_unmut

private theorem SepWPp.of_sepWP_lscl {prog : Program} {pl : Obj.MultiPlacement}
    {mid ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P
      (fun sm Pm => LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ (h : LibsignalCodeLoaded pl _) hkf => h.of_keepsFrozen hkf) hcl h

private theorem SepWPp.call_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call (x := x) (F := F) hcall hpc hrun hsp hlr ?_ hexit hpanic ?_
    (fun sf R' hoom_s hm => (hoom sf _ hoom_s hm).elim)
  · intro R hm
    dsimp only [withLsCl]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  · intro sf hpcm hrunm hspm hcsm
    dsimp only [withLsCl]
    rw [sepConj_assoc]
    exact SepWPp.pure_elim (hnext sf hpcm hrunm hspm hcsm)

private theorem SepWPp.call_frame_lscl {α : Type} {prog : Program} {pl : Obj.MultiPlacement}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcall : subroutine_ok prog entry (withLsCl pl spec))
    (hcl : LibsignalCodeLoaded pl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = ⌜φ⌝ ∗ T)
    (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      LibsignalCodeLoaded pl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SepWPp prog ret s P Q Qp := by
  refine SepWPp.call_lscl (x := x) (F := F) hcall hcl hpc hrun hsp hlr ?_ hexit hpanic hnext hoom
  intro R hm
  rw [hspec, sepConj_assoc, satisfies_pure_sepConj, ← sepConj_assoc, ← hP]
  exact ⟨hφ, hm⟩

attribute [local irreducible] withLsCl

def rustPanicOnOomPlaced {α : Type} : α → State → State → SepProp :=
  fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

theorem dealloc_bytes_placed_ok [LibsignalPlacement] {A : RustAlloc} {prog : Program}
    {H : LibsignalHooks} {i : Nat} [IsLsBlockProg prog i H]
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hi : i < 619 := by decide)
    (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocBytesSpec A) := by
  have hd : subroutine_ok prog (lsρ lsRustDeallocSym) (rustDeallocSpec A) :=
    ls_hook_ok_of_mem hdealloc (by decide) hi hunmut
  apply subroutine_ok_outcome_intro
  intro ⟨p, bs, n, align⟩ R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (rustDeallocSpec A).pre (p, n, align) s0 ∗ R := by
    unfold rustDeallocBytesSpec at hpre
    unfold rustDeallocSpec
    dsimp only at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hpre⟩
    refine ⟨⟨hx0, hx1, hx2⟩, ?_⟩
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc] at hpre ⊢
    refine Satisfies.mono ?_ hpre
    rw [← hlen]
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (pointsToBytes_entails_memRegion
      p bs)))
  exact (hd.to_outcome (p, n, align) R s0 hpc hrun hpre' hsp).mono_outcome fun _ h => h

def privKeySerializePlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × List (BitVec 8) × BitVec 64) where
  pre := fun (privKeyPtr, sk, outVecPtr) s =>
    ⌜s.readReg64 .x0 = privKeyPtr ∧ s.readReg64 .x8 = outVecPtr ∧ sk.length = 32⌝ ∗
      (privKeyPtr ↦ₛ sk) ∗ cells outVecPtr 3 ∗
    (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun (privKeyPtr, sk, outVecPtr) s0 sf =>
    ∃∗ bufPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ bufPtr ≠ 0⌝ ∗ (privKeyPtr ↦ₛ sk) ∗
      (outVecPtr ↦₆₄ 32#64) ∗
      ((outVecPtr + 8#64) ↦₆₄ bufPtr) ∗ ((outVecPtr + 16#64) ↦₆₄ 32#64) ∗ (bufPtr ↦ₛ sk) ∗
        A.live bufPtr 32 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem privKeySerialize_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_208).rebase (blkPl_208).base H) (blkPl_208).base
      (privKeySerializePlacedSpec A) := by
  unfold privKeySerializePlacedSpec rustPanicOnOomPlaced
  simp only [stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_208).rebase (blkPl_208).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hpanic' : ((blkPC_208).rebase (blkPl_208).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  wpp_init g s0
  obtain ⟨privKeyPtr, sk, outVecPtr⟩ := g
  dsimp only at *
  subst h_1 h_2
  obtain ⟨w0, w1, w2, w3, _, hsk_cells⟩ := exists_unpack64_of_length_32 h
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_208).base + 36#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm =>
      by simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
          ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    simp only [hoom, ite_false, hm32, cells, sepConj_emp, sepExists_sepConj_left,
      sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    rw [hsk_cells (s0.readReg64 (Reg.gpr 0#5))]
    wp_steps
    simp only [hsk_cells, sepConj_assoc]
    wp_done

def ecPubKeySerializeAllocPlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × Bytes) where
  pre := fun (keyPtr, keyBytes) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32⌝ ∗ (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
    (memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun (keyPtr, keyBytes) s0 sf =>
    ∃∗ outPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = outPtr ∧ sf.readReg64 .x1 =
      33#64 ∧ outPtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (outPtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
        A.live outPtr 33 1 ∗
      (memRegion (s0.sp - 4128#64) 32 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem ecPubKeySerialize_alloc_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeAllocPlacedSpec A) := by
  unfold ecPubKeySerializeAllocPlacedSpec rustPanicOnOomPlaced
  simp only [bytesToBv8_encodeEC_alloc, stackAt_privKeySerialize]
  cells_unfold_fast
  have hshim' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hpanic' : ((blkPC_205).rebase (blkPl_205).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  wpp_init g s0
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  subst h_1
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells (s0.readReg64 (Reg.gpr 0#5))]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_205).base + 32#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_alloc, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 =>
      SepWPp.exists_elim fun b0 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_done

theorem finishGrowZero_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A)) :
    subroutine_ok ((blkPC_45).rebase (blkPl_45).base H) (blkPl_45).base
      (finishGrowZeroSpec A) := by
  unfold finishGrowZeroSpec
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_45).rebase (blkPl_45).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  wp_init x s0
  obtain ⟨out, cap, ptr, new, bs, o0, o1, o2, fsp⟩ := x
  dsimp only at *
  subst fsp
  subst cap
  have humulh := umulh_104_eq_zero h
  have hhi := hi_104_eq_false h
  have hcbz := beq_mul_104_zero_eq_false h_11 h
  have hmul : (104#64 * new).toNat = new.toNat * 104 := mul_104_toNat (by omega)
  have hpow8 : ∃ k, 8 = 2 ^ k := ⟨3, rfl⟩
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (new.toNat * 104, 8)
  wp_steps
  wp_if hoom
  · have hoom' : sf_1.readReg64 Reg.x0 ≠ 0 := hoom
    simp only [hoom', ite_false]
    wp_steps
    apply SepWP.instantiate_post_exists 0#64
    apply SepWP.instantiate_post_exists (sf_1.readReg64 Reg.x0)
    simp only [(by decide : (0#64 : BitVec 64) = 1#64 ↔ False), ite_false]
    wp_done
  · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true]
    wp_steps
    apply SepWP.instantiate_post_exists 1#64
    apply SepWP.instantiate_post_exists 8#64
    simp only [ite_true]
    wp_done

def growOneChainZeroPlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (vecPtr, oldPtr) s =>
    ⌜s.readReg64 .x0 = vecPtr⌝ ∗ (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool ∗
      cells (s.sp - 64#64) 8 ∗
    cells (s.sp - 112#64) 6 ∗ stackAt (s.sp - 112#64) allocHookStack
  post := fun (vecPtr, _oldPtr) s0 sf =>
    ∃∗ newPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗ (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr +
      8#64) ↦₆₄ newPtr) ∗ A.live newPtr 416 8 ∗
      memRegion newPtr 416 ∗ A.pool ∗ cells (s0.sp - 64#64) 8 ∗ cells (s0.sp - 112#64) 6 ∗
        stackAt (s0.sp - 112#64) allocHookStack
  onPanic := rustPanicOnOomPlaced

theorem growOneChain_zero_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec A)) := by
  unfold withLsCodeLoaded growOneChainZeroPlacedSpec rustPanicOnOomPlaced
  cells_unfold
  have hpanic' : ((blkPC_43).rebase (blkPl_43).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hfg0 := ls_subroutine_ok_of_block (callerProg := (blkPC_43).rebase (blkPl_43).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain (finishGrowZero_placed_ok hshim halloc))
  change subroutine_ok _ (lsmpl.base 45) _ at hfg0
  simp only [withLsCodeLoaded, finishGrowZeroSpec, cells, sepExists_sepConj_right, sepConj_emp,
    bv_sub_add_lit', BitVec.reduceSub] at hfg0
  wpp_init x s0
  obtain ⟨vecPtr, oldPtr⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst vecPtr
  apply SepWPp.of_sepWP (mid := (blkPl_43).base + 60#64)
  apply sepWP_seq_lscl hcl0 (mid := lsmpl.base 45)
  wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hcl1
  wp_call hfg0 (s0.sp - 56#64, 0#64, oldPtr, 4#64, [], v_stk_7, v_stk_8, v_stk_9, s0.sp - 64#64)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases htag : w = 1#64
  · simp only [htag, ite_true, sepConj_assoc]
    refine SepWPp.pure_elim fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm,
        *])) hm
  · simp only [htag, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hw0, hp', htrace⟩ => ?_
    subst hw0
    apply SepWPp.of_sepWP_ret
    wp_steps
    wp_done

def growOneChainZeroRegionPlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64) where
  pre := fun (vecPtr, oldPtr) s =>
    ⌜s.readReg64 .x0 = vecPtr⌝ ∗ (vecPtr ↦₆₄ 0#64) ∗ ((vecPtr + 8#64) ↦₆₄ oldPtr) ∗ A.pool ∗
      memRegion (s.sp - 4208#64) 80 ∗
    memRegion (s.sp - 4128#64) 32 ∗ stackAt s.sp allocHookStack
  post := fun (vecPtr, _oldPtr) s0 sf =>
    ∃∗ newPtr : BitVec 64, ⌜sf.trace = s0.trace ∧ newPtr ≠ 0#64⌝ ∗ (vecPtr ↦₆₄ 4#64) ∗ ((vecPtr +
      8#64) ↦₆₄ newPtr) ∗ A.live newPtr 416 8 ∗
      memRegion newPtr 416 ∗ A.pool ∗ memRegion (s0.sp - 4208#64) 80 ∗ memRegion (s0.sp -
        4128#64) 32 ∗ stackAt s0.sp allocHookStack
  onPanic := rustPanicOnOomPlaced

theorem growOneChain_zero_region_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (growOneChainZeroRegionPlacedSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro g R s0 hpc hrun hpre hsp
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (growOneChainZeroPlacedSpec A)).pre g s0 ∗ R := by
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpre
  refine ((growOneChain_zero_placed_ok hshim halloc hpanic).to_outcome
    g R s0 hpc hrun hpre' hsp).mono_outcome ?_
  rintro sf (⟨hret, hcs, hpost⟩ | hrest)
  · left
    refine ⟨hret, hcs, ?_⟩
    simpa only [withLsCodeLoaded, growOneChainZeroRegionPlacedSpec, growOneChainZeroPlacedSpec,
      stackAt_growOneChain, sepConj_assoc] using hpost
  · exact Or.inr hrest

def sessionStateNewPlacedSpec (A : RustAlloc) : Spec SessionStateNewGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg32 .x0 = g.version ∧ s.readReg64 .x1 = g.localIkPtr ∧
      s.readReg64 .x2 = g.remoteIkPtr ∧
      s.readReg64 .x3 = g.rootKeyPtr ∧ s.readReg64 .x4 = g.baseKeyPtr ∧ s.readReg64 .x5 =
        g.spqrVecPtr ∧ g.localIk32.length = 32 ∧
      g.remoteIk32.length = 32 ∧ g.rootKey32.length = 32 ∧ g.baseKey32.length = 32⌝ ∗
        (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗
    (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗ (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗
    (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr + 0x08#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.spqrVecPtr +
      0x10#64) ↦₆₄ g.spqrLen) ∗
    memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4224#64) 128 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ localIkBoxPtr : BitVec 64, ∃∗ remoteIkBoxPtr : BitVec 64, ∃∗ rootKeyBoxPtr : BitVec 64, ∃∗
      baseKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ localIkBoxPtr ≠ 0 ∧ remoteIkBoxPtr ≠ 0 ∧ rootKeyBoxPtr ≠ 0 ∧
        baseKeyBoxPtr ≠ 0⌝ ∗
      (g.localIkPtr ↦ₛ bytesToBv8 g.localIk32) ∗ (g.remoteIkPtr ↦ₛ bytesToBv8 g.remoteIk32) ∗
        (g.rootKeyPtr ↦ₛ bytesToBv8 g.rootKey32) ∗
      (g.baseKeyPtr ↦ₛ bytesToBv8 g.baseKey32) ∗ (g.spqrVecPtr ↦₆₄ g.spqrCap) ∗ ((g.spqrVecPtr +
        0x08#64) ↦₆₄ g.spqrBufPtr) ∗
      ((g.spqrVecPtr + 0x10#64) ↦₆₄ g.spqrLen) ∗
        (localIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.localIk32)) ∗ A.live localIkBoxPtr 33 1 ∗
      (remoteIkBoxPtr ↦ₛ bytesToBv8 (encodeEC g.remoteIk32)) ∗ A.live remoteIkBoxPtr 33 1 ∗
      (rootKeyBoxPtr ↦ₛ bytesToBv8 g.rootKey32) ∗ A.live rootKeyBoxPtr 32 1 ∗
      (baseKeyBoxPtr ↦ₛ bytesToBv8 (encodeEC g.baseKey32)) ∗ A.live baseKeyBoxPtr 33 1 ∗
        (g.outPtr ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x08#64) ↦₆₄ localIkBoxPtr) ∗ ((g.outPtr + 0x10#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x18#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x20#64) ↦₆₄ remoteIkBoxPtr) ∗ ((g.outPtr + 0x28#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x30#64) ↦₆₄ 32#64) ∗
      ((g.outPtr + 0x38#64) ↦₆₄ rootKeyBoxPtr) ∗ ((g.outPtr + 0x40#64) ↦₆₄ 32#64) ∗ ((g.outPtr +
        0x48#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x50#64) ↦₆₄ 8#64) ∗ ((g.outPtr + 0x58#64) ↦₆₄ 0#64) ∗ ((g.outPtr +
        0x60#64) ↦₆₄ 33#64) ∗
      ((g.outPtr + 0x68#64) ↦₆₄ baseKeyBoxPtr) ∗ ((g.outPtr + 0x70#64) ↦₆₄ 33#64) ∗ ((g.outPtr +
        0x78#64) ↦₆₄ g.spqrCap) ∗
      ((g.outPtr + 0x80#64) ↦₆₄ g.spqrBufPtr) ∗ ((g.outPtr + 0x88#64) ↦₆₄ g.spqrLen) ∗ ((g.outPtr +
        0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.outPtr + 0x98#64) 96 ∗ ((g.outPtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
        memRegion (g.outPtr + 0x100#64) 40 ∗
      ((g.outPtr + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (g.outPtr + 0x130#64) 24 ∗
      ((g.outPtr + 0x148#64) ↦₃₂ (BitVec.ofNat 32 (g.version.toNat % 256))) ∗ ((g.outPtr +
        0x14c#64) ↦₆₄ 0#64) ∗
      ((g.outPtr + 0x154#64) ↦₃₂ 0#32) ∗ (memRegion (s0.sp - 4224#64) 128 ∗
        stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem sessionStateNew_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_37).rebase (blkPl_37).base H) (blkPl_37).base
      (withLsCodeLoaded lsmpl (sessionStateNewPlacedSpec A)) := by
  unfold withLsCodeLoaded sessionStateNewPlacedSpec rustPanicOnOomPlaced
  simp only [stackAt_sessionStateNew_entry, memRegion_344_sessionStateNew_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wpp_init g s0
  rcases g with ⟨outPtr, version, localIkPtr, localIk32, remoteIkPtr, remoteIk32,
    rootKeyPtr, rootKey32, baseKeyPtr, baseKey32, spqrVecPtr, spqrCap, spqrBufPtr, spqrLen⟩
  dsimp only at *
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_37).rebase (blkPl_37).base H)
    (ecPubKeySerialize_alloc_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec A)) at hser
  have hshim' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_37).rebase (blkPl_37).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hpanic' : ((blkPC_37).rebase (blkPl_37).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr version localIkPtr remoteIkPtr rootKeyPtr baseKeyPtr spqrVecPtr
  have hlen_rk : (bytesToBv8 rootKey32).length = 32 := by simp [bytesToBv8, ‹rootKey32.length = 32›]
  obtain ⟨rk0, rk1, rk2, rk3, _, hrk_cells⟩ := exists_unpack64_of_length_32 hlen_rk
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 1#5), localIk32)) hser hcl1
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := (blkPl_37).base + 60#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocPlacedSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    ‹localIk32.length = 32› (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm]) h) hm)
    (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 => ?_)
  simp only [arm64_norm] at hspm1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
  rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29⟩
  simp only [arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
  clear hpre
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun localIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_local⟩ => ?_
  apply SepWPp.of_sepWP_lscl hclm1 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl2
  refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 2#5), remoteIk32)) hser hcl2
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [State.spAligned, arm64_norm, hspm1, hsp_align])
    (ret_pc := (blkPl_37).base + 76#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeAllocPlacedSpec]; simp only [arm64_norm, hspm1, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    ‹remoteIk32.length = 32› (by sep_focus) (fun _ _ _ _ hm => allowPanic_not_exited hm) (fun sm _ hm => by
      dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
      exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
        htr1]) h) hm)
    (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 hclm2 => ?_)
  simp only [arm64_norm, hspm1] at hspm2
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
  rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
    hcs2_27, hcs2_28, hcs2_29⟩
  simp only [arm64_norm, hcs1_19, hcs1_20, hcs1_21, hcs1_24, hcs1_25]
    at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
  conv =>
    arg 4
    dsimp only [ecPubKeySerializeAllocPlacedSpec]
    simp only [arm64_norm, hspm1, htr1, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
      sepConj_assoc]
  refine SepWPp.exists_elim fun remoteIkBoxPtr => ?_
  refine SepWPp.pure_left fun ⟨htr2, hx0_2, hx1_2, hne_remote⟩ => ?_
  apply SepWPp.of_sepWP_lscl hclm2 (mid := (blkPl_37).base + 100#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl3
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    conv =>
      arg 4
      simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = sm2.trace›, htr2])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom, ite_false, ‹sf.sp = sm2.sp›, hspm2, hm32, cells, sepConj_emp,
        sepExists_sepConj_left,
        sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    rw [hrk_cells (s0.readReg64 (.gpr 3#5))]
    apply SepWPp.of_sepWP_lscl hcl3 (mid := lsmpl.base 205)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl4
    refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 4#5), baseKey32)) hser hcl4
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := (blkPl_37).base + 128#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocPlacedSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      ‹baseKey32.length = 32›
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
        exact allowPanic_frame (fun h => allocFailedIn_of_trace_eq (by simp only [arm64_norm,
          htrace, ‹sf.trace = sm2.trace›, htr2]) h) hm)
      (fun sm3 hpcm3 hrunm3 hspm3 hcsm3 _hclm3 => ?_)
    simp only [*, arm64_norm] at hspm3
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm3
    rcases hcsm3 with ⟨hcs3_19, hcs3_20, hcs3_21, hcs3_22, hcs3_23, hcs3_24, hcs3_25, hcs3_26,
      hcs3_27, hcs3_28, hcs3_29⟩
    simp only [*, arm64_norm]
      at hcs3_19 hcs3_20 hcs3_21 hcs3_22 hcs3_23 hcs3_24 hcs3_25 hcs3_26 hcs3_27 hcs3_28 hcs3_29
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocPlacedSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun baseKeyBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr3, hx0_3, hx1_3, hne_base⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [hrk_cells, sepConj_assoc]
    wp_done

def withSenderChainNonePlacedSpec (A : RustAlloc) :
    Spec WithSenderChainGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x1 = g.senderKeyPairPtr ∧
      s.readReg64 .x2 = g.senderChainKeyPtr ∧
      g.senderRatchetPub32.length = 32 ∧ g.senderRatchetPriv32.length = 32 ∧
        g.senderChainKey32.length = 32 ∧ g.pre144.length = 144 ∧
      g.post100.length = 100⌝ ∗ (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
    ((g.senderKeyPairPtr + 32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗
    ((g.senderChainKeyPtr + 32#64) ↦₃₂ g.senderChainIdx) ∗ (g.inPtr ↦ₛ g.pre144) ∗ ((g.inPtr +
      0x90#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (g.inPtr + 0x98#64) 92 ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗ memRegion g.outPtr 344 ∗
    (memRegion (s.sp - 4256#64) 160 ∗ stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ senderRatchetPubBoxPtr : BitVec 64, ∃∗ senderRatchetPrivBoxPtr : BitVec 64, ∃∗
      senderChainKeyBoxPtr : BitVec 64,
      ⌜sf.trace = s0.trace ∧ senderRatchetPubBoxPtr ≠ 0 ∧ senderRatchetPrivBoxPtr ≠ 0 ∧
        senderChainKeyBoxPtr ≠ 0⌝ ∗
      (g.senderKeyPairPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗ ((g.senderKeyPairPtr +
        32#64) ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
      (g.senderChainKeyPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ ((g.senderChainKeyPtr +
        32#64) ↦₃₂ g.senderChainIdx) ∗
      (senderRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
        A.live senderRatchetPubBoxPtr 33 1 ∗
      (senderRatchetPrivBoxPtr ↦ₛ bytesToBv8 g.senderRatchetPriv32) ∗
        A.live senderRatchetPrivBoxPtr 32 1 ∗
      (senderChainKeyBoxPtr ↦ₛ bytesToBv8 g.senderChainKey32) ∗ A.live senderChainKeyBoxPtr 32 1 ∗
        (g.outPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.outPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.outPtr + 0xf4#64) ↦ₛ g.post100) ∗
        (g.inPtr ↦ₛ g.pre144) ∗
      senderChainFieldsAt g.inPtr senderRatchetPubBoxPtr senderRatchetPrivBoxPtr
        senderChainKeyBoxPtr g.senderChainIdx ∗ ((g.inPtr + 0xf4#64) ↦ₛ g.post100) ∗
      (memRegion (s0.sp - 4256#64) 160 ∗ stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem withSenderChain_none_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_27).rebase (blkPl_27).base H) (blkPl_27).base
      (withLsCodeLoaded lsmpl (withSenderChainNonePlacedSpec A)) := by
  unfold withLsCodeLoaded withSenderChainNonePlacedSpec rustPanicOnOomPlaced
  simp only [stackAt_withSenderChain_entry, memRegion_92_senderChain_split]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wpp_init g s0
  rcases g with ⟨outPtr, inPtr, senderKeyPairPtr, senderRatchetPub32,
    senderRatchetPriv32, senderChainKeyPtr, senderChainKey32, senderChainIdx, pre144, post100⟩
  dsimp only at *
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (ecPubKeySerialize_alloc_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec A)) at hser
  have hpser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_27).rebase (blkPl_27).base H)
    (privKeySerialize_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 208) (withLsCl lsmpl (privKeySerializePlacedSpec A)) at hpser
  have hshim' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_27).rebase (blkPl_27).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_27).rebase (blkPl_27).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec := ls_hook_ok_of_mem hmemcpy
  have hpanic' : ((blkPC_27).rebase (blkPl_27).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderKeyPairPtr senderChainKeyPtr
  have hlen_ck : (bytesToBv8 senderChainKey32).length = 32 := by
    simp [bytesToBv8, ‹senderChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP_lscl hcl0 (mid := (blkPl_27).base + 68#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 128#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 205)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl2
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser hcl2
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := (blkPl_27).base + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocPlacedSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      ‹senderRatchetPub32.length = 32›
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocPlacedSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP_lscl hclm1 (mid := (blkPl_27).base + 144#64)
    wp_steps
    wp_call hshim' ()
    wp_steps
    wp_call halloc' (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl3
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [‹senderRatchetPub32.length = 32›]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP_lscl hcl3 (mid := lsmpl.base 208)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy' (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33]
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl4
      have hlen_priv32 : (bytesToBv8 senderRatchetPriv32).length = 32 := by
        simp [bytesToBv8, ‹senderRatchetPriv32.length = 32›]
      refine SepWPp.fold (cells_three_entails s0.sp _ _ _) (by sep_focus) ?_
      refine SepWPp.call_frame_lscl
        (x := (s0.readReg64 (.gpr 1#5) + 32#64, bytesToBv8 senderRatchetPriv32, s0.sp -
        120#64)) hpser hcl4
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := (blkPl_27).base + 176#64) (by wp_norm_lhs)
        (by dsimp only [privKeySerializePlacedSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
        hlen_priv32
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [privKeySerializePlacedSpec, rustPanicOnOomPlaced] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_4.trace = sf_3.trace›, htrace2,
            ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [privKeySerializePlacedSpec]
        simp only [*, arm64_norm, bv_sub_add_lit', BitVec.sub_sub, BitVec.reduceAdd,
          sepExists_sepConj_left, sepConj_assoc]
      refine SepWPp.exists_elim fun privBoxPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_priv⟩ => ?_
      apply SepWPp.of_sepWP (mid := (blkPl_27).base + 260#64)
      wp_steps
      wp_call hshim' ()
      wp_steps
      wp_call halloc' (32, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      by_cases hoom3 : sf_6.readReg64 (Reg.gpr 0#5) = 0
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) = 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_true]
        refine sepWPp_pure_mid fun htrace3 => ?_
        apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
        wp_steps
        apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
        simpa only [sepConj_assoc] using
          allowPanic_panicked
            (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace3,
            ‹sf_5.trace = sm2.trace›, htr2])) hm
      · have hoom3_64 : sf_6.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom3
        conv =>
          arg 4
          simp only [hoom3, ite_false, ‹sf_5.sp = sm2.sp›, hspm2, sepConj_assoc]
        refine sepWPp_pure_mid fun ⟨hmod3, htrace3⟩ => ?_
        apply SepWPp.of_sepWP_ret
        wp_steps
        rw [← hlen_priv32]
        wp_call hmemcpy' (sf_6.readReg64 (Reg.gpr 0#5), privBoxPtr, bytesToBv8 senderRatchetPriv32)
        simp only [hlen_priv32, ‹senderRatchetPriv32.length = 32›]
        wp_steps
        wp_call hdealloc' (privBoxPtr, bytesToBv8 senderRatchetPriv32, 32, 1)
        wp_steps
        wp_call hdealloc' (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
        wp_steps
        have hpack_in := withSenderChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
          (sf_3.readReg64 (.gpr 0#5)) (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5))
          senderChainIdx pre144 post100 ‹pre144.length = 144›
        have hlen_full : (pre144 ++ (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++
            post100)).length = 344 := by
          simp [‹pre144.length = 144›, ‹post100.length = 100›]
        refine sepWP_focus (T :=
          (s0.readReg64 (.gpr 0#5) ↦ₛ pre144) ∗ ((s0.readReg64 (.gpr 0#5) + 0x90#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0x98#64) ↦₆₄ sf_3.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa0#64) ↦₆₄ 33#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xa8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xb0#64) ↦₆₄ sf_6.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xb8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xc0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xc8#64) ↦₆₄ 8#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xd0#64) ↦₆₄ 0#64) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xd8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xe0#64) ↦₆₄ sf_1.readReg64 (.gpr 0#5)) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xe8#64) ↦₆₄ 32#64) ∗ ((s0.readReg64 (.gpr 0#5) +
          0xf0#64) ↦₃₂ senderChainIdx) ∗
          ((s0.readReg64 (.gpr 0#5) + 0xf4#64) ↦ₛ post100)) (by sep_focus) ?_
        rw [hpack_in, ← hlen_full]
        wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre144 ++
          (senderChainBytes100 (sf_3.readReg64 (.gpr 0#5))
            (sf_6.readReg64 (.gpr 0#5)) (sf_1.readReg64 (.gpr 0#5)) senderChainIdx ++ post100))
        simp only [← withSenderChain_pack344 _ _ _ _ _ _ _ ‹pre144.length = 144›]
        wp_done

def withReceiverChainEmptyPlacedSpec (A : RustAlloc) :
    Spec WithReceiverChainGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x8 = g.outPtr ∧ s.readReg64 .x0 = g.inPtr ∧ s.readReg64 .x1 =
      g.senderRatchetPubPtr ∧
      s.readReg64 .x2 = g.receiverChainKeyPtr ∧ g.senderRatchetPub32.length = 32 ∧
        g.receiverChainKey32.length = 32 ∧ g.pre72.length = 72 ∧
      g.post248.length = 248⌝ ∗ (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
    (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗ ((g.receiverChainKeyPtr +
      32#64) ↦₃₂ g.receiverChainIdx) ∗
    (g.inPtr ↦ₛ g.pre72) ∗ ((g.inPtr + 0x48#64) ↦₆₄ 0#64) ∗ ((g.inPtr + 0x50#64) ↦₆₄ g.oldVecPtr) ∗
      ((g.inPtr + 0x58#64) ↦₆₄ 0#64) ∗
    ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ memRegion g.outPtr 344 ∗ (memRegion (s.sp - 4576#64) 480 ∗
      stackAt s.sp allocHookStack) ∗ A.pool
  post := fun g s0 sf =>
    ∃∗ receiverRatchetPubBoxPtr : BitVec 64, ∃∗ receiverChainKeyBoxPtr : BitVec 64, ∃∗
      chainBufPtr : BitVec 64, ⌜sf.trace = s0.trace ∧
        receiverRatchetPubBoxPtr ≠ 0 ∧ receiverChainKeyBoxPtr ≠ 0 ∧ chainBufPtr ≠ 0⌝ ∗
      (g.senderRatchetPubPtr ↦ₛ bytesToBv8 g.senderRatchetPub32) ∗
        (g.receiverChainKeyPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      ((g.receiverChainKeyPtr + 32#64) ↦₃₂ g.receiverChainIdx) ∗
        (receiverRatchetPubBoxPtr ↦ₛ bytesToBv8 (encodeEC g.senderRatchetPub32)) ∗
      A.live receiverRatchetPubBoxPtr 33 1 ∗
        (receiverChainKeyBoxPtr ↦ₛ bytesToBv8 g.receiverChainKey32) ∗
      A.live receiverChainKeyBoxPtr 32 1 ∗ A.live chainBufPtr 416 8 ∗
      receiverChainElemAt chainBufPtr receiverRatchetPubBoxPtr receiverChainKeyBoxPtr
        g.receiverChainIdx ∗
      memRegion (chainBufPtr + 0x64#64) 316 ∗ (g.outPtr ↦ₛ g.pre72) ∗
        receiverChainVecFieldsAt g.outPtr chainBufPtr ∗
      ((g.outPtr + 0x60#64) ↦ₛ g.post248) ∗ (g.inPtr ↦ₛ g.pre72) ∗
        receiverChainVecFieldsAt g.inPtr chainBufPtr ∗
      ((g.inPtr + 0x60#64) ↦ₛ g.post248) ∗ (memRegion (s0.sp - 4576#64) 480 ∗
        stackAt s0.sp allocHookStack) ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem withReceiverChain_empty_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_30).rebase (blkPl_30).base H) (blkPl_30).base
      (withLsCodeLoaded lsmpl (withReceiverChainEmptyPlacedSpec A)) := by
  unfold withLsCodeLoaded withReceiverChainEmptyPlacedSpec rustPanicOnOomPlaced
  simp only [stackAt_withReceiverChain_entry]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right, bv_sub_add_lit',
      BitVec.reduceSub, sepConj_assoc]
  wpp_init g s0
  rcases g with ⟨outPtr, inPtr, senderRatchetPubPtr, senderRatchetPub32,
    receiverChainKeyPtr, receiverChainKey32, receiverChainIdx, oldVecPtr, pre72, post248⟩
  dsimp only at *
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (ecPubKeySerialize_alloc_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsCl lsmpl (ecPubKeySerializeAllocPlacedSpec A)) at hser
  have hgrow := ls_subroutine_ok_cl_of_block (callerProg := (blkPC_30).rebase (blkPl_30).base H)
    (growOneChain_zero_region_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 43) (withLsCl lsmpl (growOneChainZeroRegionPlacedSpec A)) at hgrow
  have hshim' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hdealloc' := dealloc_bytes_placed_ok (prog := (blkPC_30).rebase (blkPl_30).base H) hdealloc
  have hmemcpy' : subroutine_ok ((blkPC_30).rebase (blkPl_30).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec := ls_hook_ok_of_mem hmemcpy
  have hpanic' : ((blkPC_30).rebase (blkPl_30).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst outPtr inPtr senderRatchetPubPtr receiverChainKeyPtr
  have hlen_ck : (bytesToBv8 receiverChainKey32).length = 32 := by
    simp [bytesToBv8, ‹receiverChainKey32.length = 32›]
  obtain ⟨ck0, ck1, ck2, ck3, _, hck_cells⟩ := exists_unpack64_of_length_32 hlen_ck
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay32 : LayoutOk 32 1 := ⟨by decide, hpow2, by decide⟩
  have hlay33 : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP_lscl hcl0 (mid := (blkPl_30).base + 68#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (32, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    conv =>
      arg 4
      simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace1,
        ‹sf.trace = s0.trace›])) hm
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    have hm32 : memRegion (sf_1.readReg64 (Reg.gpr 0#5)) 32 =
        cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 :=
      memRegion_cells (sf_1.readReg64 (Reg.gpr 0#5)) 4 (by decide)
    conv =>
      arg 4
      simp only [hoom1, ite_false, ‹sf.sp = s0.sp - 368#64›, hm32, cells, sepConj_emp,
        sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
        sepConj_assoc]
    refine SepWPp.exists_elim fun u0 => SepWPp.exists_elim fun u1 =>
      SepWPp.exists_elim fun u2 => SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    rw [hck_cells (s0.readReg64 (.gpr 2#5))]
    apply SepWPp.of_sepWP_lscl hcl1 (mid := lsmpl.base 205)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl2
    simp only [hck_cells, sepConj_assoc]
    refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 1#5), senderRatchetPub32)) hser hcl2
      (by wp_norm_lhs) (by wp_norm_lhs)
      (by simp only [*, State.spAligned, arm64_norm])
      (ret_pc := (blkPl_30).base + 92#64) (by wp_norm_lhs)
      (by dsimp only [ecPubKeySerializeAllocPlacedSpec]; simp only [*, arm64_norm, BitVec.sub_sub,
        BitVec.reduceAdd]; rfl)
      ‹senderRatchetPub32.length = 32›
      (by sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun sm _ hm => by
        dsimp only [ecPubKeySerializeAllocPlacedSpec, rustPanicOnOomPlaced] at hm
        simpa only [sepConj_assoc] using allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
          s0) (by simp only [arm64_norm, htrace1, ‹sf.trace = s0.trace›]) h) hm)
      (fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hclm1 => ?_)
    simp only [*, arm64_norm] at hspm1
    dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm1
    rcases hcsm1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
      hcs1_27, hcs1_28, hcs1_29⟩
    simp only [*, arm64_norm]
      at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28 hcs1_29
    clear hpre
    conv =>
      arg 4
      dsimp only [ecPubKeySerializeAllocPlacedSpec]
      simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
        sepConj_assoc]
    refine SepWPp.exists_elim fun pubBoxPtr => ?_
    refine SepWPp.pure_left fun ⟨htr1, hx0_1, hx1_1, hne_pub⟩ => ?_
    apply SepWPp.of_sepWP_lscl hclm1 (mid := (blkPl_30).base + 144#64)
    wp_steps
    wp_call hshim' ()
    wp_steps
    wp_call halloc' (33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hcl3
    by_cases hoom2 : sf_3.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked
          (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace2,
          ‹sf_2.trace = sm1.trace›, htr1])) hm
    · have hoom2_64 : sf_3.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      conv =>
        arg 4
        simp only [hoom2, ite_false, ‹sf_2.sp = sm1.sp›, hspm1, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      have henc33 : (encodeEC senderRatchetPub32).length = 33 := by
        change (0x05 :: senderRatchetPub32).length = 33
        simp [‹senderRatchetPub32.length = 32›]
      have hlen_pub33 : (bytesToBv8 (encodeEC senderRatchetPub32)).length = 33 := by
        simp [bytesToBv8, henc33]
      apply SepWPp.of_sepWP_lscl hcl3 (mid := lsmpl.base 43)
      wp_steps
      rw [← hlen_pub33]
      wp_call hmemcpy' (sf_3.readReg64 (Reg.gpr 0#5), pubBoxPtr,
        bytesToBv8 (encodeEC senderRatchetPub32))
      simp only [hlen_pub33, henc33]
      wp_steps
      wp_call hdealloc' (pubBoxPtr, bytesToBv8 (encodeEC senderRatchetPub32), 33, 1)
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hcl4
      conv =>
        arg 4
        simp only [‹sf_4.sp = sf_3.sp›, ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1]
      refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 0#5) + 0x48#64, oldVecPtr)) hgrow hcl4
        (by wp_norm_lhs) (by wp_norm_lhs)
        (by simp only [*, State.spAligned, arm64_norm])
        (ret_pc := (blkPl_30).base + 364#64) (by wp_norm_lhs)
        (by simp (config := { decide := true }) only [State.sp_writeReg64, State.sp_setPC,
        State.sp_setPState, ite_false, ‹sf_5.sp = sf_4.sp›, ‹sf_4.sp = sf_3.sp›,
        ‹sf_3.sp = sf_2.sp›, ‹sf_2.sp = sm1.sp›, hspm1, BitVec.sub_sub, BitVec.reduceAdd]; rfl)
        (by wp_norm_lhs)
        (by sep_focus)
        (fun _ _ _ _ hm => allowPanic_not_exited hm)
        (fun sm _ hm => by
          dsimp only [growOneChainZeroRegionPlacedSpec, rustPanicOnOomPlaced] at hm
          simpa only [sepConj_assoc] using
            allowPanic_frame (fun h => allocFailedIn_of_trace_eq (s0 :=
            s0) (by simp only [arm64_norm, ‹sf_5.trace = sf_4.trace›, ‹sf_4.trace = sf_3.trace›,
            htrace2, ‹sf_2.trace = sm1.trace›, htr1]) h) hm)
        (fun sm2 hpcm2 hrunm2 hspm2 hcsm2 _hclm2 => ?_)
      simp only [*, arm64_norm] at hspm2
      dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm2
      rcases hcsm2 with ⟨hcs2_19, hcs2_20, hcs2_21, hcs2_22, hcs2_23, hcs2_24, hcs2_25, hcs2_26,
        hcs2_27, hcs2_28, hcs2_29⟩
      simp only [*, arm64_norm]
        at hcs2_19 hcs2_20 hcs2_21 hcs2_22 hcs2_23 hcs2_24 hcs2_25 hcs2_26 hcs2_27 hcs2_28 hcs2_29
      conv =>
        arg 4
        dsimp only [growOneChainZeroRegionPlacedSpec]
        simp only [*, arm64_norm, BitVec.sub_sub, BitVec.reduceAdd, sepExists_sepConj_left,
          sepConj_assoc]
      refine SepWPp.exists_elim fun chainBufPtr => ?_
      refine SepWPp.pure_left fun ⟨htr2, hne_buf⟩ => ?_
      conv =>
        arg 4
        simp only [memRegion_416_receiverChain_split chainBufPtr, cells, sepConj_emp,
          sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
          sepConj_assoc]
      repeat (refine SepWPp.exists_elim fun _ => ?_)
      apply SepWPp.of_sepWP_ret
      wp_steps
      have hpack_in := withReceiverChain_pack344_unfolded (s0.readReg64 (.gpr 0#5))
        chainBufPtr pre72 post248 ‹pre72.length = 72›
      have hlen_full : (pre72 ++ (receiverChainVecBytes24 chainBufPtr ++ post248)).length = 344 :=
        by
        simp [‹pre72.length = 72›, ‹post248.length = 248›]
      refine sepWP_focus (T :=
        (s0.readReg64 (.gpr 0#5) ↦ₛ pre72) ∗ ((s0.readReg64 (.gpr 0#5) + 0x48#64) ↦₆₄ 4#64) ∗
        ((s0.readReg64 (.gpr 0#5) + 0x50#64) ↦₆₄ chainBufPtr) ∗ ((s0.readReg64 (.gpr 0#5) +
        0x58#64) ↦₆₄ 1#64) ∗ ((s0.readReg64 (.gpr 0#5) + 0x60#64) ↦ₛ post248)) (by sep_focus) ?_
      rw [hpack_in, ← hlen_full]
      wp_call hmemcpy' (s0.readReg64 (.gpr 8#5), s0.readReg64 (.gpr 0#5), pre72 ++
        (receiverChainVecBytes24 chainBufPtr ++ post248))
      simp only [← withReceiverChain_pack344 _ _ _ _ ‹pre72.length = 72›]
      wp_steps
      unfold receiverChainElemAt receiverChainVecFieldsAt
      simp only [sepConj_assoc]
      wp_done

def ecPubKeySerializeRawPlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × Bytes) where
  pre := fun (keyPtr, keyBytes) s =>
    ⌜s.readReg64 .x0 = keyPtr ∧ keyBytes.length = 32⌝ ∗ (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗
      stackAt (s.sp - 32#64) allocHookStack ∗
    cells (s.sp - 32#64) 4 ∗ A.pool
  post := fun (keyPtr, keyBytes) s0 sf =>
    ∃∗ slicePtr : BitVec 64, ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = slicePtr ∧ sf.readReg64 .x1 =
      33#64 ∧ slicePtr ≠ 0⌝ ∗
      (keyPtr ↦ₛ bytesToBv8 keyBytes) ∗ (slicePtr ↦ₛ bytesToBv8 (encodeEC keyBytes)) ∗
        A.live slicePtr 33 1 ∗
      stackAt (s0.sp - 32#64) allocHookStack ∗ cells (s0.sp - 32#64) 4 ∗ A.pool
  onPanic := rustPanicOnOomPlaced

theorem ecPubKeySerializeRaw_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hpanic : H lsHandleErrorSym = some Rust.panicked) :
    subroutine_ok ((blkPC_205).rebase (blkPl_205).base H) (blkPl_205).base
      (ecPubKeySerializeRawPlacedSpec A) := by
  unfold ecPubKeySerializeRawPlacedSpec rustPanicOnOomPlaced
  simp only [bytesToBv8_encodeEC_raw]
  cells_unfold
  have hshim' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_205).rebase (blkPl_205).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hpanic' : ((blkPC_205).rebase (blkPl_205).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  wpp_init g s0
  obtain ⟨keyPtr, keyBytes⟩ := g
  dsimp only at *
  have hlen_bv : (bytesToBv8 keyBytes).length = 32 := by simp [bytesToBv8, h]
  obtain ⟨w0, w1, w2, w3, _, hpk_cells⟩ := exists_unpack64_of_length_32 hlen_bv
  rw [hpk_cells keyPtr]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  apply SepWPp.of_sepWP (mid := (blkPl_205).base + 32#64)
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm => ?_
    simpa only [sepConj_assoc] using
      allowPanic_panicked
        (allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm, htrace,
        ‹sf.trace = s0.trace›])) hm
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, memRegion_33_cells_raw, sepExists_sepConj_left,
      sepExists_sepConj_right, sepConj_assoc]
    refine SepWPp.exists_elim fun b0 => SepWPp.exists_elim fun u0 =>
      SepWPp.exists_elim fun u1 => SepWPp.exists_elim fun u2 =>
      SepWPp.exists_elim fun u3 => ?_
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    simp only [pointsToBytes_cons, hpk_cells, BitVec.add_assoc, BitVec.reduceAdd]
    wp_done

def setUnackPreKeyMsgPlacedSpec (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × Bytes) where
  pre := fun (statePtr, baseKeyPtr, baseKeyBytes) s =>
    ⌜s.readReg64 .x0 = statePtr ∧ s.readReg64 .x4 = baseKeyPtr ∧ baseKeyBytes.length = 32⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗ ((statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
    memRegion (statePtr + 0x100#64) 40 ∗ stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
    cells (s.sp - 144#64) 18 ∗
    A.pool
  post := fun (statePtr, baseKeyPtr, baseKeyBytes) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
    (baseKeyPtr ↦ₛ bytesToBv8 baseKeyBytes) ∗
    vecU8 A (statePtr + 0xf8#64) (bytesToBv8 (encodeEC baseKeyBytes)) ∗
    memRegion (statePtr + 0x110#64) 24 ∗
    stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
    cells (s0.sp - 144#64) 18 ∗
    A.pool
  onPanic := rustPanicOnOomPlaced

abbrev lsSystemTimeDurationSinceSym : String :=
  "_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since"

theorem setUnackPreKeyMsg_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hshim : HookSat H lsRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H lsRustAllocSym (rustAllocSpec A))
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hpanic : H lsHandleErrorSym = some Rust.panicked)
    (hTime : HookSat H lsSystemTimeDurationSinceSym (cryptoLeafStubSpec id 16 16)) :
    subroutine_ok ((blkPC_33).rebase (blkPl_33).base H) (blkPl_33).base
      (withLsCodeLoaded lsmpl (setUnackPreKeyMsgPlacedSpec A)) := by
  unfold withLsCodeLoaded setUnackPreKeyMsgPlacedSpec rustPanicOnOomPlaced
  wpp_init g s0
  obtain ⟨statePtr, baseKeyPtr, baseKeyBytes⟩ := g
  dsimp only at *
  have hser := ls_subroutine_ok_cl_of_plain (callerProg := (blkPC_33).rebase (blkPl_33).base H)
    (ecPubKeySerializeRaw_placed_ok hshim halloc hpanic)
  change subroutine_ok _ (lsmpl.base 205) (withLsCl lsmpl (ecPubKeySerializeRawPlacedSpec A)) at hser
  have hshim' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustNoAllocShimSym) noAllocShimSpec := ls_hook_ok_of_mem hshim
  have halloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustAllocSym) (rustAllocSpec A) := ls_hook_ok_of_mem halloc
  have hmemcpy' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec := ls_hook_ok_of_mem hmemcpy
  have htime' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsSystemTimeDurationSinceSym) (cryptoLeafStubSpec id 16 16) := ls_hook_ok_of_mem hTime
  have hdealloc' : subroutine_ok ((blkPC_33).rebase (blkPl_33).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc
  have hpanic' : ((blkPC_33).rebase (blkPl_33).base H).externAt? (lsρ lsHandleErrorSym) =
      some Rust.panicked := (ls_externAt?_of_mem (sym := lsHandleErrorSym)).trans hpanic
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  subst statePtr baseKeyPtr
  have hlen_enc : (bytesToBv8 (encodeEC baseKeyBytes)).length = 33 := by
    rw [bytesToBv8_encodeEC_raw]; simp [bytesToBv8, ‹baseKeyBytes.length = 32›]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk 33 1 := ⟨by decide, hpow2, by decide⟩
  rw [memRegion_40_unack_split (s0.readReg64 (.gpr 0#5))]
  cells_pre_unfold_fast
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 => SepWPp.exists_elim fun c2 => ?_
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  rw (occs := .pos [1]) [stackAt_setUnack_call s0.sp]
  rw [pointsTo64_split32' (s0.sp - 128#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  apply SepWPp.of_sepWP_lscl hcl0 (mid := lsmpl.base 205)
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hcl1
  refine SepWPp.call_frame_lscl (x := (s0.readReg64 (.gpr 4#5), baseKeyBytes)) hser hcl1
    (by wp_norm_lhs) (by wp_norm_lhs)
    (by simp only [State.spAligned, arm64_norm, hsp_align])
    (ret_pc := (blkPl_33).base + 64#64) (by wp_norm_lhs)
    (by dsimp only [ecPubKeySerializeRawPlacedSpec]; simp only [arm64_norm, BitVec.sub_sub,
      BitVec.reduceAdd]; rfl)
    ‹baseKeyBytes.length = 32›
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      dsimp only [ecPubKeySerializeRawPlacedSpec, rustPanicOnOomPlaced] at hm
      rw [← sepConj_assoc]
      exact allowPanic_frame (by simp only [allocFailedIn, arm64_norm]; exact id) hm)
    (fun sm hpcm hrunm hspm hcsm _hclm => ?_)
  simp only [arm64_norm] at hspm
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcsm
  rcases hcsm with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29⟩
  simp only [arm64_norm] at hcs19 hcs20 hcs21 hcs22 hcs23 hcs24 hcs25 hcs26 hcs27 hcs28 hcs29
  clear hpre
  dsimp only [ecPubKeySerializeRawPlacedSpec]
  simp only [arm64_norm, BitVec.sub_sub, BitVec.reduceAdd,
    sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun slicePtr => ?_
  refine SepWPp.pure_left fun ⟨htr_sm, hx0_sm, hx1_sm, hne_slice⟩ => ?_
  apply SepWPp.of_sepWP (mid := (blkPl_33).base + 116#64)
  apply SepWP.replace_pre (by sep_focus) (Entails.of_eq (stackAt_setUnack_hooks s0.sp))
  wp_steps
  wp_call hshim' ()
  wp_steps
  wp_call halloc' (33, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    simp only [hoom, ite_true]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ lsHandleErrorSym)
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic') fun hm =>
      ⟨allocFailedIn_of_eq (by simp only [Rust.panicked, arm64_norm]; rw [htrace,
        ‹sf.trace = sm.trace›, htr_sm]),
        Satisfies.mono (sepConj_mono_left (ent_anyHeap _)) hm⟩
  · have hoom64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    rw [← hlen_enc]
    wp_call hmemcpy' (sf_1.readReg64 (Reg.gpr 0#5), slicePtr, bytesToBv8 (encodeEC baseKeyBytes))
    wp_steps
    have h128_eq : s0.sp - 128#64 + 4#64 = s0.sp - 124#64 := by bv_arith
    have h136_eq : s0.sp - 136#64 + 8#64 = s0.sp - 128#64 := by bv_arith
    have h120_eq : s0.sp - 120#64 + 8#64 = s0.sp - 112#64 := by bv_arith
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq (h128_eq ▸ pointsTo32_pair (s0.sp - 128#64) _ _))
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq (h136_eq ▸ pointsTo64_pair_eq_twoWords (s0.sp - 136#64) _ _))
    apply SepWP.replace_pre (by sep_focus)
      (h120_eq ▸ pointsTo64_pair_entails_memRegion16 (s0.sp - 120#64) _ _)
    have hlen_tw := twoWordsToBytes_length (s0.readReg64 (.gpr 5#5))
      (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5)))
    wp_call htime' ⟨s0.sp - 136#64, twoWordsToBytes (s0.readReg64 (.gpr 5#5))
      (BitVec.extractLsb' 32 32 c2 ++ BitVec.truncate 32 (s0.readReg64 (.gpr 6#5))), s0.sp - 120#64⟩
    rw [fitBv8_16_twoWords, ← pointsTo64_pair_eq_twoWords (s0.sp - 136#64),
      ← pointsTo64_pair_eq_twoWords (s0.sp - 120#64), h136_eq, h120_eq]
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (pointsToBytes_entails_memRegion_33 slicePtr _ hlen_enc)
    wp_call hdealloc' (slicePtr, 33, 1)
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (unack_tail24_entails_memRegion (s0.readReg64 (.gpr 0#5)) _ _ _ _)
    simp only [*] at *
    apply SepWP.replace_pre (by sep_focus)
      (Entails.of_eq ((stackAt_setUnack_call s0.sp).trans (stackAt_setUnack_hooks s0.sp)).symm)
    dsimp only [vecU8]
    cells_unfold
    wp_done

end PlacedSessionStateCallees

end CryptoVerification.E2E.Pqxdh.Initiator
