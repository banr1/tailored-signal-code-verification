/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.AllocCodeSym
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.Hooks
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Verification of `SessionRecord::set_session_state` (`0x174d4`, Block `48`)

Proves fixed-image (`set_session_state_ok`) and relocatable `[LibsignalPlacement]`
(`set_session_state_placed_ok`) contracts for `<SessionRecord>::set_session_state`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_setSessionState (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := stackAt_split_cells sp dropSessionStructureLocal1Stack 4 (by decide)
  change stackAt sp setSessionStateStack =
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]
  simp only [sepExists_sepConj_right]

private theorem pointsTo64_memRegion_336_eq_344 (r : BitVec 64) :
    (∃∗ v : BitVec 64, ((r + 24#64) ↦₆₄ v)) ∗ memRegion (r + 32#64) 336 =
      memRegion (r + 24#64) 344 := by
  have h := memRegion_split (r + 24#64) 8 336 (by decide)
  have hadd : r + 24#64 + 8#64 = r + 32#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (8 + 336 : Nat) = 344 by rfl, hadd, memRegion_eight] at h
  exact h.symm

private theorem pointsTo64_memRegion_336_entails_344 (r v : BitVec 64) :
    ((r + 24#64) ↦₆₄ v) ∗ memRegion (r + 32#64) 336 ⊢ memRegion (r + 24#64) 344 := by
  rw [← pointsTo64_memRegion_336_eq_344 r]
  exact sepConj_mono_left (Entails.sepExists_intro v)

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

private def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]
  ac_rfl

private def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗
  optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗
  ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt A G.localIk ss ∗
      sessionStateAfterLocalIk A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk
  rw [vecGhostAt_unfold_cap]
  ac_rfl

private def dropSessionStructureLocal1HeadSpec (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧
      x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk A x.ss x.G x.st ∗
      A.pool ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal1Stack

private theorem drop_session_structure_local1_head_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1HeadSpec A) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine hdrop1.mono_outcome x R s0 hpc hrun ?_ hsp fun _ h => h
  simp only [dropSessionStructureLocal1Spec, dropSessionStructureLocal1HeadSpec,
    sessionStateAt_unfold_cap, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

/-! ## Case 1: `cur = none` -/

set_option quotPrecheck false in
local notation "setSessionStateNoneSpec" =>
  (fun (A : RustAlloc) =>
    ({ pre := fun (record, src, bs) s =>
         ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
           ((record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (record + 0x20#64) 336 ∗
           (src ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack
       post := fun (record, src, bs) s0 sf =>
         ⌜sf.trace = s0.trace⌝ ∗
           ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool ∗
           stackAt s0.sp setSessionStateStack } :
      Spec (BitVec 64 × BitVec 64 × List (BitVec 8))))

private theorem set_session_state_none_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateNoneSpec A) := by
  simp only [noneCap]
  have hfn : libsignalSessionCode.fnOff setSessionStateName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      framelessMemcpySpec :=
    sub_ok_at_of_fnAddr hmemcpy0 setSessionStateName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0x34 8
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨record, src, bs⟩ := x
  dsimp only at *
  wp_steps
  refine SepWP.fold (pointsTo64_memRegion_336_entails_344 record 0xffffffffffffffff#64)
    (by sep_focus) ?_
  rw [← h]
  wp_apply
  wp_done

/-! ## Case 2: `cur = some (G, st)` -/

set_option quotPrecheck false in
local notation "setSessionStateSomeSpec" =>
  (fun (A : RustAlloc) =>
    ({ pre := fun (record, src, G, st, bs) s =>
         ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
           sessionStateAt A (record + 0x18#64) G st ∗
           (src ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack
       post := fun (record, src, _G, _st, bs) s0 sf =>
         ⌜sf.trace = s0.trace⌝ ∗
           ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool ∗
           stackAt s0.sp setSessionStateStack } :
      Spec (BitVec 64 × BitVec 64 × SessionGhost × SessionState (List (BitVec 8)) × List (BitVec 8))))

private theorem set_session_state_some_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSomeSpec A) := by
  simp only [sessionStateAt_unfold_cap, stackAt_setSessionState, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff setSessionStateName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      framelessMemcpySpec :=
    sub_ok_at_of_fnAddr hmemcpy0 setSessionStateName (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
  have hdrop := drop_session_structure_local1_head_ok hdrop1
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name =
      (tripleRatchetProgAtExt b ext).fnAddr setSessionStateName + bv% (2 ^ 64 + (ls_off% "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]") - (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, (ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::proto::storage::SessionStructure> [local#1]"),
      (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state"), BitVec.add_assoc]
    rfl
  rw [hrel] at hdrop
  clear hrel
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0 60
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨record, src, G, st, bs⟩ := x
  dsimp only at *
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false (by omega)
  wp_steps
  wp_apply
  wp_steps
  rw [← h_2]
  wp_apply
  wp_done

/-! ## Unified `set_session_state_ok` -/

private theorem set_session_state_ok_of_memcpy {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) sessionMemcpyRegionSpec)
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    SetSessionStateOkExt b A ext := by
  apply subroutine_ok_outcome_intro
  intro ⟨record, src, cur, bs⟩ R s0 hpc hrun hpre hsp
  rcases cur with _ | ⟨G, st⟩
  · exact (set_session_state_none_ok hmemcpy0).mono_outcome (record, src, bs) R s0 hpc hrun
      (by simpa only [setSessionStateSpec, sepConj_assoc] using hpre) hsp fun _ h => h
  · exact (set_session_state_some_ok hmemcpy0 hdrop1).mono_outcome (record, src, G, st, bs) R s0 hpc hrun
      (by simpa only [setSessionStateSpec, sepConj_assoc] using hpre) hsp fun _ h => h

theorem set_session_state_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    SetSessionStateOkExt b A ext :=
  set_session_state_ok_of_memcpy hA.session_memcpy_region hdrop1

theorem set_session_state_ok_trap {A : RustAlloc} {b : BitVec 64}
    {C : Crypto}
    {abs : String → Option (State → State)}
    (hdrop1 : DropSessionStructureLocal1Ok_trap b C A abs) :
    SetSessionStateOk_trap b C A abs := by
  have hmemcpy0 : subroutine_ok (trTrapProgAt b C abs)
      ((trTrapProgAt b C abs).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memcpy_region_ok_at_trap
        b C abs memcpyName 0 (Nat.add_zero _)
  exact set_session_state_ok_of_memcpy hmemcpy0 hdrop1

/-- `<SessionRecord>::set_session_state` (`0x174d4`, 15 insns) meets
`setSessionStateSpec A` on `tripleRatchetProgAt`. -/
theorem set_session_state_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hdrop1 : DropSessionStructureLocal1Ok b C A ctl abs) :
    SetSessionStateOk b C A ctl abs := by
  have hmemcpy0 : subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr memcpyName) sessionMemcpyRegionSpec := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      CryptoVerification.LibsignalTripleRatchet.session_memcpy_region_ok_at
        b C ctl abs memcpyName 0 (Nat.add_zero _)
  exact set_session_state_ok_of_memcpy hmemcpy0 hdrop1

/-! ## Relocatable `[LibsignalPlacement]` Contracts (Block `48`) -/

private theorem drop_session_structure_local1_placed_head_ok [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (hdrop1 : subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec A))) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (dropSessionStructureLocal1HeadSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  refine hdrop1.mono_outcome x R s0 hpc hrun ?_ hsp fun _ h => h
  simp only [dropSessionStructureLocal1Spec, dropSessionStructureLocal1HeadSpec,
    sessionStateAt_unfold_cap, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

theorem set_session_state_none_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (setSessionStateNoneSpec A) := by
  simp only [noneCap]
  wp_init x s0
  obtain ⟨record, src, bs⟩ := x
  dsimp only at *
  wp_steps
  refine SepWP.fold (pointsTo64_memRegion_336_entails_344 record 0xffffffffffffffff#64)
    (by sep_focus) ?_
  rw [← h]
  wp_apply
  wp_done

theorem set_session_state_some_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) framelessMemcpySpec)
    (hdrop1 : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsmpl.base 6) (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec A))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSomeSpec A)) := by
  simp only [withLsCodeLoaded, sessionStateAt_unfold_cap,
    stackAt_setSessionState, sepExists_sepConj_right]
  have hdrop := drop_session_structure_local1_placed_head_ok hdrop1
  wp_init x s0
  obtain ⟨record, src, G, st, bs⟩ := x
  dsimp only at *
  have hcl0 : LibsignalCodeLoaded lsmpl s0.mem := by assumption
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false (by omega)
  wp_steps_lscl ((blkPl_48).base + 32#64)
  wp_apply
  wp_steps
  rw [← h_3]
  wp_apply
  wp_done

theorem set_session_state_placed_ok_of_memcpy [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmemcpy : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsρ lsMemcpySym) sessionMemcpyRegionSpec)
    (hdrop1 : subroutine_ok ((blkPC_48).rebase (blkPl_48).base H)
      (lsmpl.base 6) (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec A))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSpec A)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨record, src, cur, bs⟩ R s0 hpc hrun hpre hsp
  rcases cur with _ | ⟨G, st⟩
  · have hnone := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
      (set_session_state_none_placed_ok (A := A) hmemcpy)
    exact hnone.mono_outcome (record, src, bs) R s0 hpc hrun
      (by simpa only [withLsCodeLoaded, setSessionStateSpec, sepConj_assoc] using hpre)
      hsp fun _ h => h
  · exact (set_session_state_some_placed_ok hmemcpy hdrop1).mono_outcome (record, src, G, st, bs) R s0 hpc hrun
      (by simpa only [withLsCodeLoaded, setSessionStateSpec, sepConj_assoc] using hpre)
      hsp fun _ h => h

/-- Block `48`: `<SessionRecord>::set_session_state` meets `setSessionStateSpec A`
under `[LibsignalPlacement]`. -/
theorem set_session_state_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)}
    (hmemcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec)
    (hdrop1 : subroutine_ok ((blkPC_6).rebase (blkPl_6).base H)
      (blkPl_6).base (withLsCodeLoaded lsmpl (dropSessionStructureLocal1Spec A))) :
    subroutine_ok ((blkPC_48).rebase (blkPl_48).base H) (blkPl_48).base
      (withLsCodeLoaded lsmpl (setSessionStateSpec A)) :=
  set_session_state_placed_ok_of_memcpy
    (ls_hook_ok_of_mem hmemcpy)
    (ls_subroutine_ok_of_block hdrop1)

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
