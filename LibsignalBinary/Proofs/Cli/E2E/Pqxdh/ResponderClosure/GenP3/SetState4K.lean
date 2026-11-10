/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.AllocContractsMem4K
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropLocal1Ext4K
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Common
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# 4K-Stack `SessionRecord::set_session_state` on `tripleRatchetProgAtExt`

Verifies `<SessionRecord>::set_session_state` (15 instructions) against `setSessionStateSpec A`
(`SetSessionStateOkExt b A ext`) on `tripleRatchetProgAtExt b ext` under
`AllocContractsMem4K b A ext` (`setSessionStateStack = 4256 = 160 + 4096`).
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees.DropsCommon
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local wp_norm] sessionMemcpySpec libcMemcpySpec

private theorem stackAt_setSessionState_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
  have h1 := ProofLib.stackAt_split_cells sp dropSessionStructureLocal1Stack 4 (by decide)
  change stackAt sp setSessionStateStack =
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗ cells (sp - 32#64) 4 at h1
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
        ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [h1, hc4]
  simp only [sepExists_sepConj_right]

private theorem stackAt_setSessionState_split_alloc_4k (sp : BitVec 64) :
    stackAt sp setSessionStateStack =
      memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [show setSessionStateStack = allocHookStack + 160 from rfl,
      stackAt_split_bottom' sp allocHookStack 160 (by decide)]

private theorem cells4_local1_entails_setSessionState_split_4k (sp v0 v1 v2 v3 : BitVec 64) :
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
      ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
      ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
    memRegion (sp - 4256#64) 160 ∗ stackAt sp allocHookStack := by
  rw [← stackAt_setSessionState_split_alloc_4k sp, stackAt_setSessionState_4k sp]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem pointsTo64_memRegion_336_eq_344_4k (r : BitVec 64) :
    (∃∗ v : BitVec 64, ((r + 24#64) ↦₆₄ v)) ∗ memRegion (r + 32#64) 336 =
      memRegion (r + 24#64) 344 := by
  have h := memRegion_split (r + 24#64) 8 336 (by decide)
  have hadd : r + 24#64 + 8#64 = r + 32#64 := by
    rw [BitVec.add_assoc]; rfl
  rw [show (8 + 336 : Nat) = 344 by rfl, hadd, ProofLib.memRegion_eight] at h
  exact h.symm

private theorem pointsTo64_memRegion_336_entails_344_4k (r v : BitVec 64) :
    ((r + 24#64) ↦₆₄ v) ∗ memRegion (r + 32#64) 336 ⊢ memRegion (r + 24#64) 344 := by
  rw [← pointsTo64_memRegion_336_eq_344_4k r]
  exact sepConj_mono_left (Entails.sepExists_intro v)

private theorem cap_add_one_beq_zero_eq_false_4k {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht
  omega

private def vecGhostTailAt4K (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap_4k (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt4K A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt4K]
  ac_rfl

private def sessionStateAfterLocalIk4K (A : RustAlloc) (ss : BitVec 64)
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

private theorem sessionStateAt_unfold_cap_4k (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt4K A G.localIk ss ∗
      sessionStateAfterLocalIk4K A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk4K
  rw [vecGhostAt_unfold_cap_4k]
  ac_rfl

private def dropSessionStructureLocal1HeadSpec4K (A : RustAlloc) : Spec DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧
      x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧
      x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt4K A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk4K A x.ss x.G x.st ∗
      A.pool ∗ stackAt s.sp dropSessionStructureLocal1Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp dropSessionStructureLocal1Stack

private theorem drop_session_structure_local1_head_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr dropSessionStructureLocal1Name)
      (dropSessionStructureLocal1HeadSpec4K A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  refine hdrop1.mono_outcome x R s0 hpc hrun ?_ hsp fun _ hout => hout
  simp only [dropSessionStructureLocal1Spec, dropSessionStructureLocal1HeadSpec4K,
    sessionStateAt_unfold_cap_4k, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

/-! ## Case 1: `cur = none` -/

private def setSessionStateNoneSpec4K (A : RustAlloc) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (record, src, bs) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      ((record + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (record + 0x20#64) 336 ∗
      (src ↦ₛ bs) ∗ A.pool ∗ stackAt s.sp setSessionStateStack
  post := fun (record, src, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool ∗
      stackAt s0.sp setSessionStateStack

private theorem set_session_state_none_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateNoneSpec4K A) := by
  unfold setSessionStateNoneSpec4K
  simp only [noneCap]
  have hfn : libsignalSessionCode.fnOff setSessionStateName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      (sessionMemcpySpec allocHookStack) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hmemcpy0 setSessionStateName
      (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
      (by fnoff_eq)
  clear hmemcpy0
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0 12
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin b
    (Rust.withPanics ext) hfn (num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")) 0x34 8
  wp_init x s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨record, src, bs⟩ := x
  dsimp only at *
  rw [stackAt_setSessionState_split_alloc_4k s0.sp]
  wp_steps
  refine SepWP.fold (pointsTo64_memRegion_336_entails_344_4k record 0xffffffffffffffff#64)
    (by sep_focus) ?_
  rw [← h]
  wp_apply
  rw [← stackAt_setSessionState_split_alloc_4k s0.sp]
  wp_done

/-! ## Case 2: `cur = some (G, st)` -/

private def setSessionStateSomeStack4K (sp : BitVec 64) : SepProp :=
  ∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
    stackAt (sp - 32#64) dropSessionStructureLocal1Stack ∗
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3)

private def setSessionStateSomeSpec4K (A : RustAlloc) :
    Spec (BitVec 64 × BitVec 64 × SessionGhost × SessionState (List (BitVec 8)) × List (BitVec 8)) where
  pre := fun (record, src, G, st, bs) s =>
    ⌜s.readReg64 .x0 = record ∧ s.readReg64 .x1 = src ∧ bs.length = 344⌝ ∗
      sessionStateAt A (record + 0x18#64) G st ∗
      (src ↦ₛ bs) ∗ A.pool ∗ setSessionStateSomeStack4K s.sp
  post := fun (record, src, _G, _st, bs) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ((record + 0x18#64) ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool ∗
      stackAt s0.sp setSessionStateStack

private theorem set_session_state_some_ok_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName)
      (setSessionStateSomeSpec4K A) := by
  unfold setSessionStateSomeSpec4K
  simp only [sessionStateAt_unfold_cap_4k, setSessionStateSomeStack4K, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff setSessionStateName = num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::set_session_state")
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr setSessionStateName + BitVec.ofNat 64 (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state")))
      (sessionMemcpySpec allocHookStack) :=
    sub_ok_at_of_fnAddr (b := b) (ext := ext) (sym := memcpyName) hmemcpy0 setSessionStateName
      (num% (ls_off% "memcpy" - ls_off% "<libsignal_protocol::state::session::SessionRecord>::set_session_state"))
      (by fnoff_eq)
  clear hmemcpy0
  have hdrop := drop_session_structure_local1_head_ok_4k hdrop1
  clear hdrop1
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
  have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false_4k (by omega)
  wp_steps
  wp_apply
  wp_steps
  refine SepWP.fold (cells4_local1_entails_setSessionState_split_4k s0.sp _ _ _ _)
    (by sep_focus) ?_
  rw [← h_2]
  wp_apply
  refine SepWP.fold (Entails.of_eq (stackAt_setSessionState_split_alloc_4k s0.sp).symm)
    (by sep_focus) ?_
  wp_done

/-! ## Unified `set_session_state_ok_ext_4k` -/

theorem set_session_state_ok_of_memcpy_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hmemcpy0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr memcpyName) (sessionMemcpySpec allocHookStack))
    (hdrop1 : DropSessionStructureLocal1OkExt b A ext) :
    SetSessionStateOkExt b A ext := by
  refine subroutine_ok_outcome_intro fun ⟨record, src, cur, bs⟩ R s0 hpc hrun hpre hsp => ?_
  rcases cur with _ | ⟨G, st⟩
  · exact (set_session_state_none_ok_4k hmemcpy0).mono_outcome (record, src, bs) R s0 hpc hrun
      (by simpa only [setSessionStateSpec, setSessionStateNoneSpec4K, sepConj_assoc] using hpre) hsp
      fun _ hout => hout
  · exact (set_session_state_some_ok_4k hmemcpy0 hdrop1).mono_outcome (record, src, G, st, bs) R s0 hpc hrun
      (by simpa only [setSessionStateSpec, setSessionStateSomeSpec4K,
        stackAt_setSessionState_4k, setSessionStateSomeStack4K, sepConj_assoc] using hpre) hsp
      fun _ hout => hout

/-- `<SessionRecord>::set_session_state` meets `setSessionStateSpec A` (`SetSessionStateOkExt b A ext`)
on `tripleRatchetProgAtExt b ext` under `AllocContractsMem4K b A ext`. -/
theorem set_session_state_ok_ext_4k {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContractsMem4K b A ext) :
    SetSessionStateOkExt b A ext :=
  set_session_state_ok_of_memcpy_4k hA.session_memcpy (drop_session_structure_local1_ok_ext_4k hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
