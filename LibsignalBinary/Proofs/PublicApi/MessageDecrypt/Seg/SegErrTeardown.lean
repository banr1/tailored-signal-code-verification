/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegStoreAux
import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegWrite
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeErrorPush.Push
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import ProofLib.SepLogic.WP.Apply

/-!
# `MessageDecrypt` Error Teardown Segment (`SegErrTeardown`)

Verifies the error teardown path (`+0x2294 / +0x22a8 → +0x24d4`) of
`session_message_decrypt_signal_with_stores`: conditionally freeing the owned plaintext `Vec<u8>`
buffer (`pt = true`), dropping `Option<SessionStructure>` via `DropSessionStructureLocal2` and
freeing `previous_sessions`, and copying the 36 staged result bytes from `sp + 0x580` to
`sp + 0x300` before jumping to `ResultFinal`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoGames CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegSave CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegStore

/-! ## 1. Decode lemmas for `+0x2294..+0x2328` (`0x3c73c..0x3c7d0`) -/

namespace ErrTeardownBin
gen_decodes libsignalSessionCode_tree libsignalSessionBin [0x3c820 → 0x3c8b0]
end ErrTeardownBin

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 2. Stack Splits and Helpers -/

private theorem stack_ws_dropLocal2 (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) ∗
        stackAt sp FromRecordCallees.dropSessionStructureLocal2Stack := by
  have h := stackAt_split_bottom sp FromRecordCallees.dropSessionStructureLocal2Stack
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) (by decide)
  rwa [show FromRecordCallees.dropSessionStructureLocal2Stack +
    (wsCalleeStack - FromRecordCallees.dropSessionStructureLocal2Stack) = wsCalleeStack by decide] at h

private theorem stack_ws_alloc (sp : BitVec 64) :
    stackAt sp wsCalleeStack =
      memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack := by
  have h := stackAt_split_bottom sp allocHookStack (wsCalleeStack - allocHookStack) (by decide)
  rwa [show allocHookStack + (wsCalleeStack - allocHookStack) = wsCalleeStack by decide] at h

private theorem cap_add_one_beq_zero_eq_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 1#64 == 0#64) = false := by
  rw [beq_eq_false_iff_ne]; intro heq
  have ht := congrArg BitVec.toNat heq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
  change cap.toNat + 1 = 0 at ht; omega

private def vecGhostTailAt (A : RustAlloc) (g : VecGhost) (v : BitVec 64) : SepProp :=
  ((v + 8#64) ↦₆₄ g.ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 g.bytes.length) ∗
  (if g.cap = 0 then emp
   else A.live g.ptr g.cap.toNat 1 ∗ (g.ptr ↦ₛ g.bytes) ∗
     memRegion (g.ptr + BitVec.ofNat 64 g.bytes.length) (g.cap.toNat - g.bytes.length))

private theorem vecGhostAt_unfold_cap (A : RustAlloc) (g : VecGhost) (v : BitVec 64) :
    vecGhostAt A g v =
      ⌜g.bytes.length ≤ g.cap.toNat ∧ g.cap.toNat < 2 ^ 63 ∧ g.ptr ≠ 0⌝ ∗
      (v ↦₆₄ g.cap) ∗ vecGhostTailAt A g v := by
  simp only [vecGhostAt, vecU8At, vecHeader, vecGhostTailAt]; ac_rfl

private def sessionStateAfterLocalIk (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  ⌜PublicKey.deserialize G.localIk.bytes = Except.ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = Except.ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧ G.pending.isSome = st.pendingPreKey ∧
    G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)⌝ ∗
  vecGhostAt A G.remoteIk (ss + 24#64) ∗
  vecU8At A (ss + 48#64) G.root.cap G.root.ptr (CryptoGames.HMAC.keyToBytes32 st.rootKey) ∗
  vecAt A 104 8 (chainAt A) (ss + 72#64) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
  vecGhostAt A G.alice (ss + 96#64) ∗
  vecU8At A (ss + 120#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
  optSenderChainAt A (ss + 144#64) G.sender st.senderChain ∗
  optTailVecAt A 48 (ss + 248#64) G.pending ∗ optTailVecAt A 32 (ss + 296#64) G.kyber ∗
  ((ss + 328#64) ↦₃₂ st.sessionVersion) ∗ ((ss + 332#64) ↦₃₂ st.previousCounter) ∗
  ((ss + 336#64) ↦ₛ G.regIds)

private theorem sessionStateAt_unfold_cap (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A ss G st =
      ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧ G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0⌝ ∗
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostTailAt A G.localIk ss ∗
      sessionStateAfterLocalIk A ss G st := by
  unfold sessionStateAt sessionStateAfterLocalIk; rw [vecGhostAt_unfold_cap]; ac_rfl

private def dropSessionStructureLocal2HeadSpec (A : RustAlloc) : Spec FromRecordCallees.DropSessionStructureGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ x.G.localIk.bytes.length ≤ x.G.localIk.cap.toNat ∧
      x.G.localIk.cap.toNat < 2 ^ 63 ∧ x.G.localIk.ptr ≠ 0⌝ ∗
      (x.ss ↦₆₄ x.G.localIk.cap) ∗ vecGhostTailAt A x.G.localIk x.ss ∗
      sessionStateAfterLocalIk A x.ss x.G x.st ∗ A.pool ∗ stackAt s.sp FromRecordCallees.dropSessionStructureLocal2Stack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion x.ss 344 ∗ A.pool ∗ stackAt s0.sp FromRecordCallees.dropSessionStructureLocal2Stack

private theorem drop_session_structure_local2_head_ok {A : RustAlloc} {b : BitVec 64}
    {C : Crypto} {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hdrop2 : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal2Name)
      (dropSessionStructureLocal2HeadSpec A) := by
  refine subroutine_ok_mono hdrop2 (fun x R s0 hpre => ?_) (fun _ _ _ _ hpost => hpost)
  simp only [FromRecordCallees.dropSessionStructureLocal2Spec, dropSessionStructureLocal2HeadSpec,
    sessionStateAt_unfold_cap, sepConj_assoc, satisfies_pure_sepConj] at hpre ⊢
  exact ⟨hpre.1.1, hpre.1.2, hpre.2⟩

private theorem prevCap_ubfm_eq {cap : BitVec 64} (h : cap.toNat * 24 < 2 ^ 63) :
    ((cap + cap <<< 1) <<< 3).toNat = cap.toNat * 24 := by
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_shiftLeft]
  omega

private theorem noneCap_fold (a v : BitVec 64) :
    (a ↦₆₄ v) ∗ memRegion (a + 8#64) 336 ⊢ memRegion a 344 := by
  rw [memRegion_split a 8 336 (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a v)

/-- The current-session part of `droppableRecordAt` at `ss = r + 0x18`. -/
def curPre (A : RustAlloc) (ss : BitVec 64) :
    Option (SessionGhost × SessionState (List (BitVec 8))) → SepProp
  | none => (ss ↦₆₄ noneCap) ∗ memRegion (ss + 8#64) 336
  | some (G, st) => sessionStateAt A ss G st

/-! ## 3. TJ + TR tail (`+0x22a8 → +0x24d4`) -/

theorem teardown_tail_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) (hdrop2 : FromRecordCallees.DropSessionStructureLocal2Ok b C A ctl abs)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64}
    {cs : Option (SessionGhost × SessionState (List (BitVec 8)))}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x22a8#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 ≠ pendingTag) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x24d4#64) s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x300#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x308#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x310#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by simp only [decWithStoresName, arm64_norm]
  have hfn2 : libsignalSessionCode.fnOff FromRecordCallees.dropSessionStructureLocal2Name = 0x35a3c := by
    simp only [FromRecordCallees.dropSessionStructureLocal2Name, arm64_norm]
  have hdrop := drop_session_structure_local2_head_ok hdrop2
  have hrel : (tripleRatchetProgAt b C ctl abs).fnAddr FromRecordCallees.dropSessionStructureLocal2Name =
      (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 18446744073709532336#64 := by
    simp only [tripleRatchetProgAt, Program.fnAddr_rebase, hfn, hfn2, BitVec.add_assoc]; rfl
  rw [hrel] at hdrop; clear hrel
  have hdealloc := dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x3a58c)) hA
  have hx28n : s.readReg64 (Reg.gpr 28#5) ≠ pendingTag := hx28
  have hx28' : (s.readReg64 (Reg.gpr 28#5) + 3#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  have hx28b : (s.readReg64 (Reg.gpr 28#5) + 3#64 != 0#64) = true := by
    rw [bne_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownBin.libsignalSessionBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x22a8 0x1c
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownBin.libsignalSessionBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x22f0 0x38
  dsimp only [tripleRatchetProgAt] at hpc hdrop hdealloc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  rcases cs with _ | ⟨G, st⟩
  · have hnone : (noneCap + 1#64 == 0#64) = true := by decide
    simp only [curPre]
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hfold := noneCap_fold (s.sp + 0x138#64) noneCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
    apply SepWP.fold hfold (by sep_focus)
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply

      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done
  · simp only [curPre]
    wp_simp_pre [sessionStateAt_unfold_cap, sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
    have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hlik_cap
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp)) (by sep_focus)
    wp_steps
    wp_apply
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp).symm) (by sep_focus)
    wp_steps
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply
      simp only [hsp_sf] at hsp_sf_1 ⊢
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done

/-! ## 4. Memory exposure / repack lemmas -/

/-- `droppableRecordAt` exposes the `previous_sessions` header cells and buffer, and `curPre`. -/
theorem droppable_expose (A : RustAlloc) (r : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8)))) :
    droppableRecordAt A r cs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap.toNat * 24 < 2 ^ 63⌝ ∗
        ((r ↦₆₄ cap) ∗ ((r + 8#64) ↦₆₄ ptr) ∗ ((r + 16#64) ↦₆₄ 0#64) ∗
          (if cap = 0#64 then emp else A.live ptr (cap.toNat * 24) 8 ∗ memRegion ptr (cap.toNat * 24)) ∗
          curPre A (r + 0x18#64) cs) := by
  have hd : droppableRecordAt A r cs =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecAt A 24 8 (fun (_ : Unit) _ => emp) r cap ptr []) ∗
        curPre A (r + 0x18#64) cs := by
    cases cs with
    | none =>
      simp only [droppableRecordAt, curPre, BitVec.add_assoc, BitVec.reduceAdd]
    | some p => rcases p with ⟨G, st⟩; rfl
  rw [hd, sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecAt vecHeader vecBuf arrayAt
  simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    emp_sepConj, sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  exact Entails.pure_right hcap_lt (Entails.refl _)

/-- The pure part of `StagedRes` for the 5 words `w0..w4`. -/
def resOk (A : RustAlloc) (x28 w20 w21 : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32)
    (F : SepProp) : Prop :=
  ∀ r : BitVec 64,
    ((r ↦₆₄ x28) ∗ ((r + 8#64) ↦₃₂ resWord1 w20 w21) ∗
      ((r + 12#64) ↦ₛ (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4)) ∗ F) ⊢
      apiDecResultAt A r res

theorem stagedRes_expose (A : RustAlloc) (x28 w20 w21 src : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) :
    StagedRes A x28 w20 w21 src res ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
      ∃∗ F : SepProp,
        ⌜resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F⌝ ∗
        (((src ↦₆₄ w0) ∗ ((src + 8#64) ↦₆₄ w1) ∗ ((src + 16#64) ↦₆₄ w2) ∗
          ((src + 24#64) ↦₆₄ w3) ∗ ((src + 32#64) ↦₃₂ w4)) ∗ F) := by
  unfold StagedRes
  apply Entails.sepExists_elim; intro bs; apply Entails.sepExists_elim; intro F
  apply Entails.pure_left; rintro ⟨hlen, hres⟩
  obtain ⟨w0, w1, w2, w3, w4, rfl⟩ := SegWrite.exists_split_36 hlen
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right F ?_)))))
  refine Entails.pure_right hres ?_
  rw [SegWrite.pointsToBytes_36_eq]; exact Entails.refl _

theorem stagedRes_repack (A : RustAlloc) (x28 w20 w21 dst : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32)
    (F : SepProp) (h : resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F) :
    (((dst ↦₆₄ w0) ∗ ((dst + 8#64) ↦₆₄ w1) ∗ ((dst + 16#64) ↦₆₄ w2) ∗
      ((dst + 24#64) ↦₆₄ w3) ∗ ((dst + 32#64) ↦₃₂ w4)) ∗ F) ⊢
      StagedRes A x28 w20 w21 dst res := by
  unfold StagedRes
  refine Entails.sepExists_right (unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3 ++ unpack32 w4)
    (Entails.sepExists_right F (Entails.pure_right ⟨?_, h⟩ ?_))
  · simp only [List.length_append, unpack64_length, unpack32_length]
  · rw [SegWrite.pointsToBytes_36_eq]; exact Entails.refl _

/-- After TJ: the record zone `sp + 0x120 .. sp + 0x2c8` is free again. -/
theorem rec120_join (sp prevCap prevPtr : BitVec 64) :
    (((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
      memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ⊢
      memRegion (sp + 0x120#64) 0x1a8 := by
  rw [memRegion_split (sp + 0x120#64) 8 416 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64) 8 408 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64) 8 400 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64) 344 56 (by decide),
    memRegion_split (sp + 0x120#64 + 8#64 + 8#64 + 8#64 + 344#64) 24 32 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _)))

/-- A 24-byte `Vec` header's 3 cells free. -/
theorem header_fold (a c p l : BitVec 64) :
    ((a ↦₆₄ c) ∗ ((a + 8#64) ↦₆₄ p) ∗ ((a + 16#64) ↦₆₄ l)) ⊢ memRegion a 24 := by
  rw [memRegion_split a 8 16 (by decide), memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _) (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (pointsTo64_entails_memRegion _ _))

/-- The plaintext `Vec<u8>` at `a`: its header cells and the (whole) buffer as `memRegion`. -/
theorem vecU8_pt_expose (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap; apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr
    (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_))
  unfold vecU8At vecHeader
  simp only [sepConj_assoc]
  rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨hlen, hcap, _⟩
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono_right ?_))
  by_cases h0 : cap = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; exact Entails.refl _
  · rw [ite_eq_right h0, ite_eq_right h0]
    refine sepConj_mono_right ?_
    have hsplit := memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
    rw [show bs.length + (cap.toNat - bs.length) = cap.toNat by omega] at hsplit
    rw [hsplit]
    exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

/-! ## 5. ErrJoin `pt = false` → ResultFinal -/

def teardownPre (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (s0_580 s1_588 s2_590 s3_598 : BitVec 64) (s4_5a0 : BitVec 32)
    (t0_300 t1_308 t2_310 t3_318 : BitVec 64) (t4_320 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
  (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
  curPre A (sp + 0x138#64) cs ∗
  ((sp + 0x300#64) ↦₆₄ t0_300) ∗ ((sp + 0x308#64) ↦₆₄ t1_308) ∗ ((sp + 0x310#64) ↦₆₄ t2_310) ∗
  ((sp + 0x318#64) ↦₆₄ t3_318) ∗ ((sp + 0x320#64) ↦₃₂ t4_320) ∗
  ((sp + 0x580#64) ↦₆₄ s0_580) ∗ ((sp + 0x588#64) ↦₆₄ s1_588) ∗ ((sp + 0x590#64) ↦₆₄ s2_590) ∗
  ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
  A.pool ∗ stackAt sp wsCalleeStack

def teardownPost (A : RustAlloc) (sp prevCap prevPtr : BitVec 64)
    (s0_580 s1_588 s2_590 s3_598 : BitVec 64) (s4_5a0 : BitVec 32) : SepProp :=
  ((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
  ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
  ((sp + 0x300#64) ↦₆₄ s0_580) ∗ ((sp + 0x308#64) ↦₆₄ s1_588) ∗ ((sp + 0x310#64) ↦₆₄ s2_590) ∗
  ((sp + 0x318#64) ↦₆₄ s3_598) ∗ ((sp + 0x320#64) ↦₃₂ s4_5a0) ∗
  ((sp + 0x580#64) ↦₆₄ s0_580) ∗ ((sp + 0x588#64) ↦₆₄ s1_588) ∗ ((sp + 0x590#64) ↦₆₄ s2_590) ∗
  ((sp + 0x598#64) ↦₆₄ s3_598) ∗ ((sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
  A.pool ∗ stackAt sp wsCalleeStack

/-- The ErrJoin frame `teardown_tail_ok` does not touch (`F`: the staged result's owned resources). -/
def teardownFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (F : SepProp) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img) ∗
  wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗ F ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem ej_false_expose (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
    ∃∗ F : SepProp,
    ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64, ∃∗ t4 : BitVec 32,
      ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗ ⌜resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F⌝ ∗
      (teardownPre A sp prevCap prevPtr cs w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 ∗
        (teardownFrame C A ctl img kit ikit x ans s0 sp F ∗ R)) := by
  rw [memRegion_300_280_head_split]
  refine Entails.trans (Entails.of_eq (show _ =
    droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion (sp + 0x300#64) 0x24 ∗
      (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (droppable_expose A (sp + 0x120#64) cs)
    (sepConj_mono (stagedRes_expose A x28 w20 w21 (sp + 0x580#64) res)
      (sepConj_mono_left (memRegion_36_entails_cells (sp + 0x300#64))))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevCap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro F
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t0
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t1
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t4
  refine Entails.sepExists_right prevCap (Entails.sepExists_right prevPtr (Entails.sepExists_right w0
    (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right F (Entails.sepExists_right t0
        (Entails.sepExists_right t1 (Entails.sepExists_right t2 (Entails.sepExists_right t3
          (Entails.sepExists_right t4 ?_))))))))))))
  unfold teardownPre teardownFrame wsEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem teardown_post_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State)
    (sp prevCap prevPtr : BitVec 64) (x28 w20 w21 : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) (F R : SepProp)
    (hres : resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F) :
    teardownPost A sp prevCap prevPtr w0 w1 w2 w3 w4 ∗ (teardownFrame C A ctl img kit ikit x ans s0 sp F ∗ R) ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R := by
  have h120 := rec120_join sp prevCap prevPtr
  have h580 := cells_36_entails_memRegion (sp + 0x580#64) w0 w1 w2 w3 w4
  have hst := stagedRes_repack A x28 w20 w21 (sp + 0x300#64) res w0 w1 w2 w3 w4 F hres
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
      memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
    ((((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x308#64) ↦₆₄ w1) ∗ ((sp + 0x310#64) ↦₆₄ w2) ∗
      ((sp + 0x318#64) ↦₆₄ w3) ∗ ((sp + 0x320#64) ↦₃₂ w4)) ∗ F) ∗
    (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₃₂ w4)) ∗
    (wsFixedV kit ikit x s0 sp ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ logOff img ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by
    unfold teardownPost teardownFrame; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst (sepConj_mono_left h580))) ?_
  rw [memRegion_324_adc_split sp]
  unfold wsEnv
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segErrTeardownV_false {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hyps : DecHypsV img C A ctl uuidTryParse S encRecord abs kit ikit Scope)
    (hdrop2 : FromRecordCallees.DropSessionStructureLocal2Ok img.base C A ctl abs)
    {x : DecryptGhost} {R : SepProp} {s0 s : State}
    (hst : ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s) :
    DecSegV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hfr, _hsym, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x22a8#64 := by
    rw [hpc, ← entryOf_eq_tripleRatchetProgAt hyps.loads]
    try rfl
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtra kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
  have hm_pre := Satisfies.mono (ej_false_expose C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_ok (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFrame C A ctl img kit ikit x ans s0 s.sp F ∗ R')
      hyps.hooks.toTripleRatchetHooks.alloc hdrop2 hpc' hrun hsp_align hx28 hx26 hprev_lt
      (teardownFrame C A ctl img kit ikit x ans s0 s.sp F ∗ R') hm_pre hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  have hmeta2 := wsMeta_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails C A ctl img kit ikit x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres) hmf'
  refine ⟨sf, hsteps, Or.inl ⟨?_, hmeta2, ans, hpan, hscope, hcalls, hid_calls, ?_, ?_⟩⟩
  · rw [hpc2, ← entryOf_eq_tripleRatchetProgAt hyps.loads]
  · rw [htr2, htr]
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]; exact hm_fin

/-! ## 6. TJ pt (`+0x2294 → +0x22a8`): free the plaintext buffer -/

theorem teardown_pt_ok {A : RustAlloc} {b : BitVec 64} {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hA : AllocHooks A abs) {s : State} {R : SepProp} {cap ptr len : BitVec 64}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x2294#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAt b C ctl abs) ((tripleRatchetProgAt b C ctl abs).fnAddr decWithStoresName + 0x22a8#64) s
      (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x2a0#64) ↦₆₄ len) ∗ A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hfn : libsignalSessionCode.fnOff decWithStoresName = 0x3a58c := by simp only [decWithStoresName, arm64_norm]
  have hdealloc := dealloc_ok_at_norm (b := b) (C := C) (ctl := ctl)
    (name := decWithStoresName) (k := num% (ls_off% "__rustc::__rust_dealloc" - 0x3a58c)) hA
  code_fetches_range CryptoVerification.libsignalSessionCode ErrTeardownBin.libsignalSessionBin b (Rust.withPanics (tripleRatchetExterns C ctl abs)) hfn 0x3a58c 0x2294 0x14
  dsimp only [tripleRatchetProgAt] at hpc hdealloc ⊢
  generalize (libsignalSessionCode.rebase b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr decWithStoresName = entry at *
  examples_hide_fetches
  by_cases hcap : cap = 0
  · subst hcap; simp only [↓reduceIte, emp_sepConj]
    wp_steps; wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap, ↓reduceIte]
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
    wp_steps
    wp_apply
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
    wp_done

def ptPre (A : RustAlloc) (sp cap ptr len : BitVec 64) : SepProp :=
  ((sp + 0x290#64) ↦₆₄ cap) ∗ ((sp + 0x298#64) ↦₆₄ ptr) ∗ ((sp + 0x2a0#64) ↦₆₄ len) ∗
  (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
  A.pool ∗ stackAt sp wsCalleeStack

def ptPost (A : RustAlloc) (sp cap ptr len : BitVec 64) : SepProp :=
  ((sp + 0x290#64) ↦₆₄ cap) ∗ ((sp + 0x298#64) ↦₆₄ ptr) ∗ ((sp + 0x2a0#64) ↦₆₄ len) ∗
  A.pool ∗ stackAt sp wsCalleeStack

def ptFrame (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) : SepProp :=
  wsFixedV kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ logOff img) ∗
  wsMsgCells x sp ∗ droppableRecordAt A (sp + 0x120#64) cs ∗
  StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem ej_true_expose (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
      ptPre A sp cap ptr len ∗ (ptFrame C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      (wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
        droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  refine Entails.trans (sepConj_mono_left (vecU8_pt_expose A (sp + 0x290#64) p)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro len
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.sepExists_right len ?_))
  unfold ptPre ptFrame wsEnv
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem pt_post_entails (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp)
    (cap ptr len : BitVec 64) :
    ptPost A sp cap ptr len ∗ (ptFrame C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) ⊢
      wsFixedV kit ikit x s0 sp ∗ wsEnv A img x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R := by
  have hh := header_fold (sp + 0x290#64) cap ptr len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hh
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x290#64) ↦₆₄ cap) ∗ ((sp + 0x298#64) ↦₆₄ ptr) ∗ ((sp + 0x2a0#64) ↦₆₄ len)) ∗
      (A.pool ∗ stackAt sp wsCalleeStack ∗ ptFrame C A ctl img kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) by
    unfold ptPost; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hh) ?_
  unfold ptFrame wsEnv
  exact Entails.of_eq (by ac_rfl)

/-! ## 7. Segment Proof -/

attribute [local semireducible] SepWP in
theorem segErrTeardownV_ok_pf {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegErrTeardownSpecV img C A ctl uuidTryParse S encRecord abs kit ikit st0 ist0 Scope := by
  intro hyps hdrop2 x pt R s0 s hst
  cases pt with
  | false => exact segErrTeardownV_false hyps hdrop2 hst
  | true =>
    intro hL
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hfr, _hsym, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    have hpc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr decWithStoresName + 0x2294#64 := by
      rw [hpc, ← entryOf_eq_tripleRatchetProgAt hyps.loads]
      try rfl
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtra kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedV kit ikit x s0 s.sp ∗ wsEnv A img x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (s.sp + 0x290#64) p) ∗
        StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
    have hm_pre := Satisfies.mono (ej_true_expose C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_ok (cap := cap) (ptr := ptr) (len := len)
        (R := ptFrame C A ctl img kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.hooks.toTripleRatchetHooks.alloc hpc' hrun hsp_align
        (ptFrame C A ctl img kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    have hmeta1 := wsMeta_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails C A ctl img kit ikit x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1'
    have hst1 : ErrJoinStateV C ctl uuidTryParse S encRecord img kit ikit st0 ist0 Scope x false R s0 s1 := by
      refine ⟨?_, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, ?_, ?_⟩
      · rw [hpc1, ← entryOf_eq_tripleRatchetProgAt hyps.loads]
        try rfl
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rw [htr1, htr]
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownV_false hyps hdrop2 hst1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

theorem segErrTeardown_ok_pf {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} :
    SegErrTeardownSpec img C A ctl uuidTryParse S encRecord abs :=
  segErrTeardownV_ok_pf

/-! ## Relocatable `[LibsignalPlacement]` Proofs -/

section Placed

open CryptoVerification.LibsignalPublicApi.Placed

theorem teardown_tail_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
    {s : State} {R : SepProp} {prevCap prevPtr : BitVec 64}
    {cs : Option (SessionGhost × SessionState (List (BitVec 8)))}
    {s0_580 s1_588 s2_590 s3_598 : BitVec 64} {s4_5a0 : BitVec 32}
    {t0_300 t1_308 t2_310 t3_318 : BitVec 64} {t4_320 : BitVec 32}
    (hcrl : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = errJoinPCPlaced false)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx28 : s.readReg64 .x28 ≠ pendingTag) (hx26 : s.readReg64 .x26 = s.sp + 0xa0#64)
    (hprev_lt : prevCap.toNat * 24 < 2 ^ 63) :
    SepWP (lsProg_197 H) resultFinalPCPlaced s
      (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
        (if prevCap = 0#64 then emp else A.live prevPtr (prevCap.toNat * 24) 8 ∗ memRegion prevPtr (prevCap.toNat * 24)) ∗
        curPre A (s.sp + 0x138#64) cs ∗
        ((s.sp + 0x300#64) ↦₆₄ t0_300) ∗ ((s.sp + 0x308#64) ↦₆₄ t1_308) ∗ ((s.sp + 0x310#64) ↦₆₄ t2_310) ∗
        ((s.sp + 0x318#64) ↦₆₄ t3_318) ∗ ((s.sp + 0x320#64) ↦₃₂ t4_320) ∗
        ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
        ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x120#64) ↦₆₄ prevCap) ∗ ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗
          ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x138#64) 344 ∗
          ((s.sp + 0x300#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x308#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x310#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x318#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x320#64) ↦₃₂ s4_5a0) ∗
          ((s.sp + 0x580#64) ↦₆₄ s0_580) ∗ ((s.sp + 0x588#64) ↦₆₄ s1_588) ∗ ((s.sp + 0x590#64) ↦₆₄ s2_590) ∗
          ((s.sp + 0x598#64) ↦₆₄ s3_598) ∗ ((s.sp + 0x5a0#64) ↦₃₂ s4_5a0) ∗
          A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdrop := drop_session_structure_local2_head_placed_ok hdrop2
  have hdealloc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  have hx28n : s.readReg64 (Reg.gpr 28#5) ≠ pendingTag := hx28
  have hx28' : (s.readReg64 (Reg.gpr 28#5) + 3#64 == 0#64) = false := by
    rw [beq_eq_false_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  have hx28b : (s.readReg64 (Reg.gpr 28#5) + 3#64 != 0#64) = true := by
    rw [bne_iff_ne]; intro h; apply hx28n
    simp only [pendingTag]; bv_omega
  simp only [errJoinPCPlaced, Bool.false_eq_true, ↓reduceIte] at hpc
  unfold resultFinalPCPlaced
  dsimp only [lsProg_197] at hdrop ⊢
  rcases cs with _ | ⟨G, st⟩
  · clear hcrl hdrop
    have hnone : (noneCap + 1#64 == 0#64) = true := by decide
    simp only [curPre]
    wp_simp_pre [sepConj_assoc]
    wp_steps
    have hfold := noneCap_fold (s.sp + 0x138#64) noneCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
    apply SepWP.fold hfold (by sep_focus)
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done
  · simp only [curPre]
    wp_simp_pre [sessionStateAt_unfold_cap_shared_lb, sepConj_assoc, sepConj_pure_left_comm]
    apply SepWP.pure_elim; rintro ⟨hlik_len, hlik_cap, hlik_ptr⟩
    have hcmn : (G.localIk.cap + 1#64 == 0#64) = false := cap_add_one_beq_zero_eq_false hlik_cap
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp)) (by sep_focus)
    apply StoreKit.sepWP_seq_lscro (mid := lsmpl.base 139) hcrl
    clear hcrl
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    intro hcrl1
    have ⟨hcl1, hro1⟩ := hcrl1
    wp_apply
    clear hcrl1 hcl1 hro1
    apply SepWP.fold (Entails.of_eq (stack_ws_dropLocal2 s.sp).symm) (by sep_focus)
    wp_steps
    by_cases hcap : prevCap = 0#64
    · subst hcap; simp only [beq_self_eq_true, ↓reduceIte, emp_sepConj]; wp_steps; wp_done
    · have hcap_beq : (prevCap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
      simp only [hcap_beq, hcap, ↓reduceIte, Bool.false_eq_true]
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
      wp_steps
      have hmul := prevCap_ubfm_eq hprev_lt
      wp_apply
      simp only [hsp_sf] at hsp_sf_1 ⊢
      apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
      wp_steps; wp_done

def teardownFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (F : SepProp) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff) ∗
  wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗ F ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem ej_false_expose_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ prevCap : BitVec 64, ∃∗ prevPtr : BitVec 64,
    ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
    ∃∗ F : SepProp,
    ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64, ∃∗ t4 : BitVec 32,
      ⌜prevCap.toNat * 24 < 2 ^ 63⌝ ∗ ⌜resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F⌝ ∗
      (teardownPre A sp prevCap prevPtr cs w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 ∗
        (teardownFramePlaced C A ctl kit ikit x ans s0 sp F ∗ R)) := by
  rw [memRegion_300_280_head_split]
  refine Entails.trans (Entails.of_eq (show _ =
    droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion (sp + 0x300#64) 0x24 ∗
      (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗ memRegion (sp + 0x290#64) 24 ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono (droppable_expose A (sp + 0x120#64) cs)
    (sepConj_mono (stagedRes_expose A x28 w20 w21 (sp + 0x580#64) res)
      (sepConj_mono_left (memRegion_36_entails_cells (sp + 0x300#64))))) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevCap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro prevPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w0
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_left, sepExists_sepConj_right]; apply Entails.sepExists_elim; intro F
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t0
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t1
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t2
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t3
  rw [sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro t4
  refine Entails.sepExists_right prevCap (Entails.sepExists_right prevPtr (Entails.sepExists_right w0
    (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.sepExists_right w3
      (Entails.sepExists_right w4 (Entails.sepExists_right F (Entails.sepExists_right t0
        (Entails.sepExists_right t1 (Entails.sepExists_right t2 (Entails.sepExists_right t3
           (Entails.sepExists_right t4 ?_))))))))))))
  unfold teardownPre teardownFramePlaced wsEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem teardown_post_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State)
    (sp prevCap prevPtr : BitVec 64) (x28 w20 w21 : BitVec 64)
    (res : Except (ApiError AddrVal Unit) (List (BitVec 8)))
    (w0 w1 w2 w3 : BitVec 64) (w4 : BitVec 32) (F R : SepProp)
    (hres : resOk A x28 w20 w21 res w0 w1 w2 w3 w4 F) :
    teardownPost A sp prevCap prevPtr w0 w1 w2 w3 w4 ∗ (teardownFramePlaced C A ctl kit ikit x ans s0 sp F ∗ R) ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A x28 w20 w21 (sp + 0x300#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R := by
  have h120 := rec120_join sp prevCap prevPtr
  have h580 := cells_36_entails_memRegion (sp + 0x580#64) w0 w1 w2 w3 w4
  have hst := stagedRes_repack A x28 w20 w21 (sp + 0x300#64) res w0 w1 w2 w3 w4 F hres
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h580 hst
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x120#64) ↦₆₄ prevCap) ∗ ((sp + 0x128#64) ↦₆₄ prevPtr) ∗
      ((sp + 0x130#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x138#64) 344 ∗
      memRegion (sp + 0x290#64) 24 ∗ memRegion (sp + 0x2a8#64) 0x20) ∗
    ((((sp + 0x300#64) ↦₆₄ w0) ∗ ((sp + 0x308#64) ↦₆₄ w1) ∗ ((sp + 0x310#64) ↦₆₄ w2) ∗
      ((sp + 0x318#64) ↦₆₄ w3) ∗ ((sp + 0x320#64) ↦₃₂ w4)) ∗ F) ∗
    (((sp + 0x580#64) ↦₆₄ w0) ∗ ((sp + 0x588#64) ↦₆₄ w1) ∗ ((sp + 0x590#64) ↦₆₄ w2) ∗
      ((sp + 0x598#64) ↦₆₄ w3) ∗ ((sp + 0x5a0#64) ↦₃₂ w4)) ∗
    (wsFixedVPlaced kit ikit x s0 sp ∗
      (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ stackAt sp wsCalleeStack ∗ A.pool) ∗
      wsMsgCells x sp ∗ memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0x25c ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by
    unfold teardownPost teardownFramePlaced; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h120 (sepConj_mono hst (sepConj_mono_left h580))) ?_
  rw [memRegion_324_adc_split sp]
  unfold wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segErrTeardownVPlaced_false [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hyps : DecHypsVPlaced C A uuidTryParse S encRecord H kit ikit Scope)
    (hdrop2 : DropSessionStructureLocal2PlacedOk A H)
    {x : DecryptGhost} {R : SepProp} {s0 s : State}
    (hst : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s) :
    DecSegVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x R s0 s') := by
  intro hL
  rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, _hnok, hscope, hcalls, hid_calls, htr, hm⟩
  have hmeta0 := hmeta
  rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, hcrl, _hvregs⟩
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  rw [← hsp] at hx26 hm
  simp only [Bool.false_eq_true, ↓reduceIte] at hm
  let R' : SepProp :=
    decStoreExtraPlaced kit ikit
      (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
      (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
  have hm_r' : s.mem ⊨ wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
      droppableRecordAt A (s.sp + 0x120#64) cs ∗ memRegion (s.sp + 0x290#64) 24 ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
        (x.model C S uuidTryParse ans).1 ∗
      memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
      memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
  have hm_pre := Satisfies.mono (ej_false_expose_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
  simp only [satisfies_sepExists] at hm_pre
  rcases hm_pre with ⟨prevCap, prevPtr, w0, w1, w2, w3, w4, F, t0, t1, t2, t3, t4, hm_pre⟩
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hprev_lt, hm_pre⟩ := hm_pre
  rw [satisfies_pure_sepConj] at hm_pre
  obtain ⟨hres, hm_pre⟩ := hm_pre
  obtain ⟨sf, hsteps, ⟨hpc2, hrun2, P_f, hmf, hpost⟩ | ⟨_, _hoom⟩⟩ :=
    teardown_tail_placed_ok (cs := cs) (prevCap := prevCap) (prevPtr := prevPtr)
      (s0_580 := w0) (s1_588 := w1) (s2_590 := w2) (s3_598 := w3) (s4_5a0 := w4)
      (t0_300 := t0) (t1_308 := t1) (t2_310 := t2) (t3_318 := t3) (t4_320 := t4)
      (R := teardownFramePlaced C A ctl kit ikit x ans s0 s.sp F ∗ R')
      hyps.hooks.dealloc hdrop2 hcrl hpc hrun hsp_align hx28 hx26 hprev_lt
      (teardownFramePlaced C A ctl kit ikit x ans s0 s.sp F ∗ R') hm_pre hL
  rotate_left
  · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨hmf', hsp2, htr2, hx28_2, hx20_2, hx21_2, hx27_2, hx29_2, hvregs_2⟩ := hpost hmf
  have hmeta2 := wsMetaPlaced_of_steps hmeta hsteps hrun2 hsp2 hx29_2 hx27_2 hvregs_2
  have hm_fin := Satisfies.mono (teardown_post_entails_placed C A ctl kit ikit x ans s0 s.sp prevCap prevPtr
    (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (x.model C S uuidTryParse ans).1
    w0 w1 w2 w3 w4 F R' hres) hmf'
  refine ⟨sf, hsteps, Or.inl ⟨hpc2, hmeta2, ans, hpan, hscope, hcalls, hid_calls, ?_, ?_⟩⟩
  · rw [htr2, htr]
  · rw [hx28_2, hx20_2, hx21_2, ← hsp]; exact hm_fin

theorem teardown_pt_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (hdealloc_sat : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    {s : State} {R : SepProp} {cap ptr len : BitVec 64}
    (hpc : s.pc = errJoinPCPlaced true)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (lsProg_197 H) (errJoinPCPlaced false) s
      (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗ ((s.sp + 0x2a0#64) ↦₆₄ len) ∗
        (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp wsCalleeStack)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (((s.sp + 0x290#64) ↦₆₄ cap) ∗ ((s.sp + 0x298#64) ↦₆₄ ptr) ∗
          ((s.sp + 0x2a0#64) ↦₆₄ len) ∗ A.pool ∗ stackAt s.sp wsCalleeStack) ∗ R) ∧
        sf.sp = s.sp ∧ sf.trace = s.trace ∧ sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧ sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧ sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s) := by
  have hdealloc : subroutine_ok ((blkPC_197).rebase (blkPl_197).base H) (lsρ lsRustDeallocSym)
      (rustDeallocSpec A) := ls_hook_ok_of_mem hdealloc_sat
  simp only [errJoinPCPlaced, ↓reduceIte] at hpc
  simp only [errJoinPCPlaced, Bool.false_eq_true, ↓reduceIte]
  dsimp only [lsProg_197]
  by_cases hcap : cap = 0
  · subst hcap; simp only [↓reduceIte, emp_sepConj]
    wp_steps; wp_done
  · have hcap_beq : (cap == 0#64) = false := beq_eq_false_iff_ne.mpr hcap
    simp only [hcap, ↓reduceIte]
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp)) (by sep_focus)
    wp_steps
    wp_apply
    apply SepWP.fold (Entails.of_eq (stack_ws_alloc s.sp).symm) (by sep_focus)
    wp_done

def ptFramePlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) : SepProp :=
  wsFixedVPlaced kit ikit x s0 sp ∗
  (signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff) ∗
  wsMsgCells x sp ∗ droppableRecordAt A (sp + 0x120#64) cs ∗
  StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
  memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
  memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
  memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans)

theorem ej_true_expose_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp) :
    (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) ⊢
    ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, ∃∗ len : BitVec 64,
      ptPre A sp cap ptr len ∗ (ptFramePlaced C A ctl kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) := by
  refine Entails.trans (Entails.of_eq (show _ =
    (∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p) ∗
      (wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
        droppableRecordAt A (sp + 0x120#64) cs ∗ StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
        memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
        memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R) by ac_rfl)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro p
  refine Entails.trans (sepConj_mono_left (vecU8_pt_expose A (sp + 0x290#64) p)) ?_
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro cap
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro ptr
  rw [sepExists_sepConj_left]; apply Entails.sepExists_elim; intro len
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.sepExists_right len ?_))
  unfold ptPre ptFramePlaced wsEnvPlaced
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

theorem pt_post_entails_placed [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (s0 : State) (sp : BitVec 64)
    (cs : Option (SessionGhost × SessionState (List (BitVec 8))))
    (x28 w20 w21 : BitVec 64) (res : Except (ApiError AddrVal Unit) (List (BitVec 8))) (R : SepProp)
    (cap ptr len : BitVec 64) :
    ptPost A sp cap ptr len ∗ (ptFramePlaced C A ctl kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) ⊢
      wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗ memRegion (sp + 0x290#64) 24 ∗
      StagedRes A x28 w20 w21 (sp + 0x580#64) res ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R := by
  have hh := header_fold (sp + 0x290#64) cap ptr len
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hh
  refine Entails.trans (Entails.of_eq (show _ =
    (((sp + 0x290#64) ↦₆₄ cap) ∗ ((sp + 0x298#64) ↦₆₄ ptr) ∗ ((sp + 0x2a0#64) ↦₆₄ len)) ∗
      (A.pool ∗ stackAt sp wsCalleeStack ∗ ptFramePlaced C A ctl kit ikit x ans s0 sp cs x28 w20 w21 res ∗ R) by
    unfold ptPost; ac_rfl)) ?_
  refine Entails.trans (sepConj_mono_left hh) ?_
  unfold ptFramePlaced wsEnvPlaced
  exact Entails.of_eq (by ac_rfl)

attribute [local semireducible] SepWP in
theorem segErrTeardownVPlaced_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} :
    SegErrTeardownSpecVPlaced C A ctl uuidTryParse S encRecord H kit ikit st0 ist0 Scope := by
  intro hyps hdrop2 x pt R s0 s hst
  cases pt with
  | false => exact segErrTeardownVPlaced_false hyps hdrop2 hst
  | true =>
    intro hL
    rcases hst with ⟨hpc, hmeta, hx26, hx28, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, htr, hm⟩
    have hmeta0 := hmeta
    rcases hmeta0 with ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, _hx27, _hcrl, _hvregs⟩
    have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
    rw [← hsp] at hx26 hm
    simp only [↓reduceIte] at hm
    let R' : SepProp :=
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2)
        (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) s0 ∗ R
    have hm_r' : s.mem ⊨ wsFixedVPlaced kit ikit x s0 s.sp ∗ wsEnvPlaced A x s.sp ∗ wsMsgCells x s.sp ∗
        droppableRecordAt A (s.sp + 0x120#64) cs ∗ (∃∗ p : List (BitVec 8), vecU8 A (s.sp + 0x290#64) p) ∗
        StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (s.sp + 0x580#64)
          (x.model C S uuidTryParse ans).1 ∗
        memRegion s.sp 0xa0 ∗ memRegion (s.sp + 0x2a8#64) 0x20 ∗ memRegion (s.sp + 0x2d0#64) 0x10 ∗
        memRegion (s.sp + 0x300#64) 0x280 ∗ memRegion (s.sp + 0x5a4#64) 0x85c ∗
        memRegion x.ret 48 ∗ tapeAfter ctl x.cur x.rest (x.draws C ans) ∗ R' := hm
    have hm_pre := Satisfies.mono (ej_true_expose_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R') hm_r'
    simp only [satisfies_sepExists] at hm_pre
    rcases hm_pre with ⟨cap, ptr, len, hm_pre⟩
    obtain ⟨s1, hsteps1, ⟨hpc1, hrun1, P_f, hm1, hpost1⟩ | ⟨_, _hoom⟩⟩ :=
      teardown_pt_placed_ok (cap := cap) (ptr := ptr) (len := len)
        (R := ptFramePlaced C A ctl kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R')
        hyps.hooks.dealloc hpc hrun hsp_align
        (ptFramePlaced C A ctl kit ikit x ans s0 s.sp cs (s.readReg64 .x28) (s.readReg64 .x20)
          (s.readReg64 .x21) (x.model C S uuidTryParse ans).1 ∗ R') hm_pre hL
    rotate_left
    · dsimp only at _hoom; exact (not_satisfies_false_sepConj _hoom).elim
    obtain ⟨hm1', hsp1, htr1, hx28_1, hx20_1, hx21_1, hx26_1, hx27_1, hx29_1, hvregs_1⟩ := hpost1 hm1
    have hmeta1 := wsMetaPlaced_of_steps hmeta hsteps1 hrun1 hsp1 hx29_1 hx27_1 hvregs_1
    have hm1_f := Satisfies.mono
      (pt_post_entails_placed C A ctl kit ikit x ans s0 s.sp cs _ _ _ _ R' cap ptr len) hm1'
    have hst1 : ErrJoinStateVPlaced C ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope x false R s0 s1 := by
      refine ⟨hpc1, hmeta1, ?_, ?_, ans, cs, hpan, hnok, hscope, hcalls, hid_calls, ?_, ?_⟩
      · rw [hx26_1, hx26, hsp]
      · rw [hx28_1]; exact hx28
      · rw [htr1, htr]
      · rw [hx28_1, hx20_1, hx21_1, ← hsp]
        simpa only [Bool.false_eq_true, ↓reduceIte] using hm1_f
    obtain ⟨s2, hsteps2, hout⟩ := segErrTeardownVPlaced_false hyps hdrop2 hst1 (hsteps1.codeLoaded hL)
    exact ⟨s2, hsteps1.trans hsteps2, hout⟩

end Placed

end CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegErrTeardown
