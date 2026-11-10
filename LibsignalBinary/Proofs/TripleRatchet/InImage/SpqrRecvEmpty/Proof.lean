/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImage.SpqrRecvEmpty.Varint
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.TripleRatchet.InImage.DecodeStateEmpty.Proof -- shake: keep

/-!
# Main Proof of Empty-State `spqr::recv`

Combines the preamble varint loops and `Ok`/`Err` tails to prove `spqrRecvEmpty_base_F`,
`spqrRecvEmpty_base`, and `spqrRecvEmpty_run'`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSpqr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.InImage.DecodeStateEmpty
  (mr_cut' vecU8Tail vecArg_at_nil)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- The buffer tail of `msg.at A` (`vecU8At`). -/
def msgHeaderTail (A : RustAlloc) (msg : VecArg) : SepProp :=
  if msg.cap = 0 then emp
  else A.live msg.ptr msg.cap.toNat 1 ∗ (msg.ptr ↦ₛ msg.bytes) ∗
    memRegion (msg.ptr + BitVec.ofNat 64 msg.bytes.length) (msg.cap.toNat - msg.bytes.length)

theorem msg_expose_hdr (A : RustAlloc) (msg : VecArg) :
    msg.at A ⊢
      ⌜msg.bytes.length < 2 ^ 63⌝ ∗
      (msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
      ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      msgHeaderTail A msg := by
  have h1 : msg.at A =
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        msgHeaderTail A msg) := by
    simp only [VecArg.at, vecU8At, vecHeader, msgHeaderTail]
    ac_rfl
  rw [h1]
  refine Entails.pure_left fun hp => ?_
  have hlt : msg.bytes.length < 2 ^ 63 := Nat.lt_of_le_of_lt hp.1 hp.2.1
  refine Entails.pure_right hlt ?_
  rw [show ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
        msgHeaderTail A msg) =
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
        ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
        msgHeaderTail A msg) by ac_rfl]
  exact Entails.pure_right hp (Entails.refl _)

theorem msg_unexpose_hdr (A : RustAlloc) (msg : VecArg) :
    ((msg.v ↦₆₄ msg.cap) ∗ ((msg.v + 8#64) ↦₆₄ msg.ptr) ∗
      ((msg.v + 16#64) ↦₆₄ BitVec.ofNat 64 msg.bytes.length) ∗
      ⌜msg.bytes.length ≤ msg.cap.toNat ∧ msg.cap.toNat < 2 ^ 63 ∧ msg.ptr ≠ 0⌝ ∗
      msgHeaderTail A msg) ⊢ msg.at A := by
  simp only [VecArg.at, vecU8At, vecHeader, msgHeaderTail, sepConj_assoc]
  exact Entails.refl _

theorem spqrRecvEmpty_nil : spqrRecvEmpty [] = .ok ([], none) := rfl

theorem spqrRecvEmpty_singleton (v : BitVec 8) : spqrRecvEmpty [v] = .error false := rfl

theorem spqrRecvEmpty_cons_cons (v b : BitVec 8) (rest : List (BitVec 8)) :
    spqrRecvEmpty (v :: b :: rest) =
      match spqrVarintAux 0 0#64 (b :: rest) with
      | none => .error false
      | some (epoch, rest1) =>
        if epoch == 0#64 then .error false
        else
          match spqrDecodeVarint rest1 with
          | none => .error false
          | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
  change (if (match spqrVarintAux 0 0#64 (b :: rest) with
    | none => none
    | some (epoch, rest1) =>
      if epoch = 0#64 then none
      else match spqrDecodeVarint rest1 with
        | none => none
        | some (index, rest2) =>
          if index.toNat < 2 ^ 32 then some ({ version := v, epoch := epoch, index := index.setWidth 32, remaining := rest2 } : MsgPreamble)
          else none).isSome = true then Except.ok ([], none) else Except.error false) = _
  cases spqrVarintAux 0 0#64 (b :: rest) with
  | none => rfl
  | some p =>
    rcases p with ⟨epoch, rest1⟩
    dsimp only
    by_cases he : epoch = 0#64
    · subst he; rfl
    · have hef : (epoch == 0#64) = false := beq_false_of_ne he
      simp only [he, hef, ↓reduceIte]
      cases spqrDecodeVarint rest1 with
      | none => rfl
      | some q =>
        rcases q with ⟨index, rest2⟩
        dsimp only
        by_cases hi : index.toNat < 2 ^ 32
        · simp only [hi, ↓reduceIte]; rfl
        · simp only [hi, ↓reduceIte]; rfl

theorem msg_nil_of_len_zero {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h0 : BitVec.ofNat 64 bs.length = 0#64) : bs = [] := by
  have hlen0 : bs.length = 0 := by bv_omega
  exact List.eq_nil_of_length_eq_zero hlen0

theorem msg_singleton_of_len_one {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h1 : BitVec.ofNat 64 bs.length = 1#64) : ∃ v, bs = [v] := by
  have hlen1 : bs.length = 1 := by bv_omega
  cases bs with
  | nil => simp at hlen1
  | cons v rest =>
    simp at hlen1
    exact ⟨v, congrArg (v :: ·) hlen1⟩

theorem msg_cons_cons_of_len_ge_two {bs : List (BitVec 8)} (hlt : bs.length < 2 ^ 63)
    (h0 : ¬BitVec.ofNat 64 bs.length = 0#64)
    (h1 : ¬BitVec.ofNat 64 bs.length = 1#64) :
    ∃ v b rest, bs = v :: b :: rest := by
  have hge2 : 2 ≤ bs.length := by bv_omega
  cases bs with
  | nil => simp at hge2
  | cons v rest1 =>
    cases rest1 with
    | nil => simp at hge2
    | cons b rest => exact ⟨v, b, rest, rfl⟩

set_option maxHeartbeats 1600000 in
/-- `spqr::recv` on an empty state, on the session code rebased at `b` with an arbitrary hook
table `hooks` and an arbitrary frame `F` (in place of `logOff img`), given the `bl memcpy` contract
`hmc` on that table; the post without the `¬ S.recvPanics` conjunct (`spqrRecvEmptyCodeSpec0`). -/
theorem spqrRecvEmpty_base_F0 (b : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) (hE : S.RecvEmptyOk)
    (hmc : subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName)
      (spqrRecvEmptyCodeSpec0 A S img F) := by
  have hfn : libsignalSessionCode.fnOff spqrRecvName = num% (ls_off% "spqr::recv") :=
    (ls_lemma% fnOff "spqr::recv")
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    b hooks hfn (num% (ls_off% "spqr::recv")) 0 96
  code_fetches_range CryptoVerification.libsignalSessionCode spqrRecvBin
    b hooks hfn (num% (ls_off% "spqr::recv")) 292 20
  clear hfn
  wp_init x s0
  obtain ⟨st, msg, ret⟩ := x
  dsimp only at *
  have hpc' : s0.pc = (libsignalSessionCode.rebase b hooks).fnAddr "spqr::recv" := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "spqr::recv")]; exact hpc
  clear hpc
  have herr_tail := step_recv_err_tail img b hooks A S F st msg ret
  have hok_tail := step_recv_ok_tail img b hooks A S F hmc st msg ret
  have hep_loop := step_epoch_loop img b hooks A S F hmc st msg ret
  dsimp only [spqrRecvName, BitVec.ofNat_eq_ofNat] at herr_tail hok_tail hep_loop ⊢
  clear hmc
  have hI0 : RecvImgInv img s0 := ⟨by assumption, by assumption⟩
  generalize_entry (libsignalSessionCode.rebase b hooks).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_simp_pre only [ret_48_split ret, stackAt_spqrRecv_split s0.sp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply SepWP.exists_elim; intro s19
  apply SepWP.exists_elim; intro s20
  apply SepWP.exists_elim; intro s21
  apply SepWP.exists_elim; intro s22
  apply SepWP.exists_elim; intro s23
  apply SepWP.exists_elim; intro s24
  apply SepWP.exists_elim; intro s25
  apply SepWP.exists_elim; intro s26
  apply SepWP.exists_elim; intro s27
  apply SepWP.exists_elim; intro s28
  apply SepWP.exists_elim; intro s30
  apply SepWP.exists_elim; intro s29
  apply SepWP.exists_elim; intro b60
  apply SepWP.exists_elim; intro b58
  apply SepWP.exists_elim; intro b50
  apply SepWP.exists_elim; intro probe
  apply SepWP.exists_elim; intro f24
  apply SepWP.exists_elim; intro f16
  apply SepWP.exists_elim; intro f8
  apply SepWP.exists_elim; intro f0
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  refine SepWP.fold (msg_expose_hdr A msg) (by sep_focus) ?_
  refine SepWP.focus_pure (by sep_focus) fun hlen_lt => ?_
  apply sepWP_seq_recvImg (mid := entry + bv% (48)) hI0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hI1
  wp_steps
  wp_if hlen0
  · refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
    wp_steps
    have hmsg_nil : msg.bytes = [] := msg_nil_of_len_zero hlen_lt hlen0
    have hok : S.recv st.bytes msg.bytes = .ok ([], none) := by
      rw [h_1, hE.recv, hmsg_nil, spqrRecvEmpty_nil]
    exact hok_tail 0#8 r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0 _ _ R _
      rfl h_1 hok (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simp [arm64_norm]) hsp_align (by simp [arm64_norm])
      (by simp [h_4, arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by unfold recvStackRest; ac_rfl)
      (RecvImgInv.congr hI1 (by simp [arm64_norm]) (by simp [arm64_norm]))
  · wp_steps
    wp_if hlen1
    · refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
      obtain ⟨v, hv⟩ := msg_singleton_of_len_one hlen_lt hlen1
      have herr : S.recv st.bytes msg.bytes = .error false := by
        rw [h_1, hE.recv, hv, spqrRecvEmpty_singleton]
      exact herr_tail r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0 _ _ R _
        rfl herr (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        (by simp [arm64_norm]) hsp_align (by simp [arm64_norm])
        (by simp [arm64_norm]) (by unfold recvStackRest; ac_rfl)
    · wp_steps
      refine SepWP.fold (msg_unexpose_hdr A msg) (by sep_focus) ?_
      obtain ⟨version, b₀, rest0', hmsg_eq⟩ := msg_cons_cons_of_len_ge_two hlen_lt hlen0 hlen1
      have hsplit0 : msg.bytes = ([] : List (BitVec 8)) ++ version :: (b₀ :: rest0') := hmsg_eq
      have hoff0 : msg.ptr = msg.ptr + BitVec.ofNat 64 ([] : List (BitVec 8)).length := by
        simp [List.length_nil]
      have hexp0 := msg_expose_byte A msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
      have hunexp0 := msg_unexpose_byte A msg [] (b₀ :: rest0') version msg.ptr hsplit0 hoff0
      clear hoff0 hsplit0
      have hmsg_symm := hmsg_eq.symm; clear hmsg_eq
      refine SepWP.fold hexp0 (by sep_focus) ?_
      wp_steps
      refine SepWP.fold hunexp0 (by sep_focus) ?_
      have hlen_eq : msg.bytes.length = 1 + 0 + (b₀ :: rest0').length := by
        rw [← hmsg_symm, List.length_cons]
        omega
      have hrecv0 : S.recv st.bytes msg.bytes =
          match spqrVarintAux 0 0#64 (b₀ :: rest0') with
          | none => .error false
          | some (epoch, rest1) =>
            if epoch == 0#64 then .error false
            else
              match spqrDecodeVarint rest1 with
              | none => .error false
              | some (index, _) => if index.toNat < 2 ^ 32 then .ok ([], none) else .error false := by
        rw [h_1, hE.recv, ← hmsg_symm, spqrRecvEmpty_cons_cons]
      exact hep_loop version (b₀ :: rest0') r0 r1 r2 r3 f0 f8 f16 f24 b50 b58 b60 s0 R _
        rfl h_1 hsp_align hlen_lt 10 0 0#64 [] rest0' b₀ _ _
        (by omega) (by omega) hmsg_symm.symm rfl rfl hrecv0
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [h_4, arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by simp [arm64_norm]; exact csel_rest1_min_10 hlen_eq hlen_lt)
        (by simp [arm64_norm]) (by simp [arm64_norm])
        (by unfold recvStackRest; ac_rfl)
        (RecvImgInv.congr hI1 (by simp [arm64_norm]) (by simp [arm64_norm]))

/-- `spqr::recv` on an empty state, on the session code rebased at `b` with an arbitrary hook
table `hooks` and an arbitrary frame `F` (in place of `logOff img`), given the `bl memcpy` contract
`hmc` on that table; `spqrRecvEmpty_base_F0` plus `hE.noPanic` (`spqrRecvEmptyCodeSpec_of_0`). -/
theorem spqrRecvEmpty_base_F (b : BitVec 64) (hooks : String → Option (State → State))
    (A : RustAlloc) (S : SpqrModel) (img : Obj.Image) (F : SepProp) (hE : S.RecvEmptyOk)
    (hmc : subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName +
        bv% (ls_off% "memcpy" - ls_off% "spqr::recv"))
      (memcpyRecvPcsSpecS.inImage img)) :
    subroutine_ok (libsignalSessionCode.rebase b hooks)
      ((libsignalSessionCode.rebase b hooks).fnAddr spqrRecvName)
      (spqrRecvEmptyCodeSpec A S img F) :=
  spqrRecvEmptyCodeSpec_of_0 hE (spqrRecvEmpty_base_F0 b hooks A S img F hE hmc)

set_option maxHeartbeats 1600000 in
theorem spqrRecvEmpty_base (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image) (hE : S.RecvEmptyOk) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs) ((tripleRatchetProgAt img.base C ctl abs).fnAddr spqrRecvName)
      (spqrRecvEmptySpec A S img) := by
  rw [spqrRecvEmptySpec_eq_code]
  exact spqrRecvEmpty_base_F img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) A S img
    (logOff img) hE (memcpy_recv_ok_at_S img img.base C ctl abs)

theorem spqrRecvEmpty_run' (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (abs : String → Option (State → State)) (img : Obj.Image) :
    SpqrRecvEmptyRunStmt C A ctl S abs img := by
  intro _ hE himg
  exact root_of_tripleRatchetProgAt himg (spqrRecvEmpty_base C A ctl S abs img hE)

end CryptoVerification.LibsignalTripleRatchet.InImage.SpqrRecvEmpty
