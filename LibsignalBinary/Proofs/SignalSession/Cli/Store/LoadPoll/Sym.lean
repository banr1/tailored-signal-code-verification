/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Branches
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append
  fs_setPC fs_advancePC fs_setMem fs_setPState fs_writeReg64 fs_writeReg32
  fs_writeReg fs_writeVReg128 fs_applyWriteback

/-- Post-`deserialize` copy block (`+0x078 .. +0x0b4`): checks `prevCap ≠ -1`, loads the inline
record words into callee-saved registers / stack slots, and copies the 312-byte `tail` to
`sp + 8` via `memcpy`. -/
theorem lpoll_deser_copy_78 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (s0 s : State)
    (prevCap prevPtr curCap w4 w5 w6 c_sp0 : BitVec 64)
    (q140 : BitVec 128) (tail : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    {ret : BitVec 64}
    (hprev_lt : prevCap.toNat < 2 ^ 63)
    (htail_len : tail.length = 312)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName + bv% (120))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0x350#64)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx25 : s.readReg64 .x25 = s0.sp - 0x210#64)
    (hfoc : P ⊢
      ((s0.sp - 0x1e0#64) ↦₆₄ prevCap) ∗
      ((s0.sp - 0x1d8#64) ↦₆₄ prevPtr) ∗
      ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 0x1c8#64) ↦₆₄ curCap) ∗
      ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
      ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
      ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      stackAt (s0.sp - 0x350#64) extHookStack ∗
      F)
    (hk : ∀ (sm : State),
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName + bv% (180) →
      sm.status = .Running →
      sm.sp = s0.sp - 0x350#64 →
      ImgCallInv img sm →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = s.readReg64 .x24 →
      sm.readReg64 .x27 = prevCap →
      sm.readReg64 .x26 = prevPtr →
      sm.readReg64 .x25 = curCap →
      sm.readReg64 .x22 = w4 →
      sm.readReg64 .x28 = s0.sp - 0x210#64 →
      SepWP (tripleRatchetProgAtExt img.base ext) ret sm
        ((((s0.sp - 0x348#64) ↦ₛ tail) ∗
          ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
          stackAt (s0.sp - 0x350#64) extHookStack) ∗
          (((s0.sp - 0x1e0#64) ↦₆₄ prevCap) ∗
            ((s0.sp - 0x1d8#64) ↦₆₄ prevPtr) ∗
            ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0x1c8#64) ↦₆₄ curCap) ∗
            ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
            ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
            ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
            F))
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmemcpy := lpoll_memcpy_ok_at hC
  clear hC
  have hprev_beq : (prevCap + 1#64 == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have hlt64 : prevCap.toNat + 1 < 2 ^ 64 := by omega
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt64] at h1
    exact Nat.succ_ne_zero _ h1
  have hfn : libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    sessLoadPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    120 60
  dsimp only [tripleRatchetProgAtExt] at hmemcpy hpc hk ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    sessLoadPollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  unfold Arm64.pointsTo128
  simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "memcpy"))
    hinv
  wp_steps
  let _ := hprev_beq
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv_mc
  have ⟨hF_mc, hsym_mc⟩ := hinv_mc
  apply SepWP.seq_inImage (mid := fnBase + bv% (180)) hinv_mc
  wp_call hmemcpy (s0.sp - 0x348#64, s0.sp - 0x1a8#64, tail)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_b4
  refine SepWP.weaken_pre
    (Entails.of_eq (by
      have h440 : s0.sp - 0x1b8#64 + 8#64 = s0.sp - 432#64 := by bv_omega
      have h528 : s0.sp - 0x210#64 + 8#64 = s0.sp - 520#64 := by bv_omega
      unfold Arm64.pointsTo128
      simp only [hsp, h440, h528, extractLsb_0_64_append, extractLsb_64_64_append]
      ac_rfl))
    (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) hinv_b4 (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]))

/-- Branch 3 (`+0x054` on `gr = .ok (b0 :: bsRest)`): calls `SessionRecord::deserialize`
(`sessDeserializeExtSpec`), copies the record out through two 312-byte `memcpy`s, frees `bytes`
and `name`, and returns `.ok (some r)`. -/
theorem lpoll_branch_ok_cons_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName -
        bv% (ls_rel%
          "<libsignal_protocol::state::session::SessionRecord>::deserialize"
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      (sessDeserializeExtSpec Scope A img))
    (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
    (r : SessionRecord (List (BitVec 8))) (b0 : BitVec 8) (bsRest : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (henc : E2E.Record.encodeRecord r = b0 :: bsRest)
    (hsc : Scope r)
    (hgr : Except.ok (b0 :: bsRest) =
        x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
      sm2.trace = s0.trace)
    (hpc : sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName + bv% (84))
    (hrun : sm2.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : sm2.sp = s0.sp - 0x350#64)
    (hinv : ImgCallInv img sm2)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.call.fut)
    (hx20 : sm2.readReg64 .x20 = x.call.out)
    (hx21 : sm2.readReg64 .x21 = namePtr)
    (hx25 : sm2.readReg64 .x25 = s0.sp - 0x210#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0x1e0#64) (.ok (b0 :: bsRest)) ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f =>
        (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).onPanic x s0 sf ∗ R)) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hdes_le : E2E.Record.recDeserializeStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hdc78 := @lpoll_deser_copy_78 img A ext hC
  have hf14c := lpoll_finish_14c hC
  have hdb13c := lpoll_drop_bytes_13c hC
  clear hC
  have hfn : libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    sessLoadPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    84 36
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    180 12
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    304 12
  dsimp only [tripleRatchetProgAtExt] at hdc78 hf14c hdb13c hDeser hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    sessLoadPollName = fnBase
  examples_hide_fetches
  rw [← henc]
  unfold postGetCommon
  rw [getResultAt_ok_unpack A s0.sp (E2E.Record.encodeRecord r),
      subStack_split s0.sp hdes_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr =>
    SepWPp.pure_elim fun ⟨hblen, hblt, hbptr⟩ => ?_
  have hlen_beq : (BitVec.ofNat 64 (b0 :: bsRest).length == 0#64) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro heq
    have h1 := congrArg BitVec.toNat heq
    have h2 : bsRest.length + 1 < 2 ^ 64 := by
      have : (b0 :: bsRest).length = bsRest.length + 1 := rfl
      rw [← this, ← henc]; omega
    simp only [List.length_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2] at h1
    exact Nat.succ_ne_zero _ h1
  have hlen_beq' : (BitVec.ofNat 64 (E2E.Record.encodeRecord r).length == 0#64) = false := by
    simpa only [henc] using hlen_beq
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_protocol::state::session::SessionRecord>::deserialize"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    hinv
  wp_steps
  let _ := hlen_beq; let _ := hlen_beq'
  apply SepWP.done (by simp only [arm64_norm]; bv_omega) (by wp_norm_lhs)
  intro hinv_ds
  refine sepWPp_name_state fun s3 hs3 => ?_
  have hs3_pc : s3.pc = fnBase - bv% (ls_rel%
      "<libsignal_protocol::state::session::SessionRecord>::deserialize"
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") := by
    rw [hs3]; simp only [arm64_norm, *]; bv_omega
  have hs3_lr : s3.readReg64 Reg.lr = fnBase + bv% (120) := by
    rw [hs3]; simp only [arm64_norm, *]
  have hs3_run : s3.status = .Running := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_sp : s3.sp = s0.sp - 0x350#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_tr : s3.trace = s0.trace := by rw [hs3]; simp only [hgr.2, arm64_norm, *]
  have hs3_x0 : s3.readReg64 .x0 = bytesPtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x1 : s3.readReg64 .x1 = BitVec.ofNat 64 (E2E.Record.encodeRecord r).length := by
    rw [hs3]; simp only [arm64_norm, *]
  have hs3_x8 : s3.readReg64 .x8 = s0.sp - 0x1e0#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x19 : s3.readReg64 .x19 = x.call.fut := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x20 : s3.readReg64 .x20 = x.call.out := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x21 : s3.readReg64 .x21 = namePtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x23 : s3.readReg64 .x23 = bytesCap := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x24 : s3.readReg64 .x24 = bytesPtr := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_x25 : s3.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs3]; simp only [arm64_norm, *]
  have hs3_vregs : calleeSavedVRegs s3 = calleeSavedVRegs s0 := by
    rw [hs3]; simp only [arm64_norm, *]
  rw [← hs3] at hinv_ds
  clear hs3
  let F_des : SepProp :=
    vecU8Tail A bytesCap bytesPtr (E2E.Record.encodeRecord r) ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
    vecU8Tail A nameCap namePtr nameBs ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - E2E.Record.recDeserializeStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA
  refine lpoll_call_deser_ext hDeser
    { p := bytesPtr, out := s0.sp - 0x1e0#64, r := r } F_des
    (s0 := s0)
    hs3_pc hs3_run (spAligned_sub_350 hsp_align hs3_sp) hs3_lr hs3_tr hinv_ds
    hs3_x0 hs3_x1 hs3_x8 hsc
    (fun sf P_f halloc hmf => by
      dsimp only [sessLoadPollSpec, Spec.inImage]
      simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf)
    (by
      rw [hs3_sp]
      refine Entails.trans (Q :=
        (((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 (E2E.Record.encodeRecord r).length) ∗
          memRegion (s0.sp - 0x1c0#64) 16 ∗ memRegion (s0.sp - 0x1b0#64) 320) ∗
        ((bytesPtr ↦ₛ E2E.Record.encodeRecord r) ∗ A.pool ∗
          stackAt (s0.sp - 0x350#64) E2E.Record.recDeserializeStack ∗ F_des))
        (Entails.of_eq (by
          unfold F_des SpqrV1.ChainProofs.bytesAt
          simp only [Bool.false_eq_true, ite_false]
          ac_rfl)) ?_
      refine Entails.trans (sepConj_mono_left (slot170_ok_collapse s0.sp okTagVec bytesCap bytesPtr
        (BitVec.ofNat 64 (E2E.Record.encodeRecord r).length))) ?_
      exact Entails.of_eq (by ac_rfl))
    fun sm3 gE2E hpcm3 hrunm3 hspm3 hcsm3 hinvm3 htrm3 _hcan => ?_
  rw [hs3_sp]
  rcases hcsm3 with ⟨hx19_3, hx20_3, hx21_3, _, hx23_3, hx24_3, hx25_3, _, _, _, _, hvregs_3⟩
  have hx19_m3 : sm3.readReg64 .x19 = x.call.fut := hx19_3.trans hs3_x19
  have hx20_m3 : sm3.readReg64 .x20 = x.call.out := hx20_3.trans hs3_x20
  have hx21_m3 : sm3.readReg64 .x21 = namePtr := hx21_3.trans hs3_x21
  have hx23_m3 : sm3.readReg64 .x23 = bytesCap := hx23_3.trans hs3_x23
  have hx24_m3 : sm3.readReg64 .x24 = bytesPtr := hx24_3.trans hs3_x24
  have hx25_m3 : sm3.readReg64 .x25 = s0.sp - 0x210#64 := hx25_3.trans hs3_x25
  have hvregs_m3 : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := hvregs_3.trans hs3_vregs
  have htr_m3 : sm3.trace = s0.trace := htrm3.trans hs3_tr
  apply sepWPp_of_sepWP_final
  let g : RecordGhost := E2E.InMem.SessionStoreImpl.ofRecordGhost gE2E
  have hunpack : E2E.Record.sessionRecordAt A (s0.sp - 0x1e0#64) gE2E r ⊢
      (∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ tail : List (BitVec 8),
        ⌜g.prevCap.toNat < 2 ^ 63 ∧ Pf.RecordMove.RecordTailInline g r w4 w5 w6 tail⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordHeap A g r) :=
    record_unpack_for_poll A s0.sp gE2E r
  unfold F_des
  have hrestk :
      stackAt (s0.sp - 0x350#64) E2E.Record.recDeserializeStack ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - E2E.Record.recDeserializeStack) =
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - extHookStack) ∗
      stackAt (s0.sp - 0x350#64) extHookStack := by
    rw [sepConj_comm, ← subStack_split s0.sp hdes_le hmin_hi,
        subStack_split s0.sp hext_le hmin_hi]
  refine SepWP.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hunpack))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun w4 => SepWP.exists_elim fun w5 =>
    SepWP.exists_elim fun w6 => SepWP.exists_elim fun tail => ?_
  refine SepWP.weaken_pre
    (Entails.of_eq (by
      unfold SpqrV1.ChainProofs.bytesAt
      simp only [Bool.false_eq_true, ite_false]
      ac_rfl) :
      _ ⊢
      ⌜g.prevCap.toNat < 2 ^ 63 ∧ Pf.RecordMove.RecordTailInline g r w4 w5 w6 tail⌝ ∗
        (stackAt (s0.sp - 0x350#64) E2E.Record.recDeserializeStack ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - E2E.Record.recDeserializeStack)) ∗
        SpqrV1.ChainProofs.bytesAt false bytesPtr (E2E.Record.encodeRecord r) ∗
        vecU8Tail A bytesCap bytesPtr (E2E.Record.encodeRecord r) ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        Pf.RecordMove.recordHeap A g r ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        memRegion (s0.sp - 0x348#64) 312 ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) ?_
  refine SepWP.pure_elim fun ⟨hprev_lt, hinl⟩ => ?_
  rw [hrestk]
  have htail_len : tail.length = 312 := hinl.1
  let F_copy : SepProp :=
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    SpqrV1.ChainProofs.bytesAt false bytesPtr (E2E.Record.encodeRecord r) ∗
    vecU8Tail A bytesCap bytesPtr (E2E.Record.encodeRecord r) ∗
    Pf.RecordMove.recordHeap A g r ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
    vecU8Tail A nameCap namePtr nameBs ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA ∗
    A.pool
  refine hdc78 s0 sm3 g.prevCap g.prevPtr (Pf.RecordMove.recordCurCap g) w4 w5 w6 c_sp0
    q140 tail _ F_copy
    hprev_lt htail_len hpcm3 hrunm3 hsp_align (hspm3.trans hs3_sp) hinvm3 hvregs_m3 hx25_m3
    (Entails.of_eq (by unfold F_copy; ac_rfl))
    fun sm4 hpcm4 hrunm4 hspm4 hinvm4 hvregsm4 htrm4
      hx19_4 hx20_4 hx21_4 hx23_4 hx24_4 hx27_4 hx26_4 hx25_4 hx22_4 hx28_4 => ?_
  have hsp_al4 : sm4.spAligned = true := spAligned_sub_350 hsp_align hspm4
  have hx19_m4 : sm4.readReg64 .x19 = x.call.fut := hx19_4.trans hx19_m3
  have hx20_m4 : sm4.readReg64 .x20 = x.call.out := hx20_4.trans hx20_m3
  have hx21_m4 : sm4.readReg64 .x21 = namePtr := hx21_4.trans hx21_m3
  have hx23_m4 : sm4.readReg64 .x23 = bytesCap := hx23_4.trans hx23_m3
  have hx24_m4 : sm4.readReg64 .x24 = bytesPtr := hx24_4.trans hx24_m3
  have htr_m4 : sm4.trace = s0.trace := htrm4.trans htr_m3
  let F_some : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
    ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
    ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
    ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
    ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
    Pf.RecordMove.recordHeap A g r ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x g.prevCap g.prevPtr 0#64 (Pf.RecordMove.recordCurCap g) w4
        (w6 ++ w5) tail ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗ A.pool ∗ F_some) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hgr_f :
        Except.ok (b0 :: bsRest) =
          x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
        sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq⟩
    have hans : SessLoadAns Scope (.ok (b0 :: bsRest)) (.ok (some r)) := ⟨r, rfl, henc, hsc⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails rd pathOk Scope A img stk x s0 sf (.ok (b0 :: bsRest)) (.ok (some r))
        hgr_f hans)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.ok (some r)) nameCap namePtr nameBs 0#64
        (w6 ++ w5))
    have hrec := record_reassemble_for_poll A s0.sp x.call.out g r hinl
    have hgrp :
        epilogueOut s0 x g.prevCap g.prevPtr 0#64 (Pf.RecordMove.recordCurCap g) w4
          (w6 ++ w5) tail ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗ A.pool ∗ F_some =
        (((x.call.out ↦₆₄ g.prevCap) ∗ ((x.call.out + 8#64) ↦₆₄ g.prevPtr) ∗
          ((x.call.out + 0x10#64) ↦₆₄ 0#64) ∗
          ((x.call.out + 0x18#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
          ((x.call.out + 0x20#64) ↦₆₄ w4) ∗ ((x.call.out + 0x28#64) ↦₁₂₈ (w6 ++ w5)) ∗
          ((x.call.out + 0x38#64) ↦ₛ tail) ∗
          ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
          ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗ ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
          ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
          ((s0.sp - 0x348#64) ↦ₛ tail) ∗
          Pf.RecordMove.recordHeap A g r) ∗
        ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - extHookStack) ∗
          stackAt (s0.sp - 0x350#64) extHookStack ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗
          dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗
          A.pool)) := by
      unfold epilogueOut F_some; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono_left hrec) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.weaken_pre (P' :=
      (SpqrV1.ChainProofs.bytesAt false bytesPtr (E2E.Record.encodeRecord r) ∗
        vecU8Tail A 0#64 bytesPtr (E2E.Record.encodeRecord r)) ∗
      (((s0.sp - 0x348#64) ↦ₛ tail) ∗
        ((s0.sp - 0x1a8#64) ↦ₛ tail) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ g.prevCap) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ g.prevPtr) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ Pf.RecordMove.recordCurCap g) ∗
        ((s0.sp - 0x1c0#64) ↦₆₄ w4) ∗
        ((s0.sp - 0x1b8#64) ↦₁₂₈ (w6 ++ w5)) ∗
        ((s0.sp - 0x350#64) ↦₆₄ 0#64) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ (w6 ++ w5)) ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        Pf.RecordMove.recordHeap A g r ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool))
      (Entails.of_eq (by unfold F_copy; ac_rfl)) ?_
    refine SepWP.weaken_pre
      (sepConj_mono_left (vecU8_free_zero A bytesPtr hblen)) ?_
    simp only [emp_sepConj]
    apply SepWP.seq_inImage (mid := fnBase + bv% (332)) hinvm4
    wp_steps
    let _ := hsp_al4
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_14c
    refine hf14c x s0 _ nameCap namePtr nameBs
      g.prevCap g.prevPtr 0#64 (Pf.RecordMove.recordCurCap g) w4
      (w6 ++ w5) tail _ F_some
      hnlen hnlt hnptr htail_len
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hinv_14c
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (Entails.of_eq (by unfold epiloguePre F_some; ac_rfl))
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    apply SepWP.seq_inImage (mid := fnBase + bv% (316)) hinvm4
    wp_steps
    let _ := hsp_al4; let _ := hbcap_beq
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_13c
    refine hdb13c x s0 _ bytesCap bytesPtr (E2E.Record.encodeRecord r)
      nameCap namePtr nameBs
      g.prevCap g.prevPtr 0#64 (Pf.RecordMove.recordCurCap g) w4
      (w6 ++ w5) tail _ F_some
      hbcap hblen hblt hbptr hnlen hnlt hnptr htail_len
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hinv_13c
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (Entails.of_eq (by unfold F_copy epiloguePre F_some; ac_rfl))
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Branch 3 (`+0x054` on `gr = .ok (b0 :: bsRest)`): `sessDeserializeSpec` wrapper. -/
theorem lpoll_branch_ok_cons {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName -
        bv% (ls_rel%
          "<libsignal_protocol::state::session::SessionRecord>::deserialize"
          "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
      (sessDeserializeSpec Scope A img)) :
    ∀ (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
      (r : SessionRecord (List (BitVec 8))) (b0 : BitVec 8) (bsRest : List (BitVec 8))
      (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
      (c_sp0 : BitVec 64) (q140 : BitVec 128),
      pollMinStk addrStk getStk ≤ stk →
      stk ≤ 2 ^ 64 →
      nameBs.length ≤ nameCap.toNat →
      nameCap.toNat < 2 ^ 63 →
      namePtr ≠ 0#64 →
      E2E.Record.encodeRecord r = b0 :: bsRest →
      Scope r →
      (Except.ok (b0 :: bsRest) =
          x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
        sm2.trace = s0.trace) →
      sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName + bv% (84) →
      sm2.status = .Running →
      s0.sp &&& 15#64 = 0#64 →
      sm2.sp = s0.sp - 0x350#64 →
      ImgCallInv img sm2 →
      calleeSavedVRegs sm2 = calleeSavedVRegs s0 →
      sm2.readReg64 .x19 = x.call.fut →
      sm2.readReg64 .x20 = x.call.out →
      sm2.readReg64 .x21 = namePtr →
      sm2.readReg64 .x25 = s0.sp - 0x210#64 →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
        (getResultAt A (s0.sp - 0x1e0#64) (.ok (b0 :: bsRest)) ∗
          postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
        (fun sf P_f =>
          ((sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
        (fun sf P_f =>
          (sf.mem ⊨ P_f ∗ R) →
            (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).onPanic x s0 sf ∗ R)) :=
  lpoll_branch_ok_cons_ext hC (subroutine_ok_sessDeserializeExtSpec_of_spec hDeser)

/-- Top-level proof of `load_session::{closure#0}` against `sessLoadPollSpec` from
`sessDeserializeExtSpec Scope A img` (carrying `A.pool`). -/
theorem sessLoadPoll_ok_ext {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeExtSpec Scope A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : pollMinStk addrStk getStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName)
      (sessLoadPollSpec rd pathOk Scope A img stk) := by
  rw [← addressText_fnAddr_eq img.base ext] at hAddr
  rw [← dirGet_fnAddr_eq img.base ext] at hGet
  rw [← recordDeserialize_fnAddr_eq img.base ext] at hDeser
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hAddrFs := subroutine_ok_withFsInv hFs hAddr s0.fs.files s0.trace
  have hbrErr := @lpoll_branch_err img A ext rd pathOk Scope addrStk getStk stk hC
  have hbrNil := @lpoll_branch_ok_nil img A ext rd pathOk Scope addrStk getStk stk hC
  have hbrCons := @lpoll_branch_ok_cons_ext img A ext rd pathOk Scope addrStk getStk stk hC hDeser
  clear hFs hAddr hDeser hC
  refine ⟨(sessLoadPollSpec rd pathOk Scope A img stk).pre x s0, R, hpre, ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).onPanic x s0 sf ∗ R)) = Qp
  have hpan_fn : ∀ (sf : State) (P_f : SepProp),
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f := by
    rw [← hQp_eq]
    intro sf P_f halloc hmf
    dsimp only [sessLoadPollSpec, Spec.inImage]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  dsimp only [sessLoadPollSpec, Spec.inImage]
  refine SepWPp.pure_elim fun ⟨hinv0_F, hinv0_sym⟩ => ?_
  refine SepWPp.pure_elim fun ⟨hx0_0, hx8_0, hname_lt, htext_lt, hdir_lt, hpOk, hwf⟩ => ?_
  refine sepWPp_with_stk_bound (a := x.call.fut) (v := x.self)
    (Rest := ((x.call.fut + 8#64) ↦₆₄ x.call.addrA) ∗ ((x.call.fut + 0x10#64) ↦₈ 0#8) ∗
      memRegion (x.call.fut + 0x11#64) 7 ∗ dirAt A x.self x.dir ∗
      memRegion x.call.out 368 ∗ protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool)
    (Entails.of_eq (by unfold sessLoadBoxAt; ac_rfl))
    fun hstk_hi => ?_
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have haddr_le : addrStk ≤ subMax addrStk getStk := by unfold subMax; omega
  have hget_le : getStk ≤ subMax addrStk getStk := by unfold subMax; omega
  have hfn : libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    sessLoadPoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}")) 84
  have hinv0 : ImgCallInv img s0 := ⟨hinv0_F, hinv0_sym⟩
  dsimp only [tripleRatchetProgAtExt] at hbrErr hbrNil hbrCons hAddrFs hGet hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    sessLoadPollName = fnBase
  examples_hide_fetches
  rw [stackAt_sub_split s0.sp hstk hstk_hi,
      stackAt_loadPoll_eq s0.sp hmin_hi,
      subStack_split s0.sp haddr_le hmin_hi]
  unfold sessLoadBoxAt loadPollFrameSlots
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun c_sp0 => SepWPp.exists_elim fun q140 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 => ?_
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "libsignal_cli::stores::address_text"))
    hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  refine sepWPp_name_state fun s1 hs1 => ?_
  have hs1_pc : s1.pc = fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "libsignal_cli::stores::address_text") := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_lr : s1.readReg64 Reg.lr = fnBase + bv% (64) := by
    rw [hs1]; simp only [arm64_norm, *]
  have hs1_run : s1.status = .Running := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_sp : s1.sp = s0.sp - 0x350#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_tr : s1.trace = s0.trace := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_fs : s1.fs = s0.fs := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x0 : s1.readReg64 .x0 = s0.sp - 0x1f8#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x1 : s1.readReg64 .x1 = x.call.addrA := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x19 : s1.readReg64 .x19 = x.call.fut := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x20 : s1.readReg64 .x20 = x.call.out := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x22 : s1.readReg64 .x22 = x.self := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_x25 : s1.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs1]; simp only [arm64_norm, *]
  have hs1_vregs : calleeSavedVRegs s1 = calleeSavedVRegs s0 := by
    rw [hs1]; simp only [arm64_norm, *]
  rw [← hs1] at hinv1
  clear hs1
  let F_addr : SepProp :=
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    dirAt A x.self x.dir ∗
    memRegion x.call.out 368 ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - addrStk) ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x1e0#64) 368 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0
  refine lpoll_call_addrText hAddrFs
    { addr := x.call.addrA, g := x.call.addr, ret := s0.sp - 0x1f8#64 } F_addr
    (s0 := s0)
    hs1_pc hs1_run (spAligned_sub_350 hsp_align hs1_sp) hs1_lr hs1_tr hinv1
    (by rw [← hs1_fs, ← hs1_tr]; exact FsInv.of_entry s1)
    hs1_x0 hs1_x1 hname_lt hpan_fn
    (Entails.of_eq (by
      rw [hs1_sp]
      unfold F_addr sessLoadBoxAt savedCalleeSlots
      dsimp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24,
        Reg.x25, Reg.x26, Reg.x27, Reg.x28, Reg.x29, Reg.lr]
      ac_rfl))
    fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hinvm1 hfsm1 htrm1 => ?_
  rw [hs1_sp]
  rcases hcsm1 with ⟨hx19_1, hx20_1, _, hx22_1, _, _, hx25_1, _, _, _, _, hvregs_1⟩
  have hsp_m1 : sm1.sp = s0.sp - 0x350#64 := hspm1.trans hs1_sp
  have hsp_al1 : sm1.spAligned = true := spAligned_sub_350 hsp_align hsp_m1
  have hx19_m1 : sm1.readReg64 .x19 = x.call.fut := hx19_1.trans hs1_x19
  have hx20_m1 : sm1.readReg64 .x20 = x.call.out := hx20_1.trans hs1_x20
  have hx22_m1 : sm1.readReg64 .x22 = x.self := hx22_1.trans hs1_x22
  have hx25_m1 : sm1.readReg64 .x25 = s0.sp - 0x210#64 := hx25_1.trans hs1_x25
  have hvregs_m1 : calleeSavedVRegs sm1 = calleeSavedVRegs s0 := hvregs_1.trans hs1_vregs
  have htr_m1 : sm1.trace = s0.trace := htrm1.trans hs1_tr
  have hfiles_m1 : sm1.fs.files = s0.fs.files := files_eq_of_fsInv_trace_eq hfsm1 htr_m1
  let nameBs := addressText x.call.addr.val
  have hrestk1 :
      stackAt (s0.sp - 0x350#64) addrStk ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - addrStk) =
      memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
        (subMax addrStk getStk - getStk) ∗
      stackAt (s0.sp - 0x350#64) getStk := by
    rw [sepConj_comm, ← subStack_split s0.sp haddr_le hmin_hi,
        subStack_split s0.sp hget_le hmin_hi]
  unfold F_addr
  rw [vecU8_eq_bytes_tail A (s0.sp - 0x1f8#64) nameBs (s0.sp - 0x1f0#64) (s0.sp - 0x1e8#64)
        (by bv_omega) (by bv_omega),
      slot170_split48 s0.sp]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr =>
    SepWPp.pure_elim fun ⟨hnlen, hnlt, hnptr⟩ => ?_
  refine sepWPp_conseq
    (P' := ((stackAt (s0.sp - 0x350#64) addrStk ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - addrStk)) ∗
      ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
      ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗
      A.pool ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
      dirAt A x.self x.dir ∗
      memRegion x.call.out 368 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
      memRegion (s0.sp - 0x200#64) 8 ∗
      memRegion (s0.sp - 0x1e0#64) 48 ∗
      memRegion (s0.sp - 0x1b0#64) 320 ∗
      memRegion (s0.sp - 0x070#64) 16 ∗
      savedCalleeSlots s0))
    (Entails.of_eq (by ac_rfl)) ?_
  rw [hrestk1]
  simp only [sepConj_assoc]
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "<libsignal_cli::stores::Dir>::get"))
    hinvm1
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  have hx3_len : (BitVec.ofNat 64 nameBs.length).toNat = nameBs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine sepWPp_name_state fun s2 hs2 => ?_
  have hs2_pc : s2.pc = fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"
      "<libsignal_cli::stores::Dir>::get") := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_lr : s2.readReg64 Reg.lr = fnBase + bv% (84) := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_run : s2.status = .Running := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_sp : s2.sp = s0.sp - 0x350#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_tr : s2.trace = s0.trace := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_files : s2.fs.files = s0.fs.files := by
    have hs2_fs : s2.fs = sm1.fs := by rw [hs2]; simp only [arm64_norm, *]
    rw [hs2_fs]; exact hfiles_m1
  have hs2_x0 : s2.readReg64 .x0 = s0.sp - 0x1e0#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x1 : s2.readReg64 .x1 = x.self := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x2 : s2.readReg64 .x2 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x3 : (s2.readReg64 .x3).toNat = nameBs.length := by
    rw [hs2]; simp only [arm64_norm, *]
  have hs2_x19 : s2.readReg64 .x19 = x.call.fut := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x20 : s2.readReg64 .x20 = x.call.out := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x21 : s2.readReg64 .x21 = namePtr := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_x25 : s2.readReg64 .x25 = s0.sp - 0x210#64 := by rw [hs2]; simp only [arm64_norm, *]
  have hs2_vregs : calleeSavedVRegs s2 = calleeSavedVRegs s0 := by
    rw [hs2]; simp only [arm64_norm, *]
  rw [← hs2] at hinv2
  clear hs2
  let F_get : SepProp :=
    memRegion (s0.sp - 0x1b0#64) 320 ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    vecU8Tail A nameCap namePtr nameBs ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x348#64) 312 ∗
    ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    savedCalleeSlots s0 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - getStk) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    memRegion x.call.out 368 ∗
    sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
    protocolAddressAt A x.call.addr x.call.addrA
  refine lpoll_call_dirGet hGet
    { ret := s0.sp - 0x1e0#64, self := x.self, dir := x.dir,
      nameA := namePtr, name := nameBs, nameRo := false } F_get
    (s0 := s0)
    hs2_pc hs2_run (spAligned_sub_350 hsp_align hs2_sp) hs2_lr hs2_tr hinv2
    hs2_x0 hs2_x1 hs2_x2 hs2_x3
    htext_lt hdir_lt hpOk hpan_fn
    (Entails.of_eq (by rw [hs2_sp]; unfold F_get; dsimp only; ac_rfl))
    fun sm2 gr hpcm2 hrunm2 hspm2 hcsm2 hinvm2 hgr => ?_
  rw [hs2_sp]
  rcases hcsm2 with ⟨hx19_2, hx20_2, hx21_2, _, _, _, hx25_2, _, _, _, _, hvregs_2⟩
  have hsp_m2 : sm2.sp = s0.sp - 0x350#64 := hspm2.trans hs2_sp
  have hx19_m2 : sm2.readReg64 .x19 = x.call.fut := hx19_2.trans hs2_x19
  have hx20_m2 : sm2.readReg64 .x20 = x.call.out := hx20_2.trans hs2_x20
  have hx21_m2 : sm2.readReg64 .x21 = namePtr := hx21_2.trans hs2_x21
  have hx25_m2 : sm2.readReg64 .x25 = s0.sp - 0x210#64 := hx25_2.trans hs2_x25
  have hvregs_m2 : calleeSavedVRegs sm2 = calleeSavedVRegs s0 := hvregs_2.trans hs2_vregs
  have hgr0 :
      gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sm2.trace = s0.trace :=
    ⟨by simpa only [nameBs, hs2_files] using hgr.1, hgr.2.trans hs2_tr⟩
  clear hs2_files hgr
  have hpost_get :
      ((getResultAt A (s0.sp - 0x1e0#64) gr ∗ dirAt A x.self x.dir ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        stackAt (s0.sp - 0x350#64) getStk ∗ A.pool) ∗ F_get) ⊢
      getResultAt A (s0.sp - 0x1e0#64) gr ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140 := by
    have hstk_merge :
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - getStk) ∗
        stackAt (s0.sp - 0x350#64) getStk =
        stackAt (s0.sp - 0x350#64) (subMax addrStk getStk) :=
      (subStack_split s0.sp hget_le hmin_hi).symm
    unfold F_get postGetCommon
    have hpull :
        ((getResultAt A (s0.sp - 0x1e0#64) gr ∗ dirAt A x.self x.dir ∗
          SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
          stackAt (s0.sp - 0x350#64) getStk ∗ A.pool) ∗
          memRegion (s0.sp - 0x1b0#64) 320 ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
          vecU8Tail A nameCap namePtr nameBs ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          memRegion (s0.sp - 0x348#64) 312 ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0 ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - getStk) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          memRegion x.call.out 368 ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
          protocolAddressAt A x.call.addr x.call.addrA) =
        ((memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - getStk) ∗
          stackAt (s0.sp - 0x350#64) getStk) ∗
          (getResultAt A (s0.sp - 0x1e0#64) gr ∗
            memRegion (s0.sp - 0x1b0#64) 320 ∗
            ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
            SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
            vecU8Tail A nameCap namePtr nameBs ∗
            ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
            memRegion (s0.sp - 0x348#64) 312 ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
            memRegion (s0.sp - 0x200#64) 8 ∗
            memRegion (s0.sp - 0x070#64) 16 ∗
            savedCalleeSlots s0 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
            memRegion x.call.out 368 ∗
            sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
            dirAt A x.self x.dir ∗
            protocolAddressAt A x.call.addr x.call.addrA ∗
            A.pool)) := by
      ac_rfl
    rw [hpull, hstk_merge]
    exact Entails.of_eq (by ac_rfl)
  refine sepWPp_conseq hpost_get ?_
  subst hQ_eq hQp_eq
  rcases gr with ⟨⟩ | ⟨_ | ⟨b0, bsRest⟩⟩
  · apply sepWPp_of_sepWP_final
    exact hbrErr x R s0 sm2 nameCap namePtr nameBs c_sp0 q140
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hinvm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2
  · apply sepWPp_of_sepWP_final
    exact hbrNil x R s0 sm2 nameCap namePtr nameBs c_sp0 q140
      hstk hstk_hi hnlen hnlt hnptr hgr0
      hpcm2 hrunm2 hsp_align hsp_m2 hinvm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2
  · rcases hwf (b0 :: bsRest) hgr0.1.symm with hbad | ⟨r, henc, hsc⟩
    · cases hbad
    · exact hbrCons x R s0 sm2 r b0 bsRest nameCap namePtr nameBs c_sp0 q140
        hstk hstk_hi hnlen hnlt hnptr henc hsc hgr0
        hpcm2 hrunm2 hsp_align hsp_m2 hinvm2 hvregs_m2 hx19_m2 hx20_m2 hx21_m2 hx25_m2

/-- Top-level proof of `load_session::{closure#0}` against `sessLoadPollSpec`. -/
theorem sessLoadPoll_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (hAddr : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr addressTextName)
      (addrTextSpec A img addrStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hDeser : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr recordDeserializeName)
      (sessDeserializeSpec Scope A img))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hstk : pollMinStk addrStk getStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr sessLoadPollName)
      (sessLoadPollSpec rd pathOk Scope A img stk) :=
  sessLoadPoll_ok_ext hC hAddr hGet (subroutine_ok_sessDeserializeExtSpec_of_spec hDeser) hFs hstk

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
