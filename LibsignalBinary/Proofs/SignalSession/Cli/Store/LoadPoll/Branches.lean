/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.LoadPoll.Layout
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

theorem sepWPp_of_sepWP_final {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWP prog ret s P Q) : SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_ret h

theorem sepWPp_name_state {prog : Program} {ret : BitVec 64} {s : State}
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (k : ∀ s' : State, s' = s → SepWPp prog ret s' P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  k s rfl

theorem getResultAt_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0x1e0#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
        ((sp - 0x1d8#64) ↦₆₄ cap) ∗
        ((sp - 0x1d0#64) ↦₆₄ ptr) ∗
        ((sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x1c0#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0x1e0#64 + 8#64 = sp - 0x1d8#64 := by bv_omega
  have e2 : sp - 0x1e0#64 + 0x20#64 = sp - 0x1c0#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0x1d8#64) bs (sp - 0x1d0#64) (sp - 0x1c8#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

theorem lpoll_post_entails (rd : ReadRule) (pathOk : List (BitVec 8) → Prop)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (A : RustAlloc) (img : Obj.Image)
    (stk : Nat) (x : SessLoadPollGhost) (s0 sf : State)
    (gr : Except Unit (List (BitVec 8)))
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (hgr : gr = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧ sf.trace = s0.trace)
    (hans : SessLoadAns Scope gr ans) :
    (sessLoadOutAt A x.call.out ans ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk) ⊢
      (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf := by
  simp only [sessLoadPollSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_right gr
    (Entails.sepExists_right ans (Entails.pure_right ⟨hgr, hans⟩ (Entails.refl _)))

theorem finish_common_reassemble (A : RustAlloc) (s0 : State) (x : SessLoadPollGhost)
    {addrStk getStk stk : Nat} (hstk : pollMinStk addrStk getStk ≤ stk) (hstk_hi : stk ≤ 2 ^ 64)
    (ans : Except Unit (Option (SessionRecord (List (BitVec 8)))))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128) :
    (sessLoadOutAt A x.call.out ans ∗
      memRegion (s0.sp - 0x1e0#64) 368 ∗
      memRegion (s0.sp - 0x348#64) 312 ∗
      (((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
      ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
      ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
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
      A.pool) ⊢
    sessLoadOutAt A x.call.out ans ∗
      sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
      protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool ∗ stackAt s0.sp stk := by
  have h24 := header3_entails_memRegion24 (s0.sp - 0x1f8#64) (s0.sp - 0x1f0#64) (s0.sp - 0x1e8#64)
    nameCap namePtr (BitVec.ofNat 64 nameBs.length) (by bv_omega) (by bv_omega)
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24)))) ?_
  have hrstk := restore_pollStack s0 hstk hstk_hi c_sp0 q140
  have hgroup :
      (sessLoadOutAt A x.call.out ans ∗
        memRegion (s0.sp - 0x1e0#64) 368 ∗
        memRegion (s0.sp - 0x348#64) 312 ∗
        memRegion (s0.sp - 0x1f8#64) 24 ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
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
        A.pool) =
      ((sessLoadOutAt A x.call.out ans ∗
          sessLoadBoxAt x.call.fut x.self x.call.addrA 1#8 ∗ dirAt A x.self x.dir ∗
          protocolAddressAt A x.call.addr x.call.addrA ∗ A.pool) ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
          memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
            (subMax addrStk getStk - extHookStack) ∗
          stackAt (s0.sp - 0x350#64) extHookStack ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          memRegion (s0.sp - 0x348#64) 312 ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
          memRegion (s0.sp - 0x200#64) 8 ∗
          memRegion (s0.sp - 0x1f8#64) 24 ∗
          memRegion (s0.sp - 0x1e0#64) 368 ∗
          memRegion (s0.sp - 0x070#64) 16 ∗
          savedCalleeSlots s0)) := by
    ac_rfl
  rw [hgroup]
  refine Entails.trans (sepConj_mono_right hrstk) ?_
  exact Entails.of_eq (by ac_rfl)

/-- Shared post-`Dir::get` spatial state before inspecting `gr`. -/
def postGetCommon (A : RustAlloc) (s0 : State) (x : SessLoadPollGhost)
    (addrStk getStk stk : Nat)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128) : SepProp :=
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
  stackAt (s0.sp - 0x350#64) (subMax addrStk getStk) ∗
  memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
  memRegion x.call.out 368 ∗
  sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
  dirAt A x.self x.dir ∗
  protocolAddressAt A x.call.addr x.call.addrA ∗
  A.pool

/-- Branch 1 (`+0x054` on `gr = .error ()`): moves `InvalidState("read", _)` to `out + 8`, frees
`name` if needed, and returns `.error ()`. -/
theorem lpoll_branch_err {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.error () = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
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
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0x1e0#64) (.error ()) ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hne : (speWord 1 + 2#64 == 0#64) = false := speWord_one_add_two_ne_zero
  have hep := lpoll_epilogue_e4 hC
  have hdn := lpoll_drop_name_d8 hC
  clear hC
  have hfn : libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    sessLoadPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    84 132
  dsimp only [tripleRatchetProgAtExt] at hep hdn hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    sessLoadPollName = fnBase
  examples_hide_fetches
  unfold postGetCommon
  change SepWP _ _ _ (speAt A (utf8 "read") (s0.sp - 0x1e0#64) .invalidState ∗ _) _
  rw [speAt_read_invalidState_unpack A s0.sp, subStack_split s0.sp hext_le hmin_hi]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun errBs => SepWP.exists_elim fun errCap =>
    SepWP.exists_elim fun errPtr => SepWP.exists_elim fun fnPtr => ?_
  rw [ProofLib.memRegion_eq_exists_bytes (s0.sp - 0x348#64) 312 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun bs312 => ?_
  refine SepWP.weaken_pre
    (by sep_focus :
      _ ⊢
      ⌜bs312.length = 312⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
        (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
          if errCap = 0#64 then emp
          else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
            memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
        (fnPtr ↦ᵣ utf8 "read") ∗
        memRegion (s0.sp - 0x1b0#64) 320 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) ?_
  refine SepWP.pure_elim fun hbs312 => ?_
  let F_err : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
    ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
    (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
      if errCap = 0#64 then emp
      else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
        memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
    (fnPtr ↦ᵣ utf8 "read") ∗
    memRegion (s0.sp - 0x1b0#64) 320 ∗
    ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
    ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
    ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
    ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
    memRegion (s0.sp - 0x200#64) 8 ∗
    memRegion (s0.sp - 0x070#64) 16 ∗
    memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
      (subMax addrStk getStk - extHookStack) ∗
    memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
    dirAt A x.self x.dir ∗
    protocolAddressAt A x.call.addr x.call.addrA
  have hdone : ∀ (sf : State) (P_f : SepProp),
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x 0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr
        (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 ∗
        A.pool ∗ F_err) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hgr_f :
        Except.error () = x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
          sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails rd pathOk Scope A img stk x s0 sf (.error ()) (.error ()) hgr_f rfl)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.error ()) nameCap namePtr nameBs c_sp0
        (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr))
    have hreasm :=
      speAt_read_invalidState_reassemble A s0.sp x.call.out errBs errCap errPtr fnPtr bs312 hbs312
    have h312 : ((s0.sp - 0x348#64) ↦ₛ bs312) ⊢ memRegion (s0.sp - 0x348#64) 312 :=
      hbs312 ▸ pointsToBytes_entails_memRegion (s0.sp - 0x348#64) bs312
    have hgrp :
        epilogueOut s0 x 0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr
          (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 ∗
          A.pool ∗ F_err =
        (((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFE#64) ∗
          ((x.call.out + 8#64) ↦₆₄ speWord 1) ∗
          ((x.call.out + 0x10#64) ↦₆₄ errCap) ∗ ((x.call.out + 0x18#64) ↦₆₄ errPtr) ∗
          ((x.call.out + 0x20#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((x.call.out + 0x28#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
          ((x.call.out + 0x38#64) ↦ₛ bs312) ∗
          (⌜errBs.length ≤ errCap.toNat ∧ errCap.toNat < 2 ^ 63 ∧ errPtr ≠ 0#64⌝ ∗
            if errCap = 0#64 then emp
            else A.live errPtr errCap.toNat 1 ∗ (errPtr ↦ₛ errBs) ∗
              memRegion (errPtr + BitVec.ofNat 64 errBs.length) (errCap.toNat - errBs.length)) ∗
          (fnPtr ↦ᵣ utf8 "read") ∗
          ((s0.sp - 0x1e0#64) ↦₆₄ speWord 1) ∗
          ((s0.sp - 0x1d8#64) ↦₆₄ errCap) ∗ ((s0.sp - 0x1d0#64) ↦₆₄ errPtr) ∗
          ((s0.sp - 0x1c8#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
          ((s0.sp - 0x1c0#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
          memRegion (s0.sp - 0x1b0#64) 320) ∗
        (((s0.sp - 0x348#64) ↦ₛ bs312) ∗
          ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
            ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
            ((s0.sp - 0x210#64) ↦₁₂₈ (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr)) ∗
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
            A.pool))) := by
      unfold epilogueOut F_err; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hreasm (sepConj_mono_left h312)) ?_
    exact Entails.of_eq (by ac_rfl)
  unfold Arm64.pointsTo128
  simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (228)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_e4
    refine hep x s0 _
      0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 _ (A.pool ∗ F_err)
      hbs312
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hinv_e4
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by
        unfold epiloguePre F_err Arm64.pointsTo128
        simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    apply SepWP.seq_inImage (mid := fnBase + bv% (216)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_d8
    refine hdn x s0 _ nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFE#64 (speWord 1) errCap errPtr (BitVec.ofNat 64 errBs.length)
      (BitVec.ofNat 64 (utf8 "read").length ++ fnPtr) bs312 _ F_err
      hncap hnlen hnlt hnptr hbs312
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      hinv_d8
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
      (by
        unfold epiloguePre F_err Arm64.pointsTo128
        simp only [extractLsb_0_64_append, extractLsb_64_64_append, sepConj_assoc]
        sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

/-- Branch 2 (`+0x054` on `gr = .ok []`): frees `bytes` and `name` if needed, writes `-1` to
`[out]`, and returns `.ok none`. -/
theorem lpoll_branch_ok_nil {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {addrStk getStk stk : Nat}
    (hC : AllocContractsX img A ext)
    (x : SessLoadPollGhost) (R : SepProp) (s0 sm2 : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (c_sp0 : BitVec 64) (q140 : BitVec 128)
    (hstk : pollMinStk addrStk getStk ≤ stk)
    (hstk_hi : stk ≤ 2 ^ 64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (hnptr : namePtr ≠ 0#64)
    (hgr : Except.ok ([] : List (BitVec 8)) =
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
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 Reg.lr) sm2
      (getResultAt A (s0.sp - 0x1e0#64) (.ok []) ∗
        postGetCommon A s0 x addrStk getStk stk nameCap namePtr nameBs c_sp0 q140)
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) := by
  have hsp_al : sm2.spAligned = true := spAligned_sub_350 hsp_align hsp
  have hmin_hi : pollMinStk addrStk getStk ≤ 2 ^ 64 := le_trans hstk hstk_hi
  have hext_le : extHookStack ≤ subMax addrStk getStk := by unfold subMax; omega
  have hok_tag : (okTagVec + 2#64 == 0#64) = true := okTagVec_add_two_eq_zero
  have hf14c := lpoll_finish_14c hC
  have hdb13c := lpoll_drop_bytes_13c hC
  clear hC
  have hfn : libsignalSessionCode.fnOff sessLoadPollName =
      num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}") :=
    sessLoadPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    84 20
  code_fetches_from CryptoVerification.libsignalSessionCode cliLoadPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::SessionFiles as libsignal_protocol::storage::traits::SessionStore>::load_session::{closure#0}"))
    304 12
  dsimp only [tripleRatchetProgAtExt] at hf14c hdb13c hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    sessLoadPollName = fnBase
  examples_hide_fetches
  unfold postGetCommon
  rw [getResultAt_ok_unpack A s0.sp [], subStack_split s0.sp hext_le hmin_hi]
  simp only [List.length_nil, sepExists_sepConj_left, sepConj_assoc]
  refine SepWP.exists_elim fun bytesCap => SepWP.exists_elim fun bytesPtr =>
    SepWP.pure_elim fun ⟨_hblen, hblt, hbptr⟩ => ?_
  rw [ProofLib.memRegion_eq_exists_bytes (s0.sp - 0x348#64) 312 (by decide)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun bs312 => ?_
  refine SepWP.weaken_pre
    (by sep_focus :
      _ ⊢
      ⌜bs312.length = 312⌝ ∗
        ((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
        ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
        ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
        ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
        SpqrV1.ChainProofs.bytesAt false bytesPtr [] ∗
        vecU8Tail A bytesCap bytesPtr [] ∗
        memRegion (s0.sp - 0x1c0#64) 16 ∗
        memRegion (s0.sp - 0x1b0#64) 320 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
        memRegion (s0.sp - 0x200#64) 8 ∗
        memRegion (s0.sp - 0x070#64) 16 ∗
        savedCalleeSlots s0 ∗
        memRegion (s0.sp - 0x350#64 - BitVec.ofNat 64 (subMax addrStk getStk))
          (subMax addrStk getStk - extHookStack) ∗
        stackAt (s0.sp - 0x350#64) extHookStack ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - pollMinStk addrStk getStk) ∗
        memRegion x.call.out 368 ∗
        sessLoadBoxAt x.call.fut x.self x.call.addrA 0#8 ∗
        dirAt A x.self x.dir ∗
        protocolAddressAt A x.call.addr x.call.addrA ∗
        A.pool) ?_
  refine SepWP.pure_elim fun hbs312 => ?_
  let F_nil : SepProp :=
    ((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗
    ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
    ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗
    ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
    memRegion (s0.sp - 0x1c0#64) 16 ∗
    memRegion (s0.sp - 0x1b0#64) 320 ∗
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
      sf.trace = sm2.trace → sf.sp = s0.sp → CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x 0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
        q140 bs312 ∗
        ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
        ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗ A.pool ∗ F_nil) →
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (sessLoadPollSpec rd pathOk Scope A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf := by
    intro sf P_f htr_eq hsp_f hcs_f hPf
    have hgr_f :
        Except.ok ([] : List (BitVec 8)) =
            x.dir.get rd s0.fs.files (addressText x.call.addr.val) ∧
          sf.trace = s0.trace :=
      ⟨hgr.1, htr_eq.trans hgr.2⟩
    refine ⟨fun hmf => Satisfies.mono (sepConj_mono_left ?_) hmf, hsp_f, hcs_f⟩
    refine Entails.trans hPf ?_
    refine Entails.trans ?_
      (lpoll_post_entails rd pathOk Scope A img stk x s0 sf (.ok []) (.ok none) hgr_f rfl)
    refine Entails.trans ?_
      (finish_common_reassemble A s0 x hstk hstk_hi (.ok none) nameCap namePtr nameBs c_sp0 q140)
    have hnone :=
      sessLoadOutAt_none_reassemble A x.call.out okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
        q140 bs312 hbs312
    have hslot := slot170_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
    have h312 : ((s0.sp - 0x348#64) ↦ₛ bs312) ⊢ memRegion (s0.sp - 0x348#64) 312 :=
      hbs312 ▸ pointsToBytes_entails_memRegion (s0.sp - 0x348#64) bs312
    have hgrp :
        epilogueOut s0 x 0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
          q140 bs312 ∗
          ((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗ A.pool ∗ F_nil =
        (((x.call.out ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
          ((x.call.out + 8#64) ↦₆₄ okTagVec) ∗ ((x.call.out + 0x10#64) ↦₆₄ c_sp0) ∗
          ((x.call.out + 0x18#64) ↦₆₄ (s0.sp - 0x210#64)) ∗ ((x.call.out + 0x20#64) ↦₆₄ 0#64) ∗
          ((x.call.out + 0x28#64) ↦₁₂₈ q140) ∗ ((x.call.out + 0x38#64) ↦ₛ bs312)) ∗
        (((s0.sp - 0x1e0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0x1d8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0x1d0#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x1c8#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x1c0#64) 16 ∗ memRegion (s0.sp - 0x1b0#64) 320) ∗
        ((s0.sp - 0x348#64) ↦ₛ bs312) ∗
        ((((s0.sp - 0x1f8#64) ↦₆₄ nameCap) ∗
            ((s0.sp - 0x1f0#64) ↦₆₄ namePtr) ∗
            ((s0.sp - 0x1e8#64) ↦₆₄ BitVec.ofNat 64 nameBs.length)) ∗
          ((s0.sp - 0x350#64) ↦₆₄ c_sp0) ∗
          ((s0.sp - 0x210#64) ↦₁₂₈ q140) ∗
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
      unfold epilogueOut F_nil; ac_rfl
    rw [hgrp]
    refine Entails.trans (sepConj_mono hnone (sepConj_mono hslot (sepConj_mono_left h312))) ?_
    exact Entails.of_eq (by ac_rfl)
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.fold (vecU8_free_zero A bytesPtr (bs := []) (Nat.zero_le _)) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (332)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_14c
    refine hf14c x s0 _ nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
      q140 bs312 _ F_nil
      hnlen hnlt hnptr hbs312
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
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf
  · have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    apply SepWP.seq_inImage (mid := fnBase + bv% (316)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_13c
    refine hdb13c x s0 _ bytesCap bytesPtr [] nameCap namePtr nameBs
      0xFFFFFFFFFFFFFFFF#64 okTagVec c_sp0 (s0.sp - 0x210#64) 0#64
      q140 bs312 _ F_nil
      hbcap (Nat.zero_le _) hblt hbptr hnlen hnlt hnptr hbs312
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
      (by unfold epiloguePre F_nil; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hdone sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f hPf

end CryptoVerification.SignalSession.Cli.Store.LoadPoll.Helpers
