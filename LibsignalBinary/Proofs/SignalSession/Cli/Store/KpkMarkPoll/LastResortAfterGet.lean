/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Drops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoop
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli
open CryptoVerification.SpqrV1.Varint

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

theorem vecU8_unpack_at (A : RustAlloc) (v : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A v bs = (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64, vecU8At A v cap ptr bs) := rfl

theorem vecU8At_unpack_any (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (if cap = 0#64 then emp
         else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
           memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, sepConj_assoc]
  ac_rfl

theorem vecU8At_of_live_parts (A : RustAlloc) (v v8 v16 cap ptr : BitVec 64)
    (bs : List (BitVec 8))
    (hv8 : v + 8#64 = v8) (hv16 : v + 16#64 = v16)
    (hlen : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hptr : ptr ≠ 0#64) :
    ((v ↦₆₄ cap) ∗ (v8 ↦₆₄ ptr) ∗ (v16 ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (if cap = 0#64 then emp
       else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))) ⊢
      vecU8At A v cap ptr bs := by
  subst hv8; subst hv16
  rw [vecU8At_unpack_any A v cap ptr bs]
  exact Entails.pure_right ⟨hlen, hlt, hptr⟩ (Entails.refl _)

theorem vecU8At_unpack_pos_lr (A : RustAlloc) (v cap ptr : BitVec 64)
    (bs : List (BitVec 8)) (hc : cap ≠ 0#64) :
    vecU8At A v cap ptr bs =
      (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        (v ↦₆₄ cap) ∗ ((v + 8#64) ↦₆₄ ptr) ∗ ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by
  unfold vecU8At vecHeader
  have hzero : (0 : BitVec 64) = 0#64 := rfl
  simp only [hzero, hc, ite_false, sepConj_assoc]
  ac_rfl

theorem assemble_baseKeysName (filePtr wDot : BitVec 64) (id : BitVec 32)
    (hwDot : unpack64 wDot = utf8 ".base-ke") :
    ((filePtr ↦ₛ keyName id) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length) ↦₆₄ wDot) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length + 8#64) ↦₁₆ 0x7379#16)) =
    SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName id) := by
  rw [pointsTo64_eq_pointsToBytes, hwDot, pointsTo16_ys_eq_bytes]
  have h1 : (filePtr ↦ₛ keyName id) ∗
      ((filePtr + BitVec.ofNat 64 (keyName id).length) ↦ₛ utf8 ".base-ke") =
      (filePtr ↦ₛ (keyName id ++ utf8 ".base-ke")) :=
    (pointsToBytes_append filePtr (keyName id) (utf8 ".base-ke")).symm
  rw [← sepConj_assoc, h1]
  have had : filePtr + BitVec.ofNat 64 (keyName id).length + 8#64 =
      filePtr + BitVec.ofNat 64 (keyName id ++ utf8 ".base-ke").length := by
    rw [List.length_append, utf8_dot_base_ke_length, BitVec.ofNat_add]; bv_omega
  rw [had, ← pointsToBytes_append, baseKeysName_eq_append]
  rfl

theorem subStack_merge_adj (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (R : SepProp) :
    memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
      (kpkSubMax decStk getStk putStk - k) ∗
      (stackAt (sp0 - 0xf0#64) k ∗ R) =
    stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

theorem subStack_merge_rev_adj (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (R : SepProp) :
    stackAt (sp0 - 0xf0#64) k ∗
      (memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - k) ∗ R) =
    stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

theorem subStack_merge_pool_mid (sp0 : BitVec 64) {k decStk getStk putStk : Nat}
    (hk : k ≤ kpkSubMax decStk getStk putStk)
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64) (X Pool R : SepProp) :
    (X ∗ stackAt (sp0 - 0xf0#64) k ∗ Pool) ∗
      (memRegion (sp0 - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - k) ∗ R) =
    X ∗ Pool ∗ stackAt (sp0 - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ R := by
  have hs := (subStack_split sp0 hk hhi).symm
  rw [← hs]
  ac_rfl

/-! ## Post-`last_resort.get` Continuation (`+372 ..`, `kpk_after_lr_get_174`) -/

set_option maxHeartbeats 1200000 in
/-- Steps from `+372` right after `last_resort.get` returns `gr`:
- `gr = .error ()`: steps `+372 .. +384` to `kpk_read_err_278` (`+632`);
- `gr = .ok seenBs`: runs `PublicKey::serialize`, `concat`, frees `serPtr`, checks `seen.len % 37`,
  and dispatches to `kpk_malformed_2a4` (`+676`), `kpk_append_37c` (`+892`), or
  `kpk_bcmp_loop_20c` (`+524`). -/
theorem kpk_after_lr_get_174 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (x : KpkMarkPollGhost) (s0 s4 : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 filePtr fileCap : BitVec 64) (tmp32 : BitVec 32)
    (gr : Except Unit (List (BitVec 8)))
    {Q Qp : State → SepProp → Prop}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hgr : gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace)
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hpc : s4.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (372))
    (hrun : s4.status = .Running)
    (hsp : s4.sp = s0.sp - 0xf0#64)
    (hfp : s4.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s4)
    (hvregs : calleeSavedVRegs s4 = calleeSavedVRegs s0)
    (hx19 : s4.readReg64 .x19 = x.fut)
    (hx20 : s4.readReg64 .x20 = x.out)
    (hx24 : s4.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length)
    (hx26 : s4.readReg64 .x26 = x.self)
    (hx28 : s4.readReg64 .x28 = x.signedId.setWidth 64)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s4
      (getResultAt A (s0.sp - 0xb0#64) gr ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool)
      Q Qp := by
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hser_le : publicKeySerializeStackX ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX publicKeySerializeStackX; omega
  have hcat_le : 96 + extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hsp_al : s4.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hser := public_key_serialize_ok_ext_x hC
  rw [← publicKeySerialize_fnAddr_eq] at hser
  have hcat := kpkConcat2_pos_ok hC (96 + extHookStack) (Nat.le_refl _)
    (le_trans hcat_le (by unfold kpkMinStk at hhi; omega))
  rw [← cliConcat_fnAddr_eq] at hcat
  have hdealloc := kpk_dealloc_ok_at hC
  have herr278 := @kpk_read_err_278 img A ext hC
  have hmal := @kpk_malformed_2a4 img A ext hb hC
  have happend := @kpk_append_37c img A ext decStk getStk putStk hC hPut
  have hloop := @kpk_bcmp_loop_20c img A ext rd decStk getStk putStk hb hC hBcmp hPut
  clear hC hBcmp hPut
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    372 140
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hser hcat hdealloc herr278 hmal happend hloop hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  rcases gr with ⟨⟩ | seenBs
  · have hne : (speWord 1 + 2#64 != 0#64) = true := rfl
    change SepWPp _ _ _ (speAt A (utf8 "read") (s0.sp - 0xb0#64) .invalidState ∗ _) _ _
    rw [speAt_read_invalidState_eq_words A (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
          (s0.sp - 0xa0#64) (s0.sp - 0x98#64) (s0.sp - 0x90#64) (s0.sp - 0x88#64)
          (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega),
        subStack_split s0.sp hext_le hhi]
    kpk_sep_norm
    refine SepWPp.exists_elim fun errBs => SepWPp.exists_elim fun errCap =>
      SepWPp.exists_elim fun errPtr => SepWPp.exists_elim fun fnPtr => ?_
    apply SepWPp.of_sepWP_ret
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (632)) hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_278
    refine herr278 x s0 _ fileCap filePtr (baseKeysName x.id)
      errBs errCap errPtr fnPtr _
      (kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ errPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
      hf_len hf_lt hf_ptr
      (by kpk_norm) (by kpk_norm) hsp_align (by kpk_norm) hinv_278
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by unfold epiloguePre; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk_final sf P_f hsp_f hcs_f <| by
          have htr_eq : sf.trace = s4.trace := htr_f.trans (by kpk_norm)
          have hres_eq :
              ((.readErr : KpkMarkAns), x.kg) =
                  kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
                sf.trace = s0.trace := by
            rcases hgr with ⟨hget2_err, hs4_tr⟩
            refine ⟨?_, htr_eq.trans hs4_tr⟩
            unfold kpkMarkOf
            rw [hget1, ← hget2_err]
          refine Entails.trans hPf ?_
          have hb0 := slot_b0_err_collapse s0.sp (speWord 1) errCap errPtr
            (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length)
            (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
            (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8)
          refine Entails.trans ?_
            (kpkMark_final_ext (pathOk := pathOk) hstk hhi_stk x s0 sf wDot wR0 wR7 wM0 wM6
              f0 f1 filePtr fileCap tmp32 (.readErr, x.kg) hres_eq)
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_left hb0)))))))))))))))))
          sep_focus
  · rcases hgr with ⟨hget2_symm, hs4_tr⟩
    have hget2 : x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs :=
      hget2_symm.symm
    have heq0 : (okTagVec + 2#64 != 0#64) = false := rfl
    rw [getResultAt_b0_ok_unpack A s0.sp seenBs,
        ProofLib.memRegion_split' (b := s0.sp - 0xc8#64) (n := 8) (k := 16)
          (b' := s0.sp - 0xc0#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := s0.sp - 0xc0#64) (n := 8) (k := 8)
          (b' := s0.sp - 0xb8#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (s0.sp - 0xc8#64),
        ProofLib.memRegion_eight (s0.sp - 0xc0#64),
        ProofLib.memRegion_eight (s0.sp - 0xb8#64)]
    unfold epiloguePre kpkMarkBoxAt
    kpk_sep_norm
    refine SepWPp.exists_elim fun seenCap => SepWPp.exists_elim fun seenPtr =>
      SepWPp.exists_elim fun c8_0 => SepWPp.exists_elim fun c0_0 =>
      SepWPp.exists_elim fun b8_0 => ?_
    refine SepWPp.pure_elim fun ⟨hs_len, hs_lt, hs_ptr⟩ => ?_
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase - bv% (ls_rel%
        "<libsignal_core::curve::PublicKey>::serialize"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")) hinv
    wp_steps
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hinv_ser
    apply bind_sepWPp_state_mark; intro st_ser
    have hsp_ser : st_ser.sp = s0.sp - 0xf0#64 := by dsimp only [st_ser]; (try kpk_norm)
    dsimp only [st_ser] at *
    refine kpk_call_serialize hser ⟨x.baseKeyA, x.baseKey⟩
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - publicKeySerializeStackX) ∗
        ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ seenPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x)
      (ret_pc := fnBase + bv% (408))
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_ser)
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs4_tr)))
      hinv_ser
      (by kpk_norm)
      hpan
      (by
        rw [hsp_ser, subStack_split s0.sp hser_le hhi]
        unfold epiloguePre kpkMarkBoxAt
        kpk_sep_norm
        sep_focus)
      fun s5 hpc5 hrun5 hsp5 hcs5 hinv5 hser_ne0 hser_33 htr5 => ?_
    have hs5_sp : s5.sp = s0.sp - 0xf0#64 := hsp5.trans hsp_ser
    have hs5_fp : s5.readReg64 .x29 = s0.sp - 0x60#64 := by rw [(cs_x29 hcs5)]; kpk_norm
    have hs5_al : s5.spAligned = true := spAligned_sub_f0 hsp_align hs5_sp
    have hs5_tr : s5.trace = s0.trace := by
      rw [htr5]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs4_tr))
    kpk_sep_norm
    rw [hsp_ser, subStack_merge_rev_adj s0.sp hser_le hhi,
        pointsTo32_eq_le32 (s0.sp - 0x64#64) x.signedId]
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#3]")) hinv5
    wp_steps
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hinv_cat
    apply bind_sepWPp_state_mark; intro st_cat
    have hsp_cat : st_cat.sp = s0.sp - 0xf0#64 := by dsimp only [st_cat]; (try kpk_norm)
    dsimp only [st_cat] at *
    refine kpk_call_concat2 hcat
      ⟨s0.sp - 0x80#64, s0.sp - 0xb0#64, s0.sp - 0x64#64, le32 x.signedId,
        s5.readReg64 .x0, x.baseKey.serialize⟩
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
        A.live (s5.readReg64 .x0) 33 1 ∗
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x)
      (ret_pc := fnBase + bv% (448))
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_cat)
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs5_tr)))
      hinv_cat
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      (by rw [le32_length]; decide)
      (by rw [publicKey_serialize_length]; decide)
      (by rw [le32_length, publicKey_serialize_length]; decide)
      hpan
      (by
        rw [hsp_cat, subStack_split s0.sp hcat_le hhi, le32_length,
            publicKey_serialize_length x.baseKey]
        have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
        have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
        have e_98 : s0.sp - 0xb0#64 + 24#64 = s0.sp - 0x98#64 := by bv_omega
        rw [e_a8, e_a0, e_98]
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun s6 hpc6 hrun6 hsp6 hcs6 hinv6 htr6 => ?_
    have hs6_sp : s6.sp = s0.sp - 0xf0#64 := hsp6.trans hsp_cat
    have hs6_al : s6.spAligned = true := spAligned_sub_f0 hsp_align hs6_sp
    have hs6_tr : s6.trace = s0.trace := by
      rw [htr6]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs5_tr))
    have hs6_21 : s6.readReg64 .x21 = 33#64 := by rw [(cs_x21 hcs6)]; kpk_norm
    have hs6_23 : s6.readReg64 .x23 = s5.readReg64 .x0 := by rw [(cs_x23 hcs6)]; kpk_norm
    obtain ⟨hpos33, hpow33, hhi33⟩ : LayoutOk 33 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
    have hfold_b0 :
        (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length)) ⊢
        (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xa8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length)) := by
      have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
      have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
      have e_98 : s0.sp - 0xb0#64 + 24#64 = s0.sp - 0x98#64 := by bv_omega
      rw [e_a8, e_a0, e_98]
      exact Entails.refl _
    have hser_mem : ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ⊢ memRegion (s5.readReg64 .x0) 33 := by
      have hl := publicKey_serialize_length x.baseKey
      exact hl ▸ pointsToBytes_entails_memRegion (s5.readReg64 .x0) x.baseKey.serialize
    rw [hsp_cat, ← pointsTo32_eq_le32 (s0.sp - 0x64#64) x.signedId]
    have hprep_448 :
        ((vecU8 A (s0.sp - 0x80#64) (le32 x.signedId ++ x.baseKey.serialize) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
          ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
          ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
          ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
          ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
          ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
          A.pool ∗ stackAt (s0.sp - 0xf0#64) (96 + extHookStack)) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
        A.live (s5.readReg64 .x0) 33 1 ∗
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        memRegion (s0.sp - 0x90#64) 16 ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x) ⊢
        A.live (s5.readReg64 .x0) 33 1 ∗ memRegion (s5.readReg64 .x0) 33 ∗
        vecU8 A (s0.sp - 0x80#64) (baseKeyEntry x.signedId x.baseKey) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool := by
      have hsub96 :
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
            stackAt (s0.sp - 0xf0#64) (96 + extHookStack) =
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - extHookStack) ∗
            stackAt (s0.sp - 0xf0#64) extHookStack := by
        rw [← subStack_split s0.sp hcat_le hhi, subStack_split s0.sp hext_le hhi]
      have hb0_col := Entails.trans (sepConj_mono_left hfold_b0)
        (by
          simpa only [sepConj_assoc] using
            slot_b0_ok_collapse s0.sp (s0.sp - 0x64#64)
              (BitVec.ofNat 64 (le32 x.signedId).length)
              (s5.readReg64 .x0)
              (BitVec.ofNat 64 x.baseKey.serialize.length))
      kpk_sep_norm
      change (vecU8 A (s0.sp - 0x80#64) (baseKeyEntry x.signedId x.baseKey) ∗ _) ⊢ _
      have h1 :
          (((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
            ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
            ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
            ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
            memRegion (s0.sp - 0x90#64) 16) ⊢ memRegion (s0.sp - 0xb0#64) 48 := by
        simpa only [sepConj_assoc] using hb0_col
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono hser_mem (Entails.refl _)))
      have hswap :
          (vecU8 A (s0.sp - 0x80#64) (baseKeyEntry x.signedId x.baseKey) ∗
            ((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
            ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
            ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
            ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
            A.pool ∗ stackAt (s0.sp - 0xf0#64) (96 + extHookStack) ∗
            memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
              (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
            A.live (s5.readReg64 .x0) 33 1 ∗
            SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
            vecU8Tail A seenCap seenPtr seenBs ∗
            memRegion (s0.sp - 0x90#64) 16 ∗
            kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
            ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
            ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
            ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
            vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
            dirAt A x.self x.kg.oneTime ∗
            dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            epiloguePre s0 x) =
          ((((s0.sp - 0xb0#64) ↦₆₄ (s0.sp - 0x64#64)) ∗
              ((s0.sp - 0xb0#64 + 8#64) ↦₆₄ BitVec.ofNat 64 (le32 x.signedId).length) ∗
              ((s0.sp - 0xb0#64 + 16#64) ↦₆₄ s5.readReg64 .x0) ∗
              ((s0.sp - 0xb0#64 + 24#64) ↦₆₄ BitVec.ofNat 64 x.baseKey.serialize.length) ∗
              memRegion (s0.sp - 0x90#64) 16) ∗
            (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                (kpkSubMax decStk getStk putStk - (96 + extHookStack)) ∗
              stackAt (s0.sp - 0xf0#64) (96 + extHookStack)) ∗
            A.live (s5.readReg64 .x0) 33 1 ∗ ((s5.readReg64 .x0) ↦ₛ x.baseKey.serialize) ∗
            vecU8 A (s0.sp - 0x80#64) (baseKeyEntry x.signedId x.baseKey) ∗
            kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
            ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
            ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
            ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
            vecU8Tail A seenCap seenPtr seenBs ∗
            SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
            vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
            dirAt A x.self x.kg.oneTime ∗
            dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
            epiloguePre s0 x ∗ A.pool) := by
        ac_rfl
      rw [hswap, hsub96]
      refine Entails.trans (sepConj_mono_left h1) ?_
      kpk_sep_norm
      sep_focus
    refine sepWPp_conseq hprep_448 ?_
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase + bv% (468)) hinv6
    have h21_f : (s6.readReg64 .x21 == 0#64) = false := by rw [hs6_21]; rfl
    have h33_ne0 : (33#64 == 0#64) = false := rfl
    apply SepWP.seq_inImage
      (mid := fnBase +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_dealloc"))
      hinv6
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_da
    have ⟨hF_da, hsym_da⟩ := hinv_da
    rw [← hs6_sp]
    wp_call hdealloc (s5.readReg64 .x0, 33, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_468
    apply bind_sepWPp_state_mark; intro s7
    let usedBs := baseKeyEntry x.signedId x.baseKey
    have hused37 : usedBs.length = 37 := baseKeyEntry_length x.signedId x.baseKey
    rw [vecU8_eq_bytes_tail A (s0.sp - 0x80#64) usedBs (s0.sp - 0x78#64) (s0.sp - 0x70#64)
          (by bv_omega) (by bv_omega)]
    kpk_sep_norm
    refine SepWPp.exists_elim fun usedCap => SepWPp.exists_elim fun usedPtr => ?_
    rw [show ∀ (A1 A2 : SepProp) (P0 : Prop) (Rest : SepProp),
          A1 ∗ A2 ∗ ⌜P0⌝ ∗ Rest = ⌜P0⌝ ∗ A1 ∗ A2 ∗ Rest from fun _ _ _ _ => by ac_rfl]
    refine SepWPp.pure_elim fun ⟨hu_len, hu_lt, hu_ptr⟩ => ?_
    rw [hs6_sp, hs5_sp]
    have hs7_pc : s7.pc = fnBase + bv% (468) := by
      (try dsimp only [s7]); kpk_norm
    have hs7_run : s7.status = .Running := by
      (try dsimp only [s7]); kpk_norm
    have hs7_sp : s7.sp = s0.sp - 0xf0#64 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs6_sp))
    have hs7_fp : s7.readReg64 .x29 = s0.sp - 0x60#64 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs5)]; kpk_norm)
    have hs7_22 : s7.readReg64 .x22 = BitVec.ofNat 64 seenBs.length := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcs5)]; kpk_norm)
    have hs7_24 : s7.readReg64 .x24 = BitVec.ofNat 64 (baseKeysName x.id).length := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcs5)]; kpk_norm)
    have hs7_25 : s7.readReg64 .x25 = seenPtr := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x25 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x25 hcs5)]; kpk_norm)
    have hs7_26 : s7.readReg64 .x26 = x.self := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs5)]; kpk_norm)
    have hs7_27 : s7.readReg64 .x27 = seenCap := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcs5)]; kpk_norm)
    have hs7_19 : s7.readReg64 .x19 = x.fut := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs5)]; kpk_norm)
    have hs7_20 : s7.readReg64 .x20 = x.out := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs5)]; kpk_norm)
    have hs7_v : calleeSavedVRegs s7 = calleeSavedVRegs s0 := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs6)])
      (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs5)]; kpk_norm)
    have hs7_tr : s7.trace = s0.trace := by
      (try dsimp only [s7]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs6_tr))
    have hs7_al : s7.spAligned = true :=
      spAligned_sub_f0 hsp_align hs7_sp
    have hinv_s7 : ImgCallInv img s7 := hinv_468
    clear_value s7
    rw [hused37]
    have h37_ne0 : (37#64 == 0#64) = false := rfl
    by_cases hmod : seenBs.length % 37 ≠ 0
    · have hrem_ne := udiv_msub_37_beq_zero_false (by omega : seenBs.length < 2 ^ 64) hmod
      have hans_m : (KpkMarkAns.malformed, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        simp [usedBs, hused37, hmod]
      unfold kpkMarkRoBundle
      kpk_sep_norm
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (676)) hinv_s7
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_2a4
      refine hmal x s0 _ wM0 wM6
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (((dotBaseKeAddr img.base) ↦₆₄ᵣ wDot) ∗
          ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗ ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm) (by kpk_norm) hsp_align
        (by kpk_norm) (by kpk_norm) (by kpk_norm) hinv_2a4
        (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        hpan
        (by
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_m P_m htr_m hsp_m hcs_m hPm =>
          hk_final sf_m P_m hsp_m hcs_m <| by
            refine Entails.trans hPm ?_
            have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
              (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
              (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
            have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
              (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
              (by bv_omega) (by bv_omega)
            refine Entails.trans ?_
              (kpkMark_final_ext (pathOk := pathOk) hstk hhi_stk x s0 sf_m wDot wR0 wR7 wM0 wM6
                f0 f1 filePtr fileCap x.signedId (.malformed, x.kg)
                ⟨hans_m, htr_m⟩)
            unfold kpkMarkRoBundle
            kpk_sep_norm
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono_right
                            (sepConj_mono hm_c8
                              (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))))))))))
            sep_focus
    · have hmod0 : seenBs.length % 37 = 0 := by omega
      have hrem_eq := udiv_msub_37_beq_zero_true (by omega : seenBs.length < 2 ^ 64) hmod0
      rw [show ∀ (Pool S U1 U2 U3 U4 U5 MR Rest : SepProp),
            Pool ∗ S ∗ U1 ∗ U2 ∗ U3 ∗ U4 ∗ U5 ∗ MR ∗ Rest =
            (MR ∗ S) ∗ Pool ∗ U1 ∗ U2 ∗ U3 ∗ U4 ∗ U5 ∗ Rest from fun _ _ _ _ _ _ _ _ _ => by ac_rfl,
          ← subStack_split s0.sp hext_le hhi]
      unfold kpkMarkRoBundle
      kpk_sep_norm
      by_cases hseen_nil : seenBs = []
      · subst hseen_nil
        have hnil_beq : (BitVec.ofNat 64 ([] : List (BitVec 8)).length == 0#64) = true := rfl
        have hans_nil :
            (KpkMarkAns.ok,
              { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) ([] ++ usedBs) }) =
            kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
          unfold kpkMarkOf
          rw [hget1, hget2]
          simp [usedBs, hasChunk_nil hused37]
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% (892)) hinv_s7
        wp_steps
        apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro hinv_37c
        refine happend x s0 _
          usedCap usedPtr usedBs seenCap seenPtr [] fileCap filePtr (baseKeysName x.id) _
          (((dotBaseKeAddr img.base) ↦₆₄ᵣ wDot) ∗
            ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
            ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
            ((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
            ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            dirAt A x.self x.kg.oneTime ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
          hhi hlr_chg hused37 hu_len hu_lt hu_ptr (by decide) hs_len hs_lt hs_ptr
          hf_len hf_lt hf_ptr
          (by kpk_norm) (by kpk_norm) hsp_align
          (by kpk_norm) (by kpk_norm) (by kpk_norm) hinv_37c
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm) (by kpk_norm)
          hpan
          (by unfold epiloguePre; kpk_sep_focus)
          fun sf_a P_a htr_a hsp_a hcs_a hPa =>
            hk_final sf_a P_a hsp_a hcs_a <| by
              refine Entails.trans hPa ?_
              have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
                (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
                (by bv_omega) (by bv_omega)
              refine Entails.trans ?_
                (kpkMark_final_ext (pathOk := pathOk) hstk hhi_stk x s0 sf_a wDot wR0 wR7 wM0 wM6
                  (BitVec.ofNat 64 (baseKeysName x.id).length) seenPtr filePtr fileCap x.signedId
                  (.ok,
                    { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) ([] ++ usedBs) })
                  ⟨hans_nil, htr_a⟩)
              rw [subStack_split s0.sp hext_le hhi]
              unfold kpkMarkRoBundle
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                              (sepConj_mono_left hm_80))))))))))))))))))))))
              sep_focus
      · have hseen_pos : 0 < seenBs.length :=
          List.length_pos_iff.mpr hseen_nil
        have hseen_beq : (BitVec.ofNat 64 seenBs.length == 0#64) = false := by
          apply beq_false_of_ne
          intro h0
          have ht := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
          change seenBs.length = 0 at ht
          omega
        have hrem_ex : ∃ rem, seenBs.length = (rem + 1) * 37 := by
          refine ⟨seenBs.length / 37 - 1, ?_⟩
          omega
        apply SepWPp.of_sepWP_inImage
          (mid := fnBase + bv% (524)) hinv_s7
        wp_steps
        apply SepWP.done (by kpk_norm) (by kpk_norm)
        intro hinv_20c
        obtain ⟨rem, hrem_len⟩ := hrem_ex
        refine hloop x s0 wR0 wR7
          usedCap usedPtr seenCap seenPtr seenBs fileCap filePtr
          (((dotBaseKeAddr img.base) ↦₆₄ᵣ wDot) ∗
            ((malformedStrAddr img.base) ↦₆₄ᵣ wM0) ∗
            ((malformedStrAddr img.base + 6#64) ↦₆₄ᵣ wM6) ∗
            memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
            memRegion (s0.sp - 0xf0#64) 8 ∗
            memRegion (s0.sp - 0x68#64) 4 ∗
            ((s0.sp - 0x64#64) ↦₃₂ x.signedId) ∗
            (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
          hhi hsp_align hSeenOk hlr_chg hget1 hget2
          hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr hpan
          (fun sf_l P_l ans kg' hans_l htr_l hsp_l hcs_l hPl =>
            hk_final sf_l P_l hsp_l hcs_l <| by
              refine Entails.trans hPl ?_
              refine Entails.trans ?_
                (kpkMark_final_sub (pathOk := pathOk) hstk hhi_stk x s0 sf_l wDot wR0 wR7 wM0 wM6
                  filePtr fileCap x.signedId (ans, kg') ⟨hans_l, htr_l⟩)
              unfold kpkMarkRoBundle
              kpk_sep_norm
              sep_focus)
          rem _ 0 [] seenBs _
          rfl rfl hrem_len (fun _ hj => absurd hj (Nat.not_lt_zero _))
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          hinv_20c (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by dsimp only [List.length_nil]; rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.add_zero]; kpk_norm)
          (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
          (by unfold epiloguePre; kpk_sep_focus)

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
