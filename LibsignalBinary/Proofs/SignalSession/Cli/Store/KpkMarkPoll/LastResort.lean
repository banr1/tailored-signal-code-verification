/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Specs
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.RoData
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Drops
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGet
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
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

/-! ## Full `last_resort` Branch (`+280 .. +372`, `kpk_last_resort_118`) -/

set_option maxHeartbeats 1200000 in
/-- Verifies the `one_time = Ok([])` continuation starting at `+280`:
`decimal(id)` + `.base-keys` reserve (`+988 .. +1020`) + `.base-keys` write + `last_resort.get` +
`kpk_after_lr_get_174`. -/
theorem kpk_last_resort_118 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hDecimal : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr decimalName)
      (decimalSpec A img decStk))
    (hGet : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirGetName)
      (dirGetSpec rd pathOk A img getStk))
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (x : KpkMarkPollGhost) (s0 s : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (P : SepProp) {Q Qp : State → SepProp → Prop}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hwDot : unpack64 wDot = utf8 ".base-ke")
    (hBkOk : KpkBaseKeysOk pathOk x.kg.lastResort x.id)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (280))
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hfs : FsInv s0.fs.files s0.trace s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx23 : s.readReg64 .x23 = x.id.setWidth 64)
    (hx26 : s.readReg64 .x26 = x.self)
    (hx28 : s.readReg64 .x28 = x.signedId.setWidth 64)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hfoc : P ⊢
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A x.self x.kg.oneTime ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x ∗ A.pool)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hget_le : getStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hres_le : doReserveStackX ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdec_fs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  rw [← decimal_fnAddr_eq] at hdec_fs
  have hres_fs := subroutine_ok_withFsInv hFs (kpkReserve_ok hC (le_refl doReserveStackX))
    s0.fs.files s0.trace
  rw [← cliDoReserve_fnAddr_eq] at hres_fs
  have hget_fs := subroutine_ok_withFsInv hFs hGet s0.fs.files s0.trace
  rw [← dirGet_fnAddr_eq] at hget_fs
  have hafter_lr := @kpk_after_lr_get_174 img A ext rd pathOk decStk getStk putStk stk hb hC hBcmp hPut
  clear hC hBcmp hDecimal hGet hPut
  have he_fn :
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr kpkMarkPollName =
      img.base + bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") := by
    simp only [Program.fnAddr_rebase, kpkMarkPollName, kpkMarkPoll_fnOff]
  have hdot_addr := adrp_add_dotBaseKe_eq hb he_fn
  clear he_fn
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    280 92
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    988 36
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hFs hdec_fs hres_fs hget_fs hafter_lr hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine sepWPp_conseq hfoc ?_
  rw [ProofLib.memRegion_split' (b := s0.sp - 0xb0#64) (n := 24) (k := 24)
        (b' := s0.sp - 0x98#64) rfl (by bv_omega) (by decide)]
  apply sepWPp_of_sepWP_fs (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "libsignal_cli::stores::decimal"))
    hFs hinv hfs
  wp_steps
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hinv_d1 hfs_d1
  apply bind_sepWPp_state_mark; intro st_d1
  have hsp_d1 : st_d1.sp = s0.sp - 0xf0#64 := by dsimp only [st_d1]; (try kpk_norm)
  dsimp only [st_d1] at *
  refine kpk_call_decimal_fs hdec_fs { n := x.id, ret := s0.sp - 0xb0#64 }
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - decStk) ∗
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0x98#64) 24 ∗
      memRegion (s0.sp - 0x80#64) 24 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A x.self x.kg.oneTime ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := fnBase + bv% (292))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp_d1)
    (by kpk_norm)
    (by kpk_norm)
    hinv_d1
    hfs_d1
    (by kpk_norm)
    (by kpk_norm)
    hpan
    (by
      rw [hsp_d1, subStack_split s0.sp hdec_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun s1 hpc1 hrun1 hsp1 hcs1 hinv1 hfs1 htr1 => ?_
  have hs1_sp : s1.sp = s0.sp - 0xf0#64 := hsp1.trans hsp_d1
  have hs1_al : s1.spAligned = true := spAligned_sub_f0 hsp_align hs1_sp
  have hs1_tr : s1.trace = s0.trace := by rw [htr1]; kpk_norm
  have hkn_lt32 : (keyName x.id).length < 2 ^ 32 := by
    have hb1 := hBkOk.1
    rw [← baseKeysName_eq_append, List.length_append, List.length_append] at hb1
    omega
  change SepWPp _ _ _ ((vecU8 A (s0.sp - 0xb0#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
  rw [hsp_d1, subStack_merge_pool_mid s0.sp hdec_le hhi,
      vecU8_unpack_at A (s0.sp - 0xb0#64) (keyName x.id)]
  kpk_sep_norm
  refine SepWPp.exists_elim fun decCap => SepWPp.exists_elim fun decPtr => ?_
  rw [vecU8At_unpack_any A (s0.sp - 0xb0#64) decCap decPtr (keyName x.id)]
  kpk_sep_norm
  refine SepWPp.pure_elim fun ⟨hd_len, hd_lt, hd_ptr⟩ => ?_
  have e_a8 : s0.sp - 0xb0#64 + 8#64 = s0.sp - 0xa8#64 := by bv_omega
  have e_a0 : s0.sp - 0xb0#64 + 16#64 = s0.sp - 0xa0#64 := by bv_omega
  rw [e_a8, e_a0]
  have hjoin_316 : ∀ (s2 : State) (fileCap filePtr : BitVec 64) (Q2 : SepProp),
      (keyName x.id).length + 10 ≤ fileCap.toNat →
      fileCap.toNat < 2 ^ 63 →
      filePtr ≠ 0#64 →
      s2.pc = fnBase + bv% (316) →
      s2.status = .Running →
      s2.sp = s0.sp - 0xf0#64 →
      s2.readReg64 .x29 = s0.sp - 0x60#64 →
      s2.trace = s0.trace →
      ImgCallInv img s2 →
      FsInv s0.fs.files s0.trace s2 →
      calleeSavedVRegs s2 = calleeSavedVRegs s0 →
      s2.readReg64 .x1 = BitVec.ofNat 64 (keyName x.id).length →
      s2.readReg64 .x19 = x.fut →
      s2.readReg64 .x20 = x.out →
      s2.readReg64 .x26 = x.self →
      s2.readReg64 .x28 = x.signedId.setWidth 64 →
      (Q2 ⊢
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xa8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x98#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        A.live filePtr fileCap.toNat 1 ∗
        (filePtr ↦ₛ keyName x.id) ∗
        memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
          (fileCap.toNat - (keyName x.id).length) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool) →
      SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s2 Q2 Q Qp := by
    intro s2 fileCap filePtr Q2 hf_ge10 hf_lt hf_ptr hpc2 hrun2 hsp2 hfp2 htr2 hinv2 hfs2
      hv2 s2_1 s2_19 s2_20 s2_26 s2_28 hQ2
    have hf_ne0 : fileCap ≠ 0#64 :=
      fun h0 => by have : fileCap.toNat = 0 := by subst h0; rfl
                   omega
    have hsp_al2 : s2.spAligned = true := spAligned_sub_f0 hsp_align hsp2
    refine sepWPp_conseq hQ2 ?_
    have hbkn_len : (baseKeysName x.id).length = (keyName x.id).length + 10 := by
      rw [← baseKeysName_eq_append, List.length_append, List.length_append,
          utf8_dot_base_ke_length]; rfl
    have hafter_dot : ∀ (s3 : State) (Q3 : SepProp),
        s3.pc = fnBase + bv% (328) →
        s3.status = .Running →
        s3.sp = s0.sp - 0xf0#64 →
        s3.readReg64 .x29 = s0.sp - 0x60#64 →
        s3.trace = s0.trace →
        ImgCallInv img s3 →
        FsInv s0.fs.files s0.trace s3 →
        calleeSavedVRegs s3 = calleeSavedVRegs s0 →
        s3.readReg64 .x1 = BitVec.ofNat 64 (keyName x.id).length →
        s3.readReg64 .x2 = filePtr →
        s3.readReg64 .x8 = dotBaseKeAddr img.base →
        s3.readReg64 .x19 = x.fut →
        s3.readReg64 .x20 = x.out →
        s3.readReg64 .x26 = x.self →
        s3.readReg64 .x28 = x.signedId.setWidth 64 →
        (Q3 ⊢
          kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          A.live filePtr fileCap.toNat 1 ∗
          (filePtr ↦ₛ keyName x.id) ∗
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
            (fileCap.toNat - (keyName x.id).length) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x ∗ A.pool) →
        SepWPp (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) (s0.readReg64 .lr) s3 Q3 Q Qp := by
      intro s3 Q3 hpc3 hrun3 hsp3 hfp3 htr3 hinv3 hfs3 hv3
        s3_1 s3_2 s3_8 s3_19 s3_20 s3_26 s3_28 hQ3
      have hsp_al3 : s3.spAligned = true := spAligned_sub_f0 hsp_align hsp3
      refine sepWPp_conseq hQ3 ?_
      have hsplit_10 :
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length)
            (fileCap.toNat - (keyName x.id).length) =
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length) 8 ∗
          memRegion (filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64) 2 ∗
          memRegion (filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
            (fileCap.toNat - (baseKeysName x.id).length) := by
        rw [ProofLib.memRegion_split'
              (b := filePtr + BitVec.ofNat 64 (keyName x.id).length)
              (n := 8) (k := fileCap.toNat - (keyName x.id).length - 8)
              (b' := filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64)
              (by omega) rfl (by omega),
            ProofLib.memRegion_split'
              (b := filePtr + BitVec.ofNat 64 (keyName x.id).length + 8#64)
              (n := 2) (k := fileCap.toNat - (baseKeysName x.id).length)
              (b' := filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
              (by omega)
              (by rw [hbkn_len, BitVec.ofNat_add]; bv_omega)
              (by omega)]
      rw [hsplit_10,
          ProofLib.memRegion_eight (filePtr + BitVec.ofNat 64 (keyName x.id).length),
          memRegion_two_16]
      unfold kpkMarkRoBundle
      kpk_sep_norm
      refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d8 => ?_
      apply sepWPp_of_sepWP_fs
        (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "<libsignal_cli::stores::Dir>::get")) hFs hinv3 hfs3
      wp_steps
      apply SepWP.done
        (by kpk_norm)
        (by wp_norm_lhs)
      intro hinv_g2 hfs_g2
      apply bind_sepWPp_state_mark; intro st_g2
      have hsp_g2 : st_g2.sp = s0.sp - 0xf0#64 := by dsimp only [st_g2]; (try kpk_norm)
      have htr_g2 : st_g2.trace = s0.trace := by dsimp only [st_g2]; (try kpk_norm)
      have hfiles_g2 : st_g2.fs.files = s0.fs.files :=
        files_eq_of_fsInv_trace_eq hfs_g2 htr_g2
      dsimp only [st_g2] at *
      have hadd10 : BitVec.ofNat 64 (keyName x.id).length + 10#64 =
          BitVec.ofNat 64 (baseKeysName x.id).length := by
        rw [hbkn_len, BitVec.ofNat_add]
      have htoNat_bkn :
          (BitVec.ofNat 64 (baseKeysName x.id).length).toNat = (baseKeysName x.id).length := by
        have := hBkOk.1
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      refine kpk_call_dirGet_fs hget_fs
        { ret := s0.sp - 0xb0#64, self := x.self + 0x28#64, dir := x.kg.lastResort,
          nameA := filePtr, name := baseKeysName x.id, nameRo := false }
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - getStk) ∗
          kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗ ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
          dirAt A x.self x.kg.oneTime ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        (ret_pc := fnBase + bv% (372))
        (by kpk_norm)
        (by kpk_norm)
        (spAligned_sub_f0 hsp_align hsp_g2)
        (by kpk_norm)
        htr_g2
        hinv_g2
        hfs_g2
        (by kpk_norm)
        (by kpk_norm)
        (by kpk_norm)
        (by
          refine Eq.trans (congrArg BitVec.toNat
            (show _ = BitVec.ofNat 64 (keyName x.id).length + 10#64 by kpk_norm)) ?_
          rw [hadd10, htoNat_bkn])
        hBkOk.1
        hBkOk.2.1
        hBkOk.2.2
        hpan
        (by
          rw [hsp_g2, subStack_split s0.sp hget_le hhi]
          have htail_file :
              A.live filePtr fileCap.toNat 1 ∗
                memRegion (filePtr + BitVec.ofNat 64 (baseKeysName x.id).length)
                  (fileCap.toNat - (baseKeysName x.id).length) =
              vecU8Tail A fileCap filePtr (baseKeysName x.id) := by
            unfold vecU8Tail; simp only [hf_ne0, ite_false]
          have hbytes_file := assemble_baseKeysName filePtr wDot x.id hwDot
          unfold kpkMarkRoBundle epiloguePre
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_left (Entails.of_eq hbytes_file)))
          rw [← htail_file]
          kpk_sep_norm
          sep_focus)
        fun s4 gr hpc4 hrun4 hsp4 hcs4 hinv4 _hfs4 hgr4 => ?_
      have hs4_sp : s4.sp = s0.sp - 0xf0#64 := hsp4.trans hsp_g2
      have hgr4_s0 :
          gr = x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) ∧ s4.trace = s0.trace := by
        rcases hgr4 with ⟨h1, h2⟩
        rw [hfiles_g2] at h1
        exact ⟨h1, h2.trans htr_g2⟩
      refine sepWPp_conseq ?_
        (hafter_lr x s0 s4 wDot wR0 wR7 wM0 wM6
          f0 f1 filePtr fileCap tmp32 gr
          hstk hhi_stk hsp_align hSeenOk hlr_chg hget1 hgr4_s0
          (by rw [hbkn_len]; exact hf_ge10) hf_lt hf_ptr
          (by kpk_norm) hrun4 hs4_sp
          (by rw [(cs_x29 hcs4)]; kpk_norm)
          hinv4
          (by rw [(cs_vregs hcs4)]; kpk_norm)
          (by rw [(cs_x19 hcs4)]; kpk_norm)
          (by rw [(cs_x20 hcs4)]; kpk_norm)
          (by rw [(cs_x24 hcs4)]; rw [← hadd10]; kpk_norm)
          (by rw [(cs_x26 hcs4)]; kpk_norm)
          (by rw [(cs_x28 hcs4)]; kpk_norm)
          hpan hk_final)
      rw [hsp_g2, subStack_split s0.sp hget_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus
    apply sepWPp_of_sepWP_fs
      (mid := fnBase + bv% (328))
      hFs hinv2 hfs2
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_dot hfs_dot
    refine hafter_dot _ _ (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      hinv_dot hfs_dot (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by rw [← hdot_addr]; kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm) ?_
    have hm_hdr := header3_entails_memRegion24 (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
      (s0.sp - 0xa0#64) fileCap filePtr (BitVec.ofNat 64 (keyName x.id).length)
      (by bv_omega) (by bv_omega)
    have hm_b0 := Entails.trans (sepConj_mono_left hm_hdr) (slot_b0_24_24_merge s0.sp)
    unfold epiloguePre
    kpk_sep_norm
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hm_b0))))))))))
    sep_focus
  by_cases hule : (decCap - BitVec.ofNat 64 (keyName x.id).length).ule 9#64 = true
  · have hbound10 := reserve_name_bound hkn_lt32 hd_len hd_lt hule
    apply sepWPp_of_sepWP_fs
      (mid := fnBase - bv% (ls_rel%
        "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#9]"
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
      hFs hinv1 hfs1
    wp_steps
    apply SepWP.done
      (by kpk_norm)
      (by wp_norm_lhs)
    intro hinv_res hfs_res
    apply bind_sepWPp_state_mark; intro st_res
    have hsp_res : st_res.sp = s0.sp - 0xf0#64 := by (try dsimp only [st_res]); (try kpk_norm)
    (try dsimp only [st_res] at *)
    have hlen_kn_nat : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    refine kpk_call_reserve_fs hres_fs ⟨s0.sp - 0xb0#64, decCap, decPtr, keyName x.id, 10⟩
      (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - doReserveStackX) ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0x98#64) 24 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x)
      (ret_pc := fnBase + bv% (1008))
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_res)
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_tr)))
      hinv_res
      hfs_res
      (by kpk_norm)
      (by
        refine Eq.trans (congrArg BitVec.toNat
          (show _ = BitVec.ofNat 64 (keyName x.id).length by kpk_norm)) ?_
        exact hlen_kn_nat)
      (by kpk_norm)
      (by kpk_norm)
      (by kpk_norm)
      hbound10
      hpan
      (by
        rw [hsp_res, subStack_split s0.sp hres_le hhi]
        have hv_at := vecU8At_of_live_parts A (s0.sp - 0xb0#64) (s0.sp - 0xa8#64)
          (s0.sp - 0xa0#64) decCap decPtr (keyName x.id) (by bv_omega) (by bv_omega)
          hd_len hd_lt hd_ptr
        refine Entails.trans ?_ (sepConj_mono_left (sepConj_mono_left hv_at))
        unfold epiloguePre
        kpk_sep_norm
        sep_focus)
      fun sm p' hpcm hrunm hspm hcsm hinvm hfsm htrm hp'_ne => ?_
    let newCapN := reserveCap decCap.toNat (keyName x.id).length 10
    have hnew_lt : newCapN < 2 ^ 63 := by dsimp [newCapN] at *; omega
    have hnew_pos : 0 < newCapN := by dsimp [newCapN, reserveCap]; omega
    have hnew_ne0 : BitVec.ofNat 64 newCapN ≠ 0#64 := by
      intro h0
      have ht := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
      change newCapN = 0 at ht; omega
    have hnew_toNat : (BitVec.ofNat 64 newCapN).toNat = newCapN := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [vecU8At_unpack_pos_lr A (s0.sp - 0xb0#64) (BitVec.ofNat 64 newCapN) p'
          (keyName x.id) hnew_ne0, e_a8, e_a0]
    kpk_sep_norm
    refine SepWPp.pure_elim fun _ => ?_
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_res
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    have hsm_tr : sm.trace = s0.trace := by
      rw [htrm]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_tr))
    rw [hsp_res, subStack_merge_rev_adj s0.sp hres_le hhi]
    apply sepWPp_of_sepWP_fs
      (mid := fnBase + bv% (316))
      hFs hinvm hfsm
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_316 hfs_316
    refine hjoin_316 _ (BitVec.ofNat 64 newCapN) p' _
      (by rw [hnew_toNat]; dsimp [newCapN, reserveCap]; omega)
      (by rw [hnew_toNat]; exact hnew_lt)
      hp'_ne
      (by kpk_norm) (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
      hinv_316 hfs_316
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs1)]; kpk_norm))
      (by kpk_norm)
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs1)]; kpk_norm))
      (by
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)])
        (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcs1)]; kpk_norm))
      (by unfold epiloguePre; kpk_sep_focus)
  · have hule_f : (decCap - BitVec.ofNat 64 (keyName x.id).length).ule 9#64 = false :=
      Bool.eq_false_iff.mpr hule
    have hfast_ge := fast_name_cap_ge hkn_lt32 hd_len hule_f
    have hd_ne0 : decCap ≠ 0#64 :=
      fun h0 => by have : decCap.toNat = 0 := by subst h0; rfl
                   omega
    simp only [hd_ne0, ite_false]
    kpk_sep_norm
    apply sepWPp_of_sepWP_fs
      (mid := fnBase + bv% (316))
      hFs hinv1 hfs1
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_316 hfs_316
    refine hjoin_316 _ decCap decPtr _
      hfast_ge hd_lt hd_ptr
      (by kpk_norm) (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_sp)))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hs1_tr)))
      hinv_316 hfs_316
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcs1)]; kpk_norm))
      (by kpk_norm)
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcs1)]; kpk_norm))
      (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcs1)]; kpk_norm))
      (by unfold epiloguePre; kpk_sep_focus)

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
