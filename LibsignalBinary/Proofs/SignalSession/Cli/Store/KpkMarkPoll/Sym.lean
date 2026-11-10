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
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResort
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortAfterGet
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortLoop
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

set_option maxHeartbeats 1200000 in
/-- Dispatches at `+88` right after `one_time.get` returns `gr`:
- `gr = .error ()`: steps `+88 .. +100` to `kpk_read_err_c4` (`+196`);
- `gr = .ok []`: steps `+88 .. +104` to `kpk_drop_both_f0` (`+240`) → `kpk_last_resort_118` (`+280`);
- `gr = .ok (b :: bs)`: steps `+88 .. +104` to `kpk_drop_both_6c` (`+108`) → `decimal(id)` (`+148`)
  → `[0, 1, 0]` (`+160 .. +180`) → `kpk_put_and_epilogue_b8` (`+184`). -/
theorem kpk_after_ot_get_58 {img : Obj.Image} {A : RustAlloc}
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
    (x : KpkMarkPollGhost) (s0 sm2 : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 nameCap namePtr : BitVec 64) (tmp32 : BitVec 32)
    (gr : Except Unit (List (BitVec 8)))
    {Q Qp : State → SepProp → Prop}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk)
    (hhi_stk : stk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hwDot : unpack64 wDot = utf8 ".base-ke")
    (hBkOk : KpkBaseKeysOk pathOk x.kg.lastResort x.id)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hot_chg : x.kg.oneTime.changed.length < 2 ^ 32)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hn_len : (keyName x.id).length ≤ nameCap.toNat)
    (hn_lt : nameCap.toNat < 2 ^ 63) (hn_ptr : namePtr ≠ 0#64)
    (hgr : gr = x.kg.oneTime.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace)
    (hpc : sm2.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (88))
    (hrun : sm2.status = .Running)
    (hsp : sm2.sp = s0.sp - 0xf0#64)
    (hfp : sm2.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img sm2)
    (hfs : FsInv s0.fs.files s0.trace sm2)
    (hvregs : calleeSavedVRegs sm2 = calleeSavedVRegs s0)
    (hx19 : sm2.readReg64 .x19 = x.fut)
    (hx20 : sm2.readReg64 .x20 = x.out)
    (hx23 : sm2.readReg64 .x23 = x.id.setWidth 64)
    (hx24 : sm2.readReg64 .x24 = namePtr)
    (hx26 : sm2.readReg64 .x26 = x.self)
    (hx28 : sm2.readReg64 .x28 = x.signedId.setWidth 64)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) sm2
      (getResultAt A (s0.sp - 0xb0#64) gr ∗
        kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr (keyName x.id) ∗
        vecU8Tail A nameCap namePtr (keyName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        epiloguePre s0 x ∗ A.pool)
      Q Qp := by
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hsp_al : sm2.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have herr_c4 := @kpk_read_err_c4 img A ext hC
  have hdrop_f0 := @kpk_drop_both_f0 img A ext hC
  have hdrop_6c := @kpk_drop_both_6c img A ext hC
  have hput_ep := @kpk_put_and_epilogue_b8 img A ext decStk getStk putStk hPut
  have hlr118 := @kpk_last_resort_118 img A ext rd pathOk decStk getStk putStk stk
    hb hC hBcmp hDecimal hGet hPut hFs
  rw [← decimal_fnAddr_eq] at hDecimal
  clear hC hBcmp hGet hPut
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    88 96
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hFs hDecimal herr_c4 hdrop_f0 hdrop_6c hput_ep hlr118 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  rcases gr with ⟨⟩ | bytesBs
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
      (mid := fnBase + bv% (196)) hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_c4
    refine herr_c4 x s0 _ nameCap namePtr (keyName x.id)
      errBs errCap errPtr fnPtr _
      (kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
        memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        memRegion (s0.sp - 0xf0#64) 8 ∗
        ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        ((s0.sp - 0xb0#64) ↦₆₄ speWord 1) ∗ ((s0.sp - 0xa8#64) ↦₆₄ errCap) ∗
        ((s0.sp - 0xa0#64) ↦₆₄ errPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 errBs.length) ∗
        ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
        memRegion (s0.sp - 0x68#64) 4 ∗
        ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
      hn_len hn_lt hn_ptr
      (by kpk_norm) (by kpk_norm) hsp_align (by kpk_norm) (by kpk_norm) hinv_c4
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
      (by unfold epiloguePre; kpk_sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk_final sf P_f hsp_f hcs_f <| by
          have htr_eq : sf.trace = sm2.trace := htr_f.trans (by kpk_norm)
          have hres_eq :
              ((.readErr : KpkMarkAns), x.kg) =
                  kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
                sf.trace = s0.trace := by
            rcases hgr with ⟨hget1_err, hsm2_tr⟩
            refine ⟨?_, htr_eq.trans hsm2_tr⟩
            unfold kpkMarkOf
            rw [← hget1_err]
          refine Entails.trans hPf ?_
          have hb0 := slot_b0_err_collapse s0.sp (speWord 1) errCap errPtr
            (BitVec.ofNat 64 errBs.length) (BitVec.ofNat 64 (utf8 "read").length)
            (fnPtr.extractLsb' 0 8) (fnPtr.extractLsb' 8 32)
            (fnPtr.extractLsb' 40 16) (fnPtr.extractLsb' 56 8)
          have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
            (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
            (by bv_omega) (by bv_omega)
          refine Entails.trans ?_
            (kpkMark_final_ext (pathOk := pathOk) hstk hhi_stk x s0 sf wDot wR0 wR7 wM0 wM6
              f0 f1 f2 f3 tmp32 (.readErr, x.kg) hres_eq)
          kpk_sep_norm
          refine Entails.trans ?_
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono hb0 (sepConj_mono_left hm80))))))))))))))))))
          sep_focus
  · rcases hgr with ⟨hget1_symm, hsm2_tr⟩
    have hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok bytesBs :=
      hget1_symm.symm
    have heq0 : (okTagVec + 2#64 != 0#64) = false := rfl
    rw [getResultAt_b0_ok_unpack A s0.sp bytesBs, subStack_split s0.sp hext_le hhi]
    kpk_sep_norm
    refine SepWPp.exists_elim fun bytesCap => SepWPp.exists_elim fun bytesPtr => ?_
    refine SepWPp.pure_elim fun ⟨hb_len, hb_lt, hb_ptr⟩ => ?_
    rcases bytesBs with _ | ⟨b0_byte, bs_tail⟩
    · have hnil_beq : (BitVec.ofNat 64 ([] : List (BitVec 8)).length == 0#64) = true := rfl
      apply sepWPp_of_sepWP_fs
        (mid := fnBase + bv% (240))
        hFs hinv hfs
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_f0 hfs_f0
      refine hdrop_f0 s0 _ bytesCap bytesPtr [] nameCap namePtr (keyName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗ ((s0.sp - 0x98#64) ↦₆₄ 0#64) ∗
          memRegion (s0.sp - 0x90#64) 16 ∗
          kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        hFs hfs_f0 hb_len hb_lt hb_ptr hn_len hn_lt hn_ptr
        (by kpk_norm) (by kpk_norm) hsp_align (by kpk_norm) (by kpk_norm) hinv_f0
        (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        (by unfold epiloguePre; kpk_sep_focus)
        fun slr hpclr hrunlr hsplr hinvlr hfslr htrlr r19 r20 r23 r26 r28 r29 hvlr =>
          hlr118 x s0 slr
            wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32 _
            hstk hhi_stk hsp_align hwDot hBkOk hSeenOk hlr_chg hget1
            (by kpk_norm) hrunlr hsplr r29
            (by rw [htrlr]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm2_tr)))
            hinvlr hfslr hvlr
            (r19.trans (by kpk_norm))
            (r20.trans (by kpk_norm))
            (r23.trans (by kpk_norm))
            (r26.trans (by kpk_norm))
            (r28.trans (by kpk_norm))
            hpan
            (by
              have hb0 := slot_b0_ok_collapse s0.sp okTagVec bytesCap bytesPtr 0#64
              have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
                (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
                (by bv_omega) (by bv_omega)
              rw [subStack_split s0.sp hext_le hhi]
              unfold epiloguePre
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right
                        (sepConj_mono hb0 (sepConj_mono_left hm80))))))))))))
              sep_focus)
            hk_final
    · let consBs := b0_byte :: bs_tail
      have hlen_ne0 : (BitVec.ofNat 64 (b0_byte :: bs_tail).length == 0#64) = false := by
        apply beq_false_of_ne
        intro h0
        have ht := congrArg BitVec.toNat h0
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
        change (b0_byte :: bs_tail).length = 0 at ht
        simp at ht
      have hans_ok :
          (KpkMarkAns.ok, { x.kg with oneTime := x.kg.oneTime.put (keyName x.id) [] }) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1]
      apply sepWPp_of_sepWP_fs
        (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "libsignal_cli::stores::decimal")) hFs hinv hfs
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (108)) hinv
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_6c
      exact hdrop_6c s0 _ bytesCap bytesPtr consBs nameCap namePtr (keyName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
          ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
          ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
          memRegion (s0.sp - 0x90#64) 16 ∗
          kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
          memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
          ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
          (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
          epiloguePre s0 x)
        hb_len hb_lt hb_ptr hn_len hn_lt hn_ptr
        (by kpk_norm) (by kpk_norm) hsp_align (by kpk_norm) (by kpk_norm) hinv_6c
        (by kpk_norm) (by kpk_norm) (by kpk_norm) (by kpk_norm)
        (by unfold epiloguePre; kpk_sep_focus)
        fun sd hpcd hrund hspd _hinvd htrd r19 r20 r23 r26 _r28 r29 hvd => by
          have hsd_al : sd.spAligned = true := spAligned_sub_f0 hsp_align hspd
          have hx23_sd : sd.readReg64 .x23 = x.id.setWidth 64 := r23.trans (by kpk_norm)
          wp_steps
          apply SepWP.done
            (by kpk_norm)
            (by wp_norm_lhs)
          intro hinv_dec2 _hfs_dec2
          apply bind_sepWPp_state_mark; intro st_dec2
          have hsp_dec2 : st_dec2.sp = s0.sp - 0xf0#64 := by
            (try dsimp only [st_dec2]); (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hspd))
          have htr_dec2 : st_dec2.trace = s0.trace := by
            (try dsimp only [st_dec2]); (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            (try rw [htrd]); (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try (first | rfl | exact hsm2_tr)
          (try dsimp only [st_dec2] at *)
          refine kpk_call_decimal hDecimal { n := x.id, ret := s0.sp - 0x80#64 }
            (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                (kpkSubMax decStk getStk putStk - decStk) ∗
              ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
              ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
              ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
              memRegion (s0.sp - 0x90#64) 16 ∗
              kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
              memRegion (s0.sp - 0xf0#64) 8 ∗
              ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
              ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
              memRegion (s0.sp - 0xc8#64) 24 ∗
              memRegion (s0.sp - 0x68#64) 4 ∗
              ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
              dirAt A x.self x.kg.oneTime ∗
              dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
              (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
              epiloguePre s0 x)
            (ret_pc := fnBase + bv% (160))
            (by kpk_norm)
            (by kpk_norm)
            (spAligned_sub_f0 hsp_align hsp_dec2)
            (by kpk_norm)
            htr_dec2
            hinv_dec2
            (by (try rw [show sd.readReg64 .x29 = s0.sp - 0x60#64 from r29]); kpk_norm)
            (by kpk_norm)
            hpan
            (by
              rw [hsp_dec2]
              have hstk_re :
                  stackAt (s0.sp - 0xf0#64) extHookStack ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - extHookStack) =
                  memRegion
                    (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                    (kpkSubMax decStk getStk putStk - decStk) ∗
                    stackAt (s0.sp - 0xf0#64) decStk := by
                rw [sepConj_comm (stackAt _ _) _,
                    ← subStack_split s0.sp hext_le hhi,
                    subStack_split s0.sp hdec_le hhi]
              have hm80 := header3_entails_memRegion24 (s0.sp - 0x80#64) (s0.sp - 0x78#64)
                (s0.sp - 0x70#64) nameCap namePtr (BitVec.ofNat 64 (keyName x.id).length)
                (by bv_omega) (by bv_omega)
              have hswap_d :
                  ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
                    stackAt (s0.sp - 0xf0#64) extHookStack ∗
                    A.pool ∗
                    (memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - extHookStack) ∗
                      ((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
                      ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
                      ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
                      ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A x.self x.kg.oneTime ∗
                      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                      epiloguePre s0 x) =
                  (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
                    ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
                    ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length)) ∗
                    (stackAt (s0.sp - 0xf0#64) extHookStack ∗
                      memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - extHookStack)) ∗
                    A.pool ∗
                    (((s0.sp - 0xb0#64) ↦₆₄ okTagVec) ∗ ((s0.sp - 0xa8#64) ↦₆₄ bytesCap) ∗
                      ((s0.sp - 0xa0#64) ↦₆₄ bytesPtr) ∗
                      ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A x.self x.kg.oneTime ∗
                      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                      epiloguePre s0 x) := by
                ac_rfl
              rw [hswap_d, hstk_re]
              refine Entails.trans (sepConj_mono_left hm80) ?_
              kpk_sep_norm
              sep_focus)
            fun sm3 hpcm3 hrunm3 hspm3 hcsm3 hinvm3 htrm3 => ?_
          have hsm3_sp : sm3.sp = s0.sp - 0xf0#64 := hspm3.trans hsp_dec2
          have hsm3_al : sm3.spAligned = true := spAligned_sub_f0 hsp_align hsm3_sp
          have hsm3_tr : sm3.trace = s0.trace := htrm3.trans htr_dec2
          have hsm3_fp : sm3.readReg64 .x29 = s0.sp - 0x60#64 := by
            rw [(cs_x29 hcsm3)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact r29))
          have hsm3_19 : sm3.readReg64 .x19 = x.fut := by
            rw [(cs_x19 hcsm3)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [r19]; kpk_norm)
          have hsm3_20 : sm3.readReg64 .x20 = x.out := by
            rw [(cs_x20 hcsm3)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [r20]; kpk_norm)
          have hsm3_26 : sm3.readReg64 .x26 = x.self := by
            rw [(cs_x26 hcsm3)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [r26]; kpk_norm)
          have hsm3_v : calleeSavedVRegs sm3 = calleeSavedVRegs s0 := by
            rw [(cs_vregs hcsm3)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *])
            try (first | rfl | exact hvd)
          change SepWPp _ _ _ ((vecU8 A (s0.sp - 0x80#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
          rw [hsp_dec2]
          kpk_sep_norm
          apply SepWPp.of_sepWP_inImage
            (mid := fnBase + bv% (184))
            hinvm3
          wp_steps
          apply SepWP.done (by kpk_norm) (by kpk_norm)
          intro hinv_b8
          refine hput_ep x s0 _ x.self (s0.sp - 0x80#64) (s0.sp - 0xb0#64)
            x.kg.oneTime (keyName x.id) [] _
            (((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
              memRegion (s0.sp - 0x90#64) 16 ∗
              kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
              memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
              memRegion (s0.sp - 0xf0#64) 8 ∗
              ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
              ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
              memRegion (s0.sp - 0xc8#64) 24 ∗
              memRegion (s0.sp - 0x68#64) 4 ∗
              ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
              dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
              (x.baseKeyA ↦ₛ x.baseKey.bytes.toList))
            hhi hot_chg
            (by kpk_norm) (by kpk_norm) hsp_align
            (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm3_sp)))
            (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm3_tr)))
            hinv_b8
            (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm3_v)))
            (by kpk_norm)
            (by kpk_norm)
            (by kpk_norm)
            (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm3_19)))
            (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm3_20)))
            hpan
            (by
              have hv_emp := vecU8_empty_of_zero_one_zero A
                (s0.sp - 0xb0#64) (s0.sp - 0xa8#64) (s0.sp - 0xa0#64)
                (by bv_omega) (by bv_omega)
              have hstk_m :
                  stackAt (s0.sp - 0xf0#64) decStk ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - decStk) =
                  stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) := by
                rw [sepConj_comm (stackAt _ _) _, ← subStack_split s0.sp hdec_le hhi]
              have hswap_p :
                  vecU8 A (s0.sp - 0x80#64) (keyName x.id) ∗
                    stackAt (s0.sp - 0xf0#64) decStk ∗ A.pool ∗
                    memRegion
                      (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                      (kpkSubMax decStk getStk putStk - decStk) ∗
                    ((s0.sp - 0xb0#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa8#64) ↦₆₄ 1#64) ∗
                    ((s0.sp - 0xa0#64) ↦₆₄ 0#64) ∗
                    ((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                    memRegion (s0.sp - 0x90#64) 16 ∗
                    kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
                    memRegion (s0.sp - BitVec.ofNat 64 stk)
                      (stk - kpkMinStk decStk getStk putStk) ∗
                    memRegion (s0.sp - 0xf0#64) 8 ∗
                    ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                    ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                    memRegion (s0.sp - 0xc8#64) 24 ∗
                    memRegion (s0.sp - 0x68#64) 4 ∗
                    ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                    dirAt A x.self x.kg.oneTime ∗
                    dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
                    (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
                    epiloguePre s0 x =
                  (((s0.sp - 0xb0#64) ↦₆₄ 0#64) ∗ ((s0.sp - 0xa8#64) ↦₆₄ 1#64) ∗
                    ((s0.sp - 0xa0#64) ↦₆₄ 0#64)) ∗
                    (stackAt (s0.sp - 0xf0#64) decStk ∗
                      memRegion
                        (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
                        (kpkSubMax decStk getStk putStk - decStk)) ∗
                    dirAt A x.self x.kg.oneTime ∗
                    vecU8 A (s0.sp - 0x80#64) (keyName x.id) ∗
                    epiloguePre s0 x ∗ A.pool ∗
                    (((s0.sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 consBs.length) ∗
                      memRegion (s0.sp - 0x90#64) 16 ∗
                      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
                      memRegion (s0.sp - BitVec.ofNat 64 stk)
                        (stk - kpkMinStk decStk getStk putStk) ∗
                      memRegion (s0.sp - 0xf0#64) 8 ∗
                      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
                      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
                      memRegion (s0.sp - 0xc8#64) 24 ∗
                      memRegion (s0.sp - 0x68#64) 4 ∗
                      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
                      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
                      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList)) := by
                ac_rfl
              rw [hswap_p, hstk_m]
              refine Entails.trans (sepConj_mono_left hv_emp) ?_
              kpk_sep_norm
              sep_focus)
            fun sf_p P_p htr_p hsp_p hcs_p hPp =>
              hk_final sf_p P_p hsp_p hcs_p <| by
                refine Entails.trans hPp ?_
                have hb0_p := slot_b0_put_collapse s0.sp (BitVec.ofNat 64 consBs.length)
                refine Entails.trans ?_
                  (kpkMark_final_ext (pathOk := pathOk) hstk hhi_stk x s0 sf_p wDot wR0 wR7 wM0 wM6
                    f0 f1 f2 f3 tmp32
                    (.ok, { x.kg with oneTime := x.kg.oneTime.put (keyName x.id) [] })
                    ⟨hans_ok, htr_p⟩)
                rw [subStack_split s0.sp hext_le hhi]
                kpk_sep_norm
                refine Entails.trans ?_
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_right (sepConj_mono_left hb0_p)))))))))))))))))
                sep_focus

set_option maxHeartbeats 1200000 in
/-- Top-level proof of `mark_kyber_pre_key_used::{closure#0}` against `kpkMarkPollSpec`. -/
theorem kpkMarkPoll_ok {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule}
    {pathOk : List (BitVec 8) → Prop} {decStk getStk putStk stk : Nat}
    (himg : Obj.Loads libsignalSessionImage img)
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
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName)
      (kpkMarkPollSpec rd pathOk A img stk) := by
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_al0
  have hsp_align : s0.sp &&& 15#64 = 0#64 := beq_iff_eq.mp hsp_al0
  have hinv0 : ImgCallInv img s0 := by
    have hp := hpre
    dsimp only [kpkMarkPollSpec, Spec.inImage] at hp
    rw [sepConj_assoc, satisfies_pure_sepConj] at hp
    exact hp.1
  have hfs0 : FsInv s0.fs.files s0.trace s0 := withFsInv_entry s0
  obtain ⟨wDot, wR0, wR7, wM0, wM6, hwDot, hpre_ro⟩ :=
    kpkMarkRoData_of_loads himg hinv0.1 hpre
  refine ⟨(kpkMarkPollSpec rd pathOk A img stk).pre x s0 ∗
    kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6, R,
    by
      rwa [show ((kpkMarkPollSpec rd pathOk A img stk).pre x s0 ∗
            kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6) ∗ R =
          kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
            ((kpkMarkPollSpec rd pathOk A img stk).pre x s0 ∗ R) by ac_rfl],
    ?_⟩
  generalize hQ_eq :
    (fun sf P_f =>
      ((sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf ∗ R)) ∧
      sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf) = Q
  generalize hQp_eq :
    (fun sf P_f =>
      (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (kpkMarkPollSpec rd pathOk A img stk).onPanic x s0 sf ∗ R)) = Qp
  have hpan : ∀ (sf : State) (P_f : SepProp),
      (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f := by
    rw [← hQp_eq]
    intro sf P_f halloc hmf
    dsimp only [kpkMarkPollSpec, Spec.inImage]
    simpa only [sepConj_assoc] using allowPanic_panicked halloc hmf
  have hk_final : ∀ (sf : State) (P_f : SepProp),
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf) →
      Q sf P_f := by
    rw [← hQ_eq]
    intro sf P_f hsp_f hcs_f hPf
    refine ⟨fun hmf => ?_, hsp_f, hcs_f⟩
    have hm1 := Satisfies.mono (sepConj_mono_left hPf) hmf
    rw [sepConj_assoc] at hm1
    exact Satisfies.of_sep_right hm1
  clear hQ_eq hQp_eq hpre hpre_ro himg
  dsimp only [kpkMarkPollSpec, Spec.inImage]
  kpk_sep_norm
  refine SepWPp.pure_elim fun _ => ?_
  refine SepWPp.pure_elim
    fun ⟨hx0_0, hx8_0, ⟨hkn_lt, hot_path_lt, hot_pOk⟩, hBkOk, hSeenOk, hot_chg, hlr_chg⟩ => ?_
  refine sepWPp_with_stk_bound (a := x.fut) (v := x.self)
    (Rest := kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      ((x.fut + 8#64) ↦₆₄ x.baseKeyA) ∗
      ((x.fut + 0x10#64) ↦₃₂ x.id) ∗ ((x.fut + 0x14#64) ↦₃₂ x.signedId) ∗
      ((x.fut + 0x18#64) ↦₈ 0#8) ∗ memRegion (x.fut + 0x19#64) 7 ∗
      dirAt A x.self x.kg.oneTime ∗ dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗ memRegion x.out 48 ∗ A.pool)
    (Entails.of_eq (by unfold kpkMarkBoxAt; ac_rfl))
    fun hhi_stk => ?_
  have hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := le_trans hstk hhi_stk
  have hdec_le : decStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hget_le : getStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hafter58 := @kpk_after_ot_get_58 img A ext rd pathOk decStk getStk putStk stk
    hb hC hBcmp hDecimal hGet hPut hFs
  have hDecFs := subroutine_ok_withFsInv hFs hDecimal s0.fs.files s0.trace
  rw [← decimal_fnAddr_eq] at hDecFs
  have hGetFs := subroutine_ok_withFsInv hFs hGet s0.fs.files s0.trace
  rw [← dirGet_fnAddr_eq] at hGetFs
  clear hC hBcmp hDecimal hGet hPut
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    88
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hFs hDecFs hGetFs hafter58 hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  rw [stackAt_sub_split s0.sp hstk hhi_stk,
      stackAt_kpkMark_eq s0.sp hhi,
      subStack_split s0.sp hdec_le hhi]
  unfold kpkMarkBoxAt kpkFrameSlots
  kpk_sep_norm
  refine SepWPp.exists_elim fun f0 => SepWPp.exists_elim fun f1 =>
    SepWPp.exists_elim fun f2 => SepWPp.exists_elim fun f3 =>
    SepWPp.exists_elim fun tmp32 =>
    SepWPp.exists_elim fun c0 => SepWPp.exists_elim fun c1 =>
    SepWPp.exists_elim fun c2 => SepWPp.exists_elim fun c3 =>
    SepWPp.exists_elim fun c4 => SepWPp.exists_elim fun c5 =>
    SepWPp.exists_elim fun c6 => SepWPp.exists_elim fun c7 =>
    SepWPp.exists_elim fun c8 => SepWPp.exists_elim fun c9 =>
    SepWPp.exists_elim fun c10 => SepWPp.exists_elim fun c11 => ?_
  apply sepWPp_of_sepWP_fs
    (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "libsignal_cli::stores::decimal")) hFs hinv0 hfs0
  wp_steps
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hinv1 hfs1
  apply bind_sepWPp_state_mark; intro st1
  have hsp1 : st1.sp = s0.sp - 0xf0#64 := by dsimp only [st1]; (try kpk_norm)
  dsimp only [st1] at *
  refine kpk_call_decimal_fs hDecFs { n := x.id, ret := s0.sp - 0x80#64 }
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - decStk) ∗
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      memRegion (s0.sp - 0xb0#64) 48 ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      dirAt A x.self x.kg.oneTime ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := fnBase + bv% (68))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp1)
    (by kpk_norm)
    (by kpk_norm)
    hinv1
    hfs1
    (by kpk_norm)
    (by kpk_norm)
    hpan
    (by
      rw [hsp1]
      unfold epiloguePre kpkMarkBoxAt savedCalleeSlots
      kpk_sep_norm
      sep_focus)
    fun sm1 hpcm1 hrunm1 hspm1 hcsm1 hinvm1 hfsm1 htrm1 => ?_
  have hsm1_sp : sm1.sp = s0.sp - 0xf0#64 := hspm1.trans hsp1
  have hsm1_al : sm1.spAligned = true := spAligned_sub_f0 hsp_align hsm1_sp
  have hsm1_tr : sm1.trace = s0.trace := by rw [htrm1]; kpk_norm
  have hsm1_fp : sm1.readReg64 .x29 = s0.sp - 0x60#64 := by rw [(cs_x29 hcsm1)]; kpk_norm
  change SepWPp _ _ _ ((vecU8 A (s0.sp - 0x80#64) (keyName x.id) ∗ _ ∗ _) ∗ _) _ _
  rw [hsp1, subStack_merge_pool_mid s0.sp hdec_le hhi,
      vecU8_eq_bytes_tail A (s0.sp - 0x80#64) (keyName x.id)
        (s0.sp - 0x78#64) (s0.sp - 0x70#64) (by bv_omega) (by bv_omega)]
  kpk_sep_norm
  refine SepWPp.exists_elim fun nameCap => SepWPp.exists_elim fun namePtr => ?_
  refine SepWPp.pure_elim fun ⟨hn_len, hn_lt, hn_ptr⟩ => ?_
  apply sepWPp_of_sepWP_fs
    (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "<libsignal_cli::stores::Dir>::get")) hFs hinvm1 hfsm1
  wp_steps
  apply SepWP.done
    (by kpk_norm)
    (by wp_norm_lhs)
  intro hinv2 hfs2
  apply bind_sepWPp_state_mark; intro st2
  have hsp2 : st2.sp = s0.sp - 0xf0#64 := by
    dsimp only [st2]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_sp))
  have htr2 : st2.trace = s0.trace := by
    dsimp only [st2]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_tr))
  have hfiles2 : st2.fs.files = s0.fs.files :=
    files_eq_of_fsInv_trace_eq hfs2 htr2
  dsimp only [st2] at *
  have htoNat_kn : (BitVec.ofNat 64 (keyName x.id).length).toNat = (keyName x.id).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine kpk_call_dirGet_fs hGetFs
    { ret := s0.sp - 0xb0#64, self := x.self, dir := x.kg.oneTime,
      nameA := namePtr, name := keyName x.id, nameRo := false }
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
        (kpkSubMax decStk getStk putStk - getStk) ∗
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
      memRegion (s0.sp - 0xf0#64) 8 ∗
      ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
      ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
      memRegion (s0.sp - 0xc8#64) 24 ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗ ((s0.sp - 0x78#64) ↦₆₄ namePtr) ∗
      ((s0.sp - 0x70#64) ↦₆₄ BitVec.ofNat 64 (keyName x.id).length) ∗
      memRegion (s0.sp - 0x68#64) 4 ∗
      ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
      vecU8Tail A nameCap namePtr (keyName x.id) ∗
      dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      epiloguePre s0 x)
    (ret_pc := fnBase + bv% (88))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp2)
    (by kpk_norm)
    htr2
    hinv2
    hfs2
    (by (try rw [show sm1.sp = s0.sp - 0xf0#64 from hsm1_sp]); kpk_norm)
    (by rw [(cs_x26 hcsm1)]; kpk_norm)
    (by kpk_norm)
    (by
      refine Eq.trans (congrArg BitVec.toNat
        (show _ = BitVec.ofNat 64 (keyName x.id).length by kpk_norm)) ?_
      exact htoNat_kn)
    hkn_lt
    hot_path_lt
    hot_pOk
    hpan
    (by
      rw [hsp2, subStack_split s0.sp hget_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun sm2 gr hpcm2 hrunm2 hspm2 hcsm2 hinvm2 hfsm2 hgr2 => ?_
  have hsm2_sp : sm2.sp = s0.sp - 0xf0#64 := hspm2.trans hsp2
  have hgr2_s0 :
      gr = x.kg.oneTime.get rd s0.fs.files (keyName x.id) ∧ sm2.trace = s0.trace := by
    rcases hgr2 with ⟨h1, h2⟩
    rw [hfiles2] at h1
    exact ⟨h1, h2.trans htr2⟩
  refine sepWPp_conseq ?_
    (hafter58 x s0 sm2
      wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 nameCap namePtr tmp32 gr
      hstk hhi_stk hsp_align hwDot hBkOk hSeenOk hot_chg hlr_chg
      hn_len hn_lt hn_ptr hgr2_s0
      (by kpk_norm) hrunm2 hsm2_sp
      (by rw [(cs_x29 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm1_fp)))
      hinvm2 hfsm2
      (by
        rw [(cs_vregs hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm1)])
        kpk_norm)
      (by rw [(cs_x19 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm1)]; kpk_norm))
      (by rw [(cs_x20 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm1)]; kpk_norm))
      (by rw [(cs_x23 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x23 hcsm1)]; kpk_norm))
      (by rw [(cs_x24 hcsm2)]; kpk_norm)
      (by rw [(cs_x26 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm1)]; kpk_norm))
      (by rw [(cs_x28 hcsm2)]; (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm1)]; kpk_norm))
      hpan hk_final)
  rw [hsp2, subStack_split s0.sp hget_le hhi]
  unfold epiloguePre
  kpk_sep_norm
  sep_focus

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
