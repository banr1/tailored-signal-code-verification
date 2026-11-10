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
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.LastResortErr
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
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

/-! ## Postcondition & Result Unpack Helpers -/

theorem getResultAt_b0_ok_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    getResultAt A (sp - 0xb0#64) (.ok bs) =
      (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64⌝ ∗
        ((sp - 0xb0#64) ↦₆₄ okTagVec) ∗
        ((sp - 0xa8#64) ↦₆₄ cap) ∗
        ((sp - 0xa0#64) ↦₆₄ ptr) ∗
        ((sp - 0x98#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        SpqrV1.ChainProofs.bytesAt false ptr bs ∗
        vecU8Tail A cap ptr bs ∗
        memRegion (sp - 0x90#64) 16) := by
  dsimp only [getResultAt, vecResultAt]
  have e1 : sp - 0xb0#64 + 8#64 = sp - 0xa8#64 := by bv_omega
  have e2 : sp - 0xb0#64 + 0x20#64 = sp - 0x90#64 := by bv_omega
  rw [e1, e2, vecU8_eq_bytes_tail A (sp - 0xa8#64) bs (sp - 0xa0#64) (sp - 0x98#64)
        (by bv_omega) (by bv_omega)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepProp_ext <;>
    (refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
      Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.of_eq (by ac_rfl))))

theorem kpkMark_post_entails {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {stk : Nat}
    (x : KpkMarkPollGhost) (s0 sf : State)
    (res : KpkMarkAns × KyberGhost)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace) :
    (kpkMarkOutAt A x.out res.1 ∗
      dirAt A x.self res.2.oneTime ∗
      dirAt A (x.self + 0x28#64) res.2.lastResort ∗
      kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
      (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
      A.pool ∗ stackAt s0.sp stk) ⊢
      (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf := by
  simp only [kpkMarkPollSpec, Spec.inImage, sepExists_sepConj_left, sepConj_assoc]
  exact Entails.sepExists_right res (Entails.pure_right hres (Entails.refl _))

theorem kpkMark_final_ext {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f0 f1 f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (res : KpkMarkAns × KyberGhost)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace) :
    (kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A x.out res.1 ∗
        dirAt A x.self res.2.oneTime ∗
        dirAt A (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          ((s0.sp - 0xe8#64) ↦₆₄ f0) ∗ ((s0.sp - 0xe0#64) ↦₆₄ f1) ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf := by
  refine sepConj_mono_right ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (restore_kpkMarkStack s0 hstk hhi_stk f0 f1 f2 f3 tmp32)))))))
    (kpkMark_post_entails x s0 sf res hres)

private theorem w0_cbnz_cond_false {v : BitVec 64} (hne : v.setWidth 32 ≠ 0#32) :
    (BitVec.zeroExtend 64 (BitVec.truncate 32 v) == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  apply hne
  have h32 := congrArg (BitVec.setWidth 32) h
  simpa [setWidth_32_setWidth_64] using h32

theorem kpkMark_final_sub {rd : ReadRule} {pathOk : List (BitVec 8) → Prop}
    {A : RustAlloc} {img : Obj.Image} {decStk getStk putStk stk : Nat}
    (hstk : kpkMinStk decStk getStk putStk ≤ stk) (hhi_stk : stk ≤ 2 ^ 64)
    (x : KpkMarkPollGhost) (s0 sf : State)
    (wDot wR0 wR7 wM0 wM6 : BitVec 64)
    (f2 f3 : BitVec 64) (tmp32 : BitVec 32)
    (res : KpkMarkAns × KyberGhost)
    (hres : res = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey ∧
        sf.trace = s0.trace) :
    (kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
      (kpkMarkOutAt A x.out res.1 ∗
        dirAt A x.self res.2.oneTime ∗
        dirAt A (x.self + 0x28#64) res.2.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        (x.baseKeyA ↦ₛ x.baseKey.bytes.toList) ∗
        A.pool ∗
        (memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - kpkMinStk decStk getStk putStk) ∗
          stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
          memRegion (s0.sp - 0xf0#64) 8 ∗
          memRegion (s0.sp - 0xe8#64) 8 ∗
          memRegion (s0.sp - 0xe0#64) 8 ∗
          ((s0.sp - 0xd8#64) ↦₆₄ f2) ∗ ((s0.sp - 0xd0#64) ↦₆₄ f3) ∗
          memRegion (s0.sp - 0xc8#64) 24 ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          memRegion (s0.sp - 0x80#64) 24 ∗
          memRegion (s0.sp - 0x68#64) 4 ∗
          ((s0.sp - 0x64#64) ↦₃₂ tmp32) ∗
          savedCalleeSlots s0))) ⊢
      kpkMarkRoBundle img.base wDot wR0 wR7 wM0 wM6 ∗
        (kpkMarkPollSpec rd pathOk A img stk).post x s0 sf := by
  have hmin : kpkMinStk decStk getStk putStk ≤ 2 ^ 64 := by omega
  have hext : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  rw [subStack_split s0.sp hext hmin,
      ProofLib.memRegion_eight (s0.sp - 0xe8#64),
      ProofLib.memRegion_eight (s0.sp - 0xe0#64)]
  kpk_sep_norm
  refine Entails.sepExists_elim fun f0 => Entails.sepExists_elim fun f1 => ?_
  refine Entails.trans (Entails.of_eq ?_)
    (kpkMark_final_ext hstk hhi_stk x s0 sf wDot wR0 wR7 wM0 wM6 f0 f1 f2 f3 tmp32 res hres)
  ac_rfl

/-! ## 37-Byte Chunk Loop (`+512 .. +556`, `kpk_bcmp_loop_20c`) -/

set_option maxHeartbeats 1200000 in
/-- Inductively steps the `bcmp` loop at `+524 .. +556` (with back-edge `+512 .. +520`) over
`rem + 1` remaining 37-byte chunks of `seenBs`, exiting through `kpk_reused_230` (`+560`) if any
chunk equals `usedBs` (`hasChunk seenBs usedBs = true`) or `kpk_append_37c` (`+892`) once all
chunks have been checked (`hasChunk seenBs usedBs = false`). -/
theorem kpk_bcmp_loop_20c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {rd : ReadRule} {decStk getStk putStk : Nat}
    (hb : (img.base &&& 0xfff#64) = 0#64)
    (hC : AllocContractsX img A ext)
    (hBcmp : HookSat ext cliBcmpName cliBcmpSpec)
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (x : KpkMarkPollGhost) (s0 : State)
    (wR0 wR7 : BitVec 64)
    (usedCap usedPtr : BitVec 64)
    (seenCap seenPtr : BitVec 64) (seenBs : List (BitVec 8))
    (fileCap filePtr : BitVec 64)
    (F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hSeenOk : KpkSeenOk rd s0.fs.files x.kg.lastResort x.id x.signedId x.baseKey)
    (hlr_chg : x.kg.lastResort.changed.length < 2 ^ 32)
    (hget1 : x.kg.oneTime.get rd s0.fs.files (keyName x.id) = .ok [])
    (hget2 : x.kg.lastResort.get rd s0.fs.files (baseKeysName x.id) = .ok seenBs)
    (hu_len : (baseKeyEntry x.signedId x.baseKey).length ≤ usedCap.toNat)
    (hu_lt : usedCap.toNat < 2 ^ 63) (hu_ptr : usedPtr ≠ 0#64)
    (hs_len : seenBs.length ≤ seenCap.toNat) (hs_lt : seenCap.toNat < 2 ^ 63)
    (hs_ptr : seenPtr ≠ 0#64)
    (hf_len : (baseKeysName x.id).length ≤ fileCap.toNat)
    (hf_lt : fileCap.toNat < 2 ^ 63) (hf_ptr : filePtr ≠ 0#64)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hk_res : ∀ (sf : State) (P_f : SepProp) (ans : KpkMarkAns) (kg' : KyberGhost),
      (ans, kg') = kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey →
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A x.out ans ∗
        dirAt A x.self kg'.oneTime ∗
        dirAt A (x.self + 0x28#64) kg'.lastResort ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗
        ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
        memRegion (s0.sp - 0xe8#64) 8 ∗
        memRegion (s0.sp - 0xe0#64) 8 ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        memRegion (s0.sp - 0xc8#64) 24 ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        memRegion (s0.sp - 0x80#64) 24 ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        A.pool ∗ F) →
      Q sf P_f) :
    ∀ (rem : Nat) (s : State) (idx : Nat) (pre suf : List (BitVec 8)) (P : SepProp),
      seenBs = pre ++ suf →
      pre.length = idx * 37 →
      suf.length = (rem + 1) * 37 →
      (∀ j < idx, (seenBs.drop (j * 37)).take 37 ≠ baseKeyEntry x.signedId x.baseKey) →
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (524) →
      s.status = .Running →
      s.sp = s0.sp - 0xf0#64 →
      s.readReg64 .x29 = s0.sp - 0x60#64 →
      s.trace = s0.trace →
      ImgCallInv img s →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      s.readReg64 .x19 = x.fut →
      s.readReg64 .x20 = x.out →
      s.readReg64 .x21 = seenPtr + BitVec.ofNat 64 pre.length →
      s.readReg64 .x22 = BitVec.ofNat 64 seenBs.length →
      s.readReg64 .x24 = usedPtr →
      s.readReg64 .x25 = BitVec.ofNat 64 suf.length →
      s.readReg64 .x26 = x.self →
      s.readReg64 .x27 = seenCap →
      s.readReg64 .x28 = 37#64 →
      (P ⊢
        ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        SpqrV1.ChainProofs.bytesAt false usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        vecU8Tail A usedCap usedPtr (baseKeyEntry x.signedId x.baseKey) ∗
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        epiloguePre s0 x ∗ A.pool ∗ F) →
      SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  let usedBs := baseKeyEntry x.signedId x.baseKey
  have hused37 : usedBs.length = 37 := baseKeyEntry_length x.signedId x.baseKey
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  have hbcmp := kpk_bcmp_ok_at (b := img.base) (ext := ext) hBcmp
  have hreused := @kpk_reused_230 img A ext hb hC
  have happend := @kpk_append_37c img A ext decStk getStk putStk hC hPut
  clear hC hBcmp hPut
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    512 48
  clear hfn
  dsimp only [tripleRatchetProgAtExt] at hbcmp hreused happend ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  intro rem
  induction rem with
  | zero =>
    intro s idx pre suf P hseen hpre hsuf hall_pre hpc hrun hsp hfp htr hinv hvregs
      r19 r20 r21 r22 r24 r25 r26 r27 r28 hfoc
    have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
    have hsuf_lt64 : suf.length < 2 ^ 64 := by rw [hseen, List.length_append] at hs_len; omega
    have hsuf_ge37 : 37 ≤ (BitVec.ofNat 64 suf.length).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]; omega
    have hcsel := csel_min_37_eq hsuf_ge37
    have hhi_f := cmp_37_hi_false hsuf_ge37
    let chunk := suf.take 37
    have hchunk_eq : suf = chunk := (List.take_of_length_le (by omega)).symm
    have hchunk_len : chunk.length = 37 := by dsimp [chunk]; rw [List.length_take]; omega
    refine sepWPp_conseq hfoc ?_
    have hsplit_seen :
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs =
        (seenPtr ↦ₛ pre) ∗ ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := by
      rw [SpqrV1.ChainProofs.bytesAt]
      simp only [Bool.false_eq_true, ite_false]
      rw [hseen, hchunk_eq, pointsToBytes_append]
    rw [hsplit_seen, subStack_split s0.sp hext_le hhi]
    have hused_bytes : SpqrV1.ChainProofs.bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    have hchunk_bytes :
        SpqrV1.ChainProofs.bytesAt false (seenPtr + BitVec.ofNat 64 pre.length) chunk =
        ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := rfl
    rw [hused_bytes]
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "bcmp")) hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_bc
    apply bind_sepWPp_state_mark; intro st_bc
    have hsp_bc : st_bc.sp = s0.sp - 0xf0#64 := by dsimp only [st_bc]; (try kpk_norm)
    dsimp only [st_bc] at *
    refine SepWPp.call_wpp_frozen hbcmp
      (x := CliBcmpCall.mk (seenPtr + BitVec.ofNat 64 pre.length) false chunk usedPtr false usedBs)
      (F := memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        (seenPtr ↦ₛ pre) ∗
        ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        vecU8Tail A usedCap usedPtr usedBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ A.pool ∗ F)
      hinv_bc.1 hinv_bc.2
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_bc)
      (by kpk_norm)
      (by
        intro R' hm
        simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc,
          satisfies_pure_sepConj]
        refine ⟨⟨by kpk_norm, by kpk_norm, ?_, by rw [hused37, hchunk_len]⟩, ?_⟩
        · have : st_bc.readReg64 .x2 = 37#64 := by dsimp only [st_bc]; (try kpk_norm); try rfl
          rw [this, hchunk_len]; rfl
        · refine Satisfies.mono ?_ hm
          kpk_sep_norm
          sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun _ _ ⟨_, hm⟩ => by
        simp only [cliBcmpSpec, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun sm hpcm hrunm hspm hcsm hfz_m hsym_m => ?_
    replace hpcm : sm.pc = fnBase + bv% (556) := by rw [hpcm]; kpk_norm
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_bc
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    have hsm_inv : ImgCallInv img sm := ⟨hfz_m, hsym_m⟩
    simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have hsm_tr : sm.trace = s0.trace := by rw [htrm]; kpk_norm
    by_cases hmatch : chunk = usedBs
    · have hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32 := heq_iff.mpr hmatch
      have hw0_beq : ((sm.readReg64 .x0).setWidth 32 == 0#32) = true := beq_iff_eq.mpr hw0
      have hhas : hasChunk seenBs usedBs = true :=
        hasChunk_true_of_match hused37 hseen hpre hsuf hmatch
      have hans : (KpkMarkAns.reused, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        have hmod0 : seenBs.length % usedBs.length = 0 := by
          rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
        simp [usedBs, hmod0, hhas]
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (560)) hsm_inv
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_230
      refine hreused x s0 _ wR0 wR7
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ F)
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hinv_230
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        hpan
        (by
          rw [hsplit_seen, hused_bytes]
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_r P_r htr_r hsp_r hcs_r hPr =>
          hk_res sf_r P_r .reused x.kg hans htr_r hsp_r hcs_r <| by
            refine Entails.trans hPr ?_
            have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
              (BitVec.ofNat 64 (baseKeysName x.id).length)
            have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
            have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
              (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
              (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
            have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
              (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
              (by bv_omega) (by bv_omega)
            rw [subStack_split s0.sp hext_le hhi]
            kpk_sep_norm
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono hm_e8
                      (sepConj_mono hm_e0
                        (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono hm_c8
                            (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))
            sep_focus
    · have hw0_ne : (sm.readReg64 .x0).setWidth 32 ≠ 0#32 := mt heq_iff.mp hmatch
      have hw0_beq :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
        w0_cbnz_cond_false hw0_ne
      have hx25_sm : sm.readReg64 .x25 = 37#64 := by
        rw [(cs_x25 hcsm)]
        have : st_bc.readReg64 .x25 = BitVec.ofNat 64 suf.length := by dsimp only [st_bc]; kpk_norm
        rw [this, hsuf]
      have hx23_sm : sm.readReg64 .x23 = 37#64 := by
        rw [(cs_x23 hcsm)]
        have : st_bc.readReg64 .x23 =
            (if (37#64 : BitVec 64).ult (BitVec.ofNat 64 suf.length) then 37#64
             else BitVec.ofNat 64 suf.length) := by dsimp only [st_bc]; (try kpk_norm); try rfl
        rw [this, hcsel]
      have hsub_zero : sm.readReg64 .x25 - sm.readReg64 .x23 = 0#64 := by
        rw [hx25_sm, hx23_sm]; rfl
      have hhas_f : hasChunk seenBs usedBs = false := by
        refine hasChunk_false_of_all_ne hused37
          (k := idx + 1) (by rw [hseen, List.length_append, hpre, hsuf]; omega) ?_
        intro j hj
        by_cases hlt_j : j < idx
        · exact hall_pre j hlt_j
        · have hjeq : j = idx := by omega
          subst hjeq
          rw [chunk_at_idx_eq hseen hpre]
          exact hmatch
      have hmod0 : seenBs.length % usedBs.length = 0 := by
        rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
      have hseen32 : seenBs.length < 2 ^ 32 := hSeenOk seenBs hget2 hmod0 hhas_f
      have hans :
          (KpkMarkAns.ok,
            { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) (seenBs ++ usedBs) }) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        simp [usedBs, hmod0, hhas_f]
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (892)) hsm_inv
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_37c
      refine happend x s0 _
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
          ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A x.self x.kg.oneTime ∗ F)
        hhi hlr_chg hused37 hu_len hu_lt hu_ptr hseen32 hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hinv_37c
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
        hpan
        (by
          rw [subStack_split s0.sp hext_le hhi, hsplit_seen, hused_bytes]
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_a P_a htr_a hsp_a hcs_a hPa =>
          hk_res sf_a P_a .ok
            { x.kg with lastResort := x.kg.lastResort.put (baseKeysName x.id) (seenBs ++ usedBs) }
            hans htr_a hsp_a hcs_a <| by
              refine Entails.trans hPa ?_
              have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
                (BitVec.ofNat 64 (baseKeysName x.id).length)
              have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
              have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
                (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
                (by bv_omega) (by bv_omega)
              kpk_sep_norm
              refine Entails.trans ?_
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right
                      (sepConj_mono hm_e8
                        (sepConj_mono hm_e0
                          (sepConj_mono_right (sepConj_mono_right
                            (sepConj_mono_right (sepConj_mono_right
                              (sepConj_mono_left hm_80))))))))))))))
              sep_focus
  | succ rem' ih =>
    intro s idx pre suf P hseen hpre hsuf hall_pre hpc hrun hsp hfp htr hinv hvregs
      r19 r20 r21 r22 r24 r25 r26 r27 r28 hfoc
    have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
    have hsuf_lt64 : suf.length < 2 ^ 64 := by rw [hseen, List.length_append] at hs_len; omega
    have hsuf_ge37 : 37 ≤ (BitVec.ofNat 64 suf.length).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]; omega
    have hcsel := csel_min_37_eq hsuf_ge37
    have hhi_f := cmp_37_hi_false hsuf_ge37
    let chunk := suf.take 37
    let rest := suf.drop 37
    have hchunk_len : chunk.length = 37 := by dsimp [chunk]; rw [List.length_take]; omega
    have hrest_len : rest.length = (rem' + 1) * 37 := by
      dsimp [rest]; rw [List.length_drop]; omega
    refine sepWPp_conseq hfoc ?_
    have hsplit_seen :
        SpqrV1.ChainProofs.bytesAt false seenPtr seenBs =
        (seenPtr ↦ₛ pre) ∗ ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) ∗
          ((seenPtr + BitVec.ofNat 64 pre.length + 37#64) ↦ₛ rest) := by
      rw [SpqrV1.ChainProofs.bytesAt]
      simp only [Bool.false_eq_true, ite_false]
      rw [hseen, ← List.take_append_drop 37 suf, pointsToBytes_append, pointsToBytes_append,
        hchunk_len]
    rw [hsplit_seen, subStack_split s0.sp hext_le hhi]
    have hused_bytes : SpqrV1.ChainProofs.bytesAt false usedPtr usedBs = (usedPtr ↦ₛ usedBs) := rfl
    have hchunk_bytes :
        SpqrV1.ChainProofs.bytesAt false (seenPtr + BitVec.ofNat 64 pre.length) chunk =
        ((seenPtr + BitVec.ofNat 64 pre.length) ↦ₛ chunk) := rfl
    rw [hused_bytes]
    have hcsel2 : (if (37#64).ult (BitVec.ofNat 64 ((rem' + 1 + 1) * 37)) = true
        then 37#64 else BitVec.ofNat 64 ((rem' + 1 + 1) * 37)) = 37#64 := hsuf ▸ hcsel
    have hhi_f2 : (BitVec.ofNat 64 ((rem' + 1 + 1) * 37)).ult 37#64 = false := hsuf ▸ hhi_f
    apply SepWPp.of_sepWP_inImage
      (mid := fnBase +
        bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "bcmp")) hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_bc
    apply bind_sepWPp_state_mark; intro st_bc
    have hsp_bc : st_bc.sp = s0.sp - 0xf0#64 := by dsimp only [st_bc]; (try kpk_norm)
    dsimp only [st_bc] at *
    refine SepWPp.call_wpp_frozen hbcmp
      (x := CliBcmpCall.mk (seenPtr + BitVec.ofNat 64 pre.length) false chunk usedPtr false usedBs)
      (F := memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
          (kpkSubMax decStk getStk putStk - extHookStack) ∗
        (seenPtr ↦ₛ pre) ∗
        ((seenPtr + BitVec.ofNat 64 pre.length + 37#64) ↦ₛ rest) ∗
        ((reusedStrAddr img.base) ↦₆₄ᵣ wR0) ∗
        ((reusedStrAddr img.base + 7#64) ↦₆₄ᵣ wR7) ∗
        ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
        ((s0.sp - 0xe0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xd8#64) ↦₆₄ filePtr) ∗
        ((s0.sp - 0xd0#64) ↦₆₄ fileCap) ∗
        ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
        ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
        ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
        memRegion (s0.sp - 0xb0#64) 48 ∗
        ((s0.sp - 0x80#64) ↦₆₄ usedCap) ∗
        ((s0.sp - 0x78#64) ↦₆₄ usedPtr) ∗
        ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
        vecU8Tail A usedCap usedPtr usedBs ∗
        vecU8Tail A seenCap seenPtr seenBs ∗
        SpqrV1.ChainProofs.bytesAt false filePtr (baseKeysName x.id) ∗
        vecU8Tail A fileCap filePtr (baseKeysName x.id) ∗
        dirAt A x.self x.kg.oneTime ∗
        dirAt A (x.self + 0x28#64) x.kg.lastResort ∗
        epiloguePre s0 x ∗ A.pool ∗ F)
      hinv_bc.1 hinv_bc.2
      (by kpk_norm)
      (by kpk_norm)
      (spAligned_sub_f0 hsp_align hsp_bc)
      (by kpk_norm)
      (by
        intro R' hm
        simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc,
          satisfies_pure_sepConj]
        refine ⟨⟨by kpk_norm, by kpk_norm, ?_, by rw [hused37, hchunk_len]⟩, ?_⟩
        · have : st_bc.readReg64 .x2 = 37#64 := by dsimp only [st_bc]; (try kpk_norm); try rfl
          rw [this, hchunk_len]; rfl
        · refine Satisfies.mono ?_ hm
          kpk_sep_norm
          sep_focus)
      (fun _ _ _ _ hm => allowPanic_not_exited hm)
      (fun _ _ ⟨_, hm⟩ => by
        simp only [cliBcmpSpec, satisfies_pure_sepConj] at hm
        exact hm.1.elim)
      fun sm hpcm hrunm hspm hcsm hfz_m hsym_m => ?_
    replace hpcm : sm.pc = fnBase + bv% (556) := by rw [hpcm]; kpk_norm
    have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_bc
    have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
    have hsm_inv : ImgCallInv img sm := ⟨hfz_m, hsym_m⟩
    simp only [cliBcmpSpec, hchunk_bytes, hused_bytes, hsp_bc, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨heq_iff, htrm⟩ => ?_
    have hsm_tr : sm.trace = s0.trace := by rw [htrm]; kpk_norm
    by_cases hmatch : chunk = usedBs
    · have hw0 : (sm.readReg64 .x0).setWidth 32 = 0#32 := heq_iff.mpr hmatch
      have hw0_beq : ((sm.readReg64 .x0).setWidth 32 == 0#32) = true := beq_iff_eq.mpr hw0
      have hhas : hasChunk seenBs usedBs = true :=
        hasChunk_true_of_match hused37 hseen hpre hsuf hmatch
      have hans : (KpkMarkAns.reused, x.kg) =
          kpkMarkOf rd s0.fs.files x.kg x.id x.signedId x.baseKey := by
        unfold kpkMarkOf
        rw [hget1, hget2]
        have hmod0 : seenBs.length % usedBs.length = 0 := by
          rw [hseen, List.length_append, hpre, hsuf, hused37]; omega
        simp [usedBs, hmod0, hhas]
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (560)) hsm_inv
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_230
      refine hreused x s0 _ wR0 wR7
        usedCap usedPtr usedBs seenCap seenPtr seenBs fileCap filePtr (baseKeysName x.id) _
        (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
            (kpkSubMax decStk getStk putStk - extHookStack) ∗
          ((s0.sp - 0xe8#64) ↦₆₄ BitVec.ofNat 64 (baseKeysName x.id).length) ∗
          ((s0.sp - 0xc8#64) ↦₆₄ seenCap) ∗
          ((s0.sp - 0xc0#64) ↦₆₄ seenPtr) ∗
          ((s0.sp - 0xb8#64) ↦₆₄ BitVec.ofNat 64 seenBs.length) ∗
          memRegion (s0.sp - 0xb0#64) 48 ∗
          ((s0.sp - 0x70#64) ↦₆₄ 37#64) ∗
          dirAt A x.self x.kg.oneTime ∗
          dirAt A (x.self + 0x28#64) x.kg.lastResort ∗ F)
        hu_len hu_lt hu_ptr hs_len hs_lt hs_ptr hf_len hf_lt hf_ptr
        (by kpk_norm)
        (by kpk_norm)
        hsp_align
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hinv_230
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        hpan
        (by
          rw [hsplit_seen, hused_bytes]
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)
        fun sf_r P_r htr_r hsp_r hcs_r hPr =>
          hk_res sf_r P_r .reused x.kg hans htr_r hsp_r hcs_r <| by
            refine Entails.trans hPr ?_
            have hm_e8 := pointsTo64_entails_memRegion (s0.sp - 0xe8#64)
              (BitVec.ofNat 64 (baseKeysName x.id).length)
            have hm_e0 := pointsTo64_entails_memRegion (s0.sp - 0xe0#64) seenPtr
            have hm_c8 := header3_entails_memRegion24 (s0.sp - 0xc8#64)
              (s0.sp - 0xc0#64) (s0.sp - 0xb8#64) seenCap seenPtr
              (BitVec.ofNat 64 seenBs.length) (by bv_omega) (by bv_omega)
            have hm_80 := header3_entails_memRegion24 (s0.sp - 0x80#64)
              (s0.sp - 0x78#64) (s0.sp - 0x70#64) usedCap usedPtr 37#64
              (by bv_omega) (by bv_omega)
            rw [subStack_split s0.sp hext_le hhi]
            kpk_sep_norm
            refine Entails.trans ?_
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right
                    (sepConj_mono hm_e8
                      (sepConj_mono hm_e0
                        (sepConj_mono_right (sepConj_mono_right
                          (sepConj_mono hm_c8
                            (sepConj_mono_right (sepConj_mono_left hm_80))))))))))))))
            sep_focus
    · have hw0_ne : (sm.readReg64 .x0).setWidth 32 ≠ 0#32 := mt heq_iff.mp hmatch
      have hw0_beq :
          (BitVec.zeroExtend 64 (BitVec.truncate 32 (sm.readReg64 (Reg.gpr 0#5))) == 0#64) = false :=
        w0_cbnz_cond_false hw0_ne
      have hx25_sm : sm.readReg64 .x25 = BitVec.ofNat 64 suf.length := by
        rw [(cs_x25 hcsm)]; kpk_norm
      have hx23_sm : sm.readReg64 .x23 = 37#64 := by
        rw [(cs_x23 hcsm)]; kpk_norm
      have hx21_sm : sm.readReg64 .x21 = seenPtr + BitVec.ofNat 64 pre.length := by
        rw [(cs_x21 hcsm)]; kpk_norm
      have hsub_rest : sm.readReg64 .x25 - sm.readReg64 .x23 = BitVec.ofNat 64 rest.length := by
        rw [hx25_sm, hx23_sm]
        apply BitVec.eq_of_toNat_eq
        have hs1 : (BitVec.ofNat 64 suf.length).toNat = suf.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hsuf_lt64]
        have hs2 : (BitVec.ofNat 64 rest.length).toNat = rest.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        have h37 : (37#64 : BitVec 64).toNat = 37 := rfl
        rw [BitVec.toNat_sub_of_le ((BitVec.le_def (x := 37#64) (y := BitVec.ofNat 64 suf.length)).mpr hsuf_ge37),
          hs1, h37, hs2]
        omega
      have hrest_ne0_1 : (BitVec.ofNat 64 rest.length == 0#64) = false := by
        apply beq_false_of_ne
        intro h0
        have ht := congrArg BitVec.toNat h0
        have hs2 : (BitVec.ofNat 64 rest.length).toNat = rest.length := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hs2] at ht
        change rest.length = 0 at ht
        omega
      have hrest_ne0_2 : (BitVec.ofNat 64 ((rem' + 1) * 37) == 0#64) = false :=
        hrest_len ▸ hrest_ne0_1
      have hadd_pre : sm.readReg64 .x21 + sm.readReg64 .x23 =
          seenPtr + BitVec.ofNat 64 (pre ++ chunk).length := by
        rw [hx21_sm, hx23_sm, List.length_append, hchunk_len, BitVec.ofNat_add]; bv_omega
      clear hx25_sm hx23_sm hx21_sm
      apply SepWPp.of_sepWP_inImage
        (mid := fnBase + bv% (524)) hsm_inv
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_next
      refine ih _ (idx + 1) (pre ++ chunk) rest _
        (by rw [hseen, ← List.take_append_drop 37 suf, List.append_assoc])
        (by rw [List.length_append, hpre, hchunk_len]; omega)
        hrest_len
        (by
          intro j hj
          by_cases hlt_j : j < idx
          · exact hall_pre j hlt_j
          · have hjeq : j = idx := by omega
            subst hjeq
            rw [chunk_at_idx_eq hseen hpre]
            exact hmatch)
        (by kpk_norm)
        (by kpk_norm)
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_sp)))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x29 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try ((first | rfl | exact hsm_tr)))
        hinv_next
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_vregs hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x19 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x20 hcsm)]; kpk_norm))
        (by simp only [wp_norm, arm64_norm])
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x22 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x24 hcsm)]; kpk_norm))
        (by simp only [wp_norm, arm64_norm, hrest_len])
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x26 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x27 hcsm)]; kpk_norm))
        (by (try conv_lhs => simp only [wp_norm, arm64_norm, *]); try (rw [(cs_x28 hcsm)]; kpk_norm))
        (by
          rw [subStack_split s0.sp hext_le hhi, hsplit_seen, hused_bytes]
          unfold epiloguePre
          kpk_sep_norm
          sep_focus)

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
