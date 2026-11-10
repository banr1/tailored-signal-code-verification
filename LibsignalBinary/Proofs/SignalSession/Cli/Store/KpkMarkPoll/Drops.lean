/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Calls
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Epilogue
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Fetches
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero setWidth_32_setWidth_64

macro_rules
  | `(tactic| kpk_norm) =>
    `(tactic|
      ((try with_reducible rfl)
       (try simp +zetaDelta only [wp_norm])
       (try simp +zetaDelta only [arm64_norm])
       (try simp +zetaDelta only [*])
       (try with_reducible rfl)
       try bv_omega))

theorem cs_x19 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x19 = s.readReg64 .x19 := h.1
theorem cs_x20 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x20 = s.readReg64 .x20 := h.2.1
theorem cs_x21 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x21 = s.readReg64 .x21 := h.2.2.1
theorem cs_x22 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x22 = s.readReg64 .x22 := h.2.2.2.1
theorem cs_x23 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x23 = s.readReg64 .x23 := h.2.2.2.2.1
theorem cs_x24 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x24 = s.readReg64 .x24 := h.2.2.2.2.2.1
theorem cs_x25 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x25 = s.readReg64 .x25 := h.2.2.2.2.2.2.1
theorem cs_x26 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x26 = s.readReg64 .x26 := h.2.2.2.2.2.2.2.1
theorem cs_x27 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x27 = s.readReg64 .x27 := h.2.2.2.2.2.2.2.2.1
theorem cs_x28 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x28 = s.readReg64 .x28 := h.2.2.2.2.2.2.2.2.2.1
theorem cs_x29 {s sm : State} (h : CalleeSavedPreserved s sm) : sm.readReg64 .x29 = s.readReg64 .x29 := h.2.2.2.2.2.2.2.2.2.2.1
theorem cs_vregs {s sm : State} (h : CalleeSavedPreserved s sm) : calleeSavedVRegs sm = calleeSavedVRegs s := h.2.2.2.2.2.2.2.2.2.2.2

/-! ## Shared `Dir::put::<String>` Tail (`+184 .. +192` → `kpk_epilogue_330`) & Dual-`Vec` Drops -/

/-- Shared `Ok(())` tail (`+184 .. +192` → `kpk_epilogue_330`) used by both `one_time` nonempty
(`dirA = x.self`, `nameV = s0.sp - 0x80#64`, `bytesV = s0.sp - 0xb0#64`) and `last_resort` append
(`dirA = x.self + 0x28#64`, `nameV = s0.sp - 0xb0#64`, `bytesV = s0.sp - 0xc8#64`). -/
theorem kpk_put_and_epilogue_b8 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {decStk getStk putStk : Nat}
    (hPut : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr dirPutName)
      (dirPutSpec A img putStk))
    (x : KpkMarkPollGhost) (s0 s : State)
    (dirA nameV bytesV : BitVec 64)
    (dir : DirGhost) (name bytes : List (BitVec 8))
    (P F : SepProp) {Q Qp : State → SepProp → Prop}
    (hhi : kpkMinStk decStk getStk putStk ≤ 2 ^ 64)
    (hlen : dir.changed.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (184))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (htr : s.trace = s0.trace)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = dirA)
    (hx1 : s.readReg64 .x1 = nameV)
    (hx2 : s.readReg64 .x2 = bytesV)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hpan : ∀ sf P_f, (allocFailedIn s0 sf ∧ s0.trace <+: sf.trace) → Qp sf P_f)
    (hfoc : P ⊢
      dirAt A dirA dir ∗
      vecU8 A nameV name ∗
      vecU8 A bytesV bytes ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
      epiloguePre s0 x ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s0.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ kpkMarkOutAt A x.out .ok ∗
        dirAt A dirA (dir.put name bytes) ∗
        memRegion nameV 24 ∗ memRegion bytesV 24 ∗
        stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗
        kpkMarkBoxAt x.fut x.self x.baseKeyA x.id x.signedId 1#8 ∗
        savedCalleeSlots s0 ∗ A.pool ∗ F) →
      Q sf P_f) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P Q Qp := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hput_le : putStk ≤ kpkSubMax decStk getStk putStk := by unfold kpkSubMax; omega
  have hext_le : extHookStack ≤ kpkSubMax decStk getStk putStk := by
    unfold kpkSubMax doReserveStackX finishGrowStackX; omega
  rw [← dirPut_fnAddr_eq] at hPut
  have hep := @kpk_epilogue_330 img ext
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    184 12
  dsimp only [tripleRatchetProgAtExt] at hPut hep hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  apply SepWPp.of_sepWP_inImage
    (mid := fnBase - bv% (ls_rel%
      "<libsignal_cli::stores::Dir>::put::<alloc::string::String>"
      "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    hinv
  wp_steps
  apply SepWP.done (by kpk_norm) (by wp_norm_lhs)
  intro hinv_put
  apply bind_sepWPp_state_mark; intro st_put
  have hsp_put : st_put.sp = s0.sp - 0xf0#64 := by kpk_norm
  refine kpk_call_dirPut hPut ⟨dirA, dir, nameV, name, bytesV, bytes⟩
    (memRegion (s0.sp - 0xf0#64 - BitVec.ofNat 64 (kpkSubMax decStk getStk putStk))
      (kpkSubMax decStk getStk putStk - putStk) ∗ epiloguePre s0 x ∗ F)
    (ret_pc := fnBase + bv% (188))
    (by kpk_norm)
    (by kpk_norm)
    (spAligned_sub_f0 hsp_align hsp_put)
    (by kpk_norm)
    (by kpk_norm)
    hinv_put
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    hlen
    hpan
    (by
      refine Entails.trans hfoc ?_
      rw [hsp_put, subStack_split s0.sp hput_le hhi]
      kpk_sep_norm
      sep_focus)
    fun sm hpcm hrunm hspm hcsm hinvm htrm => ?_
  have hsm_sp : sm.sp = s0.sp - 0xf0#64 := hspm.trans hsp_put
  have hsm_al : sm.spAligned = true := spAligned_sub_f0 hsp_align hsm_sp
  have hsm_19 : sm.readReg64 .x19 = x.fut := by
    rw [(cs_x19 hcsm)]; kpk_norm
  have hsm_20 : sm.readReg64 .x20 = x.out := by
    rw [(cs_x20 hcsm)]; kpk_norm
  have hsm_v : calleeSavedVRegs sm = calleeSavedVRegs s0 := by
    rw [(cs_vregs hcsm)]; kpk_norm
  have hsm_tr : sm.trace = s0.trace := by
    rw [htrm]; kpk_norm
  apply SepWPp.of_sepWP_ret
  apply SepWP.seq_inImage (mid := fnBase + bv% (816)) hinvm
  wp_steps
  apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
  intro _hinv_330
  refine hep x s0 _ 0xFFFFFFFFFFFFFFFE#64
    (sm.readReg64 .x27) (sm.readReg64 .x25) (sm.readReg64 .x22)
    (sm.readReg64 .x28) (sm.readReg64 .x23) (sm.readReg64 .x26) _
    (dirAt A dirA (dir.put name bytes) ∗
      memRegion nameV 24 ∗ memRegion bytesV 24 ∗
      stackAt (s0.sp - 0xf0#64) (kpkSubMax decStk getStk putStk) ∗ A.pool ∗ F)
    (by kpk_norm)
    (by kpk_norm)
    hsp_align
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by kpk_norm)
    (by
      rw [hsp_put, subStack_split s0.sp hput_le hhi]
      unfold epiloguePre
      kpk_sep_norm
      sep_focus)
    fun sf P_f htr_f hsp_f hcs_f hPf =>
      hk sf P_f (htr_f.trans ((by kpk_norm : _ = sm.trace).trans hsm_tr))
        hsp_f hcs_f <| by
          refine Entails.trans hPf ?_
          unfold epilogueOut
          refine Entails.trans ?_
            (sepConj_mono_left
              (kpkMarkOutAt_ok_reassemble A x.out
                (sm.readReg64 .x27) (sm.readReg64 .x25) (sm.readReg64 .x22) (sm.readReg64 .x26)
                ((sm.readReg64 .x28).setWidth 8) ((sm.readReg64 .x23).setWidth 32)
                (((sm.readReg64 .x23) >>> 32).setWidth 16) (((sm.readReg64 .x23) >>> 48).setWidth 8)))
          sep_focus

/-- Dual-`Vec` drop block at `+108 .. +144` (`one_time` nonempty: drops `bytes` then `name`,
joining at `+148`). -/
theorem kpk_drop_both_6c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {post : State → SepProp → Prop}
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (108))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      SpqrV1.ChainProofs.bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (148) →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      ImgCallInv img sm →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP (tripleRatchetProgAtExt img.base ext) ret sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool ∗ F)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdealloc := kpk_dealloc_ok_at hC
  clear hC
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    108 40
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc hk ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  have hsecond : ∀ (s1 : State) (Q1 : SepProp),
      s1.pc = fnBase + bv% (128) →
      s1.status = .Running →
      s1.sp = s0.sp - 0xf0#64 →
      ImgCallInv img s1 →
      s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = namePtr →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (Q1 ⊢
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool ∗ F) →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) ret s1 Q1 post := by
    intro s1 Q1 hpc1 hrun1 hsp1 hinv1 htr1 r19 r20 r23 r24 r26 r28 r29 hv1 hQ1
    have hsp_al1 : s1.spAligned = true := spAligned_sub_f0 hsp_align hsp1
    refine SepWP.weaken_pre hQ1 ?_
    by_cases hncap : nameCap = 0#64
    · subst hncap
      refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (148)) hinv1
      wp_steps
      apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv2
      refine SepWP.weaken_pre (by sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hinv2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
    · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
      have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
      refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_dealloc"))
        hinv1
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_da2
      have ⟨hF_da2, hsym_da2⟩ := hinv_da2
      apply SepWP.seq_inImage (mid := fnBase + bv% (148)) hinv_da2
      wp_call hdealloc (namePtr, nameCap.toNat, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hinv2
      refine SepWP.weaken_pre (by rw [hsp1]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hinv2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.fold (vecU8_free_zero A bytesPtr hblen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (128)) hinv
    wp_steps
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hinv1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_sep_focus)
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap hblen hblt) (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_da1
    have ⟨hF_da1, hsym_da1⟩ := hinv_da1
    apply SepWP.seq_inImage (mid := fnBase + bv% (128)) hinv_da1
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hinv1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_sep_focus)

private theorem kpk_drop_both_f0_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {post : State → SepProp → Prop}
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (240))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      SpqrV1.ChainProofs.bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (280) →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      ImgCallInv img sm →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (280)) sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool ∗ F)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (280)) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_f0 hsp_align hsp
  have hdealloc := kpk_dealloc_ok_at hC
  clear hC
  have hfn : libsignalSessionCode.fnOff kpkMarkPollName =
      num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}") :=
    kpkMarkPoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliKpkMarkPollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"))
    240 40
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc hk ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    kpkMarkPollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  have hsecond : ∀ (s1 : State) (Q1 : SepProp),
      s1.pc = fnBase + bv% (260) →
      s1.status = .Running →
      s1.sp = s0.sp - 0xf0#64 →
      ImgCallInv img s1 →
      s1.trace = s.trace →
      s1.readReg64 .x19 = s.readReg64 .x19 →
      s1.readReg64 .x20 = s.readReg64 .x20 →
      s1.readReg64 .x23 = s.readReg64 .x23 →
      s1.readReg64 .x24 = namePtr →
      s1.readReg64 .x26 = s.readReg64 .x26 →
      s1.readReg64 .x28 = s.readReg64 .x28 →
      s1.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs s1 = calleeSavedVRegs s0 →
      (Q1 ⊢
        ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
        SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
        vecU8Tail A nameCap namePtr nameBs ∗
        stackAt (s0.sp - 0xf0#64) extHookStack ∗
        A.pool ∗ F) →
      SepWP (libsignalSessionCode.rebase img.base (Rust.withPanics ext))
        (fnBase + bv% (280)) s1 Q1 post := by
    intro s1 Q1 hpc1 hrun1 hsp1 hinv1 htr1 r19 r20 r23 r24 r26 r28 r29 hv1 hQ1
    have hsp_al1 : s1.spAligned = true := spAligned_sub_f0 hsp_align hsp1
    refine SepWP.weaken_pre hQ1 ?_
    by_cases hncap : nameCap = 0#64
    · subst hncap
      refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
      apply SepWP.seq_inImage (mid := fnBase + bv% (280)) hinv1
      wp_steps
      apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv2
      refine SepWP.weaken_pre (by sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hinv2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
    · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
      have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
      refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
      apply SepWP.seq_inImage
        (mid := fnBase + bv% (ls_rel%
          "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
          "__rustc::__rust_dealloc"))
        hinv1
      wp_steps
      apply SepWP.done (by kpk_norm) (by kpk_norm)
      intro hinv_da2
      have ⟨hF_da2, hsym_da2⟩ := hinv_da2
      apply SepWP.seq_inImage (mid := fnBase + bv% (280)) hinv_da2
      wp_call hdealloc (namePtr, nameCap.toNat, 1)
      apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      intro hinv2
      refine SepWP.weaken_pre (by rw [hsp1]; sep_focus)
        (hk _ (by kpk_norm) (by kpk_norm)
          (by kpk_norm) hinv2 (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm) (by kpk_norm)
          (by kpk_norm))
  by_cases hbcap : bytesCap = 0#64
  · subst hbcap
    refine SepWP.fold (vecU8_free_zero A bytesPtr hblen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (260)) hinv
    wp_steps
    apply bind_sepWP_state_mark; intro _st; apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hinv1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_sep_focus)
  · obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
    have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
    refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap hblen hblt) (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by kpk_norm) (by kpk_norm)
    intro hinv_da1
    have ⟨hF_da1, hsym_da1⟩ := hinv_da1
    apply SepWP.seq_inImage (mid := fnBase + bv% (260)) hinv_da1
    wp_call hdealloc (bytesPtr, bytesCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1
    exact hsecond _ _ (by kpk_norm) (by kpk_norm)
      (by kpk_norm) hinv1 (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm)
      (by kpk_norm) (by kpk_norm) (by kpk_sep_focus)

/-- Dual-`Vec` drop block at `+240 .. +276` (`one_time` empty: drops `bytes` then `name`,
preserving `FsInv` across `Steps` via `TraceFsSound`, joining at `+280`). -/
theorem kpk_drop_both_f0 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {Q Qp : State → SepProp → Prop}
    {F0 : FsFiles} {T0 : List TraceEvent}
    (hFs : TraceFsSound (tripleRatchetProgAtExt img.base ext))
    (hfs_s : FsInv F0 T0 s)
    (hblen : bytesBs.length ≤ bytesCap.toNat) (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat) (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (240))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xf0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx27 : s.readReg64 .x27 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx24 : s.readReg64 .x24 = namePtr)
    (hfoc : P ⊢
      SpqrV1.ChainProofs.bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xf0#64) extHookStack ∗
      A.pool ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr kpkMarkPollName + bv% (280) →
      sm.status = .Running →
      sm.sp = s0.sp - 0xf0#64 →
      ImgCallInv img sm →
      FsInv F0 T0 sm →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x28 = s.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        (((s0.sp - 0x80#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xf0#64) extHookStack ∗
          A.pool ∗ F)
        Q Qp) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q Qp :=
  sepWPp_of_sepWP_fs hFs hinv hfs_s <|
    kpk_drop_both_f0_wp hC s0 s bytesCap bytesPtr bytesBs nameCap namePtr nameBs P F
      hblen hblt _hbptr hnlen hnlt _hnptr hpc hrun hsp_align hsp hfp hinv hvregs
      hx27 hx25 hx24 hfoc fun sm hpcm hrunm hspm hinvm htrm r19 r20 r23 r26 r28 r29 hvm =>
        SepWP.done hpcm hrunm fun _ hfs_sm =>
          hk sm hpcm hrunm hspm hinvm hfs_sm htrm r19 r20 r23 r26 r28 r29 hvm

end CryptoVerification.SignalSession.Cli.Store.KpkMarkPoll.Helpers
