/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Layout
import LibsignalBinary.Proofs.SignalSession.Cli.Store.PkRemovePoll.Fetches
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Defs
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoop
import ProofLib.SepLogic.WPp

/-!
# Epilogue and Deallocation Blocks for `remove_pre_key::{closure#0}`

Shared return epilogue (`+0x108 .. +0x13c`), optional `name` deallocation tail (`+0x0f4 .. +0x104`),
and nonempty `bytes` + `name` deallocation block (`+0x06c .. +0x090`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout CryptoVerification.SignalSession.Cli

attribute [local irreducible] Program.fetch Program.externAt?

theorem extractLsb_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  ext i _hi_lt
  simp

theorem extractLsb_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  ext i _hi_lt
  simp

theorem setWidth_64_append (hi lo : BitVec 64) :
    BitVec.setWidth 64 (hi ++ lo) = lo := by
  ext i _hi_lt
  simp

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.add_zero BitVec.zero_add
  BitVec.toNat_zero calleeSavedVRegs_writeVReg128_0 setWidth_32_setWidth_64
  extractLsb_0_64_append extractLsb_64_64_append setWidth_64_append

/-- Shared epilogue (`+0x108 .. +0x13c`): loads `q0` from `[sp]`, writes `[out .. out + 0x30]`,
sets `[fut + 0xc] := 1`, restores all saved registers and `sp`, and returns to `s0.readReg64 .lr`. -/
theorem pkrm_epilogue_108 {img : Obj.Image} {ext : String → Option (State → State)}
    (x : PkPollGhost) (s0 s : State)
    (w0 w1 w2 w3 : BitVec 64) (q_sp0 : BitVec 128)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (264))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = w0)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = w2)
    (hx27 : s.readReg64 .x27 = w3)
    (hfoc : P ⊢ epiloguePre s0 x q_sp0 ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 q_sp0 ∗ F) →
      post sf P_f) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    264 56
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  unfold epiloguePre pkBoxAt savedCalleeSlots
  rw [sret48_epilogue_split x.out]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun o0 => SepWP.exists_elim fun o1 =>
    SepWP.exists_elim fun o2 => SepWP.exists_elim fun o3 =>
    SepWP.exists_elim fun oq => ?_
  have hb8 : s0.sp - 0xc0#64 + 8#64 = s0.sp - 184#64 := by bv_omega
  unfold Arm64.pointsTo128
  simp only [hb8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine hk _ _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [CalleeSavedPreserved, arm64_norm, *]) ?_
  unfold epilogueOut savedCalleeSlots pkBoxAt Arm64.pointsTo128
  simp only [hb8, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_focus

/-- Tail block at `+0x0f4 .. +0x104`: loads `nameCap` from `[x29 - 0x18]`, frees `name` if
`nameCap ≠ 0#64`, and chains into `pkrm_epilogue_108`. -/
theorem pkrm_finish_f4 {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (x : PkPollGhost) (s0 s : State)
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (w0 w1 w2 w3 : BitVec 64) (q_sp0 : BitVec 128)
    (P F : SepProp) {post : State → SepProp → Prop}
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (244))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hx19 : s.readReg64 .x19 = x.fut)
    (hx20 : s.readReg64 .x20 = x.out)
    (hx26 : s.readReg64 .x26 = w0)
    (hx24 : s.readReg64 .x24 = w1)
    (hx25 : s.readReg64 .x25 = w2)
    (hx27 : s.readReg64 .x27 = w3)
    (hfoc : P ⊢ ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      epiloguePre s0 x q_sp0 ∗ A.pool ∗ F)
    (hk : ∀ (sf : State) (P_f : SepProp),
      sf.trace = s.trace →
      sf.sp = s0.sp →
      CalleeSavedPreserved s0 sf →
      (P_f ⊢ epilogueOut s0 x w0 w1 w2 w3 q_sp0 ∗
        ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
        stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F) →
      post sf P_f) :
    SepWP (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .lr) s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  have hdealloc := pkrm_dealloc_ok_at hC
  have hep := @pkrm_epilogue_108 img ext
  clear hC
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    244 20
  dsimp only [tripleRatchetProgAtExt] at hep hdealloc hpc ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (264)) hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro _hinv_108
    refine hep x s0 _ w0 w1 w2 w3 q_sp0 _
      (((s0.sp - 0x78#64) ↦₆₄ 0#64) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))
  · obtain ⟨hcap_pos, hpow1, hcap_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_da
    have ⟨hF_da, hsym_da⟩ := hinv_da
    apply SepWP.seq_inImage (mid := fnBase + bv% (264)) hinv_da
    wp_call hdealloc (namePtr, nameCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro _hinv_108
    refine hep x s0 _ w0 w1 w2 w3 q_sp0 _
      (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗ stackAt (s0.sp - 0xc0#64) extHookStack ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      hsp_align
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *])
      (by unfold epiloguePre; simp only [sepConj_assoc]; sep_focus)
      fun sf P_f htr_f hsp_f hcs_f hPf =>
        hk sf P_f (htr_f.trans (by simp only [arm64_norm, *])) hsp_f hcs_f
          (Entails.trans hPf (Entails.of_eq (by ac_rfl)))

/-- Deallocation block on nonempty bytes (`+0x06c .. +0x090`): frees `bytes` (`bytesCap ≠ 0#64`)
and `name` (if `nameCap ≠ 0#64`), joining both sub-arms at `+0x094` (`148`). -/
theorem pkrm_drop_both_6c {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : AllocContractsX img A ext)
    (s0 s : State)
    (bytesCap bytesPtr : BitVec 64) (bytesBs : List (BitVec 8))
    (nameCap namePtr : BitVec 64) (nameBs : List (BitVec 8))
    (P F : SepProp) {ret : BitVec 64} {post : State → SepProp → Prop}
    (hbcap : bytesCap ≠ 0#64)
    (hblen : bytesBs.length ≤ bytesCap.toNat)
    (hblt : bytesCap.toNat < 2 ^ 63)
    (_hbptr : bytesPtr ≠ 0#64)
    (hnlen : nameBs.length ≤ nameCap.toNat)
    (hnlt : nameCap.toNat < 2 ^ 63)
    (_hnptr : namePtr ≠ 0#64)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (108))
    (hrun : s.status = .Running)
    (hsp_align : s0.sp &&& 15#64 = 0#64)
    (hsp : s.sp = s0.sp - 0xc0#64)
    (hfp : s.readReg64 .x29 = s0.sp - 0x60#64)
    (hinv : ImgCallInv img s)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx24 : s.readReg64 .x24 = bytesCap)
    (hx25 : s.readReg64 .x25 = bytesPtr)
    (hx21 : s.readReg64 .x21 = namePtr)
    (hfoc : P ⊢
      SpqrV1.ChainProofs.bytesAt false bytesPtr bytesBs ∗
      vecU8Tail A bytesCap bytesPtr bytesBs ∗
      ((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
      SpqrV1.ChainProofs.bytesAt false namePtr nameBs ∗
      vecU8Tail A nameCap namePtr nameBs ∗
      stackAt (s0.sp - 0xc0#64) extHookStack ∗
      A.pool ∗ F)
    (hk : ∀ sm : State,
      sm.pc = (tripleRatchetProgAtExt img.base ext).fnAddr pkRemovePollName + bv% (148) →
      sm.status = .Running →
      sm.sp = s0.sp - 0xc0#64 →
      ImgCallInv img sm →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x20 = s.readReg64 .x20 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x24 = bytesCap →
      sm.readReg64 .x25 = bytesPtr →
      sm.readReg64 .x26 = s.readReg64 .x26 →
      sm.readReg64 .x27 = s.readReg64 .x27 →
      sm.readReg64 .x28 = s0.readReg64 .x28 →
      sm.readReg64 .x29 = s0.sp - 0x60#64 →
      calleeSavedVRegs sm = calleeSavedVRegs s0 →
      SepWP (tripleRatchetProgAtExt img.base ext) ret sm
        (((s0.sp - 0x78#64) ↦₆₄ nameCap) ∗
          stackAt (s0.sp - 0xc0#64) extHookStack ∗
          A.pool ∗ F)
        post) :
    SepWP (tripleRatchetProgAtExt img.base ext) ret s P post := by
  have hsp_al : s.spAligned = true := spAligned_sub_c0 hsp_align hsp
  obtain ⟨hb_pos, hb_pow1, hb_hi⟩ := layoutOk_u8_of_ne_zero hbcap hblt
  have hbcap_beq : (bytesCap == 0#64) = false := beq_eq_false_iff_ne.mpr hbcap
  have hdealloc := pkrm_dealloc_ok_at hC
  clear hC
  have hfn : libsignalSessionCode.fnOff pkRemovePollName =
      num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}") :=
    pkRemovePoll_fnOff
  code_fetches_from CryptoVerification.libsignalSessionCode cliPkRemovePollBin img.base
    (Rust.withPanics ext) hfn
    (num% (ls_off% "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"))
    108 40
  dsimp only [tripleRatchetProgAtExt] at hdealloc hpc hk ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    pkRemovePollName = fnBase
  examples_hide_fetches
  refine SepWP.weaken_pre hfoc ?_
  refine SepWP.fold (vecU8_free_ne A (ptr := bytesPtr) hbcap hblen hblt) (by sep_focus) ?_
  apply SepWP.seq_inImage
    (mid := fnBase + bv% (ls_rel%
      "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
      "__rustc::__rust_dealloc"))
    hinv
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv_da1
  have ⟨hF_da1, hsym_da1⟩ := hinv_da1
  apply SepWP.seq_inImage (mid := fnBase + bv% (128)) hinv_da1
  wp_call hdealloc (bytesPtr, bytesCap.toNat, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv_80
  by_cases hncap : nameCap = 0#64
  · subst hncap
    refine SepWP.fold (vecU8_free_zero A namePtr hnlen) (by sep_focus) ?_
    apply SepWP.seq_inImage (mid := fnBase + bv% (148)) hinv_80
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_94
    refine SepWP.weaken_pre (Entails.of_eq (by simp only [*]; ac_rfl))
      (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) hinv_94 (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))
  · obtain ⟨hn_pos, hn_pow1, hn_hi⟩ := layoutOk_u8_of_ne_zero hncap hnlt
    have hncap_beq : (nameCap == 0#64) = false := beq_eq_false_iff_ne.mpr hncap
    refine SepWP.fold (vecU8_free_ne A (ptr := namePtr) hncap hnlen hnlt) (by sep_focus) ?_
    apply SepWP.seq_inImage
      (mid := fnBase + bv% (ls_rel%
        "<libsignal_cli::stores::OneTimePreKeyFiles as libsignal_protocol::storage::traits::PreKeyStore>::remove_pre_key::{closure#0}"
        "__rustc::__rust_dealloc"))
      hinv_80
    wp_steps
    apply SepWP.done (by rfl) (by wp_norm_lhs)
    intro hinv_da2
    have ⟨hF_da2, hsym_da2⟩ := hinv_da2
    apply SepWP.seq_inImage (mid := fnBase + bv% (148)) hinv_da2
    wp_call hdealloc (namePtr, nameCap.toNat, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv_94
    refine SepWP.weaken_pre (Entails.of_eq (by simp only [*]; ac_rfl))
      (hk _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) hinv_94 (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]))

end CryptoVerification.SignalSession.Cli.Store.PkRemovePoll.Helpers
