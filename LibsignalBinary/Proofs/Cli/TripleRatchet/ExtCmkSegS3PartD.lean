/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS3Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.AdvanceChainKey
import LibsignalBinary.Proofs.ConsumeMessageKey.StoreLoopProofs.Fetch
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S3 Part D (`AdvanceChainKeySpecX`)

Proves `advanceChainKey_ok_x` (`+0x474 → nextPC`) for `RatchetState::consume_message_key` on
`SP2Ext img.base ext` at `cmkLoopStackX = 20000` bytes.
-/

@[expose] public section

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib SepProp
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession.StoreLoop
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X
open ProofLib.ProgramReflection

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS3PartD : True := trivial

private theorem pointsTo8_eq_pointsToBytes_singleton (a : BitVec 64) (b : BitVec 8) :
    (a ↦₈ b) = (a ↦ₛ [b]) := by
  rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]

private theorem memRegion_256_partD_split (sp0 : BitVec 64) :
    memRegion (sp0 - 352#64) 256 =
      ∃∗ b320 : BitVec 8,
        ((sp0 - 320#64) ↦₈ b320) ∗
        memRegion (sp0 - 319#64) 31 ∗
        memRegion (sp0 - 224#64) 32 ∗
        (memRegion (sp0 - 352#64) 32 ∗
         memRegion (sp0 - 288#64) 64 ∗
         memRegion (sp0 - 192#64) 96) := by
  rw [show (256 : Nat) = 32 + (1 + (31 + (64 + (32 + 96)))) from rfl,
      memRegion_split (sp0 - 352#64) 32 224 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64) 1 223 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64) 31 192 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64) 64 128 (by decide),
      memRegion_split (sp0 - 352#64 + 32#64 + 1#64 + 31#64 + 64#64) 32 96 (by decide)]
  have ha1 : sp0 - 352#64 + 32#64 = sp0 - 320#64 := by bv_omega
  have ha2 : sp0 - 320#64 + 1#64 = sp0 - 319#64 := by bv_omega
  have ha3 : sp0 - 319#64 + 31#64 = sp0 - 288#64 := by bv_omega
  have ha4 : sp0 - 288#64 + 64#64 = sp0 - 224#64 := by bv_omega
  have ha5 : sp0 - 224#64 + 32#64 = sp0 - 192#64 := by bv_omega
  rw [ha1, ha2, ha3, ha4, ha5, memRegion_one_eq_exists_pointsTo8 (sp0 - 320#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  ac_rfl

private theorem memRegion_32_eq_exists_pointsTo64_4 (a : BitVec 64) :
    memRegion a 32 =
      ∃∗ t0 : BitVec 64, ∃∗ t1 : BitVec 64, ∃∗ t2 : BitVec 64, ∃∗ t3 : BitVec 64,
        (a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3) := by
  rw [show (32 : Nat) = 8 + (8 + (8 + 8)) from rfl,
      memRegion_split a 8 24 (by decide),
      memRegion_split (a + 8#64) 8 16 (by decide),
      memRegion_split (a + 8#64 + 8#64) 8 8 (by decide)]
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [ha16, ha24, ProofLib.memRegion_eight a, sepExists_sepConj_left]
  apply congrArg SepProp.sepExists; funext t0
  rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext t1
  rw [ProofLib.memRegion_eight (a + 16#64), sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext t2
  rw [ProofLib.memRegion_eight (a + 24#64), sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]

private theorem pointsTo64_4_entails_memRegion_32 (a : BitVec 64)
    (t0 t1 t2 t3 : BitVec 64) :
    ((a ↦₆₄ t0) ∗ ((a + 8#64) ↦₆₄ t1) ∗ ((a + 16#64) ↦₆₄ t2) ∗ ((a + 24#64) ↦₆₄ t3)) ⊢
      memRegion a 32 := by
  refine Entails.trans (sepConj_mono (pointsTo64_entails_memRegion a t0)
    (sepConj_mono (pointsTo64_entails_memRegion (a + 8#64) t1)
      (sepConj_mono (pointsTo64_entails_memRegion (a + 16#64) t2)
        (pointsTo64_entails_memRegion (a + 24#64) t3)))) ?_
  have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  have ha24 : a + 16#64 + 8#64 = a + 24#64 := by bv_omega
  rw [← ha24, ← memRegion_split (a + 16#64) 8 8 (by decide),
      ← ha16, ← memRegion_split (a + 8#64) 8 16 (by decide),
      ← memRegion_split a 8 24 (by decide)]
  exact Entails.refl _

private def advanceChainKeyFrameX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (s0 : State) : SepProp :=
  ratchetAt A x.self G' st' ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  memRegion (s0.sp - 20480#64) 1568 ∗
  memRegion (s0.sp - 480#64) 112 ∗
  ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
  memRegion (s0.sp - 360#64) 4 ∗
  memRegion (s0.sp - 352#64) 32 ∗
  memRegion (s0.sp - 288#64) 64 ∗
  memRegion (s0.sp - 192#64) 96 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

private theorem cmkLoopHeapX_partD_split (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey) (s0 : State) :
    cmkLoopHeapX A img x G' st' ckc s0 =
      ∃∗ b320 : BitVec 8,
        ((s0.sp - 320#64) ↦₈ b320) ∗
        (memRegion (s0.sp - 224#64) 32 ∗
         (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
         stackAt (s0.sp - 480#64) hmacStackX ∗
         memRegion (s0.sp - 319#64) 31 ∗
         ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
         ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
         advanceChainKeyFrameX A img x G' st' s0) := by
  unfold cmkLoopHeapX cmkLoopFrame advanceChainKeyFrameX
  rw [chainKeyBytes_pointsTo x.ckA ckc,
      stackAt_20000_split_hmacX s0.sp,
      memRegion_256_partD_split s0.sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply congrArg SepProp.sepExists; funext b320
  ac_rfl

private theorem partDPost_entails_cmkLoopHeapX (F : ShaCompress)
    (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (G' : RatchetGhost) (st' : RatchetState) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi : BitVec 64)
    (hq0_lo : q0_lo = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).take 8))
    (hq0_hi : q0_hi = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 8).take 8))
    (hq1_lo : q1_lo = pack64 (((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 16).take 8))
    (hq1_hi : q1_hi = pack64 ((hmacWith F (keyToBytes32 ckc.key) [2#8]).drop 24))
    (s0 : State) :
    (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
     ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
     ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
     ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
     (x.ckA ↦₆₄ q0_lo) ∗
     ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
     ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
     ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
     ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
     stackAt (s0.sp - 480#64) hmacStackX ∗
     advanceChainKeyFrameX A img x G' st' s0) ⊢
      cmkLoopHeapX A img x G' st' (chainStepN F 1 ckc) s0 := by
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hck'_key : keyToBytes32 (chainStepN F 1 ckc).key = bs := by
    change keyToBytes32 (bytesToKey32 bs) = bs
    exact keyToBytes32_bytesToKey32 bs hbs
  have hck'_idx : (chainStepN F 1 ckc).index = ckc.index + 1#32 := rfl
  have hckA_words :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi)) =
      (x.ckA ↦ₛ bs) := by
    rw [hq0_lo, hq0_hi, hq1_lo, hq1_hi, ← pointsToBytes_32_eq_pointsTo64 x.ckA bs hbs]
  have hckA_full :
      ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) =
      (x.ckA ↦ₛ chainKeyBytes (chainStepN F 1 ckc)) := by
    rw [chainKeyBytes_pointsTo x.ckA (chainStepN F 1 ckc), hck'_key, hck'_idx, ← hckA_words]
    ac_rfl
  have h224 := pointsTo64_4_entails_memRegion_32 (s0.sp - 224#64) q0_lo q0_hi q1_lo q1_hi
  have h320 := pointsTo64_4_entails_memRegion_32 (s0.sp - 320#64) q0_lo q0_hi q1_lo q1_hi
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200] at h224
  rw [ha312, ha304, ha296] at h320
  have h256 :
      (memRegion (s0.sp - 352#64) 32 ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 288#64) 64 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       memRegion (s0.sp - 192#64) 96) =
      memRegion (s0.sp - 352#64) 256 := by
    have hb1 : s0.sp - 352#64 + 32#64 = s0.sp - 320#64 := by bv_omega
    have hb2 : s0.sp - 320#64 + 32#64 = s0.sp - 288#64 := by bv_omega
    have hb3 : s0.sp - 288#64 + 64#64 = s0.sp - 224#64 := by bv_omega
    have hb4 : s0.sp - 224#64 + 32#64 = s0.sp - 192#64 := by bv_omega
    rw [← hb4, ← memRegion_split (s0.sp - 224#64) 32 96 (by decide),
        ← hb3, ← memRegion_split (s0.sp - 288#64) 64 128 (by decide),
        ← hb2, ← memRegion_split (s0.sp - 320#64) 32 192 (by decide),
        ← hb1, ← memRegion_split (s0.sp - 352#64) 32 224 (by decide)]
  unfold cmkLoopHeapX cmkLoopFrame advanceChainKeyFrameX
  rw [stackAt_20000_split_hmacX s0.sp]
  have hreord1 :
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
       (x.ckA ↦₆₄ q0_lo) ∗
       ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
       ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
       ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
       ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
       stackAt (s0.sp - 480#64) hmacStackX ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        memRegion (s0.sp - 20480#64) 1568 ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       (((s0.sp - 320#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 296#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ q0_lo) ∗ ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗ ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗
       (ratchetAt A x.self G' st' ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ret 88 ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗
        (memRegion (s0.sp - 20480#64) 1568 ∗ stackAt (s0.sp - 480#64) hmacStackX) ∗
        memRegion (s0.sp - 480#64) 112 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        memRegion (s0.sp - 360#64) 4 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        memRegion (s0.sp - 352#64) 32 ∗
        memRegion (s0.sp - 288#64) 64 ∗
        memRegion (s0.sp - 192#64) 96 ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool)) := by ac_rfl
  rw [hreord1, hckA_full]
  refine Entails.trans (sepConj_mono h224 (sepConj_mono_left h320)) ?_
  rw [← h256]
  exact Entails.of_eq (by ac_rfl)

private theorem partD1_wp_x (b : BitVec 64) (ext : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (b320 : BitVec 8) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1140#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) s
      ((s0.sp - 320#64) ↦₈ b320)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R → sf.mem ⊨ ((s0.sp - 320#64) ↦₈ 2#8) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x0 = s0.sp - 224#64 ∧
        sf.readReg64 .x1 = x.ckA ∧
        sf.readReg64 .x2 = 32#64 ∧
        sf.readReg64 .x3 = s0.sp - 320#64 ∧
        sf.readReg64 .x4 = 1#64 ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64 ∧
        sf.readReg64 .x30 = (SP2Ext b ext).fnAddr cmkName + 1172#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  cmk_fetches_range b (Rust.withPanics ext) hfn 285 293
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  unfold SP2Ext cmkName at *
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  wp_steps
  wp_done

private theorem partD_hmac_wp_x (img : Obj.Image) (F : ShaCompress)
    (ext : String → Option (State → State))
    (hHmac : HmacOkX img F ext)
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey) (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "libsignal_protocol::crypto::hmac_sha256" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx0 : s.readReg64 .x0 = s0.sp - 224#64)
    (hx1 : s.readReg64 .x1 = x.ckA)
    (hx2 : s.readReg64 .x2 = 32#64)
    (hx3 : s.readReg64 .x3 = s0.sp - 320#64)
    (hx4 : s.readReg64 .x4 = 1#64)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hx30 : s.readReg64 .x30 = (SP2Ext img.base ext).fnAddr cmkName + 1172#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hfrozen : img.FrozenLoaded s)
    (hsymtab : s.symtab = img.symtab) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1172#64) s
      (memRegion (s0.sp - 224#64) 32 ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) hmacStackX)
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦ₛ hmacWith F (keyToBytes32 ckc.key) [2#8]) ∗
             (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
             ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
             stackAt (s0.sp - 480#64) hmacStackX) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x22 = x.theirA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hhmac := hmac_ok_at_cmk_x hHmac
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  unfold SP2Ext cmkName at *
  generalize (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  wp_call hhmac (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  wp_done

private theorem add_one_ne_zero_of_lt {idx ctr : BitVec 32} (h : idx < ctr) :
    idx + 1#32 ≠ 0#32 := by
  intro heq
  have hlt_nat : idx.toNat < ctr.toNat := BitVec.lt_def.mp h
  have hctr : ctr.toNat < 2 ^ 32 := ctr.isLt
  have hadd : (idx + 1#32).toNat = idx.toNat + 1 := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0 : (idx + 1#32).toNat = 0 := by rw [heq]; rfl
  omega

private theorem partD2_wp_x (b : BitVec 64) (ext : String → Option (State → State))
    (x : ConsumeMessageKeyGhost) (ckc : ChainKey)
    (q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3 : BitVec 64)
    (s0 s : State)
    (hstat : s.status = .Running)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1172#64)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp0_align : s0.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = x.theirA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlt : ckc.index < x.counter) :
    SepWP (SP2Ext b ext)
      (if (ckc.index + 1#32) < x.counter
       then (SP2Ext b ext).fnAddr cmkName + 820#64
       else (SP2Ext b ext).fnAddr cmkName + 1244#64)
      s
      (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
       ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
       ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
       ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦₆₄ t0) ∗
       ((s0.sp - 312#64) ↦₆₄ t1) ∗
       ((s0.sp - 304#64) ↦₆₄ t2) ∗
       ((s0.sp - 296#64) ↦₆₄ t3) ∗
       (x.ckA ↦₆₄ k0) ∗
       ((x.ckA + 8#64) ↦₆₄ k1) ∗
       ((x.ckA + 16#64) ↦₆₄ k2) ∗
       ((x.ckA + 24#64) ↦₆₄ k3) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index))
      (fun sf P_f =>
        (∀ R, sf.mem ⊨ P_f ∗ R →
          sf.mem ⊨
            (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
             ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
             ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
             ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
             ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
             ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
             (x.ckA ↦₆₄ q0_lo) ∗
             ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
             ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
             ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
             ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R) ∧
        sf.sp = s0.sp - 480#64 ∧
        sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        sf.readReg64 .x19 = 1#64 ∧
        sf.readReg64 .x21 = x.ckA ∧
        sf.readReg64 .x23 = x.self ∧
        sf.readReg64 .x26 = x.theirA ∧
        sf.readReg64 .x27 = s0.sp - 224#64 ∧
        sf.readReg64 .x28 = (ckc.index + 1#32).zeroExtend 64 ∧
        sf.readReg64 .x29 = s0.sp - 96#64) := by
  rcases htr with ⟨htr, hvregs⟩
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
  cmk_fetches_range b (Rust.withPanics ext) hfn 293 306
  have hsp0_and : (s0.sp &&& 15#64 == 0#64) = true := hsp0_align
  have hne0 : ckc.index + 1#32 ≠ 0#32 := add_one_ne_zero_of_lt hlt
  unfold SP2Ext cmkName at *
  generalize (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" = entry at *
  examples_hide_fetches
  wp_steps
  wp_if hloop
  · have hlt' : ckc.index + 1#32 < x.counter := BitVec.ult_iff_lt.mp hloop
    simp only [hlt', ↓reduceIte]
    wp_done
  · have hnlt' : ¬ (ckc.index + 1#32 < x.counter) := mt BitVec.ult_iff_lt.mpr hloop
    simp only [hnlt', ↓reduceIte]
    wp_steps
    wp_done

theorem advanceChainKey_ok_x {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} {img : Obj.Image} :
    AdvanceChainKeySpecX F A ext img := by
  intro himg hHmac x G' st' ckc R s0 sD hlt hD hL
  dsimp only
  rcases hD with
    ⟨hpc,
     ⟨hstat, hsp, hsp0_align, _hsp_align, hx29, htr, hfrozen, hsymtab, hvregs⟩,
     ⟨hx19, hx21, hx22, hx23, hx27⟩,
     hmem⟩
  have hpc' : sD.pc = (SP2Ext img.base ext).fnAddr cmkName + 1140#64 := by
    rw [hpc, cmkAdvanceChainKeyPC_eq_fnAddr_x himg ext]
  rw [cmkLoopHeapX_partD_split A img x G' st' ckc s0] at hmem
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem
  rcases hmem with ⟨b320, hmem⟩
  rw [sepConj_assoc] at hmem
  let R1 : SepProp :=
    (memRegion (s0.sp - 224#64) 32 ∗
     (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
     stackAt (s0.sp - 480#64) hmacStackX ∗
     memRegion (s0.sp - 319#64) 31 ∗
     ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
     ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
     advanceChainKeyFrameX A img x G' st' s0) ∗ R
  rcases (partD1_wp_x img.base ext x b320 s0 sD hstat hpc' hsp hsp0_align
      hx19 hx21 hx22 hx23 hx27 hx29 ⟨htr, hvregs⟩).elim hmem hL with
    ⟨s1, hsteps1, ⟨_hpc1, hstat1, P_f1, hm1, hpost1,
      hsp1, _hsp1_align, htr1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1,
      hx19_1, hx21_1, hx22_1, hx23_1, hx27_1, hx29_1, hx30_1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem1 := hpost1 R1 hm1
  rw [pointsTo8_eq_pointsToBytes_singleton (s0.sp - 320#64) 2#8] at hmem1
  have hreord1 :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ R1) =
      ((memRegion (s0.sp - 224#64) 32 ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) hmacStackX) ∗
       (memRegion (s0.sp - 319#64) 31 ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        advanceChainKeyFrameX A img x G' st' s0 ∗ R)) := by
    dsimp only [R1]
    ac_rfl
  rw [hreord1] at hmem1
  let R2 : SepProp :=
    memRegion (s0.sp - 319#64) 31 ∗
    ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
    ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
    advanceChainKeyFrameX A img x G' st' s0 ∗ R
  have hfrozen1 : img.FrozenLoaded s1 := hfrozen.of_keepsFrozen hsteps1.keepsFrozen
  have hsymtab1 : s1.symtab = img.symtab := hsteps1.symtab_eq.trans hsymtab
  have hL1 : (SP2Ext img.base ext).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rcases (partD_hmac_wp_x img F ext hHmac x ckc s0 s1 hstat1 _hpc1 hsp1 hsp0_align
      hx0_1 hx1_1 hx2_1 hx3_1 hx4_1 hx19_1 hx21_1 hx22_1 hx23_1 hx27_1 hx29_1 hx30_1
      htr1 hfrozen1 hsymtab1).elim hmem1 hL1 with
    ⟨s2, hsteps2, ⟨_hpc2, hstat2, P_f2, hm2, hpost2,
      hsp2, _hsp2_align, htr2, hx19_2, hx21_2, hx22_2, hx23_2, hx27_2, hx29_2⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem2 := hpost2 R2 hm2
  let bs := hmacWith F (keyToBytes32 ckc.key) [2#8]
  have hbs : bs.length = 32 := hmacWith_length F (keyToBytes32 ckc.key) [2#8]
  have hkey_len : (keyToBytes32 ckc.key).length = 32 := keyToBytes32_length ckc.key
  have h320_combine :
      (((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ⊢
        memRegion (s0.sp - 320#64) 32 := by
    refine Entails.trans (sepConj_mono_left (pointsToBytes_entails_memRegion (s0.sp - 320#64) [2#8])) ?_
    have ha319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_omega
    change (memRegion (s0.sp - 320#64) 1 ∗ memRegion (s0.sp - 319#64) 31) ⊢ _
    rw [← ha319, ← memRegion_split (s0.sp - 320#64) 1 31 (by decide)]
    exact Entails.refl _
  have hreord2 :
      ((((s0.sp - 224#64) ↦ₛ bs) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
        stackAt (s0.sp - 480#64) hmacStackX) ∗ R2) =
      ((((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31) ∗
       ((s0.sp - 224#64) ↦ₛ bs) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) hmacStackX ∗
       advanceChainKeyFrameX A img x G' st' s0 ∗ R) := by
    dsimp only [R2]
    ac_rfl
  rw [hreord2] at hmem2
  have hmem2' := Satisfies.mono (sepConj_mono_left h320_combine) hmem2
  rw [memRegion_32_eq_exists_pointsTo64_4 (s0.sp - 320#64),
      pointsToBytes_32_eq_pointsTo64 (s0.sp - 224#64) bs hbs,
      pointsToBytes_32_eq_pointsTo64 x.ckA (keyToBytes32 ckc.key) hkey_len] at hmem2'
  have ha216 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_omega
  have ha208 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_omega
  have ha200 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_omega
  have ha312 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_omega
  have ha304 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_omega
  have ha296 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_omega
  rw [ha216, ha208, ha200, ha312, ha304, ha296] at hmem2'
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hmem2'
  rcases hmem2' with ⟨t0, t1, t2, t3, hmem2'⟩
  let q0_lo := pack64 (bs.take 8)
  let q0_hi := pack64 ((bs.drop 8).take 8)
  let q1_lo := pack64 ((bs.drop 16).take 8)
  let q1_hi := pack64 (bs.drop 24)
  let k0 := pack64 ((keyToBytes32 ckc.key).take 8)
  let k1 := pack64 (((keyToBytes32 ckc.key).drop 8).take 8)
  let k2 := pack64 (((keyToBytes32 ckc.key).drop 16).take 8)
  let k3 := pack64 ((keyToBytes32 ckc.key).drop 24)
  have hreord3 :
      ((((s0.sp - 320#64) ↦₆₄ t0) ∗ ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗ ((s0.sp - 296#64) ↦₆₄ t3)) ∗
       (((s0.sp - 224#64) ↦₆₄ q0_lo) ∗ ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗ ((s0.sp - 200#64) ↦₆₄ q1_hi)) ∗
       ((x.ckA ↦₆₄ k0) ∗ ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗ ((x.ckA + 24#64) ↦₆₄ k3)) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       stackAt (s0.sp - 480#64) hmacStackX ∗
       advanceChainKeyFrameX A img x G' st' s0 ∗ R) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ t0) ∗
        ((s0.sp - 312#64) ↦₆₄ t1) ∗
        ((s0.sp - 304#64) ↦₆₄ t2) ∗
        ((s0.sp - 296#64) ↦₆₄ t3) ∗
        (x.ckA ↦₆₄ k0) ∗
        ((x.ckA + 8#64) ↦₆₄ k1) ∗
        ((x.ckA + 16#64) ↦₆₄ k2) ∗
        ((x.ckA + 24#64) ↦₆₄ k3) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index)) ∗
       (stackAt (s0.sp - 480#64) hmacStackX ∗ advanceChainKeyFrameX A img x G' st' s0 ∗ R)) := by ac_rfl
  rw [hreord3] at hmem2'
  let R3 : SepProp := stackAt (s0.sp - 480#64) hmacStackX ∗ advanceChainKeyFrameX A img x G' st' s0 ∗ R
  have hL2 : (SP2Ext img.base ext).CodeLoaded s2.mem := hsteps2.codeLoaded hL1
  rcases (partD2_wp_x img.base ext x ckc q0_lo q0_hi q1_lo q1_hi k0 k1 k2 k3 t0 t1 t2 t3
      s0 s2 hstat2 _hpc2 hsp2 hsp0_align hx19_2 hx21_2 hx22_2 hx23_2 hx27_2 hx29_2
      htr2 hlt).elim hmem2' hL2 with
    ⟨s', hsteps3, ⟨hpc', hstat', P_f3, hm3, hpost3,
      hsp', hsp'_align, htr', hx19', hx21', hx23', hx26', hx27', hx28', hx29'⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  have hmem3 := hpost3 R3 hm3
  have hreord4 :
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32))) ∗ R3) =
      ((((s0.sp - 224#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 216#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 208#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 200#64) ↦₆₄ q1_hi) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦₆₄ q0_lo) ∗
        ((s0.sp - 312#64) ↦₆₄ q0_hi) ∗
        ((s0.sp - 304#64) ↦₆₄ q1_lo) ∗
        ((s0.sp - 296#64) ↦₆₄ q1_hi) ∗
        (x.ckA ↦₆₄ q0_lo) ∗
        ((x.ckA + 8#64) ↦₆₄ q0_hi) ∗
        ((x.ckA + 16#64) ↦₆₄ q1_lo) ∗
        ((x.ckA + 24#64) ↦₆₄ q1_hi) ∗
        ((x.ckA + 32#64) ↦₃₂ (ckc.index + 1#32)) ∗
        stackAt (s0.sp - 480#64) hmacStackX ∗
        advanceChainKeyFrameX A img x G' st' s0) ∗ R) := by
    dsimp only [R3]
    ac_rfl
  rw [hreord4] at hmem3
  have hmem_final := Satisfies.mono
    (sepConj_mono_left
      (partDPost_entails_cmkLoopHeapX F A img x G' st' ckc q0_lo q0_hi q1_lo q1_hi rfl rfl rfl rfl s0))
    hmem3
  rw [← cmkLoopHeap_sep_low_eq A img x G' st' (chainStepN F 1 ckc) s0, sepConj_assoc] at hmem_final
  have hsteps_all : Steps (SP2Ext img.base ext) sD s' :=
    (hsteps1.trans hsteps2).trans hsteps3
  have hnextPC_eq :
      (if (chainStepN F 1 ckc).index < x.counter then cmkLoopPC img else cmkEpiloguePC img) =
      (if (ckc.index + 1#32) < x.counter
       then (SP2Ext img.base ext).fnAddr cmkName + 820#64
       else (SP2Ext img.base ext).fnAddr cmkName + 1244#64) := by
    rw [cmkLoopPC_eq_fnAddr_x himg ext, cmkEpiloguePC_eq_fnAddr_x himg ext]
    rfl
  refine ⟨s', hsteps_all, ?_⟩
  refine ⟨by rw [hnextPC_eq]; exact hpc',
    ⟨hstat', hsp', hsp0_align, hsp'_align, hx29', htr'.1,
     hfrozen.of_keepsFrozen hsteps_all.keepsFrozen,
     hsteps_all.symtab_eq.trans hsymtab, htr'.2⟩,
    ⟨hx21', hx23', hx26', hx27', hx28'⟩,
    fun _ => hx19',
    hmem_final⟩

end Proofs.libsignal.Stage1X.CmkX
