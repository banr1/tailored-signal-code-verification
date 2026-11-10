/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `segPreKey` Stale Pre-Key Error Path (`segPreKey_stale_ok`)

When `expiry.lt x.now = true` at `+0x6fc`, clones `x.rem.name`, stages
`SessionNotFound(x.rem, "message_encrypt")`, and exits via `tailDropRecord_ok` at `+0x46c`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## `SystemTime.lt` Branch Normalization (`+0x6fc..+0x71c`) -/

@[simp, arm64_norm, wp_norm]
theorem systemTime_lt_w9_eq (a b : SystemTime) :
    (if (a.tvSec == b.tvSec) = true then
       if b.tvNsec.ule a.tvNsec = true then 0#64 else 1#64
     else if b.tvSec.sle a.tvSec = true then 0#64 else 1#64) =
    if a.lt b then 1#64 else 0#64 := by
  rw [← systemTime_lt_cond_eq a b]
  by_cases hsec : a.tvSec = b.tvSec
  · simp only [hsec, beq_self_eq_true, ↓reduceIte]
    by_cases hns : a.tvNsec.ult b.tvNsec = true
    · have hule : b.tvNsec.ule a.tvNsec = false := by
        simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hns ⊢
        omega
      simp [hns, hule]
    · have hns' : a.tvNsec.ult b.tvNsec = false := Bool.eq_false_iff.mpr hns
      have hule : b.tvNsec.ule a.tvNsec = true := by
        simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at hns' ⊢
        omega
      simp [hns', hule]
  · have hbeq : (a.tvSec == b.tvSec) = false := beq_false_of_ne hsec
    simp only [hbeq, Bool.false_eq_true, ↓reduceIte]
    by_cases hslt : a.tvSec.slt b.tvSec = true
    · have hsle : b.tvSec.sle a.tvSec = false := by
        simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at hslt ⊢
        omega
      simp [hslt, hsle]
    · have hslt' : a.tvSec.slt b.tvSec = false := Bool.eq_false_iff.mpr hslt
      have hsle : b.tvSec.sle a.tvSec = true := by
        simp only [BitVec.slt, BitVec.sle, decide_eq_true_eq, decide_eq_false_iff_not] at hslt' ⊢
        omega
      simp [hslt', hsle]

/-! ## Separation-Logic Helpers for the Stale Branch -/

theorem takenRecord_sessionRecordAt_pack_exact (A : RustAlloc) (sp : BitVec 64)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) :
    (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ⊢
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) := by
  unfold sessionRecordAt takenRecord
  dsimp only
  have h128 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_omega
  rw [h128]
  exact Entails.refl _

theorem cmSlotAt_none_pack (A : RustAlloc) (sp : BitVec 64) (k : IdentityKey) :
    (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      ((sp + 0x468#64) ↦₈ 0#8)) ⊢
    cmSlotAt A sp none := by
  unfold cmSlotAt
  have h1 := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
  rw [k.publicKey.bytes.toList_length] at h1
  have h2 : ((sp + 0x468#64) ↦₈ 0#8) ⊢ memRegion (sp + 0x468#64) 1 :=
    pointsTo8_entails_memRegion _ _
  rw [mr_cut_add sp 0x350 0x20 0xf9 (by decide),
      mr_cut_add sp 0x370 0xf8 1 (by decide)]
  exact sepConj_mono h1 (sepConj_mono_right h2)

theorem preKeyScratch_stale_weaken (sp kyLen : BitVec 64) (spk kyIdVal pkVal : BitVec 32)
    (kyber : Option PendingKyberPreKey) :
    preKeyScratch sp kyLen spk kyIdVal pkVal kyber ⊢
      memRegion sp 0x48 ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64)) := by
  unfold preKeyScratch
  rw [memRegion_split sp 0x18 0x30 (by decide),
      mr_cut_add sp 0x18 8 0x28 (by decide),
      mr_cut_add sp 0x20 4 0x24 (by decide),
      mr_cut_add sp 0x24 4 0x20 (by decide),
      mr_cut_add sp 0x28 8 0x18 (by decide),
      mr_cut_add sp 0x30 4 0x14 (by decide),
      mr_cut_add sp 0x34 4 0x10 (by decide),
      mr_cut_add sp 0x38 8 8 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))))))

theorem curScratch_stale_pack (sp : BitVec 64) :
    (memRegion sp 0x48 ∗
      ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
      ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))) ⊢
    curScratch sp := by
  unfold curScratch
  rw [memRegion_split sp 0x48 8 (by decide), sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono_left (pointsTo64_entails_memRegion _ _))

theorem pollWithBaseKey_stale_weaken (sp : BitVec 64) (items : PendingPreKey) :
    pollWithBaseKey sp items ⊢ memRegion (sp + 0x46a#64) 0x716 := by
  unfold pollWithBaseKey
  have h2 := pointsToBytes_entails_memRegion (sp + 0xab4#64) items.baseKey.bytes.toList
  rw [items.baseKey.bytes.toList_length] at h2
  rw [mr_cut_add sp 0x46a 0x64a 0xcc (by decide),
      mr_cut_add sp 0xab4 32 0xac (by decide)]
  exact sepConj_mono_right (sepConj_mono_left h2)

theorem memRegion_16_unpack_598 (sp : BitVec 64) :
    memRegion (sp + 0x598#64) 16 ⊢
      ∃∗ w5a0 : BitVec 64, ∃∗ w598 : BitVec 64,
        ((sp + 0x598#64) ↦₆₄ w598) ∗ ((sp + 0x5a0#64) ↦₆₄ w5a0) := by
  rw [mr_cut_add sp 0x598 8 8 (by decide),
      ProofLib.memRegion_eight (sp + 0x598#64),
      ProofLib.memRegion_eight (sp + 0x5a0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem memRegion_24_unpack_9d0 (sp : BitVec 64) :
    memRegion (sp + 0x9d0#64) 24 ⊢
      ∃∗ w9e0 : BitVec 64, ∃∗ w9d8 : BitVec 64, ∃∗ w9d0 : BitVec 64,
        ((sp + 0x9d0#64) ↦₆₄ w9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ w9d8) ∗ ((sp + 0x9e0#64) ↦₆₄ w9e0) := by
  rw [mr_cut_add sp 0x9d0 8 16 (by decide),
      mr_cut_add sp 0x9d8 8 8 (by decide),
      ProofLib.memRegion_eight (sp + 0x9d0#64),
      ProofLib.memRegion_eight (sp + 0x9d8#64),
      ProofLib.memRegion_eight (sp + 0x9e0#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  exact Entails.refl _

theorem poll_stale_split (sp : BitVec 64) :
    memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 16 ∗
      memRegion (sp + 0x5a8#64) 0x428 ∗
      memRegion (sp + 0x9d0#64) 24 ∗
      memRegion (sp + 0x9e8#64) 0x198 := by
  rw [mr_cut_add sp 0x46a 0x116 0x600 (by decide),
      mr_cut_add sp 0x580 24 0x5e8 (by decide),
      mr_cut_add sp 0x598 16 0x5d8 (by decide),
      mr_cut_add sp 0x5a8 0x428 0x1b0 (by decide),
      mr_cut_add sp 0x9d0 24 0x198 (by decide)]

theorem vecU8_580_unpack (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x580#64) bs ⊢
      ∃∗ ptr : BitVec 64, ∃∗ cap : BitVec 64,
        ((sp + 0x580#64) ↦₆₄ cap) ∗
        ((sp + 0x588#64) ↦₆₄ ptr) ∗
        ((sp + 0x590#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Body A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader vecU8Body
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr =>
    Entails.sepExists_right ptr (Entails.sepExists_right cap ?_)
  have ha1 : sp + 0x580#64 + 8#64 = sp + 0x588#64 := by bv_omega
  have ha2 : sp + 0x580#64 + 16#64 = sp + 0x590#64 := by bv_omega
  rw [ha1, ha2]
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem pollWith_9d0_pack (sp cap ptr len w598 w5a0 w3 w4 w5 : BitVec 64) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      ((sp + 0x580#64) ↦₆₄ cap) ∗
      ((sp + 0x588#64) ↦₆₄ ptr) ∗
      ((sp + 0x590#64) ↦₆₄ len) ∗
      ((sp + 0x598#64) ↦₆₄ w598) ∗
      ((sp + 0x5a0#64) ↦₆₄ w5a0) ∗
      memRegion (sp + 0x5a8#64) 0x428 ∗
      ((sp + 0x9d0#64) ↦₆₄ w3) ∗
      ((sp + 0x9d8#64) ↦₆₄ w4) ∗
      ((sp + 0x9e0#64) ↦₆₄ w5) ∗
      memRegion (sp + 0x9e8#64) 0x198) ⊢
    pollWith sp 0x9d0 [w3, w4, w5] := by
  unfold pollWith
  dsimp only [words64At]
  rw [show (0x9d0 - 0x46a : Nat) = 0x566 from rfl,
      mr_cut_add sp 0x46a 0x116 0x450 (by decide),
      mr_cut_add sp 0x580 8 0x448 (by decide),
      mr_cut_add sp 0x588 8 0x440 (by decide),
      mr_cut_add sp 0x590 8 0x438 (by decide),
      mr_cut_add sp 0x598 8 0x430 (by decide),
      mr_cut_add sp 0x5a0 8 0x428 (by decide)]
  have hw0 : sp + BitVec.ofNat 64 0x9d0 = sp + 0x9d0#64 := rfl
  have hw1 : sp + 0x9d0#64 + 8#64 = sp + 0x9d8#64 := by bv_omega
  have hw2 : sp + 0x9d8#64 + 8#64 = sp + 0x9e0#64 := by bv_omega
  have hw3 : sp + BitVec.ofNat 64 (0x9d0 + 8 * [w3, w4, w5].length) = sp + 0x9e8#64 := rfl
  have hlen3 : 0xb80 - (0x9d0 + 8 * [w3, w4, w5].length) = 0x198 := rfl
  rw [hw0, hw1, hw2, hw3, hlen3, sepConj_emp]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))))

theorem adrp_0x718_logFilterAddr {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + 248792#64) :
    ((entry + 1816#64 &&& 18446744073709547520#64) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - 0x3d000)) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have hbal := ProofLib.ObjectLoad.base_aligned_of_loads himg
  rw [adrp_0x4b000_eq img.base entry hbal hentry.symm,
      CryptoVerification.LibsignalSession.logFilterAddr]
  bv_omega

theorem adrp_0x718_logFilterAddr_norm {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + 248792#64) :
    (entry + 1816#64 &&& 18446744073709547520#64) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - 0x3d000) =
      CryptoVerification.LibsignalSession.logFilterAddr img := by
  have h := adrp_0x718_logFilterAddr himg hentry
  rw [BitVec.add_assoc] at h
  exact h

/-! ## Main Theorem (`segPreKey_stale_ok`) -/

set_option maxHeartbeats 800000 in
theorem segPreKey_stale_ok
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hlt : expiry.lt x.now = true)
    (hadd : StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  rcases hadd with ⟨hts, hexp, _hpkVal, _hkyIdVal, _hkySlice, hpc, hmeta, htr,
    hx0, hx1, hx20, _hx21, hx22, _hx23, _hx24, hx25, hx26, _hx27, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have ⟨hmod, hdraws⟩ := model_of_stale (C := C) (S := S) (x := x)
    hcur hotr hrem hpk hts hexp hlt
  set sp := s0.sp - 0xbe0#64
  apply segExit_trans
    (mid := fun sf =>
      ∃ cap ptr devWord,
        devWord.setWidth 8 = x.rem.device ∧
        sf.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
        EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) (encEntry img + 0x46c#64)
          (tailRegs cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length))
          (fun sp => dropRecordSlots A sp curScratch ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
            (some (pqCap, pqPtr, otr)) none
            (pollWith sp 0x9d0 [devWord, img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4), 15#64]) ∗
            (vecU8Body A cap ptr x.rem.name.bytes ∗
              ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")))
          R s0 sf)
  · change s.pc = encEntry img + 1788#64 at hpc
    apply segExit_of_sepWPp_callInv ⟨hfrozen, hsym⟩
      (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 1132#64)
      (dur_mem_group hmem)
    have himg := env.loads
    refine rodata_message_encrypt_sepWPp himg hfrozen.roData ?_
    refine SepWPp.fold (takenRecord_sessionRecordAt_pack_exact A sp prevCap prevPtr G sess taken)
      (by sep_focus) ?_
    refine SepWPp.fold (pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64))
      (by sep_focus) ?_
    refine SepWPp.fold (cmSlotAt_none_pack A sp k) (by sep_focus) ?_
    refine SepWPp.fold
      (preKeyScratch_stale_weaken sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey)
      (by sep_focus) ?_
    refine SepWPp.fold (pollWithBaseKey_stale_weaken sp items) (by sep_focus) ?_
    dsimp only [encSpillsAt, encSpillsAtV, encCommon, protocolAddressAt, logOff]
    rw [poll_stale_split sp, encSubStack_split_ext hsp]
    refine SepWPp.fold (memRegion_16_unpack_598 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w5a0 => sepWPp_elim_ex fun w598 => ?_
    refine SepWPp.fold (memRegion_24_unpack_9d0 sp) (by sep_focus) ?_
    refine sepWPp_elim_ex fun w9e0 => sepWPp_elim_ex fun w9d8 => sepWPp_elim_ex fun w9d0 => ?_
    have henc_fn := encEntry_eq_fnAddr env
    rw [henc_fn] at hpc
    have hclone_call := henc_fn ▸ stringClone_ok_at_enc env
    have hentry_val : (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName =
        img.base + 248792#64 := by
      rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x3cbd8]
    clear env
    messageEncryptPreKey_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) libsignalSessionCode_fnOff_0x3cbd8 0x6fc 0x34
    messageEncryptPreKey_fetches img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) libsignalSessionCode_fnOff_0x3cbd8 0x78c 0x44
    dsimp only [tripleRatchetProgAt] at hpc hclone_call henc_fn hentry_val ⊢
    generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr encryptWithStoresName = entry
    examples_hide_fetches
    have hlog := adrp_0x718_logFilterAddr himg hentry_val
    have hlog_norm := adrp_0x718_logFilterAddr_norm himg hentry_val
    have hadrp_op := adrp_0x4a6a0_eq img.base entry
      (ProofLib.ObjectLoad.base_aligned_of_loads himg) hentry_val.symm
    clear hentry_val
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::string::String as core::clone::Clone>::clone" - 0x3cbd8))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
    refine SepWPp.call_frame hclone_call
      (x := (x.remA, sp + 1408#64, x.rem.name))
      (ret_pc := entry + 1948#64)
      (by wp_norm_goal) (by wp_norm_goal) hspAl
      rfl rfl ⟨by wp_norm_goal, by wp_norm_goal⟩
      (by dsimp only [State.sp, State.setPC, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
      (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
      (fun sf _ hm => by
        rw [sepConj_assoc] at hm
        refine onPanic_of_alloc (s := _) ?_ hm
        change s0.trace <+: s.trace
        rw [htr]
        exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩)
      fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
    dsimp only [stringCloneSpec]
    rw [sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
    rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm]
      at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hx29_1 hvregs_1 hsp1 htr1
    rw [hx19] at hx19_1; rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
    have hsp1_al : s1.spAligned = true := by
      unfold State.spAligned at hspAl ⊢; rwa [hsp1]
    rw [hsp] at hsp1
    rw [htr] at htr1
    refine SepWPp.fold (vecU8_580_unpack A sp x.rem.name.bytes) (by sep_focus) ?_
    refine sepWPp_elim_ex fun ptr => sepWPp_elim_ex fun cap => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    refine SepWP.fold (curScratch_stale_pack sp) (by sep_focus) ?_
    refine SepWP.fold (pollWith_9d0_pack sp cap ptr _ _ _ _ _ _) (by sep_focus) ?_
    have hsp1_pack :
        (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
          stackAt s1.sp extHookStack) ⊢ stackAt sp encSubStack := by
      rw [hsp1, ← encSubStack_split_ext rfl]
      exact Entails.refl _
    refine SepWP.fold hsp1_pack (by sep_focus) ?_
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    intro hinv1 hmf
    have hfinal :
        kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    have hidfinal :
        ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
      rw [congrArg Prod.snd hmod]
      rfl
    dsimp only [EncTail, EncTailV, encStoreExtra, tailRegs, dropRecordSlots, otrSlotAt, encSpillsAt, encSpillsAtV, encCommon, protocolAddressAt, logOff, sp]
      at hsp1 hx19_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
    refine ⟨cap, ptr, (w598 &&& 0xffffffffffffff00#64) ||| BitVec.zeroExtend 64 x.rem.device,
      by ext i hi; simp, by wp_norm_goal, ?_, ?_, ?_,
      hstack, ?_⟩
    · rw [henc_fn]; wp_norm_goal
    · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al, hsp1_al,
        by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
        by wp_norm_goal, hinv1.1, hinv1.2, by wp_norm_goal⟩
    · refine ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    · rw [hdraws, hfinal, hidfinal]
      arm64_sep_close
  · intro sf ⟨cap, ptr, devWord, hdev, htr_sf, htail⟩
    have hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r)
        (.error (.sessionNotFound x.rem.val "message_encrypt")) s0 sf := by
      refine ⟨⟨congrArg Prod.fst hmod, by rw [congrArg Prod.snd hmod]; exact ⟨hscope.2, trivial⟩,
        by rw [congrArg Prod.snd hmod]; trivial⟩, ?_⟩
      rw [congrArg Prod.snd hmod, htr_sf, ikit.traceOfWith_load]
      rfl
    have h15 : 15#64 = BitVec.ofNat 64 (utf8 "message_encrypt").length := by
      open ProofLib.ProgramReflection in rfl_kernel
    have hst : SpeStaged A x.ret (.sessionNotFound x.rem.val "message_encrypt")
        [cap, ptr, BitVec.ofNat 64 x.rem.name.bytes.length, devWord, img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4), 15#64]
        (vecU8Body A cap ptr x.rem.name.bytes ∗
          ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt")) :=
      speStaged_sessionNotFound A x.ret x.rem.val "message_encrypt"
        cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) 15#64
        rfl hdev h15
    exact tailDropRecord_ok env x R s0 sf (preKeyErrAnswers r)
      (.sessionNotFound x.rem.val "message_encrypt")
      cap ptr (BitVec.ofNat 64 x.rem.name.bytes.length) devWord (img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) 15#64
      (vecU8Body A cap ptr x.rem.name.bytes ∗
        ((img.base + bv% (ls_xref% 0x3cdb0 0x3cdb4)) ↦ᵣ utf8 "message_encrypt"))
      curScratch (Or.inl rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
      (some (pqCap, pqPtr, otr)) hm hst htail

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
