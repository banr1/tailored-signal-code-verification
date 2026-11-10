/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyStale
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSym
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import ProofLib.RegChain

/-!
# `segPreKey` `OTR::encrypt` Call and Error Branch (`+0x8b4..+0x8ec`)

Steps from `PreKeyEncryptState'` (`+0x8b4`) through `otrEncryptSpecQ` to `PreKeyEncryptRetState`
(`+0x8c8`), and routes the `.error e` branch (`+0x8c8..+0x8ec`) to `tailPreKeyEncryptErr_ok` at
`+0xc38`.
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
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Separation-Logic Helpers (`+0x8b4..+0x8c8`) -/

def preKeyEncryptScratchRest (sp : BitVec 64) (regId spk pkVal : BitVec 32) : SepProp :=
  memRegion sp 0x14 ∗
  ((sp + 0x14#64) ↦₃₂ regId) ∗
  memRegion (sp + 0x18#64) 0xc ∗
  ((sp + 0x24#64) ↦₃₂ spk) ∗
  memRegion (sp + 0x28#64) 0xc ∗
  ((sp + 0x34#64) ↦₃₂ pkVal) ∗
  ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
  ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
  ((sp + 0x50#64) ↦₆₄ (sp + 0x128#64))

theorem preKeyEncryptScratch'_eq (sp : BitVec 64) (regId spk pkVal : BitVec 32) :
    preKeyEncryptScratch' sp regId spk pkVal =
      ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ preKeyEncryptScratchRest sp regId spk pkVal := by
  unfold preKeyEncryptScratch' preKeyEncryptScratchRest
  ac_rfl

def encSpillsRest (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) : SepProp :=
  ((sp + 0x58#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0x60#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0x64#64) 4 ∗ ((sp + 0x68#64) ↦₆₄ x.ptA) ∗
  ((sp + 0x70#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0x78#64) ↦₆₄ x.remA) ∗
  ((sp + 0x80#64) ↦₆₄ x.locA) ∗ ((sp + 0x88#64) ↦₆₄ x.ssA) ∗ ((sp + 0x90#64) ↦₆₄ ss_vt) ∗
  ((sp + 0x98#64) ↦₆₄ x.idA) ∗ ((sp + 0xa0#64) ↦₆₄ id_vt) ∗
  ((sp + 0xa8#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0xd0#64) ↦₆₄ x.ssA) ∗ ((sp + 0xd8#64) ↦₆₄ ss_vt) ∗
  ((sp + 0xe0#64) ↦₆₄ x.idA) ∗ ((sp + 0xe8#64) ↦₆₄ id_vt) ∗
  ((sp + 0xf0#64) ↦₆₄ x.now.tvSec) ∗ ((sp + 0xf8#64) ↦₃₂ x.now.tvNsec) ∗
  memRegion (sp + 0xfc#64) 4 ∗ ((sp + 0x100#64) ↦₆₄ (sp + 0xb6f#64)) ∗
  ((sp + 0x108#64) ↦₆₄ x.remA)

theorem encSpillsAt_eq (ss_vt id_vt sp : BitVec 64) (x : WithStoresEncGhost) :
    encSpillsAtV ss_vt id_vt sp x =
      (((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      encSpillsRest ss_vt id_vt sp x := by
  unfold encSpillsAtV encSpillsRest
  ac_rfl

theorem tapeAfter_zero_entails_tapeAt (ctl cur : BitVec 64) (rest : List (BitVec 8))
    (hrest : rest.length < 2 ^ 63) :
    tapeAfter ctl cur rest 0 ⊢ tapeAt ctl cur rest := by
  unfold tapeAfter tapeAt
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := rfl
  rw [hcur, hlen]
  exact Entails.pure_right hrest (Entails.refl _)

theorem pollPreKeyEncrypt_split_580 (A : RustAlloc) (sp : BitVec 64) (kyBoxPtr : BitVec 64)
    (items : PendingPreKey) (kyber : Option PendingKyberPreKey) :
    pollE6c' A sp kyBoxPtr items kyber =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 120 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (kyber.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac := by
  unfold pollE6c'
  rw [mr_cut_add sp 0x46a 0x116 0x320 (by decide),
      mr_cut_add sp 0x580 120 0x2a8 (by decide)]
  simp only [sepConj_assoc]

theorem bitvec_ofNat_toNat_lt_32 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]
  omega

def preKeyEncryptCallRestFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (x : WithStoresEncGhost)
    (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x370#64) 0xf8 ∗
  preKeyEncryptScratchRest sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
  encSpillsRest ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x2a8 ∗
  optKyberAt A (sp + 0x8a0#64) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
  memRegion (sp + 0x8b8#64) 0x1fc ∗
  ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
  memRegion (sp + 0xad4#64) 0xac ∗
  memRegion x.ret 248 ∗
  nowAt s0.sp x.now ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - rootStack) ∗
  encSavedRegs s0.sp s0

theorem preKeyEncrypt_mem_unpack (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hrest : x.rest.length < 2 ^ 63)
    (hm : m ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV ss_vt id_vt sp x ∗
      pollE6c' A sp kyBoxPtr items sess.pendingKyberPreKey ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ R) :
    m ⊨ (((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  rw [preKeyEncryptScratch'_eq, encSpillsAt_eq, pollPreKeyEncrypt_split_580] at hm
  unfold encCommon at hm
  rw [hsp0, stackAt_sub sp encSubStack rootStack] at hm
  have htape := tapeAfter_zero_entails_tapeAt ctl x.cur x.rest hrest
  have hm_rearr : m ⊨
      tapeAfter ctl x.cur x.rest 0 ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) := by
    unfold preKeyEncryptCallRestFrame
    exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm
  have hm_tape := Satisfies.mono (sepConj_mono_left htape) hm_rearr
  exact Eq.mp (congrArg (m ⊨ ·) (by ac_rfl)) hm_tape

theorem otrEnc_pre_frame {Q : List (BitVec 8) → Prop} (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hQ : Q otr.pqrState)
    (hfl : img.FrozenLoaded s1) (hsym : s1.symtab = img.symtab)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x580#64)
    (hx1 : s1.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s1.readReg64 .x2 = x.ptA)
    (hx3 : s1.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hptlen : x.ptext.length < 2 ^ 32)
    (hx4 : s1.readReg64 .x4 = x.locA)
    (hlocA : x.locA ≠ 0#64)
    (hx5 : s1.readReg64 .x5 = x.remA)
    (hPm : Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
      ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
      ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA))
    (hm : s1.mem ⊨ Pm ∗
      ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) :
    s1.mem ⊨ (otrEncryptSpecQ Q C A ctl uuidTryParse S img).pre (preKeyOtrGhost x sp pqCap pqPtr otr) s1 ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold otrEncryptSpecQ otrEncryptSpec Spec.inImage preKeyOtrGhost optAddrAt
  dsimp only
  rw [hsp1]
  have hx3_nat : (s1.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3]
    exact bitvec_ofNat_toNat_lt_32 hptlen
  have hpure :
      (⌜Q otr.pqrState⌝ : SepProp) ∗
      ⌜img.FrozenLoaded s1 ∧ s1.symtab = img.symtab⌝ ∗
      ⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
        s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧
        x.ptext.length < 2 ^ 32 ∧
        s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
        ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) =
      ((⌜Q otr.pqrState⌝ ∗
        (⌜img.FrozenLoaded s1 ∧ s1.symtab = img.symtab⌝ ∗
          (⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
            s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧
            x.ptext.length < 2 ^ 32 ∧
            s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
            ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗
          stackAt sp rootStack ∗ A.pool))) ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hQ, ⟨hfl, hsym⟩, ⟨hx0, hx1, hx2, hx3_nat, hptlen, hx4, fun _ => hlocA, hx5⟩, hm'⟩

theorem otrEnc_post_unpack {Q : List (BitVec 8) → Prop} (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨ ((otrEncryptSpecQ Q C A ctl uuidTryParse S img).post
        (preKeyOtrGhost x sp pqCap pqPtr otr) s1 s2 ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) :
    let res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
    ∃ pqCap' pqPtr' : BitVec 64,
      res.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨
        sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗
        preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt A (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗
        ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0xac ∗
        memRegion x.ret 248 ∗
        encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ R) := by
  intro res
  change s2.mem ⊨ ((otrEncryptSpec C A ctl uuidTryParse S img).post
      (preKeyOtrGhost x sp pqCap pqPtr otr) s1 s2 ∗ _) ∗ R at hpost
  unfold otrEncryptSpec Spec.inImage at hpost
  dsimp only [optAddrAt] at hpost
  rw [hsp1] at hpost
  change s2.mem ⊨ ((⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64, otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2) ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
    tapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
    logOff img ∗ stackAt sp rootStack ∗ A.pool) ∗ _) ∗ R at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨pqCap', pqPtr', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      ((otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        tapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ stackAt sp rootStack ∗ A.pool ∗
        (((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
          ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨pqCap', pqPtr', hne, htr, ?_⟩
  unfold preKeyEncryptCallRestFrame at hmem
  rw [preKeyEncryptScratch'_eq, encSpillsAt_eq]
  unfold encCommon
  rw [hsp0, stackAt_sub sp encSubStack rootStack]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem

/-! ## `OTR::encrypt` Call (`+0x8b4..+0x8c8`) -/

theorem segPreKey_encrypt_call_ok
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState' kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R0 s0) := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hst with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr,
    hts, hexp, hlt, hpkVal, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩, htr,
    hx20, hx22, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  have hQ : Q otr.pqrState := env.q_otr hcur hscope hfrom
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have henc_fn := encEntry_eq_fnAddr env
  have hs_pc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x8b4#64 := by
    rw [← henc_fn]; exact hpc
  have hm_unp := preKeyEncrypt_mem_unpack kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess otr taken pqCap pqPtr k items
    pkVal kyBoxPtr sp R s0 hsp0 hrestlen hmem
  refine SegExit.of_sepWP hm_unp (preKeyEncrypt_step_bl hs_pc hrun hsp hal) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5,
      hs1_x19, hs1_x20, hs1_x22, hs1_x24, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hotr_call : subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 18446744073709515544#64)
      (otrEncryptSpecQ Q C A ctl uuidTryParse S img) := by
    rw [← henc_fn]; exact otrEnc_ok_at_enc env
  have hm1_pre := otrEnc_pre_frame kit.ss_vt ikit.id_vt C A ctl S img x prevCap prevPtr G sess otr taken
    pqCap pqPtr k items pkVal kyBoxPtr sp R Pm1 s0 s1
    hQ hfl1 hsym1 hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_x3 hptlen hs1_x4 hlocA hs1_x5 hPm1 hm1
  refine SegExit.call hotr_call (preKeyOtrGhost x sp pqCap pqPtr otr)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (otrEncryptSpecQ Q C A ctl uuidTryParse S img).onExit (preKeyOtrGhost x sp pqCap pqPtr otr) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      change sf.mem ⊨ ((⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
          S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s1 sf) ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ _) ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) at hpost
      rw [sepConj_assoc] at hpost
      exact onPanic_absorb_extra (onPanic_of_otrEnc (hs1_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt hpost))
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x24 : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    rw [hcs12.2.2.2.2.2.1, hs1_x24]; exact hx24
  obtain ⟨pqCap', pqPtr', hne2, hs2_tr, hm2⟩ :=
    otrEnc_post_unpack kit.ss_vt ikit.id_vt C A ctl S img x prevCap prevPtr G sess otr taken pqCap pqPtr k items
      pkVal kyBoxPtr sp R s0 s1 s2 hsp0 hs1_sp hpost2
  refine SegExit.next ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, hne2, ?_,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hfl2, hsym2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, hs2_x24, by reg_chain, by reg_chain, by reg_chain,
    hptlen, hrestlen, hlocA, hnow, hstack, hm2⟩
  rw [hs2_pc, ← henc_fn]

/-! ## `OTR::encrypt` Error Exit (`+0x8c8..+0x8ec`) -/

theorem preKeyEncryptScratch'_weaken_cmScratch (sp : BitVec 64) (regId spk pkVal : BitVec 32) :
    preKeyEncryptScratch' sp regId spk pkVal ⊢ cmScratch sp := by
  unfold preKeyEncryptScratch' cmScratch
  rw [memRegion_split sp 0x14 0x24 (by decide),
      mr_cut_add sp 0x14 4 0x20 (by decide),
      mr_cut_add sp 0x18 0xc 0x14 (by decide),
      mr_cut_add sp 0x24 4 0x10 (by decide),
      mr_cut_add sp 0x28 0xc 4 (by decide)]
  simp only [sepConj_assoc]
  exact sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
    (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (pointsTo64_entails_memRegion _ _)))))))))

private theorem list_len6 {α : Type} (ws : List α) (h : ws.length = 6) :
    ∃ w0 w1 w2 w3 w4 w5, ws = [w0, w1, w2, w3, w4, w5] := by
  rcases ws with _ | ⟨w0, ws⟩; · nomatch h
  rcases ws with _ | ⟨w1, ws⟩; · nomatch h
  rcases ws with _ | ⟨w2, ws⟩; · nomatch h
  rcases ws with _ | ⟨w3, ws⟩; · nomatch h
  rcases ws with _ | ⟨w4, ws⟩; · nomatch h
  rcases ws with _ | ⟨w5, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨w0, w1, w2, w3, w4, w5, rfl⟩
  · nomatch h

private theorem memRegion_24_exists_words64At (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 24 ∗ R) :
    ∃ v0 v1 v2 : BitVec 64, m ⊨ words64At a [v0, v1, v2] ∗ R := by
  obtain ⟨ws, hlen, hws⟩ := memRegion_exists_words64At 3 a (by decide) hm
  rcases ws with _ | ⟨v0, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨v1, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨v2, ws⟩; · nomatch hlen
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, hws⟩
  · nomatch hlen

def preKeyEncryptErrRestFrame (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x370#64) 0xf8 ∗
  preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
  encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5b8#64) 64 ∗
  memRegion (sp + 0x5f8#64) 0x2a8 ∗
  optKyberAt A (sp + 0x8a0#64) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
  memRegion (sp + 0x8b8#64) 0x1fc ∗
  ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
  memRegion (sp + 0xad4#64) 0x2c ∗
  memRegion (sp + 0xb18#64) 0x68 ∗
  memRegion x.ret 248 ∗
  encCommon A ctl img x draws s0

theorem preKeyEncrypt_err_unpack (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (e : SignalProtocolError) (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (_hne : (Except.error e : Except SignalProtocolError SignalMessage) ≠ .error .panic)
    (hm : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.error e) ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x draws s0 ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 v0 v1 v2 : BitVec 64) (H : SepProp),
      SpeStaged A x.ret (.protocol e) [w0, w1, w2, w3, w4, w5] H ∧
      (s.mem ⊨ (((sp + 0x580#64) ↦₆₄ errTag) ∗
          words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2]) ∗
        (preKeyEncryptErrRestFrame ss_vt id_vt A ctl img x prevCap prevPtr G sess taken otr' pqCap' pqPtr' k items
          pkVal kyBoxPtr draws sp H s0 ∗ R)) := by
  have hp_pan : (ApiError.protocol e : ApiError AddrVal Unit) ≠ .panic := by
    intro h; cases h
  unfold signalMessageResultAt errResultAt at hm
  dsimp only at hm
  have h588 : (sp + 0x580#64) + 8#64 = sp + 0x588#64 := by bv_omega
  have h5b8 : (sp + 0x580#64) + 56#64 = sp + 0x5b8#64 := by bv_omega
  rw [h588, h5b8] at hm
  have had4 : memRegion (sp + 0xad4#64) 0xac =
      memRegion (sp + 0xad4#64) 0x2c ∗ memRegion (sp + 0xb00#64) 24 ∗
      memRegion (sp + 0xb18#64) 0x68 := by
    rw [mr_cut_add sp 0xad4 0x2c 0x80 (by decide),
        mr_cut_add sp 0xb00 24 0x68 (by decide)]
  rw [had4] at hm
  have hstage := speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol e) hp_pan
  have hm_rearr : s.mem ⊨ encErrAt A (sp + 0x588#64) (.protocol e) ∗
      (memRegion (sp + 0xb00#64) 24 ∗
        ((sp + 0x580#64) ↦₆₄ errTag) ∗
        sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗
        preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt A (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗
        ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0x2c ∗
        memRegion (sp + 0xb18#64) 0x68 ∗
        memRegion x.ret 248 ∗
        encCommon A ctl img x draws s0 ∗ R) := by
    change s.mem ⊨ speAt A (utf8 "encrypt") (sp + 0x588#64) e ∗ _
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  have hm_st := Satisfies.mono (sepConj_mono_left hstage) hm_rearr
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm_st
  obtain ⟨ws, H, hm_st⟩ := hm_st
  have hm_pure : s.mem ⊨ ⌜SpeStaged A x.ret (.protocol e) ws H⌝ ∗
      (memRegion (sp + 0xb00#64) 24 ∗
        (((sp + 0x580#64) ↦₆₄ errTag) ∗
          words64At (sp + 0x588#64) ws ∗
          preKeyEncryptErrRestFrame ss_vt id_vt A ctl img x prevCap prevPtr G sess taken otr' pqCap' pqPtr' k items
            pkVal kyBoxPtr draws sp H s0 ∗ R)) := by
    unfold preKeyEncryptErrRestFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_st
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hst, hm_v⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := list_len6 ws hst.2.1
  obtain ⟨v0, v1, v2, hm_v⟩ := memRegion_24_exists_words64At (sp + 0xb00#64) hm_v
  refine ⟨w0, w1, w2, w3, w4, w5, v0, v1, v2, H, hst, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_v

theorem preKeyEncrypt_err_tail_mem (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp)
    (s0 s3 : State)
    (hPm : Pm ⊢ ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
      words64At (sp + 0xb00#64) [w3, w4, w5])
    (hm : s3.mem ⊨ Pm ∗
      (preKeyEncryptErrRestFrame ss_vt id_vt A ctl img x prevCap prevPtr G sess taken otr' pqCap' pqPtr' k items
        pkVal kyBoxPtr draws sp H s0 ∗ R)) :
    s3.mem ⊨
      (dropRecordSlots A sp cmScratch ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
          (some (pqCap', pqPtr', otr')) none
          (memRegion (sp + 0x46a#64) 0x436 ∗
            optKyberAt A (sp + 0x8a0#64) kyBoxPtr
              (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗
            words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H) ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommon A ctl img x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold preKeyEncryptErrRestFrame at hm1
  have hscr := preKeyEncryptScratch'_weaken_cmScratch sp sess.localRegistrationId items.signedPreKeyId pkVal
  have h280 := pointsTo64_entails_memRegion (sp + 0x280#64) (sp + 0x128#64)
  have hcm := cmSlotAt_none_pack A sp k
  have h580 :
      ((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ⊢
      memRegion (sp + 0x580#64) 56 := by
    rw [mr_cut_add sp 0x580 8 48 (by decide)]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (words64At_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp + 0x588#64)
        (by simp only [List.length_cons, List.length_nil]; decide))
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x436 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 56 ∗
        memRegion (sp + 0x5b8#64) 64 ∗ memRegion (sp + 0x5f8#64) 0x2a8 := by
    rw [mr_cut_add sp 0x46a 0x116 0x320 (by decide),
        mr_cut_add sp 0x580 56 0x2e8 (by decide),
        mr_cut_add sp 0x5b8 64 0x2a8 (by decide)]
  have hbk : ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ⊢ memRegion (sp + 0xab4#64) 32 := by
    have h := pointsToBytes_entails_memRegion (sp + 0xab4#64) items.baseKey.bytes.toList
    rwa [items.baseKey.bytes.toList_length] at h
  have h8b8_eq :
      memRegion (sp + 0x8b8#64) 0x248 =
      memRegion (sp + 0x8b8#64) 0x1fc ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0x2c := by
    rw [mr_cut_add sp 0x8b8 0x1fc 0x4c (by decide),
        mr_cut_add sp 0xab4 32 0x2c (by decide)]
  have hm_rearr : s3.mem ⊨
      (preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        (((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
          memRegion (sp + 0x370#64) 0xf8 ∗ ((sp + 0x468#64) ↦₈ 0#8)) ∗
        (((sp + 0x580#64) ↦₆₄ errTag) ∗
          words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5]) ∗
        ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList)) ∗
      (sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt A (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗ memRegion (sp + 0xad4#64) 0x2c ∗
        words64At (sp + 0xb00#64) [w3, w4, w5] ∗ memRegion (sp + 0xb18#64) 0x68 ∗
        H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗
        encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono hscr (sepConj_mono h280 (sepConj_mono hcm (sepConj_mono h580 hbk))))) hm_rearr
  unfold dropRecordSlots otrSlotAt
  dsimp only
  rw [h46a_eq, h8b8_eq]
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm_mono

theorem segPreKey_encrypt_err_ok
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (e : SignalProtocolError)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (herr : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .error e)
    (hret : PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, _hpkVal, hnp, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩, htr,
    _hx20, _hx22, _hx24, hx25, hx26, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  set sp := s0.sp - 0xbe0#64
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have herr' : res.1 = .error e := herr
  rw [herr'] at hnp hmem
  have he_np : e ≠ .panic := fun h => hnp (congrArg Except.error h)
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl he_np
  have henc_fn := encEntry_eq_fnAddr env
  have hs_pc : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x8c8#64 := by
    rw [← henc_fn]; exact hpc
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, ← sp_sub_60_eq_add_b80 s0.sp]
  obtain ⟨w0, w1, w2, w3, w4, w5, v0, v1, v2, H, hst, hm_err⟩ :=
    preKeyEncrypt_err_unpack kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess taken res.2 pqCap' pqPtr' k items
      pkVal kyBoxPtr e (S.draws otr.pqrState x.rest) sp R s0 s hnp hmem
  refine SegExit.of_sepWP hm_err (preKeyEncrypt_step_err hs_pc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := callInv_steps hfl hsym hsteps23 hL2
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm3_tail := preKeyEncrypt_err_tail_mem kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess taken res.2 pqCap' pqPtr'
    k items pkVal kyBoxPtr w0 w1 w2 w3 w4 w5 (S.draws otr.pqrState x.rest) sp H R Pm3 s0 s3 hPm3 hm3
  have htm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (.protocol e)) s0 s3 := by
    rw [← hprot]
    exact tailModel_of_otr_err (hs3_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt herr
  have hfinal :
      kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
    have hexec := execOk_of_preKeyOtrGhost_error herr
    have hm : x.model C S uuidTryParse (preKeyErrAnswers r) =
        (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
      rw [EncryptGhost.model, messageEncrypt_eq_flat]
      simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
        hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
    rw [congrArg Prod.snd hm]
    rfl
  have hidfinal :
      ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
    have hexec := execOk_of_preKeyOtrGhost_error herr
    have hm : x.model C S uuidTryParse (preKeyErrAnswers r) =
        (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
      rw [EncryptGhost.model, messageEncrypt_eq_flat]
      simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
        hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
    rw [congrArg Prod.snd hm]
    rfl
  have hdraws := draws_of_not_stale (S := S) hcur hfrom hrem hpk hts hexp hlt
  exact tailPreKeyEncryptErr_ok env x R0 s0 s3
    (preKeyErrAnswers r) (.protocol e)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
    (some (pqCap', pqPtr', res.2)) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
    htm hst
    ⟨by rw [hs3_pc, ← henc_fn],
      ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hfl3, hsym3, hs3_vregs.trans hvregs⟩,
      ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstack, by rw [hdraws, hfinal, hidfinal]; exact Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [R])) hm3_tail⟩

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
