/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessage
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncrypt
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailSym
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg5
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageLengthBound
import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApiFacts
import ProofLib.RegChain

/-!
# CLI MessageEncrypt `WithStoresVT` (Part 6): `SegPreKey` tail (`+0x8b4..+0xa70`) and `h45_segPreKey_okVT_trap`
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalSpqrV1 (TokenInit)
open CryptoVerification.Cli.LibsignalPublicApi (encryptWithStoresName)

set_option maxRecDepth 200000
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

section SegPreKeyTail

private theorem h45_segExitVT_of_sepWP_trap {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (trTrapProgAt img.base C abs) mid s P post)
    (hcont : ∀ sm Pm, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

private theorem h45_segExitVT_call_sub_trap {α : Type} {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (trTrapProgAt img.base C abs) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (trTrapProgAt img.base C abs) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (trTrapProgAt img.base C abs).CodeLoaded s.mem →
      Steps (trTrapProgAt img.base C abs) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome xc (F ∗ R) s hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_st, hpost⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ hoom_st hpost).elim

private theorem h45_otrEnc_ok_at_enc_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope C ctl S encRecord abs}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs) :
    subroutine_ok (trTrapProgAt img.base C abs)
      (encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img) := by
  have h := hEnv.callees.otrEnc
  unfold OtrEncryptOkT_trap at h
  have haddr : (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName =
      encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>"),
      Pf.SegPreKey.encEntry_eq_fnAddr_trap (h45_envF hEnv),
      Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt")]
    bv_omega
  rwa [← haddr]

private theorem h45_otrEnc_pre_frame (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (h64 : 64 ≤ x.rest.length)
    (hQ : otr.pqrState.length < 2 ^ 32)
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
        memRegion (sp + 0x580#64) 120 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (TokenInit img ∗ R))) :
    s1.mem ⊨ (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).pre (preKeyOtrGhost x sp pqCap pqPtr otr) s1 ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage preKeyOtrGhost optAddrAt
  dsimp only
  rw [hsp1]
  have hx3_nat : (s1.readReg64 .x3).toNat = x.ptext.length := by
    rw [hx3]
    exact bitvec_ofNat_toNat_lt_32 hptlen
  have hpure :
      (⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ : SepProp) ∗
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
        memRegion (sp + 0x580#64) 120 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (TokenInit img ∗ R))) =
      ((⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ TokenInit img ∗
        (⌜img.FrozenLoaded s1 ∧ s1.symtab = img.symtab⌝ ∗
          (⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
            s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧
            x.ptext.length < 2 ^ 32 ∧
            s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
            ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗ CryptoVerification.SignalSession.Coins.coinsAt img.base x.cur x.rest ∗ logOff img ∗
          stackAt sp rootStack ∗ A.pool))) ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
        ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
        ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) := by
    ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨⟨hQ, h64⟩, ⟨hfl, hsym⟩, ⟨hx0, hx1, hx2, hx3_nat, hptlen, hx4, fun _ => hlocA, hx5⟩, hm'⟩

private theorem h45_otrEnc_post_unpack (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (S : SpqrModel) (img : Obj.Image)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr : BitVec 64)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨ ((CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).post
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
        encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ (TokenInit img ∗ R)) := by
  intro res
  unfold CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptSpec Spec.inImage at hpost
  dsimp only [optAddrAt] at hpost
  rw [hsp1] at hpost
  change s2.mem ⊨ ((TokenInit img ∗ ⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64, otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2) ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
    logOff img ∗ stackAt sp rootStack ∗ A.pool) ∗ _) ∗ R at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨pqCap', pqPtr', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      ((otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest (S.draws otr.pqrState x.rest) ∗
        logOff img ∗ stackAt sp rootStack ∗ A.pool ∗
        (((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗ ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗
          ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (TokenInit img ∗ R)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hne, htr⟩, hmem⟩
  refine ⟨pqCap', pqPtr', hne, htr, ?_⟩
  unfold preKeyEncryptCallRestFrame at hmem
  rw [preKeyEncryptScratch'_eq, encSpillsAt_eq]
  unfold encCommon
  rw [hsp0, stackAt_sub sp encSubStack rootStack]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hmem

theorem h45_segPreKey_encrypt_call_ok_trap
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : Pf.SegPreKey.PreKeyEncryptState' kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      (TokenInit img ∗ R0) s0 s) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (Pf.SegPreKey.PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items
        (TokenInit img ∗ R0) s0) := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hst with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr,
    hts, hexp, hlt, hpkVal, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩, htr,
    hx20, hx22, hx24, hx25, hx26, _hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  have hQ : otr.pqrState.length < 2 ^ 32 :=
    fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hscope hcur
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap (h45_envF hEnv)
  have hs_pc : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x8b4#64 := by
    rw [← henc_fn]; exact hpc
  have hmem' : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      pollE6c' A sp kyBoxPtr items sess.pendingKyberPreKey ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x 0 s0 ∗ (TokenInit img ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; ac_rfl)) hmem
  have hm_unp := Pf.SegPreKey.preKeyEncrypt_mem_unpack kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess otr taken pqCap pqPtr k items
    pkVal kyBoxPtr sp (TokenInit img ∗ R) s0 hsp0 hrestlen hmem'
  refine h45_segExitVT_of_sepWP_trap hm_unp (Pf.SegPreKey.preKeyEncrypt_step_bl_trap hs_pc hrun hsp hal) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5,
      hs1_x19, hs1_x20, hs1_x22, hs1_x24, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hotr_call : subroutine_ok (trTrapProgAt img.base C abs)
      ((trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + bv% ((2^64 + ls_off% "<libsignal_protocol::triple_ratchet::OutgoingTripleRatchet>::encrypt::<libsignal_cli_ratchet::Coins>" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
      (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img) := by
    rw [← henc_fn]; exact h45_otrEnc_ok_at_enc_trap hEnv
  have hm1_pre := h45_otrEnc_pre_frame kit.ss_vt ikit.id_vt C A ctl S img x prevCap prevPtr G sess otr taken
    pqCap pqPtr k items pkVal kyBoxPtr sp R Pm1 s0 s1
    h64 hQ hfl1 hsym1 hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_x3 hptlen hs1_x4 hlocA hs1_x5 hPm1 hm1
  refine h45_segExitVT_call_sub_trap hotr_call (preKeyOtrGhost x sp pqCap pqPtr otr)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (CryptoVerification.Cli.LibsignalSpqrV1.otrEncryptSpecT C A ctl uuidTryParse S img).onExit (preKeyOtrGhost x sp pqCap pqPtr otr) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      change sf.mem ⊨ ((⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
          S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s1 sf) ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ _) ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) at hpost
      rw [sepConj_assoc] at hpost
      exact Pf.SegPreKey.onPanic_absorb_extra (Pf.SegPreKey.onPanic_of_otrEnc (hs1_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt hpost))
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x24 : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    rw [hcs12.2.2.2.2.2.1, hs1_x24]; exact hx24
  obtain ⟨pqCap', pqPtr', hne2, hs2_tr, hm2⟩ :=
    h45_otrEnc_post_unpack kit.ss_vt ikit.id_vt C A ctl S img x prevCap prevPtr G sess otr taken pqCap pqPtr k items
      pkVal kyBoxPtr sp R s0 s1 s2 hsp0 hs1_sp hpost2
  have hm2' : s2.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗
      memRegion x.ret 248 ∗
      encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtra kit st0 ikit ist0 x s0 ∗ (TokenInit img ∗ R0)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [R]; ac_rfl)) hm2
  refine h45_segExitVT_of_segExit_trap (Pf.SegFrom.SegExit.next_trap ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, hne2, ?_,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hfl2, hsym2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, hs2_x24, by reg_chain, by reg_chain, by reg_chain,
    hptlen, hrestlen, hlocA, hnow, hstack, hm2'⟩)
  rw [hs2_pc, ← henc_fn]

theorem h45_segPreKey_encrypt_err_ok_trap
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
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
    (hret : Pf.SegPreKey.PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  let envF := h45_envF hEnv
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
  have henc_fn := Pf.SegPreKey.encEntry_eq_fnAddr_trap envF
  have hs_pc : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x8c8#64 := by
    rw [← henc_fn]; exact hpc
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, ← sp_sub_60_eq_add_b80 s0.sp]
  obtain ⟨w0, w1, w2, w3, w4, w5, v0, v1, v2, H, hst, hm_err⟩ :=
    Pf.SegPreKey.preKeyEncrypt_err_unpack kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess taken res.2 pqCap' pqPtr' k items
      pkVal kyBoxPtr e (S.draws otr.pqrState x.rest) sp R s0 s hnp hmem
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm_err (Pf.SegPreKey.preKeyEncrypt_step_err_trap hs_pc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := callInv_steps hfl hsym hsteps23 hL2
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm3_tail := Pf.SegPreKey.preKeyEncrypt_err_tail_mem kit.ss_vt ikit.id_vt A ctl img x prevCap prevPtr G sess taken res.2 pqCap' pqPtr'
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
  rw [← h45_segExit_kitF_trap]
  exact Tails.tailPreKeyEncryptErr_ok_trap envF x R0 s0 s3
    (preKeyErrAnswers r) (.protocol e)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
    (some (pqCap', pqPtr', res.2)) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
    ((h45_tailModel_kitF kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (.protocol e)) s0 s3).mpr htm)
    hst
    ((h45_encTailV_kitF kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) _ _ _ R0 s0 s3).mpr
      ⟨by rw [hs3_pc, ← henc_fn],
        ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hfl3, hsym3, hs3_vregs.trans hvregs⟩,
        ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
        hstack, by rw [hdraws, hfinal, hidfinal]; exact Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [R])) hm3_tail⟩)

theorem h45_segPreKey_buildMessage_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (sm : SignalMessage)
    (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hok : ((preKeyOtrGhost (s0.sp - 0xbe0#64 |> fun _sp => x) (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm)
    (hret : Pf.SegPreKey.PreKeyEncryptRetState kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          R s0 sf) := by
  let envF := h45_envF hEnv
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx22, hx24, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp_eq : sp = s0.sp - 0xbe0#64 := rfl
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have hok' : res.1 = .ok sm := hok
  have hentry : encEntry img = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName :=
    Pf.SegPreKey.encEntry_eq_fnAddr_trap envF
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr encryptWithStoresName + 0x8c8#64 := by
    rw [hs_pc, hentry]
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  let R' := encStoreExtra kit st0 ikit ist0 x s0 ∗ R
  change s.mem ⊨
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
    optKyberAt A (sp + 0x8a0#64) kyBoxPtr
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
    memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
    encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗ R' at hm
  rw [hok'] at hm
  obtain ⟨msgG, u0, ik0, ik1, ik2, ik3,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    k0, k1, k2, kd0, kd1, kd2, bk0, bk1, bk2, bk3, bkd0, bkd1, bkd2, bkd3,
    ikd0, ikd1, ikd2, ikd3, H_sm, H_ky, hw0, hmsg_len, hik, hbk, hsm_rel, hky_rel, hm_e6d⟩ :=
    Pf.SegPreKey.buildPreKeyMsg_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
      items pkVal sm (S.draws otr.pqrState x.rest) sp R' s0 s hm
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm_e6d
    (Pf.SegPreKey.buildPreKeyMsg_step_bl_trap hs_pc' hrun hsp hal hx22 hx25 hx26 hx29' hw0) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8,
      hs1_x19, hs1_x20, hs1_x22, _, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have ⟨hfl1, hsym1⟩ := Pf.SegFrom.callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hs1_pc' : s1.pc = encEntry img + bv% ((2^64 + ls_off% "<libsignal_protocol::protocol::PreKeySignalMessage>::new" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64) := by
    rw [hs1_pc, hentry]
  let call : PreKeyMsgNewCall :=
    { ret := sp + 0x580#64, ver := res.2.sessionVersion, regId := sess.localRegistrationId,
      preKeyId := items.preKeyId, spk := items.signedPreKeyId, kyA := sp + 0x950#64,
      kyPtr := kyBoxPtr,
      kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload),
      bkA := sp + 0xae0#64, baseKey := items.baseKey, ikA := sp + 0xb00#64,
      ik := res.2.localIdentityKey, msgA := sp + 0x8b8#64, msgG := msgG, msg := sm }
  have hm1_sub : s1.mem ⊨
      (Pm1 ∗ Pf.SegPreKey.buildPreKeyMsgRestFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp H_sm H_ky s0) ∗ R' :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm1_pack := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm1)
        (Pf.SegPreKey.preKeyMsgNew_pre_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
          items pkVal msgG sm ik0 ik1 ik2 ik3
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
          k0 k1 k2 bk0 bk1 bk2 bk3 H_sm H_ky (S.draws otr.pqrState x.rest) sp s0 s1
          hsp_eq hs1_sp hik hbk hsm_rel hky_rel)))
    hm1_sub
  have hcall_len : call.model.serialized.length < 2 ^ 42 :=
    call.model_serialized_length_lt hmsg_len
      (kyber_ciphertext_length_lt (hEnv.scopeIn r hscope) hcur)
  have hcall_pure :
      (s1.readReg64 .x0).setWidth 8 = call.ver ∧ (s1.readReg64 .x1).setWidth 32 = call.regId ∧
      (s1.readReg64 .x2).setWidth 32 = (if call.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, call.preKeyId = some v → (s1.readReg64 .x3).setWidth 32 = v) ∧
      (s1.readReg64 .x4).setWidth 32 = call.spk ∧ s1.readReg64 .x5 = call.kyA ∧
      s1.readReg64 .x6 = call.bkA ∧ s1.readReg64 .x7 = call.ikA ∧
      s1.readReg64 .x8 = call.ret ∧ call.model.serialized.length < 2 ^ 42 :=
    ⟨hs1_x0, hs1_x1, hs1_x2.trans hx24, fun v hv => hs1_x3.trans (hpkVal v hv),
      hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8, hcall_len⟩
  have hm1_pre : s1.mem ⊨ (preKeyMsgNewSpec A).pre call s1 ∗
      (Pf.SegPreKey.preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    unfold preKeyMsgNewSpec
    dsimp only [call]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcall_pure, Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1_pack⟩
  have hpref01 : s0.trace <+: s1.trace := by
    rw [hs1_tr, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩
  refine Pf.SegFrom.SegExit.call_trap (Pf.SegPreKey.preKeyMsgNew_ok_at_enc_trap envF) call hs1_pc' hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (preKeyMsgNewSpec A).onExit call code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      have hp : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗
          (Pf.SegPreKey.preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
            items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ encStoreExtra kit st0 ikit ist0 x s0) ∗ R := by
        dsimp only [preKeyMsgNewSpec, R'] at hpost; exact Eq.mp (congrArg (sf.mem ⊨ ·) (by ac_rfl)) hpost
      exact Pf.SegPreKey.onPanic_of_alloc hpref01 hp)
    ?_
  intro s2 hL1 hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have ⟨hfl2, hsym2⟩ := Pf.SegFrom.callInv_steps hfl1 hsym1 hsteps12 hL1
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x22 : s2.readReg64 .x22 = sp + 0x8b8#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  unfold preKeyMsgNewSpec at hpost2
  dsimp only [call] at hpost2
  rw [hs1_sp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost2
  rcases hpost2 with ⟨hs2_tr, hm2⟩
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  have hm2' : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) call.model) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ res.2.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      Pf.SegPreKey.preKeyMsgCallFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R' :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by ac_rfl)) hm2
  obtain ⟨psmG,
    pw0, pw1, pw2, pw3, pw4, pw5, pw6, pw7, pw8, pw9, pw10, pw11, pw12, pw13, pw14,
    pw15, pw16, pw17, pw18, pw19, pw20, pw21, pw22, pw23, pw24, pw25, pw26, pw27, pw28, pw29, pw30,
    v0, v1, v2,
    pd0, pd1, pd2, pd3, pd4, pd5, pd6, pd7, pd8, pd9, pd10, pd11, pd12, pd13, pd14,
    pd15, pd16, pd17, pd18, pd19, pd20, pd21, pd22, pd23, pd24, pd25, pd26, pd27, pd28, pd29, pd30,
    H_psm, hpw0, hpsm_rel, hm2_e6e⟩ :=
    Pf.SegPreKey.cmCopy_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
      items pkVal call.model (S.draws otr.pqrState x.rest) sp R' s0 s2 hsp_eq hm2'
  refine Pf.SegFrom.SegExit.of_sepWP_trap hm2_e6e
    (Pf.SegPreKey.cmCopy_step_ok_trap hs2_pc hs2_run hs2_sp' hs2_al hs2_x22 hs2_x25 hpw0) ?_
  intro s3 Pm3 hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := Pf.SegFrom.callInv_steps hfl2 hsym2 hsteps23 hL2
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_sub : s3.mem ⊨
      (Pm3 ∗ Pf.SegPreKey.cmCopyRestFrame kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp H_psm s0) ∗ R' :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm3
  have hm3_cm := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm3)
        (Pf.SegPreKey.cmCopy_post_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
          psmG call.model
          pw0 pw1 pw2 pw3 pw4 pw5 pw6 pw7 pw8 pw9 pw10 pw11 pw12 pw13 pw14
          pw15 pw16 pw17 pw18 pw19 pw20 pw21 pw22 pw23 pw24 pw25 pw26 pw27 pw28 pw29 pw30
          H_psm (S.draws otr.pqrState x.rest) sp s0 hpsm_rel)))
    hm3_sub
  have hsteps15 := stepsThroughEncrypt_of_preKey_ok hcur hscope hfrom hrem hpk hts hexp hlt hok'
  refine Pf.SegFrom.SegExit.next_trap ⟨.preKeySignalMessage call.model, res.2, pqCap', pqPtr',
    hsteps15, ?_⟩
  refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hfl3, hsym3,
      hs3_vregs.trans ((hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs))⟩,
    hs3_tr.trans hs2_tr', ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk,
    Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [sp, call, PreKeyMsgNewCall.model, R']; ac_rfl)) hm3_cm⟩
  rw [hs3_pc, cmPC, hentry]

theorem h45_segPreKey_tail_ok_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hst : Pf.SegPreKey.PreKeyEncryptState' kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      (TokenInit img ∗ R0) s0 s) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          (TokenInit img ∗ R0) s0 sf) := by
  refine h45_segExitVT_trans_trap
    (h45_segPreKey_encrypt_call_ok_trap hEnv x r sess otr taken pqCap pqPtr k items R0 s0 s
      h64 hcur hscope hfrom hrem hpk hst)
    fun s2 hret => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact h45_segExitVT_of_false_trap
      (h45_segExitVT_of_segExit_trap
        (h45_segPreKey_encrypt_err_ok_trap hEnv x r sess otr taken pqCap pqPtr k items e (TokenInit img ∗ R0) s0 s2
          hcur hscope hfrom hrem hpk hres hret))
  · exact h45_segExitVT_of_segExit_trap
      (h45_segPreKey_buildMessage_ok_trap hEnv x r sess otr taken pqCap pqPtr k items sm (TokenInit img ∗ R0) s0 s2
        hcur hscope hfrom hrem hpk hres hret)

theorem h45_segPreKey_okVT_trap {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (hEnv : EncEnvT_trap kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length)
    (his : sess.pendingPreKey.isSome = true)
    (hkey : KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k
      (TokenInit img ∗ R0) s0 s) :
    h45_SegExitVT_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr'
          (TokenInit img ∗ R0) s0 sf) := by
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.1
  have hscope := hkey.2.1
  have hfrom := hkey.2.2.1
  have hrem := hkey.2.2.2.1
  refine h45_segExitVT_trans_trap
    (h45_segExitVT_of_segExit_trap
      (h45_segPreKey_unackItems_to_dur_ok_trap hEnv x r sess otr taken pqCap pqPtr k items
        (TokenInit img ∗ R0) s0 s hpk hkey)) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine h45_segExitVT_trans_trap
    (h45_segExitVT_of_segExit_trap
      (h45_segPreKey_staleness_to_add_ok_trap hEnv x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen (TokenInit img ∗ R0) s0 s1
        hcur hscope hfrom hrem hpk hdur)) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact h45_segExitVT_of_false_trap
      (h45_segExitVT_of_segExit_trap
        (h45_segPreKey_stale_ok_trap hEnv x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (TokenInit img ∗ R0) s0 s2
          hcur hscope hfrom hrem hpk hlt hadd))
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine h45_segExitVT_trans_trap
      (h45_segExitVT_of_segExit_trap
        (h45_segPreKey_regId_kyber_ok_trap hEnv x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (TokenInit img ∗ R0) s0 s2
          hcur hscope hlt_f hadd)) ?_
    intro s3 he6c
    exact h45_segPreKey_tail_ok_trap hEnv x r sess otr taken pqCap pqPtr k items R0 s0 s3
      h64 hcur hscope hfrom hrem hpk he6c

end SegPreKeyTail

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
