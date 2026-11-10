/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg6Placed
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailEncryptPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyTailBuildMessagePlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.AssemblyPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.SpqrV1Empty
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable CLI `MessageEncrypt` `WithStoresVTPlaced`: `SegPreKey` Tail and Top-Level Composition

Proves `h45_segPreKey_placed_okVT`, `withStores_placed_okVT_fs`, `withStores_placed_okVT`, and
`withStoresEncPlacedSpecVT_cli` on Block `464` (`lsProg_464 Hk`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt

open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section SegPreKeyTail

private theorem h45_segExitVT_of_sepWP_placed [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp} {s0 s : State} {next : State → Prop}
    {mid : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R)) (hwp : SepWP (lsProg_464 Hk) mid s P post)
    (hcont : ∀ sm Pm, (lsProg_464 Hk).CodeLoaded s.mem → Steps (lsProg_464 Hk) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) → post sm Pm →
      h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

private theorem h45_otrEnc_placed_pre_frame [LibsignalPlacement]
    (F0 : SepProp) (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr sp : BitVec 64)
    (R Pm : SepProp) (s0 s1 : State) (h64 : 64 ≤ x.rest.length) (hQ : otr.pqrState.length < 2 ^ 32)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem) (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x580#64) (hx1 : s1.readReg64 .x1 = sp + 0x288#64)
    (hx2 : s1.readReg64 .x2 = x.ptA) (hx3 : s1.readReg64 .x3 = BitVec.ofNat 64 x.ptext.length)
    (hptlen : x.ptext.length < 2 ^ 32) (hx4 : s1.readReg64 .x4 = x.locA) (hlocA : x.locA ≠ 0#64)
    (hx5 : s1.readReg64 .x5 = x.remA)
    (hPm : Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
      ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA))
    (hm : s1.mem ⊨ Pm ∗ ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (F0 ∗ R))) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).pre
        (preKeyOtrGhost x sp pqCap pqPtr otr) s1 ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold StoreKit.withLsRoCl otrEncryptPlacedSpecQT otrEncryptPlacedSpecQF otrEncryptPlacedSpec preKeyOtrGhost optAddrAt
  dsimp only; rw [hsp1]
  have hx3_nat : (s1.readReg64 .x3).toNat = x.ptext.length := by rw [hx3]; exact bitvec_ofNat_toNat_lt_32 hptlen
  have hpure :
      (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ : SepProp) ∗
      ⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗
      ⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
        s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
        s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
        ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
      ((otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
        memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
        stackAt sp rootStack ∗ A.pool ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
        (F0 ∗ R))) =
      (((⌜otr.pqrState.length < 2 ^ 32 ∧ 64 ≤ x.rest.length⌝ ∗ F0 ∗
          (⌜s1.readReg64 .x0 = sp + 0x580#64 ∧ s1.readReg64 .x1 = sp + 0x288#64 ∧
            s1.readReg64 .x2 = x.ptA ∧ (s1.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
            s1.readReg64 .x4 = (if (some x.loc).isSome then x.locA else 0#64) ∧
            ((some x.loc).isSome → x.locA ≠ 0#64) ∧ s1.readReg64 .x5 = x.remA⌝ ∗
          otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
          memRegion (sp + 0x580#64) 120 ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp rootStack ∗ A.pool)) ∗
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗
      (((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗ R)) := by
    sep_ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hcrl1, ⟨hQ, h64⟩, ⟨hx0, hx1, hx2, hx3_nat, hptlen, hx4, fun _ => hlocA, hx5⟩, hm'⟩

private theorem h45_otrEnc_placed_post_unpack [LibsignalPlacement]
    (F0 : SepProp) (ss_vt id_vt : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (kyBoxPtr sp : BitVec 64)
    (R : SepProp) (s0 s1 s2 : State) (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).post
        (preKeyOtrGhost x sp pqCap pqPtr otr) s1 s2 ∗
      ((((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
        ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
        preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0)) ∗ R) :
    let res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
    ∃ pqCap' pqPtr' : BitVec 64,
      StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧ res.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨
        sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
        encSpillsAtV ss_vt id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
        optKyberAt A (sp + 0x8a0#64) kyBoxPtr
          (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
        memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
        memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
        encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗ (F0 ∗ R)) := by
  intro res
  unfold StoreKit.withLsRoCl otrEncryptPlacedSpecQT otrEncryptPlacedSpecQF otrEncryptPlacedSpec at hpost
  dsimp only [optAddrAt] at hpost; rw [hsp1] at hpost
  change s2.mem ⊨ ((⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
    (F0 ∗ ⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64, otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2) ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
      cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
      FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool)) ∗ _) ∗ R at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨pqCap', pqPtr', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
      (⌜res.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
        ((otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗
          signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗
          (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.loc x.locA ∗ protocolAddressAt A x.rem x.remA ∗
          cliTapeAfter ctl x.cur x.rest (S.draws otr.pqrState x.rest) ∗
          FromRecordCallees.lsLogOff ∗ stackAt sp rootStack ∗ A.pool ∗
          (((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
            ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗ ((sp + 0xc8#64) ↦₆₄ x.locA)) ∗
          preKeyEncryptCallRestFrame ss_vt id_vt A x prevCap prevPtr G sess taken k items pkVal kyBoxPtr sp s0) ∗
          (F0 ∗ R))) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hcrl2, ⟨hne, htr⟩, hmem⟩
  refine ⟨pqCap', pqPtr', hcrl2, hne, htr, ?_⟩
  unfold preKeyEncryptCallRestFrame at hmem
  rw [preKeyEncryptScratch'_eq, encSpillsAt_eq]; unfold encCommonPlaced
  rw [hsp0, stackAt_sub sp encSubStack rootStack]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem

theorem h45_segPreKey_encrypt_call_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState'Placed kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (PreKeyEncryptRetStatePlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0) := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hst with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr,
    hts, hexp, hlt, hpkVal, hpc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr,
    hx20, hx22, hx24, hx25, hx26, _hx27, hx28, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  have hQ : otr.pqrState.length < 2 ^ 32 := fromSessionState_pqrState hfrom ▸ hEnv.scopeQ r sess hscope hcur
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hmem' : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ pollE6c' A sp kyBoxPtr items sess.pendingKyberPreKey ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ (F0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hmem
  have hm_unp := preKeyEncrypt_placed_mem_unpack kit.ss_vt ikit.id_vt A ctl x prevCap prevPtr G sess otr taken pqCap pqPtr k items
    pkVal kyBoxPtr sp (F0 ∗ R) s0 hsp0 hrestlen hmem'
  refine h45_segExitVT_of_sepWP_placed hm_unp (preKeyEncrypt_placed_step_bl hpc hrun hsp hal) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5,
      hs1_x19, hs1_x20, hs1_x22, hs1_x24, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := Pf.SegIdentity.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := h45_otrEnc_placed_pre_frame F0 kit.ss_vt ikit.id_vt C A ctl S x prevCap prevPtr G sess otr taken
    pqCap pqPtr k items pkVal kyBoxPtr sp R Pm1 s0 s1
    h64 hQ hcrl1 hs1_sp hs1_x0 hs1_x1 hs1_x2 hs1_x3 hptlen hs1_x4 hlocA hs1_x5 hPm1 hm1
  refine h45_segExitVT_call_sub_placed hEnv.callees.otrEnc (preKeyOtrGhost x sp pqCap pqPtr otr)
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)).onExit
            (preKeyOtrGhost x sp pqCap pqPtr otr) code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      change sf.mem ⊨ ((⌜(((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 = .error .panic ∨
          S.sendPanics otr.pqrState x.rest ∨ allocFailedIn s1 sf) ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ _) ∗
        (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) at hpost
      rw [sepConj_assoc] at hpost
      exact onPanicPlaced_absorb_extra
        (onPanic_of_otrEnc_placed (hs1_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt hpost))
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_al : s2.spAligned = true := Pf.SegIdentity.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x24 : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    rw [hcs12.2.2.2.2.2.1, hs1_x24]; exact hx24
  obtain ⟨pqCap', pqPtr', hcrl2, hne2, hs2_tr, hm2⟩ :=
    h45_otrEnc_placed_post_unpack F0 kit.ss_vt ikit.id_vt C A ctl S x prevCap prevPtr G sess otr taken pqCap pqPtr k items
      pkVal kyBoxPtr sp R s0 s1 s2 hsp0 hs1_sp hpost2
  have hm2' : s2.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).2 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) ((preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse).1 ∗
      memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗
      (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ (F0 ∗ R0)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [R]; sep_ac_rfl)) hm2
  exact h45_segExitVT_of_segExit_placed (SegExitPlaced.next ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, hne2, hs2_pc,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hcrl2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, hs2_x24, by reg_chain, by reg_chain, by reg_chain,
    hptlen, hrestlen, hlocA, hnow, hstack, hm2'⟩)

theorem h45_segPreKey_encrypt_err_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (e : SignalProtocolError) (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess) (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (herr : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .error e)
    (hret : PreKeyEncryptRetStatePlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R0 s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s (fun _ => False) := by
  let envF := h45_envF_placed hEnv
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, _hpkVal, hnp, hpc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩, htr,
    _hx20, _hx22, _hx24, hx25, hx26, hx28,
    _hptlen, _hrestlen, _hlocA, _hnow, hstack, hmem⟩
  set sp := s0.sp - 0xbe0#64
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have herr' : res.1 = .error e := herr
  rw [herr'] at hnp hmem
  have he_np : e ≠ .panic := fun h => hnp (congrArg Except.error h)
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl he_np
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, ← sp_sub_60_eq_add_b80 s0.sp]
  obtain ⟨w0, w1, w2, w3, w4, w5, v0, v1, v2, H, hst, hm_err⟩ :=
    preKeyEncrypt_placed_err_unpack kit.ss_vt ikit.id_vt A ctl x prevCap prevPtr G sess taken res.2 pqCap' pqPtr' k items
      pkVal kyBoxPtr e (S.draws otr.pqrState x.rest) sp R s0 s hnp hmem
  refine SegExitPlaced.of_sepWP hm_err (preKeyEncrypt_placed_step_err hpc hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, _hs3_x20, hs3_x21, hs3_x23, _hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 := hcrl.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := Pf.SegIdentity.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm3_tail := preKeyEncrypt_placed_err_tail_mem kit.ss_vt ikit.id_vt A ctl x prevCap prevPtr G sess taken res.2 pqCap' pqPtr'
    k items pkVal kyBoxPtr w0 w1 w2 w3 w4 w5 (S.draws otr.pqrState x.rest) sp H R Pm3 s0 s3 hPm3 hm3
  have htm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (.protocol e)) s0 s3 := by
    rw [← hprot]
    exact tailModel_of_otr_err_placed (hs3_tr.trans htr) hcur hscope hfrom hrem hpk hts hexp hlt herr
  have hexec := execOk_of_preKeyOtrGhost_error herr
  have hmod_err : x.model C S uuidTryParse (preKeyErrAnswers r) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    rw [EncryptGhost.model, messageEncrypt_eq_flat]
    simp only [encryptFlat, wrapFlat, preKeyErrAnswers, okAnswers, hcur, hfrom, hrem, hpk, hts,
      hexp, hlt, ↓reduceIte, Bool.false_eq_true, hexec]
  have hfinal :
      kit.storeFinal st0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = st0 := by
    rw [congrArg Prod.snd hmod_err]; rfl
  have hidfinal :
      ikit.idFinal ist0 (preKeyErrAnswers r) (x.model C S uuidTryParse (preKeyErrAnswers r)).2 = ist0 := by
    rw [congrArg Prod.snd hmod_err]; rfl
  have hdraws := draws_of_not_stale (S := S) hcur hfrom hrem hpk hts hexp hlt
  rw [← h45_segExit_kitF_placed]
  exact Tails.tailPreKeyEncryptErr_placed_ok envF x R0 s0 s3
    (preKeyErrAnswers r) (.protocol e)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken)
    (some (pqCap', pqPtr', res.2)) kyBoxPtr
    (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload))
    ((h45_tailModel_kitF_placed kit st0 ikit ist0 C S uuidTryParse encRecord x (preKeyErrAnswers r) (.error (.protocol e)) s0 s3).mpr htm)
    hst
    ((h45_encTailV_kitF_placed kit st0 ikit ist0 C ctl uuidTryParse S x (preKeyErrAnswers r) _ _ _ R0 s0 s3).mpr
      ⟨hs3_pc,
        ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19, hcrl3, hs3_vregs.trans hvregs⟩,
        ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
        hstack, by rw [hdraws, hfinal, hidfinal]; exact Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [R])) hm3_tail⟩)

private structure BuildPreKeyMsgWords where mk ::
  (msgG : SignalMessageGhost)
  (u0 ik0 ik1 ik2 ik3 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
  (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 : BitVec 64)
  (k0 k1 k2 kd0 kd1 kd2 bk0 bk1 bk2 bk3 bkd0 bkd1 bkd2 bkd3 ikd0 ikd1 ikd2 ikd3 : BitVec 64)
  (H_sm H_ky : SepProp)

private theorem buildPreKeyMsg_placed_pre_unpack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' kyBoxPtr : BitVec 64) (G : SessionGhost)
    (k : IdentityKey) (items : PendingPreKey) (pkVal : BitVec 32) (sm : SignalMessage)
    (draws : Nat) (sp : BitVec 64) (R : SepProp) (s0 s : State)
    (hm : s.mem ⊨
      sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗
      preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
      optKyberAt A (sp + 0x8a0#64) kyBoxPtr
        (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
      memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x draws s0 ∗ R) :
    let kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)
    ∃ b : BuildPreKeyMsgWords,
      b.w0 + 1#64 ≠ 0#64 ∧ sm.serialized.length < 2 ^ 40 ∧
      (∀ a : BitVec 64,
        (a ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) = words64At a [b.ik0, b.ik1, b.ik2, b.ik3]) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ items.baseKey.bytes.toList) = words64At a [b.bk0, b.bk1, b.bk2, b.bk3]) ∧
      (∀ dst : BitVec 64,
        words64At dst [b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7, b.w8, b.w9, b.w10, b.w11, b.w12, b.w13, b.w14] ∗ b.H_sm ⊢
          signalMessageAt A b.msgG dst sm) ∧
      (∀ dst : BitVec 64,
        words64At dst [b.k0, b.k1, b.k2] ∗ b.H_ky ⊢ optKyberAt A dst kyBoxPtr kp) ∧
      (s.mem ⊨
        ((sp ↦₆₄ b.u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
          ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
          words64At (sp + 0x2e0#64) [b.ik0, b.ik1, b.ik2, b.ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
          words64At (sp + 0x580#64) [b.w0, b.w1, b.w2, b.w3, b.w4, b.w5, b.w6, b.w7, b.w8, b.w9, b.w10, b.w11, b.w12, b.w13, b.w14] ∗
          words64At (sp + 0x8a0#64) [b.k0, b.k1, b.k2] ∗
          words64At (sp + 0x8b8#64) [b.d0, b.d1, b.d2, b.d3, b.d4, b.d5, b.d6, b.d7, b.d8, b.d9, b.d10, b.d11, b.d12, b.d13, b.d14] ∗
          words64At (sp + 0x950#64) [b.kd0, b.kd1, b.kd2] ∗
          words64At (sp + 0xab4#64) [b.bk0, b.bk1, b.bk2, b.bk3] ∗
          words64At (sp + 0xae0#64) [b.bkd0, b.bkd1, b.bkd2, b.bkd3] ∗
          words64At (sp + 0xb00#64) [b.ikd0, b.ikd1, b.ikd2, b.ikd3]) ∗
        (buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
          b.H_sm b.H_ky s0 ∗ R)) := by
  intro kp
  obtain ⟨ik0, ik1, ik2, ik3, hik⟩ :=
    bytes32_exists_words64At (bs := otr'.localIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  obtain ⟨bk0, bk1, bk2, bk3, hbk⟩ :=
    bytes32_exists_words64At (bs := items.baseKey.bytes.toList) (List.Vector.toList_length _)
  dsimp only [signalMessageResultAt] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨msgG, hm⟩ := hm
  rw [otrAt_eq_ik_ver_rest A sp pqCap' pqPtr' otr' ik0 ik1 ik2 ik3 hik, hbk (sp + 0xab4#64)] at hm
  have h5f8 : memRegion (sp + 0x5f8#64) 0x2a8 =
      memRegion (sp + 0x5f8#64) 128 ∗ memRegion (sp + 0x678#64) 0x228 :=
    mr_cut_add sp 0x5f8 128 0x228 (by decide)
  have h8b8 : memRegion (sp + 0x8b8#64) 0x1fc =
      memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x930#64) 0x20 ∗
        memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x968#64) 0x14c := by
    rw [mr_cut_add sp 0x8b8 120 0x184 (by decide),
        mr_cut_add sp 0x930 0x20 0x164 (by decide), mr_cut_add sp 0x950 24 0x14c (by decide)]
  have had4 : memRegion (sp + 0xad4#64) 0xac =
      memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 := by
    rw [mr_cut_add sp 0xad4 0xc 0xa0 (by decide),
        mr_cut_add sp 0xae0 32 0x80 (by decide), mr_cut_add sp 0xb00 32 0x60 (by decide)]
  rw [h5f8, h8b8, had4] at hm
  let F_rest :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrRestAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 128 ∗
      memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x930#64) 0x20 ∗
      memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xad4#64) 0xc ∗
      memRegion (sp + 0xb20#64) 0x60 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R
  have hm_scr : s.mem ⊨ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
      (signalMessageAt A msgG (sp + 0x580#64) sm ∗ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗
        ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
        words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3] ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; sep_ac_rfl)) hm
  obtain ⟨u0, hm_scr⟩ := preKeyEncryptScratch'_unpack sp sess.localRegistrationId items.signedPreKeyId pkVal hm_scr
  let S_sc := (sp ↦₆₄ u0) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
    ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗
    words64At (sp + 0x2e0#64) [ik0, ik1, ik2, ik3] ∗ ((sp + 0x348#64) ↦₈ otr'.sessionVersion) ∗
    words64At (sp + 0xab4#64) [bk0, bk1, bk2, bk3]
  have hm_sm : s.mem ⊨ signalMessageAt A msgG (sp + 0x580#64) sm ∗
      (optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
        memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        S_sc ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc]; sep_ac_rfl)) hm_scr
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    H_sm, hw0, hmsg_len, hm_sm, hpack_sm⟩ :=
    signalMessageAt_relocate A msgG (sp + 0x580#64) sm hm_sm
  let W_sm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
  have hm_ky : s.mem ⊨ optKyberAt A (sp + 0x8a0#64) kyBoxPtr kp ∗
      (memRegion (sp + 0x8b8#64) 120 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ S_sc ∗ H_sm ∗ buildPreKeyMsgScratchRest sp ∗ F_rest) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_sm]; sep_ac_rfl)) hm_sm
  obtain ⟨k0, k1, k2, H_ky, hm_ky, hpack_ky⟩ :=
    optKyberAt_relocate A (sp + 0x8a0#64) kyBoxPtr kp hm_ky
  let F_e6d := buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp
    H_sm H_ky s0 ∗ R
  have hm_d : s.mem ⊨ memRegion (sp + 0x8b8#64) 120 ∗
      (memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ S_sc ∗ F_e6d) := by
    dsimp only [F_e6d]; unfold buildPreKeyMsgRestFramePlaced
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [F_rest]; sep_ac_rfl)) hm_ky
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, hm_d⟩ :=
    memRegion_120_exists_words15 (sp + 0x8b8#64) hm_d
  let W_d := words64At (sp + 0x8b8#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14]
  have hm_kd : s.mem ⊨ memRegion (sp + 0x950#64) 24 ∗
      (memRegion (sp + 0xae0#64) 32 ∗ memRegion (sp + 0xb00#64) 32 ∗
        W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [W_d]; sep_ac_rfl)) hm_d
  obtain ⟨kd0, kd1, kd2, hm_kd⟩ := memRegion_24_exists_words3 (sp + 0x950#64) hm_kd
  have hm_bkd : s.mem ⊨ memRegion (sp + 0xae0#64) 32 ∗
      (memRegion (sp + 0xb00#64) 32 ∗ W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_kd
  obtain ⟨bkd0, bkd1, bkd2, bkd3, hm_bkd⟩ := memRegion_32_exists_words4 (sp + 0xae0#64) hm_bkd
  have hm_ikd : s.mem ⊨ memRegion (sp + 0xb00#64) 32 ∗
      (W_sm ∗ words64At (sp + 0x8a0#64) [k0, k1, k2] ∗ W_d ∗
        words64At (sp + 0x950#64) [kd0, kd1, kd2] ∗
        words64At (sp + 0xae0#64) [bkd0, bkd1, bkd2, bkd3] ∗ S_sc ∗ F_e6d) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by sep_ac_rfl)) hm_bkd
  obtain ⟨ikd0, ikd1, ikd2, ikd3, hm_ikd⟩ := memRegion_32_exists_words4 (sp + 0xb00#64) hm_ikd
  refine ⟨⟨msgG, u0, ik0, ik1, ik2, ik3,
    w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    k0, k1, k2, kd0, kd1, kd2, bk0, bk1, bk2, bk3, bkd0, bkd1, bkd2, bkd3,
    ikd0, ikd1, ikd2, ikd3, H_sm, H_ky⟩, hw0, hmsg_len, hik, hbk, hpack_sm, hpack_ky, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by dsimp only [S_sc, W_sm, W_d, F_e6d]; sep_ac_rfl)) hm_ikd

private structure CmCopyWords where mk ::
  (psmG : PreKeyMsgGhost)
  (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 : BitVec 64)
  (v0 v1 v2 d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 : BitVec 64)
  (H_psm : SepProp)

private theorem cmCopy_placed_pre_unpack [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (prevCap prevPtr pqCap' pqPtr' : BitVec 64) (G : SessionGhost) (k : IdentityKey)
    (items : PendingPreKey) (pkVal : BitVec 32) (psm : PreKeySignalMessage) (draws : Nat)
    (sp : BitVec 64) (R : SepProp) (s0 s2 : State) (hsp_eq : sp = s0.sp - 0xbe0#64)
    (hm2 : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) psm) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k
        items pkVal draws sp s0 ∗ R) :
    ∃ u : CmCopyWords, u.w0 + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [u.w0, u.w1, u.w2, u.w3, u.w4, u.w5, u.w6, u.w7, u.w8, u.w9, u.w10, u.w11, u.w12, u.w13, u.w14,
          u.w15, u.w16, u.w17, u.w18, u.w19, u.w20, u.w21, u.w22, u.w23, u.w24, u.w25, u.w26, u.w27, u.w28, u.w29, u.w30] ∗
          u.H_psm ⊢ preKeyMsgAt A u.psmG dst psm) ∧
      (s2.mem ⊨
        (words64At (sp + 0x580#64) [u.w0, u.w1, u.w2, u.w3, u.w4, u.w5, u.w6, u.w7, u.w8, u.w9, u.w10, u.w11, u.w12, u.w13,
            u.w14, u.w15, u.w16, u.w17, u.w18, u.w19, u.w20, u.w21, u.w22, u.w23, u.w24, u.w25, u.w26, u.w27, u.w28, u.w29, u.w30] ∗
          words64At (sp + 0x930#64) [u.v0, u.v1, u.v2] ∗
          words64At (sp + 0x370#64) [u.d0, u.d1, u.d2, u.d3, u.d4, u.d5, u.d6, u.d7, u.d8, u.d9, u.d10, u.d11, u.d12, u.d13,
            u.d14, u.d15, u.d16, u.d17, u.d18, u.d19, u.d20, u.d21, u.d22, u.d23, u.d24, u.d25, u.d26, u.d27, u.d28, u.d29, u.d30]) ∗
        (cmCopyRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp u.H_psm s0 ∗ R)) := by
  unfold preKeyMsgCallFramePlaced at hm2
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨psmG, hm2⟩ := hm2
  have hcm := preKeyEncryptScratch'_to_cmScratch sp (sp + 0x8b8#64) sess.localRegistrationId items.signedPreKeyId pkVal
  have hbk_ae0 := bytes32_entails_memRegion (sp + 0xae0#64) items.baseKey.bytes.toList (List.Vector.toList_length _)
  have hik_b00 := bytes32_entails_memRegion (sp + 0xb00#64) otr'.localIdentityKey.publicKey.bytes.toList (List.Vector.toList_length _)
  let F_core :=
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗ memRegion x.ret 248 ∗ R
  have hm2_sub : s2.mem ⊨
      (((sp ↦₆₄ (sp + 0x8b8#64)) ∗ ((sp + 0x14#64) ↦₃₂ sess.localRegistrationId) ∗
        ((sp + 0x24#64) ↦₃₂ items.signedPreKeyId) ∗ ((sp + 0x34#64) ↦₃₂ pkVal) ∗ buildPreKeyMsgScratchRest sp) ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗ ((sp + 0xb00#64) ↦ₛ otr'.localIdentityKey.publicKey.bytes.toList)) ∗
      (preKeyMsgAt A psmG (sp + 0x580#64) psm ∗ memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x8b8#64) 120 ∗
        (A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonPlacedRest A ctl x draws s0) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗
        memRegion (sp + 0x930#64) 0x20 ∗ memRegion (sp + 0x968#64) 0x14c ∗ memRegion (sp + 0xab4#64) 32 ∗
        memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xb20#64) 0x60 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; sep_ac_rfl)) hm2
  have hm2_mono := Satisfies.mono (sepConj_mono_left (sepConj_mono hcm (sepConj_mono hbk_ae0 hik_b00))) hm2_sub
  have h930 : memRegion (sp + 0x930#64) 0x20 = memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x948#64) 8 :=
    mr_cut_add sp 0x930 24 8 (by decide)
  have henc_psm : A.pool ∗ stackAt sp preKeyMsgNewStack ∗ encCommonPlacedRest A ctl x draws s0 =
      encCommonPlaced A ctl x draws s0 := by
    rw [hsp_eq, ← encCommonPlaced_eq_preKeyMsg A ctl x draws s0]
  rw [henc_psm, h930] at hm2_mono
  have hmerge_678 : memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x8b8#64) 120 =
      memRegion (sp + 0x678#64) 0x2b8 := by
    rw [mr_cut_add sp 0x678 0x228 0x90 (by decide), mr_cut_add sp 0x8a0 24 120 (by decide)]
  have hmerge_948 :
      memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x968#64) 0x14c ∗
        memRegion (sp + 0xab4#64) 32 ∗ memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
        memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60 = memRegion (sp + 0x948#64) 0x238 := by
    rw [mr_cut_add sp 0x948 8 0x230 (by decide), mr_cut_add sp 0x950 24 0x218 (by decide),
        mr_cut_add sp 0x968 0x14c 0xcc (by decide), mr_cut_add sp 0xab4 32 0xac (by decide),
        mr_cut_add sp 0xad4 0xc 0xa0 (by decide), mr_cut_add sp 0xae0 32 0x80 (by decide),
        mr_cut_add sp 0xb00 32 0x60 (by decide)]
  have hm2_merged : s2.mem ⊨
      preKeyMsgAt A psmG (sp + 0x580#64) psm ∗
      (memRegion (sp + 0x930#64) 24 ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        (memRegion (sp + 0x678#64) 0x228 ∗ memRegion (sp + 0x8a0#64) 24 ∗ memRegion (sp + 0x8b8#64) 120) ∗
        (memRegion (sp + 0x948#64) 8 ∗ memRegion (sp + 0x950#64) 24 ∗ memRegion (sp + 0x968#64) 0x14c ∗
          memRegion (sp + 0xab4#64) 32 ∗ memRegion (sp + 0xad4#64) 0xc ∗ memRegion (sp + 0xae0#64) 32 ∗
          memRegion (sp + 0xb00#64) 32 ∗ memRegion (sp + 0xb20#64) 0x60) ∗
        cmScratch sp ∗ encCommonPlaced A ctl x draws s0 ∗ F_core) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2_mono
  rw [hmerge_678, hmerge_948] at hm2_merged
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    H_psm, hw0, hm2_psm, hpsm_rel⟩ :=
    preKeyMsgAt_relocate A psmG (sp + 0x580#64) psm hm2_merged
  let W_psm := words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
    w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30]
  let F_e6e := cmCopyRestFramePlaced kit ikit ctl x sess taken otr' prevCap prevPtr pqCap' pqPtr' G k draws sp H_psm s0 ∗ R
  have hm2_930 : s2.mem ⊨ memRegion (sp + 0x930#64) 24 ∗ (memRegion (sp + 0x370#64) 0xf8 ∗ W_psm ∗ F_e6e) := by
    dsimp only [W_psm, F_e6e]; unfold cmCopyRestFramePlaced
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [F_core]; sep_ac_rfl)) hm2_psm
  obtain ⟨v0, v1, v2, hm2_930⟩ := memRegion_24_exists_words3 (sp + 0x930#64) hm2_930
  have hm2_370 : s2.mem ⊨ memRegion (sp + 0x370#64) 248 ∗ (W_psm ∗ words64At (sp + 0x930#64) [v0, v1, v2] ∗ F_e6e) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2_930
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, hm2_370⟩ :=
    memRegion_248_exists_words31 (sp + 0x370#64) hm2_370
  exact ⟨⟨psmG, w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14,
    d15, d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30,
    H_psm⟩, hw0, hpsm_rel, Eq.mp (congrArg (s2.mem ⊨ ·) (by dsimp only [W_psm, F_e6e]; sep_ac_rfl)) hm2_370⟩

theorem h45_segPreKey_buildMessage_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (sm : SignalMessage) (R : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess) (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (hok : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 = .ok sm)
    (hret : PreKeyEncryptRetStatePlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord x r sess otr taken pqCap pqPtr k items R s0 s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' R s0 sf) := by
  rcases hret with ⟨prevCap, prevPtr, G, ts, expiry, pkVal, kyBoxPtr, pqCap', pqPtr',
    hts, hexp, hlt, hpkVal, _, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx22, hx24, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp_eq : sp = s0.sp - 0xbe0#64 := rfl
  set res := (preKeyOtrGhost x sp pqCap pqPtr otr).model C S uuidTryParse
  have hok' : res.1 = .ok sm := hok
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by rw [hx29]; dsimp only [sp]; bv_omega
  let R' := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R
  change s.mem ⊨
    sessionRecordAt A (sp + 0x110#64) ⟨prevCap, prevPtr, some G⟩ (takenRecord sess taken) ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap' pqPtr' res.2 ∗ ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗ preKeyEncryptScratch' sp sess.localRegistrationId items.signedPreKeyId pkVal ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x46a#64) 0x116 ∗
    signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) res.1 ∗ memRegion (sp + 0x5f8#64) 0x2a8 ∗
    optKyberAt A (sp + 0x8a0#64) kyBoxPtr
      (sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload)) ∗
    memRegion (sp + 0x8b8#64) 0x1fc ∗ ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0xac ∗ memRegion x.ret 248 ∗
    encCommonPlaced A ctl x (S.draws otr.pqrState x.rest) s0 ∗ R' at hm
  rw [hok'] at hm
  obtain ⟨b, hw0, hmsg_len, hik, hbk, hsm_rel, hky_rel, hm_e6d⟩ :=
    buildPreKeyMsg_placed_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
      items pkVal sm (S.draws otr.pqrState x.rest) sp R' s0 s hm
  refine Pf.SegFrom.SegExitPlaced.of_sepWP hm_e6d
    (buildPreKeyMsg_placed_step_bl hs_pc hrun hsp hal hx22 hx25 hx26 hx29' hw0) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x1, hs1_x2, hs1_x3, hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8,
      hs1_x19, hs1_x20, hs1_x22, _, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  let call : PreKeyMsgNewCall :=
    { ret := sp + 0x580#64, ver := res.2.sessionVersion, regId := sess.localRegistrationId,
      preKeyId := items.preKeyId, spk := items.signedPreKeyId, kyA := sp + 0x950#64, kyPtr := kyBoxPtr,
      kp := sess.pendingKyberPreKey.map fun k => (⟨k.preKeyId, k.ciphertext⟩ : KyberPayload),
      bkA := sp + 0xae0#64, baseKey := items.baseKey, ikA := sp + 0xb00#64,
      ik := res.2.localIdentityKey, msgA := sp + 0x8b8#64, msgG := b.msgG, msg := sm }
  have hm1_sub : s1.mem ⊨
      (Pm1 ∗ buildPreKeyMsgRestFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp b.H_sm b.H_ky s0) ∗ R' :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm1_pack := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm1)
        (preKeyMsgNew_placed_pre_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' kyBoxPtr G k
          items pkVal b.msgG sm b.ik0 b.ik1 b.ik2 b.ik3
          b.w0 b.w1 b.w2 b.w3 b.w4 b.w5 b.w6 b.w7 b.w8 b.w9 b.w10 b.w11 b.w12 b.w13 b.w14
          b.k0 b.k1 b.k2 b.bk0 b.bk1 b.bk2 b.bk3 b.H_sm b.H_ky (S.draws otr.pqrState x.rest) sp s0 s1
          hsp_eq hs1_sp hik hbk hsm_rel hky_rel)))
    hm1_sub
  have hcall_len : call.model.serialized.length < 2 ^ 42 :=
    call.model_serialized_length_lt hmsg_len (kyber_ciphertext_length_lt (hEnv.scopeIn r hscope) hcur)
  have hcall_pure :
      (s1.readReg64 .x0).setWidth 8 = call.ver ∧ (s1.readReg64 .x1).setWidth 32 = call.regId ∧
      (s1.readReg64 .x2).setWidth 32 = (if call.preKeyId.isSome then 1#32 else 0#32) ∧
      (∀ v, call.preKeyId = some v → (s1.readReg64 .x3).setWidth 32 = v) ∧
      (s1.readReg64 .x4).setWidth 32 = call.spk ∧ s1.readReg64 .x5 = call.kyA ∧
      s1.readReg64 .x6 = call.bkA ∧ s1.readReg64 .x7 = call.ikA ∧
      s1.readReg64 .x8 = call.ret ∧ call.model.serialized.length < 2 ^ 42 :=
    ⟨hs1_x0, hs1_x1, hs1_x2.trans hx24, fun v hv => hs1_x3.trans (hpkVal v hv),
      hs1_x4, hs1_x5, hs1_x6, hs1_x7, hs1_x8, hcall_len⟩
  have hm1_pre : s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A)).pre call s1 ∗
      (preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R') := by
    change s1.mem ⊨ ((preKeyMsgNewSpec A).pre call s1 ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗ _
    rw [sepConj_comm ((preKeyMsgNewSpec A).pre call s1), sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hcrl1, ?_⟩
    unfold preKeyMsgNewSpec
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcall_pure, Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) hm1_pack⟩
  clear hw0 hik hbk hsm_rel hky_rel hm_e6d Pm1 hm1 hPm1 hm1_sub hm1_pack hcall_len hcall_pure
  have hpref01 : s0.trace <+: s1.trace := by
    rw [hs1_tr, htr]; exact ⟨kit.loadEvs encRecord x.rem.val (.ok (some r)), rfl⟩
  refine Pf.SegFrom.SegExitPlaced.call hEnv.callees.psmNew call hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A)).onExit call code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost => by
      have hp : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗
          (preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
            items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ encStoreExtraPlaced kit st0 ikit ist0 x s0) ∗ R := by
        dsimp only [StoreKit.withLsRoCl, preKeyMsgNewSpec, R'] at hpost
        exact Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
      exact onPanic_of_alloc_placed hpref01 hp)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  rcases hcs12 with ⟨hx19_2, hx20_2, _, hx22_2, _, _, hx25_2, hx26_2, _, hx28_2, hx29_2, hvregs_2⟩
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x22 : s2.readReg64 .x22 = sp + 0x8b8#64 := hx22_2.trans (hs1_x22.trans hx22)
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := hx25_2.trans (hs1_x25.trans hx25)
  unfold StoreKit.withLsRoCl preKeyMsgNewSpec at hpost2
  dsimp only [call] at hpost2
  rw [hs1_sp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpost2
  rcases hpost2 with ⟨hcrl2, hs2_tr, hm2⟩
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  have hm2' : s2.mem ⊨
      ((∃∗ g : PreKeyMsgGhost, preKeyMsgAt A g (sp + 0x580#64) call.model) ∗
        (sp ↦₆₄ (sp + 0x8b8#64)) ∗ memRegion (sp + 0x950#64) 24 ∗
        ((sp + 0xae0#64) ↦ₛ items.baseKey.bytes.toList) ∗
        ((sp + 0xb00#64) ↦ₛ res.2.localIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x8b8#64) 120 ∗ A.pool ∗ stackAt sp preKeyMsgNewStack) ∗
      preKeyMsgCallFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        items pkVal (S.draws otr.pqrState x.rest) sp s0 ∗ R' :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm2
  clear hm2 hm1_pre
  obtain ⟨u, hpw0, hpsm_rel, hm2_e6e⟩ :=
    cmCopy_placed_pre_unpack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
      items pkVal call.model (S.draws otr.pqrState x.rest) sp R' s0 s2 hsp_eq hm2'
  refine Pf.SegFrom.SegExitPlaced.of_sepWP hm2_e6e
    (cmCopy_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x22 hs2_x25 hpw0) ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := Pf.SegFrom.spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_sub : s3.mem ⊨
      (Pm3 ∗ cmCopyRestFramePlaced kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
        (S.draws otr.pqrState x.rest) sp u.H_psm s0) ∗ R' :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm3
  have hm3_cm := Satisfies.mono
    (sepConj_mono_left
      (Entails.trans (sepConj_mono_left hPm3)
        (cmCopy_placed_post_pack kit ikit ctl x sess taken res.2 prevCap prevPtr pqCap' pqPtr' G k
          u.psmG call.model
          u.w0 u.w1 u.w2 u.w3 u.w4 u.w5 u.w6 u.w7 u.w8 u.w9 u.w10 u.w11 u.w12 u.w13 u.w14
          u.w15 u.w16 u.w17 u.w18 u.w19 u.w20 u.w21 u.w22 u.w23 u.w24 u.w25 u.w26 u.w27 u.w28 u.w29 u.w30
          u.H_psm (S.draws otr.pqrState x.rest) sp s0 hpsm_rel)))
    hm3_sub
  clear u hpw0 hpsm_rel hm2' hm2_e6e Pm3 hm3 hPm3 hm3_sub
  have hsteps15 := stepsThroughEncrypt_of_preKey_ok_placed hcur hscope hfrom hrem hpk hts hexp hlt hok'
  refine Pf.SegFrom.SegExitPlaced.next ⟨.preKeySignalMessage call.model, res.2, pqCap', pqPtr',
    hsteps15, ?_⟩
  refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al,
      hs3_x29.trans (hx29_2.trans (hs1_x29.trans hx29)),
      hs3_x19.trans (hx19_2.trans (hs1_x19.trans hx19)),
      hcrl3,
      hs3_vregs.trans (hvregs_2.trans (hs1_vregs.trans hvregs))⟩,
    hs3_tr.trans hs2_tr',
    ⟨hs3_x20.trans (hx20_2.trans (hs1_x20.trans hx20)),
      hs3_x25.trans hs2_x25,
      hs3_x26.trans (hx26_2.trans (hs1_x26.trans hx26)),
      hs3_x28.trans (hx28_2.trans (hs1_x28.trans hx28))⟩,
    hpt, hrest, hloc, hnow, hstk,
    Eq.mp (congrArg (s3.mem ⊨ ·) (by dsimp only [sp, call, PreKeyMsgNewCall.model, R']; sep_ac_rfl)) hm3_cm⟩

theorem h45_segPreKey_tail_placed_ok [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k) (hpk : sess.pendingPreKey = some items)
    (hst : PreKeyEncryptState'Placed kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R0) s0 sf) := by
  refine h45_segExitVT_trans_placed
    (h45_segPreKey_encrypt_call_placed_ok hEnv x r sess otr taken pqCap pqPtr k items R0 s0 s
      h64 hcur hscope hfrom hrem hpk hst) fun s2 hret => ?_
  rcases hres : ((preKeyOtrGhost x (s0.sp - 0xbe0#64) pqCap pqPtr otr).model C S uuidTryParse).1 with e | sm
  · exact h45_segExitVT_of_false_placed (h45_segExitVT_of_segExit_placed
      (h45_segPreKey_encrypt_err_placed_ok hEnv x r sess otr taken pqCap pqPtr k items e (F0 ∗ R0) s0 s2
        hcur hscope hfrom hrem hpk hres hret))
  · exact h45_segExitVT_of_segExit_placed
      (h45_segPreKey_buildMessage_placed_ok hEnv x r sess otr taken pqCap pqPtr k items sm (F0 ∗ R0) s0 s2
        hcur hscope hfrom hrem hpk hres hret)

theorem h45_segPreKey_placed_okVT [LibsignalPlacement]
    {F0 : SepProp} {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (h64 : 64 ≤ x.rest.length) (his : sess.pendingPreKey.isSome = true)
    (hkey : KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k (F0 ∗ R0) s0 s) :
    h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s
      (fun sf => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R0) s0 sf) := by
  obtain ⟨items, hpk⟩ := Option.isSome_iff_exists.mp his
  have hcur := hkey.1; have hscope := hkey.2.1; have hfrom := hkey.2.2.1; have hrem := hkey.2.2.2.1
  refine h45_segExitVT_trans_placed (h45_segExitVT_of_segExit_placed
    (h45_segPreKey_unackItems_to_dur_placed_ok hEnv x r sess otr taken pqCap pqPtr k items (F0 ∗ R0) s0 s hpk hkey)) ?_
  rintro s1 ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen, hdur⟩
  refine h45_segExitVT_trans_placed (h45_segExitVT_of_segExit_placed
    (h45_segPreKey_staleness_to_add_placed_ok hEnv x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s1 hcur hscope hfrom hrem hpk hdur)) ?_
  rintro s2 ⟨expiry, hadd⟩
  by_cases hlt : expiry.lt x.now = true
  · exact h45_segExitVT_of_false_placed (h45_segExitVT_of_segExit_placed
      (h45_segPreKey_stale_placed_ok hEnv x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s2 hcur hscope hfrom hrem hpk hlt hadd))
  · have hlt_f : expiry.lt x.now = false := Bool.eq_false_iff.mpr hlt
    refine h45_segExitVT_trans_placed (h45_segExitVT_of_segExit_placed
      (h45_segPreKey_regId_kyber_placed_ok hEnv x r sess otr taken pqCap pqPtr k items
        prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen (F0 ∗ R0) s0 s2 hcur hscope hlt_f hadd)) ?_
    intro s3 he6c
    exact h45_segPreKey_tail_placed_ok hEnv x r sess otr taken pqCap pqPtr k items R0 s0 s3 h64 hcur hscope hfrom hrem hpk he6c

end SegPreKeyTail

/-! ## 1. Segment Chaining & `withStores_placed_okVT_fs` -/

private theorem h45_segExitVT_chain_placed [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h1 : h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next)
    (h2 : ∀ s', next s' → reaches_outcome (lsProg_464 Hk)
      (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (lsProg_464 Hk) (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

private theorem h45_segExitVT_chainFs_placed [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {R : SepProp} {s0 s : State} {next : State → Prop} (hfs : EncFsCtxPlaced kit ikit Hk s0 s)
    (h1 : h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next)
    (h2 : ∀ s', EncFsCtxPlaced kit ikit Hk s0 s' → next s' →
      reaches_outcome (lsProg_464 Hk) (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s') :
    reaches_outcome (lsProg_464 Hk) (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hst, hnext | hout⟩ := h1 hL
  · exact reaches_outcome_steps hst (h2 sf (hfs.of_steps hst) hnext)
  · exact reaches_outcome_steps hst (reaches_outcome.of_outcome hout)

/-- Frame-generalised `withStores_placed_okV_fs` with `64 ≤ x.rest.length` and `F0` framed,
carrying both kits' `envOk` from `KitFsOk`. -/
theorem withStores_placed_okVT_fs [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_464 Hk)) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withEnvPre (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord)
        fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpre_rearr : s0.mem ⊨ ⌜64 ≤ x.rest.length⌝ ∗
      ((withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ (F0 ∗ R)) := by
    change s0.mem ⊨ (⌜64 ≤ x.rest.length⌝ ∗ F0 ∗
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_rearr
  rcases hpre_rearr with ⟨h64, hpreV⟩
  have ⟨haddr_ss, haddr_id⟩ := withStoresEncPlacedSpecV_pre_addrOk hpreV
  have hfs0 : EncFsCtxPlaced kit ikit Hk s0 s0 := FsCtx.of_entry hKitFs h0
  refine h45_segExitVT_chainFs_placed hfs0
    (h45_segExitVT_of_segExit_placed (h45_segLoad_placed_okVT hEnv x (F0 ∗ R) s0 hfs0 hpc hrun hal hpreV)) ?_
  rintro s hfs ⟨r, g, sess, hCur⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed (h45_segFrom_placed_okVT hEnv x r g sess (F0 ∗ R) s0 s hCur)) ?_
  rintro s hfs ⟨otr, taken, pqCap, pqPtr, hOtr⟩
  refine h45_segExitVT_chainFs_placed hfs
    (h45_segExitVT_of_segExit_placed (h45_segIdentity_placed_okVT hEnv x r sess otr taken pqCap pqPtr (F0 ∗ R) s0 s hOtr)) ?_
  rintro s hfs ⟨k, hKey⟩
  have hCm : h45_SegExitVTPlaced F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CmStateVPlaced kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R) s0 s') := by
    cases hp : sess.pendingPreKey with
    | none => exact h45_segSignal_placed_okVT hEnv x r sess otr taken pqCap pqPtr k R s0 s h64 hp hKey
    | some _ => exact h45_segPreKey_placed_okVT hEnv x r sess otr taken pqCap pqPtr k R s0 s h64 (by simp [hp]) hKey
  refine h45_segExitVT_chainFs_placed hfs hCm ?_
  rintro s hfs ⟨m, otr', pqCap', pqPtr', hCmS⟩
  refine h45_segExitVT_chainFs_placed hfs (h45_segExitVT_of_segExit_placed
    (h45_segTrust_placed_okVT hEnv x r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R) s0 s haddr_id hfs hCmS)) ?_
  intro s hfs hSave
  refine h45_segExitVT_chainFs_placed hfs (h45_segExitVT_of_segExit_placed
    (h45_segSave_placed_okVT hEnv x r sess otr taken k m otr' pqCap' pqPtr' (F0 ∗ R) s0 s haddr_id hfs hSave)) ?_
  rintro s hfs ⟨c, hApply⟩
  refine h45_segExitVT_chainFs_placed hfs (h45_segExitVT_of_segExit_placed
    (h45_segApplyStore_placed_okVT hEnv x r sess otr taken k m otr' pqCap' pqPtr' c (F0 ∗ R) s0 s haddr_ss hfs hApply)) ?_
  intro s _ hStored
  exact h45_segExitVT_chain_placed
    (h45_segExitVT_of_segExit_placed (h45_segFinish_placed_okVT hEnv x r sess otr taken k m otr' c (F0 ∗ R) s0 s hStored))
    (fun _ hF => False.elim hF)

/-- Corollary of `withStores_placed_okVT_fs` when `envOk` holds trivially. -/
theorem withStores_placed_okVT [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hEnv : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk)
    (htriv : ∀ f, kit.envOk f ∧ ikit.envOk f := by exact fun _ => ⟨trivial, trivial⟩) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord) :=
  subroutine_ok_of_withEnvPre (withStores_placed_okVT_fs hEnv (.inl htriv)) fun s => htriv s.fs.files

/-! ## 2. Remote-Address Kit Restriction (`h45_kitAt_placed`) & Disjunctive CLI Spec -/

@[reducible] private def h45_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) : SessionStoreSpec A b :=
  { kit with
    addrOk := fun rem => kit.addrOk rem ∧ rem = target
    loadRel := fun st rem ans => kit.loadRel st rem ans ∧ rem = target }

private theorem h45_pure_mono_placed {φ ψ : Prop} (h : φ → ψ) : (⌜φ⌝ : SepProp) ⊢ ⌜ψ⌝ :=
  Entails.pure_left_only fun hφ => Entails.pure_right_only (h hφ) (Entails.refl _)

private theorem h45_storeFinal_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt_placed kit target).storeFinal st0 ans calls = kit.storeFinal st0 ans calls := by
  induction calls generalizing st0 with
  | nil => rfl
  | cons c cs ih => cases c <;> simp only [SessionStoreSpec.storeFinal, h45_kitAt_placed, ih]

private theorem h45_traceOfWith_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    ikit.traceOfWith (h45_kitAt_placed kit target) encRecord ans calls = ikit.traceOfWith kit encRecord ans calls := rfl

private theorem h45_stackV_kitAt_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (ikit : IdentityStoreSpec A b) :
    withStoresEncStackV (h45_kitAt_placed kit target) ikit = withStoresEncStackV kit ikit := rfl

private theorem h45_callsRel_kitAt_imp_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (target : AddrVal) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) (calls : List (StoreCall AddrVal (List (BitVec 8)))) :
    (h45_kitAt_placed kit target).callsRel st0 ans calls → kit.callsRel st0 ans calls := by
  induction calls generalizing st0 with
  | nil => exact id
  | cons c cs ih =>
    cases c with
    | loadSession rem => intro ⟨⟨hl, _⟩, hcs⟩; exact ⟨hl, ih st0 hcs⟩
    | isTrustedIdentity _ _ _ => intro hcs; exact ih st0 hcs
    | saveIdentity _ _ => intro hcs; exact ih st0 hcs
    | storeSession rem r' => intro ⟨hs, hcs⟩; exact ⟨hs, ih st0 hcs⟩

private theorem h45_stepsThroughEncrypt_mono_placed {Scope1 Scope2 : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {S : SpqrModel} {parse : UuidParser} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {otr : OutgoingTripleRatchet (List (BitVec 8))} {taken : SessionState (List (BitVec 8))}
    {k : IdentityKey} {m : CiphertextMessage} {otr' : OutgoingTripleRatchet (List (BitVec 8))}
    (himp : ∀ r', Scope1 r' → Scope2 r')
    (h : StepsThroughEncrypt Scope1 C S parse x r sess otr taken k m otr') :
    StepsThroughEncrypt Scope2 C S parse x r sess otr taken k m otr' :=
  ⟨h.1, himp r h.2.1, h.2.2⟩

private theorem h45_sessionOnlyKitPlacedOkSE_kitAt [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    (target : AddrVal) (hKitOk : SessionOnlyKitPlacedOkSE kit Scope encRecord Hk) :
    SessionOnlyKitPlacedOkSE (h45_kitAt_placed kit target) Scope encRecord Hk where
  loadShim := hKitOk.loadShim
  loadFutDrop := hKitOk.loadFutDrop
  storeShim := hKitOk.storeShim
  storeFutDrop := hKitOk.storeFutDrop
  loadPoll := by
    intro callerProg callerBlk _hcaller hblk ⟨c, self, st⟩ R s0 hpc hrun hpre0 hal
    have ⟨hcrl0, hp1⟩ := StoreKit.extract_withLsRoCl hpre0
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hp1
    have hpre_pure : s0.mem ⊨
        ⌜s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧ (kit.addrOk c.addr.val ∧ c.addr.val = target)⌝ ∗
        (kit.loadBoxAt c.fut self c.addrA 0#8 ∗ kit.storeAt self st ∗ memRegion c.out 368 ∗
          protocolAddressAt A c.addr c.addrA ∗ A.pool ∗ stackAt s0.sp kit.loadPollStack ∗ R) := by
      simpa only [kitLoadPollPlacedSpecS, h45_kitAt_placed, sepConj_assoc] using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hx0, hx8, haddr, hrem⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        (StoreKit.withLsRoCl lsmpl (kitLoadPollPlacedSpecSE kit Scope encRecord)).pre (c, self, st) s0 ∗ R := by
      dsimp only [StoreKit.withLsRoCl]
      rw [sepConj_comm _ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcrl0, withEnvPre_pre_intro henv ?_⟩
      dsimp only [kitLoadPollPlacedSpecS]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8, haddr⟩, by simpa only [sepConj_assoc] using hmem⟩
    have hcall := hKitOk.loadPoll (callerProg := callerProg) (callerBlk := callerBlk) hblk
      (c, self, st) R s0 hpc hrun hpre_kit hal
    refine hcall.mono_outcome (fun sf hout => ?_)
    rcases hout with ⟨hret, hcs, hpost⟩ | hpan | hexit | hoom
    · refine Or.inl ⟨hret, hcs, ?_⟩
      dsimp only [StoreKit.withLsRoCl, withEnvPre, kitLoadPollPlacedSpecS, h45_kitAt_placed] at hpost ⊢
      refine Satisfies.mono (sepConj_mono_left (sepConj_mono_right (Entails.sepExists_elim fun ans =>
        Entails.sepExists_right ans ?_))) hpost
      exact sepConj_mono_left (h45_pure_mono_placed fun ⟨hl, htr⟩ => ⟨⟨hl, hrem⟩, htr⟩)
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr (Or.inl hexit))
    · exact Or.inr (Or.inr (Or.inr hoom))
  storePoll := by
    intro callerProg callerBlk _hcaller hblk ⟨c, self, st⟩ R s0 hpc hrun hpre0 hal
    have ⟨hcrl0, hp1⟩ := StoreKit.extract_withLsRoCl hpre0
    obtain ⟨henv, hpre⟩ := withEnvPre_pre_elim hp1
    have hpre_pure : s0.mem ⊨
        ⌜s0.readReg64 .x0 = c.fut ∧ s0.readReg64 .x8 = c.out ∧ kit.RecOk c.call.record ∧
          (kit.addrOk c.call.addr.val ∧ c.call.addr.val = target)⌝ ∗
        (kit.storeBoxAt c.fut self c.call.addrA c.call.recA 0#8 ∗ kit.storeAt self st ∗ memRegion c.out 48 ∗
          protocolAddressAt A c.call.addr c.call.addrA ∗ sessionRecordAt A c.call.recA c.call.g c.call.record ∗
          A.pool ∗ stackAt s0.sp kit.storePollStack ∗ R) := by
      simpa only [kitStorePollPlacedSpec, h45_kitAt_placed, sepConj_assoc] using hpre
    rw [satisfies_pure_sepConj] at hpre_pure
    rcases hpre_pure with ⟨⟨hx0, hx8, hrec, haddr, _⟩, hmem⟩
    have hpre_kit : s0.mem ⊨
        (StoreKit.withLsRoCl lsmpl (kitStorePollPlacedSpecE kit encRecord)).pre (c, self, st) s0 ∗ R := by
      dsimp only [StoreKit.withLsRoCl]
      rw [sepConj_comm _ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem⌝, sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hcrl0, withEnvPre_pre_intro henv ?_⟩
      dsimp only [kitStorePollPlacedSpec]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx8, hrec, haddr⟩, by simpa only [sepConj_assoc] using hmem⟩
    exact hKitOk.storePoll (callerProg := callerProg) (callerBlk := callerBlk) hblk
      (c, self, st) R s0 hpc hrun hpre_kit hal

/-- Relocatable disjunctive CLI `_with_stores` encrypt spec (`64 ≤ x.rest.length ∨ RecordPqEmpty`)
framing `F0` across the call. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecVT_cli
    [LibsignalPlacement] {A : RustAlloc} (F0 : SepProp)
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState) (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec WithStoresEncGhost :=
  { CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
      kit st0 ikit ist0 C ctl uuidParse S encRecord with
    pre := fun x s =>
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗ F0 ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
          kit st0 ikit ist0 C ctl uuidParse S encRecord).pre x s
    post := fun x s0 sf =>
      F0 ∗ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncPlacedSpecV
        kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf }

private theorem h45_subroutineOutcome_cli_of_kitAt_placed [LibsignalPlacement]
    {F0 : SepProp} {A : RustAlloc} {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncPlacedSpecV (h45_kitAt_placed kit x.rem.val) st0 ikit ist0 C ctl uuidParse S encRecord)
      x (F0 ∗ R) s0 sf) :
    SubroutineOutcome
      (withStoresEncPlacedSpecVT_cli F0 kit st0 ikit ist0 Scope C ctl uuidParse S encRecord) x R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncPlacedSpecVT_cli]
    have hrearr : (F0 ∗
        (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf) ∗ R =
      (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidParse S encRecord).post x s0 sf ∗ (F0 ∗ R) := by sep_ac_rfl
    rw [hrearr]
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded]
    refine Entails.sepExists_elim fun answers => Entails.sepExists_right answers ?_
    rw [h45_traceOfWith_kitAt_placed kit x.rem.val, h45_storeFinal_kitAt_placed kit x.rem.val,
      h45_stackV_kitAt_placed kit x.rem.val]
    exact sepConj_mono_left (h45_pure_mono_placed fun ⟨hnp, hcalls, hid, htr⟩ =>
      ⟨hnp, h45_callsRel_kitAt_imp_placed kit x.rem.val st0 answers _ hcalls, hid, htr⟩)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncPlacedSpecVT_cli, withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded, h45_kitAt_placed] at honp ⊢
    have hmono1 :
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              (kit.loadRel st0 x.rem.val answers.loadSession ∧ x.rem.val = x.rem.val) ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ⊢
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ := by
      refine h45_pure_mono_placed fun ⟨htr, hor⟩ => ⟨htr, ?_⟩
      rcases hor with halloc | ⟨ans, ⟨hl, _⟩, hpfx, herr⟩
      · exact Or.inl halloc
      · exact Or.inr ⟨ans, hl, hpfx, herr⟩
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc _ anyHeap F0]
    exact sepConj_mono_left (sepConj_mono hmono1 (entails_anyHeap (anyHeap ∗ F0)))
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honex; rw [satisfies_pure_sepConj] at honex; exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (F0 ∗ R) at honoom; rw [satisfies_pure_sepConj] at honoom; exact False.elim honoom.1

/-- **Relocatable CLI disjunctive `_with_stores` encrypt (`_fs`)** on `lsProg_464 Hk`. -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStores_placed_okVT_fs_cli
    [LibsignalPlacement] {F0 : SepProp} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState} {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    (hhooks : PublicApiEncHooksPlaced A Hk) (hKitOk : SessionOnlyKitPlacedOkSE kit Scope encRecord Hk)
    (hIkitOk : IdentityStoreKitPlacedOkI ikit Hk)
    (hOtrT : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQT F0 C A ctl uuidTryParse S)))
    (hOtrEmpty : subroutine_ok (lsProg_464 Hk)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ (· = []) C A ctl uuidTryParse S)))
    (hVtables : SessionOnlyVtablesPlacedOk kit) (hIdVtables : IdentityVtablesPlacedOk ikit)
    (hKitFs : KitFsOk (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet) (lsProg_464 Hk))
    (hScopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r)
    (hScopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
      kit.ScopeAt Scope st0 rem r → r.currentSession = some s → s.state.pqRatchetState.length < 2 ^ 32)
    (hRecOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
      {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
      {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
      {otr' : OutgoingTripleRatchet (List (BitVec 8))},
      kit.addrOk x.rem.val →
      StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidTryParse x r sess otr taken k m otr' →
      kit.RecOk (storedRecord sess otr' taken)) :
    subroutine_ok (lsProg_464 Hk) encEntryPlaced
      (withEnvPre (withStoresEncPlacedSpecVT_cli F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord)
        (fun s => kit.envOk s.fs.files ∧ ikit.envOk s.fs.files)) := by
  intro x R s0 hpc hrun hpre0 hal
  obtain ⟨h0, hpre⟩ := withEnvPre_pre_elim hpre0
  rw [reaches_outcome_withEnvPre]
  have hpre_disj : s0.mem ⊨
      ⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗
      ((F0 ∗ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0) ∗ R) := by
    change s0.mem ⊨
      (⌜64 ≤ x.rest.length ∨ (∀ r, kit.ScopeAt Scope st0 x.rem.val r → E2E.Record.RecordPqEmpty r)⌝ ∗ F0 ∗
        (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0) ∗ R at hpre
    exact Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre
  rw [satisfies_pure_sepConj] at hpre_disj
  rcases hpre_disj with ⟨h64 | hpqE, hpre_tok⟩
  · have hEnvT : EncEnvTPlaced F0 kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord Hk :=
      { hooks := hhooks, kitOk := hKitOk, ikitOk := hIkitOk, callees := EncCalleesTPlaced.of_otrEnc hhooks hOtrT,
        vtables := hVtables, idVtables := hIdVtables, scopeIn := hScopeIn, scopeQ := hScopeQ, recOk := hRecOk }
    have hpreVT : s0.mem ⊨
        (withStoresEncPlacedSpecVT F0 kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R := by
      dsimp only [withStoresEncPlacedSpecVT]; rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨h64, by simpa only [sepConj_assoc] using hpre_tok⟩
    have hcall := withStores_placed_okVT_fs hEnvT hKitFs x R s0 hpc hrun (withEnvPre_pre_intro h0 hpreVT) hal
    rw [reaches_outcome_withEnvPre] at hcall; exact hcall
  · have hpreV_rearr : s0.mem ⊨
        (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ (F0 ∗ R) :=
      Eq.mp (congrArg (s0.mem ⊨ ·) (by sep_ac_rfl)) hpre_tok
    have ⟨haddr_ss, _⟩ := withStoresEncPlacedSpecV_pre_addrOk hpreV_rearr
    let kit' := h45_kitAt_placed kit x.rem.val
    have hEnvE : EncEnvPlaced kit' st0 ikit ist0 Scope (· = []) C ctl uuidTryParse S encRecord Hk := {
      hooks := hhooks, kitOk := h45_sessionOnlyKitPlacedOkSE_kitAt x.rem.val hKitOk, ikitOk := hIkitOk
      callees := EncCalleesPlaced.of_otrEnc hhooks hOtrEmpty
      vtables := ⟨hVtables.loadSlot, hVtables.storeSlot, hVtables.loadFutDrop, hVtables.loadFutSize,
        hVtables.loadFutAlign, hVtables.loadFutPoll, hVtables.storeFutDrop, hVtables.storeFutSize,
        hVtables.storeFutAlign, hVtables.storeFutPoll⟩
      idVtables := hIdVtables
      scopeIn := fun r ⟨hsc, hl, _⟩ => hScopeIn r ⟨hsc, hl⟩
      scopeQ := fun r s ⟨hsc, hl, hrem⟩ hsess => by subst hrem; exact hpqE r ⟨hsc, hl⟩ s hsess
      recOk := fun {y r sess otr taken k m otr'} h15 =>
        hRecOk (h15.2.1.2.2.symm ▸ haddr_ss)
          (h45_stepsThroughEncrypt_mono_placed (fun _ ⟨hsc, hl, _⟩ => ⟨hsc, hl⟩) h15) }
    have hpreV' : s0.mem ⊨
        (withStoresEncPlacedSpecV kit' st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ (F0 ∗ R) := by
      refine Satisfies.mono (sepConj_mono_left ?_) hpreV_rearr
      dsimp only [withStoresEncPlacedSpecV, StoreKit.withLsCodeRoLoaded, kit']
      rw [h45_stackV_kitAt_placed kit x.rem.val]
      exact sepConj_mono_left (sepConj_mono_left
        (h45_pure_mono_placed fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hss, hid⟩ =>
          ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, ⟨hss, rfl⟩, hid⟩))
    have hcall := withStores_placed_okV_fs hEnvE hKitFs x (F0 ∗ R) s0 hpc hrun (withEnvPre_pre_intro h0 hpreV') hal
    rw [reaches_outcome_withEnvPre] at hcall
    exact hcall.mono_outcome (fun _ hout => h45_subroutineOutcome_cli_of_kitAt_placed hout)

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
