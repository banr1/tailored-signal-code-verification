/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegPreKeyUnackStaleness
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyCommon
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegPreKeyFetch
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# `segPreKey` Unacknowledged Items Getter and Staleness Check (`+0x344..+0x6fc`)

Proves `segPreKey_unackItems_to_dur_ok` (`+0x344..+0x6c4`, calling
`unacknowledged_pre_key_message_items` and unpacking the 88-byte return slot) and
`segPreKey_staleness_to_add_ok` (`+0x6c4..+0x6fc`, calling `duration_since` and `timeAdd`),
along with their trap-mode counterparts.
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

/-! ## 1. Representation unpack/pack helpers for `unackOutAt` and `baseKey` 36-byte copy -/

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap
    (sp : BitVec 64) (items : PendingPreKey) (ts : SystemTime) : SepProp :=
  memRegion (sp + 0x46a#64) 0x64a ∗
    ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
    memRegion (sp + 0xad4#64) 0x2c ∗
    ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
    ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
    memRegion (sp + 0xb0c#64) 4 ∗
    memRegion (sp + 0xb10#64) 0x70

private theorem poll_unackItems_pack_pollWithBaseKey_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    (memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 88 ∗
      memRegion (sp + 0x5d8#64) 0x298 ∗
      memRegion (sp + 0x870#64) 36 ∗
      memRegion (sp + 0x894#64) 0x21c ∗
      memRegion (sp + 0xab0#64) 4 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70) ⊢
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap sp items ts := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 88 0x4dc (by decide),
      mr_cut_add sp 0x5d8 0x298 0x244 (by decide),
      mr_cut_add sp 0x870 36 0x220 (by decide),
      mr_cut_add sp 0x894 0x21c 4 (by decide)]
  simp only [sepConj_assoc]
  exact Entails.refl _

private theorem pollWithBaseKey_dur_unpack_trap (sp : BitVec 64) (items : PendingPreKey)
    (ts : SystemTime) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap sp items ts =
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x580#64) 24 ∗
      memRegion (sp + 0x598#64) 0x300 ∗
      memRegion (sp + 0x898#64) 8 ∗
      memRegion (sp + 0x8a0#64) 0x214 ∗
      ((sp + 0xab4#64) ↦ₛ items.baseKey.bytes.toList) ∗
      memRegion (sp + 0xad4#64) 0x2c ∗
      ((sp + 0xb00#64) ↦₆₄ ts.tvSec) ∗
      ((sp + 0xb08#64) ↦₃₂ ts.tvNsec) ∗
      memRegion (sp + 0xb0c#64) 4 ∗
      memRegion (sp + 0xb10#64) 0x70 := by
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap
  rw [mr_cut_add sp 0x46a 0x116 0x534 (by decide),
      mr_cut_add sp 0x580 24 0x51c (by decide),
      mr_cut_add sp 0x598 0x300 0x21c (by decide),
      mr_cut_add sp 0x898 8 0x214 (by decide)]
  simp only [sepConj_assoc]

private theorem durationSinceBounded_b00_intro_trap (sp : BitVec 64) (tvSec : BitVec 64)
    (tvNsec : BitVec 32) (hns : tvNsec.toNat < 1000000000) :
    (((sp + 0xb00#64) ↦₆₄ tvSec) ∗ ((sp + 0xb08#64) ↦₃₂ tvNsec) ∗ memRegion (sp + 0xb0c#64) 4) ⊢
      (∃∗ tvSec : BitVec 64, ∃∗ tvNsec : BitVec 32,
        ⌜tvNsec.toNat < 1000000000⌝ ∗
        ((sp + 0xb00#64) ↦₆₄ tvSec) ∗ (((sp + 0xb00#64) + 8#64) ↦₃₂ tvNsec) ∗
        memRegion ((sp + 0xb00#64) + 12#64) 4) := by
  have h := CryptoVerification.SignalSession.Cli.Slots.durationSinceBounded_self_intro
    (sp + 0xb00#64) tvSec tvNsec hns
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState_trap {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
  optU32ValProp items.preKeyId pkVal ∧
  optU32ValProp (sess.pendingKyberPreKey.map (·.preKeyId)) kyIdVal ∧
  unackKyberSliceProp G.kyber kyPtr kyLen ∧
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1732#64 ∧
  encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = sp + 0xb00#64 ∧
  (s.readReg64 .x2).setWidth 32 = 0#32 ∧
  s.readReg64 .x8 = sp + 0x580#64 ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  (s.readReg64 .x21).setWidth 32 = ts.tvNsec ∧
  s.readReg64 .x22 = sp + 0x8b8#64 ∧
  s.readReg64 .x23 = kyPtr ∧
  (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = ts.tvSec ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyScratch sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.pollWithBaseKey_trap sp items ts ∗
    memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

/-- State at `+0x6c4` (`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1732#64`), right before `bl durationSince`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
  optU32ValProp items.preKeyId pkVal ∧
  optU32ValProp (sess.pendingKyberPreKey.map (·.preKeyId)) kyIdVal ∧
  unackKyberSliceProp G.kyber kyPtr kyLen ∧
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1732#64 ∧
  encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = sp + 0xb00#64 ∧
  s.readReg64 .x8 = sp + 0x580#64 ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  (s.readReg64 .x21).setWidth 32 = ts.tvNsec ∧
  s.readReg64 .x22 = sp + 0x8b8#64 ∧
  s.readReg64 .x23 = kyPtr ∧
  (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = ts.tvSec ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyScratch sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    pollWithBaseKey sp items ∗
    memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {next : State → Prop}
    (hinv : CallInv img s)
    (hm : s.mem ⊨ P ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWPp (trTrapProgAt img.base C abs) target s P
      (fun sf P_f => CallInv img sf → (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) → next sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
          (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut (hinv.of_steps hsteps) hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_absorb_extra (hqp hmf)⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    {x : WithStoresEncGhost} {R0 : SepProp} {s0 s : State} {target : BitVec 64} {P : SepProp}
    {next : State → Prop}
    (hinv : CallInv img s)
    (hm : s.mem ⊨ P ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))
    (hwp : SepWPp (tripleRatchetProgAt img.base C ctl abs) target s P
      (fun sf P_f => CallInv img sf → (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) → next sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)) →
        (sf.mem ⊨ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.withStoresEncSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗
          (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0)))) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hout⟩ := hwp (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) hm hL
  rcases hout with ⟨_, _, P_f, hmf, hOut⟩ | ⟨hpan, P_f, hmf, hqp⟩ | ⟨_, _hoom⟩
  · exact ⟨sf, hsteps, Or.inl (hOut (hinv.of_steps hsteps) hmf)⟩
  · exact ⟨sf, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_absorb_extra (hqp hmf)⟩))⟩
  · dsimp only at _hoom
    exact (not_satisfies_false_sepConj _hoom).elim

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_unackItems_to_dur_ok_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState_trap kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  have hmeta' := hmeta
  rcases hmeta' with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 836#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 1732#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env
  rw [henc_fn] at hpc
  have hunack := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.unack_ok_at_enc_trap env
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x344 0x4c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x680 0x44
  dsimp only [trTrapProgAt] at hpc hunack henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine SepWPp.call_frame hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (ret_pc := entry + 840#64)
    (by simp_all) (by simp_all) hspAl rfl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by rw [sepConj_assoc] at hm; exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_unack htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [unackItemsSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (poll_unackItems_pack_pollWithBaseKey_trap sp items ts) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp (entry + 840#64) (entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState_trap, sp] at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hinv.1, hinv.2, by wp_norm_goal⟩
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, encSpillsAtV] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_unackItems_to_dur_ok {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (R0 : SepProp) (s0 s : State)
    (hpk : sess.pendingPreKey = some items)
    (hkey : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.KeyStateV kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hkey with ⟨hcur, hscope, hotr, hrem, hpc, hmeta, htr, hregs, hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hregs with ⟨hx0, hx8, hx20, hx22, hx23, hx25, hx26, hx27, hx28⟩
  have hmeta' := hmeta
  rcases hmeta' with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  rw [sp_sub_60_eq_add_b80 s0.sp] at hx29
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 836#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv ⟨hfrozen, hsym⟩
    (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 1732#64)
    (encSeam_mem_group hmem)
  dsimp only [takenSlots, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon]
  rw [poll_unackItems_regions sp, encSubStack_split_unack hsp]
  refine SepWPp.fold (takenRecord_sessionRecordAt_unpack A sp sess taken) (by sep_focus) ?_
  refine sepWPp_elim_ex fun prevCap => sepWPp_elim_ex fun prevPtr => sepWPp_elim_ex fun G => ?_
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env
  rw [henc_fn] at hpc
  have hunack := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.unack_ok_at_enc env
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x344 0x4c
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x680 0x44
  dsimp only [tripleRatchetProgAt] at hpc hunack henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine SepWPp.call_frame hunack
    (x := (⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ : UnackCall))
    (ret_pc := entry + 840#64)
    (by simp_all) (by simp_all) hspAl rfl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by rw [sepConj_assoc] at hm; exact CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_unack htr hcur hscope hotr hrem hpk hm)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [unackItemsSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (unackOutAt_taken_some sp G.kyber sess items hpk) (by sep_focus) ?_
  refine sepWPp_elim_ex fun ts => ?_
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun hts => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack32 (sp + 0x580#64) items.preKeyId) (by sep_focus)
    fun pkVal hpkVal => ?_
  refine sepWPp_fold_ex1 (optU32At_unpack64 (sp + 0x588#64) (sess.pendingKyberPreKey.map (·.preKeyId)))
    (by sep_focus) fun kyIdVal hkyIdVal => ?_
  refine sepWPp_fold_ex5 (baseKeyShift_unpack_59c sp items.baseKey) (by sep_focus)
    fun bk0 bk1 bk2 bk3 bk4 hbk => ?_
  refine sepWPp_fold_ex2 (unackKyberSliceAt_unpack (sp + 0x5c0#64) G.kyber) (by sep_focus)
    fun kyPtr kyLen hkySlice => ?_
  refine SepWPp.fold (curScratch_unackItems_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun s48 => sepWPp_elim_ex fun s40 => sepWPp_elim_ex fun s38 =>
    sepWPp_elim_ex fun s34 => sepWPp_elim_ex fun s28 => sepWPp_elim_ex fun s24 =>
    sepWPp_elim_ex fun s18 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0x870#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w890 => sepWPp_elim_ex fun w888 => sepWPp_elim_ex fun w880 =>
    sepWPp_elim_ex fun w878 => sepWPp_elim_ex fun w870 => ?_
  refine SepWPp.fold (memRegion_36_unpack (sp + 0xab0#64)) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wad0 => sepWPp_elim_ex fun wac8 => sepWPp_elim_ex fun wac0 =>
    sepWPp_elim_ex fun wab8 => sepWPp_elim_ex fun wab0 => ?_
  refine SepWPp.fold (memRegion_16_ts_unpack_b00 sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun wb08 => sepWPp_elim_ex fun wb00 => ?_
  apply SepWPp.of_sepWP_ret
  wp_steps
  refine SepWP.fold (ts_cells_entails_memRegion_16_b00 sp ts.tvSec ts.tvNsec) (by sep_focus) ?_
  refine SepWP.fold (baseKeyShift_pack_ab0 sp items.baseKey bk0 bk1 bk2 bk3 bk4 hbk) (by sep_focus) ?_
  refine SepWP.fold (cells36_entails_memRegion_36_870 sp bk0 bk1 bk2 bk3 bk4) (by sep_focus) ?_
  refine SepWP.fold
    (unackOut_cells_entails_memRegion_88_580 sp _ pkVal _ ts.tvSec ts.tvNsec bk0 bk1 bk2 bk3 bk4 kyPtr kyLen items.signedPreKeyId)
    (by sep_focus) ?_
  refine SepWP.fold (poll_unackItems_pack_pollWithBaseKey sp items) (by sep_focus) ?_
  refine sepWP_fold_preKeyScratch sp kyLen _ items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey
    (by sep_focus) (by rfl) ?_
  refine SepWP.fold (encSubStack_pack_unack hsp (entry + 840#64) (entry + bv% ((2^64 + ls_off% "<libsignal_protocol::state::session::SessionState>::unacknowledged_pre_key_message_items" - ls_off% "libsignal_cli_ratchet::encrypt") % 2^64))) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState, sp] at hsp1 hx19_1 hx20_1 hx22_1 hx25_1 hx26_1 hx28_1 hx29_1 hvregs_1 hmf ⊢
  refine ⟨prevCap, prevPtr, G, ts, pkVal, kyIdVal, kyPtr, kyLen,
    hts, hpkVal, hkyIdVal, hkySlice, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; wp_norm_goal
  · refine ⟨by wp_norm_goal, by wp_norm_goal, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; wp_norm_goal; exact hsp0Al,
      by rw [sp_sub_60_eq_add_b80 s0.sp]; wp_norm_goal,
      by wp_norm_goal, hinv.1, hinv.2, by wp_norm_goal⟩
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · cases items.preKeyId <;> wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · wp_norm_goal
  · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon, encSpillsAtV] at hmf ⊢; arm64_sep_close

/-! ## 2. E6a (`+0x6c4..+0x6fc`): `durationSince` and `timeAdd` -/

/-- State at `+0x6fc` (`CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1788#64`), right after `bl timeAdd`. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState {A : RustAlloc} {img : Obj.Image}
    (kit : SessionStoreSpec A img.base) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts expiry : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  SystemTime.unixEpoch.checkedAddSecs items.timestamp.toNat = some ts ∧
  ts.checkedAddSecs maxUnacknowledgedSessionAge = some expiry ∧
  optU32ValProp items.preKeyId pkVal ∧
  optU32ValProp (sess.pendingKyberPreKey.map (·.preKeyId)) kyIdVal ∧
  unackKyberSliceProp G.kyber kyPtr kyLen ∧
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1788#64 ∧
  encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x0 = expiry.tvSec ∧
  (s.readReg64 .x1).setWidth 32 = expiry.tvNsec ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧
  (s.readReg64 .x21).setWidth 32 = ts.tvNsec ∧
  s.readReg64 .x22 = sp + 0x8b8#64 ∧
  s.readReg64 .x23 = kyPtr ∧
  (s.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) ∧
  s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧
  s.readReg64 .x27 = ts.tvSec ∧
  s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  (s.mem ⊨
    vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
    sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
    otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
    ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
    memRegion (sp + 0x370#64) 0xf8 ∗
    preKeyScratch sp kyLen items.signedPreKeyId kyIdVal pkVal sess.pendingKyberPreKey ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    pollWithBaseKey sp items ∗
    memRegion x.ret 248 ∗
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x 0 s0 ∗ (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_staleness_to_add_ok_trap {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState_trap kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ expiry,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hdur with ⟨hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx2, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1732#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv_trap ⟨hfrozen, hsym⟩
    (target := (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 1788#64)
    (dur_mem_group hmem)
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon]
  rw [pollWithBaseKey_dur_unpack_trap sp items ts, encSubStack_split_ext hsp]
  refine SepWPp.fold (durationSinceBounded_b00_intro_trap sp ts.tvSec ts.tvNsec hts_nsec) (by sep_focus) ?_
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr_trap env
  rw [henc_fn] at hpc
  have hdur_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.durationSince_ok_at_enc_trap env
  have hadd_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.timeAdd_ok_at_enc_trap env
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (trTrapExterns C abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6c4 0x38
  dsimp only [trTrapProgAt] at hpc hdur_call hadd_call henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (trTrapExterns C abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime>::duration_since" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (ret_pc := entry + 1736#64)
    (by simp_all) (by simp_all) hspAl rfl rfl
    ⟨by simp_all, by simp_all, by dsimp [State.setPC, State.writeReg64, State.readReg64, Reg.x2] at hx2 ⊢; rw [hx2]; decide⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [CryptoVerification.SignalSession.Cli.Slots.durationSinceBoundedSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (ret_pc := entry + 1788#64)
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    rfl rfl
    ⟨by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_timeAdd (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState, sp] at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, ?_, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; exact hpc2
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hinv.1, hinv.2, hvregs_2⟩
  · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon] at hmf ⊢; arm64_sep_close

set_option maxHeartbeats 800000 in
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segPreKey_staleness_to_add_ok {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (items : PendingPreKey) (prevCap prevPtr : BitVec 64) (G : SessionGhost)
    (ts : SystemTime) (pkVal kyIdVal : BitVec 32) (kyPtr kyLen : BitVec 64)
    (R0 : SepProp) (s0 s : State)
    (hcur : r.currentSession = some sess)
    (hscope : kit.ScopeAt Scope st0 x.rem.val r)
    (hotr : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (hpk : sess.pendingPreKey = some items)
    (hdur : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessDurState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
      prevCap prevPtr G ts pkVal kyIdVal kyPtr kyLen R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ expiry,
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState kit st0 ikit ist0 ctl encRecord x r sess otr taken pqCap pqPtr k items
          prevCap prevPtr G ts expiry pkVal kyIdVal kyPtr kyLen R0 s0 s') := by
  rcases hdur with ⟨hts, hpkVal, hkyIdVal, hkySlice, hpc, hmeta, htr,
    hx0, hx8, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28,
    hptlen, hrestlen, hlocA, hnow, hstack, hmem⟩
  rcases hmeta with ⟨hstat, hsp, hsp0Al, hspAl, hx29, hx19, hfrozen, hsym, hvregs⟩
  have hts_nsec : ts.tvNsec.toNat < 10 ^ 9 := (unixEpoch_checkedAddSecs_tvNsec hts).2
  set sp := s0.sp - 0xbe0#64
  change s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 1732#64 at hpc
  apply CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.segExit_of_sepWPp_callInv ⟨hfrozen, hsym⟩
    (target := (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 1788#64)
    (dur_mem_group hmem)
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon]
  rw [pollWithBaseKey_dur_unpack sp items, encSubStack_split_ext hsp]
  have henc_fn := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.encEntry_eq_fnAddr env
  rw [henc_fn] at hpc
  have hdur_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.durationSince_ok_at_enc env
  have hadd_call := henc_fn ▸ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.timeAdd_ok_at_enc env
  clear env
  messageEncryptPreKey_fetches_cli img.base (Rust.withPanics (tripleRatchetExterns C ctl abs)) (ls_lemma% fnOff "libsignal_cli_ratchet::encrypt") 0x6c4 0x38
  dsimp only [tripleRatchetProgAt] at hpc hdur_call hadd_call henc_fn ⊢
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime>::duration_since" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_step
  apply SepWP.done (by simp_all) (by simp_all)
  refine SepWPp.call_frame hdur_call
    (x := (sp + 0xb00#64, sp + 0x580#64))
    (ret_pc := entry + 1736#64)
    (by simp_all) (by simp_all) hspAl rfl rfl ⟨by simp_all, by simp_all⟩
    (by dsimp [State.sp, State.setPC, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun _ _ hm => by
      dsimp only [durationSinceSpec, Spec.onPanic] at hm
      rw [sepConj_assoc] at hm
      exact (not_satisfies_false_sepConj hm).elim)
    fun s1 hpc1 hstat1 hsp1 hcs1 => ?_
  dsimp only [durationSinceSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun htr1 => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp1) (by sep_focus) ?_
  have hcs1' := calleeSavedPreserved_after_bl hcs1; clear hcs1
  rcases hcs1' with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx29_1, hvregs_1⟩
  rw [hx19] at hx19_1; rw [hx20] at hx20_1; rw [hx22] at hx22_1; rw [hx23] at hx23_1
  rw [hx25] at hx25_1; rw [hx26] at hx26_1; rw [hx27] at hx27_1; rw [hx28] at hx28_1; rw [hx29] at hx29_1; rw [hvregs] at hvregs_1
  have hx21_1' : (s1.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s1.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_1]; exact hx21
  have hx24_1' : (s1.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s1.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_1]; exact hx24
  rw [sp_after_bl] at hsp1
  rw [trace_after_bl] at htr1
  have hsp1_al : s1.spAligned = true := by
    unfold State.spAligned at hspAl ⊢; rwa [hsp1]
  rw [hsp] at hsp1
  rw [htr] at htr1
  refine SepWPp.fold (dur_ret_24_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w588 => sepWPp_elim_ex fun w580 => ?_
  refine SepWPp.fold (memRegion_8_898_unpack sp) (by sep_focus) ?_
  refine sepWPp_elim_ex fun w898 => ?_
  apply SepWPp.of_sepWP (mid := entry + bv% ((2^64 + ls_off% "<std::time::SystemTime as core::ops::arith::Add<core::time::Duration>>::add" - (ls_off% "libsignal_cli_ratchet::encrypt")) % 2^64))
  wp_steps
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  refine SepWPp.call_frame hadd_call
    (x := (ts, maxUnacknowledgedSessionAge))
    (ret_pc := entry + 1788#64)
    (by wp_norm_goal) (by wp_norm_goal)
    (by unfold State.spAligned at hsp1_al ⊢; rw [hsp1] at hsp1_al; wp_norm_goal)
    rfl rfl
    ⟨by wp_norm_goal, by wp_norm_goal, hts_nsec, by wp_norm_goal, by wp_norm_goal⟩
    (by dsimp [State.sp, State.setPC, State.setMem, State.setPState, State.writeReg64, State.readReg64]; sep_focus)
    (fun _ _ _ _ hm => not_satisfies_false_sepConj hm)
    (fun sf _ hm => by
      rw [sepConj_assoc] at hm
      refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.onPanic_of_timeAdd (s := _) ?_ hcur hscope hotr hrem hpk hts hm
      wp_norm_goal)
    fun s2 hpc2 hstat2 hsp2 hcs2 => ?_
  dsimp only [timeAddSpec]
  rw [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hexp, htr2⟩ => ?_
  refine SepWPp.fold (stackAt_eq_sp hsp2) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hx29_2, hvregs_2⟩
  simp only [wp_norm, arm64_norm]
    at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hx29_2 hvregs_2 hsp2 htr2
  rw [hx19_1] at hx19_2; rw [hx20_1] at hx20_2; rw [hx22_1] at hx22_2; rw [hx23_1] at hx23_2
  rw [hx25_1] at hx25_2; rw [hx26_1] at hx26_2; rw [hx27_1] at hx27_2; rw [hx28_1] at hx28_2; rw [hx29_1] at hx29_2; rw [hvregs_1] at hvregs_2
  have hx21_2' : (s2.readReg64 .x21).setWidth 32 = ts.tvNsec := by
    change (s2.readReg64 (.gpr 21#5)).setWidth 32 = ts.tvNsec; rw [hx21_2]; exact hx21_1'
  have hx24_2' : (s2.readReg64 .x24).setWidth 32 = (if items.preKeyId.isSome then 1#32 else 0#32) := by
    change (s2.readReg64 (.gpr 24#5)).setWidth 32 = _; rw [hx24_2]; exact hx24_1'
  rw [hsp1] at hsp2
  rw [htr1] at htr2
  apply SepWPp.of_sepWP_ret
  refine SepWP.fold (pollWithBaseKey_dur_pack sp items w580 w588 _) (by sep_focus) ?_
  have hsp2_pack :
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - extHookStack) ∗
        stackAt s2.sp extHookStack) ⊢ stackAt sp encSubStack := by
    rw [hsp2, ← encSubStack_split_ext rfl]
    exact Entails.refl _
  refine SepWP.fold hsp2_pack (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro hinv hmf
  dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey.StalenessAddState, sp] at hsp2 hx19_2 hx20_2 hx22_2 hx25_2 hx26_2 hx28_2 hx29_2 hvregs_2 hmf ⊢
  refine ⟨⟨s2.readReg64 .x0, (s2.readReg64 .x1).setWidth 32⟩,
    hts, hexp, hpkVal, hkyIdVal, hkySlice, ?_, ?_, htr2, rfl, rfl,
    hx20_2, hx21_2', hx22_2, hx23_2, hx24_2', hx25_2, hx26_2, hx27_2, hx28_2,
    hptlen, hrestlen, hlocA, hnow, hstack, ?_⟩
  · rw [henc_fn]; exact hpc2
  · refine ⟨hstat2, hsp2, hsp0Al,
      by unfold State.spAligned at hsp0Al ⊢; rw [hsp2]; wp_norm_goal,
      hx29_2, hx19_2, hinv.1, hinv.2, hvregs_2⟩
  · dsimp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon] at hmf ⊢; arm64_sep_close

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegPreKey
