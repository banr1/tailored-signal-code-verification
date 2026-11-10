/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalOk
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem

/-!
# `segSignal` Success Path (`+0x3a4..+0x418` → `Cm` `+0xa70`)

Defines `SegSignalRetStateV` at `+0x3a4` and proves `segSignal_ok_path` (and `segSignal_ok_path_trap`),
copying the 120-byte `SignalMessage` into `sp + 0x370` with `ctSignalTag` and branching to `+0xa70`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Encrypt

open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec

open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession

open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

set_option maxRecDepth 200000

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- **Ret** (`+0x3a4`, parameterized by `kit`, `st0`, `ikit`, and `ist0`): `OTR::encrypt` returned
(not panicking) at segSignal. -/
def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV {img : Obj.Image} {A : RustAlloc} (kit : SessionStoreSpec A img.base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (R0 : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧ sess.pendingPreKey = none ∧
  (segSignalRes C S x otr).1 ≠ .error .panic ∧
  s.pc = CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img + 0x3a4#64 ∧ encMidMeta img x s0 s ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) ∧
  s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
  s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧
  x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
  x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
  ∃ g : RecordGhost, (s.mem ⊨
    (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' (segSignalRes C S x otr).2) ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    cmScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗
      signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (segSignalRes C S x otr).1 ∗
      memRegion (sp + 0x5f8#64) 0x588) ∗
    memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x (S.draws otr.pqrState x.rest) s0 ∗
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0))

private theorem pqCap_add_one_ne_zero {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    cap + 1#64 ≠ 0#64 := by
  intro heq
  have ht := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at ht
  omega

private theorem segSignal_list_len3 {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

private theorem signalMessageWordsAt_eq_words64At (gm : SignalMessageGhost) (sm : SignalMessage)
    (a : BitVec 64) (m7 m8 m9 m10 m11 m12 m14 : BitVec 64) :
    signalMessageWordsAt gm sm a m7 m8 m9 m10 m11 m12 m14 =
      words64At a [gm.pqCap, gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
        BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
        m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14] := by
  simp only [signalMessageWordsAt, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd]

private theorem signalMessageAt_relocate (A : RustAlloc) (gm : SignalMessageGhost) (src : BitVec 64)
    (sm : SignalMessage) {m : Memory} {R : SepProp}
    (hm : m ⊨ signalMessageAt A gm src sm ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (m ⊨ words64At src [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ∗ R) ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) := by
  have hm' := Satisfies.mono (sepConj_mono_left (signalMessageAt_unpack A gm src sm)) hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm'
  rcases hm' with ⟨hpq, hm'⟩
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm'
  obtain ⟨m7, m8, m9, m10, m11, m12, m14, hm'⟩ := hm'
  rw [signalMessageWordsAt_eq_words64At, sepConj_assoc] at hm'
  refine ⟨gm.pqPtr, BitVec.ofNat 64 sm.pqRatchet.length, gm.ctPtr,
    BitVec.ofNat 64 sm.ciphertext.length, gm.serPtr, BitVec.ofNat 64 sm.serialized.length,
    m7, m8, m9, m10, m11, m12, sm.previousCounter ++ sm.counter, m14,
    signalMessageHeap A gm sm m7 m8 m9 m10 m11 m12 m14,
    pqCap_add_one_ne_zero hpq, hm', ?_⟩
  intro dst
  rw [← signalMessageWordsAt_eq_words64At]
  exact signalMessageAt_pack A gm dst sm m7 m8 m9 m10 m11 m12 m14

private def _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (x : WithStoresEncGhost)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (k : IdentityKey) (draws : Nat) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
  ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
  memRegion (sp + 0x3f0#64) 120 ∗
  cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x5f8#64) 0x508 ∗
  memRegion (sp + 0xb18#64) 0x68 ∗
  memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_unpack_trap {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (k : IdentityKey) (sm : SignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp)
    (s0 s : State)
    (hm : s.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :
    ∃ (pqCap' pqPtr' : BitVec 64) (gm : SignalMessageGhost)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) ∧
      (s.mem ⊨ (words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15]) ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr'
          k draws sp H s0 ∗ R)) := by
  unfold signalMessageResultAt at hm
  dsimp only at hm
  have hm1 : s.mem ⊨
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqCap', hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqPtr', hm1⟩ := hm1
  have hm2 : s.mem ⊨
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨gm, hm2⟩ := hm2
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H, hpq, hm3, hpack⟩ :=
    signalMessageAt_relocate A gm (sp + 0x580#64) sm hm2
  have h370 : memRegion (sp + 0x370#64) 0xf8 =
      memRegion (sp + 0x370#64) 128 ∗ memRegion (sp + 0x3f0#64) 120 :=
    segSignal_memRegion_cut (sp + 0x370#64) (sp + 0x3f0#64) 0xf8 128 120 (by bv_omega) (by decide) (by decide)
  have h5f8 : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗
        (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68) := by
    rw [segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  rw [h370, h5f8] at hm3
  have hm_d : s.mem ⊨ memRegion (sp + 0x370#64) (8 * 16) ∗
      (memRegion (sp + 0xb00#64) (8 * 3) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) := by
    unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm3
  obtain ⟨ds, hds_len, hm_d⟩ := memRegion_exists_words64At 16 (sp + 0x370#64) (by decide) hm_d
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :=
    segSignal_list_len16 ds hds_len
  have hm_v : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗
      (words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15] ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_d
  obtain ⟨vs, hvs_len, hm_v⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm_v
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3 vs hvs_len
  refine ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_v

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_unpack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (k : IdentityKey) (sm : SignalMessage) (draws : Nat) (sp : BitVec 64) (R : SepProp)
    (s0 s : State)
    (hm : s.mem ⊨
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
          otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗
        signalMessageResultAt A (utf8 "encrypt") (sp + 0x580#64) (.ok sm) ∗
        memRegion (sp + 0x5f8#64) 0x588) ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :
    ∃ (pqCap' pqPtr' : BitVec 64) (gm : SignalMessageGhost)
      (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64) (H : SepProp),
      gm.pqCap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
          H ⊢ signalMessageAt A gm dst sm) ∧
      (s.mem ⊨ (words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗
          words64At (sp + 0xb00#64) [v0, v1, v2] ∗
          words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
            d14, d15]) ∗
        (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr'
          k draws sp H s0 ∗ R)) := by
  unfold signalMessageResultAt at hm
  dsimp only at hm
  have hm1 : s.mem ⊨
      (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
        otrAt A (sp + 0x288#64) pqCap' pqPtr' otr') ∗
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqCap', hm1⟩ := hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨pqPtr', hm1⟩ := hm1
  have hm2 : s.mem ⊨
      (∃∗ gm : SignalMessageGhost, signalMessageAt A gm (sp + 0x580#64) sm) ∗
      (otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
        ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x588 ∗
        memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm1
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm2
  obtain ⟨gm, hm2⟩ := hm2
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, H, hpq, hm3, hpack⟩ :=
    signalMessageAt_relocate A gm (sp + 0x580#64) sm hm2
  have h370 : memRegion (sp + 0x370#64) 0xf8 =
      memRegion (sp + 0x370#64) 128 ∗ memRegion (sp + 0x3f0#64) 120 :=
    segSignal_memRegion_cut (sp + 0x370#64) (sp + 0x3f0#64) 0xf8 128 120 (by bv_omega) (by decide) (by decide)
  have h5f8 : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗
        (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68) := by
    rw [segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  rw [h370, h5f8] at hm3
  have hm_d : s.mem ⊨ memRegion (sp + 0x370#64) (8 * 16) ∗
      (memRegion (sp + 0xb00#64) (8 * 3) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) := by
    unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame
    exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm3
  obtain ⟨ds, hds_len, hm_d⟩ := memRegion_exists_words64At 16 (sp + 0x370#64) (by decide) hm_d
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, rfl⟩ :=
    segSignal_list_len16 ds hds_len
  have hm_v : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗
      (words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15] ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr' pqCap' pqPtr' k
          draws sp H s0 ∗ R) :=
    Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_d
  obtain ⟨vs, hvs_len, hm_v⟩ := memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm_v
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3 vs hvs_len
  refine ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s.mem ⊨ ·) (by ac_rfl)) hm_v

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_pack_trap {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (sm : SignalMessage) (gm : SignalMessageGhost)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp) (s0 s1 : State)
    (hpack : ∀ dst : BitVec 64,
      words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ⊢ signalMessageAt A gm dst sm)
    (hPm : Pm ⊢ words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗
      words64At (sp + 0xb00#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14])
    (hm : s1.mem ⊨ Pm ∗ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr'
      pqCap' pqPtr' k draws sp H s0 ∗ R)) :
    s1.mem ⊨ cmSlots A sp sess taken otr' pqCap' pqPtr' k (.signalMessage sm) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame at hm1
  have h370_hd :
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14] =
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
        words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14] := rfl
  rw [h370_hd] at hm1
  have h580 :
      words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14] ⊢ memRegion (sp + 0x580#64) 120 :=
    words64At_entails_memRegion
      [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
      (sp + 0x580#64) (by simp only [List.length_cons, List.length_nil]; decide)
  have hb00 :
      words64At (sp + 0xb00#64) [w4, w5, w6] ⊢ memRegion (sp + 0xb00#64) 24 :=
    words64At_entails_memRegion [w4, w5, w6] (sp + 0xb00#64)
      (by simp only [List.length_cons, List.length_nil]; decide)
  have hsm_ex :
      words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗ H ⊢
      ∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm :=
    Entails.trans (hpack ((sp + 0x370#64) + 8#64)) (Entails.sepExists_right gm (Entails.refl _))
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.sepExists_right g (Entails.refl _)
  have hm_rearr : s1.mem ⊨
      ((words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        words64At (sp + 0xb00#64) [w4, w5, w6]) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗ memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x508 ∗
      memRegion (sp + 0xb18#64) 0x68 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hsm_ex (sepConj_mono hrec_ex (sepConj_mono h580 hb00))))
    hm_rearr
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68))) := by
    rw [segSignal_memRegion_cut (sp + 0x46a#64) (sp + 0x580#64) 0x716 0x116 0x600 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x580#64) (sp + 0x5f8#64) 0x600 120 0x588 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  have h3f0 : (sp + 0x370#64) + 0x80#64 = sp + 0x3f0#64 := by bv_omega
  have hm_poll : s1.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68)))) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
      (∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm) ∗
      memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold cmSlots takenSlots apiEncResultAt
  dsimp only
  rw [h3f0]
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_poll

private theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_pack {ss_vt id_vt : BitVec 64} (A : RustAlloc) (ctl : BitVec 64)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (g : RecordGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (k : IdentityKey) (sm : SignalMessage) (gm : SignalMessageGhost)
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 : BitVec 64)
    (draws : Nat) (sp : BitVec 64) (H R Pm : SepProp) (s0 s1 : State)
    (hpack : ∀ dst : BitVec 64,
      words64At dst [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14] ∗
        H ⊢ signalMessageAt A gm dst sm)
    (hPm : Pm ⊢ words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗
      words64At (sp + 0xb00#64) [w4, w5, w6] ∗
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14])
    (hm : s1.mem ⊨ Pm ∗ (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame (ss_vt := ss_vt) (id_vt := id_vt) A ctl img x g sess taken otr'
      pqCap' pqPtr' k draws sp H s0 ∗ R)) :
    s1.mem ⊨ cmSlots A sp sess taken otr' pqCap' pqPtr' k (.signalMessage sm) ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignalOkFrame at hm1
  have h370_hd :
      words64At (sp + 0x370#64) [0x8000000000000000#64, gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8,
        w9, w10, w11, w12, w13, w14] =
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
        words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
          w12, w13, w14] := rfl
  rw [h370_hd] at hm1
  have h580 :
      words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
        w14] ⊢ memRegion (sp + 0x580#64) 120 :=
    words64At_entails_memRegion
      [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14]
      (sp + 0x580#64) (by simp only [List.length_cons, List.length_nil]; decide)
  have hb00 :
      words64At (sp + 0xb00#64) [w4, w5, w6] ⊢ memRegion (sp + 0xb00#64) 24 :=
    words64At_entails_memRegion [w4, w5, w6] (sp + 0xb00#64)
      (by simp only [List.length_cons, List.length_nil]; decide)
  have hsm_ex :
      words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
        w12, w13, w14] ∗ H ⊢
      ∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm :=
    Entails.trans (hpack ((sp + 0x370#64) + 8#64)) (Entails.sepExists_right gm (Entails.refl _))
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.sepExists_right g (Entails.refl _)
  have hm_rearr : s1.mem ⊨
      ((words64At ((sp + 0x370#64) + 8#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11,
            w12, w13, w14] ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        words64At (sp + 0x580#64) [gm.pqCap, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
          w13, w14] ∗
        words64At (sp + 0xb00#64) [w4, w5, w6]) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗ memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5f8#64) 0x508 ∗
      memRegion (sp + 0xb18#64) 0x68 ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hsm_ex (sepConj_mono hrec_ex (sepConj_mono h580 hb00))))
    hm_rearr
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68))) := by
    rw [segSignal_memRegion_cut (sp + 0x46a#64) (sp + 0x580#64) 0x716 0x116 0x600 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x580#64) (sp + 0x5f8#64) 0x600 120 0x588 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0x5f8#64) (sp + 0xb00#64) 0x588 0x508 0x80 (by bv_omega) (by decide)
          (by decide),
        segSignal_memRegion_cut (sp + 0xb00#64) (sp + 0xb18#64) 0x80 24 0x68 (by bv_omega) (by decide) (by decide)]
  have h3f0 : (sp + 0x370#64) + 0x80#64 = sp + 0x3f0#64 := by bv_omega
  have hm_poll : s1.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗
        (memRegion (sp + 0x580#64) 120 ∗
          (memRegion (sp + 0x5f8#64) 0x508 ∗
            (memRegion (sp + 0xb00#64) 24 ∗ memRegion (sp + 0xb18#64) 0x68)))) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap' pqPtr' otr' ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗
      ((sp + 0x370#64) ↦₆₄ ctSignalTag) ∗
      (∃∗ gm' : SignalMessageGhost, signalMessageAt A gm' ((sp + 0x370#64) + 8#64) sm) ∗
      memRegion (sp + 0x3f0#64) 120 ∗
      cmScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encCommon A ctl img x draws s0 ∗ R :=
    Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold cmSlots takenSlots apiEncResultAt
  dsimp only
  rw [h3f0]
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by ac_rfl)) hm_poll

/-- **The `Ok` path** (`+0x3a4..+0x418`): `OTR::encrypt` = `Ok sm` → Cm (`+0xa70`) with the CM
`.signalMessage sm` at `sp+0x370` (`ctSignalTag` + the 120-byte message copied from `sp+0x580`). -/
theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_path_trap {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv_trap kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit_trap kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, g, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt_trap (C := C) (abs := abs) env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (trTrapProgAt img.base C abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64 := by
    simpa only [hentry] using hs_pc
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]
    change s0.sp - 0x60#64 = (s0.sp - 0xbe0#64) + 0xb80#64
    bv_omega
  rw [hok] at hm
  obtain ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, hm_unp⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_unpack_trap A ctl img x g sess taken (segSignalRes C S x otr).2 k sm
      (S.draws otr.pqrState x.rest) sp R s0 s hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP_trap hm_unp
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_ok_trap hs_pc' hrun hsp hal hx25 hx26 hx29' hpq) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x19, hs1_x20, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_ok := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_pack_trap A ctl img x g sess taken (segSignalRes C S x otr).2 pqCap' pqPtr' k sm gm
    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
    (S.draws otr.pqrState x.rest) sp H R Pm1 s0 s1 hpack hPm1 hm1
  have hstep5 : EncEncryptStep C S uuidTryParse x sess otr (.signalMessage sm) (segSignalRes C S x otr).2 := by
    unfold EncEncryptStep
    rw [hnone]
    exact ⟨sm, execOk_of_exec_ok hok, rfl⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next_trap ⟨.signalMessage sm, (segSignalRes C S x otr).2, pqCap', pqPtr',
    ⟨hcur, hsc, hfrom, hrem, hstep5⟩, ?_⟩
  refine ⟨?_, ⟨hs1_run, hs1_sp, hal0, hs1_al, hs1_x29.trans hx29, hs1_x19.trans hx19,
      hfl1, hsym1, hs1_vregs.trans hvregs⟩, hs1_tr.trans htr,
    ⟨hs1_x20.trans hx20, hs1_x25.trans hx25, hs1_x26.trans hx26, hs1_x28.trans hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm1_ok⟩
  rw [hs1_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmPC, hentry]

theorem _root_.CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_path {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (sm : SignalMessage) (hok : (segSignalRes C S x otr).1 = .ok sm)
    (hs : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s
      (fun s' => ∃ m otr' pqCap' pqPtr',
        CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.CmStateV kit st0 ikit ist0 Scope C ctl uuidTryParse S encRecord x r sess otr taken k m otr' pqCap'
          pqPtr' R0 s0 s') := by
  let R := encStoreExtra kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hcur, hsc, hfrom, hrem, hnone, _, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩,
    htr, hx20, hx25, hx26, hx28, hpt, hrest, hloc, hnow, hstk, g, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hentry : CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr CryptoVerification.Cli.LibsignalPublicApi.encryptWithStoresName + 0x3a4#64 := by
    simpa only [hentry] using hs_pc
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]
    change s0.sp - 0x60#64 = (s0.sp - 0xbe0#64) + 0xb80#64
    bv_omega
  rw [hok] at hm
  obtain ⟨pqCap', pqPtr', gm, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14,
    v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, H,
    hpq, hpack, hm_unp⟩ :=
    CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_unpack A ctl img x g sess taken (segSignalRes C S x otr).2 k sm
      (S.draws otr.pqrState x.rest) sp R s0 s hm
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.of_sepWP hm_unp
    (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_step_ok hs_pc' hrun hsp hal hx25 hx26 hx29' hpq) ?_
  intro s1 Pm1 hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x19, hs1_x20, hs1_x25, hs1_x26, hs1_x28, hs1_x29, hs1_vregs, hPm1⟩
  have ⟨hfl1, hsym1⟩ := callInv_steps hfl hsym hsteps01 hL0
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_ok := CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal.segSignal_ok_pack A ctl img x g sess taken (segSignalRes C S x otr).2 pqCap' pqPtr' k sm gm
    w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14
    (S.draws otr.pqrState x.rest) sp H R Pm1 s0 s1 hpack hPm1 hm1
  have hstep5 : EncEncryptStep C S uuidTryParse x sess otr (.signalMessage sm) (segSignalRes C S x otr).2 := by
    unfold EncEncryptStep
    rw [hnone]
    exact ⟨sm, execOk_of_exec_ok hok, rfl⟩
  refine CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom.SegExit.next ⟨.signalMessage sm, (segSignalRes C S x otr).2, pqCap', pqPtr',
    ⟨hcur, hsc, hfrom, hrem, hstep5⟩, ?_⟩
  refine ⟨?_, ⟨hs1_run, hs1_sp, hal0, hs1_al, hs1_x29.trans hx29, hs1_x19.trans hx19,
      hfl1, hsym1, hs1_vregs.trans hvregs⟩, hs1_tr.trans htr,
    ⟨hs1_x20.trans hx20, hs1_x25.trans hx25, hs1_x26.trans hx26, hs1_x28.trans hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm1_ok⟩
  rw [hs1_pc, CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.cmPC, hentry]

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
