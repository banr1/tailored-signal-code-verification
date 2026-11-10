/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
import ProofLib.SepLogic.WPp

/-!
# Segment S1 (`LoadRatchet`) Proofs for `try_decrypt_with_state`

Verifies Segment S1 (`+0x1d8 → +0x2a4 / +0x384 → +0x3b0`), calling
`TripleRatchet::from_session_state` and either returning an error via the epilogue
(`missingRemoteIdentity`) or copying `TripleRatchet` (`264` B) into the stack frame to enter
`FindChainState`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem loadRatchet_err_stack_recombine (sp remA tag w0 w1 w2 w3 w4 : BitVec 64) :
    (memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x38#64) 0x158 ∗
     ((sp + 0x190#64) ↦₆₄ errTag) ∗
     ((sp + 0x198#64) ↦₆₄ tag) ∗
     words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x1c8#64) 208 ∗
     memRegion (sp + 0x298#64) 0x268 ∗
     ((sp + 0x500#64) ↦₆₄ tag) ∗
     words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion sp 1408 := by
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x30#64) remA)
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x190#64) errTag)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x198#64) tag)
      (sepConj_mono (words5At_entails_memRegion (sp + 0x1a0#64) w0 w1 w2 w3 w4)
      (sepConj_mono_right
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x500#64) tag)
      (sepConj_mono_left (words5At_entails_memRegion (sp + 0x508#64) w0 w1 w2 w3 w4))))))))))) ?_
  rw [show sp + 0x530#64 = (sp + 0x508#64) + 40#64 by bv_omega,
      ← memRegion_split (sp + 0x508#64) 40 0x50 (by decide),
      show sp + 0x508#64 = (sp + 0x500#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x500#64) 8 120 (by decide),
      show sp + 0x500#64 = (sp + 0x298#64) + BitVec.ofNat 64 0x268 by bv_omega,
      ← memRegion_split (sp + 0x298#64) 0x268 128 (by decide),
      show sp + 0x298#64 = (sp + 0x1c8#64) + 208#64 by bv_omega,
      ← memRegion_split (sp + 0x1c8#64) 208 744 (by decide),
      show sp + 0x1c8#64 = (sp + 0x1a0#64) + 40#64 by bv_omega,
      ← memRegion_split (sp + 0x1a0#64) 40 952 (by decide),
      show sp + 0x1a0#64 = (sp + 0x198#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x198#64) 8 992 (by decide),
      show sp + 0x198#64 = (sp + 0x190#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 8 1000 (by decide),
      show sp + 0x190#64 = (sp + 0x38#64) + BitVec.ofNat 64 0x158 by bv_omega,
      ← memRegion_split (sp + 0x38#64) 0x158 1008 (by decide),
      show sp + 0x38#64 = (sp + 0x30#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x30#64) 8 1352 (by decide),
      ← memRegion_split sp 0x30 1360 (by decide)]
  exact Entails.refl _

theorem loadRatchet_err_pre_extract {A : RustAlloc} {ctl : BitVec 64} {img : Obj.Image}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State} (hnpan : e ≠ .panic)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    let sp := s0.sp - 1504#64
    ∃ (w0 w1 w2 w3 w4 t0 t1 t2 t3 t4 t5 r0 r1 r2 r3 r4 r5 : BitVec 64) (H_spe : SepProp),
      (∀ q : BitVec 64, (q ↦₆₄ speTag e) ∗ words5At (q + 8#64) w0 w1 w2 w3 w4 ∗ H_spe ⊢
        speAt A (utf8 "decrypt") q e) ∧
      (s.mem ⊨
        (((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
         words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ ((sp + 0x500#64) ↦₆₄ t0) ∗
         words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5) ∗
        (H_spe ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x30 ∗
         ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
         memRegion (sp + 0x1c8#64) 208 ∗ memRegion (sp + 0x298#64) 0x268 ∗
         memRegion (sp + 0x530#64) 0x50 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R)) := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (((sp + 0x190#64) ↦₆₄ errTag) ∗ speAt A (utf8 "decrypt") (sp + 0x190#64 + 8#64) e ∗
     memRegion (sp + 0x190#64 + 56#64) 208) ∗
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  rw [show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega,
      show sp + 0x190#64 + 56#64 = sp + 0x1c8#64 by bv_omega,
      speAt_eq_speTag_speBodyAt hnpan,
      show sp + 0x198#64 + 8#64 = sp + 0x1a0#64 by bv_omega,
      memRegion_split (sp + 0x298#64) 0x268 0x80 (by decide),
      show (sp + 0x298#64) + BitVec.ofNat 64 0x268 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 48 0x50 (by decide),
      show (sp + 0x500#64) + 48#64 = sp + 0x530#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x1a0#64) e ∗
      (memRegion (sp + 0x500#64) 48 ∗ memRegion x.ret 48 ∗ ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x1c8#64) 208 ∗ memRegion (sp + 0x298#64) 0x268 ∗
       memRegion (sp + 0x530#64) 0x50 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hm2, hent_spe⟩ := exists_words5_of_speBodyAt hnpan hm1
  have hm3 : s.mem ⊨ memRegion (sp + 0x500#64) 48 ∗
      (memRegion x.ret 48 ∗ words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ memRegion (sp + 0x530#64) 0x50 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by convert hm2 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm4⟩ := exists_words6_of_memRegion_48 hm3
  rw [show sp + 0x500#64 + 8#64 = sp + 0x508#64 by bv_omega] at hm4
  have hm5 : s.mem ⊨ memRegion x.ret 48 ∗
      (((sp + 0x500#64) ↦₆₄ t0) ∗ words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ H_spe ∗ ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x1c8#64) 208 ∗ memRegion (sp + 0x298#64) 0x268 ∗
       memRegion (sp + 0x530#64) 0x50 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hm6⟩ := exists_words6_of_memRegion_48 hm5
  refine ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, ?_⟩
  dsimp only [sp] at hm6 ⊢; convert hm6 using 1; sep_ac_rfl

theorem loadRatchet_after_call_error {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64) (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome himg x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract hnpan hm
  have hwp := loadRatchet_err_wp (ext := ext)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta hinv_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speAt A (utf8 "decrypt") x.ret e ∗ memRegion sp 1408 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H) ∗
      (memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

/-- All fields of `signalMessageAt A g a m` except the 32-bit `counter` at `a + 0x68`. -/

def signalMessageNoCounterAt (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) : SepProp :=
  ⌜macLength + 1 ≤ m.serialized.length ∧ m.serialized.length < 2 ^ 40 ∧
    m.ciphertext.length < 2 ^ 40 ∧ m.pqRatchet.length < 2 ^ 40 ∧
    (∀ ad, m.addresses = some ad → ad.length < 2 ^ 40)⌝ ∗
    vecU8At A a g.pqCap g.pqPtr m.pqRatchet ∗
    boxU8At A (a + 0x18#64) g.ctPtr m.ciphertext ∗
    boxU8At A (a + 0x28#64) g.serPtr m.serialized ∗
    ((a + 0x38#64) ↦ₛ m.senderRatchetKey.bytes.toList) ∗
    optBoxU8At A (a + 0x58#64) g.addrPtr m.addresses ∗
    ((a + 0x6c#64) ↦₃₂ m.previousCounter) ∗
    ((a + 0x70#64) ↦₈ m.messageVersion) ∗ memRegion (a + 0x71#64) 7

theorem signalMessageAt_eq_counter_rest (A : RustAlloc) (g : SignalMessageGhost) (a : BitVec 64)
    (m : SignalMessage) :
    signalMessageAt A g a m =
      ((a + 0x68#64) ↦₃₂ m.counter) ∗ signalMessageNoCounterAt A g a m := by
  unfold signalMessageAt signalMessageNoCounterAt; ac_rfl

theorem exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) ∧
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) := by
  obtain ⟨bs, H_tr, hlen, hm', hent⟩ := relocBytes_trBodyAt trG tr hpad p R m hm
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, by rwa [← hwords p], fun q => ?_⟩
  rw [← hwords q]
  exact hent q

theorem exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨ memRegion p 256 ∗ R) :
    ∃ d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
      d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64,
      m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R := by
  rw [memRegion_eq_exists_bytes p 256 (by decide), sepExists_sepConj_left, satisfies_sepExists] at hm
  rcases hm with ⟨bs, hm⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨hlen, hm⟩
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hwords⟩ :=
    exists_words32_of_length_256 hlen
  exact ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    by rwa [← hwords p]⟩



namespace ChainLookupFacts

theorem elim_exists_words32_of_trBodyAt {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hpad : trG.ratchet.senderPad.length = 100)
    (hm : m ⊨ trBodyAt p trG tr ∗ R)
    (k : ∀ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64)
      (H_tr : SepProp),
      (m ⊨ (words32At p w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
              w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗ R) →
      (∀ q : BitVec 64,
        words32At q w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr ⊢
        trBodyAt q trG tr) → P) : P :=
  let ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
    w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31,
    H_tr, hm_w, hent_tr⟩ := exists_words32_of_trBodyAt hpad hm
  k w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
    w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr

theorem elim_exists_words32_of_memRegion_256 {p : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨ memRegion p 256 ∗ R)
    (k : ∀ (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64),
      (m ⊨ words32At p d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
            d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗ R) → P) : P :=
  let ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31, hm'⟩ :=
    exists_words32_of_memRegion_256 hm
  k d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm'

end ChainLookupFacts

theorem loadRatchet_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R) :
    ∃ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗ memRegion (sp + 0x530#64) 0x50) ∗ R := by
  let F_rem := memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗
    memRegion (sp + 0x2ad#64) 0x253 ∗ memRegion (sp + 0x530#64) 0x50
  rw [memRegion_split sp 0x20 0x10 (by decide),
      memRegion_split (sp + 0x20#64) 8 8 (by decide),
      show (sp + 0x20#64) + 8#64 = sp + 0x28#64 by bv_omega,
      memRegion_split (sp + 0x28#64) 4 4 (by decide),
      show (sp + 0x28#64) + 4#64 = sp + 0x2c#64 by bv_omega,
      memRegion_split (sp + 0x38#64) 8 0x150 (by decide),
      show (sp + 0x38#64) + 8#64 = sp + 0x40#64 by bv_omega,
      memRegion_split (sp + 0x40#64) 256 0x50 (by decide),
      show (sp + 0x40#64) + 256#64 = sp + 0x140#64 by bv_omega,
      memRegion_split (sp + 0x298#64) 8 0x2e0 (by decide),
      show (sp + 0x298#64) + 8#64 = sp + 0x2a0#64 by bv_omega,
      memRegion_split (sp + 0x2a0#64) 8 0x2d8 (by decide),
      show (sp + 0x2a0#64) + 8#64 = sp + 0x2a8#64 by bv_omega,
      memRegion_split (sp + 0x2a8#64) 4 0x2d4 (by decide),
      show (sp + 0x2a8#64) + 4#64 = sp + 0x2ac#64 by bv_omega,
      memRegion_split (sp + 0x2ac#64) 1 0x2d3 (by decide),
      show (sp + 0x2ac#64) + 1#64 = sp + 0x2ad#64 by bv_omega,
      memRegion_split (sp + 0x2ad#64) 0x253 0x80 (by decide),
      show (sp + 0x2ad#64) + BitVec.ofNat 64 0x253 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 48 0x50 (by decide),
      show (sp + 0x500#64) + 48#64 = sp + 0x530#64 by bv_omega] at hm
  have hm1 : m ⊨ memRegion (sp + 0x20#64) 8 ∗
      (memRegion (sp + 0x28#64) 4 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗ memRegion (sp + 0x2ac#64) 1 ∗ memRegion (sp + 0x500#64) 48 ∗
       F_rem ∗ R) := by dsimp only [F_rem]; convert hm using 1; sep_ac_rfl
  obtain ⟨g20, hm1⟩ := exists_word64_of_memRegion_8 hm1
  have hm2 : m ⊨ memRegion (sp + 0x28#64) 4 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗ memRegion (sp + 0x2ac#64) 1 ∗ memRegion (sp + 0x500#64) 48 ∗
       F_rem ∗ R) := by convert hm1 using 1; sep_ac_rfl
  obtain ⟨g28, hm2⟩ := exists_word32_of_memRegion_4 hm2
  have hm3 : m ⊨ memRegion (sp + 0x38#64) 8 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ memRegion (sp + 0x40#64) 256 ∗
       memRegion (sp + 0x2a0#64) 8 ∗ memRegion (sp + 0x2ac#64) 1 ∗ memRegion (sp + 0x500#64) 48 ∗
       F_rem ∗ R) := by convert hm2 using 1; sep_ac_rfl
  obtain ⟨d_cap, hm3⟩ := exists_word64_of_memRegion_8 hm3
  have hm4 : m ⊨ memRegion (sp + 0x40#64) 256 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       memRegion (sp + 0x2a0#64) 8 ∗ memRegion (sp + 0x2ac#64) 1 ∗ memRegion (sp + 0x500#64) 48 ∗
       F_rem ∗ R) := by convert hm3 using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_memRegion_256 hm4
    fun d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 hm4 => ?_
  have hm5 : m ⊨ memRegion (sp + 0x2a0#64) 8 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       memRegion (sp + 0x2ac#64) 1 ∗ memRegion (sp + 0x500#64) 48 ∗ F_rem ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨g2a0, hm5⟩ := exists_word64_of_memRegion_8 hm5
  have hm6 : m ⊨ memRegion (sp + 0x2ac#64) 1 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ memRegion (sp + 0x500#64) 48 ∗ F_rem ∗ R) := by
    convert hm5 using 1; sep_ac_rfl
  obtain ⟨g2ac, hm6⟩ := exists_word8_of_memRegion_1 hm6
  have hm7 : m ⊨ memRegion (sp + 0x500#64) 48 ∗
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗ F_rem ∗ R) := by
    convert hm6 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm7⟩ := exists_words6_of_memRegion_48 hm7
  have h500 :
      (((sp + 0x500#64) ↦₆₄ t0) ∗ words5At (sp + 0x500#64 + 8#64) t1 t2 t3 t4 t5) =
      (words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5)) := by
    unfold words5At words4At; simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl
  rw [h500] at hm7
  refine ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, ?_⟩
  dsimp only [F_rem] at hm7; convert hm7 using 1; sep_ac_rfl


namespace ChainLookupFacts

theorem elim_s1_ok_stack_extract {sp : BitVec 64} {R : SepProp} {m : Memory} {P : Prop}
    (hm : m ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗ R)
    (k : ∀ (g20 d_cap g2a0 t0 t1 t2 t3 t4 t5 : BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
       d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 : BitVec 64)
      (g28 : BitVec 32) (g2ac : BitVec 8),
      (m ⊨
        (((sp + 0x20#64) ↦₆₄ g20) ∗
         ((sp + 0x28#64) ↦₃₂ g28) ∗
         ((sp + 0x38#64) ↦₆₄ d_cap) ∗
         words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
           d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
         ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
         ((sp + 0x2ac#64) ↦₈ g2ac) ∗
         words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
         ((sp + 0x520#64) ↦₆₄ t4) ∗
         ((sp + 0x528#64) ↦₆₄ t5)) ∗
        (memRegion sp 0x20 ∗
         memRegion (sp + 0x2c#64) 4 ∗
         memRegion (sp + 0x140#64) 0x50 ∗
         memRegion (sp + 0x298#64) 8 ∗
         memRegion (sp + 0x2a8#64) 4 ∗
         memRegion (sp + 0x2ad#64) 0x253 ∗
         memRegion (sp + 0x530#64) 0x50) ∗ R) → P) : P :=
  let ⟨g20, d_cap, g2a0, t0, t1, t2, t3, t4, t5,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15,
    d16, d17, d18, d19, d20, d21, d22, d23, d24, d25, d26, d27, d28, d29, d30, d31,
    g28, g2ac, hm_stk2⟩ := loadRatchet_ok_stack_extract hm
  k g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
    d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
    d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
    g28 g2ac hm_stk2

end ChainLookupFacts

theorem loadRatchet_ok_stack_recombine (sp cap remA : BitVec 64) (b2ac : BitVec 8)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
     w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 : BitVec 64) :
    (memRegion (sp + 0x140#64) 0x50 ∗
     ((sp + 0x190#64) ↦₆₄ cap) ∗
     words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
       w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
     memRegion (sp + 0x298#64) 8 ∗
     ((sp + 0x2a0#64) ↦₆₄ remA) ∗
     memRegion (sp + 0x2a8#64) 4 ∗
     ((sp + 0x2ac#64) ↦₈ b2ac) ∗
     memRegion (sp + 0x2ad#64) 0x253 ∗
     words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
     ((sp + 0x520#64) ↦₆₄ w4) ∗
     ((sp + 0x528#64) ↦₆₄ w5) ∗
     memRegion (sp + 0x530#64) 0x50) ⊢
    memRegion (sp + 0x140#64) 0x440 := by
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x190#64) cap)
      (sepConj_mono
        (words32At_entails_memRegion (sp + 0x198#64)
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31)
      (sepConj_mono_right
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x2a0#64) remA)
      (sepConj_mono_right
      (sepConj_mono (pointsTo8_entails_memRegion (sp + 0x2ac#64) b2ac)
      (sepConj_mono_right
      (sepConj_mono (words4At_entails_memRegion (sp + 0x500#64) w0 w1 w2 w3)
      (sepConj_mono (pointsTo64_entails_memRegion (sp + 0x520#64) w4)
      (sepConj_mono_left (pointsTo64_entails_memRegion (sp + 0x528#64) w5)))))))))))) ?_
  rw [show sp + 0x530#64 = (sp + 0x528#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x528#64) 8 0x50 (by decide),
      show sp + 0x528#64 = (sp + 0x520#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x520#64) 8 88 (by decide),
      show sp + 0x520#64 = (sp + 0x500#64) + 32#64 by bv_omega,
      ← memRegion_split (sp + 0x500#64) 32 96 (by decide),
      show sp + 0x500#64 = (sp + 0x2ad#64) + BitVec.ofNat 64 0x253 by bv_omega,
      ← memRegion_split (sp + 0x2ad#64) 0x253 128 (by decide),
      show sp + 0x2ad#64 = (sp + 0x2ac#64) + 1#64 by bv_omega,
      ← memRegion_split (sp + 0x2ac#64) 1 723 (by decide),
      show sp + 0x2ac#64 = (sp + 0x2a8#64) + 4#64 by bv_omega,
      ← memRegion_split (sp + 0x2a8#64) 4 724 (by decide),
      show sp + 0x2a8#64 = (sp + 0x2a0#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x2a0#64) 8 728 (by decide),
      show sp + 0x2a0#64 = (sp + 0x298#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x298#64) 8 736 (by decide),
      show sp + 0x298#64 = (sp + 0x198#64) + 256#64 by bv_omega,
      ← memRegion_split (sp + 0x198#64) 256 744 (by decide),
      show sp + 0x198#64 = (sp + 0x190#64) + 8#64 by bv_omega,
      ← memRegion_split (sp + 0x190#64) 8 1000 (by decide),
      show sp + 0x190#64 = (sp + 0x140#64) + BitVec.ofNat 64 0x50 by bv_omega,
      ← memRegion_split (sp + 0x140#64) 0x50 1008 (by decide)]
  exact Entails.refl _

theorem loadRatchet_after_call_ok {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext) (segFindChainPC img) s
      (fun s' => ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗
    memRegion (sp + 0x298#64) 0x2e8 ∗
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨
    trAt A (sp + 0x190#64) trG tr ∗
    (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
     memRegion x.ret 48 ∗
     memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ x.remA) ∗
     memRegion (sp + 0x38#64) 0x158 ∗
     memRegion (sp + 0x298#64) 0x2e8 ∗
     tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A trG tr ∗
      (((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       trBodyAt (sp + 0x198#64) trG tr ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 0x198#64) trG tr ∗
      (trHeapAt A trG tr ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
        H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 0x30 ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8) ∗
      (words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗
       trHeapAt A trG tr ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion x.ret 48 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
        g28 g2ac hm_stk2 => ?_
  unfold tryDecryptCommonHeap at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗
    trHeapAt A trG tr ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗
    memRegion (sp + 0x2c#64) 4 ∗
    memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗
    memRegion (sp + 0x2a8#64) 4 ∗
    memRegion (sp + 0x2ad#64) 0x253 ∗
    memRegion (sp + 0x530#64) 0x50 ∗
    protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗
    signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗
    tapeAfter ctl x.cur x.rest 0 ∗
    logOff img ∗
    stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
    tryDecryptSavedRegs s0.sp s0 ∗
    A.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x20#64) ↦₆₄ g20) ∗
       ((sp + 0x28#64) ↦₃₂ g28) ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗
       ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗
       ((sp + 0x520#64) ↦₆₄ t4) ∗
       ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢
    convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_wp (ext := ext)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    himg hcap hpc (tryDecryptMidMeta.to_wpInv hmeta) hx20 hx22 hx23 hx25
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨b2ac, hPf, hwpInv_f, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hinv_f hmf
  subst hPf
  refine ⟨trG, hpcf, hwpInv_f.to_midMeta hinv_f, hx0_f, hx1_f, hx8_f,
    hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
    hx25_f, hx27_f, hx28_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [trAt_eq_cap_body_heap, show sp + 0x38#64 + 8#64 = sp + 0x40#64 by bv_omega,
      signalMessageAt_eq_counter_rest]
  have hmf_re : sf.mem ⊨
      (words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       memRegion (sp + 0x298#64) 8 ∗
       ((sp + 0x2a0#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x2a8#64) 4 ∗
       ((sp + 0x2ac#64) ↦₈ b2ac) ∗
       memRegion (sp + 0x2ad#64) 0x253 ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗
       ((sp + 0x520#64) ↦₆₄ w4) ∗
       ((sp + 0x528#64) ↦₆₄ w5) ∗
       memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       trHeapAt A trG tr ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x20 ∗
       ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗
       memRegion (sp + 0x2c#64) 4 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗
       signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest 0 ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool ∗ R) := by
    dsimp only [F_ok, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_tr (sp + 0x40#64))
      (sepConj_mono_left
        (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

private abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

theorem loadRatchet_ok_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    S1SpecExt img C A ctl uuidTryParse S ext := by
  intro himg htrFrom x R s0 s hS1 hcode
  have hcall := loadRatchet_call_trFrom_reaches himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAtExt img.base ext) (segFindChainPC img) s
        (fun s' => ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

/-- Segment S1 theorem (`LoadRatchetSpec`). -/
theorem loadRatchet_ok {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    LoadRatchetSpec img C A ctl uuidTryParse S abs :=
  loadRatchet_ok_ext

theorem loadRatchet_after_call_error_x {img : Obj.Image} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64) (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (tryDecryptFnSpec C decFn A ctl uuidTryParse S img) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp_fn C decFn S x e st1 herr
  have hmod1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_fn himg x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract hnpan hm
  have hwp := loadRatchet_err_wp (ext := ext)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta hinv_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speFnAt A (utf8 "decrypt") x.ret e ∗ memRegion sp 1408 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H) ∗
      (memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono
      (Entails.trans (hent_spe x.ret) (speAt_entails_speFnAt A (utf8 "decrypt") x.ret e))
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

/-- Segment S1 theorem (`S1SpecX`). -/
theorem loadRatchet_ok_x {img : Obj.Image} {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    S1SpecX img C decFn A ctl uuidTryParse S ext := by
  intro himg htrFrom x R s0 s hS1 hcode
  have hcall := loadRatchet_call_trFrom_reaches_x himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error_x himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAtExt img.base ext) (segFindChainPC img) s
        (fun s' => ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

/-! ## Relocatable (`[LibsignalPlacement]`) Segment S1 Proofs -/

theorem LoadRatchetStatePlaced.to_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetStatePlaced (blkPl_131).base A ctl x R s0 s) :
    LoadRatchetState_placed A ctl x R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1, h.2.1.2.2.2.2.1,
          h.2.1.2.2.2.2.2.1, h.2.1.2.2.2.2.2.2.1.1, h.2.1.2.2.2.2.2.2.2⟩,
    h.2.2⟩, h.2.1.2.2.2.2.2.2.1.2⟩

theorem FindChainStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {R : SepProp} {s0 s : State}
    (h : FindChainState_placed A ctl x trG tr st1 R s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    FindChainStatePlaced (blkPl_131).base A ctl x trG tr st1 R s0 s :=
  ⟨h.1, ⟨h.2.1.1, h.2.1.2.1, h.2.1.2.2.1, h.2.1.2.2.2.1, h.2.1.2.2.2.2.1,
         h.2.1.2.2.2.2.2.1, ⟨h.2.1.2.2.2.2.2.2.1, hro⟩, h.2.1.2.2.2.2.2.2.2⟩,
   h.2.2⟩

theorem loadRatchet_after_call_error_placed [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_131).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpec C A ctl uuidTryParse S tryDecryptDummyImg) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_placed x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract hnpan hm
  have hwp := loadRatchet_err_wp_placed (H := H)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hcl_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta_placed hcl_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speAt A (utf8 "decrypt") x.ret e ∗ memRegion sp 1408 ∗
    tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
      (memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem loadRatchet_after_call_ok_placed [LibsignalPlacement]
    {A : RustAlloc} {ctl : BitVec 64} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (hpc : s.pc = (blkPl_131).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx21 : s.readReg64 .x21 = x.ss)
    (hx22 : s.readReg64 .x22 = x.msgA)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hx24 : (s.readReg64 .x24).setWidth 8 = msgTypeByte x.msgType)
    (hx25 : s.readReg64 .x25 = x.locA)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.ok tr) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
      (fun s' => ∃ trG, FindChainState_placed A ctl x trG tr st1 R s0 s') := by
  let sp := s0.sp - 1504#64
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (∃∗ senderPad : List (BitVec 8),
      trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
    memRegion x.ret 48 ∗ memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8 ∗
    tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R at hm
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  rw [sepExists_sepConj_left, satisfies_sepExists] at hm_ex
  rcases hm_ex with ⟨senderPad, hm_tr⟩
  let trG : TrGhost := ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩
  change s.mem ⊨ trAt A (sp + 0x190#64) trG tr ∗
    (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
     ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
     memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) at hm_tr
  rw [trAt_eq_cap_body_heap, show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega] at hm_tr
  have hm_heap : s.mem ⊨ trHeapAt A trG tr ∗
      (((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗ trBodyAt (sp + 0x198#64) trG tr ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_tr using 1; sep_ac_rfl
  obtain ⟨hpad, hcap⟩ := trHeapAt_facts hm_heap
  have hm_body : s.mem ⊨ trBodyAt (sp + 0x198#64) trG tr ∗
      (trHeapAt A trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_exists_words32_of_trBodyAt hpad hm_body
    fun w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
        w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 H_tr hm_w hent_tr => ?_
  have hm_stk : s.mem ⊨
      (memRegion sp 0x30 ∗ memRegion (sp + 0x38#64) 0x158 ∗ memRegion (sp + 0x298#64) 0x2e8) ∗
      (words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       H_tr ∗ trHeapAt A trG tr ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine ChainLookupFacts.elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 g28 g2ac hm_stk2 => ?_
  unfold tryDecryptCommonHeap at hm_stk2
  rw [signalMessageAt_eq_counter_rest] at hm_stk2
  let F_ok : SepProp :=
    H_tr ∗ trHeapAt A trG tr ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗
    memRegion sp 0x20 ∗ memRegion (sp + 0x2c#64) 4 ∗ memRegion (sp + 0x140#64) 0x50 ∗
    memRegion (sp + 0x298#64) 8 ∗ memRegion (sp + 0x2a8#64) 4 ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
    memRegion (sp + 0x530#64) 0x50 ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest 0 ∗
    logOff tryDecryptDummyImg ∗ stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
    tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x20#64) ↦₆₄ g20) ∗ ((sp + 0x28#64) ↦₃₂ g28) ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       ((sp + 0x38#64) ↦₆₄ d_cap) ∗
       words32At (sp + 0x40#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
         d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31 ∗
       ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       ((sp + 0x2a0#64) ↦₆₄ g2a0) ∗ ((sp + 0x2ac#64) ↦₈ g2ac) ∗
       words4At (sp + 0x500#64) t0 t1 t2 t3 ∗ ((sp + 0x520#64) ↦₆₄ t4) ∗ ((sp + 0x528#64) ↦₆₄ t5) ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter)) ∗ F_ok := by
    dsimp only [F_ok, sp] at hm_stk2 ⊢; convert hm_stk2 using 1; sep_ac_rfl
  have hwp := loadRatchet_ok_wp_placed (H := H)
    (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
    (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
    (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14) (w15 := w15)
    (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21) (w22 := w22) (w23 := w23)
    (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29) (w30 := w30) (w31 := w31)
    (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
    (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14) (d15 := d15)
    (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21) (d22 := d22) (d23 := d23)
    (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29) (d30 := d30) (d31 := d31)
    (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
    hcap hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx20 hx22 hx23 hx25
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨b2ac, hPf, hwpInv_f, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hcl_f hmf
  subst hPf
  refine ⟨trG, hpcf, hwpInv_f.to_midMeta_placed hcl_f, hx0_f, hx1_f, hx8_f,
    hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
    hx25_f, hx27_f, hx28_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [trAt_eq_cap_body_heap, show sp + 0x38#64 + 8#64 = sp + 0x40#64 by bv_omega,
      signalMessageAt_eq_counter_rest]
  have hmf_re : sf.mem ⊨
      (words32At (sp + 0x40#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗ H_tr) ∗
      (memRegion (sp + 0x140#64) 0x50 ∗ ((sp + 0x190#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       words32At (sp + 0x198#64) w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
         w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 ∗
       memRegion (sp + 0x298#64) 8 ∗ ((sp + 0x2a0#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x2a8#64) 4 ∗
       ((sp + 0x2ac#64) ↦₈ b2ac) ∗ memRegion (sp + 0x2ad#64) 0x253 ∗
       words4At (sp + 0x500#64) w0 w1 w2 w3 ∗ ((sp + 0x520#64) ↦₆₄ w4) ∗ ((sp + 0x528#64) ↦₆₄ w5) ∗
       memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
       trHeapAt A trG tr ∗ memRegion x.ret 48 ∗ memRegion sp 0x20 ∗ ((sp + 0x20#64) ↦₆₄ x.locA) ∗
       ((sp + 0x28#64) ↦₃₂ x.msg.counter) ∗ memRegion (sp + 0x2c#64) 4 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       ((x.msgA + 0x68#64) ↦₃₂ x.msg.counter) ∗ signalMessageNoCounterAt A x.msgG x.msgA x.msg ∗
       tapeAfter ctl x.cur x.rest 0 ∗ logOff tryDecryptDummyImg ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗ tryDecryptSavedRegs s0.sp s0 ∗ A.pool ∗ R) := by
    dsimp only [F_ok, sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_tr (sp + 0x40#64))
      (sepConj_mono_left
        (loadRatchet_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem loadRatchet_placed_ok [LibsignalPlacement]
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base (trFromPlacedSpec A)) :
    S1SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x R s0 s hS1 hcode
  obtain ⟨hS1_pl, hro⟩ := LoadRatchetStatePlaced.to_placed hS1
  have hcall := loadRatchet_call_trFrom_reaches_placed htrFrom x R s0 s hS1_pl hro
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact (reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error_placed hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)).mono_outcome
        fun _ hout => hout
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
        (fun s' => (∃ trG, FindChainState_placed A ctl x trG tr st1 R s0 s') ∧ LibsignalRoLoaded lsmpl s'.mem) := by
      refine reaches_pc_lsro hro (reaches_pc_seq hcall ?_)
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, ⟨trG, hS2⟩, hro'⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, trG, FindChainStatePlaced.of_placed hS2 hro'⟩
    · exact hoom.elim

theorem loadRatchet_after_call_error_x_placed [LibsignalPlacement]
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_131).base + 484#64) (hmeta : tryDecryptMidMeta_placed s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗ memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptFnSpec C decFn A ctl uuidTryParse S tryDecryptDummyImg) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp_fn C decFn S x e st1 herr
  have hmod1 : (x.modelFn C decFn S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.modelFn C decFn S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.modelFn C decFn S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.modelFn C decFn S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_fn_placed x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract hnpan hm
  have hwp := loadRatchet_err_wp_placed (H := H)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hcl_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta_placed hcl_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speFnAt A (utf8 "decrypt") x.ret e ∗ memRegion sp 1408 ∗
    tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
      (memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono
      (Entails.trans (hent_spe x.ret) (speAt_entails_speFnAt A (utf8 "decrypt") x.ret e))
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem loadRatchet_placed_ok_x [LibsignalPlacement]
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base (trFromPlacedSpec A)) :
    S1SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S := by
  intro x R s0 s hS1 hcode
  obtain ⟨hS1_pl, hro⟩ := LoadRatchetStatePlaced.to_placed hS1
  have hcall := loadRatchet_call_trFrom_reaches_placed htrFrom x R s0 s hS1_pl hro
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact (reaches_outcome_steps hsteps_ret
        (loadRatchet_after_call_error_x_placed hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)).mono_outcome
        fun _ hout => hout
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
        (fun s' => (∃ trG, FindChainState_placed A ctl x trG tr st1 R s0 s') ∧ LibsignalRoLoaded lsmpl s'.mem) := by
      refine reaches_pc_lsro hro (reaches_pc_seq hcall ?_)
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, ⟨trG, hS2⟩, hro'⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, trG, FindChainStatePlaced.of_placed hS2 hro'⟩
    · exact hoom.elim

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
