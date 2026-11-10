/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalOk
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tails
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFetch
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem

/-!
# `segSignal` `OTR::encrypt` Error Path (`+0x3a4..+0x3c8` → `+0xc14`)

Routes an `Err p` result of `OTR::encrypt` at `SegSignalRetStateV` (`+0x3a4`) through `+0x3c8` to
the shared protocol-error tail `tailSignalEncryptErr_ok` (`+0xc14`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000

theorem segSignal_apply {m : Memory} {B L L' G : SepProp} (hent : L ⊢ L') (hB : B = L ∗ G)
    (hm : m ⊨ B) : m ⊨ L' ∗ G := by
  subst hB
  exact Satisfies.mono (sepConj_mono_left hent) hm

theorem segSignal_focusR {m : Memory} {B T G F : SepProp} (R : SepProp) (hB : B = T ∗ G)
    (hG : G = R ∗ F) (hm : m ⊨ B) : m ⊨ T ∗ (F ∗ R) := by
  subst hB hG
  rwa [sepConj_comm R F] at hm

theorem segSignal_ofProtocol {p : SignalProtocolError} (hp : p ≠ .panic) :
    (ApiError.ofProtocol p : ApiError AddrVal Unit) = .protocol p := by
  cases p <;> first | rfl | exact absurd rfl hp

theorem segSignal_err_tail_ent (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8))) (k : IdentityKey)
    (pqCap pqPtr : BitVec 64) (ot : OutgoingTripleRatchet (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [w3, w4, w5]) ∗
      (cmScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g (takenRecord sess taken) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr ot ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb18#64) 0x68) ⊢
      dropRecordSlots A sp cmScratch g (takenRecord sess taken) (some (pqCap, pqPtr, ot)) none
        (pollWith sp 0xb00 [w3, w4, w5]) := by
  have hkey : ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ⊢ memRegion (sp + 0x350#64) 0x20 := by
    have h := pointsToBytes_entails_memRegion (sp + 0x350#64) k.publicKey.bytes.toList
    simpa using h
  have hw6 : words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ⊢ memRegion (sp + 0x588#64) 48 :=
    SegFrom.words64At_entails_memRegion [w0, w1, w2, w3, w4, w5] (sp + 0x588#64)
      (by simp only [List.length_cons, List.length_nil]; omega)
  have hcm : memRegion (sp + 0x350#64) 0x119 =
      memRegion (sp + 0x350#64) 0x20 ∗ memRegion (sp + 0x370#64) 0xf8 ∗
        memRegion (sp + 0x468#64) 1 := by
    rw [show (0x119 : Nat) = 0x20 + 0xf9 from rfl,
      mr_cut_add sp 0x350 0x20 0xf9 (by decide),
      show (0xf9 : Nat) = 0xf8 + 1 from rfl,
      mr_cut_add sp (0x350 + 0x20) 0xf8 1 (by decide)]
  have hpoll : pollWith sp 0xb00 [w3, w4, w5] =
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        memRegion (sp + 0x588#64) 48 ∗ memRegion (sp + 0x5b8#64) 64 ∗
        memRegion (sp + 0x5f8#64) 0x508) ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    unfold pollWith
    have h1 : memRegion (sp + 0x46a#64) (0xb00 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
          memRegion (sp + 0x588#64) 48 ∗ memRegion (sp + 0x5b8#64) 64 ∗
          memRegion (sp + 0x5f8#64) 0x508 := by
      rw [show (0xb00 - 0x46a : Nat) = 0x116 + (8 + (48 + (64 + 0x508))) from rfl,
        mr_cut_add sp 0x46a 0x116 _ (by decide),
        mr_cut_add sp (0x46a + 0x116) 8 _ (by decide),
        mr_cut_add sp (0x46a + 0x116 + 8) 48 _ (by decide),
        mr_cut_add sp (0x46a + 0x116 + 8 + 48) 64 _ (by decide)]
    rw [h1]
    rfl
  unfold dropRecordSlots otrSlotAt cmSlotAt
  dsimp only
  rw [hcm, hpoll]
  refine Entails.trans ?_ (Entails.of_eq rfl)
  refine Entails.trans (sepConj_mono_left (sepConj_mono
    (pointsTo64_entails_memRegion _ _) (sepConj_mono_left hw6))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_left (pointsTo64_entails_memRegion _ _))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hkey))))))) ?_
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_left (pointsTo8_entails_memRegion _ _)))))))))) ?_
  exact Entails.of_eq (by ac_rfl)

theorem segSignal_list_len3 {α : Type} (ws : List α) (h : ws.length = 3) :
    ∃ v0 v1 v2, ws = [v0, v1, v2] := by
  rcases ws with _ | ⟨v0, ws⟩; · nomatch h
  rcases ws with _ | ⟨v1, ws⟩; · nomatch h
  rcases ws with _ | ⟨v2, ws⟩; · nomatch h
  rcases ws with _ | ⟨_, _⟩
  · exact ⟨v0, v1, v2, rfl⟩
  · nomatch h

theorem segSignal_pure_front {m : Memory} {φ : Prop} {P G : SepProp} (hm : m ⊨ (⌜φ⌝ ∗ P) ∗ G) :
    φ ∧ (m ⊨ P ∗ G) := by
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  exact hm

/-- From `SegSignalRetStateV` (`+0x3a4`) on `OTR::encrypt = .error p`, stages the error words
and exits via `tailSignalEncryptErr_ok`. -/
theorem segSignal_err_path_pf {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {abs : String → Option (State → State)}
    (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (R0 : SepProp) (s0 s : State)
    (p : SignalProtocolError) (herr : (segSignalRes C S x otr).1 = .error p)
    (hs : SegSignalRetStateV kit st0 ikit ist0 Scope C ctl S encRecord x r sess otr taken k R0 s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R0 s0 s (fun _ => False) := by
  obtain ⟨hcur, hsc, hfrom, hrem, hnone, hnp, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hfl, hsym, hvregs⟩, htr, hx20, hx25, hx26, hx28,
    hpt, hrest, hloc, hnow, hstk, g, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  have hp_pan : p ≠ .panic := by
    rintro rfl
    exact hnp herr
  rw [herr] at hm
  simp only [signalMessageResultAt, errResultAt, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceSub,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨pqCap', pqPtr', hm⟩ := hm
  have hst : speAt A (utf8 "encrypt") (sp + 0x588#64) p ⊢
      ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
        ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗ words64At (sp + 0x588#64) ws ∗ H :=
    speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) (by intro h; cases h)
  have hm1 := segSignal_apply hst (by sep_focus) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists] at hm1
  obtain ⟨ws, H, hm1⟩ := hm1
  obtain ⟨hstg, hm1⟩ := segSignal_pure_front hm1
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := segSignal_list_len6 ws hstg.2.1
  have hsplit : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x508 ∗ memRegion (sp + 0xb00#64) 24 ∗
        memRegion (sp + 0xb18#64) 0x68 := by
    rw [show (0x588 : Nat) = 0x508 + (24 + 0x68) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x508 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x508) 24 _ (by decide)]
  have hm2 := segSignal_apply (Entails.of_eq_explicit hsplit) (by sep_focus) hm1
  have hm2' : s.mem ⊨ memRegion (sp + 0xb00#64) (8 * 3) ∗ _ :=
    segSignal_apply (Entails.refl _) (by sep_focus) hm2
  obtain ⟨vs, hvs, hm3⟩ := SegFrom.memRegion_exists_words64At 3 (sp + 0xb00#64) (by decide) hm2'
  obtain ⟨v0, v1, v2, rfl⟩ := segSignal_list_len3 vs hvs
  have hentry : encEntry img = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName :=
    entryOf_eq_tripleRatchetProgAt env.loads encryptWithStoresName
  have hs_pc' : s.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr encryptWithStoresName + 0x3a4#64 := by
    rw [hs_pc, hentry]
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29, hsp0]
    bv_omega
  have hm4 := segSignal_focusR (T := ((sp + 0x580#64) ↦₆₄ errTag) ∗
      words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗ words64At (sp + 0xb00#64) [v0, v1, v2])
    (encStoreExtra kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm3
  refine SegFrom.SegExit.of_sepWP hm4 (segSignal_step_err hs_pc' hrun hsp hal hx25 hx26 hx29') ?_
  intro s3 Pm3 hL hsteps hs3_pc hs3_run hm5
    ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x20, hs3_x21, hs3_x23, hs3_x25, hs3_x26, hs3_x27, hs3_x28,
      hs3_x29, hs3_vregs, hPm3⟩
  have ⟨hfl3, hsym3⟩ := SegFrom.callInv_steps hfl hsym hsteps hL
  have hs3_al : s3.spAligned = true := SegFrom.spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  have hm6 := Satisfies.mono (sepConj_mono_left hPm3) hm5
  rw [← sepConj_assoc] at hm6
  have hm7 := segSignal_apply (segSignal_err_tail_ent A sp g sess taken k pqCap' pqPtr' (segSignalRes C S x otr).2
    w0 w1 w2 w3 w4 w5) (by sep_focus) hm6
  have hmod := segSignal_model_err (C := C) (S := S) (x := x) hcur hnone hfrom hrem
    (execOk_of_exec_error herr)
  have hdraws := (segSignal_sendState (S := S) (x := x) (c := .newOrUnchanged) hcur hnone hfrom hrem).2
  have hstf : kit.storeFinal st0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = st0 := by
    rw [hmod]; rfl
  have histf : ikit.idFinal ist0 (okAnswers r .newOrUnchanged)
      (x.model C S uuidTryParse (okAnswers r .newOrUnchanged)).2 = ist0 := by
    rw [hmod]; rfl
  refine tailSignalEncryptErr_ok env x R0 s0 s3
    (okAnswers r .newOrUnchanged) (.protocol p)
    w0 w1 w2 w3 w4 w5 H cmScratch (Or.inr rfl) g (takenRecord sess taken)
    (some (pqCap', pqPtr', (segSignalRes C S x otr).2)) ?_ hstg ?_
  · refine ⟨⟨by rw [hmod, segSignal_ofProtocol hp_pan], by rw [hmod]; exact ⟨hsc.2, trivial⟩,
      by rw [hmod]; trivial⟩, ?_⟩
    rw [hs3_tr, htr, hmod, ikit.traceOfWith_load]; rfl
  · refine ⟨?_, ⟨hs3_run, hs3_sp, hal0, hs3_al, hs3_x29.trans hx29, hs3_x19.trans hx19,
      hfl3, hsym3, hs3_vregs.trans hvregs⟩, ⟨hs3_x26.trans hx26, hs3_x28.trans hx28, hs3_x27, hs3_x21, hs3_x23⟩,
      hstk, ?_⟩
    · rw [hs3_pc, hentry]
    · rw [hdraws, hstf, histf]
      dsimp only
      rw [← hsp0]
      exact Eq.mp (congrArg (s3.mem ⊨ ·) (by ac_rfl)) hm7

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
