/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.ExtDefs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtCommon
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtS1Sym
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.SegFront.S1Proof

@[expose] public section

set_option autoImplicit false

/-!
# Contract-Backed (`tripleRatchetProgAtExt`) `S1` Proofs (`s1_ok_ext`, `s1_okT_ext`)
-/

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto Mut SessionState SignalProtocolError TripleRatchet)
open CryptoVerification (libsignalSessionImage)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.LibsignalSessionRepr (msgTypeByte)
open CryptoVerification.LibsignalTripleRatchetRepr
  (vecResultAt decryptDraws errTag protocolAddressAt sessionStateAt signalMessageAt speAt
   utf8 uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet
  (SpqrModel TrGhost TryDecryptGhost logOff trAt trResultAt tripleRatchetProgAtExt)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq
  (speBodyAt speTag tryDecryptMidMeta tryDecryptSavedRegs tryDecryptSubStack)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA
  (decRel_afterTrFrom exists_words5_of_speBodyAt exists_words6_of_memRegion_48
   fromSessionState_error_imp s1_err_stack_recombine s1_ok_stack_recombine
   sepWP_to_reaches_pc_with_midMeta signalMessageAt_eq_counter_rest signalMessageNoCounterAt
   speAt_eq_speTag_speBodyAt trAt_eq_cap_body_heap trBodyAt trHeapAt trHeapAt_facts
   tryDecryptMidMeta.to_wpInv tryDecryptWPInv.to_midMeta words4At words5At words32At)
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.SegA.BS9
  (elim_exists_words32_of_trBodyAt elim_s1_ok_stack_extract)

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtS1Proof

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem s1_after_call_error_epilogue_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    (x.model C S uuidTryParse).1 ≠ .error .panic ∧
    x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom ∧
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.retEpiloguePC img) s
      (fun s1 =>
        tryDecryptMidMeta img s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss x.G.afterTrFrom (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x
            (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R)) := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine ⟨hnpan_mod, hG', ?_⟩
  change s.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (((sp + 0x190#64) ↦₆₄ errTag) ∗
     speAt A (utf8 "decrypt") (sp + 0x190#64 + 8#64) e ∗
     memRegion (sp + 0x190#64 + 56#64) 208) ∗
    memRegion x.ret 48 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗
    memRegion (sp + 0x298#64) 0x2e8 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  rw [show sp + 0x190#64 + 8#64 = sp + 0x198#64 by bv_omega,
      show sp + 0x190#64 + 56#64 = sp + 0x1c8#64 by bv_omega,
      speAt_eq_speTag_speBodyAt hnpan,
      show sp + 0x198#64 + 8#64 = sp + 0x1a0#64 by bv_omega,
      memRegion_split (sp + 0x298#64) 0x268 0x80 (by decide),
      show (sp + 0x298#64) + BitVec.ofNat 64 0x268 = sp + 0x500#64 by bv_omega,
      memRegion_split (sp + 0x500#64) 48 0x50 (by decide),
      show (sp + 0x500#64) + 48#64 = sp + 0x530#64 by bv_omega] at hm
  have hm1 : s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x1a0#64) e ∗
      (memRegion (sp + 0x500#64) 48 ∗
       memRegion x.ret 48 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗
       memRegion (sp + 0x530#64) 0x50 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H, hm2, hent_spe⟩ := exists_words5_of_speBodyAt hnpan hm1
  have hm3 : s.mem ⊨ memRegion (sp + 0x500#64) 48 ∗
      (memRegion x.ret 48 ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       H ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗
       memRegion (sp + 0x530#64) 0x50 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm2 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, t3, t4, t5, hm4⟩ := exists_words6_of_memRegion_48 hm3
  rw [show sp + 0x500#64 + 8#64 = sp + 0x508#64 by bv_omega] at hm4
  have hm5 : s.mem ⊨ memRegion x.ret 48 ∗
      (((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       H ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗
       memRegion (sp + 0x530#64) 0x50 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm4 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hm6⟩ := exists_words6_of_memRegion_48 hm5
  let F_err :=
    H ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    memRegion sp 0x30 ∗
    ((sp + 0x30#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 0x38#64) 0x158 ∗
    memRegion (sp + 0x1c8#64) 208 ∗
    memRegion (sp + 0x298#64) 0x268 ∗
    memRegion (sp + 0x530#64) 0x50 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hm_pre : s.mem ⊨
      (((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       ((sp + 0x500#64) ↦₆₄ t0) ∗
       words5At (sp + 0x508#64) t1 t2 t3 t4 t5 ∗
       (x.ret ↦₆₄ r0) ∗
       words5At (x.ret + 8#64) r1 r2 r3 r4 r5) ∗ F_err := by
    dsimp only [F_err]
    convert hm6 using 1; sep_ac_rfl
  have hwp :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_err_wp_ext (ext := ext)
      (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      himg hpc (tryDecryptMidMeta.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta hinv_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speAt A (utf8 "decrypt") x.ret e ∗
    memRegion sp 1408 ∗
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H) ∗
      (memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗
       ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗
       memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗
       ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗
       memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [F_err, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (s1_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_error_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s := by
  obtain ⟨hnpan, hG', hreach⟩ :=
    s1_after_call_error_epilogue_ext (C := C) (S := S) (ext := ext)
      himg herr hpc hmeta hx19 hx20 hx23 hm
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.reaches_epilogue_to_outcome_ext
    himg x x.G.afterTrFrom R s0 s hnpan hG' hreach

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_error_tight_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
    (hmeta : tryDecryptMidMeta img s0 s)
    (hx19 : s.readReg64 .x19 = x.ret)
    (hx20 : s.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64)
    (hx23 : s.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64)
    (hm : s.mem ⊨
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
      trResultAt A ((s0.sp - 1504#64) + 0x190#64) x.G (.error e) ∗
      memRegion x.ret 48 ∗
      memRegion (s0.sp - 1504#64) 0x30 ∗
      (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
      memRegion ((s0.sp - 1504#64) + 0x38#64) 0x158 ∗
      memRegion ((s0.sp - 1504#64) + 0x298#64) 0x2e8 ∗
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  obtain ⟨hnpan, hG', hreach⟩ :=
    s1_after_call_error_epilogue_ext (C := C) (S := S) (ext := ext)
      himg herr hpc hmeta hx19 hx20 hx23 hm
  exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.reaches_epilogue_to_outcome_tight_ext
    himg x x.G.afterTrFrom R s0 s hnpan hG' hreach

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_ok_ext
    {img : Obj.Image} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (hpc : s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptEntry img + 0x1e4#64)
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
      CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_pc (tripleRatchetProgAtExt img.base ext)
      (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img) s
      (fun s' => ∃ trG, CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s') := by
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
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R at hm
  have hm_ex : s.mem ⊨
      (∃∗ senderPad : List (BitVec 8),
        trAt A (sp + 0x190#64) ⟨⟨x.G.chainsCap, x.G.chainsPtr, x.G.chains, senderPad⟩, x.G.pq⟩ tr) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       memRegion x.ret 48 ∗
       memRegion sp 0x30 ∗
       ((sp + 0x30#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 0x38#64) 0x158 ∗
       memRegion (sp + 0x298#64) 0x2e8 ∗
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
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
     CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) at hm_tr
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_heap using 1; sep_ac_rfl
  refine elim_exists_words32_of_trBodyAt hpad hm_body
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
       CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    convert hm_w using 1; sep_ac_rfl
  refine elim_s1_ok_stack_extract hm_stk
    fun g20 d_cap g2a0 t0 t1 t2 t3 t4 t5
        d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15
        d16 d17 d18 d19 d20 d21 d22 d23 d24 d25 d26 d27 d28 d29 d30 d31
        g28 g2ac hm_stk2 => ?_
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap at hm_stk2
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
    CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
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
  have hwp :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_wp_ext (ext := ext)
      (cap := trG.ratchet.chainsCap) (locA := x.locA) (remA := x.remA) (msgA := x.msgA)
      (g20 := g20) (d_cap := d_cap) (g2a0 := g2a0)
      (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4) (w5 := w5) (w6 := w6) (w7 := w7)
      (w8 := w8) (w9 := w9) (w10 := w10) (w11 := w11) (w12 := w12) (w13 := w13) (w14 := w14)
      (w15 := w15)
      (w16 := w16) (w17 := w17) (w18 := w18) (w19 := w19) (w20 := w20) (w21 := w21)
      (w22 := w22) (w23 := w23)
      (w24 := w24) (w25 := w25) (w26 := w26) (w27 := w27) (w28 := w28) (w29 := w29)
      (w30 := w30) (w31 := w31)
      (d0 := d0) (d1 := d1) (d2 := d2) (d3 := d3) (d4 := d4) (d5 := d5) (d6 := d6) (d7 := d7)
      (d8 := d8) (d9 := d9) (d10 := d10) (d11 := d11) (d12 := d12) (d13 := d13) (d14 := d14)
      (d15 := d15)
      (d16 := d16) (d17 := d17) (d18 := d18) (d19 := d19) (d20 := d20) (d21 := d21)
      (d22 := d22) (d23 := d23)
      (d24 := d24) (d25 := d25) (d26 := d26) (d27 := d27) (d28 := d28) (d29 := d29)
      (d30 := d30) (d31 := d31)
      (counter := x.msg.counter) (g28 := g28) (g2ac := g2ac)
      himg hcap hpc (tryDecryptMidMeta.to_wpInv hmeta) hx20 hx22 hx23 hx25
  refine sepWP_to_reaches_pc_with_midMeta hmeta hwp hm_pre ?_
  intro sf Pf hpcf ⟨b2ac, hPf, hwpInv_f, hx0_f, hx1_f, hx8_f, hx19_f, hx20_f, hx21_f, hx22_f,
      hx23_f, hx24_f, hx25_f, hx27_f, hx28_f⟩ hinv_f hmf
  subst hPf
  refine ⟨trG, hpcf, hwpInv_f.to_midMeta hinv_f, hx0_f, hx1_f, hx8_f,
    hx19_f.trans hx19, hx20_f.trans hx20, hx21_f.trans hx21, hx22_f.trans hx22, hx23_f.trans hx23,
    by change (sf.readReg64 (Reg.gpr 24#5)).setWidth 8 = _; rw [hx24_f]; exact hx24,
    hx25_f, hx27_f, hx28_f, ?_⟩
  unfold CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.tryDecryptCommonHeap
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
       CryptoVerification.SignalSession.Coins.coinsAfter img.base x.cur x.rest 0 ∗
       logOff img ∗
       stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗
       A.pool ∗ R) := by
    dsimp only [F_ok, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_tr (sp + 0x40#64))
      (sepConj_mono_left
        (s1_ok_stack_recombine sp trG.ratchet.chainsCap x.remA b2ac
          w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15
          w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_ok_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1Spec_ext
      img C A ctl uuidTryParse S ext := by
  intro himg _hC _hMem htrFrom x R s0 s hS1 hcode
  have hcall :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_call_trFrom_reaches_ext
      himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret,
        _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact reaches_outcome_steps hsteps_ret
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_error_ext
          himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach :
        reaches_pc (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img) s
          (fun s' => ∃ trG,
            CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret,
          hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_ok_ext
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_okT_ext
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)} :
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S1SpecTight_ext
      img C A ctl uuidTryParse S ext := by
  intro himg _hC _hMem htrFrom x R s0 s hS1 hcode
  have hcall :=
    CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_call_trFrom_reaches_ext
      himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret,
        _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact reaches_outcome_steps hsteps_ret
        (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_error_tight_ext
          himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach :
        reaches_pc (tripleRatchetProgAtExt img.base ext)
          (CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.segS2PC img) s
          (fun s' => ∃ trG,
            CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.S2State A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret,
          hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.SegA.s1_after_call_ok_ext
        himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.Trap.SegFront.ExtS1Proof
