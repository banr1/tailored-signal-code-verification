/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTight
public import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244Placed
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof

/-!
# Tight-Panic Segment S1 & `ErrTail` Theorems

Proves `loadRatchet_okT`, `errTail_okT`, and their relocatable `[LibsignalPlacement]` counterparts
(`loadRatchet_placed_okT`, `errTail_placed_okT`), discharging `LoadRatchetSpecTight` and
`ErrTailSpecTight` (`OnPanicTight`).
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

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace P3kR1bc

theorem reaches_epilogue_to_outcome_tight {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hreach : reaches_pc (tripleRatchetProgAtExt img.base ext) (retEpiloguePC img) s
      (fun s1 =>
        tryDecryptMidMeta img s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap A ctl img x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  have hentry := tryDecryptEntry_eq_fnAddr (ext := ext) himg
  have hcomb : reaches_pc (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (fun sf =>
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).post x s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    intro s1 hpc1 _ ⟨⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, _, hvregs1⟩, hm1⟩
    dsimp only [retEpiloguePC] at hpc1
    rw [hentry] at hpc1
    unfold tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
         vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ A.pool ∗ R) := by
      convert hm1 using 1; ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (tryDecrypt_epilogue_394_wp s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    simp only [tryDecryptSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
        (vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff img ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
      convert hm2 using 1; ac_rfl
    have hent :
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ⊢
          ⌜(x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) :=
      Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.trans (Entails.pure_right hG' (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) G'))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

theorem loadRatchet_after_call_error_tight {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {ext : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (himg : Obj.Loads libsignalSessionImage img)
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = tryDecryptEntry img + 0x1e4#64)
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
      tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) :
    reaches_outcome (tripleRatchetProgAtExt img.base ext)
      (tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_tight himg x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
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
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
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
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
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
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
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
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
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
  change sf.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    speAt A (utf8 "decrypt") x.ret e ∗
    memRegion sp 1408 ∗
    tryDecryptCommonHeap A ctl img x 0 s0 ∗ R
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
       tryDecryptCommonHeap A ctl img x 0 s0 ∗ R) := by
    dsimp only [F_err, sp] at hmf ⊢
    convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢
  convert hmf2 using 1; sep_ac_rfl

abbrev reaches_outcome_steps := @Arm64.reaches_outcome_steps

theorem errTail_ok_tight_ext {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : Stage2Contracts img.base C A ctl uuidTryParse S ext)
    (hdrop : DropChainOkExt img.base A ext) :
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S uuidTryParse).1 = .error e →
      (x.model C S uuidTryParse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAtExt img.base ext)
        (tryDecryptSpecTight C A ctl uuidTryParse S img) x R s0 s := by
  intro x trG tr st1 e R s0 s he hmod1 hmod2 herr
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta.to_wpInv hmeta
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion x.ret 48 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 =
      memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide,
        memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗
         (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl img x draws s0 ∗ R) := by
    rw [h140_split] at hmem3
    dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp :
      SepWP (tripleRatchetProgAtExt img.base ext) (retEpiloguePC img) s
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack)
        (fun sf P =>
          P = (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
               ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
               ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
               ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
               ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
               ((sp + 0x140#64) ↦₆₄ w0) ∗
               ((sp + 0x148#64) ↦₆₄ w1) ∗
               ((sp + 0x150#64) ↦₆₄ w2) ∗
               words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
               (x.ret ↦₆₄ speTag e) ∗
                words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
                A.pool ∗ stackAt sp dropChainStack) ∧
           tryDecryptWPInv s0 sf) := by
    have hcopy := errTail_copy_spe_wp (img := img) (ext := ext)
      (chainsPtr := trG.ratchet.chainsPtr) (chainsLen := BitVec.ofNat 64 cs.length)
      (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
      (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
      (t0 := t0) (t1 := t1) (t2 := t2)
      himg hpc hmeta_wp hx19 hx20 hx26
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
            A.pool ∗ stackAt sp dropChainStack)
      hcopy ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s1 P1 ⟨hP1, hmeta1, hx20_1, hx21_1⟩ hpc1
    subst hP1
    have hcs_lt' : cs.length * 104 < 2 ^ 63 :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right 104 hcs_le) hcs_lt
    have hdrop_cs := errTail_drop_chains_wp (img := img) (A := A) (ext := ext)
      himg hdrop hcs_lt' hpc1 hmeta1 hx20_1 hx21_1
    refine SepWP.bind_framed
      (F := ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdrop_cs ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro s2 P2 ⟨hP2, hmeta2, hx20_2⟩ hpc2
    subst hP2
    have hre_cs :
        (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗ stackAt sp dropChainStack) ∗
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
           ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
           ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
           ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
           ((sp + 0x140#64) ↦₆₄ w0) ∗
           ((sp + 0x148#64) ↦₆₄ w1) ∗
           ((sp + 0x150#64) ↦₆₄ w2) ∗
           words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
           (x.ret ↦₆₄ speTag e) ∗
           words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
           (if trG.pq.cap = 0#64 then emp
            else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
              memRegion trG.pq.ptr trG.pq.cap.toNat)))) ⊢
        ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          (if trG.ratchet.chainsCap = 0#64 then emp
           else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
             memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
          A.pool ∗ stackAt sp allocHookStack) ∗
         (memRegion (sp - 4144#64) 48 ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          (x.ret ↦₆₄ speTag e) ∗
          words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
          (if trG.pq.cap = 0#64 then emp
           else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
             memRegion trG.pq.ptr trG.pq.cap.toNat))) := by
      rw [stackAt_dropChainStack_sub sp]
      have hcomm1 :
          (((memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗ A.pool ∗
              (stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48)) ∗
            (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
             ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
             ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
             ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
             ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
             ((sp + 0x140#64) ↦₆₄ w0) ∗
             ((sp + 0x148#64) ↦₆₄ w1) ∗
             ((sp + 0x150#64) ↦₆₄ w2) ∗
             words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
             (x.ret ↦₆₄ speTag e) ∗
             words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
             (if trG.ratchet.chainsCap = 0#64 then emp
              else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
                memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                  ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
             (if trG.pq.cap = 0#64 then emp
              else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
                memRegion trG.pq.ptr trG.pq.cap.toNat)))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (memRegion trG.ratchet.chainsPtr (cs.length * 104) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
                 ((trG.ratchet.chainsCap.toNat - cs.length) * 104))) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      have hcomm2 :
          ((((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            (if trG.ratchet.chainsCap = 0#64 then emp
             else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
               memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
            A.pool ∗ stackAt sp allocHookStack) ∗
           (memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) =
          (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
           (if trG.ratchet.chainsCap = 0#64 then emp
            else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
              memRegion trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104)) ∗
           (A.pool ∗ stackAt sp allocHookStack ∗ memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))) := by dsimp only [sp]; sep_ac_rfl
      rw [hcomm1, hcomm2]
      exact sepConj_mono_right (sepConj_mono_left (chains_recombine_entails hcs_le hcs_lt))
    refine SepWP.mono_pre (by dsimp only [sp] at hre_cs ⊢; exact hre_cs) ?_
    have hdealloc_cs := errTail_dealloc_chains_wp (img := img) (A := A) (ext := ext)
      himg hA.toAllocContracts hcs_lt hpc2 hmeta2 hx20_2
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
            ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗
            (if trG.pq.cap = 0#64 then emp
             else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
               memRegion trG.pq.ptr trG.pq.cap.toNat))
      hdealloc_cs ?_ ?_
    · dsimp only [sp]
    intro s3 P3 ⟨hP3, hmeta3⟩ hpc3
    subst hP3
    have hdealloc_pq := errTail_dealloc_pq_wp (img := img) (A := A) (ext := ext)
      (pqCap := trG.pq.cap) (pqPtr := trG.pq.ptr)
      himg hA.toAllocContracts hpc3 hmeta3
    refine SepWP.bind_framed
      (F := memRegion (sp - 4144#64) 48 ∗
            ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
            ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
            ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
            ((sp + 0x140#64) ↦₆₄ w0) ∗
            ((sp + 0x148#64) ↦₆₄ w1) ∗
            ((sp + 0x150#64) ↦₆₄ w2) ∗
            words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
            (x.ret ↦₆₄ speTag e) ∗
            words5At (x.ret + 8#64) w0 w1 w2 w3 w4)
      hdealloc_pq ?_ ?_
    · dsimp only [sp]; sep_ac_rfl
    intro sf Pf ⟨hPf, hmeta_f⟩ hpcf
    subst hPf
    refine SepWP.done hpcf hmeta_f.1 ⟨?_, hmeta_f⟩
    rw [stackAt_dropChainStack_sub sp]
    dsimp only [sp]; sep_ac_rfl
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
         ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
         ((sp + 0x140#64) ↦₆₄ t0) ∗
         ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
         (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104))
              ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗
            memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗
         H_spe ∗
         memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗
         memRegion (sp + 0xf8#64) 0x48 ∗
         memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest draws ∗
         logOff img ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]
    exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]
    exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight himg x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩
  subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]
    exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗
          ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
          ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗
          ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗
          memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗
          ((sp + 0x148#64) ↦₆₄ w1) ∗
          ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗
          words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗
          tapeAfter ctl x.cur x.rest draws ∗
          logOff img ∗
          (stackAt sp dropChainStack ∗
           memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗
          A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right
      (sepConj_mono hdec_ent
      (sepConj_mono_left
        (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
          (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4))))
    hmem_f_re

end P3kR1bc

/-- Segment S1 theorem with the tight panic condition (`LoadRatchetSpecTight`). -/
theorem loadRatchet_okT {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    LoadRatchetSpecTight img C A ctl uuidTryParse S abs := by
  intro himg htrFrom x R s0 s hS1 hcode
  have hcall := loadRatchet_call_trFrom_reaches himg htrFrom x R s0 s hS1
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact P3kR1bc.reaches_outcome_steps hsteps_ret
        (P3kR1bc.loadRatchet_after_call_error_tight himg hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc (tripleRatchetProgAt img.base C ctl abs) (segFindChainPC img) s
        (fun s' => ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok himg hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, hS2⟩
    · exact hoom.elim

/-- ErrTail theorem with the tight panic condition (`ErrTailSpecTight`). -/
theorem errTail_okT {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)} :
    ErrTailSpecTight img C A ctl uuidTryParse S abs :=
  fun himg hH hdrop =>
    P3kR1bc.errTail_ok_tight_ext himg
      (Stage2Contracts.of_tripleRatchetProgAt img.base C A ctl S abs hH) hdrop

/-! ## Relocatable `[LibsignalPlacement]` Tight S1 / ErrTail Theorems (Block `130`) -/

namespace P3kR1bc

theorem reaches_epilogue_to_outcome_tight_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (x : TryDecryptGhost) (G' : SessionGhost) (R : SepProp) (s0 s : State)
    (hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic)
    (hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G')
    (hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) retEpiloguePC_placed s
      (fun s1 =>
        tryDecryptMidMeta_placed s0 s1 ∧
        (s1.mem ⊨
          sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
          vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
          memRegion (s0.sp - 1504#64) 1408 ∗
          tryDecryptCommonHeap A ctl tryDecryptDummyImg x (decryptDraws C x.st x.msg.senderRatchetKey x.rest) s0 ∗ R))) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecTightPlaced C A ctl uuidTryParse S) x R s0 s := by
  have hcomb : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) (s0.readReg64 .x30) s
      (fun sf =>
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
        (sf.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S tryDecryptDummyImg).post x s0 sf ∗ R)) := by
    refine reaches_pc_seq hreach ?_
    intro s1 hpc1 _ ⟨⟨hrun1, hsp1, hs0_align, hsp_align1, _, htrace1, _, hvregs1⟩, hm1⟩
    dsimp only [retEpiloguePC_placed, tryDecryptEntry_placed] at hpc1
    unfold tryDecryptCommonHeap at hm1
    have hm1_re : s1.mem ⊨
        (stackAt (s0.sp - 1504#64) tryDecryptSubStack ∗
          memRegion (s0.sp - 1504#64) 1408 ∗ tryDecryptSavedRegs s0.sp s0) ∗
        (sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
         vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ A.pool ∗ R) := by
      convert hm1 using 1; ac_rfl
    refine reaches_pc_mono
      (sepWP_to_reaches_pc
        (tryDecrypt_epilogue_394_wp_placed s0 s1 hpc1 hrun1 hsp1 hs0_align hsp_align1 htrace1 hvregs1) hm1_re) ?_
    intro sf _ _ ⟨P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩
    refine ⟨hsp_sf, hcc_sf, ?_⟩
    have hm2 := Satisfies.mono (sepConj_mono_left hP_f) hm_sf
    simp only [tryDecryptSpec, Spec.inImage]
    have hm3 : sf.mem ⊨
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ∗
        (vecResultAt A x.ret (x.model C S uuidTryParse).1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗
         tapeAfter ctl x.cur x.rest (decryptDraws C x.st x.msg.senderRatchetKey x.rest) ∗
         logOff tryDecryptDummyImg ∗ stackAt s0.sp rootStack ∗ A.pool ∗ R) := by
      convert hm2 using 1; ac_rfl
    have hent :
        sessionStateAt A x.ss G' (x.model C S uuidTryParse).2 ⊢
          ⌜(x.model C S uuidTryParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
            (∃∗ G'' : SessionGhost, ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) :=
      Entails.pure_right ⟨hnpan, htrace_sf⟩
        (Entails.trans (Entails.pure_right hG' (Entails.refl _))
          (Entails.sepExists_intro
            (P := fun G'' => ⌜x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool G''⌝ ∗
              sessionStateAt A x.ss G'' (x.model C S uuidTryParse).2) G'))
    have hm4 := Satisfies.mono (sepConj_mono_left hent) hm3
    convert hm4 using 1; ac_rfl
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, ⟨hpc_sf, hrun_sf, hsp_sf, hcc_sf, hpost_sf⟩ | ⟨_, hfalse⟩⟩ := hcomb hL
  · exact reaches_outcome_steps hsteps
      (reaches_outcome.of_outcome (Or.inl ⟨⟨hpc_sf, hsp_sf, hrun_sf⟩, ⟨hsp_sf, hcc_sf⟩, hpost_sf⟩))
  · exact hfalse.elim

theorem loadRatchet_after_call_error_tight_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    {x : TryDecryptGhost} {e : SignalProtocolError} {st1 : SessionState (List (BitVec 8))}
    {R : SepProp} {s0 s : State}
    (herr : Mut.exec TripleRatchet.fromSessionState x.st = (.error e, st1))
    (hpc : s.pc = (blkPl_131).base + 484#64)
    (hmeta : tryDecryptMidMeta_placed s0 s)
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
      (tryDecryptSpecTightPlaced C A ctl uuidTryParse S) x R s0 s := by
  let sp := s0.sp - 1504#64
  obtain ⟨_, hnpan, hdraws, hmodel⟩ := fromSessionState_error_imp C S x e st1 herr
  have hmod1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
  have hmod2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
  have hnpan_mod : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; intro h; injection h with h'; exact hnpan h'
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  refine reaches_epilogue_to_outcome_tight_placed x x.G.afterTrFrom R s0 s hnpan_mod hG' ?_
  obtain ⟨w0, w1, w2, w3, w4, t0, t1, t2, t3, t4, t5, r0, r1, r2, r3, r4, r5, H_spe, hent_spe, hm_pre⟩ :=
    loadRatchet_err_pre_extract hnpan hm
  have hwp := loadRatchet_err_wp_placed (H := H)
    (ret := x.ret) (tag := speTag e) (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (t0 := t0) (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    hpc (tryDecryptMidMeta_placed.to_wpInv hmeta) hx19 hx20 hx23
  refine sepWP_to_reaches_pc_with_midMeta_placed hmeta hwp hm_pre ?_
  intro sf Pf _ ⟨hPf, hwpInv_f⟩ hinv_f hmf
  subst hPf
  refine ⟨hwpInv_f.to_midMeta_placed hinv_f, ?_⟩
  rw [hmod1, hmod2, hdraws]
  change sf.mem ⊨
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ speAt A (utf8 "decrypt") x.ret e ∗
    memRegion sp 1408 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R
  have hmf_re : sf.mem ⊨
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
      (memRegion sp 0x30 ∗ ((sp + 0x30#64) ↦₆₄ x.remA) ∗ memRegion (sp + 0x38#64) 0x158 ∗
       ((sp + 0x190#64) ↦₆₄ errTag) ∗ ((sp + 0x198#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x1a0#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x1c8#64) 208 ∗
       memRegion (sp + 0x298#64) 0x268 ∗ ((sp + 0x500#64) ↦₆₄ speTag e) ∗
       words5At (sp + 0x508#64) w0 w1 w2 w3 w4 ∗ memRegion (sp + 0x530#64) 0x50) ∗
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
       tryDecryptCommonHeap A ctl tryDecryptDummyImg x 0 s0 ∗ R) := by
    dsimp only [sp] at hmf ⊢; convert hmf using 1; sep_ac_rfl
  have hmf2 := Satisfies.mono
    (sepConj_mono (hent_spe x.ret)
      (sepConj_mono_left (loadRatchet_err_stack_recombine sp x.remA (speTag e) w0 w1 w2 w3 w4))) hmf_re
  dsimp only [sp] at hmf2 ⊢; convert hmf2 using 1; sep_ac_rfl

theorem errTail_ok_tight_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A))
    (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State)
    (he : e ≠ .panic)
    (hmod1 : (x.model C S uuidTryParse).1 = .error e)
    (hmod2 : (x.model C S uuidTryParse).2 = st1)
    (herr : ErrTailState_placed A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s) :
    reaches_outcome ((blkPC_131).rebase (blkPl_131).base H)
      (tryDecryptSpecTightPlaced C A ctl uuidTryParse S) x R s0 s := by
  rcases herr with ⟨hpc, hmeta, hx19, hx20, hx26, hmem⟩
  have hmeta_wp : tryDecryptWPInv s0 s := tryDecryptMidMeta_placed.to_wpInv hmeta
  have hcl : LibsignalCodeLoaded lsmpl s.mem := hmeta.2.2.2.2.2.2.1
  let sp := s0.sp - 1504#64
  set draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
  set cs := trG.ratchet.chains.zip tr.ratchet.receiverChains
  have hmem_tr :
      s.mem ⊨ trAt A (sp + 0x38#64) trG tr ∗
        (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp]; convert hmem using 1; sep_ac_rfl
  obtain ⟨hcs_le, hcs_lt, _, _, _, _, hmem1⟩ := trAt_expose_errTail hmem_tr
  have hmem_spe :
      s.mem ⊨ speBodyAt A (utf8 "decrypt") (sp + 0x168#64) e ∗
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion x.ret 48 ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x140#64) 0x28 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem1 ⊢; convert hmem1 using 1; sep_ac_rfl
  obtain ⟨w0, w1, w2, w3, w4, H_spe, hmem2, hspe_ent⟩ := exists_words5_of_speBodyAt he hmem_spe
  have hmem_ret :
      s.mem ⊨ memRegion x.ret 48 ∗
        (words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x140#64) 0x28 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    dsimp only [sp] at hmem2 ⊢; convert hmem2 using 1; sep_ac_rfl
  obtain ⟨r0, r1, r2, r3, r4, r5, hmem3⟩ := exists_words6_of_memRegion_48 hmem_ret
  have h140_split :
      memRegion (sp + 0x140#64) 0x28 = memRegion (sp + 0x140#64) 24 ∗ memRegion (sp + 0x158#64) 16 := by
    rw [show (0x28 : Nat) = 24 + 16 by decide, memRegion_split (sp + 0x140#64) 24 16 (by decide),
        show (sp + 0x140#64) + 24#64 = sp + 0x158#64 by simp only [BitVec.add_assoc, BitVec.reduceAdd]]
  have hmem_t :
      s.mem ⊨ memRegion (sp + 0x140#64) 24 ∗
        (memRegion (sp + 0x158#64) 16 ∗ (x.ret ↦₆₄ r0) ∗ words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗
         words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ H_spe ∗
         ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ memRegion (sp + 0x50#64) 0x98 ∗
         ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗ ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
         arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ memRegion sp 0x38 ∗ memRegion (sp + 0x190#64) 0x3f0 ∗
         tryDecryptCommonHeap A ctl tryDecryptDummyImg x draws s0 ∗ R) := by
    rw [h140_split] at hmem3; dsimp only [sp] at hmem3 ⊢; convert hmem3 using 1; sep_ac_rfl
  obtain ⟨t0, t1, t2, hmem4⟩ := exists_words3_of_memRegion_24 hmem_t
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmem4
  have hwp := errTail_all_steps_wp_placed (A := A) (H := H)
    (w0 := w0) (w1 := w1) (w2 := w2) (w3 := w3) (w4 := w4)
    (r0 := r0) (r1 := r1) (r2 := r2) (r3 := r3) (r4 := r4) (r5 := r5)
    (t0 := t0) (t1 := t1) (t2 := t2)
    hdealloc hcs_le hcs_lt hpc hmeta_wp hcl hx19 hx20 hx26
  unfold tryDecryptCommonHeap at hmem4
  rw [stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)] at hmem4
  have hmem_start :
      s.mem ⊨
        (((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗ ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗
         ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
         ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ ((sp + 0x140#64) ↦₆₄ t0) ∗ ((sp + 0x148#64) ↦₆₄ t1) ∗
         ((sp + 0x150#64) ↦₆₄ t2) ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗ (x.ret ↦₆₄ r0) ∗
         words5At (x.ret + 8#64) r1 r2 r3 r4 r5 ∗ arrayAt (chainAt A) 104 trG.ratchet.chainsPtr cs ∗
         (if trG.ratchet.chainsCap = 0#64 then emp
          else A.live trG.ratchet.chainsPtr (trG.ratchet.chainsCap.toNat * 104) 8 ∗
            memRegion (trG.ratchet.chainsPtr + BitVec.ofNat 64 (cs.length * 104)) ((trG.ratchet.chainsCap.toNat - cs.length) * 104)) ∗
         (if trG.pq.cap = 0#64 then emp
          else A.live trG.pq.ptr trG.pq.cap.toNat 1 ∗ memRegion trG.pq.ptr trG.pq.cap.toNat) ∗
         A.pool ∗ stackAt sp dropChainStack) ∗
        (memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack) ∗ H_spe ∗ memRegion sp 0x38 ∗
         memRegion (sp + 0x50#64) 0x98 ∗ memRegion (sp + 0xf8#64) 0x48 ∗ memRegion (sp + 0x158#64) 16 ∗
         memRegion (sp + 0x190#64) 0x3f0 ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
         signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
         tryDecryptSavedRegs s0.sp s0 ∗ R) := by
    dsimp only [sp] at hmem4 ⊢; convert hmem4 using 1; sep_ac_rfl
  have hnpan : (x.model C S uuidTryParse).1 ≠ .error .panic := by
    rw [hmod1]; exact fun h => he (Except.error.inj h)
  have hG' : x.G.AfterTryDecrypt (x.model C S uuidTryParse).1.toBool x.G.afterTrFrom := by
    rw [hmod1]; exact decRel_afterTrFrom x.G
  apply reaches_epilogue_to_outcome_tight_placed x x.G.afterTrFrom R s0 s hnpan hG'
  refine reaches_pc_mono (sepWP_to_reaches_pc_midMeta_placed hmeta hwp hmem_start) ?_
  intro sf _ _ ⟨Pf, hm_sf, hPf, hmeta_f⟩; subst hPf
  refine ⟨hmeta_f, ?_⟩
  unfold tryDecryptCommonHeap
  rw [hmod2, stackAt_tryDecryptSubStack_sub s0.sp dropChainStack (by decide)]
  have hdec_ent :
      ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ⊢
      vecResultAt A x.ret (x.model C S uuidTryParse).1 := by
    rw [hmod1]; exact hspe_ent x.ret
  have hmem_f_re :
      sf.mem ⊨
        sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         ((x.ret ↦₆₄ speTag e) ∗ words5At (x.ret + 8#64) w0 w1 w2 w3 w4 ∗ H_spe) ∗
         (memRegion sp 0x38 ∗ ((sp + 0x38#64) ↦₆₄ trG.ratchet.chainsCap) ∗
          ((sp + 0x40#64) ↦₆₄ trG.ratchet.chainsPtr) ∗ ((sp + 0x48#64) ↦₆₄ BitVec.ofNat 64 cs.length) ∗
          memRegion (sp + 0x50#64) 0x98 ∗ ((sp + 0xe8#64) ↦₆₄ trG.pq.cap) ∗
          ((sp + 0xf0#64) ↦₆₄ trG.pq.ptr) ∗ memRegion (sp + 0xf8#64) 0x48 ∗
          ((sp + 0x140#64) ↦₆₄ w0) ∗ ((sp + 0x148#64) ↦₆₄ w1) ∗ ((sp + 0x150#64) ↦₆₄ w2) ∗
          memRegion (sp + 0x158#64) 16 ∗ words5At (sp + 0x168#64) w0 w1 w2 w3 w4 ∗
          memRegion (sp + 0x190#64) 0x3f0) ∗
         (protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗ logOff tryDecryptDummyImg ∗
          (stackAt sp dropChainStack ∗ memRegion (s0.sp - 262144#64) (tryDecryptSubStack - dropChainStack)) ∗
          tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ R := by
    dsimp only [sp] at hm_sf ⊢; convert hm_sf using 1; sep_ac_rfl
  exact Satisfies.mono
    (sepConj_mono_right (sepConj_mono hdec_ent (sepConj_mono_left
      (errTail_stack_recombine sp trG.ratchet.chainsCap trG.ratchet.chainsPtr
        (BitVec.ofNat 64 cs.length) trG.pq.cap trG.pq.ptr w0 w1 w2 w3 w4)))) hmem_f_re

end P3kR1bc

/-- Relocatable `[LibsignalPlacement]` Segment S1 theorem with tight panic (`S1SeamTightPlaced`). -/
theorem loadRatchet_placed_okT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (htrFrom : subroutine_ok ((blkPC_57).rebase (blkPl_57).base H) (blkPl_57).base
      (trFromPlacedSpec A)) :
    S1SeamTightPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x R s0 s hS1 hcode
  obtain ⟨hS1_pl, hro⟩ := LoadRatchetStatePlaced.to_placed hS1
  have hcall := loadRatchet_call_trFrom_reaches_placed htrFrom x R s0 s hS1_pl hro
  dsimp only at hcall
  rcases hres : Mut.exec TripleRatchet.fromSessionState x.st with ⟨r, st1⟩
  cases r with
  | error e =>
    obtain ⟨s_ret, hsteps_ret, ⟨hpc_ret, _, hmeta_ret, hx19_ret, hx20_ret, _, _, hx23_ret, _, _, hm_ret⟩ | ⟨_, hoom⟩⟩ := hcall hcode
    · rw [hres] at hm_ret
      exact P3kR1bc.reaches_outcome_steps hsteps_ret
        (P3kR1bc.loadRatchet_after_call_error_tight_placed hres hpc_ret hmeta_ret hx19_ret hx20_ret hx23_ret hm_ret)
    · exact hoom.elim
  | ok tr =>
    have hreach : reaches_pc ((blkPC_131).rebase (blkPl_131).base H) segFindChainPC_placed s
        (fun s' => ∃ trG, FindChainState_placed A ctl x trG tr st1 R s0 s') := by
      refine reaches_pc_seq hcall ?_
      intro s_ret hpc_ret _ ⟨hmeta_ret, hx19_ret, hx20_ret, hx21_ret, hx22_ret, hx23_ret, hx24_ret, hx25_ret, hm_ret⟩
      rw [hres] at hm_ret
      exact loadRatchet_after_call_ok_placed hpc_ret hmeta_ret hx19_ret hx20_ret hx21_ret hx22_ret hx23_ret hx24_ret hx25_ret hm_ret
    obtain ⟨s', hsteps, ⟨_, _, trG, hS2⟩ | ⟨_, hoom⟩⟩ := hreach hcode
    · exact ⟨s', hsteps, trG, FindChainStatePlaced.of_placed hS2 (libsignalRoLoaded_of_keepsFrozen hro hsteps.keepsFrozen)⟩
    · exact hoom.elim

/-- Relocatable `[LibsignalPlacement]` ErrTail theorem with tight panic (`ErrTailSeamTightPlaced`). -/
theorem errTail_placed_okT [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    ErrTailSeamTightPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 e R s0 s he hmod1 hmod2 herr
  have herr_pl : ErrTailState_placed A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s :=
    ⟨herr.1, ⟨herr.2.1.1, herr.2.1.2.1, herr.2.1.2.2.1, herr.2.1.2.2.2.1,
      herr.2.1.2.2.2.2.1, herr.2.1.2.2.2.2.2.1, herr.2.1.2.2.2.2.2.2.1.1, herr.2.1.2.2.2.2.2.2.2⟩,
     herr.2.2⟩
  exact P3kR1bc.errTail_ok_tight_placed hdealloc x trG tr st1 e R s0 s he hmod1 hmod2 herr_pl

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

