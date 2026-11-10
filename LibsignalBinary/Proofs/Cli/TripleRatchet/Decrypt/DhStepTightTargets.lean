/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepTightTargets
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhCommitMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepMain
import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DhStepRecvChain
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DhStepRecvChain

/-!
# `try_decrypt_with_state` Tight-Panic Segment S3 Contract

Lifts `dhStep_ok` from `spqrNoPanic` to `DhStepSpecTight` (`dhStep_okT`) for arbitrary `S : SpqrModel`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep

open Arm64 ProofLib ProofLib.ProgramReflection

open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession

open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

open CryptoVerification.LibsignalTripleRatchetRepr

open CryptoVerification.LibsignalTripleRatchet

open CryptoVerification.LibsignalTripleRatchet.Getters

open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet

open CryptoVerification.LibsignalTripleRatchet.Decrypt


open CryptoVerification.LibsignalSession

namespace P3kR1bd

/-- Any panic outcome against `spqrNoPanic` satisfies `tryDecryptOnPanicTight` for any `S`. -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse spqrNoPanic img).onPanic x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | hpan | ha
  · exact Or.inl (model_fst_eq_panic_of_spqrNoPanic C S x hp)
  · nomatch hpan
  · exact Or.inr ha

end P3kR1bd

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_okT (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpecTight img C A ctl uuidTryParse S abs := by
  intro himg hHooks hcc hdpk hPkSer hToPb hGrowOne hDropChain
    x trG tr st1 R s0 s hfrom hfind hrc_len hsp0 hs3 hcode
  dsimp only
  cases hsc : tr.ratchet.senderChain with
  | none =>
    rw [dhRatchetStep_none C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet hsc,
        decryptDraws_of_senderChain_none C x.st st1 tr x.msg.senderRatchetKey x.rest hfrom hfind hsc]
    obtain ⟨s', hsteps, ⟨_, _, herr⟩ | ⟨_, hoom⟩⟩ :=
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_missing_sender_chain (A := A) (ctl := ctl) (ext := tripleRatchetExterns C ctl abs)
        himg x trG tr st1 R s0 s hsc hs3 hcode
    · exact ⟨s', hsteps, Or.inl ⟨trG, tr.ratchet, herr⟩⟩
    · exact hoom.elim
  | some sc =>
    have ⟨hrk1_ne, hrk2_ne⟩ := rk_ne_zero s0.sp (s0.sp - 1504#64) rfl hsp0
    have hstep1 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_recv_create_chain (S := P3kR1bd.spqrNoPanic)
      himg hcc x trG tr st1 sc R s0 s hsc hrk1_ne hs3 hcode
    cases hcc1 : rootCreateChain C tr.ratchet.rootKey x.msg.senderRatchetKey sc.ratchetKey.privateKey with
    | error e =>
      rw [hcc1] at hstep1
      rw [dhRatchetStep_some_err1 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet sc e hsc hcc1,
          decryptDraws_of_cc1_err C x.st st1 tr x.msg.senderRatchetKey x.rest sc e hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, herr1 | ⟨hpan1, hq1⟩⟩ := hstep1
      · exact ⟨s1, hsteps1, Or.inl herr1⟩
      · exact ⟨s1, hsteps1, Or.inr ⟨hpan1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩
    | ok p1 =>
      rcases p1 with ⟨rk1, rck⟩
      rw [hcc1] at hstep1
      rw [decryptDraws_of_cc1_ok C x.st st1 tr x.msg.senderRatchetKey x.rest sc rk1 rck hfrom hfind hsc hcc1]
      obtain ⟨s1, hsteps1, hafter | ⟨hpan1, hq1⟩⟩ := hstep1
      · have hrng := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.DhStepCallees.coinsFillAt_ok_td (b := img.base) (C := C) (ctl := ctl)
          (abs := abs) (cur := x.cur) (rest := x.rest) hHooks.alloc (ProofLib.ObjectLoad.base_aligned_of_loads himg)
        have hsd := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.DhStepCallees.staticDrop_ok_at2_td (b := img.base) (C := C) (ctl := ctl) (abs := abs)
        have hstep2 := CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.dhStep_keygen_and_send_create_chain (S := P3kR1bd.spqrNoPanic)
          himg hcc hdpk x trG tr st1 rk1 rck R s0 s1 hrng hsd hrk2_ne hafter (hsteps1.codeLoaded hcode)
        dsimp only at hstep2
        cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, herr2 | ⟨hpan2, hq2⟩⟩ := hstep2
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inl herr2⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq2⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [hcc2] at hstep2
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          obtain ⟨s2, hsteps2, hcommit | ⟨hpan2, hq2⟩⟩ := hstep2
          · have hsteps12 := Steps.trans hsteps1 hsteps2
            have hclamp := clampScalar_keyPair_generate C (coinsOf x.rest)
            obtain ⟨s3, hsteps3, hout3 | ⟨hpan3, hq3⟩⟩ :=
              CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhCommit.s3_commit_spec_ext img C A ctl P3kR1bd.spqrNoPanic (tripleRatchetExterns C ctl abs)
                himg (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hHooks.alloc)
                hPkSer hToPb hGrowOne hDropChain
                x trG tr st1 sc rck (KeyPair.generate C (coinsOf x.rest))
                finalRootKey senderChainKey R s0 s2
                hsc hrc_len hclamp hcommit (hsteps12.codeLoaded hcode)
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inl hout3⟩
            · exact ⟨s3, Steps.trans hsteps12 hsteps3, Or.inr ⟨hpan3, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq3⟩⟩
          · exact ⟨s2, Steps.trans hsteps1 hsteps2, Or.inr ⟨hpan2, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq2⟩⟩
      · cases hcc2 : rootCreateChain C rk1 x.msg.senderRatchetKey
            (KeyPair.generate C (coinsOf x.rest)).privateKey with
        | error e =>
          rw [dhRatchetStep_some_err2 C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 rck e hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩
        | ok p2 =>
          rcases p2 with ⟨finalRootKey, senderChainKey⟩
          rw [dhRatchetStep_some_ok C x.msg.senderRatchetKey (coinsOf x.rest) tr.ratchet
              sc rk1 finalRootKey rck senderChainKey hsc hcc1 hcc2]
          exact ⟨s1, hsteps1, Or.inr ⟨hpan1, CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStep.P3kR1bd.onPanicTight_of_spqrNoPanic hq1⟩⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt.DhStep
