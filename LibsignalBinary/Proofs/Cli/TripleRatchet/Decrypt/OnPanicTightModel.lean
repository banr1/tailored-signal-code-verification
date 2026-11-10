/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.OnPanicTight
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.OnPanicTightModel

/-!
# Tight-Panic Weakening and Post-`consume_message_key` Model Panic Bridge

Proves weakening from `tryDecryptSpecTight` to `tryDecryptSpec` and shows that once
`fromSessionState`, `ensureReceiverChain`, and `consumeMessageKey` succeed, any `S.recvPanics`
disjunct in `tryDecryptSpec.onPanic` is already a pure model panic (`Model.model_of_recvPanics`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalSession

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  simp only [tryDecryptOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inr ha)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_tight_weaken
    {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptSpecTight C A ctl parse S img) x R s0 s) :
    reaches_outcome P (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl parse S img) x R s0 s := by
  refine h.mono_outcome fun sf hout => ?_
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan,
      CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecTight.weaken
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpecTight img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.ErrTailSpec img C A ctl parse S abs :=
  fun himg hH hdrop x trG tr st1 e R s0 s hne hm1 hm2 hst =>
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_tight_weaken
      (h himg hH hdrop x trG tr st1 e R s0 s hne hm1 hm2 hst)

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpecTight.weaken
    {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpecTight img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.LoadRatchetSpec img C A ctl parse S abs := by
  intro himg hfrom x R s0 s hst hcode
  have h' := h himg hfrom x R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.reaches_outcome_tight_weaken
  · exact id

theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpecTight.weaken
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpecTight img C A ctl parse S abs) :
    CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.DhStepSpec img C A ctl parse S abs := by
  intro himg hH hcc hdpk hpks hpb hgo hdc x trG tr st1 R s0 s hfrom hfind hlen hsp hst hcode
  have h' := h himg hH hcc hdpk hpks hpb hgo hdc x trG tr st1 R s0 s hfrom hfind hlen hsp hst hcode
  dsimp only at h' ⊢
  revert h'
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with ⟨_ | ck, r1⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan,
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken hq⟩⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan,
        CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecryptOnPanicTight_weaken hq⟩⟩

/-- After `consumeMessageKey` succeeds, the binding panic condition of CLI `tryDecryptSpec` implies
the tight one: its `S.recvPanics` disjunct is a model panic (`Model.model_of_recvPanics`). -/
theorem _root_.CryptoVerification.Cli.LibsignalTripleRatchet.Decrypt.tryDecrypt_onPanicTight_of_afterCmk
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {tr : TripleRatchet (List (BitVec 8))} {st1 : SessionState (List (BitVec 8))}
    {ck : ChainKey} {r1 r2 : RatchetState} {mkg : MessageKeyGenerator} {R : SepProp}
    {s0 sf : State}
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 = (.ok mkg, r2))
    (h : sf.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 sf ∗ R) :
    sf.mem ⊨ tryDecryptOnPanicTight C S uuidTryParse x s0 sf ∗ R := by
  simp only [CryptoVerification.Cli.LibsignalTripleRatchet.tryDecryptSpec, Spec.inImage] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptOnPanicTight]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htrace⟩, hmem⟩ := h
  refine ⟨⟨?_, htrace⟩, hmem⟩
  rcases hc with hm | hp | ha
  · exact Or.inl hm
  · exact Or.inl (Model.model_of_recvPanics htr herc hcmk hp)
  · exact Or.inr ha

end CryptoVerification.LibsignalTripleRatchet.Decrypt
