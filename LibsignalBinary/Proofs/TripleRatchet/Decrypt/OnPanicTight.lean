/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Defs

/-!
# Tight Panic Contracts for `try_decrypt_with_state`

Defines `tryDecryptOnPanicTight` (dropping the `S.recvPanics` disjunct from `tryDecryptSpec.onPanic`,
retaining only model panics and allocator failures), `tryDecryptSpecTight`, and the tight segment
contracts `ErrTailSpecTight`, `LoadRatchetSpecTight`, and `DhStepSpecTight` (plus relocatable
`[LibsignalPlacement]` counterparts and weakenings to the standard contracts).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalSession

/-- The panic condition of `tryDecryptSpec` without the `S.recvPanics` disjunct: the model panics or
an allocation failed, and the trace only grew. -/
def tryDecryptOnPanicTight (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (x : TryDecryptGhost) (s0 sf : State) : SepProp :=
  ⌜((x.model C S parse).1 = .error .panic ∨ allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
    anyHeap

/-- `tryDecryptSpec` with the tight panic condition `tryDecryptOnPanicTight`. -/
def tryDecryptSpecTight (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl parse S img with onPanic := tryDecryptOnPanicTight C S parse }

/-- The tight panic condition implies the binding one. -/
theorem tryDecryptOnPanicTight_weaken {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 sf ∗ R := by
  simp only [tryDecryptOnPanicTight] at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  simp only [tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  obtain ⟨⟨hc, htr⟩, hmem⟩ := h
  refine ⟨⟨?_, htr⟩, hmem⟩
  rcases hc with hp | ha
  · exact Or.inl hp
  · exact Or.inr (Or.inr ha)

/-- `reaches_outcome` against `tryDecryptSpecTight` implies it against `tryDecryptSpec`. -/
theorem reaches_outcome_tight_weaken {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost}
    {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (tryDecryptSpecTight C A ctl parse S img) x R s0 s) :
    reaches_outcome P (tryDecryptSpec C A ctl parse S img) x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

/-- `ErrTailSpec` with the outcome stated against `tryDecryptSpecTight`. -/
def ErrTailSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
      (R : SepProp) (s0 s : State),
      e ≠ .panic →
      (x.model C S parse).1 = .error e →
      (x.model C S parse).2 = st1 →
      ErrTailState A ctl img x trG tr st1 e
        (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
      reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
        (tryDecryptSpecTight C A ctl parse S img) x R s0 s

/-- `LoadRatchetSpec` with the error outcome stated against `tryDecryptSpecTight`. -/
def LoadRatchetSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TrFromOk img C A ctl abs →
    ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
      LoadRatchetState A ctl img x R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      match Mut.exec TripleRatchet.fromSessionState x.st with
      | (.error _, _) =>
        reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
          (tryDecryptSpecTight C A ctl parse S img) x R s0 s
      | (.ok tr, st1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ∃ trG, FindChainState A ctl img x trG tr st1 R s0 s'

/-- `DhStepSpec` with both panic outcomes stated against `tryDecryptOnPanicTight`. -/
def DhStepSpecTight (img : Obj.Image) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (abs : String → Option (State → State)) : Prop :=
  Obj.Loads libsignalSessionImage img →
  TripleRatchetHooks C A S abs →
  CreateChainOk img C A ctl abs →
  DerivePublicKeyBytesOk img.base C ctl abs →
  PublicKeySerializeOk img.base C A ctl abs →
  ChainKeyToPbOk img.base C A ctl abs →
  GrowOneChainOk img C A ctl abs →
  DropChainOk img.base C A ctl abs →
    ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
      (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
      Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
      tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
      tr.ratchet.receiverChains.length < 2 ^ 32 →
      rootStack ≤ s0.sp.toNat →
      DhStepState A ctl img x trG tr st1 R s0 s →
      (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem →
      let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
      match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
          tr.ratchet with
      | (.ok ck, r1) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG', ConsumeMsgKeyState A ctl img x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
      | (.error e, _) =>
        ∃ s', Steps (tripleRatchetProgAt img.base C ctl abs) s s' ∧
          ((∃ trG' r1, ErrTailState A ctl img x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
           (s'.status = .Panicked ∧
             (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

theorem ErrTailSpecTight.weaken {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : ErrTailSpecTight img C A ctl parse S abs) : ErrTailSpec img C A ctl parse S abs :=
  fun himg hH hdrop x trG tr st1 e R s0 s hne hm1 hm2 hst =>
    reaches_outcome_tight_weaken (h himg hH hdrop x trG tr st1 e R s0 s hne hm1 hm2 hst)

theorem LoadRatchetSpecTight.weaken {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : LoadRatchetSpecTight img C A ctl parse S abs) : LoadRatchetSpec img C A ctl parse S abs := by
  intro himg hfrom x R s0 s hst hcode
  have h' := h himg hfrom x R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact reaches_outcome_tight_weaken
  · exact id

theorem DhStepSpecTight.weaken {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {abs : String → Option (State → State)}
    (h : DhStepSpecTight img C A ctl parse S abs) : DhStepSpec img C A ctl parse S abs := by
  intro himg hH hcc hdpk hpks hpb hgo hdc x trG tr st1 R s0 s hfrom hfind hlen hsp hst hcode
  have h' := h himg hH hcc hdpk hpks hpb hgo hdc x trG tr st1 R s0 s hfrom hfind hlen hsp hst hcode
  dsimp only at h' ⊢
  revert h'
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with ⟨_ | ck, r1⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken hq⟩⟩

/-! ## Relocatable `[LibsignalPlacement]` Tight Panic Contracts -/

def tryDecryptSpecTightPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { tryDecryptSpecPlaced C A ctl parse S with onPanic := tryDecryptOnPanicTight C S parse }

theorem tryDecryptOnPanicTight_weaken_placed [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {x : TryDecryptGhost}
    {R : SepProp} {s0 sf : State}
    (h : sf.mem ⊨ tryDecryptOnPanicTight C S parse x s0 sf ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 sf ∗ R :=
  tryDecryptOnPanicTight_weaken (img := tryDecryptPlacedImg) h

theorem reaches_outcome_tight_weaken_placed [LibsignalPlacement] {P : Program} {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {x : TryDecryptGhost}
    {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (tryDecryptSpecTightPlaced C A ctl parse S) x R s0 s) :
    reaches_outcome P (tryDecryptSpecPlaced C A ctl parse S) x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with hret | ⟨hpan, hq⟩ | hexit | hoom
  · exact Or.inl hret
  · exact Or.inr (Or.inl ⟨hpan, tryDecryptOnPanicTight_weaken_placed hq⟩)
  · exact Or.inr (Or.inr (Or.inl hexit))
  · exact Or.inr (Or.inr (Or.inr hoom))

def ErrTailSeamTightPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (e : SignalProtocolError)
    (R : SepProp) (s0 s : State),
    e ≠ .panic →
    (x.model C S parse).1 = .error e →
    (x.model C S parse).2 = st1 →
    ErrTailStatePlaced entry A ctl x trG tr st1 e
      (decryptDraws C x.st x.msg.senderRatchetKey x.rest) R s0 s →
    reaches_outcome prog (tryDecryptSpecTightPlaced C A ctl parse S) x R s0 s

def S1SeamTightPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (R : SepProp) (s0 s : State),
    LoadRatchetStatePlaced entry A ctl x R s0 s →
    prog.CodeLoaded s.mem →
    match Mut.exec TripleRatchet.fromSessionState x.st with
    | (.error _, _) =>
      reaches_outcome prog (tryDecryptSpecTightPlaced C A ctl parse S) x R s0 s
    | (.ok tr, st1) =>
      ∃ s', Steps prog s s' ∧
        ∃ trG, FindChainStatePlaced entry A ctl x trG tr st1 R s0 s'

def S3SeamTightPlaced [LibsignalPlacement] (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (R : SepProp) (s0 s : State),
    Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr, st1) →
    tr.ratchet.findReceiverChainKey x.msg.senderRatchetKey = .ok none →
    tr.ratchet.receiverChains.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    x.rest.length < 2 ^ 63 →
    DhStepStatePlaced entry A ctl x trG tr st1 R s0 s →
    prog.CodeLoaded s.mem →
    let draws := decryptDraws C x.st x.msg.senderRatchetKey x.rest
    match Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
        tr.ratchet with
    | (.ok ck, r1) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG', ConsumeMsgKeyStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 ck draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))
    | (.error e, _) =>
      ∃ s', Steps prog s s' ∧
        ((∃ trG' r1, ErrTailStatePlaced entry A ctl x trG' { tr with ratchet := r1 } st1 e draws R s0 s') ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ tryDecryptOnPanicTight C S parse x s0 s' ∗ R)))

theorem ErrTailSeamTightPlaced.weaken [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    (h : ErrTailSeamTightPlaced prog entry C A ctl parse S) :
    ErrTailSeamPlaced prog entry C A ctl parse S :=
  fun x trG tr st1 e R s0 s hne hm1 hm2 hst =>
    reaches_outcome_tight_weaken_placed (h x trG tr st1 e R s0 s hne hm1 hm2 hst)

theorem S1SeamTightPlaced.weaken [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    (h : S1SeamTightPlaced prog entry C A ctl parse S) :
    S1SeamPlaced prog entry C A ctl parse S := by
  intro x R s0 s hst hcode
  have h' := h x R s0 s hst hcode
  revert h'
  rcases Mut.exec TripleRatchet.fromSessionState x.st with ⟨_ | tr, st1⟩
  · exact reaches_outcome_tight_weaken_placed
  · exact id

theorem S3SeamTightPlaced.weaken [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel}
    (h : S3SeamTightPlaced prog entry C A ctl parse S) :
    S3SeamPlaced prog entry C A ctl parse S := by
  intro x trG tr st1 R s0 s hfrom hfind hlen hsp hrest hst hcode
  have h' := h x trG tr st1 R s0 s hfrom hfind hlen hsp hrest hst hcode
  dsimp only at h' ⊢
  revert h'
  rcases Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey (coinsOf x.rest))
      tr.ratchet with ⟨_ | ck, r1⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken_placed hq⟩⟩
  · rintro ⟨s', hsteps, hok | ⟨hpan, hq⟩⟩
    · exact ⟨s', hsteps, Or.inl hok⟩
    · exact ⟨s', hsteps, Or.inr ⟨hpan, tryDecryptOnPanicTight_weaken_placed hq⟩⟩

end CryptoVerification.LibsignalTripleRatchet.Decrypt
