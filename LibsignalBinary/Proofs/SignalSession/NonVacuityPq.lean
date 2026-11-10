/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.SignalSession.CliBinaryPq
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Proofs.SignalSession.NonVacuity
import all Init.Data.Repr
import all Init.Data.String.Defs

/-!
# Non-Vacuity Checks for `PqDirNoMatch` and `CliBinaryPq`

Sanity and non-vacuity theorems for the PQXDH-mode CLI specifications:
1. Reflexivity, path-alias tolerance (`agreeExcept_diff_at_alias`), and discrimination properties of
   `Outcome.AgreeExcept` and `OutcomeMatchesModelExceptPath`.
2. Unconditional inhabitation of all five clauses of `CliPqxdhInputs W`.
3. Concrete `pqInitModel`-constructed session witness on `emptyParty` at `W0` with non-matching
   pre-key message (`¬ PqSessionMatches x g m`), ruling out `none`, always-aborting, and
   always-accepting runs under `CliSpecPqxdhNoMatch`.
4. Rejection of malformed ELF bytes by `CliPqxdhBinaryCorrect` and `#print axioms` checks.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.NonVacuityPq

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E CryptoVerification.LibsignalProtoCodec

/-! ## 1. `Outcome.AgreeExcept` and `OutcomeMatchesModelExceptPath` sanity checks -/

theorem agreeExcept_refl (p : String) (o : Outcome) : Outcome.AgreeExcept p o o := by
  cases o with
  | aborted => trivial
  | exited c out fs => exact ⟨rfl, rfl, fun _ _ => rfl⟩

theorem agreeExcept_diff_at_p (p : String) (c : Nat) (out : List (BitVec 8))
    (fs : String → Option (List (BitVec 8))) (v : Option (List (BitVec 8))) :
    Outcome.AgreeExcept p
      (.exited c out (fun q => if q = p then v else fs q))
      (.exited c out fs) := by
  refine ⟨rfl, rfl, fun q hq => ?_⟩
  have hqp : q ≠ p := fun h => hq (h ▸ rfl)
  simp [hqp]

/-- The exception covers every spelling of `p`: the files may differ at `"./sessions/peer"` when
`p = "sessions/peer"` (the two have the same canonical form, so `fsView` reads the same file at
both). With raw `String` inequality this would fail. -/
theorem agreeExcept_diff_at_alias (c : Nat) (out : List (BitVec 8))
    (fs : String → Option (List (BitVec 8))) (v : Option (List (BitVec 8))) :
    Outcome.AgreeExcept "sessions/peer"
      (.exited c out (fun q => if q = "./sessions/peer" then v else fs q))
      (.exited c out fs) := by
  refine ⟨rfl, rfl, fun q hq => ?_⟩
  have hqa : q ≠ "./sessions/peer" := by
    rintro rfl
    exact hq (by decide)
  simp [hqa]

theorem not_agreeExcept_diff_code :
    ¬ Outcome.AgreeExcept "sessions/peer"
      (.exited 0 [] (fun _ => none))
      (.exited 1 [] (fun _ => none)) := by
  simp [Outcome.AgreeExcept]

theorem not_agreeExcept_diff_other_path :
    ¬ Outcome.AgreeExcept "sessions/peer"
      (.exited 0 [] (fun q => if q = "address" then some [1#8] else none))
      (.exited 0 [] (fun _ => none)) := by
  intro h
  have hq := h.2.2 "address" (by decide)
  simp at hq

theorem not_agreeExcept_exited_aborted (p : String) (c : Nat) (out : List (BitVec 8))
    (fs : String → Option (List (BitVec 8))) :
    ¬ Outcome.AgreeExcept p (.exited c out fs) .aborted := by
  simp [Outcome.AgreeExcept]

theorem observedExcept_pqObserve (W : PEParams) (i : Inputs) (p : String)
    (r : Option (Option (PqParty × List (BitVec 8)))) :
    OutcomeMatchesModelExceptPath W i p r (pqxdhExpectedOutcome W i r) := by
  cases r with
  | none => rfl
  | some opt =>
    cases opt with
    | none => rfl
    | some _ =>
      dsimp only [OutcomeMatchesModelExceptPath]
      exact agreeExcept_refl p _

theorem observedExcept_reject_iff (W : PEParams) (i : Inputs) (p : String) (o : Outcome) :
    OutcomeMatchesModelExceptPath W i p (some none) o ↔ o = pqxdhExpectedOutcome W i (some none) :=
  Iff.rfl

theorem observedExcept_panic_iff (W : PEParams) (i : Inputs) (p : String) (o : Outcome) :
    OutcomeMatchesModelExceptPath W i p none o ↔ o = .aborted := by
  simp [OutcomeMatchesModelExceptPath, pqxdhExpectedOutcome, observe]

theorem observedExcept_accept_iff (W : PEParams) (i : Inputs) (p : String)
    (st' : PqParty) (out : List (BitVec 8)) (o : Outcome) :
    OutcomeMatchesModelExceptPath W i p (some (some (st', out))) o ↔
      Outcome.AgreeExcept p o (pqxdhExpectedOutcome W i (some (some (st', out)))) :=
  Iff.rfl

/-! ## 2. `CliPqxdhInputs W` is inhabited in all five clauses for every `W` -/

/-- A typed pre-key message with empty inner message and chosen `baseKey`. -/
def testPreKeyMsg (bk : List.Vector (BitVec 8) 32) : PreKeyMessageFields where
  regId := 0
  opkId := none
  spkId := 0
  kpkId := 0
  kyberCt := List.Vector.replicate 1568 0#8
  baseKey := bk
  idPub := List.Vector.replicate 32 0#8
  inner := []

def nzVec32 : List.Vector (BitVec 8) 32 := ⟨1#8 :: List.replicate 31 0#8, rfl⟩

theorem cliPqInputs_emptyParty_init (W : PEParams) (b : PreKeyBundleFields)
    (t : List.Vector (BitVec 8) initiateTapeLen) :
    CliPqxdhInputs W (pqInitInputs W emptyParty b t) :=
  ⟨emptyParty, wfPq_emptyParty_uncond W, Or.inl ⟨rfl, b, t, rfl⟩⟩

theorem cliPqInputs_emptyParty_send (W : PEParams) (r : List.Vector (BitVec 8) 64) :
    CliPqxdhInputs W (pqSendInputs W emptyParty [] r) :=
  ⟨emptyParty, wfPq_emptyParty_uncond W, Or.inr (Or.inl ⟨[], r, by decide, rfl⟩)⟩

theorem cliPqInputs_emptyParty_recvWhisper (W : PEParams) (rc : BitVec 256) :
    CliPqxdhInputs W (pqRecvInputs W emptyParty [wireWhisper] rc) :=
  ⟨emptyParty, wfPq_emptyParty_uncond W, Or.inr (Or.inr (Or.inl ⟨[], rc, by decide, rfl⟩))⟩

theorem cliPqInputs_emptyParty_recvPrekey (W : PEParams) (rc : BitVec 256) :
    CliPqxdhInputs W (pqRecvInputs W emptyParty (wirePrekey :: (testPreKeyMsg nzVec32).bytes) rc) := by
  refine ⟨emptyParty, wfPq_emptyParty_uncond W, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  refine ⟨testPreKeyMsg nzVec32, rc, ?_, rfl⟩
  change ([] : List (BitVec 8)).length + 2048 < 2 ^ 32
  decide

theorem cliPqInputs_emptyParty_recv (W : PEParams) (rc : BitVec 256) :
    CliPqxdhInputs W (pqRecvInputs W emptyParty [] rc) := by
  refine ⟨emptyParty, wfPq_emptyParty_uncond W, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
  exact ⟨[], rc, by decide, by simp, by simp, rfl⟩

/-! ## 3. General non-vacuity of `CliSpecPqxdhNoMatch` from any `PqxdhPartyInSpecDomain` state holding a session -/

/-- Flip the first byte after the DJB type tag so `s ≠ djbKey (flipBaseKey s)`. -/
def flipBaseKey (s : List (BitVec 8)) : List.Vector (BitVec 8) 32 :=
  ⟨(match s.drop 1 with
    | b :: _ => b ^^^ 1#8
    | [] => 1#8) :: List.replicate 31 0#8, rfl⟩

theorem flipBaseKey_ne_djbKey (s : List (BitVec 8)) :
    s ≠ djbKey (flipBaseKey s) := by
  intro h
  cases s with
  | nil => simp [djbKey] at h
  | cons a rest =>
    cases rest with
    | nil => simp [djbKey, flipBaseKey] at h
    | cons b tl =>
      simp [djbKey, flipBaseKey] at h
      have hb : b = b ^^^ 1#8 := h.2.1
      have : (b ^^^ b) = (b ^^^ (b ^^^ 1#8)) := congrArg (b ^^^ ·) hb
      simp at this

theorem not_pqSessionMatches_flip (x : RecordExtras) (g : GhostState Bytes) :
    ¬ PqSessionMatches x g (testPreKeyMsg (flipBaseKey x.aliceBaseKey)) := by
  intro hm
  exact flipBaseKey_ne_djbKey x.aliceBaseKey hm.1

private theorem prost_bytesField_djbKey_length (tag : Nat) (bk1 bk2 : List.Vector (BitVec 8) 32) :
    (Prost.bytesField tag (some (djbKey bk1))).length =
      (Prost.bytesField tag (some (djbKey bk2))).length := by
  simp [Prost.bytesField, djbKey]

private theorem testPreKeyMsg_bytes_length_eq (bk : List.Vector (BitVec 8) 32) :
    (testPreKeyMsg bk).bytes.length = (testPreKeyMsg nzVec32).bytes.length := by
  simp only [testPreKeyMsg, PreKeyMessageFields.bytes, ProtoPreKeySignalMessage.encode,
    List.length_cons, List.length_append]
  rw [prost_bytesField_djbKey_length 2 bk nzVec32]

private theorem not_testPreKeyMsg_gt_stdinCapBytes (bk : List.Vector (BitVec 8) 32) :
    ¬ (wirePrekey :: (testPreKeyMsg bk).bytes).length > stdinCapBytes := by
  have hlen : (wirePrekey :: (testPreKeyMsg bk).bytes).length =
      (wirePrekey :: (testPreKeyMsg nzVec32).bytes).length := by
    simp [testPreKeyMsg_bytes_length_eq bk]
  rw [hlen]
  decide +kernel

theorem not_cliSpecPqNoMatch_none_of_wfSession (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st : PqParty) (x : RecordExtras) (g : GhostState Bytes)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = some (x, g)) :
    ¬ CliSpecPqxdhNoMatch (fun _ => none) X W := by
  intro hspec
  let m := testPreKeyMsg (flipBaseKey x.aliceBaseKey)
  have hlen : m.inner.length + 2048 < 2 ^ 32 := by
    change ([] : List (BitVec 8)).length + 2048 < 2 ^ 32
    decide
  have hnm : ¬ PqSessionMatches x g m := not_pqSessionMatches_flip x g
  have hcap : ¬ (wirePrekey :: m.bytes).length > stdinCapBytes :=
    not_testPreKeyMsg_gt_stdinCapBytes (flipBaseKey x.aliceBaseKey)
  have hspec' := hspec st hwf x g hs m 0 hlen hnm
  simp only [hcap, ↓reduceIte] at hspec'
  obtain ⟨o, ho, _⟩ := hspec'
  simp at ho

theorem not_cliSpecPqNoMatch_aborted_of_wfSession (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st : PqParty) (x : RecordExtras) (g : GhostState Bytes)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = some (x, g)) :
    ¬ CliSpecPqxdhNoMatch (fun _ => some .aborted) X W := by
  intro hspec
  let m := testPreKeyMsg (flipBaseKey x.aliceBaseKey)
  have hlen : m.inner.length + 2048 < 2 ^ 32 := by
    change ([] : List (BitVec 8)).length + 2048 < 2 ^ 32
    decide
  have hnm : ¬ PqSessionMatches x g m := not_pqSessionMatches_flip x g
  have hcap : ¬ (wirePrekey :: m.bytes).length > stdinCapBytes :=
    not_testPreKeyMsg_gt_stdinCapBytes (flipBaseKey x.aliceBaseKey)
  have hspec' := hspec st hwf x g hs m 0 hlen hnm
  simp only [hcap, ↓reduceIte] at hspec'
  obtain ⟨o, ho, hobs⟩ := hspec'
  simp at ho
  subst ho
  have htry : SignalMessage.tryFrom protoSignalCodec m.inner =
      .error (.ciphertextMessageTooShort 0) := rfl
  simp [OutcomeMatchesModelExceptPath, pqRecvPrekeyModel, htry, pqxdhExpectedOutcome, observe] at hobs

theorem not_cliSpecPqNoMatch_alwaysAccept_of_wfSession (X : UnreachedPqxdhPrimitives) (W : PEParams)
    (st : PqParty) (x : RecordExtras) (g : GhostState Bytes)
    (hwf : PqxdhPartyInSpecDomain W st) (hs : st.session = some (x, g)) :
    ¬ CliSpecPqxdhNoMatch (fun i => some (.exited 0 [] (filesOf i.files))) X W := by
  intro hspec
  let m := testPreKeyMsg (flipBaseKey x.aliceBaseKey)
  have hlen : m.inner.length + 2048 < 2 ^ 32 := by
    change ([] : List (BitVec 8)).length + 2048 < 2 ^ 32
    decide
  have hnm : ¬ PqSessionMatches x g m := not_pqSessionMatches_flip x g
  have hcap : ¬ (wirePrekey :: m.bytes).length > stdinCapBytes :=
    not_testPreKeyMsg_gt_stdinCapBytes (flipBaseKey x.aliceBaseKey)
  have hspec' := hspec st hwf x g hs m 0 hlen hnm
  simp only [hcap, ↓reduceIte] at hspec'
  obtain ⟨o, ho, hobs⟩ := hspec'
  simp at ho
  subst ho
  have htry : SignalMessage.tryFrom protoSignalCodec m.inner =
      .error (.ciphertextMessageTooShort 0) := rfl
  simp [OutcomeMatchesModelExceptPath, pqRecvPrekeyModel, htry, pqxdhExpectedOutcome, observe] at hobs

/-! ## 4. Concrete `pqInitModel`-built session witness at `W0` -/

def C0 : Crypto where
  F st _ := st
  E _ b := b
  D _ b := b
  X _ _ := nzVec32
  pubKey _ := nzVec32

def K0 : CryptoVerification.LibsignalSpqrV1.MlKem where
  keyPair _ := List.Vector.replicate 2400 0#8
  encaps1 _ _ :=
    some (List.Vector.replicate 960 0#8,
          List.Vector.replicate 2080 0#8,
          List.Vector.replicate 32 0#8)
  encaps2 _ _ := List.Vector.replicate 128 0#8
  decaps _ _ _ := List.Vector.replicate 32 0#8
  validPk _ _ := true

def Q0 : PqxdhPrims where
  F512 st _ := st
  montToEd _ _ := some (List.Vector.replicate 160 0#8)
  compress _ := List.Vector.replicate 32 0#8
  edNeg p := p
  isTorsionFree _ := true
  dsmb _ A _ := A
  scalarMod s := s
  scalarWide w := fitVec 32 w.toList
  encaps _ _ := (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps _ _ := List.Vector.replicate 32 0#8
  K := K0

def W0 : PEParams := ⟨C0, Q0⟩

def b0 : PreKeyBundleFields where
  regId := 0
  opk := none
  spkId := 0
  spkPub := List.Vector.replicate 32 0#8
  spkSig := List.Vector.replicate 64 0#8
  kpkId := 0
  kpkPub := List.Vector.replicate 1568 0#8
  kpkSig := List.Vector.replicate 64 0#8
  idPub := List.Vector.replicate 32 0#8

def t0 : List.Vector (BitVec 8) initiateTapeLen :=
  List.Vector.replicate initiateTapeLen 0#8

def X0 : UnreachedPqxdhPrimitives where
  sigPkGen _ := []
  sigSign _ _ _ := []
  scalarMul _ _ := []
  scalarAdd _ _ := []
  kemKeyGen _ := ([], [])
  pow8 _ := []
  isValidDhTriple _ _ _ := false

set_option maxRecDepth 16384 in
theorem initiateState_W0_eq (X : UnreachedPqxdhPrimitives) :
    initiateState X W0 .A emptyParty.me b0 t0 = initiateState X0 W0 .A emptyParty.me b0 t0 := by
  with_unfolding_all rfl

theorem initiateState_W0_isSome :
    (initiateState X0 W0 .A emptyParty.me b0 t0).isSome = true := by
  decide +kernel

theorem pqInitModel_W0_creates_wfSession (X : UnreachedPqxdhPrimitives) :
    ∃ st1 x g,
      pqInitModel X W0 emptyParty b0 t0 = some (some (st1, [])) ∧
      st1.session = some (x, g) ∧
      PqxdhPartyInSpecDomain W0 st1 := by
  have hEq := initiateState_W0_eq X
  have hSome := initiateState_W0_isSome
  cases hInit0 : initiateState X0 W0 .A emptyParty.me b0 t0 with
  | none => simp [hInit0] at hSome
  | some xg =>
    rcases xg with ⟨x, g⟩
    have hInit : initiateState X W0 .A emptyParty.me b0 t0 = some (x, g) := hEq.trans hInit0
    let st1 : PqParty := { emptyParty with peerId := some ⟨⟨b0.idPub⟩⟩, session := some (x, g) }
    refine ⟨st1, x, g, ?_, rfl, ?_⟩
    · have hparty : emptyParty.party = .A := rfl
      have htrusts : emptyParty.trusts ⟨⟨b0.idPub⟩⟩ = true := rfl
      simp only [pqInitModel, htrusts, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hparty, hInit]
      rfl
    · have hrec : (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 31 := by
        have : (match initiateState X0 W0 .A emptyParty.me b0 t0 with
          | some (x', g') => decide ((encodeRecordUnderExtras (fun _ => x') g').length < 2 ^ 31)
          | none => false) = true := by decide +kernel
        simpa [hInit0] using this
      have hdir : ∀ f ∈ encodeDir W0 st1,
          f.2.length < 2 ^ 31 ∧ ((∀ i, f.1 ≠ baseKeysFile i) → f.2.length ≤ fileCapBytes) := by
        have hcap : decide (∀ f ∈ (match initiateState X0 W0 .A emptyParty.me b0 t0 with
            | some (x', g') => encodeDir W0
                { emptyParty with peerId := some ⟨⟨b0.idPub⟩⟩, session := some (x', g') }
            | none => []), f.2.length ≤ fileCapBytes) = true := by decide +kernel
        have hcap' : ∀ f ∈ encodeDir W0 st1, f.2.length ≤ fileCapBytes := by
          simpa [hInit0, st1] using hcap
        intro f hf
        have hle := hcap' f hf
        have hlt : fileCapBytes < 2 ^ 31 := by decide
        exact ⟨Nat.lt_of_le_of_lt hle hlt, fun _ => hle⟩
      have hgparty : g.party = .A := by
        have : (match initiateState X0 W0 .A emptyParty.me b0 t0 with
          | some (_, g') => decide (g'.party = .A)
          | none => false) = true := by decide +kernel
        simpa [hInit0] using this
      refine ⟨?_, hdir, by simp [st1, emptyParty], by simp [st1, emptyParty],
        by simp [st1, emptyParty], by simp [st1, emptyParty]⟩
      intro x' g' hs
      injection hs with hpair
      cases hpair
      exact ⟨⟨g, ReachablePqxdhSession.initiate X .A emptyParty.me b0 t0 x g hInit, rfl, rfl⟩,
        hgparty, hrec⟩

theorem cliPqInputs_withSession_W0_recvPrekey (X : UnreachedPqxdhPrimitives) (rc : BitVec 256) :
    ∃ st1 x g,
      st1.session = some (x, g) ∧
      PqxdhPartyInSpecDomain W0 st1 ∧
      ¬ PqSessionMatches x g (testPreKeyMsg (flipBaseKey x.aliceBaseKey)) ∧
      CliPqxdhInputs W0 (pqRecvInputs W0 st1
        (wirePrekey :: (testPreKeyMsg (flipBaseKey x.aliceBaseKey)).bytes) rc) := by
  obtain ⟨st1, x, g, _, hs, hwf⟩ := pqInitModel_W0_creates_wfSession X
  refine ⟨st1, x, g, hs, hwf, not_pqSessionMatches_flip x g, ?_⟩
  refine ⟨st1, hwf, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
  refine ⟨testPreKeyMsg (flipBaseKey x.aliceBaseKey), rc, ?_, rfl⟩
  change ([] : List (BitVec 8)).length + 2048 < 2 ^ 32
  decide

theorem not_cliSpecPqNoMatch_none (X : UnreachedPqxdhPrimitives) :
    ¬ CliSpecPqxdhNoMatch (fun _ => none) X W0 := by
  obtain ⟨st1, x, g, _, hs, hwf⟩ := pqInitModel_W0_creates_wfSession X
  exact not_cliSpecPqNoMatch_none_of_wfSession X W0 st1 x g hwf hs

theorem not_cliSpecPqNoMatch_aborted (X : UnreachedPqxdhPrimitives) :
    ¬ CliSpecPqxdhNoMatch (fun _ => some .aborted) X W0 := by
  obtain ⟨st1, x, g, _, hs, hwf⟩ := pqInitModel_W0_creates_wfSession X
  exact not_cliSpecPqNoMatch_aborted_of_wfSession X W0 st1 x g hwf hs

theorem not_cliSpecPqNoMatch_alwaysAccept (X : UnreachedPqxdhPrimitives) :
    ¬ CliSpecPqxdhNoMatch (fun i => some (.exited 0 [] (filesOf i.files))) X W0 := by
  obtain ⟨st1, x, g, _, hs, hwf⟩ := pqInitModel_W0_creates_wfSession X
  exact not_cliSpecPqNoMatch_alwaysAccept_of_wfSession X W0 st1 x g hwf hs

/-! ## 5. `CliPqxdhElfCorrect` and `CliPqxdhBinaryCorrect` non-triviality -/

theorem not_libsignalCliPqBinaryCorrect_nil : ¬ CliPqxdhBinaryCorrect [] := by
  rintro ⟨elf, hparse, _⟩
  have h : Arm64.Process.ElfImage.parse [] =
      .error "ElfImage.parse: file shorter than 64-byte ELF64 header" := rfl
  rw [h] at hparse
  cases hparse

theorem cliPqBinaryCorrect_send_some (elf : Arm64.Process.ElfImage) (W : CliHooks)
    (h : CliPqxdhElfCorrect elf) :
    cliRunAbortOnPanic elf W (pqSendInputs ⟨W.C, W.Q⟩ emptyParty [] (List.Vector.replicate 64 0#8)) ≠
      none := by
  have hspec := (h.2 W X0).1
  have hsend := (hspec emptyParty (wfPq_emptyParty_uncond ⟨W.C, W.Q⟩)).2.1
    [] (List.Vector.replicate 64 0#8) (by decide)
  rw [hsend]
  simp [stdinCapBytes, maxPlaintextBytes]

/-! ## 6. `#print axioms` on all new definitions and non-vacuity checks -/

#print axioms CryptoVerification.SignalSession.Outcome.AgreeExcept
#print axioms CryptoVerification.SignalSession.OutcomeMatchesModelExceptPath
#print axioms CryptoVerification.SignalSession.CliSpecPqxdhNoMatch
#print axioms CryptoVerification.SignalSession.CliPqxdhInputs
#print axioms CryptoVerification.SignalSession.CliPqxdhAllocNeverFails
#print axioms CryptoVerification.SignalSession.CliPqxdhElfCorrect
#print axioms CryptoVerification.SignalSession.CliPqxdhBinaryCorrect
#print axioms agreeExcept_diff_at_p
#print axioms agreeExcept_diff_at_alias
#print axioms not_agreeExcept_diff_code
#print axioms not_agreeExcept_diff_other_path
#print axioms observedExcept_pqObserve
#print axioms cliPqInputs_emptyParty_init
#print axioms cliPqInputs_emptyParty_send
#print axioms cliPqInputs_emptyParty_recvWhisper
#print axioms cliPqInputs_emptyParty_recvPrekey
#print axioms cliPqInputs_emptyParty_recv
#print axioms cliPqInputs_withSession_W0_recvPrekey
#print axioms not_cliSpecPqNoMatch_none
#print axioms not_cliSpecPqNoMatch_aborted
#print axioms not_cliSpecPqNoMatch_alwaysAccept
#print axioms not_libsignalCliPqBinaryCorrect_nil
#print axioms cliPqBinaryCorrect_send_some

end CryptoVerification.SignalSession.NonVacuityPq
