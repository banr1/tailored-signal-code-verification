/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.LibsignalE2E.SchemeModel
public import LibsignalBinary.Specifications.SignalSession.PqDir

/-!
# Shared Non-Vacuity Witnesses

Provides a degenerate `PEParams` witness (`nonVacCommonPEParams`, whose `montToEd = none` makes
`ReachablePqxdhSession` empty so `SessionRecordCapInDomain` holds trivially), fresh Alice/Bob
`PqParty` directory witnesses (`session = none`, empty pre-key stores), and shared `CliMainSetupEnv` /
`CliMainEnv` helpers for the CLI non-vacuity proofs.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacCommon

open Arm64.Process (initFsState)
open CryptoGames (Party)
open CryptoGames.LibsignalSession (Crypto GhostState SignalMessage)
open CryptoVerification.E2E
  (LocalIdentity PEParams PqxdhPrims ReachablePqxdhSession RecordExtras
   blockLevelPrims initiateState modelPrims partyAddressName recvPrekeyState)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoVerification.LibsignalSpqrV1 (MlKem)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (Address Inputs PqParty PqxdhPartyInSpecDomain encodeDir fileCapBytes partyAddress textBytes)
open CryptoVerification.SignalSession.Cli (cliInputs utf8)
open CryptoVerification.SignalSession.Cli.Decimal.Helpers (decimalText_length_le)
open CryptoVerification.SignalSession.Cli.MainHops (RunCall cliIo)
open CryptoVerification.SignalSession.Cli.RunCompose (runFiles)
open CryptoVerification.SignalSession.CliExt (readFileResult)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs)
open LibsignalBinary.Heap.SpecBudget (ReadFileEnv allocBytes1Events readFileEnv_of_hook)
open LibsignalBinary.Proofs.PeakBudget.CliDomainCaps
  (PqPartyBaseKeysCap SessionRecordCapInDomain)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
  (CliMainEnv CliMainSetupEnv M1PhaseEnv M2CollectEnv M3PhaseEnv M5PhaseEnv M6Env)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOpenedEnv R0OpenedEnv RunArmEnv cliRunOfR0Env_of_r0_arm)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (sessionCapBytes)

/-! ## 1. Degenerate `PEParams` Witness & Empty `ReachablePqxdhSession` -/

def nonVacCommonMlKem : MlKem where
  keyPair := fun _ => List.Vector.replicate 2400 0#8
  encaps1 := fun _ _ => none
  encaps2 := fun _ _ => List.Vector.replicate 128 0#8
  decaps := fun _ _ _ => List.Vector.replicate 32 0#8
  validPk := fun _ _ => false

def nonVacCommonCrypto : Crypto where
  F := fun s _ => s
  E := fun _ b => b
  D := fun _ b => b
  X := fun _ _ => List.Vector.replicate 32 0#8
  pubKey := fun _ => List.Vector.replicate 32 0#8

def nonVacCommonPqxdhPrims : PqxdhPrims where
  F512 := fun s _ => s
  montToEd := fun _ _ => none
  compress := fun _ => List.Vector.replicate 32 0#8
  edNeg := fun _ => List.Vector.replicate 160 0#8
  isTorsionFree := fun _ => false
  dsmb := fun _ _ _ => List.Vector.replicate 160 0#8
  scalarMod := fun _ => List.Vector.replicate 32 0#8
  scalarWide := fun _ => List.Vector.replicate 32 0#8
  encaps := fun _ _ => (List.Vector.replicate 1568 0#8, List.Vector.replicate 32 0#8)
  decaps := fun _ _ => List.Vector.replicate 32 0#8
  K := nonVacCommonMlKem

/-- Concrete `PEParams` witness whose `montToEd = none` rejects every handshake (`ReachablePqxdhSession`
is empty, so `SessionRecordCapInDomain` holds with zero model assumptions). -/
def nonVacCommonPEParams : PEParams where
  C := nonVacCommonCrypto
  Q := nonVacCommonPqxdhPrims

theorem nonVacCommonPEParams_not_reachable
    {me : LocalIdentity}
    {x : RecordExtras}
    {g : GhostState (List (BitVec 8))}
    (hr : ReachablePqxdhSession nonVacCommonPEParams me x g) : False := by
  induction hr with
  | initiate X P me' b t x' g' hinit =>
    have hsig : ∀ pk msg sig,
        (modelPrims X nonVacCommonPEParams).sigVerify pk msg sig = false := by
      intro pk msg sig
      unfold modelPrims SignalPqxdh.xeddsaVerifyRef
        blockLevelPrims nonVacCommonPEParams nonVacCommonPqxdhPrims
      dsimp only
      split <;> rfl
    unfold initiateState SignalPqxdh.Model.initiateKeys at hinit
    simp [hsig] at hinit
  | recvPrekey X P me' k m rc x' g' pt hrecv =>
    have hcan : ∀ pk,
        (modelPrims X nonVacCommonPEParams).isCanonical pk = false := by
      intro pk
      unfold modelPrims SignalPqxdh.isCanonicalRef
        blockLevelPrims nonVacCommonPEParams nonVacCommonPqxdhPrims
      dsimp only
      split <;> rfl
    have hacc : ∀ inp,
        SignalPqxdh.Model.acceptKeys (modelPrims X nonVacCommonPEParams) inp = none := by
      intro inp
      unfold SignalPqxdh.Model.acceptKeys
      simp [hcan]
    unfold recvPrekeyState at hrecv
    cases htry : SignalMessage.tryFrom protoSignalCodec m.inner with
    | error _ =>
      rw [htry] at hrecv
      nomatch hrecv
    | ok inner =>
      rw [htry] at hrecv
      dsimp only at hrecv
      split at hrecv
      · nomatch hrecv
      · rw [hacc] at hrecv
        nomatch hrecv
  | send _ _ _ _ ih => exact ih
  | recv _ _ _ ih => exact ih

/-- `SessionRecordCapInDomain nonVacCommonPEParams sessionCapBytes` holds unconditionally. -/
theorem nonVacCommonSessionCap : SessionRecordCapInDomain nonVacCommonPEParams sessionCapBytes :=
  fun _ _ _ hr => False.elim (nonVacCommonPEParams_not_reachable hr)

/-! ## 2. Fresh Alice/Bob `PqParty` Directory Witnesses (`session = none`) -/

/-- Fresh party directory witness (`session = none`, empty pre-key stores) for party `p`. -/
def nonVacCommonPartyOf (p : Party) : PqParty where
  party := p
  me := ⟨List.Vector.replicate 32 0#8, 0#32⟩
  peerId := none
  session := none
  signed := []
  oneTime := []
  kyberOneTime := []
  kyberLastResort := []

/-- Fresh Alice directory witness (`party = .A`, peer `.B`). -/
abbrev nonVacCommonAliceParty : PqParty := nonVacCommonPartyOf .A

/-- Fresh Bob directory witness (`party = .B`, peer `.A`). -/
abbrev nonVacCommonBobParty : PqParty := nonVacCommonPartyOf .B

private def nonVacKutf8 (s : String) : List (BitVec 8) :=
  (s.toList.flatMap String.utf8EncodeChar).map fun b => BitVec.ofNat 8 b.toNat

private theorem nonVac_byteArray_toList_eq_data : ∀ (bs : ByteArray), bs.toList = bs.data.toList
  | ⟨⟨xs⟩⟩ => by
    have hloop : ∀ i r, ByteArray.toList.loop ⟨⟨xs⟩⟩ i r = r.reverse ++ xs.drop i := by
      intro i r
      fun_induction ByteArray.toList.loop ⟨⟨xs⟩⟩ i r with
      | case1 i r hi ih =>
        have hget : (ByteArray.mk ⟨xs⟩).get! i = xs[i] := getElem!_pos (⟨xs⟩ : Array UInt8) i hi
        rw [ih, hget, List.reverse_cons, List.append_assoc, List.singleton_append,
          List.drop_eq_getElem_cons hi]
      | case2 i r hni =>
        rw [List.drop_eq_nil_of_le (Nat.le_of_not_lt hni), List.append_nil]
    exact hloop 0 []

private theorem nonVac_utf8_eq_kutf8 (s : String) :
    utf8 s = nonVacKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [utf8, nonVacKutf8, List.utf8Encode, nonVac_byteArray_toList_eq_data]

private theorem nonVac_repr_utf8_eq_kutf8 (s : String) :
    CryptoVerification.LibsignalTripleRatchetRepr.utf8 s = nonVacKutf8 s := by
  obtain ⟨l, rfl⟩ := s.exists_eq_ofList
  simp [CryptoVerification.LibsignalTripleRatchetRepr.utf8, nonVacKutf8, List.utf8Encode,
    nonVac_byteArray_toList_eq_data]

theorem nonVacCommonParty_inSpecDomain (p : Party) :
    PqxdhPartyInSpecDomain nonVacCommonPEParams (nonVacCommonPartyOf p) := by
  refine ⟨?_, ?_, List.nodup_nil, List.nodup_nil, List.nodup_nil, List.nodup_nil⟩
  · intro _ _ hs
    nomatch hs
  · intro f hf
    have hle : f.2.length ≤ fileCapBytes := by
      unfold encodeDir nonVacCommonPartyOf nonVacCommonPEParams nonVacCommonCrypto at hf
      simp only [List.map_nil, List.flatten_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hf
      unfold fileCapBytes
      rcases hf with rfl | rfl | rfl
      · dsimp only
        unfold textBytes partyAddress Address.text
        dsimp only
        rw [nonVac_repr_utf8_eq_kutf8]
        have hk_app (a b : String) : nonVacKutf8 (a ++ b) = nonVacKutf8 a ++ nonVacKutf8 b := by
          simp [nonVacKutf8, String.toList_append, List.flatMap_append]
        rw [hk_app, hk_app, List.length_append, List.length_append]
        have hd : (nonVacKutf8 (toString (1 : Nat))).length ≤ 1 := by
          rw [← nonVac_utf8_eq_kutf8]
          exact decimalText_length_le 1 1 (by omega) (by omega)
        have hdot : (nonVacKutf8 ".").length = 1 := rfl
        have hp : (nonVacKutf8 (partyAddressName p)).length = 36 := by
          cases p <;> rfl
        omega
      · decide
      · decide
    refine ⟨?_, fun _ => hle⟩
    unfold fileCapBytes at hle
    omega

theorem nonVacCommonAliceParty_inSpecDomain :
    PqxdhPartyInSpecDomain nonVacCommonPEParams nonVacCommonAliceParty :=
  nonVacCommonParty_inSpecDomain .A

theorem nonVacCommonBobParty_inSpecDomain :
    PqxdhPartyInSpecDomain nonVacCommonPEParams nonVacCommonBobParty :=
  nonVacCommonParty_inSpecDomain .B

theorem nonVacCommonParty_baseKeysCap (p : Party) :
    PqPartyBaseKeysCap sessionCapBytes (nonVacCommonPartyOf p) := by
  intro _ _ _ hmem
  nomatch hmem

theorem nonVacCommonAliceParty_baseKeysCap :
    PqPartyBaseKeysCap sessionCapBytes nonVacCommonAliceParty :=
  nonVacCommonParty_baseKeysCap .A

theorem nonVacCommonBobParty_baseKeysCap :
    PqPartyBaseKeysCap sessionCapBytes nonVacCommonBobParty :=
  nonVacCommonParty_baseKeysCap .B

/-! ## 3. Shared `CliMainSetupEnv` & `CliMainEnv` Plumbing -/

/-- Phase-M3 `"coins"` `read_file` allocation trace on `i`. -/
def nonVacCoinsEvents (i : Inputs) : List AllocEvent :=
  match readFileResult (initFsState (cliInputs i)).files (utf8 "coins") with
  | Except.ok bs => allocBytes1Events bs
  | Except.error () => []

theorem nonVacCoinsEvents_readFileEnv (i : Inputs) :
    ReadFileEnv (initFsState (cliInputs i)).files (utf8 "coins") (nonVacCoinsEvents i) := by
  refine readFileEnv_of_hook _ _ ?_
  unfold nonVacCoinsEvents
  cases readFileResult (initFsState (cliInputs i)).files (utf8 "coins") with
  | ok _ => rfl
  | error u => cases u; rfl

theorem cliMainSetupEnv_nonVac_len2 (i : Inputs) (hlen : i.argv.length = 2) :
    CliMainSetupEnv uuidTryParse i none false (nonVacCoinsEvents i) := by
  have hM1 : M1PhaseEnv i.argv.length [] := Or.inl rfl
  have hM2 : M2CollectEnv i.argv.length [] := by
    rw [hlen]
    exact Or.inr ⟨[], [], rfl, Or.inl rfl, Or.inr ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩
  have hM3 : M3PhaseEnv false i.stdin (initFsState (cliInputs i)).files (utf8 "coins")
      (nonVacCoinsEvents i) :=
    Or.inr ⟨[], nonVacCoinsEvents i, rfl, rfl,
      Or.inr ⟨nonVacCoinsEvents i, [], (List.append_nil _).symm,
        nonVacCoinsEvents_readFileEnv i, FreeOnlyEvs.nil⟩⟩
  exact Or.inr ⟨[], nonVacCoinsEvents i, rfl, hM1,
    Or.inr ⟨[], nonVacCoinsEvents i, rfl, hM2,
      Or.inr ⟨[], nonVacCoinsEvents i, rfl, rfl, hM3⟩⟩⟩

theorem cliMainSetupEnv_nonVac_len3 (i : Inputs) (hlen : i.argv.length = 3) :
    CliMainSetupEnv uuidTryParse i none false (nonVacCoinsEvents i) := by
  have hM1 : M1PhaseEnv i.argv.length [] := Or.inl rfl
  have hM2 : M2CollectEnv i.argv.length [] := by
    rw [hlen]
    exact Or.inr ⟨[], [], rfl, Or.inl rfl,
      Or.inr ⟨[], [], rfl, Or.inl rfl,
        Or.inr ⟨[], [], rfl, Or.inl rfl, rfl⟩⟩⟩
  have hM3 : M3PhaseEnv false i.stdin (initFsState (cliInputs i)).files (utf8 "coins")
      (nonVacCoinsEvents i) :=
    Or.inr ⟨[], nonVacCoinsEvents i, rfl, rfl,
      Or.inr ⟨nonVacCoinsEvents i, [], (List.append_nil _).symm,
        nonVacCoinsEvents_readFileEnv i, FreeOnlyEvs.nil⟩⟩
  exact Or.inr ⟨[], nonVacCoinsEvents i, rfl, hM1,
    Or.inr ⟨[], nonVacCoinsEvents i, rfl, hM2,
      Or.inr ⟨[], nonVacCoinsEvents i, rfl, rfl, hM3⟩⟩⟩

theorem cliMainEnv_of_setup_and_runArm
    {E : RunCall → CliRunCalleeEnvs} {g : RunCall}
    {evsSetup evsArm : List AllocEvent}
    (hSetup : CliMainSetupEnv uuidTryParse g.i none false evsSetup)
    (hArm : RunArmEnv cliIo.rd (runFiles g.i) (E g) sessionCapBytes g.i.stdin g.c evsArm) :
    CliMainEnv uuidTryParse
      (fun g' => CliRunOpenedEnv cliIo.rd (E g') sessionCapBytes g')
      g none false [] false (evsSetup ++ evsArm) := by
  have hRun : CliRunOpenedEnv cliIo.rd (E g) sessionCapBytes g evsArm := by
    simpa only [List.nil_append] using
      (cliRunOfR0Env_of_r0_arm
        (R0StageEnv := R0OpenedEnv cliIo.rd (runFiles g.i))
        (Or.inl FreeOnlyEvs.nil) hArm)
  have hM5 : M5PhaseEnv [] [] :=
    Or.inr ⟨[], [], rfl, rfl, FreeOnlyEvs.nil⟩
  have hM6 : M6Env false [] :=
    Or.inr ⟨[], [], rfl, rfl, FreeOnlyEvs.nil⟩
  exact Or.inr ⟨evsSetup, evsArm, rfl, hSetup,
    Or.inr (Or.inr ⟨evsArm, [], (List.append_nil _).symm, hRun,
      Or.inr ⟨[], [], rfl, hM5, hM6⟩⟩)⟩

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacCommon
