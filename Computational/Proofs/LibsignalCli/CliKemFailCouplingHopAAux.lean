/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs
public import Computational.Proofs.SpecLemmas.Game.StatementPq
import Computational.Proofs.LibsignalCli.Oom.Faithful

/-!
# Retained-directory log projection for send-coin coupling

Defines the send-coin-logged retained-directory game `dirPqExpCoinLogged` and shows that
projecting `cliPqxdhExpFlagged`'s input log with `sendTapesOfInputs` matches mapping
`dirPqExpCoinLogged`'s coin log with `coinBytes` (`DEV-CLI18`).
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.LibsignalCli.CliKemFailCouplingHopAAux

open OracleComp OracleSpec
open CryptoGames (Party SMSchemeR SMSchemeR.sendPart)
open CryptoGames.CBC (Plain)
open CryptoGames.LibsignalSession (PublicKey)
open CryptoGames.SM (ConfigR GameState)
open CryptoVerification.LibsignalSpqrV1 (coinBytes)
open CryptoVerification.SignalSession (CliRun Inputs PqParty pqInitInputs)
open CryptoVerification.E2E (BHDrvM BHDrvMode BinState Bytes CliDriverState CliDrvM CliDrvMT
  CliGameAdversary CliPartyState Dir.cliDrvCtl Dir.cliDrvImplM Dir.cliDrvSMM Dir.cliDrvStart
  Dir.cliDrvStartM Dir.cliPqInitM Dir.cliPqReceive Dir.cliPqReceiveM Dir.cliPqRecvM
  Dir.cliPqScheme Dir.cliPqSchemeM Dir.cliPqSend Dir.cliPqSendM Dir.cliRunStdSMM
  Dir.cliStepLocalSMM ModelDriverInstance ModelDriverInstanceMeta PEParams SMSchemeRM
  UnreachedPqxdhPrimitives allTestedSessionsFresh appendInitiateTape bhAlignTransForBob
  bhDecodePreKeyMsgE bhDrvGuard bhDrvInstClean bhDrvKeyInd bhExpectedPreKeyMsg bhHdrOfPreKeyMsg
  bhIdKeyOf bhInstIkACorrupted bhIsBobRecvSMQuery bhLiftCli bhLiftCliM bhMetaAfterSM
  bhNoExtWithSpqr bhPartneredInTransitA bhPartneredInnerBytes bhSmDefaultWithSpqr challRM
  cliConfigSpkS cliDrvCtl cliGameDrSpec cliGameSmSpec cliGameSpec cliMapGameState cliOracleImplRM
  cliPartyStateB0 cliPqLenOk cliPqRecvInp cliPqScheme cliPqSendInp cliPqSigsOf cliPqxdhExpFlagged
  cliRunLogged cliRunPure deliverRM driverSomeInstanceWon injectRM liftQueryImplStateT2 liftStateT
  mkBundleEStrict mkKeysEStrict mkMeEStrict modelPrims runCliDriverLogged smSchemeCoinLogged
  transmitRM wirePrekey wireWhisper)
open Computational.Proofs.LibsignalCli.Oom.Faithful (instLawfulMonadWriterTList)
open Computational.Proofs.LibsignalCli.CliKemFailCouplingDefs (CoinLogM cliDrvImplCoinLogged
  cliDrvSMCoinLogged cliPqExpProjCoinLogged cliRunStdSMCoinLogged cliStepLocalSMCoinLogged
  sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_cliPqRecvInp
  sendTapesOfInputs_cliPqSendInp sendTapesOfInputs_nil sendTapesOfInputs_pqInitInputs)

/-! ## Retained-directory send-coin game -/

private abbrev LogM : Type → Type := WriterT (List Inputs) ProbComp
private abbrev ByteLogM : Type → Type := WriterT (List (List (BitVec 8))) ProbComp

def dirRunStdSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    CliDrvMT S ℓ CoinLogM ((cliGameSmSpec ℓ (BitVec 512)).Range q) := do
  let scheme := smSchemeCoinLogged (Dir.cliPqScheme run ℓ bi (gs.st .A) (gs.st .B))
  let cfg := cliConfigSpkS (St := CliPartyState) (Msg := Plain ℓ) decT encT
  let gsIn : GameState CliPartyState (Plain ℓ) Bytes := match q with
    | .inl (.inl (.inr (.B, c))) => bhAlignTransForBob im.bobAccepted bi.meA.regId bi.hdr c gs
    | _ => gs
  let (r, gsOut) ←
    StateT.lift (StateT.lift ((cliOracleImplRM CliPartyState.bin scheme (2 + 1) qep cfg q).run gsIn))
  let gs' : GameState CliPartyState (Plain ℓ) Bytes := match q, r with
    | .inl (.inl (.inr (.B, c))), some (.accepted _ _ _) =>
      match gsIn.inTransit .A c with
      | some rMatched =>
        { gsOut with trans := gs.trans.filter (fun rec => rec.pos != rMatched.pos) }
      | none => { gsOut with trans := gs.trans }
    | .inl (.inl (.inr (.B, _))), _ => { gsOut with trans := gs.trans }
    | _, _ => gsOut
  let im' := bhMetaAfterSM ds.toModelDriverState bi im q r
  set { ds with bhInsts := ds.bhInsts.set i { bi with gs := some (cliMapGameState CliPartyState.bin gs') },
                instMeta := ds.instMeta.set i im',
                instGs := ds.instGs.set i (some gs') }
  return r

def dirStepLocalSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S)
    (gs : GameState CliPartyState (Plain ℓ) Bytes) :
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) →
      CliDrvMT S ℓ CoinLogM ((cliGameSmSpec ℓ (BitVec 512)).Range q)
  | .inl (.inl (.inr (.A, c))) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs (.inl (.inl (.inr (.A, c))))
  | .inl (.inr (.A, c)) => do
    if (bhDecodePreKeyMsgE c).isSome then return none
    else dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs (.inl (.inr (.A, c)))
  | .inl (.inl (.inr (.B, c))) => do
    if (bhPartneredInnerBytes im.bobAccepted bi.meA.regId bi.hdr c).isNone then return none
    else dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs (.inl (.inl (.inr (.B, c))))
  | .inl (.inr (.B, c)) => do
    if !im.bobAccepted then return none
    else if (bhPartneredInnerBytes true bi.meA.regId bi.hdr c).isNone ||
        bhPartneredInTransitA true bi.meA.regId bi.hdr c gs then return none
    else dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs (.inl (.inr (.B, c)))
  | q => dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs q

def dirDrvSMCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (CliDrvMT S ℓ CoinLogM)) :
    QueryImpl (cliGameDrSpec ℓ (BitVec 512)) (CliDrvMT S ℓ CoinLogM) := fun ⟨i, q⟩ => do
  let ds ← get
  if !bhDrvInstClean ds.toModelDriverState i then return bhSmDefaultWithSpqr q
  else
    match ds.bhInsts[i]?, ds.instMeta[i]? with
    | some bi, some im =>
      if !im.bobAccepted && bhIsBobRecvSMQuery q && bhInstIkACorrupted ds.toModelDriverState bi then
        let imCorr : ModelDriverInstanceMeta S := { im with bobAccepted := true, ikACorrAtAccept := true }
        set { ds with instMeta := ds.instMeta.set i imCorr }; return bhSmDefaultWithSpqr q
      else
        match ds.instGs[i]? with
        | some (some gs) => dirStepLocalSMCoinLogged S ℓ run qep decT encT ds i bi im gs q
        | _ =>
          let r ← ext q
          set { ds with instMeta := ds.instMeta.set i (bhMetaAfterSM ds.toModelDriverState bi im q r) }; return r
    | _, _ => return bhSmDefaultWithSpqr q

def dirDrvImplCoinLogged (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (CliDrvM S ℓ)) (mode : BHDrvMode S) :
    QueryImpl (cliGameSpec S ℓ (BitVec 512)) (CliDrvMT S ℓ CoinLogM) :=
  (QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S ℓ CoinLogM) +
    liftQueryImplStateT2 (n := CoinLogM) (fun q => bhLiftCli (bhDrvKeyInd S ℓ P false q)) +
    liftQueryImplStateT2 (n := CoinLogM) (Dir.cliDrvCtl S ℓ P run W mode) +
    dirDrvSMCoinLogged S ℓ run qep decT encT (liftQueryImplStateT2 (n := CoinLogM) ext)

/-- Retained-directory counterpart of `cliPqExpProjCoinLogged` over `CoinLogM`. -/
def dirPqExpCoinLogged (S : SignalPqxdh.Setup) (run : CliRun) (X : UnreachedPqxdhPrimitives)
    (W : PEParams) (ℓ qep : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) : ProbComp (Bool × List (BitVec 512)) :=
  WriterT.run do
    let P := modelPrims X W
    let b ← liftM ($ᵗ Bool : ProbComp Bool)
    let ((b', ds), st) ←
      (((simulateQ (dirDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr
          (fun _ _ _ _ _ => some b)) A.run).run {}).run (SignalPqxdh.KeyIndState.empty S true))
    if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
    else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b)

/-! ## Monad-homomorphism log projection -/

private def mapLogW {ω₁ ω₂ α : Type} (φ : List ω₁ → List ω₂)
    (m : WriterT (List ω₁) ProbComp α) : WriterT (List ω₂) ProbComp α :=
  WriterT.mk (Prod.map id φ <$> m.run)

@[simp] private theorem mapLogW_run {ω₁ ω₂ α : Type} (φ : List ω₁ → List ω₂)
    (m : WriterT (List ω₁) ProbComp α) :
    (mapLogW φ m).run = Prod.map id φ <$> m.run := rfl

private theorem mapLogW_pure {ω₁ ω₂ α : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = []) (a : α) :
    mapLogW φ (pure a) = pure a := by
  show (mapLogW φ (pure a)).run = (pure a : WriterT (List ω₂) ProbComp α).run
  simp [mapLogW, hnil]

private theorem mapLogW_map {ω₁ ω₂ α β : Type} (φ : List ω₁ → List ω₂) (f : α → β)
    (m : WriterT (List ω₁) ProbComp α) :
    mapLogW φ (f <$> m) = f <$> mapLogW φ m := by
  show (mapLogW φ (f <$> m)).run = (f <$> mapLogW φ m).run
  simp [mapLogW, Functor.map_map]

private theorem mapLogW_bind {ω₁ ω₂ α β : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys)
    (m : WriterT (List ω₁) ProbComp α) (k : α → WriterT (List ω₁) ProbComp β) :
    mapLogW φ (m >>= k) = mapLogW φ m >>= fun a => mapLogW φ (k a) := by
  show (mapLogW φ (m >>= k)).run = (mapLogW φ m >>= fun a => mapLogW φ (k a)).run
  simp [mapLogW, map_eq_bind_pure_comp, bind_assoc, happ]

private theorem mapLogW_liftM {ω₁ ω₂ α : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = [])
    (c : ProbComp α) :
    mapLogW φ (liftM c) = liftM c := by
  show (mapLogW φ (liftM c)).run = (liftM c : WriterT (List ω₂) ProbComp α).run
  dsimp [mapLogW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [Functor.map_map, hnil]

private def mapLogS1 {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (m : StateT σ (WriterT (List ω₁) ProbComp) α) :
    StateT σ (WriterT (List ω₂) ProbComp) α :=
  fun s => mapLogW φ (m.run s)

@[simp] private theorem mapLogS1_run {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (m : StateT σ (WriterT (List ω₁) ProbComp) α) (s : σ) :
    (mapLogS1 φ m).run s = mapLogW φ (m.run s) := rfl

private theorem mapLogS1_pure {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = [])
    (a : α) :
    mapLogS1 φ (pure a : StateT σ (WriterT (List ω₁) ProbComp) α) = pure a := by
  ext s; simp [mapLogW_pure φ hnil]

private theorem mapLogS1_map {ω₁ ω₂ σ α β : Type} (φ : List ω₁ → List ω₂) (f : α → β)
    (m : StateT σ (WriterT (List ω₁) ProbComp) α) :
    mapLogS1 φ (f <$> m) = f <$> mapLogS1 φ m := by
  ext s; simp [StateT.run_map, mapLogW_map]

private theorem mapLogS1_bind {ω₁ ω₂ σ α β : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys)
    (m : StateT σ (WriterT (List ω₁) ProbComp) α)
    (k : α → StateT σ (WriterT (List ω₁) ProbComp) β) :
    mapLogS1 φ (m >>= k) = mapLogS1 φ m >>= fun a => mapLogS1 φ (k a) := by
  ext s; simp [mapLogW_bind φ happ]

private theorem mapLogS1_get {ω₁ ω₂ σ : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = []) :
    mapLogS1 φ (get : StateT σ (WriterT (List ω₁) ProbComp) σ) = get := by
  ext s; simp [mapLogW_pure φ hnil]

private theorem mapLogS1_set {ω₁ ω₂ σ : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = [])
    (s' : σ) :
    mapLogS1 φ (set s' : StateT σ (WriterT (List ω₁) ProbComp) PUnit) = set s' := by
  ext s; simp [mapLogW_pure φ hnil]

private theorem mapLogS1_lift {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (m : WriterT (List ω₁) ProbComp α) :
    mapLogS1 φ (StateT.lift m : StateT σ (WriterT (List ω₁) ProbComp) α) =
      StateT.lift (mapLogW φ m) := by
  have _ := happ; have _ := hnil
  ext s; simp [StateT.run_lift]

private theorem mapLogS1_liftM_prob {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (c : ProbComp α) :
    mapLogS1 φ (liftM c : StateT σ (WriterT (List ω₁) ProbComp) α) = liftM c := by
  change mapLogS1 φ (StateT.lift (liftM c)) = StateT.lift (liftM c)
  rw [mapLogS1_lift φ happ hnil, mapLogW_liftM φ hnil]

private theorem mapLogS1_liftStateT {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (hnil : φ [] = []) (x : StateT σ ProbComp α) :
    mapLogS1 φ (liftStateT (n := WriterT (List ω₁) ProbComp) x) =
      liftStateT (n := WriterT (List ω₂) ProbComp) x := by
  ext s; exact mapLogW_liftM φ hnil (x s)

private theorem mapLogS1_ite {ω₁ ω₂ σ α : Type} (φ : List ω₁ → List ω₂)
    (c : Prop) [Decidable c]
    (t e : StateT σ (WriterT (List ω₁) ProbComp) α) :
    mapLogS1 φ (if c then t else e) = if c then mapLogS1 φ t else mapLogS1 φ e := by
  split_ifs <;> rfl

private def mapLogS2 {ω₁ ω₂ σ₁ σ₂ α : Type} (φ : List ω₁ → List ω₂)
    (m : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) :
    StateT σ₁ (StateT σ₂ (WriterT (List ω₂) ProbComp)) α :=
  fun s₁ => mapLogS1 φ (m.run s₁)

@[simp] private theorem mapLogS2_run {ω₁ ω₂ σ₁ σ₂ α : Type} (φ : List ω₁ → List ω₂)
    (m : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) (s₁ : σ₁) :
    (mapLogS2 φ m).run s₁ = mapLogS1 φ (m.run s₁) := rfl

private theorem mapLogS2_pure {ω₁ ω₂ σ₁ σ₂ α : Type} (φ : List ω₁ → List ω₂)
    (hnil : φ [] = []) (a : α) :
    mapLogS2 φ (pure a : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) = pure a := by
  ext s₁; simp [mapLogS1_pure φ hnil]

private theorem mapLogS2_map {ω₁ ω₂ σ₁ σ₂ α β : Type} (φ : List ω₁ → List ω₂) (f : α → β)
    (m : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) :
    mapLogS2 φ (f <$> m) = f <$> mapLogS2 φ m := by
  ext s₁; simp [StateT.run_map, mapLogS1_map]

private theorem mapLogS2_bind {ω₁ ω₂ σ₁ σ₂ α β : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys)
    (m : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α)
    (k : α → StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) β) :
    mapLogS2 φ (m >>= k) = mapLogS2 φ m >>= fun a => mapLogS2 φ (k a) := by
  ext s₁; simp [mapLogS1_bind φ happ]

private theorem mapLogS2_get {ω₁ ω₂ σ₁ σ₂ : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = []) :
    mapLogS2 φ (get : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) σ₁) = get := by
  ext s₁; simp [mapLogS1_pure φ hnil]

private theorem mapLogS2_set {ω₁ ω₂ σ₁ σ₂ : Type} (φ : List ω₁ → List ω₂) (hnil : φ [] = [])
    (s₁' : σ₁) :
    mapLogS2 φ (set s₁' : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) PUnit) = set s₁' := by
  ext s₁; simp [mapLogS1_pure φ hnil]

private theorem mapLogS2_lift {ω₁ ω₂ σ₁ σ₂ α : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (m : StateT σ₂ (WriterT (List ω₁) ProbComp) α) :
    mapLogS2 φ (StateT.lift m : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) =
      StateT.lift (mapLogS1 φ m) := by
  have _ := happ; have _ := hnil
  ext s₁; simp [StateT.run_lift]

private theorem mapLogS2_liftM_prob {ω₁ ω₂ σ₁ σ₂ α : Type} (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (c : ProbComp α) :
    mapLogS2 φ (liftM c : StateT σ₁ (StateT σ₂ (WriterT (List ω₁) ProbComp)) α) = liftM c := by
  change mapLogS2 φ (StateT.lift (liftM c)) = StateT.lift (liftM c)
  rw [mapLogS2_lift φ happ hnil, mapLogS1_liftM_prob φ happ hnil]

private theorem mapLogS2_liftQueryImplStateT2 {ι ω₁ ω₂ σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (φ : List ω₁ → List ω₂) (hnil : φ [] = [])
    (h : QueryImpl spec (StateT σ₁ (StateT σ₂ ProbComp))) (q : spec.Domain) :
    mapLogS2 φ (liftQueryImplStateT2 (n := WriterT (List ω₁) ProbComp) h q) =
      liftQueryImplStateT2 (n := WriterT (List ω₂) ProbComp) h q := by
  ext s₁ s₂; exact mapLogW_liftM φ hnil (((h q).run s₁).run s₂)

private def mapLogScheme {ω₁ ω₂ Key St Msg Coins RCoins C : Type}
    (φ : List ω₁ → List ω₂)
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St Msg Coins RCoins C) :
    SMSchemeRM (WriterT (List ω₂) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send s m rs := mapLogW φ (sm.send s m rs)
  receive s c rc := mapLogW φ (sm.receive s c rc)

private theorem mapLogS1_transmitRM {ω₁ ω₂ Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × Msg × Option Coins) :
    mapLogS1 φ (transmitRM sm Δ qep cfg q) = transmitRM (mapLogScheme φ sm) Δ qep cfg q := by
  rcases q with ⟨P, m, r⟩
  unfold transmitRM
  simp only [mapLogS1_bind φ happ, mapLogS1_get φ hnil]
  congr 1; funext s
  cases cfg.sendOK s P
  · simp [mapLogS1_pure φ hnil]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil,
        mapLogW_liftM φ hnil]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact mapLogS1_pure φ hnil _
      | some s₁ =>
        simp [mapLogScheme, mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil,
          mapLogS1_map φ, mapLogS1_set φ hnil]
    · simp [mapLogS1_pure φ hnil]

private theorem mapLogS1_challRM {ω₁ ω₂ Key St Msg Coins RCoins C : Type}
    [SampleableType Coins] (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × Msg × Msg × Option Coins) :
    mapLogS1 φ (challRM sm Δ qep cfg q) = challRM (mapLogScheme φ sm) Δ qep cfg q := by
  rcases q with ⟨P, m₀, m₁, r⟩
  unfold challRM
  simp only [mapLogS1_bind φ happ, mapLogS1_get φ hnil]
  congr 1; funext s
  cases cfg.sendOK s P
  · simp [mapLogS1_pure φ hnil]
  · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    cases s.win
    · simp only [Bool.false_eq_true, ↓reduceIte, mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil,
        mapLogW_liftM φ hnil]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact mapLogS1_pure φ hnil _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
        · simp [mapLogScheme, mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil,
            mapLogS1_map φ, mapLogS1_set φ hnil]
        · simp [mapLogS1_pure φ hnil]
    · simp [mapLogS1_pure φ hnil]

private theorem mapLogS1_deliverRM {ω₁ ω₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St Msg Coins RCoins C)
    (cfg : ConfigR St Msg C) (q : Party × C) :
    mapLogS1 φ (deliverRM sm cfg q) = deliverRM (mapLogScheme φ sm) cfg q := by
  rcases q with ⟨P, c⟩
  unfold deliverRM
  simp only [mapLogS1_bind φ happ, mapLogS1_get φ hnil]
  congr 1; funext s
  cases s.win
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases s.inTransit P.other c with
    | none => exact mapLogS1_pure φ hnil _
    | some r =>
      dsimp only
      simp only [mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil, mapLogW_liftM φ hnil]
      congr 1; funext rc
      dsimp only [mapLogScheme]
      congr 1; funext out
      cases out with
      | none =>
        dsimp only
        split_ifs
        · rw [mapLogS1_bind φ happ, mapLogS1_set φ hnil]
          exact congrArg _ (funext fun _ => mapLogS1_pure φ hnil _)
        · exact mapLogS1_pure φ hnil _
      | some x =>
        rcases x with ⟨st', t', i', m'⟩
        dsimp only
        split_ifs <;>
          (rw [mapLogS1_bind φ happ, mapLogS1_set φ hnil]
           exact congrArg _ (funext fun _ => mapLogS1_pure φ hnil _))
  · simp [mapLogS1_pure φ hnil]

private theorem mapLogS1_injectRM {ω₁ ω₂ Key St Msg Coins RCoins C : Type}
    [DecidableEq C] [SampleableType RCoins]
    (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : Party × C) :
    mapLogS1 φ (injectRM sm Δ qep cfg q) = injectRM (mapLogScheme φ sm) Δ qep cfg q := by
  rcases q with ⟨P, c⟩
  unfold injectRM
  simp only [mapLogS1_bind φ happ, mapLogS1_get φ hnil]
  congr 1; funext s
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c))
  · simp only [Bool.false_eq_true, ↓reduceIte, mapLogS1_bind φ happ, mapLogS1_lift φ happ hnil,
      mapLogW_liftM φ hnil]
    congr 1; funext rc
    dsimp only [mapLogScheme]
    congr 1; funext out
    cases out with
    | none => exact mapLogS1_pure φ hnil _
    | some x =>
      rcases x with ⟨st', t', i', m'⟩
      dsimp only
      split_ifs
      · exact mapLogS1_pure φ hnil _
      · rw [mapLogS1_bind φ happ, mapLogS1_set φ hnil]
        exact congrArg _ (funext fun _ => mapLogS1_pure φ hnil _)
      · rw [mapLogS1_bind φ happ, mapLogS1_set φ hnil]
        exact congrArg _ (funext fun _ => mapLogS1_pure φ hnil _)
      · exact mapLogS1_pure φ hnil _
  · simp [mapLogS1_pure φ hnil]

private theorem mapLogS1_cliOracleImplRM {ω₁ ω₂ Key St' St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (φ : List ω₁ → List ω₂)
    (happ : ∀ xs ys, φ (xs ++ ys) = φ xs ++ φ ys) (hnil : φ [] = [])
    (proj : St' → St)
    (sm : SMSchemeRM (WriterT (List ω₁) ProbComp) Key St' Msg Coins RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St' Msg C)
    (q : (CryptoGames.SM.spec St Msg Coins C).Domain) :
    mapLogS1 φ (cliOracleImplRM proj sm Δ qep cfg q) =
      cliOracleImplRM proj (mapLogScheme φ sm) Δ qep cfg q := by
  rcases q with (((q₁ | q₂) | q₃) | q₄) | q₅
  · exact mapLogS1_transmitRM φ happ hnil sm Δ qep cfg q₁
  · exact mapLogS1_challRM φ happ hnil sm Δ qep cfg q₂
  · exact mapLogS1_deliverRM φ happ hnil sm cfg q₃
  · exact mapLogS1_injectRM φ happ hnil sm Δ qep cfg q₄
  · exact mapLogS1_liftStateT φ hnil _

private theorem mapLogScheme_cliPqSchemeM_eq (run : CliRun) (ℓ : ℕ)
    {S : SignalPqxdh.Setup} {ℓ' : ℕ} (bi : ModelDriverInstance S ℓ')
    (stA0 stB0 : CliPartyState) :
    mapLogScheme sendTapesOfInputs (Dir.cliPqSchemeM (cliRunLogged run) ℓ bi stA0 stB0) =
      mapLogScheme (List.map coinBytes) (smSchemeCoinLogged (Dir.cliPqScheme run ℓ bi stA0 stB0)) := by
  unfold mapLogScheme
  dsimp only [Dir.cliPqSchemeM, smSchemeCoinLogged, Dir.cliPqScheme]
  congr 1
  · funext s m rs
    show (mapLogW sendTapesOfInputs (Dir.cliPqSendM (cliRunLogged run) s m.toList rs)).run =
      (mapLogW (List.map coinBytes)
        (MonadWriter.tell [rs] >>= fun _ => pure (Dir.cliPqSend run s m.toList rs))).run
    simp [mapLogW, Dir.cliPqSendM, cliRunLogged]
    rfl
  · funext s c rc
    show (mapLogW sendTapesOfInputs (Dir.cliPqReceiveM (cliRunLogged run) ℓ bi s c rc)).run =
      (mapLogW (List.map coinBytes) (pure (Dir.cliPqReceive run ℓ bi s c rc))).run
    dsimp only [Dir.cliPqReceiveM, Dir.cliPqReceive]
    cases cliPqLenOk c with
    | false => simp [mapLogW]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases s.bin.party with
      | A =>
        dsimp only
        split_ifs
        · simp [mapLogW]
        · simp [mapLogW, Dir.cliPqRecvM, cliRunLogged]
          rfl
      | B =>
        dsimp only
        cases bhDecodePreKeyMsgE c with
        | none =>
          dsimp only
          split_ifs
          · simp [mapLogW]
          · simp [mapLogW, Dir.cliPqRecvM, cliRunLogged]
            rfl
          · simp [mapLogW]
        | some m =>
          dsimp only
          split_ifs <;> simp [mapLogW, Dir.cliPqRecvM, cliRunLogged] <;> rfl

private theorem mapLogS2_cliRunStdSMM_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    mapLogS2 sendTapesOfInputs (Dir.cliRunStdSMM S ℓ (cliRunLogged run) qep decT encT ds i bi im gs q) =
      mapLogS2 (List.map coinBytes) (dirRunStdSMCoinLogged S ℓ run qep decT encT ds i bi im gs q) := by
  unfold Dir.cliRunStdSMM dirRunStdSMCoinLogged
  simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
    mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
    mapLogS1_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
    mapLogS2_bind (List.map coinBytes) (fun xs ys => List.map_append),
    mapLogS2_lift (List.map coinBytes) (fun xs ys => List.map_append) List.map_nil,
    mapLogS1_lift (List.map coinBytes) (fun xs ys => List.map_append) List.map_nil,
    ← mapLogS1_run,
    mapLogS1_cliOracleImplRM sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
    mapLogS1_cliOracleImplRM (List.map coinBytes) (fun xs ys => List.map_append) List.map_nil,
    mapLogScheme_cliPqSchemeM_eq]
  congr 1

private theorem mapLogS2_cliStepLocalSMM_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ds : CliDriverState S ℓ) (i : ℕ) (bi : ModelDriverInstance S ℓ)
    (im : ModelDriverInstanceMeta S) (gs : GameState CliPartyState (Plain ℓ) Bytes)
    (q : (cliGameSmSpec ℓ (BitVec 512)).Domain) :
    mapLogS2 sendTapesOfInputs (Dir.cliStepLocalSMM S ℓ (cliRunLogged run) qep decT encT ds i bi im gs q) =
      mapLogS2 (List.map coinBytes) (dirStepLocalSMCoinLogged S ℓ run qep decT encT ds i bi im gs q) := by
  rcases q with (((q₁ | q₂) | ⟨p, c⟩) | ⟨p, c⟩) | q₅
  · exact mapLogS2_cliRunStdSMM_eq S ℓ run qep decT encT ds i bi im gs _
  · exact mapLogS2_cliRunStdSMM_eq S ℓ run qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [Dir.cliStepLocalSMM, dirStepLocalSMCoinLogged] <;> split_ifs <;>
      first | rfl | exact mapLogS2_cliRunStdSMM_eq S ℓ run qep decT encT ds i bi im gs _
  · cases p <;> dsimp only [Dir.cliStepLocalSMM, dirStepLocalSMCoinLogged] <;> split_ifs <;>
      first | rfl | exact mapLogS2_cliRunStdSMM_eq S ℓ run qep decT encT ds i bi im gs _
  · exact mapLogS2_cliRunStdSMM_eq S ℓ run qep decT encT ds i bi im gs _

private theorem mapLogS2_cliDrvSMM_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (run : CliRun) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (CliDrvM S ℓ))
    (q : (cliGameDrSpec ℓ (BitVec 512)).Domain) :
    mapLogS2 sendTapesOfInputs (Dir.cliDrvSMM S ℓ (cliRunLogged run) qep decT encT
        (liftQueryImplStateT2 (n := LogM) ext) q) =
      mapLogS2 (List.map coinBytes) (dirDrvSMCoinLogged S ℓ run qep decT encT
        (liftQueryImplStateT2 (n := CoinLogM) ext) q) := by
  rcases q with ⟨i, sq⟩
  dsimp only [Dir.cliDrvSMM, dirDrvSMCoinLogged]
  simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
    mapLogS2_get sendTapesOfInputs sendTapesOfInputs_nil,
    mapLogS2_bind (List.map coinBytes) (fun xs ys => List.map_append),
    mapLogS2_get (List.map coinBytes) List.map_nil]
  congr 1; funext ds
  split_ifs
  · rfl
  · cases ds.bhInsts[i]? with
    | none => rfl
    | some bi =>
      cases ds.instMeta[i]? with
      | none => rfl
      | some im =>
        dsimp only
        split_ifs
        · rfl
        · cases ds.instGs[i]? with
          | none =>
            simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
              mapLogS2_liftQueryImplStateT2 sendTapesOfInputs sendTapesOfInputs_nil,
              mapLogS2_bind (List.map coinBytes) (fun xs ys => List.map_append),
              mapLogS2_liftQueryImplStateT2 (List.map coinBytes) List.map_nil]
            congr 1
          | some gsOpt =>
            cases gsOpt with
            | none =>
              simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
                mapLogS2_liftQueryImplStateT2 sendTapesOfInputs sendTapesOfInputs_nil,
                mapLogS2_bind (List.map coinBytes) (fun xs ys => List.map_append),
                mapLogS2_liftQueryImplStateT2 (List.map coinBytes) List.map_nil]
              congr 1
            | some gs => exact mapLogS2_cliStepLocalSMM_eq S ℓ run qep decT encT ds i bi im gs sq

private def pureByteS2 {σ₁ σ₂ α : Type} (m : StateT σ₁ (StateT σ₂ ProbComp) α) :
    StateT σ₁ (StateT σ₂ ByteLogM) α :=
  fun s₁ s₂ => liftM ((m.run s₁).run s₂)

private theorem pureByteS2_pure {σ₁ σ₂ α : Type} (a : α) :
    pureByteS2 (pure a : StateT σ₁ (StateT σ₂ ProbComp) α) = pure a := by
  ext s₁ s₂
  show (liftM (pure ((a, s₁), s₂)) : ByteLogM _).run = (pure ((a, s₁), s₂) : ByteLogM _).run
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

private theorem pureByteS2_map {σ₁ σ₂ α β : Type} (f : α → β)
    (m : StateT σ₁ (StateT σ₂ ProbComp) α) :
    pureByteS2 (f <$> m) = f <$> pureByteS2 m := by
  ext s₁ s₂
  show (liftM (((f <$> m).run s₁).run s₂) : ByteLogM _).run =
    (((f <$> pureByteS2 m).run s₁).run s₂).run
  simp only [StateT.run_map]
  dsimp [pureByteS2, StateT.run, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem pureByteS2_bind {σ₁ σ₂ α β : Type}
    (m : StateT σ₁ (StateT σ₂ ProbComp) α) (k : α → StateT σ₁ (StateT σ₂ ProbComp) β) :
    pureByteS2 (m >>= k) = pureByteS2 m >>= fun a => pureByteS2 (k a) := by
  ext s₁ s₂
  show (liftM (((m >>= k).run s₁).run s₂) : ByteLogM _).run =
    (((pureByteS2 m >>= fun a => pureByteS2 (k a)).run s₁).run s₂).run
  simp only [StateT.run_bind]
  dsimp [pureByteS2, StateT.run, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift,
    WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem pureByteS2_get {σ₁ σ₂ : Type} :
    pureByteS2 (get : StateT σ₁ (StateT σ₂ ProbComp) σ₁) = get := by
  ext s₁ s₂
  show (liftM (pure ((s₁, s₁), s₂)) : ByteLogM _).run = (pure ((s₁, s₁), s₂) : ByteLogM _).run
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

private theorem pureByteS2_set {σ₁ σ₂ : Type} (s₁' : σ₁) :
    pureByteS2 (set s₁' : StateT σ₁ (StateT σ₂ ProbComp) PUnit) = set s₁' := by
  ext s₁ s₂
  show (liftM (pure (((), s₁'), s₂)) : ByteLogM _).run = (pure (((), s₁'), s₂) : ByteLogM _).run
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

private theorem pureByteS2_lift_get {σ₁ σ₂ : Type} :
    pureByteS2 (StateT.lift get : StateT σ₁ (StateT σ₂ ProbComp) σ₂) = StateT.lift get := by
  ext s₁ s₂
  show (liftM ((StateT.lift get : StateT σ₁ (StateT σ₂ ProbComp) σ₂).run s₁ |>.run s₂) : ByteLogM _).run =
    ((StateT.lift get : StateT σ₁ (StateT σ₂ ByteLogM) σ₂).run s₁ |>.run s₂).run
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

private theorem pureByteS2_lift_set {σ₁ σ₂ : Type} (s₂' : σ₂) :
    pureByteS2 (StateT.lift (set s₂') : StateT σ₁ (StateT σ₂ ProbComp) PUnit) =
      StateT.lift (set s₂') := by
  ext s₁ s₂
  show (liftM ((StateT.lift (set s₂') : StateT σ₁ (StateT σ₂ ProbComp) PUnit).run s₁ |>.run s₂) : ByteLogM _).run =
    ((StateT.lift (set s₂') : StateT σ₁ (StateT σ₂ ByteLogM) PUnit).run s₁ |>.run s₂).run
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp

private theorem pureByteS2_lift_prob {σ₁ σ₂ α : Type} (c : ProbComp α) :
    pureByteS2 (StateT.lift (liftM c) : StateT σ₁ (StateT σ₂ ProbComp) α) =
      StateT.lift (liftM c) := by
  ext s₁ s₂
  show (liftM ((StateT.lift (liftM c) : StateT σ₁ (StateT σ₂ ProbComp) α).run s₁ |>.run s₂) : ByteLogM _).run =
    ((StateT.lift (liftM c) : StateT σ₁ (StateT σ₂ ByteLogM) α).run s₁ |>.run s₂).run
  dsimp [pureByteS2, StateT.run, StateT.lift, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem pureByteS2_lift2 {σ₁ σ₂ α : Type} (c : ProbComp α) :
    pureByteS2 (StateT.lift (StateT.lift c) : StateT σ₁ (StateT σ₂ ProbComp) α) =
      StateT.lift (StateT.lift (liftM c)) := by
  ext s₁ s₂
  show (liftM ((StateT.lift (StateT.lift c) : StateT σ₁ (StateT σ₂ ProbComp) α).run s₁ |>.run s₂) : ByteLogM _).run =
    ((StateT.lift (StateT.lift (liftM c)) : StateT σ₁ (StateT σ₂ ByteLogM) α).run s₁ |>.run s₂).run
  dsimp [pureByteS2, StateT.run, StateT.lift, liftM, monadLift, MonadLiftT.monadLift,
    MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem mapLogS2_cliDrvStartM_eq (S : SignalPqxdh.Setup) (ℓ : ℕ)
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (mode : BHDrvMode S)
    (sid : SignalPqxdh.SessionId S) :
    mapLogS2 sendTapesOfInputs (Dir.cliDrvStartM S ℓ P (cliRunLogged run) W mode sid) =
      mapLogS2 (List.map coinBytes)
        (liftQueryImplStateT2 (n := CoinLogM) (Dir.cliDrvCtl S ℓ P run W mode) (.startDR sid)) := by
  rw [mapLogS2_liftQueryImplStateT2 (List.map coinBytes) List.map_nil]
  change mapLogS2 sendTapesOfInputs (Dir.cliDrvStartM S ℓ P (cliRunLogged run) W mode sid) =
    pureByteS2 (Dir.cliDrvStart S ℓ P run W mode sid)
  unfold Dir.cliDrvStart Dir.cliDrvStartM
  simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
    mapLogS2_get sendTapesOfInputs sendTapesOfInputs_nil,
    pureByteS2_bind, pureByteS2_get]
  congr 1; funext ds
  have hpure : mapLogS2 sendTapesOfInputs (pure none : CliDrvMT S ℓ LogM (Option ℕ)) =
      pureByteS2 (pure none : CliDrvM S ℓ (Option ℕ)) :=
    (mapLogS2_pure sendTapesOfInputs sendTapesOfInputs_nil none).trans (pureByteS2_pure none).symm
  cases bhDrvGuard ds.toModelDriverState sid with
  | none => exact hpure
  | some g =>
    rcases g with ⟨hdr, bnd, u_resp, j_resp⟩
    dsimp only
    simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
      mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      mapLogS1_get sendTapesOfInputs sendTapesOfInputs_nil,
      pureByteS2_bind, pureByteS2_lift_get]
    congr 1; funext st0
    simp only [mapLogS1_liftM_prob sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      ← pureByteS2_lift_prob]
    congr 1; funext r1
    rcases r1 with ⟨resp1, st1⟩
    cases resp1 <;> try exact hpure
    dsimp only
    simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
      mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      mapLogS1_liftM_prob sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      pureByteS2_bind, pureByteS2_lift_prob]
    congr 1; funext r2
    rcases r2 with ⟨resp2, st⟩
    cases resp2 <;> try exact hpure
    dsimp only
    simp only [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
      mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      mapLogS1_liftM_prob sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      pureByteS2_bind, pureByteS2_lift_prob]
    congr 1; funext t_dr
    cases ds.initTapes.find? (fun (s, _, _, _) => s == sid) with
    | none => exact hpure
    | some it =>
      rcases it with ⟨_, u_init, _, t_init⟩
      dsimp only
      cases st.principals.find? (fun (idx, _) => idx == u_init.val) with
      | none => exact hpure
      | some ip =>
        rcases ip with ⟨_, initPrinEntry⟩
        dsimp only
        cases st.principals.find? (fun (idx, _) => idx == u_resp.val) with
        | none => exact hpure
        | some rp =>
          rcases rp with ⟨_, respPrinEntry⟩
          dsimp only
          cases st.spkBundles.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val)) with
          | none => exact hpure
          | some spk =>
            rcases spk with ⟨_, respSpkEntry⟩
            dsimp only
            have htail : ∀ opkSk? : Option (Option (ℕ × SignalPqxdh.Bytes)),
                mapLogS2 sendTapesOfInputs ((do
                  let some opkOpt := opkSk? | return none
                  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
                  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
                  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
                  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
                  let dA : PqParty :=
                    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                      session := none, signed := [], oneTime := [], kyberOneTime := [],
                      kyberLastResort := [] }
                  let some stA0 ←
                    StateT.lift (StateT.lift (Dir.cliPqInitM (cliRunLogged run) W dA bundleE
                      (appendInitiateTape t_init t_dr)))
                    | return none
                  let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
                  let bi0 : ModelDriverInstance S ℓ :=
                    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                      meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
                  let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
                  let scheme := Dir.cliPqSchemeM (cliRunLogged run) ℓ bi0 stA0 stB0
                  let gsDir :=
                    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB ‹_›).map
                      (fun b => scheme.initState () b)
                  let gs := gsDir.map (cliMapGameState CliPartyState.bin)
                  let bi : ModelDriverInstance S ℓ := { bi0 with gs := gs }
                  let im0 : ModelDriverInstanceMeta S :=
                    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
                  StateT.lift (set st)
                  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                                instGs := ds.instGs ++ [gsDir] }
                  return some ds.bhInsts.length) : CliDrvMT S ℓ LogM (Option ℕ)) = pureByteS2 ((do
                  let some opkOpt := opkSk? | return none
                  let some meA := mkMeEStrict u_init.val initPrinEntry.secIKA0 | return none
                  let some meB := mkMeEStrict u_resp.val respPrinEntry.secIKA0 | return none
                  let some keysB := mkKeysEStrict j_resp.val respSpkEntry opkOpt | return none
                  let some bundleE := mkBundleEStrict u_resp.val bnd | return none
                  let dA : PqParty :=
                    { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                      session := none, signed := [], oneTime := [], kyberOneTime := [],
                      kyberLastResort := [] }
                  let some stA0 ←
                    StateT.lift (StateT.lift (Dir.cliPqInitM (cliRunPure run) W dA bundleE
                      (appendInitiateTape t_init t_dr)))
                    | return none
                  let stB0Bin : BinState := { party := .B, bytes := [], epochs := { epoch := 0, chains := [] } }
                  let bi0 : ModelDriverInstance S ℓ :=
                    { sid := sid, hdr := hdr, idBBytes := bnd.ikB, respSlot := (u_resp, j_resp),
                      meA := meA, meB := meB, keysB := keysB, stA0 := stA0.bin, stB0 := stB0Bin, gs := none }
                  let stB0 := cliPartyStateB0 W bi0 (cliPqSigsOf st bi0)
                  let scheme := Dir.cliPqSchemeM (cliRunPure run) ℓ bi0 stA0 stB0
                  let gsDir :=
                    (mode sid (u_resp, j_resp) hdr.ikAPk bnd.ikB ‹_›).map
                      (fun b => scheme.initState () b)
                  let gs := gsDir.map (cliMapGameState CliPartyState.bin)
                  let bi : ModelDriverInstance S ℓ := { bi0 with gs := gs }
                  let im0 : ModelDriverInstanceMeta S :=
                    { respPrin := some u_resp, respSpkIdx := some j_resp, instOpkId? := bnd.opkB?.map Prod.fst }
                  StateT.lift (set st)
                  set { ds with bhInsts := ds.bhInsts ++ [bi], instMeta := ds.instMeta ++ [im0],
                                instGs := ds.instGs ++ [gsDir] }
                  return some ds.bhInsts.length) : CliDrvM S ℓ (Option ℕ)) := by
              intro opkSk?
              cases opkSk? with
              | none => exact hpure
              | some opkOpt =>
                dsimp only
                cases mkMeEStrict u_init.val initPrinEntry.secIKA0 with
                | none => exact hpure
                | some meA =>
                  dsimp only
                  cases mkMeEStrict u_resp.val respPrinEntry.secIKA0 with
                  | none => exact hpure
                  | some meB =>
                    dsimp only
                    cases mkKeysEStrict j_resp.val respSpkEntry opkOpt with
                    | none => exact hpure
                    | some keysB =>
                      dsimp only
                      cases mkBundleEStrict u_resp.val bnd with
                      | none => exact hpure
                      | some bundleE =>
                        dsimp only
                        have hinit :
                            mapLogW sendTapesOfInputs (Dir.cliPqInitM (cliRunLogged run) W
                              { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                                session := none, signed := [], oneTime := [], kyberOneTime := [],
                                kyberLastResort := [] }
                              bundleE (appendInitiateTape t_init t_dr)) =
                            liftM (Dir.cliPqInitM (cliRunPure run) W
                              { party := .A, me := meA, peerId := some (bhIdKeyOf bnd.ikB),
                                session := none, signed := [], oneTime := [], kyberOneTime := [],
                                kyberLastResort := [] }
                              bundleE (appendInitiateTape t_init t_dr)) := by
                          show (mapLogW sendTapesOfInputs _).run = (liftM _ : ByteLogM _).run
                          dsimp [mapLogW, Dir.cliPqInitM, cliRunLogged, cliRunPure, liftM, monadLift,
                            MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
                          simp
                        rw [mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
                          mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
                          mapLogS1_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
                          hinit, pureByteS2_bind, pureByteS2_lift2]
                        congr 1; funext stA0?
                        cases stA0? with
                        | none => exact hpure
                        | some stA0 =>
                          dsimp only
                          simp [SMSchemeRM.initState, Dir.cliPqSchemeM,
                            mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append,
                            mapLogS2_lift sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
                            mapLogS1_set sendTapesOfInputs sendTapesOfInputs_nil,
                            mapLogS2_map, mapLogS2_set sendTapesOfInputs sendTapesOfInputs_nil,
                            pureByteS2_bind, pureByteS2_lift_set, pureByteS2_map, pureByteS2_set]
            cases hdr.opkId? with
            | none =>
              dsimp only
              simp only [pure_bind]
              exact htail (some none)
            | some opkId =>
              dsimp only
              cases st.opkEntries.find? (fun (idx, _) => idx == (u_resp.val, j_resp.val, opkId.toNat)) with
              | none =>
                dsimp only
                simp only [pure_bind]
                exact htail none
              | some oe =>
                dsimp only
                simp only [pure_bind]
                exact htail (some (some (opkId.toNat, oe.2.opkSk)))

private theorem mapLogS2_bhLiftCliM_eq {S : SignalPqxdh.Setup} {ℓ : ℕ} {α : Type}
    (m : BHDrvM S ℓ α) :
    mapLogS2 sendTapesOfInputs (bhLiftCliM (M := LogM) m) =
      mapLogS2 (List.map coinBytes)
        (fun s₁ s₂ => liftM (((bhLiftCli m).run s₁).run s₂)) := by
  ext cds kst
  show (mapLogW sendTapesOfInputs (((bhLiftCliM (M := LogM) m).run cds).run kst)).run =
    (mapLogW (List.map coinBytes) (liftM (((bhLiftCli m).run cds).run kst))).run
  unfold bhLiftCliM bhLiftCli
  simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, StateT.run_set, StateT.run_pure,
    pure_bind]
  dsimp only [liftStateT, StateT.run]
  simp only [bind_assoc, pure_bind, mapLogW_bind sendTapesOfInputs sendTapesOfInputs_append,
    mapLogW_liftM sendTapesOfInputs sendTapesOfInputs_nil,
    mapLogW_pure sendTapesOfInputs sendTapesOfInputs_nil,
    mapLogW_liftM (List.map coinBytes) List.map_nil]
  dsimp [mapLogW, liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem mapLogS2_cliDrvImplM_eq (S : SignalPqxdh.Setup) (ℓ : ℕ) {Pt : Type}
    (P : SignalPqxdh.Primitives) (run : CliRun) (W : PEParams) (qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (ext : QueryImpl (cliGameSmSpec ℓ (BitVec 512)) (CliDrvM S ℓ)) (mode : BHDrvMode S)
    (t : (cliGameSpec S ℓ (BitVec 512)).Domain) :
    mapLogS2 sendTapesOfInputs (Dir.cliDrvImplM S ℓ P (cliRunLogged run) W qep decT encT
        (liftQueryImplStateT2 (n := LogM) ext) mode t) =
      mapLogS2 (List.map coinBytes)
        (dirDrvImplCoinLogged S ℓ P run W qep decT encT ext mode t) := by
  rcases t with ((t_unif | t_ki) | t_ctl) | t_sm
  · change mapLogS2 sendTapesOfInputs
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S ℓ LogM)) t_unif) =
      mapLogS2 (List.map coinBytes)
        (((QueryImpl.ofLift unifSpec ProbComp).liftTarget (CliDrvMT S ℓ CoinLogM)) t_unif)
    rw [QueryImpl.liftTarget_apply, QueryImpl.liftTarget_apply,
      mapLogS2_liftM_prob sendTapesOfInputs sendTapesOfInputs_append sendTapesOfInputs_nil,
      mapLogS2_liftM_prob (List.map coinBytes) (fun xs ys => List.map_append) List.map_nil]
  · exact mapLogS2_bhLiftCliM_eq (bhDrvKeyInd S ℓ P false t_ki)
  · cases t_ctl with
    | startDR sid => exact mapLogS2_cliDrvStartM_eq S ℓ P run W mode sid
  · exact mapLogS2_cliDrvSMM_eq S ℓ run qep decT encT ext t_sm

private theorem mapLogS2_simulateQ_eq {ι σ₁ σ₂ : Type} {spec : OracleSpec ι}
    (impl₁ : QueryImpl spec (StateT σ₁ (StateT σ₂ LogM)))
    (impl₂ : QueryImpl spec (StateT σ₁ (StateT σ₂ CoinLogM)))
    (himpl : ∀ t, mapLogS2 sendTapesOfInputs (impl₁ t) = mapLogS2 (List.map coinBytes) (impl₂ t))
    {α : Type} (oa : OracleComp spec α) :
    mapLogS2 sendTapesOfInputs (simulateQ impl₁ oa) =
      mapLogS2 (List.map coinBytes) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    exact (mapLogS2_pure sendTapesOfInputs sendTapesOfInputs_nil a).trans
      (mapLogS2_pure (List.map coinBytes) List.map_nil a).symm
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query,
      mapLogS2_bind sendTapesOfInputs sendTapesOfInputs_append, himpl t,
      simulateQ_bind, simulateQ_spec_query,
      mapLogS2_bind (List.map coinBytes) (fun xs ys => List.map_append)]
    exact congrArg (mapLogS2 (List.map coinBytes) (impl₂ t) >>= ·) (funext ih)

theorem cliPqxdhExpFlagged_sendTapes_eq_dirCoinLogged
    {Pt : Type} (S : SignalPqxdh.Setup) (run : CliRun)
    (X : UnreachedPqxdhPrimitives) (W : PEParams) (ℓ qep : ℕ)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey)
    (A : CliGameAdversary S ℓ (BitVec 512)) :
    Prod.map id sendTapesOfInputs <$> cliPqxdhExpFlagged S run X W ℓ qep decT encT A =
      Prod.map id (List.map coinBytes) <$> dirPqExpCoinLogged S run X W ℓ qep decT encT A := by
  change (mapLogW sendTapesOfInputs (do
      let P := modelPrims X W
      let b ← liftM ($ᵗ Bool : ProbComp Bool)
      let ((b', ds), st) ←
        (runCliDriverLogged S ℓ P run W qep decT encT bhNoExtWithSpqr (fun _ _ _ _ _ => some b)
          A).run (SignalPqxdh.KeyIndState.empty S true)
      if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
      else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b))).run =
    (mapLogW (List.map coinBytes) (do
      let P := modelPrims X W
      let b ← liftM ($ᵗ Bool : ProbComp Bool)
      let ((b', ds), st) ←
        (((simulateQ (dirDrvImplCoinLogged S ℓ P run W qep decT encT bhNoExtWithSpqr
            (fun _ _ _ _ _ => some b)) A.run).run {}).run (SignalPqxdh.KeyIndState.empty S true))
      if !allTestedSessionsFresh P st then liftM ($ᵗ Bool : ProbComp Bool)
      else return (b' == b || driverSomeInstanceWon ds.toModelDriverState b))).run
  congr 1
  simp only [mapLogW_bind sendTapesOfInputs sendTapesOfInputs_append,
    mapLogW_liftM sendTapesOfInputs sendTapesOfInputs_nil,
    mapLogW_bind (List.map coinBytes) (fun xs ys => List.map_append),
    mapLogW_liftM (List.map coinBytes) List.map_nil]
  congr 1; funext b
  unfold runCliDriverLogged
  rw [← mapLogS1_run, ← mapLogS2_run, ← mapLogS1_run, ← mapLogS2_run,
    mapLogS2_simulateQ_eq _ _
      (mapLogS2_cliDrvImplM_eq S ℓ (modelPrims X W) run W qep decT encT bhNoExtWithSpqr
        (fun _ _ _ _ _ => some b)) A.run]
  congr 1; funext ⟨⟨b', ds⟩, st⟩
  split_ifs
  · exact (mapLogW_liftM sendTapesOfInputs sendTapesOfInputs_nil _).trans
      (mapLogW_liftM (List.map coinBytes) List.map_nil _).symm
  · exact (mapLogW_pure sendTapesOfInputs sendTapesOfInputs_nil _).trans
      (mapLogW_pure (List.map coinBytes) List.map_nil _).symm


end Computational.Proofs.LibsignalCli.CliKemFailCouplingHopAAux
