/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec
public import LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs
public import LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
public import LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
public import LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacCommon
public import LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seams
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Skeleton
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.CliBinaryPqProofDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionApi
public import LibsignalBinary.Specifications.SignalSession.PqDir
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Refine.Plumbing

/-!
# Concrete `send`-Arm Early/Error-Path Envelope Inhabitation

Proves non-vacuity of the `.send` CLI arm envelope via the early/error path on `nonVacCommonAliceParty`
(`session = none`), exhibiting the `24`-byte `async_trait` future allocation (`AllocEvent.alloc 24`)
in `<SessionFiles as SessionStore>::load_session` followed by `R2ConcatTailEnv`'s early/error
`FreeOnlyEvs` branch (`evs₂ = []`), `M5PhaseEnv [] []`, and `M6Env false []` across `CliMainEnv`
and `RealCliMainEnvOf`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSend

open Arm64.Process (bytesOfString)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoGames.LibsignalSessionApi (SessionRecord SystemTime)
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.E2E (PEParams partyAddressName)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (WithStoresEncGhost)
open CryptoVerification.LibsignalPublicApiRepr (RecordGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost uuidTryParse)
open CryptoVerification.SignalSession (CliPqxdhInputs Inputs pqSendInputs)
open CryptoVerification.SignalSession.Cli (ReadRule pathOf utf8)
open CryptoVerification.SignalSession.Cli.MainHops (AddrV RunCall cliIo parseArgs)
open CryptoVerification.SignalSession.Cli.RunCompose (InitGhost RunSem addrValOf runFiles)
open CryptoVerification.SignalSession.Cli.RunProofs.EncryptLemmas (w1SessKit)
open CryptoVerification.SignalSession.Cli.RunRefine (parseArgs_send)
open CryptoVerification.SignalSession.Cli.RunSkeleton (RunBudgets)
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateGhost)
open LibsignalBinary.Heap (AllocEvent FreeOnlyEvs rustAllocEvents)
open LibsignalBinary.Proofs.PeakBudget.CliMainPeakSpec (CliMainEnv)
open LibsignalBinary.Proofs.PeakBudget.CliRealExistentialCalleeEnvs (mkExistentialRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.CliRunArmsPeak
  (CliRunCalleeEnvs CliRunOpenedEnv R2Env RunArmEnv)
open LibsignalBinary.Proofs.PeakBudget.CliTopBudgetReal (CliPqRealCallDomain mkRealCalleeEnvs)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvAdapter
  (RealCliMainEnvOf realCliMainEnvOf_of_cliMainEnv)
open LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacCommon
  (cliMainEnv_of_setup_and_runArm cliMainSetupEnv_nonVac_len2 nonVacCoinsEvents
   nonVacCommonAliceParty nonVacCommonAliceParty_baseKeysCap nonVacCommonAliceParty_inSpecDomain
   nonVacCommonPEParams nonVacCommonSessionCap)
open LibsignalBinary.Proofs.PeakBudget.SpqrDomainCapsAux (msgCapBytes sessionCapBytes)
open LibsignalBinary.Proofs.PeakBudget.W1SendRealSlot
  (W1SendRealDom W1SendRealEnv W1SendRealParams W1SendRealSlotEnv)
open LibsignalBinary.Proofs.PeakBudget.W2RecvWhisperRealSlot (W2RecvWhisperRealParams)
open LibsignalBinary.Proofs.PeakBudget.W4RecvPrekeyRealSlot (W4RecvPrekeyRealParams)
open LibsignalBinary.Proofs.SessionRecordMin.DeserializeCancelBudgetAux (RecordDeserializeCancelEnv)

/-! ## 1. Concrete `send` Call & `W1SendRealSlotEnv` `.alloc 24` Witness -/

/-- Parsed peer `AddrV` for Bob (`.B`) on Alice's `send <Bob>` invocation. -/
def nonVacSendPeer : AddrV :=
  ⟨utf8 (partyAddressName .B), 1#8⟩

/-- Concrete `pqSendInputs` on `nonVacCommonAliceParty` (`session = none`, empty plaintext, zero coins). -/
def nonVacSendInputs : Inputs :=
  pqSendInputs nonVacCommonPEParams nonVacCommonAliceParty [] (List.Vector.replicate 64 0#8)

/-- Concrete `RunCall` for `send <Bob>` on `nonVacCommonAliceParty`. -/
def nonVacSendCall : RunCall where
  i := nonVacSendInputs
  c := .send nonVacSendPeer
  a := some none
  res := 0#64
  call := 0#64
  stores := 0#64
  inp := 0#64
  coins := 0#64

theorem nonVacSendCall_parseArgs :
    parseArgs uuidTryParse (nonVacSendCall.i.argv.map bytesOfString) =
      some (.send nonVacSendPeer) :=
  parseArgs_send .B

theorem nonVacSendCall_inDomain :
    CliPqRealCallDomain nonVacCommonPEParams nonVacSendCall := by
  refine ⟨nonVacCommonAliceParty, nonVacCommonAliceParty_inSpecDomain,
    Or.inr (Or.inl ⟨[], List.Vector.replicate 64 0#8, by decide, rfl⟩),
    nonVacCommonSessionCap, nonVacCommonAliceParty_baseKeysCap,
    Nat.zero_le msgCapBytes, nonVacSendCall_parseArgs, ?_⟩
  intro _ _ hc
  nomatch hc

/-- Concrete `AddrGhost` matching `addrValOf peerAddr`. -/
def nonVacSendAddrGhost (peerAddr : AddrV) : AddrGhost :=
  ⟨⟨0#64, 0#64, (addrValOf peerAddr).name⟩, (addrValOf peerAddr).device⟩

/-- Concrete `WithStoresEncGhost` with empty plaintext and remote/local address `nonVacSendAddrGhost peerAddr`. -/
def nonVacSendEncGhost (peerAddr : AddrV) : WithStoresEncGhost where
  ret := 0#64
  ptA := 0#64
  ptext := []
  remA := 0#64
  rem := nonVacSendAddrGhost peerAddr
  locA := 0#64
  loc := nonVacSendAddrGhost peerAddr
  now := SystemTime.unixEpoch
  cur := 0#64
  rest := []
  ssA := 0#64
  idA := 0#64

/-- Concrete `W1SendRealParams` bundle aligned with `.send peerAddr`. -/
def nonVacW1SendRealParams (peerAddr : AddrV) : W1SendRealParams where
  B := ⟨0⟩
  peer := nonVacSendAddrGhost peerAddr
  x := nonVacSendEncGhost peerAddr

theorem nonVacW1SendRealParams_dom (peerAddr : AddrV) :
    W1SendRealDom (.send peerAddr) (nonVacW1SendRealParams peerAddr) := by
  intro p hp
  injection hp with hp
  subst hp
  exact ⟨rfl, rfl, Nat.zero_le msgCapBytes⟩

/-- Explicit `.alloc 24` witness in `W1SendRealSlotEnv`: the `24`-B `load_session` shim `Box`
(`rustAllocEvents 24 8 = [AllocEvent.alloc 24]`) inhabits `W1SendRealSlotEnv`. -/
theorem w1SendRealSlotEnv_alloc24
    (img : Arm64.Obj.Image) (W : PEParams) (i : Inputs) (R : W1SendRealParams) :
    AllocEvent.alloc 24 ∈ rustAllocEvents 24 8 ∧
      W1SendRealSlotEnv img W i R (rustAllocEvents 24 8) := by
  have hbox : (w1SessKit R.B img (runFiles i) R.peer).loadBoxSize = 24 := rfl
  refine ⟨by simp [rustAllocEvents], ?_⟩
  change W1SendRealEnv R.B img (runFiles i) R.peer W R.x RecordDeserializeCancelEnv
    (rustAllocEvents 24 8)
  rw [← hbox]
  exact Or.inl (Or.inl (Or.inr ⟨by rw [hbox]; decide, rfl⟩))

theorem existentialRealCalleeEnvs_encEnv_alloc24 [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem)
    (P : PEParams) (g : RunCall) (peer : AddrV) (hc : g.c = .send peer) :
    ∃ evs, AllocEvent.alloc 24 ∈ evs ∧
      (mkExistentialRealCalleeEnvs img S P g).encEnv evs := by
  have hw := w1SendRealSlotEnv_alloc24 img P g.i (nonVacW1SendRealParams peer)
  refine ⟨rustAllocEvents 24 8, hw.1, ?_⟩
  dsimp only [mkExistentialRealCalleeEnvs]
  rw [hc]
  exact ⟨nonVacW1SendRealParams peer, nonVacW1SendRealParams_dom peer, hw.2⟩

/-! ## 2. `send`-Arm Early/Error-Path Envelope Inhabitation Theorems -/

/-- Constructs `(nonVacCommonPEParams, nonVacSendCall, fullLog)` in `CliPqRealCallDomain` satisfying
`CliMainEnv` over `CliRunOpenedEnv` on the `.send` early/error path with `AllocEvent.alloc 24 ∈ fullLog`. -/
theorem cliPqRealCallDomain_send_nonvacuous
    (E : PEParams → RunCall → CliRunCalleeEnvs)
    (henc : ∀ (P : PEParams) (g : RunCall) (peer : AddrV),
      g.c = .send peer →
      ∃ evs, AllocEvent.alloc 24 ∈ evs ∧ (E P g).encEnv evs) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      (∃ peer, parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some (.send peer)) ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd (E P₀ g') sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 24 ∈ fullLog := by
  let g₀ := nonVacSendCall
  obtain ⟨evsEnc, hmem24, henc₀⟩ := henc nonVacCommonPEParams g₀ nonVacSendPeer rfl
  refine ⟨nonVacCommonPEParams, g₀, nonVacCoinsEvents g₀.i ++ evsEnc,
    nonVacSendCall_inDomain, ⟨nonVacSendPeer, nonVacSendCall_parseArgs⟩, ?_,
    List.mem_append_right _ hmem24⟩
  have hSetup := cliMainSetupEnv_nonVac_len2 g₀.i rfl
  have hArm : RunArmEnv cliIo.rd (runFiles g₀.i) (E nonVacCommonPEParams g₀) sessionCapBytes
      g₀.i.stdin g₀.c evsEnc := by
    change R2Env (E nonVacCommonPEParams g₀).encEnv sessionCapBytes evsEnc
    exact Or.inr (Or.inr ⟨evsEnc, [], (List.append_nil _).symm, henc₀, Or.inl FreeOnlyEvs.nil⟩)
  exact cliMainEnv_of_setup_and_runArm hSetup hArm

/-- Specialization of `cliPqRealCallDomain_send_nonvacuous` to `mkRealCalleeEnvs`. -/
theorem cliPqRealCallDomain_mkRealCalleeEnvs_send_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image)
    (rd : RunCall → ReadRule)
    (x : RunCall → InitGhost)
    (ownKeyName ownRegName : RunCall → List (BitVec 8))
    (F : RunCall → ShaCompress)
    (x_spqr : RunCall → InitialStateGhost)
    (g_rec : RunCall → RecordGhost)
    (r_rec : RunCall → SessionRecord (List (BitVec 8)))
    (w1R : RunCall → W1SendRealParams)
    (w2R : RunCall → W2RecvWhisperRealParams)
    (w4R : RunCall → W4RecvPrekeyRealParams) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      (∃ peer, parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some (.send peer)) ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkRealCalleeEnvs img P₀ g' (rd g') (x g') (ownKeyName g') (ownRegName g')
            (F g') (x_spqr g') (g_rec g') (r_rec g')
            (w1R g') (w2R g') (w4R g'))
          sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 24 ∈ fullLog :=
  cliPqRealCallDomain_send_nonvacuous _ fun P g _ _ =>
    let hw := w1SendRealSlotEnv_alloc24 img P g.i (w1R g)
    ⟨rustAllocEvents 24 8, hw.1, hw.2⟩

/-- Specialization of `cliPqRealCallDomain_send_nonvacuous` to `mkExistentialRealCalleeEnvs img S`. -/
theorem existentialRealCalleeEnvs_send_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (g₀ : RunCall) (fullLog : List AllocEvent),
      CliPqRealCallDomain P₀ g₀ ∧
      (∃ peer, parseArgs uuidTryParse (g₀.i.argv.map bytesOfString) = some (.send peer)) ∧
      CliMainEnv uuidTryParse
        (fun g' => CliRunOpenedEnv cliIo.rd
          (mkExistentialRealCalleeEnvs img S P₀ g') sessionCapBytes g')
        g₀ none false [] false fullLog ∧
      AllocEvent.alloc 24 ∈ fullLog :=
  cliPqRealCallDomain_send_nonvacuous (mkExistentialRealCalleeEnvs img S)
    (existentialRealCalleeEnvs_encEnv_alloc24 img S)

/-- Parametric lift of `cliPqRealCallDomain_send_nonvacuous` to `RealCliMainEnvOf (E P₀) i₀`. -/
theorem realCliMainEnvOf_send_nonvacuous
    (E : PEParams → RunCall → CliRunCalleeEnvs)
    (henc : ∀ (P : PEParams) (g : RunCall) (peer : AddrV),
      g.c = .send peer →
      ∃ evs, AllocEvent.alloc 24 ∈ evs ∧ (E P g).encEnv evs) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peer)) ∧
      RealCliMainEnvOf (E P₀) i₀ fullLog ∧
      AllocEvent.alloc 24 ∈ fullLog := by
  obtain ⟨P₀, g₀, fullLog, hd, hcmd, hEnv, ha24⟩ :=
    cliPqRealCallDomain_send_nonvacuous E henc
  refine ⟨P₀, g₀.i, fullLog, hd.toCliPqxdhInputs, hcmd, ?_, ha24⟩
  exact realCliMainEnvOf_of_cliMainEnv hd.toCliPqxdhInputs uuidTryParse none false [] false
    ⟨hd.parseArgs_eq, hd.toCliPqDomainCaps.stdin_le, Nat.zero_le _, fun _ hm => nomatch hm⟩ hEnv

/-- Concrete early/error-path `.send` non-vacuity witness on
`RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀` (`AllocEvent.alloc 24 ∈ fullLog`). -/
theorem realCliMainEnvOf_concrete_send_nonvacuous [LibsignalPlacement]
    (img : Arm64.Obj.Image) (S : RunSem) :
    ∃ (P₀ : PEParams) (i₀ : Inputs) (fullLog : List AllocEvent),
      CliPqxdhInputs P₀ i₀ ∧
      (∃ peer, parseArgs uuidTryParse (i₀.argv.map bytesOfString) = some (.send peer)) ∧
      RealCliMainEnvOf (mkExistentialRealCalleeEnvs img S P₀) i₀ fullLog ∧
      AllocEvent.alloc 24 ∈ fullLog :=
  realCliMainEnvOf_send_nonvacuous (mkExistentialRealCalleeEnvs img S)
    (existentialRealCalleeEnvs_encEnv_alloc24 img S)

end LibsignalBinary.Proofs.PeakBudget.RealMainEnvNonVacSend
