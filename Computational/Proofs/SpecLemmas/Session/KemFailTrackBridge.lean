/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Session.StatementSession
public import Computational.Proofs.CryptoGames.Ratchet.LibsignalSMInstanceProofDefs
public import LibsignalBinary.Specifications.LibsignalSpqrV1.KemFailFind
public import LibsignalBinary.Proofs.SpqrV1Sync.CoinBridge
public import ToMathlib.MeasureTheory.Measure.Bool
import Mathlib.Tactic.Ring
import VCVio.OracleComp.SimSemantics.SimulateQ
import VCVio.EvalDist.Monad.Basic
import VCVio.EvalDist.ProbabilityBounds
import VCVio.EvalDist.MeasureTVDist.Event
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section

set_option autoImplicit false

/-!
# SPQR V1 braid tracker and halted `SM.gameR` bridge

**Checked by Lean.**

Defines the per-session SPQR V1 braid tracker (`KemFailTrackState`, `KemFailSessionTrack`) and
tracker-halted `SM.gameR` (`gameRTrackHalted`), and proves online bad-event and `boolBias`
transfer bounds from `SM.gameR` via `gameRCoinLogged`.
-/

namespace Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge

open MeasureTheory (Measure IsProbabilityMeasure lintegral_congr lintegral_indicator)
open OracleComp OracleSpec
open scoped ENNReal
open CryptoGames (Party SMSchemeR)
open CryptoGames.CBC (Plain)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (Crypto GhostState IdentityKey Params PublicKey RootKey ShaCompress)
open CryptoGames.Ratchet.LibsignalInst (libsignalSessionScheme)
open CryptoGames.SM (Adversary ConfigR GameState RecvResult challImpl challR corrR deliverR
  gameR initState injectR oracleImplR runR samIfNec spec transmitImpl transmitR)
open CryptoVerification.E2E (Bytes SampledSessionKey SMSchemeRM challRM configRefuseEarlyBobCorr
  deliverRM gameRCoinLogged injectRM liftStateT oracleImplRM paramsIdsWithSpqr
  sessionKemFailProb sessionSchemeFixedSpk smSchemeCoinLogged transmitRM)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Epoch MlKem coinBytes
  coinBytes_length spqrV1SessionUniformCoins)
open CryptoVerification.SpqrV1Sync.InSync (Msg Seed St freshDec)
open CryptoVerification.SpqrV1Sync.Braid (EncRand authNext coinEquiv coinEquiv_apply ekSide
  encRandOf nextCoins nextCoins_init_coin nextCoins_seed_coin noneMsg)

/-! ## Braid tracker and tracker-halted `SM.gameR` -/

def kemBraidParty : Party → CryptoVerification.SpqrV1Sync.Braid.Party
  | .A => .a
  | .B => .b

/-- Per-session SPQR V1 braid tracker monitoring cross-party `(seed, encRandOf r)` pairs. -/
structure KemFailTrackState (F : ShaCompress) where
  e : Epoch
  auth : Authenticator
  c : CryptoVerification.SpqrV1Sync.Braid.Coins
  st : Party → St F
  sentB : List (Msg × BitVec 32)
  sendCtr : Party → ℕ → ℕ
  cand : Option (List.Vector (BitVec 8) 64 × List.Vector (BitVec 8) 32)

/-- Pairs `KemFailTrackState F` with the prepend-only `(wire, sender)` history of honest sends. -/
abbrev KemFailSessionTrack (F : ShaCompress) (C : Type) : Type :=
  KemFailTrackState F × List (C × Party)

def initKemFailTrack (F : ShaCompress) (k : BitVec 256) : KemFailTrackState F :=
  let auth₀ := Authenticator.new F (keyToBytes32 k) 1#64
  let stA₀ : St F := .keysUnsampled { uc := { epoch := 1#64, auth := auth₀ } }
  let stB₀ : St F := .noHeaderReceived
    { uc := { epoch := 1#64, auth := auth₀ }, receiving_hdr := freshDec 96 }
  { e := 1#64
    auth := auth₀
    c := .init
    st := fun Q => match Q with | .A => stA₀ | .B => stB₀
    sentB := []
    sendCtr := fun _ _ => 0
    cand := none }

def initKemFailSessionTrack (F : ShaCompress) (C : Type) (k : BitVec 256) :
    KemFailSessionTrack F C :=
  (initKemFailTrack F k, [])

/-- Advances `KemFailTrackState` on a send by `Q`, latching `cand` if encapsulation fails. -/
def stepKemFailSend (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F) (Q : Party)
    (r : BitVec 512) : KemFailTrackState F :=
  let cand' :=
    match tr.cand with
    | some p => some p
    | none =>
      if ekSide tr.e != kemBraidParty Q then
        match tr.c, tr.st Q with
        | .seed s, .headerReceived _ =>
          if K.honestExchangeFails s (encRandOf r) then some (s, encRandOf r) else none
        | _, _ => none
      else none
  match (tr.st Q).send K (coinBytes r) with
  | .ok (out, _) =>
    let E := out.msg.epoch.toNat - 1
    let n := tr.sendCtr Q E
    { tr with
      c := nextCoins F tr.c (tr.st Q) (coinBytes r)
      st := Function.update tr.st Q out.state
      sentB := tr.sentB ++ [(out.msg, BitVec.ofNat 32 (n + 1))]
      sendCtr := Function.update tr.sendCtr Q (Function.update (tr.sendCtr Q) E (n + 1))
      cand := cand' }
  | .error _ => { tr with cand := cand' }

/-- Advances `KemFailTrackState` on an accepted delivery of honest send `j` to `Q`. -/
def stepKemFailDeliver (F : ShaCompress) (K : MlKem) (tr : KemFailTrackState F) (Q : Party)
    (j : ℕ) : KemFailTrackState F :=
  match tr.sentB[j]? with
  | none => tr
  | some (m, _) =>
    match (tr.st Q).recv K m with
    | .ok out =>
      let tr1 := { tr with st := Function.update tr.st Q out.state }
      if m = noneMsg (tr.e + 1#64) then
        match tr.c with
        | .both s r =>
          { tr1 with e := tr.e + 1#64, auth := authNext F K tr.e tr.auth s r, c := .init }
        | _ => tr1
      else tr1
    | .error _ => tr

/-- Tracker-halted `transmit` oracle latching `cand` and returning `none` when `stepKemFailSend` fails. -/
def transmitRTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      let (tr, honestWires) ← StateT.lift get
      let tr' := stepKemFailSend F K tr P coins
      if tr'.cand.isSome then
        StateT.lift (set ({ tr with cand := tr'.cand }, honestWires))
        return none
      else
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ false)
        StateT.lift (set (tr', (out.2, P) :: honestWires))
        return some out.2

/-- Tracker-halted `chall` oracle latching `cand` and returning `none` when `stepKemFailSend` fails. -/
def challRTrackHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let (tr, honestWires) ← StateT.lift get
      let tr' := stepKemFailSend F K tr P coins
      if tr'.cand.isSome then
        StateT.lift (set ({ tr with cand := tr'.cand }, honestWires))
        return none
      else
        let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
        let out := sm.send (s₁.st P) m coins
        set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ true)
        StateT.lift (set (tr', (out.2, P) :: honestWires))
        return some out.2

/-- Tracker-halted `deliver` oracle advancing `stepKemFailDeliver` upon accepted honest deliveries. -/
def deliverRTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  fun ⟨Q, w⟩ => do
    let (_, honestWires) ← StateT.lift get
    let j? := honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    let res ← liftStateT (deliverR sm cfg (Q, w))
    match res, j? with
    | some (.accepted _ _ _), some j =>
      StateT.lift (modify fun ⟨tr, hw⟩ => (stepKemFailDeliver F K tr Q j, hw))
    | _, _ => pure ()
    return res

def oracleImplRTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  transmitRTrackHalted F K sm Δ qep cfg + challRTrackHalted F K sm Δ qep cfg +
    deliverRTrackHalted F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)))

def cliOracleImplRTrackHalted {Key St' St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (proj : St' → St) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St' Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St' Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St' Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) :=
  transmitRTrackHalted F K sm Δ qep cfg + challRTrackHalted F K sm Δ qep cfg +
    deliverRTrackHalted F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St' Msg C) (StateT (KemFailSessionTrack F C) ProbComp))) +
    ((fun P => liftStateT (Option.map proj <$> corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St' Msg C) (StateT (KemFailSessionTrack F C) ProbComp)))

def runRTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (b : Bool) (A : Adversary St Msg (BitVec 512) C) :
    ProbComp ((Bool × GameState St Msg C) × KemFailSessionTrack F C) := do
  let k ← ($ᵗ Key : ProbComp Key)
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRTrackHalted F K sm Δ qep cfg
  ((simulateQ impl A).run (initState sm.sendPart k b)).run (initKemFailTrack F (pqrOf k), [])

/-- Tracker-halted `SM.gameR` returning `(b == b' || s.win, stTrack)`. -/
def gameRTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    ProbComp (Bool × KemFailSessionTrack F C) := do
  let b ← ($ᵗ Bool : ProbComp Bool)
  let k ← ($ᵗ Key : ProbComp Key)
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRTrackHalted F K sm Δ qep cfg
  let ((b', s), stTrack) ←
    ((simulateQ impl A).run (initState sm.sendPart k b)).run (initKemFailTrack F (pqrOf k), [])
  return (b == b' || s.win, stTrack)

abbrev sampledSessionPqrOf (k : SampledSessionKey) : BitVec 256 := k.2.2

abbrev libsignalSessionPqrOf (k : RootKey × BitVec 256 × BitVec 256 × BitVec 256) : BitVec 256 :=
  k.2.2.2

theorem gameRTrackHalted_eq_bind_runRTrackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    gameRTrackHalted pqrOf F K sm Δ qep cfg A =
      (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let ((b', s), stTrack) ← runRTrackHalted pqrOf F K sm Δ qep cfg b A
        return (b == b' || s.win, stTrack)) := by
  simp [gameRTrackHalted, runRTrackHalted]

/-! ## `KemTrackLoggedInv` -/

theorem tapePairFails_coinBytes (K : MlKem) (r₁ r₂ : BitVec 512) :
    K.tapePairFails (coinBytes r₁) (coinBytes r₂) =
      K.honestExchangeFails (coinEquiv r₁) (encRandOf r₂) := by
  have h₁ := coinBytes_length r₁
  have h₂ := coinBytes_length r₂
  simp only [MlKem.tapePairFails, h₁, h₂, ↓reduceDIte]
  rw [show (⟨coinBytes r₁, h₁⟩ : Seed) = coinEquiv r₁ from
        List.Vector.eq _ _ (coinEquiv_apply r₁).symm,
    show (⟨(coinBytes r₂).take 32, by simp [h₂]⟩ : EncRand) = encRandOf r₂ from
        List.Vector.eq _ _ rfl]

theorem kemFailBad_of_honestExchangeFails_coinEquiv (K : MlKem) (log : List (BitVec 512))
    {r₁ r₂ : BitVec 512} (hr₁ : r₁ ∈ log) (hr₂ : r₂ ∈ log)
    (hfail : K.honestExchangeFails (coinEquiv r₁) (encRandOf r₂) = true) :
    K.KemFailBad (log.map coinBytes) = true := by
  simp only [MlKem.KemFailBad, List.any_eq_true, List.mem_map]
  exact ⟨_, ⟨r₁, hr₁, rfl⟩, _, ⟨r₂, hr₂, rfl⟩, (tapePairFails_coinBytes K r₁ r₂).trans hfail⟩

theorem kemFailBad_mono_subset {K : MlKem} {l₁ l₂ : List (List (BitVec 8))}
    (hsub : ∀ t ∈ l₁, t ∈ l₂) (hbad : K.KemFailBad l₁ = true) : K.KemFailBad l₂ = true := by
  simp only [MlKem.KemFailBad, List.any_eq_true] at hbad ⊢
  rcases hbad with ⟨t₁, ht₁, t₂, ht₂, hf⟩
  exact ⟨t₁, hsub t₁ ht₁, t₂, hsub t₂ ht₂, hf⟩

theorem kemFailBad_mono (K : MlKem) {l₁ l₂ : List (List (BitVec 8))}
    (hbad : K.KemFailBad l₁ = true) : K.KemFailBad (l₁ ++ l₂) = true :=
  kemFailBad_mono_subset (fun _ ht => List.mem_append_left l₂ ht) hbad

/-- Invariant tying `KemFailTrackState` (`tr.c` and `tr.cand`) to a send-coin log `log`. -/
structure KemTrackLoggedInv {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackState F) (log : List (BitVec 512)) : Prop where
  seed_mem : ∀ s, tr.c = .seed s → ∃ r₁ ∈ log, s = coinEquiv r₁
  cand_mem : ∀ p, tr.cand = some p →
    ∃ r₁ ∈ log, ∃ r₂ ∈ log,
      p = (coinEquiv r₁, encRandOf r₂) ∧ K.honestExchangeFails p.1 p.2 = true

theorem kemTrackLoggedInv_init (F : ShaCompress) (K : MlKem) (pqrKey : BitVec 256) :
    KemTrackLoggedInv K (initKemFailTrack F pqrKey) [] where
  seed_mem _ hs := by simp [initKemFailTrack] at hs
  cand_mem _ hc := by simp [initKemFailTrack] at hc

theorem kemTrackLoggedInv_mono {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log log' : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hsub : ∀ r ∈ log, r ∈ log') :
    KemTrackLoggedInv K tr log' where
  seed_mem s hs := let ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s hs; ⟨r₁, hsub r₁ hr₁, hEq⟩
  cand_mem p hp := let ⟨r₁, hr₁, r₂, hr₂, hEq, hf⟩ := hinv.cand_mem p hp
    ⟨r₁, hsub r₁ hr₁, r₂, hsub r₂ hr₂, hEq, hf⟩

theorem nextCoins_seed_mem {F : ShaCompress} {c : CryptoVerification.SpqrV1Sync.Braid.Coins} {st : St F} {log : List (BitVec 512)}
    (r : BitVec 512) (hseed : ∀ s, c = .seed s → ∃ r₁ ∈ log, s = coinEquiv r₁)
    {s' : Seed} (hs' : nextCoins F c st (coinBytes r) = .seed s') :
    ∃ r₁ ∈ log ++ [r], s' = coinEquiv r₁ := by
  cases c with
  | init => cases st with
    | keysUnsampled ku =>
      rw [nextCoins_init_coin F r (.keysUnsampled ku) ⟨ku, rfl⟩] at hs'
      cases hs'
      exact ⟨r, List.mem_append_right _ (List.mem_singleton_self r), rfl⟩
    | _ => simp [nextCoins] at hs'
  | seed s => cases st with
    | headerReceived hr =>
      rw [nextCoins_seed_coin F s r (.headerReceived hr) ⟨hr, rfl⟩] at hs'
      cases hs'
    | _ =>
      simp [nextCoins] at hs'
      subst hs'
      obtain ⟨r₁, hr₁, hEq⟩ := hseed s rfl
      exact ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
  | both _ _ => simp [nextCoins] at hs'

theorem stepKemFailSend_cand_mem {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512)
    {p : Seed × EncRand} (hp : (stepKemFailSend F K tr Q r).cand = some p) :
    ∃ r₁ ∈ log ++ [r], ∃ r₂ ∈ log ++ [r],
      p = (coinEquiv r₁, encRandOf r₂) ∧ K.honestExchangeFails p.1 p.2 = true := by
  have hcand_eq : (stepKemFailSend F K tr Q r).cand = match tr.cand with
      | some p => some p
      | none => if ekSide tr.e != kemBraidParty Q then match tr.c, tr.st Q with
        | .seed s, .headerReceived _ =>
          if K.honestExchangeFails s (encRandOf r) then some (s, encRandOf r) else none
        | _, _ => none else none := by
    unfold stepKemFailSend
    cases (tr.st Q).send K (coinBytes r) <;> rfl
  rw [hcand_eq] at hp
  cases htc : tr.cand with
  | some p₀ =>
    rw [htc] at hp
    obtain ⟨r₁, hr₁, r₂, hr₂, hEq, hf⟩ := hinv.cand_mem p₀ htc
    cases hp
    exact ⟨r₁, List.mem_append_left _ hr₁, r₂, List.mem_append_left _ hr₂, hEq, hf⟩
  | none =>
    rw [htc] at hp
    by_cases hek : (ekSide tr.e != kemBraidParty Q) = true
    · simp only [hek] at hp
      cases hc : tr.c <;> rw [hc] at hp
      · simp at hp
      · rename_i s
        cases hst : tr.st Q <;> rw [hst] at hp <;> try simp at hp
        by_cases hf : K.honestExchangeFails s (encRandOf r) = true
        · have hp' : (s, encRandOf r) = p := by simpa [hf] using hp
          subst hp'
          obtain ⟨r₁, hr₁, rfl⟩ := hinv.seed_mem s hc
          exact ⟨r₁, List.mem_append_left _ hr₁,
            r, List.mem_append_right _ (List.mem_singleton_self r), rfl, hf⟩
        · simp [hf] at hp
      · simp at hp
    · simp [hek] at hp

theorem kemTrackLoggedInv_stepKemFailSend {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512) :
    KemTrackLoggedInv K (stepKemFailSend F K tr Q r) (log ++ [r]) where
  seed_mem s' hs' := by
    unfold stepKemFailSend at hs'
    cases hsend : (tr.st Q).send K (coinBytes r) with
    | error _ =>
      simp only [hsend] at hs'
      obtain ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s' hs'
      exact ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
    | ok val =>
      rcases val with ⟨out, _⟩
      simp only [hsend] at hs'
      exact nextCoins_seed_mem r hinv.seed_mem hs'
  cand_mem _ hp := stepKemFailSend_cand_mem hinv Q r hp

theorem kemTrackLoggedInv_stepKemFailSend_candOnly {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (r : BitVec 512) :
    KemTrackLoggedInv K { tr with cand := (stepKemFailSend F K tr Q r).cand } (log ++ [r]) where
  seed_mem s' hs' := let ⟨r₁, hr₁, hEq⟩ := hinv.seed_mem s' hs'; ⟨r₁, List.mem_append_left _ hr₁, hEq⟩
  cand_mem _ hp := stepKemFailSend_cand_mem hinv Q r hp

theorem stepKemFailDeliver_cand {F : ShaCompress} (K : MlKem)
    (tr : KemFailTrackState F) (Q : Party) (j : ℕ) :
    (stepKemFailDeliver F K tr Q j).cand = tr.cand := by
  unfold stepKemFailDeliver
  split <;> [rfl; (split <;> [(dsimp only; split <;> [(split <;> rfl); rfl]); rfl])]

theorem stepKemFailDeliver_c_eq_seed {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {Q : Party} {j : ℕ} {s' : Seed}
    (hs' : (stepKemFailDeliver F K tr Q j).c = .seed s') : tr.c = .seed s' := by
  unfold stepKemFailDeliver at hs'
  split at hs' <;> [exact hs'; (split at hs' <;>
    [(dsimp only at hs'; split at hs' <;> [(split at hs' <;> [cases hs'; exact hs']); exact hs']); exact hs'])]

theorem kemTrackLoggedInv_stepKemFailDeliver {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (Q : Party) (j : ℕ) :
    KemTrackLoggedInv K (stepKemFailDeliver F K tr Q j) log where
  seed_mem s' hs' := hinv.seed_mem s' (stepKemFailDeliver_c_eq_seed hs')
  cand_mem p hp := hinv.cand_mem p (stepKemFailDeliver_cand K tr Q j ▸ hp)

/-- Under `KemTrackLoggedInv`, `tr.cand.isSome` implies `K.KemFailBad (log.map coinBytes)`. -/
theorem kemFailBad_of_kemTrackLoggedInv {F : ShaCompress} {K : MlKem}
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hcand : tr.cand.isSome = true) :
    K.KemFailBad (log.map coinBytes) = true := by
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp hcand
  obtain ⟨r₁, hr₁, r₂, hr₂, rfl, hfail⟩ := hinv.cand_mem p hp
  exact kemFailBad_of_honestExchangeFails_coinEquiv K log hr₁ hr₂ hfail

theorem cand_eq_none_of_kemTrackLoggedInv {F : ShaCompress} (K : MlKem)
    {tr : KemFailTrackState F} {log : List (BitVec 512)}
    (hinv : KemTrackLoggedInv K tr log) (hgood : K.KemFailBad (log.map coinBytes) = false) :
    tr.cand = none := by
  cases hc : tr.cand with
  | none => rfl
  | some _ =>
    have hbad := kemFailBad_of_kemTrackLoggedInv hinv (by simp [hc])
    rw [hgood] at hbad
    cases hbad

/-! ## Ghost-coupled online agreement -/

private local instance instLawfulMonadWriterTListCoin {Coins : Type} {M : Type → Type}
    [Monad M] [LawfulMonad M] : LawfulMonad (WriterT (List Coins) M) :=
  LawfulMonad.mk' (id_map := fun _ => by ext; simp) (pure_bind := fun _ _ => by ext; simp)
    (bind_assoc := fun _ _ _ => by ext; simp) (bind_pure_comp := fun _ _ => by ext; simp)

@[simp] private theorem smSchemeCoinLogged_send_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    ((smSchemeCoinLogged sm).send st m r).run = pure (sm.send st m r, [r]) := by
  simp [smSchemeCoinLogged, MonadWriter.tell]

@[simp] private theorem smSchemeCoinLogged_receive_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    ((smSchemeCoinLogged sm).receive st c rc).run = pure (sm.receive st c rc, []) := by
  simp [smSchemeCoinLogged]

@[simp] private theorem smSchemeCoinLogged_initState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (k : Key) (b : Bool) :
    (smSchemeCoinLogged sm).initState k b = initState sm.sendPart k b := rfl

private def embedCoinW {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    StateT (List Coins) ProbComp α :=
  fun pre => (fun zw => (zw.1, pre ++ zw.2)) <$> m.run

@[simp] private theorem embedCoinW_run {Coins α : Type}
    (m : WriterT (List Coins) ProbComp α) (pre : List Coins) :
    (embedCoinW m).run pre = (fun zw => (zw.1, pre ++ zw.2)) <$> m.run := rfl

@[simp] private theorem embedCoinW_run_nil {Coins α : Type} (m : WriterT (List Coins) ProbComp α) :
    (embedCoinW m).run [] = m.run := by simp

@[simp] private theorem embedCoinW_pure {Coins α : Type} (a : α) :
    embedCoinW (pure a : WriterT (List Coins) ProbComp α) = pure a := by ext pre; simp

@[simp] private theorem embedCoinW_map {Coins α β : Type} (f : α → β)
    (m : WriterT (List Coins) ProbComp α) :
    embedCoinW (f <$> m) = f <$> embedCoinW m := by ext pre; simp [Functor.map_map]

@[simp] private theorem embedCoinW_liftM {Coins α : Type} (c : ProbComp α) :
    embedCoinW (liftM c : WriterT (List Coins) ProbComp α) = liftM c := by
  ext pre
  change (fun zw => (zw.1, pre ++ zw.2)) <$> (liftM c : WriterT (List Coins) ProbComp α).run =
    (StateT.lift c).run pre
  dsimp [liftM, monadLift, MonadLiftT.monadLift, MonadLift.monadLift, WriterT.liftTell]
  simp [map_eq_bind_pure_comp]

@[simp] private theorem embedCoinW_bind {Coins α β : Type}
    (m : WriterT (List Coins) ProbComp α) (f : α → WriterT (List Coins) ProbComp β) :
    embedCoinW (m >>= f) = embedCoinW m >>= fun a => embedCoinW (f a) := by
  ext pre
  simp only [embedCoinW_run, WriterT.run_bind, StateT.run_bind, map_eq_bind_pure_comp,
    Function.comp_apply, bind_assoc, pure_bind, List.append_assoc]; rfl

@[simp] private theorem embedCoinW_smSchemeCoinLogged_send {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (r : Coins) :
    embedCoinW ((smSchemeCoinLogged sm).send st m r) =
      (fun pre => pure (sm.send st m r, pre ++ [r])) := by
  ext pre; change _ = pure (sm.send st m r, pre ++ [r]); simp

@[simp] private theorem embedCoinW_smSchemeCoinLogged_receive {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (c : C) (rc : RCoins) :
    embedCoinW ((smSchemeCoinLogged sm).receive st c rc) = pure (sm.receive st c rc) := by
  ext pre; simp

private def embedCoinS1 {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    StateT σ (StateT (List Coins) ProbComp) α :=
  fun s => embedCoinW (m.run s)

@[simp] private theorem embedCoinS1_run {Coins σ α : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α) (s : σ) :
    (embedCoinS1 m).run s = embedCoinW (m.run s) := rfl

@[simp] private theorem embedCoinS1_pure {Coins σ α : Type} (a : α) :
    embedCoinS1 (pure a : StateT σ (WriterT (List Coins) ProbComp) α) = pure a := by
  ext s pre; simp

@[simp] private theorem embedCoinS1_map {Coins σ α β : Type} (f : α → β)
    (m : StateT σ (WriterT (List Coins) ProbComp) α) :
    embedCoinS1 (f <$> m) = f <$> embedCoinS1 m := by ext s pre; simp

@[simp] private theorem embedCoinS1_bind {Coins σ α β : Type}
    (m : StateT σ (WriterT (List Coins) ProbComp) α)
    (f : α → StateT σ (WriterT (List Coins) ProbComp) β) :
    embedCoinS1 (m >>= f) = embedCoinS1 m >>= fun a => embedCoinS1 (f a) := by
  ext s pre; simp

@[simp] private theorem embedCoinS1_get {Coins σ : Type} :
    embedCoinS1 (get : StateT σ (WriterT (List Coins) ProbComp) σ) = get := by
  ext s pre; simp

@[simp] private theorem embedCoinS1_set {Coins σ : Type} (s' : σ) :
    embedCoinS1 (set s' : StateT σ (WriterT (List Coins) ProbComp) PUnit) = set s' := by
  ext s pre; simp

@[simp] private theorem embedCoinS1_lift {Coins σ α : Type}
    (m : WriterT (List Coins) ProbComp α) :
    embedCoinS1 (StateT.lift m : StateT σ (WriterT (List Coins) ProbComp) α) =
      StateT.lift (embedCoinW m) := by ext s pre; simp [StateT.run_lift]

@[simp] private theorem embedCoinS1_liftStateT {Coins σ α : Type} (x : StateT σ ProbComp α) :
    embedCoinS1 (liftStateT (n := WriterT (List Coins) ProbComp) x) =
      liftStateT (n := StateT (List Coins) ProbComp) x := by
  ext s pre; exact congrFun (congrArg StateT.run (embedCoinW_liftM (x s))) pre

private theorem embedCoinS1_simulateQ {Coins ι σ : Type} {ospec : OracleSpec ι}
    (impl : QueryImpl ospec (StateT σ (WriterT (List Coins) ProbComp)))
    (impl₀ : QueryImpl ospec (StateT σ (StateT (List Coins) ProbComp)))
    (himpl : ∀ t, embedCoinS1 (impl t) = impl₀ t) {α : Type} (oa : OracleComp ospec α) :
    embedCoinS1 (simulateQ impl oa) = simulateQ impl₀ oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t m ih =>
    rw [simulateQ_bind, simulateQ_spec_query, embedCoinS1_bind, himpl t,
      simulateQ_bind, simulateQ_spec_query]
    congr 1; funext u; exact ih u

private def smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) :
    SMSchemeRM (StateT (List Coins) ProbComp) Key St Msg Coins RCoins C where
  initA := sm.initA
  initB := sm.initB
  send st m r := fun log => pure (sm.send st m r, log ++ [r])
  receive st c rc := pure (sm.receive st c rc)

@[simp] private theorem smSchemeCoinState_send_run {Key St Msg Coins RCoins C : Type}
    (sm : SMSchemeR Key St Msg Coins RCoins C) (st : St) (m : Msg) (coins : Coins)
    (log : List Coins) :
    ((smSchemeCoinState sm).send st m coins).run log =
      pure (sm.send st m coins, log ++ [coins]) := rfl

private theorem embedCoinS1_oracleImplRM_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    embedCoinS1 (oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg q) =
      oracleImplRM (smSchemeCoinState sm) Δ qep cfg q := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · change embedCoinS1 (transmitRM (smSchemeCoinLogged sm) Δ qep cfg (P, m, r)) =
      transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)
    unfold transmitRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ => simp [smSchemeCoinState]
  · change embedCoinS1 (challRM (smSchemeCoinLogged sm) Δ qep cfg (P, m₀, m₁, r)) =
      challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)
    unfold challRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact embedCoinS1_pure _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind,
        embedCoinS1_lift, embedCoinW_liftM, embedCoinS1_pure]
      congr 1; funext ⟨coins, bad⟩
      cases s.epMgmt Δ qep P bad with
      | none => exact embedCoinS1_pure _
      | some s₁ =>
        dsimp only
        cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
          simp [smSchemeCoinState]
  · change embedCoinS1 (deliverRM (smSchemeCoinLogged sm) cfg (P, c)) =
      deliverRM (smSchemeCoinState sm) cfg (P, c)
    unfold deliverRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_pure]
    cases s.inTransit P.other c with
    | none => exact embedCoinS1_pure _
    | some r =>
      dsimp only
      simp only [embedCoinS1_bind, embedCoinS1_lift, embedCoinW_liftM,
        embedCoinW_smSchemeCoinLogged_receive, smSchemeCoinState]
      congr 1; funext rc; congr 1; funext out
      cases out with
      | none => split_ifs <;> simp
      | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · change embedCoinS1 (injectRM (smSchemeCoinLogged sm) Δ qep cfg (P, c)) =
      injectRM (smSchemeCoinState sm) Δ qep cfg (P, c)
    unfold injectRM; simp only [embedCoinS1_bind, embedCoinS1_get]; congr 1; funext s
    cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte, embedCoinS1_bind, embedCoinS1_lift,
        embedCoinW_liftM, embedCoinW_smSchemeCoinLogged_receive, embedCoinS1_pure, smSchemeCoinState]
    congr 1; funext rc; congr 1; funext out
    cases out with
    | none => exact embedCoinS1_pure _
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp
  · exact embedCoinS1_liftStateT _

private theorem gameRCoinLogged_eq_state {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    gameRCoinLogged sm Δ qep cfg A =
      (StateT.run · []) do
        let b ← liftM ($ᵗ Bool : ProbComp Bool)
        let k ← liftM ($ᵗ Key : ProbComp Key)
        let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
            (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
          oracleImplRM (smSchemeCoinState sm) Δ qep cfg
        let (b', s) ← (simulateQ impl A).run (initState sm.sendPart k b)
        return (b == b' || s.win) := by
  unfold gameRCoinLogged; rw [← embedCoinW_run_nil]; congr 1
  simp only [embedCoinW_bind, embedCoinW_liftM, smSchemeCoinLogged_initState]
  congr 1; funext b; congr 1; funext k
  have himpl : ∀ t : (unifSpec + spec St Msg Coins C).Domain,
      embedCoinS1 (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (WriterT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinLogged sm) Δ qep cfg) t) =
      (((QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
        oracleImplRM (smSchemeCoinState sm) Δ qep cfg) t) := by
    rintro (u | q)
    · change embedCoinS1 (StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))) =
        StateT.lift (liftM (QueryImpl.ofLift unifSpec ProbComp u))
      rw [embedCoinS1_lift, embedCoinW_liftM]
    · exact embedCoinS1_oracleImplRM_eq sm Δ qep cfg q
  rw [← embedCoinS1_run, embedCoinS1_simulateQ _ _ himpl A]; ext pre; simp

@[simp] private theorem liftM_state_run {τ α : Type} (c : ProbComp α) (t : τ) :
    (liftM c : StateT τ ProbComp α).run t = (c >>= fun a => pure (a, t)) := rfl

@[simp] private theorem liftStateT_run_state {σ τ α : Type}
    (x : StateT σ ProbComp α) (s : σ) (t : τ) :
    ((liftStateT (n := StateT τ ProbComp) x).run s).run t = (x.run s >>= fun a => pure (a, t)) := rfl

@[simp] private theorem stateT_run_modify {σ : Type} (f : σ → σ) (s : σ) :
    (modify f : StateT σ ProbComp PUnit).run s = pure ((), f s) := rfl

private def DropStateEq {σ α : Type} (m₁ : StateT σ ProbComp α) (m₂ : ProbComp α) : Prop :=
  ∀ s : σ, Prod.fst <$> m₁.run s = m₂

private def DropStateEqS1 {σ ρ α : Type}
    (m₁ : StateT ρ (StateT σ ProbComp) α) (m₂ : StateT ρ ProbComp α) : Prop :=
  ∀ r, DropStateEq (m₁.run r) (m₂.run r)

private theorem DropStateEq.pure {σ α : Type} (a : α) :
    DropStateEq (σ := σ) (pure a) (pure a) := fun _ => by simp

private theorem DropStateEq.liftM {σ α : Type} (c : ProbComp α) :
    DropStateEq (σ := σ) (liftM c) c := fun _ => by simp

private theorem DropStateEq.bind {σ α β : Type}
    {m₁ : StateT σ ProbComp α} {m₂ : ProbComp α}
    {k₁ : α → StateT σ ProbComp β} {k₂ : α → ProbComp β}
    (hm : DropStateEq m₁ m₂) (hk : ∀ a, DropStateEq (k₁ a) (k₂ a)) :
    DropStateEq (m₁ >>= k₁) (m₂ >>= k₂) := fun s => by
  calc Prod.fst <$> (m₁ >>= k₁).run s
      = m₁.run s >>= fun x => Prod.fst <$> (k₁ x.1).run x.2 := by
          simp [StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]
    _ = m₁.run s >>= fun x => k₂ x.1 := by congr 1; funext x; exact hk x.1 x.2
    _ = (Prod.fst <$> m₁.run s) >>= k₂ := by simp [map_eq_bind_pure_comp, bind_assoc]
    _ = m₂ >>= k₂ := by rw [hm s]

private theorem DropStateEqS1.pure {σ ρ α : Type} (a : α) :
    DropStateEqS1 (σ := σ) (ρ := ρ) (pure a) (pure a) := fun r => DropStateEq.pure (a, r)

private theorem DropStateEqS1.lift {σ ρ α : Type}
    {m₁ : StateT σ ProbComp α} {m₂ : ProbComp α} (hm : DropStateEq m₁ m₂) :
    DropStateEqS1 (ρ := ρ) (StateT.lift m₁) (StateT.lift m₂) := fun r => by
  simp only [StateT.run_lift]; exact DropStateEq.bind hm fun a => DropStateEq.pure (a, r)

private theorem DropStateEqS1.liftStateT {σ ρ α : Type} (x : StateT ρ ProbComp α) :
    DropStateEqS1 (σ := σ) (liftStateT x) x := fun r => DropStateEq.liftM (x r)

private theorem DropStateEqS1.bind {σ ρ α β : Type}
    {m₁ : StateT ρ (StateT σ ProbComp) α} {m₂ : StateT ρ ProbComp α}
    {k₁ : α → StateT ρ (StateT σ ProbComp) β} {k₂ : α → StateT ρ ProbComp β}
    (hm : DropStateEqS1 m₁ m₂) (hk : ∀ a, DropStateEqS1 (k₁ a) (k₂ a)) :
    DropStateEqS1 (m₁ >>= k₁) (m₂ >>= k₂) := fun r => by
  simp only [StateT.run_bind]; exact DropStateEq.bind (hm r) fun x => hk x.1 x.2

private theorem DropStateEqS1.simulateQ {ι σ ρ : Type} {ospec : OracleSpec ι}
    (impl₁ : QueryImpl ospec (StateT ρ (StateT σ ProbComp)))
    (impl₂ : QueryImpl ospec (StateT ρ ProbComp))
    (himpl : ∀ t, DropStateEqS1 (impl₁ t) (impl₂ t)) {α : Type} (oa : OracleComp ospec α) :
    DropStateEqS1 (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact DropStateEqS1.pure a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact DropStateEqS1.bind (himpl t) ih

private abbrev TL (F : ShaCompress) (C : Type) : Type :=
  KemFailSessionTrack F C × List (BitVec 512)

private def ProjStateEq {σ τ α : Type} (π : σ → τ)
    (m₁ : StateT σ ProbComp α) (m₂ : StateT τ ProbComp α) : Prop :=
  ∀ s : σ, (fun z : α × σ => (z.1, π z.2)) <$> m₁.run s = m₂.run (π s)

private def ProjStateEqS1 {σ τ ρ α : Type} (π : σ → τ)
    (m₁ : StateT ρ (StateT σ ProbComp) α) (m₂ : StateT ρ (StateT τ ProbComp) α) : Prop :=
  ∀ r, ProjStateEq π (m₁.run r) (m₂.run r)

private theorem ProjStateEq.pure {σ τ α : Type} (π : σ → τ) (a : α) :
    ProjStateEq π (pure a) (pure a) := fun _ => by simp

private theorem ProjStateEq.liftM {σ τ α : Type} (π : σ → τ) (c : ProbComp α) :
    ProjStateEq π (liftM c) (liftM c) := fun _ => by
  simp [map_eq_bind_pure_comp, bind_assoc]

private theorem ProjStateEq.bind {σ τ α β : Type} {π : σ → τ}
    {m₁ : StateT σ ProbComp α} {m₂ : StateT τ ProbComp α}
    {k₁ : α → StateT σ ProbComp β} {k₂ : α → StateT τ ProbComp β}
    (hm : ProjStateEq π m₁ m₂) (hk : ∀ a, ProjStateEq π (k₁ a) (k₂ a)) :
    ProjStateEq π (m₁ >>= k₁) (m₂ >>= k₂) := fun s => by
  calc (fun z : β × σ => (z.1, π z.2)) <$> (m₁ >>= k₁).run s
      = m₁.run s >>= fun x => (fun z : β × σ => (z.1, π z.2)) <$> (k₁ x.1).run x.2 := by
          simp [StateT.run_bind, map_eq_bind_pure_comp, bind_assoc]
    _ = m₁.run s >>= fun x => (k₂ x.1).run (π x.2) := by congr 1; funext x; exact hk x.1 x.2
    _ = ((fun x : α × σ => (x.1, π x.2)) <$> m₁.run s) >>= fun y => (k₂ y.1).run y.2 := by
          simp [map_eq_bind_pure_comp, bind_assoc]
    _ = (m₂ >>= k₂).run (π s) := by rw [hm s]; simp [StateT.run_bind]

private theorem ProjStateEqS1.pure {σ τ ρ α : Type} (π : σ → τ) (a : α) :
    ProjStateEqS1 (ρ := ρ) π (pure a) (pure a) := fun r => ProjStateEq.pure π (a, r)

private theorem ProjStateEqS1.get {σ τ ρ : Type} (π : σ → τ) :
    ProjStateEqS1 (ρ := ρ) π get get := fun r => ProjStateEq.pure π (r, r)

private theorem ProjStateEqS1.set {σ τ ρ : Type} (π : σ → τ) (r' : ρ) :
    ProjStateEqS1 (ρ := ρ) π (set r') (set r') := fun _ => ProjStateEq.pure π ((), r')

private theorem ProjStateEqS1.lift {σ τ ρ α : Type} {π : σ → τ}
    {m₁ : StateT σ ProbComp α} {m₂ : StateT τ ProbComp α} (hm : ProjStateEq π m₁ m₂) :
    ProjStateEqS1 (ρ := ρ) π (StateT.lift m₁) (StateT.lift m₂) := fun r => by
  simp only [StateT.run_lift]; exact ProjStateEq.bind hm fun a => ProjStateEq.pure π (a, r)

private theorem ProjStateEqS1.liftStateT {σ τ ρ α : Type} (π : σ → τ) (x : StateT ρ ProbComp α) :
    ProjStateEqS1 π (liftStateT x) (liftStateT x) := fun r => ProjStateEq.liftM π (x r)

private theorem ProjStateEqS1.bind {σ τ ρ α β : Type} {π : σ → τ}
    {m₁ : StateT ρ (StateT σ ProbComp) α} {m₂ : StateT ρ (StateT τ ProbComp) α}
    {k₁ : α → StateT ρ (StateT σ ProbComp) β} {k₂ : α → StateT ρ (StateT τ ProbComp) β}
    (hm : ProjStateEqS1 π m₁ m₂) (hk : ∀ a, ProjStateEqS1 π (k₁ a) (k₂ a)) :
    ProjStateEqS1 π (m₁ >>= k₁) (m₂ >>= k₂) := fun r => by
  simp only [StateT.run_bind]; exact ProjStateEq.bind (hm r) fun x => hk x.1 x.2

private theorem ProjStateEqS1.simulateQ {ι σ τ ρ : Type} {ospec : OracleSpec ι} (π : σ → τ)
    (impl₁ : QueryImpl ospec (StateT ρ (StateT σ ProbComp)))
    (impl₂ : QueryImpl ospec (StateT ρ (StateT τ ProbComp)))
    (himpl : ∀ t, ProjStateEqS1 π (impl₁ t) (impl₂ t)) {α : Type} (oa : OracleComp ospec α) :
    ProjStateEqS1 π (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact ProjStateEqS1.pure π a
  | query_bind t k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact ProjStateEqS1.bind (himpl t) ih

private structure AgreeInv {σ α : Type} (inv good : σ → Prop)
    (m₁ m₂ : StateT σ ProbComp α) : Prop where
  inv₁ : ∀ s, inv s → ∀ z ∈ support (m₁.run s), inv z.2
  inv₂ : ∀ s, inv s → ∀ z ∈ support (m₂.run s), inv z.2
  pres₁ : ∀ s, inv s → ¬ good s → ∀ z ∈ support (m₁.run s), ¬ good z.2
  pres₂ : ∀ s, inv s → ¬ good s → ∀ z ∈ support (m₂.run s), ¬ good z.2
  agree : ∀ s, inv s → good s → ∀ p : α × σ → Prop,
    Pr{let z ← m₁.run s}[p z ∧ good z.2] = Pr{let z ← m₂.run s}[p z ∧ good z.2]

private def AgreeInvS1 {σ τ α : Type} (inv good : σ → Prop)
    (m₁ m₂ : StateT τ (StateT σ ProbComp) α) : Prop :=
  ∀ t, AgreeInv inv good (m₁.run t) (m₂.run t)

private theorem AgreeInv.pure {σ α : Type} (inv good : σ → Prop) (a : α) :
    AgreeInv inv good (pure a : StateT σ ProbComp α) (pure a) where
  inv₁ s hs _ hz := by simp at hz; rcases hz with ⟨_, rfl⟩; exact hs
  inv₂ s hs _ hz := by simp at hz; rcases hz with ⟨_, rfl⟩; exact hs
  pres₁ s _ hb _ hz := by simp at hz; rcases hz with ⟨_, rfl⟩; exact hb
  pres₂ s _ hb _ hz := by simp at hz; rcases hz with ⟨_, rfl⟩; exact hb
  agree _ _ _ _ := rfl

private theorem AgreeInv.get {σ : Type} (inv good : σ → Prop) :
    AgreeInv inv good (get : StateT σ ProbComp σ) get where
  inv₁ s hs _ hz := by simp [StateT.run_get] at hz; rcases hz with ⟨_, rfl⟩; exact hs
  inv₂ s hs _ hz := by simp [StateT.run_get] at hz; rcases hz with ⟨_, rfl⟩; exact hs
  pres₁ s _ hb _ hz := by simp [StateT.run_get] at hz; rcases hz with ⟨_, rfl⟩; exact hb
  pres₂ s _ hb _ hz := by simp [StateT.run_get] at hz; rcases hz with ⟨_, rfl⟩; exact hb
  agree _ _ _ _ := rfl

private theorem AgreeInv.liftM {σ α : Type} (inv good : σ → Prop) (c : ProbComp α) :
    AgreeInv inv good (liftM c : StateT σ ProbComp α) (liftM c) where
  inv₁ s hs z hz := by
    simp only [liftM_state_run, support_bind, Set.mem_iUnion, exists_prop, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hs
  inv₂ s hs z hz := by
    simp only [liftM_state_run, support_bind, Set.mem_iUnion, exists_prop, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hs
  pres₁ s _ hb z hz := by
    simp only [liftM_state_run, support_bind, Set.mem_iUnion, exists_prop, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hb
  pres₂ s _ hb z hz := by
    simp only [liftM_state_run, support_bind, Set.mem_iUnion, exists_prop, support_pure,
      Set.mem_singleton_iff] at hz
    rcases hz with ⟨_, _, rfl⟩; exact hb
  agree _ _ _ _ := rfl

private theorem ae_indicator_of_pres {σ α β : Type}
    [MeasurableSpace (α × σ)] [DiscreteMeasurableSpace (α × σ)]
    {inv good : σ → Prop} (c : ProbComp (α × σ)) (k : α → StateT σ ProbComp β)
    (p : β × σ → Prop) (hinv : ∀ x ∈ support c, inv x.2)
    (hpres : ∀ x : α × σ, inv x.2 → ¬ good x.2 → ∀ z ∈ support ((k x.1).run x.2), ¬ good z.2) :
    ∀ᵐ x ∂𝒟[c], Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2] =
      {x : α × σ | inv x.2 ∧ good x.2}.indicator
        (fun x => Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2]) x := by
  let G : Set (α × σ) := {x | inv x.2 ∧ good x.2}
  let F (x : α × σ) : ℝ≥0∞ := Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2]
  change ∀ᵐ x ∂𝒟[c], F x = G.indicator F x
  rw [MeasureTheory.ae_iff]
  have hsub : {x : α × σ | ¬ F x = G.indicator F x} ⊆ (support c)ᶜ := by
    intro x hne hsupp
    have hix : inv x.2 := hinv x hsupp
    by_cases hgx : good x.2
    · exact hne (Set.indicator_of_mem (s := G) ⟨hix, hgx⟩ F).symm
    · have hxG : x ∉ G := fun h => hgx h.2
      have hind : G.indicator F x = 0 := Set.indicator_of_notMem hxG F
      change ¬ F x = G.indicator F x at hne
      rw [hind] at hne
      exact hne (prEvent_eq_zero_of_forall_mem_support _ _ fun z hz ⟨_, hgz⟩ =>
        hpres x hix hgx z hz hgz)
  have hnull : (𝒟[c]) (support c)ᶜ = 0 := by
    change (𝒟[c]) {x | x ∉ support c} = 0
    rw [← prEvent_eq_evalDist_of_discrete]
    exact prEvent_eq_zero_of_forall_mem_support _ _ fun _ hx hnot => hnot hx
  exact MeasureTheory.measure_mono_null hsub hnull

private theorem AgreeInv.bind {σ α β : Type} {inv good : σ → Prop}
    {m₁ m₂ : StateT σ ProbComp α} {k₁ k₂ : α → StateT σ ProbComp β}
    (hm : AgreeInv inv good m₁ m₂) (hk : ∀ a, AgreeInv inv good (k₁ a) (k₂ a)) :
    AgreeInv inv good (m₁ >>= k₁) (m₂ >>= k₂) where
  inv₁ s hs z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩; exact (hk x.1).inv₁ x.2 (hm.inv₁ s hs x hx) z hz
  inv₂ s hs z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩; exact (hk x.1).inv₂ x.2 (hm.inv₂ s hs x hx) z hz
  pres₁ s hs hb z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩; exact (hk x.1).pres₁ x.2 (hm.inv₁ s hs x hx) (hm.pres₁ s hs hb x hx) z hz
  pres₂ s hs hb z hz := by
    simp only [StateT.run_bind, support_bind, Set.mem_iUnion, exists_prop] at hz
    rcases hz with ⟨x, hx, hz⟩; exact (hk x.1).pres₂ x.2 (hm.inv₂ s hs x hx) (hm.pres₂ s hs hb x hx) z hz
  agree s hs hg p := by
    simp only [StateT.run_bind]
    let : MeasurableSpace (α × σ) := ⊤
    let G : Set (α × σ) := {x | inv x.2 ∧ good x.2}
    let F (k : α → StateT σ ProbComp β) (x : α × σ) : ℝ≥0∞ :=
      Pr{let z ← (k x.1).run x.2}[p z ∧ good z.2]
    have hFG : G.indicator (F k₁) = G.indicator (F k₂) := funext fun x => by
      by_cases hx : x ∈ G
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact (hk x.1).agree x.2 hx.1 hx.2 p
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    have hae₁ := ae_indicator_of_pres (m₁.run s) k₁ p (hm.inv₁ s hs) (fun x => (hk x.1).pres₁ x.2)
    have hae₂ := ae_indicator_of_pres (m₂.run s) k₂ p (hm.inv₂ s hs) (fun x => (hk x.1).pres₂ x.2)
    have hrestrict : (𝒟[m₁.run s]).restrict G = (𝒟[m₂.run s]).restrict G :=
      Measure.ext fun A hA => by
        have hAG : A ∩ G = {z | (z ∈ A ∧ inv z.2) ∧ good z.2} :=
          Set.ext fun _ => ⟨fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩, fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩⟩
        rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hAG,
          ← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
        exact hm.agree s hs hg (fun z => z ∈ A ∧ inv z.2)
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
    change ∫⁻ x, F k₁ x ∂𝒟[m₁.run s] = ∫⁻ x, F k₂ x ∂𝒟[m₂.run s]
    calc ∫⁻ x, F k₁ x ∂𝒟[m₁.run s]
        = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₁.run s] := by
            rw [← hFG]; exact MeasureTheory.lintegral_congr_ae hae₁
      _ = ∫⁻ x, F k₂ x ∂((𝒟[m₁.run s]).restrict G) := lintegral_indicator MeasurableSet.of_discrete _
      _ = ∫⁻ x, F k₂ x ∂((𝒟[m₂.run s]).restrict G) := by rw [hrestrict]
      _ = ∫⁻ x, G.indicator (F k₂) x ∂𝒟[m₂.run s] :=
            (lintegral_indicator MeasurableSet.of_discrete _).symm
      _ = ∫⁻ x, F k₂ x ∂𝒟[m₂.run s] := (MeasureTheory.lintegral_congr_ae hae₂).symm

private theorem AgreeInvS1.pure {σ τ α : Type} (inv good : σ → Prop) (a : α) :
    AgreeInvS1 inv good (pure a : StateT τ (StateT σ ProbComp) α) (pure a) :=
  fun t => AgreeInv.pure inv good (a, t)

private theorem AgreeInvS1.get {σ τ : Type} (inv good : σ → Prop) :
    AgreeInvS1 inv good (get : StateT τ (StateT σ ProbComp) τ) get :=
  fun t => AgreeInv.pure inv good (t, t)

private theorem AgreeInvS1.set {σ τ : Type} (inv good : σ → Prop) (t' : τ) :
    AgreeInvS1 inv good (set t' : StateT τ (StateT σ ProbComp) PUnit) (set t') :=
  fun _ => AgreeInv.pure inv good ((), t')

private theorem AgreeInvS1.lift {σ τ α : Type} {inv good : σ → Prop}
    {m₁ m₂ : StateT σ ProbComp α} (hm : AgreeInv inv good m₁ m₂) :
    AgreeInvS1 inv good (StateT.lift m₁ : StateT τ (StateT σ ProbComp) α) (StateT.lift m₂) :=
  fun t => by simp only [StateT.run_lift]; exact AgreeInv.bind hm fun a => AgreeInv.pure inv good (a, t)

private theorem AgreeInvS1.liftStateT {σ τ α : Type} (inv good : σ → Prop)
    (x : StateT τ ProbComp α) :
    AgreeInvS1 inv good (liftStateT x : StateT τ (StateT σ ProbComp) α) (liftStateT x) :=
  fun t => AgreeInv.liftM inv good (x t)

private theorem AgreeInvS1.bind {σ τ α β : Type} {inv good : σ → Prop}
    {m₁ m₂ : StateT τ (StateT σ ProbComp) α} {k₁ k₂ : α → StateT τ (StateT σ ProbComp) β}
    (hm : AgreeInvS1 inv good m₁ m₂) (hk : ∀ a, AgreeInvS1 inv good (k₁ a) (k₂ a)) :
    AgreeInvS1 inv good (m₁ >>= k₁) (m₂ >>= k₂) :=
  fun t => by simp only [StateT.run_bind]; exact AgreeInv.bind (hm t) fun x => hk x.1 x.2

private theorem AgreeInvS1.simulateQ {ι σ τ : Type} {ospec : OracleSpec ι} {inv good : σ → Prop}
    (impl₁ impl₂ : QueryImpl ospec (StateT τ (StateT σ ProbComp)))
    (himpl : ∀ q, AgreeInvS1 inv good (impl₁ q) (impl₂ q)) {α : Type} (oa : OracleComp ospec α) :
    AgreeInvS1 inv good (simulateQ impl₁ oa) (simulateQ impl₂ oa) := by
  induction oa using OracleComp.inductionOn with
  | pure a => exact AgreeInvS1.pure inv good a
  | query_bind q k ih =>
    rw [simulateQ_bind, simulateQ_spec_query, simulateQ_bind, simulateQ_spec_query]
    exact AgreeInvS1.bind (himpl q) ih

private theorem deliverRM_smSchemeCoinState_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (cfg : ConfigR St Msg C) (q : Party × C) :
    deliverRM (smSchemeCoinState sm) cfg q = liftStateT (deliverR sm cfg q) := by
  rcases q with ⟨P, c⟩; ext s log
  rw [liftStateT_run_state]
  unfold deliverRM deliverR smSchemeCoinState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind]
  cases s.inTransit P.other c with
  | none => simp
  | some r =>
    dsimp only
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, bind_assoc, pure_bind]
    congr 1; funext rc
    cases sm.receive (s.st P) c rc with
    | none => split_ifs <;> simp [StateT.run_map]
    | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp [StateT.run_map]

private theorem injectRM_smSchemeCoinState_eq {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : Party × C) :
    injectRM (smSchemeCoinState sm) Δ qep cfg q = liftStateT (injectR sm Δ qep cfg q) := by
  rcases q with ⟨P, c⟩; ext s log
  rw [liftStateT_run_state]
  unfold injectRM injectR smSchemeCoinState
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases (s.win || (s.inTransit P.other c).isSome || !(s.safeInj Δ) || !(cfg.injOK c)) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, pure_bind, StateT.run_bind,
      StateT.run_lift, liftM_state_run, bind_assoc]
  congr 1; funext rc
  cases sm.receive (s.st P) c rc with
  | none => simp
  | some x => rcases x with ⟨st', t', i', m'⟩; dsimp only; split_ifs <;> simp [StateT.run_map]

private theorem dropStateEqS1_oracleImplRM_smSchemeCoinState {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Coins] [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (q : (spec St Msg Coins C).Domain) :
    DropStateEqS1 (oracleImplRM (smSchemeCoinState sm) Δ qep cfg q)
      (oracleImplR sm Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨P, c⟩) | ⟨P, c⟩) | P
  · intro s₀ log
    change Prod.fst <$> ((transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r)).run s₀).run log =
      (transmitR sm Δ qep cfg (P, m, r)).run s₀
    unfold transmitRM transmitR transmitImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK s₀ P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, map_pure, StateT.run_bind, StateT.run_get, pure_bind]
    cases s₀.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext ⟨coins, bad⟩
    cases s₀.epMgmt Δ qep P bad with
    | none => simp
    | some s₁ =>
      simp [SMSchemeR.sendPart, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_map]
  · intro s₀ log
    change Prod.fst <$> ((challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r)).run s₀).run log =
      (challR sm Δ qep cfg (P, m₀, m₁, r)).run s₀
    unfold challRM challR challImpl
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases cfg.sendOK s₀ P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, StateT.run_pure, map_pure, StateT.run_bind, StateT.run_get, pure_bind]
    cases s₀.win <;> simp only [Bool.false_eq_true, ↓reduceIte, StateT.run_pure, map_pure]
    simp only [StateT.run_bind, StateT.run_lift, liftM_state_run, map_eq_bind_pure_comp,
      bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext ⟨coins, bad⟩
    cases s₀.epMgmt Δ qep P bad with
    | none => simp
    | some s₁ =>
      dsimp only
      cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P))) <;>
        simp [SMSchemeR.sendPart, StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_map]
  · change DropStateEqS1 (deliverRM (smSchemeCoinState sm) cfg (P, c)) (deliverR sm cfg (P, c))
    rw [deliverRM_smSchemeCoinState_eq]; exact DropStateEqS1.liftStateT _
  · change DropStateEqS1 (injectRM (smSchemeCoinState sm) Δ qep cfg (P, c))
      (injectR sm Δ qep cfg (P, c))
    rw [injectRM_smSchemeCoinState_eq]; exact DropStateEqS1.liftStateT _
  · exact DropStateEqS1.liftStateT _

private theorem fst_gameRCoinLogged {Key St Msg Coins RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType Coins]
    [SampleableType RCoins]
    (sm : SMSchemeR Key St Msg Coins RCoins C) (Δ qep : ℕ) (cfg : ConfigR St Msg C)
    (A : Adversary St Msg Coins C) :
    Prod.fst <$> gameRCoinLogged sm Δ qep cfg A = gameR sm Δ qep cfg A := by
  rw [gameRCoinLogged_eq_state]
  unfold gameR runR
  simp only [StateT.run_bind, liftM_state_run, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  congr 1; funext b; congr 1; funext k
  let implLog := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (List Coins) ProbComp)) +
    oracleImplRM (smSchemeCoinState sm) Δ qep cfg
  let implR := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) ProbComp) +
    oracleImplR sm Δ qep cfg
  have himpl : ∀ t, DropStateEqS1 (implLog t) (implR t) := by
    rintro (u | q)
    · exact DropStateEqS1.lift (DropStateEq.liftM _)
    · exact dropStateEqS1_oracleImplRM_smSchemeCoinState sm Δ qep cfg q
  have heq := DropStateEqS1.simulateQ implLog implR himpl A (initState sm.sendPart k b) []
  rw [← heq]
  simp only [StateT.run_pure, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
  rfl

private def sendStepGhostLogged {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ : ℕ) (P : Party) (s₁ : GameState St Msg C) (m : Msg) (coins : BitVec 512) (isChal : Bool) :
    StateT (GameState St Msg C) (StateT (TL F C) ProbComp) (Option C) := do
  let ((tr, honestWires), log) ← StateT.lift get
  let out := sm.send (s₁.st P) m coins
  set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ isChal)
  StateT.lift (set ((stepKemFailSend F K tr P coins, (out.2, P) :: honestWires), log ++ [coins]))
  return some out.2

private def sendStepGhostHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ : ℕ) (P : Party) (s₁ : GameState St Msg C) (m : Msg) (coins : BitVec 512) (isChal : Bool) :
    StateT (GameState St Msg C) (StateT (TL F C) ProbComp) (Option C) := do
  let ((tr, honestWires), log) ← StateT.lift get
  let tr' := stepKemFailSend F K tr P coins
  if tr'.cand.isSome then
    StateT.lift (set (({ tr with cand := tr'.cand }, honestWires), log ++ [coins]))
    return none
  else
    let out := sm.send (s₁.st P) m coins
    set (s₁.record Δ P out.1 ⟨⟨P, s₁.epoch P, s₁.idx P + 1⟩, m, out.2⟩ isChal)
    StateT.lift (set ((tr', (out.2, P) :: honestWires), log ++ [coins]))
    return some out.2

private def transmitRGhostLogged {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ => sendStepGhostLogged F K sm Δ P s₁ m coins false

private def challRGhostLogged {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      sendStepGhostLogged F K sm Δ P s₁ m coins true

private def transmitRGhostHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  fun ⟨P, m, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ => sendStepGhostHalted F K sm Δ P s₁ m coins false

private def challRGhostHalted {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × Msg × Msg × Option (BitVec 512)) →ₒ Option C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  fun ⟨P, m₀, m₁, r⟩ => do
    let s ← get
    if !(cfg.sendOK s P) then return none
    if s.win then return none
    let (coins, bad) ← StateT.lift (liftM (samIfNec r : ProbComp (BitVec 512 × Bool)))
    match s.epMgmt Δ qep P bad with
    | none => return none
    | some s₁ =>
      if !(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)) then return none
      let m := (cfg.base.challMsg (s₁.epoch P)).getD (if s.b then m₁ else m₀)
      sendStepGhostHalted F K sm Δ P s₁ m coins true

private def deliverRGhost {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (cfg : ConfigR St Msg C) :
    QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  fun ⟨Q, w⟩ => do
    let ((_, honestWires), _) ← StateT.lift get
    let j? := honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other)
    let res ← liftStateT (deliverR sm cfg (Q, w))
    match res, j? with
    | some (.accepted _ _ _), some j =>
      StateT.lift (modify fun ⟨⟨tr, hw⟩, log⟩ => ((stepKemFailDeliver F K tr Q j, hw), log))
    | _, _ => pure ()
    return res

private def oracleImplRGhostLogged {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  transmitRGhostLogged F K sm Δ qep cfg + challRGhostLogged F K sm Δ qep cfg +
    deliverRGhost F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (TL F C) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)))

private def oracleImplRGhostHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) :
    QueryImpl (spec St Msg (BitVec 512) C)
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) :=
  transmitRGhostHalted F K sm Δ qep cfg + challRGhostHalted F K sm Δ qep cfg +
    deliverRGhost F K sm cfg +
    ((fun q => liftStateT (injectR sm Δ qep cfg q)) :
      QueryImpl ((Party × C) →ₒ Option (RecvResult Msg))
        (StateT (GameState St Msg C) (StateT (TL F C) ProbComp))) +
    ((fun P => liftStateT (corrR cfg P)) :
      QueryImpl (Party →ₒ Option St)
        (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)))

private theorem projStateEqS1_oracleImplRGhostLogged {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : (spec St Msg (BitVec 512) C).Domain) :
    ProjStateEqS1 Prod.snd (oracleImplRGhostLogged F K sm Δ qep cfg q)
      (oracleImplRM (smSchemeCoinState sm) Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change ProjStateEqS1 Prod.snd (transmitRGhostLogged F K sm Δ qep cfg (P, m, r))
      (transmitRM (smSchemeCoinState sm) Δ qep cfg (P, m, r))
    unfold transmitRGhostLogged transmitRM
    refine ProjStateEqS1.bind (ProjStateEqS1.get Prod.snd) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact ProjStateEqS1.pure Prod.snd _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ProjStateEqS1.bind (ProjStateEqS1.lift (ProjStateEq.liftM Prod.snd _))
          fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact ProjStateEqS1.pure Prod.snd _
        | some s₁ =>
          rintro s₀ ⟨⟨tr, hw⟩, log⟩
          simp [sendStepGhostLogged, StateT.run_bind, StateT.run_lift,
            StateT.run_get, StateT.run_set, StateT.run_map]
      · exact ProjStateEqS1.pure Prod.snd _
  · change ProjStateEqS1 Prod.snd (challRGhostLogged F K sm Δ qep cfg (P, m₀, m₁, r))
      (challRM (smSchemeCoinState sm) Δ qep cfg (P, m₀, m₁, r))
    unfold challRGhostLogged challRM
    refine ProjStateEqS1.bind (ProjStateEqS1.get Prod.snd) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact ProjStateEqS1.pure Prod.snd _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ProjStateEqS1.bind (ProjStateEqS1.lift (ProjStateEq.liftM Prod.snd _))
          fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact ProjStateEqS1.pure Prod.snd _
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · rintro s₀ ⟨⟨tr, hw⟩, log⟩
            simp [sendStepGhostLogged, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_map]
          · exact ProjStateEqS1.pure Prod.snd _
      · exact ProjStateEqS1.pure Prod.snd _
  · change ProjStateEqS1 Prod.snd (deliverRGhost F K sm cfg (Q, w))
      (deliverRM (smSchemeCoinState sm) cfg (Q, w))
    rw [deliverRM_smSchemeCoinState_eq]
    rintro s₀ ⟨⟨tr₀, hw₀⟩, log₀⟩
    unfold deliverRGhost
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext ⟨res, s₁⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> simp only
      · simp
      · cases hw₀.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
          simp [StateT.run_lift, StateT.run_map]
  · change ProjStateEqS1 Prod.snd (liftStateT (injectR sm Δ qep cfg (Q, w)))
      (injectRM (smSchemeCoinState sm) Δ qep cfg (Q, w))
    rw [injectRM_smSchemeCoinState_eq]; exact ProjStateEqS1.liftStateT Prod.snd _
  · exact ProjStateEqS1.liftStateT Prod.snd _

private theorem projStateEqS1_oracleImplRGhostHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : (spec St Msg (BitVec 512) C).Domain) :
    ProjStateEqS1 Prod.fst (oracleImplRGhostHalted F K sm Δ qep cfg q)
      (oracleImplRTrackHalted F K sm Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change ProjStateEqS1 Prod.fst (transmitRGhostHalted F K sm Δ qep cfg (P, m, r))
      (transmitRTrackHalted F K sm Δ qep cfg (P, m, r))
    unfold transmitRGhostHalted transmitRTrackHalted
    refine ProjStateEqS1.bind (ProjStateEqS1.get Prod.fst) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact ProjStateEqS1.pure Prod.fst _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ProjStateEqS1.bind (ProjStateEqS1.lift (ProjStateEq.liftM Prod.fst _))
          fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact ProjStateEqS1.pure Prod.fst _
        | some s₁ =>
          rintro s₀ ⟨⟨tr, hw⟩, log⟩
          simp only [sendStepGhostHalted, StateT.run_bind, StateT.run_lift, StateT.run_get,
            pure_bind, bind_assoc]
          cases (stepKemFailSend F K tr P coins).cand.isSome <;>
            simp [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_map]
      · exact ProjStateEqS1.pure Prod.fst _
  · change ProjStateEqS1 Prod.fst (challRGhostHalted F K sm Δ qep cfg (P, m₀, m₁, r))
      (challRTrackHalted F K sm Δ qep cfg (P, m₀, m₁, r))
    unfold challRGhostHalted challRTrackHalted
    refine ProjStateEqS1.bind (ProjStateEqS1.get Prod.fst) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact ProjStateEqS1.pure Prod.fst _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine ProjStateEqS1.bind (ProjStateEqS1.lift (ProjStateEq.liftM Prod.fst _))
          fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact ProjStateEqS1.pure Prod.fst _
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · rintro s₀ ⟨⟨tr, hw⟩, log⟩
            simp only [Bool.false_eq_true, ↓reduceIte, sendStepGhostHalted, StateT.run_bind,
              StateT.run_lift, StateT.run_get, pure_bind, bind_assoc]
            cases (stepKemFailSend F K tr P coins).cand.isSome <;>
              simp [StateT.run_bind, StateT.run_lift, StateT.run_set, StateT.run_map]
          · exact ProjStateEqS1.pure Prod.fst _
      · exact ProjStateEqS1.pure Prod.fst _
  · change ProjStateEqS1 Prod.fst (deliverRGhost F K sm cfg (Q, w))
      (deliverRTrackHalted F K sm cfg (Q, w))
    rintro s₀ ⟨⟨tr₀, hw₀⟩, log₀⟩
    unfold deliverRGhost deliverRTrackHalted
    simp only [StateT.run_bind, StateT.run_lift, StateT.run_get, liftStateT_run_state,
      map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_def]
    congr 1; funext ⟨res, s₁⟩
    cases res with
    | none => simp
    | some rr =>
      cases rr <;> simp only
      · simp
      · cases hw₀.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) <;>
          simp [StateT.run_lift, StateT.run_map]
  · exact ProjStateEqS1.liftStateT Prod.fst _
  · exact ProjStateEqS1.liftStateT Prod.fst _

private abbrev invTL {F : ShaCompress} {C : Type} (K : MlKem) (tl : TL F C) : Prop :=
  KemTrackLoggedInv K tl.1.1 tl.2

private abbrev goodTL {F : ShaCompress} {C : Type} (K : MlKem) (tl : TL F C) : Prop :=
  K.KemFailBad (tl.2.map coinBytes) = false

private theorem agreeInvS1_send_step {Key St Msg RCoins C : Type}
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ : ℕ) (P : Party) (s₁ : GameState St Msg C) (m : Msg) (coins : BitVec 512) (isChal : Bool) :
    AgreeInvS1 (invTL K) (goodTL K)
      (sendStepGhostLogged F K sm Δ P s₁ m coins isChal)
      (sendStepGhostHalted F K sm Δ P s₁ m coins isChal) := by
  intro s₀
  refine
    { inv₁ := fun ⟨⟨tr, hw⟩, log⟩ hinv z hz => by
        simp only [sendStepGhostLogged, StateT.run_bind, StateT.run_lift, StateT.run_get,
          StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; exact kemTrackLoggedInv_stepKemFailSend hinv P coins
      inv₂ := fun ⟨⟨tr, hw⟩, log⟩ hinv z hz => by
        cases hc : (stepKemFailSend F K tr P coins).cand.isSome
        · simp only [sendStepGhostHalted, StateT.run_bind, StateT.run_lift, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, hc,
            Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz; exact kemTrackLoggedInv_stepKemFailSend hinv P coins
        · simp only [sendStepGhostHalted, StateT.run_bind, StateT.run_lift, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, hc,
            ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz
          subst hz; simpa using kemTrackLoggedInv_stepKemFailSend_candOnly hinv P coins
      pres₁ := fun ⟨⟨tr, hw⟩, log⟩ _ hbad z hz => by
        simp only [sendStepGhostLogged, StateT.run_bind, StateT.run_lift, StateT.run_get,
          StateT.run_set, StateT.run_pure, pure_bind,
          support_pure, Set.mem_singleton_iff] at hz
        subst hz; intro hg
        have hbad' : K.KemFailBad (log.map coinBytes) = true := Bool.eq_true_of_not_eq_false hbad
        have hmono := kemFailBad_mono K (l₂ := [coinBytes coins]) hbad'
        have htrue : K.KemFailBad ((log ++ [coins]).map coinBytes) = true := by
          simpa [List.map_append] using hmono
        change K.KemFailBad ((log ++ [coins]).map coinBytes) = false at hg
        rw [htrue] at hg; cases hg
      pres₂ := fun ⟨⟨tr, hw⟩, log⟩ _ hbad z hz => by
        have hbad' : K.KemFailBad (log.map coinBytes) = true := Bool.eq_true_of_not_eq_false hbad
        have hmono := kemFailBad_mono K (l₂ := [coinBytes coins]) hbad'
        have htrue : K.KemFailBad ((log ++ [coins]).map coinBytes) = true := by
          simpa [List.map_append] using hmono
        cases hc : (stepKemFailSend F K tr P coins).cand.isSome <;>
          simp only [sendStepGhostHalted, StateT.run_bind, StateT.run_lift, StateT.run_get,
            StateT.run_set, StateT.run_pure, pure_bind, hc,
            Bool.false_eq_true, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hz <;>
          (subst hz; intro hg; change K.KemFailBad ((log ++ [coins]).map coinBytes) = false at hg;
            rw [htrue] at hg; cases hg)
      agree := fun ⟨⟨tr, hw⟩, log⟩ hinv _ p => by
        have hinv' := kemTrackLoggedInv_stepKemFailSend hinv P coins
        by_cases hg' : K.KemFailBad ((log ++ [coins]).map coinBytes) = false
        · have hnone := cand_eq_none_of_kemTrackLoggedInv K hinv' hg'
          have hc : (stepKemFailSend F K tr P coins).cand.isSome = false := by simp [hnone]
          simp only [sendStepGhostLogged, sendStepGhostHalted, StateT.run_bind, StateT.run_lift,
            StateT.run_get, StateT.run_set, StateT.run_pure, map_pure,
            pure_bind, hc, Bool.false_eq_true, ↓reduceIte]
        · cases hc : (stepKemFailSend F K tr P coins).cand.isSome
          · simp only [sendStepGhostLogged, sendStepGhostHalted, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure, map_pure,
              pure_bind, hc, Bool.false_eq_true, ↓reduceIte]
          · have hbt : K.KemFailBad ((log ++ [coins]).map coinBytes) = true :=
              Bool.eq_true_of_not_eq_false hg'
            simp only [sendStepGhostLogged, sendStepGhostHalted, StateT.run_bind, StateT.run_lift,
              StateT.run_get, StateT.run_set, StateT.run_pure, map_pure,
              pure_bind, hc, ↓reduceIte, goodTL, hbt, reduceCtorEq, and_false] }

private theorem agreeInvS1_oracleImplRGhost {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType RCoins]
    (F : ShaCompress) (K : MlKem) (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (q : (spec St Msg (BitVec 512) C).Domain) :
    AgreeInvS1 (invTL K) (goodTL K)
      (oracleImplRGhostLogged F K sm Δ qep cfg q)
      (oracleImplRGhostHalted F K sm Δ qep cfg q) := by
  rcases q with (((⟨P, m, r⟩ | ⟨P, m₀, m₁, r⟩) | ⟨Q, w⟩) | ⟨Q, w⟩) | P
  · change AgreeInvS1 (invTL K) (goodTL K)
      (transmitRGhostLogged F K sm Δ qep cfg (P, m, r))
      (transmitRGhostHalted F K sm Δ qep cfg (P, m, r))
    unfold transmitRGhostLogged transmitRGhostHalted
    refine AgreeInvS1.bind (AgreeInvS1.get _ _) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact AgreeInvS1.pure _ _ _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine AgreeInvS1.bind (AgreeInvS1.lift (AgreeInv.liftM _ _ _)) fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact AgreeInvS1.pure _ _ _
        | some s₁ => exact agreeInvS1_send_step F K sm Δ P s₁ m coins false
      · exact AgreeInvS1.pure _ _ _
  · change AgreeInvS1 (invTL K) (goodTL K)
      (challRGhostLogged F K sm Δ qep cfg (P, m₀, m₁, r))
      (challRGhostHalted F K sm Δ qep cfg (P, m₀, m₁, r))
    unfold challRGhostLogged challRGhostHalted
    refine AgreeInvS1.bind (AgreeInvS1.get _ _) fun s => ?_
    cases cfg.sendOK s P <;> simp only [Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    · exact AgreeInvS1.pure _ _ _
    · cases s.win <;> simp only [Bool.false_eq_true, ↓reduceIte]
      · refine AgreeInvS1.bind (AgreeInvS1.lift (AgreeInv.liftM _ _ _)) fun ⟨coins, bad⟩ => ?_
        cases s.epMgmt Δ qep P bad with
        | none => exact AgreeInvS1.pure _ _ _
        | some s₁ =>
          dsimp only
          cases (!(s₁.safeCh Δ P) || !(cfg.base.challAllowedIn (s₁.epoch P)))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            exact agreeInvS1_send_step F K sm Δ P s₁ _ coins true
          · exact AgreeInvS1.pure _ _ _
      · exact AgreeInvS1.pure _ _ _
  · change AgreeInvS1 (invTL K) (goodTL K)
      (deliverRGhost F K sm cfg (Q, w)) (deliverRGhost F K sm cfg (Q, w))
    unfold deliverRGhost
    refine AgreeInvS1.bind (AgreeInvS1.lift (AgreeInv.get _ _)) fun ⟨⟨_, honestWires⟩, _⟩ => ?_
    refine AgreeInvS1.bind (AgreeInvS1.liftStateT _ _ _) fun res => ?_
    cases res with
    | none => exact AgreeInvS1.bind (AgreeInvS1.pure _ _ ()) fun _ => AgreeInvS1.pure _ _ _
    | some rr =>
      cases rr
      · exact AgreeInvS1.bind (AgreeInvS1.pure _ _ ()) fun _ => AgreeInvS1.pure _ _ _
      · cases honestWires.reverse.findIdx? (fun wp => wp.1 == w && wp.2 == Q.other) with
        | none => exact AgreeInvS1.bind (AgreeInvS1.pure _ _ ()) fun _ => AgreeInvS1.pure _ _ _
        | some j =>
          refine AgreeInvS1.bind (AgreeInvS1.lift ?_) fun _ => AgreeInvS1.pure _ _ _
          exact
            { inv₁ := fun ⟨⟨tr, hw⟩, log⟩ hinv z hz => by
                simp only [stateT_run_modify, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact kemTrackLoggedInv_stepKemFailDeliver hinv Q j
              inv₂ := fun ⟨⟨tr, hw⟩, log⟩ hinv z hz => by
                simp only [stateT_run_modify, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact kemTrackLoggedInv_stepKemFailDeliver hinv Q j
              pres₁ := fun ⟨⟨_, _⟩, _⟩ _ hb z hz => by
                simp only [stateT_run_modify, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hb
              pres₂ := fun ⟨⟨_, _⟩, _⟩ _ hb z hz => by
                simp only [stateT_run_modify, support_pure, Set.mem_singleton_iff] at hz
                subst hz; exact hb
              agree := fun _ _ _ _ => rfl }
  · exact AgreeInvS1.liftStateT _ _ _
  · exact AgreeInvS1.liftStateT _ _ _

/-! ## Boolean distance and bias transfer -/

theorem gameRCoinLogged_good_le_trackHalted {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C)
    (p : Bool → Prop) :
    Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[p z.1 ∧ K.KemFailBad (z.2.map coinBytes) = false] ≤
      Pr{let z ← gameRTrackHalted pqrOf F K sm Δ qep cfg A}[p z.1 ∧ z.2.1.cand = none] := by
  rw [gameRCoinLogged_eq_state]; unfold gameRTrackHalted
  simp only [StateT.run_bind, liftM_state_run, bind_assoc, pure_bind]
  let : MeasurableSpace Bool := ⊤
  let : MeasurableSpace Key := ⊤
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  refine MeasureTheory.lintegral_mono fun b => ?_
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  refine MeasureTheory.lintegral_mono fun k => ?_
  let implGLog := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) +
    oracleImplRGhostLogged F K sm Δ qep cfg
  let implGHalt := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (TL F C) ProbComp)) +
    oracleImplRGhostHalted F K sm Δ qep cfg
  let implLog := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (List (BitVec 512)) ProbComp)) +
    oracleImplRM (smSchemeCoinState sm) Δ qep cfg
  let implHalt := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (GameState St Msg C) (StateT (KemFailSessionTrack F C) ProbComp)) +
    oracleImplRTrackHalted F K sm Δ qep cfg
  let tl₀ : TL F C := ((initKemFailTrack F (pqrOf k), []), [])
  let gs₀ := initState sm.sendPart k b
  have hDropTrack : ProjStateEq Prod.snd
      (do let (b', s) ← (simulateQ implGLog A).run gs₀; return (b == b' || s.win))
      (do let (b', s) ← (simulateQ implLog A).run gs₀; return (b == b' || s.win)) := by
    refine ProjStateEq.bind (ProjStateEqS1.simulateQ Prod.snd implGLog implLog ?_ A gs₀)
      fun ⟨b', s⟩ => ProjStateEq.pure Prod.snd (b == b' || s.win)
    rintro (u | q)
    · exact ProjStateEqS1.lift (ProjStateEq.liftM Prod.snd _)
    · exact projStateEqS1_oracleImplRGhostLogged F K sm Δ qep cfg q
  have hSimHalt :
      (fun z => (z.1, z.2.1)) <$> ((simulateQ implGHalt A).run gs₀).run tl₀ =
        ((simulateQ implHalt A).run gs₀).run (initKemFailTrack F (pqrOf k), []) := by
    refine ProjStateEqS1.simulateQ Prod.fst implGHalt implHalt ?_ A gs₀ tl₀
    rintro (u | q)
    · exact ProjStateEqS1.lift (ProjStateEq.liftM Prod.fst _)
    · exact projStateEqS1_oracleImplRGhostHalted F K sm Δ qep cfg q
  have hAgree : AgreeInv (invTL K) (goodTL K)
      (do let (b', s) ← (simulateQ implGLog A).run gs₀; return (b == b' || s.win))
      (do let (b', s) ← (simulateQ implGHalt A).run gs₀; return (b == b' || s.win)) := by
    refine AgreeInv.bind (AgreeInvS1.simulateQ implGLog implGHalt ?_ A gs₀) fun ⟨b', s⟩ =>
      AgreeInv.pure _ _ (b == b' || s.win)
    rintro (u | q)
    · exact AgreeInvS1.lift (AgreeInv.liftM _ _ _)
    · exact agreeInvS1_oracleImplRGhost F K sm Δ qep cfg q
  have hinv₀ : invTL K tl₀ := kemTrackLoggedInv_init F K (pqrOf k)
  have hgood₀ : goodTL K tl₀ := rfl
  let mGLog := (do let (b', s) ← (simulateQ implGLog A).run gs₀; return (b == b' || s.win)).run tl₀
  let mGHalt := (do let (b', s) ← (simulateQ implGHalt A).run gs₀; return (b == b' || s.win)).run tl₀
  have hmap := hDropTrack tl₀
  conv at hmap => rhs; rw [StateT.run_bind]
  have heqR :
      (do
          let ((b', s), stTrack) ←
            ((simulateQ implHalt A).run gs₀).run (initKemFailTrack F (pqrOf k), [])
          return (b == b' || s.win, stTrack)) =
        (fun z : Bool × TL F C => (z.1, z.2.1)) <$> mGHalt := by
    rw [← hSimHalt]
    simp only [mGHalt, StateT.run_bind, StateT.run_pure, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_def]
  have hR :
      Pr{let z ← (do
          let ((b', s), stTrack) ←
            ((simulateQ implHalt A).run gs₀).run (initKemFailTrack F (pqrOf k), [])
          return (b == b' || s.win, stTrack))}[p z.1 ∧ z.2.1.cand = none] =
        Pr{let z ← mGHalt}[p z.1 ∧ z.2.1.1.cand = none] := by
    rw [heqR, prEvent_map]
  rw [← hmap, prEvent_map, hR]
  change Pr{let z ← mGLog}[p z.1 ∧ goodTL K z.2] ≤ Pr{let z ← mGHalt}[p z.1 ∧ z.2.1.1.cand = none]
  rw [hAgree.agree tl₀ hinv₀ hgood₀ (fun z => p z.1)]
  let : MeasurableSpace (Bool × TL F C) := ⊤
  have hsupp_zero :
      Pr{let z ← mGHalt}[(p z.1 ∧ goodTL K z.2) ∧ ¬ (p z.1 ∧ z.2.1.1.cand = none)] = 0 :=
    prEvent_eq_zero_of_forall_mem_support mGHalt _ fun z hz ⟨⟨hpz, hgz⟩, hnot⟩ =>
      hnot ⟨hpz, cand_eq_none_of_kemTrackLoggedInv K (hAgree.inv₂ tl₀ hinv₀ z hz) hgz⟩
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
  have hsub : {z : Bool × TL F C | p z.1 ∧ goodTL K z.2} ⊆
      {z | p z.1 ∧ z.2.1.1.cand = none} ∪
        {z | (p z.1 ∧ goodTL K z.2) ∧ ¬ (p z.1 ∧ z.2.1.1.cand = none)} :=
    fun z hz => by by_cases hc : p z.1 ∧ z.2.1.1.cand = none <;> [exact Or.inl hc; exact Or.inr ⟨hz, hc⟩]
  calc (𝒟[mGHalt]) {z | p z.1 ∧ goodTL K z.2}
      ≤ (𝒟[mGHalt]) ({z | p z.1 ∧ z.2.1.1.cand = none} ∪
          {z | (p z.1 ∧ goodTL K z.2) ∧ ¬ (p z.1 ∧ z.2.1.1.cand = none)}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ (𝒟[mGHalt]) {z | p z.1 ∧ z.2.1.1.cand = none} +
          (𝒟[mGHalt]) {z | (p z.1 ∧ goodTL K z.2) ∧ ¬ (p z.1 ∧ z.2.1.1.cand = none)} :=
        MeasureTheory.measure_union_le _ _
    _ = (𝒟[mGHalt]) {z | p z.1 ∧ z.2.1.1.cand = none} := by
        rw [← prEvent_eq_evalDist_of_discrete mGHalt
          (fun z => (p z.1 ∧ goodTL K z.2) ∧ ¬ (p z.1 ∧ z.2.1.1.cand = none)), hsupp_zero, add_zero]

theorem prEvent_trackHalted_cand_isSome_le {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    Pr{let z ← gameRTrackHalted pqrOf F K sm Δ qep cfg A}[z.2.1.cand.isSome = true] ≤
      Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[K.KemFailBad (z.2.map coinBytes) = true] := by
  let : MeasurableSpace (Bool × KemFailSessionTrack F C) := ⊤
  let : MeasurableSpace (Bool × List (BitVec 512)) := ⊤
  have hle := gameRCoinLogged_good_le_trackHalted pqrOf F K sm Δ qep cfg A (fun _ => True)
  simp only [true_and] at hle
  rw [prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete] at hle ⊢
  have hcompl₁ :
      (𝒟[gameRTrackHalted pqrOf F K sm Δ qep cfg A]) {z | z.2.1.cand.isSome = true} =
        1 - (𝒟[gameRTrackHalted pqrOf F K sm Δ qep cfg A]) {z | z.2.1.cand = none} := by
    have hset : ({z : Bool × KemFailSessionTrack F C | z.2.1.cand.isSome = true} : Set _) =
        {z | z.2.1.cand = none}ᶜ := by
      ext z; change (z.2.1.cand.isSome = true) ↔ ¬ (z.2.1.cand = none)
      generalize z.2.1.cand = c; cases c <;> simp
    rw [hset, MeasureTheory.prob_compl_eq_one_sub MeasurableSet.of_discrete]
  have hcompl₂ :
      (𝒟[gameRCoinLogged sm Δ qep cfg A]) {z | K.KemFailBad (z.2.map coinBytes) = true} =
        1 - (𝒟[gameRCoinLogged sm Δ qep cfg A]) {z | K.KemFailBad (z.2.map coinBytes) = false} := by
    have hset : ({z : Bool × List (BitVec 512) | K.KemFailBad (z.2.map coinBytes) = true} : Set _) =
        {z | K.KemFailBad (z.2.map coinBytes) = false}ᶜ := by ext z; simp
    rw [hset, MeasureTheory.prob_compl_eq_one_sub MeasurableSet.of_discrete]
  rw [hcompl₁, hcompl₂]
  exact tsub_le_tsub_left hle 1

private theorem boolDist_fst_le_prEvent_of_good_le {β : Type}
    (exp : ProbComp (Bool × β)) (exp₀ : ProbComp Bool) (badEv : Bool × β → Prop)
    (hgood : ∀ b : Bool, Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] ≤ Pr{let b' ← exp₀}[b' = b]) :
    (𝒟[Prod.fst <$> exp]).boolDist (𝒟[exp₀]) ≤ Pr{let z ← exp}[badEv z] := by
  let : MeasurableSpace (Bool × β) := ⊤
  refine Measure.boolDist_le_of_apply_le _ _ fun b => ?_
  have hsing : ({b} : Set Bool) = {x | x = b} := Set.ext fun _ => Set.mem_singleton_iff
  have hfst : (𝒟[Prod.fst <$> exp]) {b} = (𝒟[exp]) {z | z.1 = b} := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete, prEvent_map, prEvent_eq_evalDist_of_discrete]
  have hrhs : (𝒟[exp₀]) {b} = Pr{let b' ← exp₀}[b' = b] := by
    rw [hsing, ← prEvent_eq_evalDist_of_discrete]
  rw [hfst, hrhs]
  have hsub : {z : Bool × β | z.1 = b} ⊆ {z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z} :=
    fun z hz => by by_cases hb : badEv z <;> [exact Or.inr hb; exact Or.inl ⟨hz, hb⟩]
  calc (𝒟[exp]) {z | z.1 = b}
      ≤ (𝒟[exp]) ({z | z.1 = b ∧ ¬ badEv z} ∪ {z | badEv z}) := MeasureTheory.measure_mono hsub
    _ ≤ (𝒟[exp]) {z | z.1 = b ∧ ¬ badEv z} + (𝒟[exp]) {z | badEv z} :=
        MeasureTheory.measure_union_le _ _
    _ = Pr{let z ← exp}[z.1 = b ∧ ¬ badEv z] + Pr{let z ← exp}[badEv z] := by
        rw [← prEvent_eq_evalDist_of_discrete, ← prEvent_eq_evalDist_of_discrete]
    _ ≤ Pr{let b' ← exp₀}[b' = b] + Pr{let z ← exp}[badEv z] := by gcongr; exact hgood b

private theorem boolBias_le_add_two_mul_of_boolDist_le (μ ν : Measure Bool)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (ε : ℝ≥0∞) (h : μ.boolDist ν ≤ ε) :
    μ.boolBias ≤ ν.boolBias + 2 * ε := by
  have hbd : μ.boolDist ν = ENNReal.absDiff (μ {true}) (ν {true}) := Measure.boolDist.eq_1 μ ν
  calc μ.boolBias = 2 * ENNReal.absDiff (μ {true}) (1 / 2) :=
        Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure μ
    _ ≤ 2 * (ENNReal.absDiff (μ {true}) (ν {true}) + ENNReal.absDiff (ν {true}) (1 / 2)) := by
        gcongr; exact ENNReal.absDiff_triangle _ _ _
    _ = 2 * ENNReal.absDiff (ν {true}) (1 / 2) + 2 * μ.boolDist ν := by rw [← hbd]; ring
    _ = ν.boolBias + 2 * μ.boolDist ν := by
        rw [Measure.boolBias_eq_two_mul_absDiff_half_of_isProbabilityMeasure ν]
    _ ≤ ν.boolBias + 2 * ε := by gcongr

/-- Bounds the Boolean distance between `SM.gameR` and `gameRTrackHalted` by `KemFailBad`. -/
theorem boolDist_gameR_trackHalted_le {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    (𝒟[gameR sm Δ qep cfg A]).boolDist
        (𝒟[Prod.fst <$> gameRTrackHalted pqrOf F K sm Δ qep cfg A]) ≤
      Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[K.KemFailBad (z.2.map coinBytes) = true] := by
  let : MeasurableSpace (Bool × KemFailSessionTrack F C) := ⊤
  rw [← fst_gameRCoinLogged sm Δ qep cfg A]
  refine boolDist_fst_le_prEvent_of_good_le
    (gameRCoinLogged sm Δ qep cfg A)
    (Prod.fst <$> gameRTrackHalted pqrOf F K sm Δ qep cfg A)
    (fun z => K.KemFailBad (z.2.map coinBytes) = true) fun b => ?_
  simp only [Bool.not_eq_true]
  calc Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[
          z.1 = b ∧ K.KemFailBad (z.2.map coinBytes) = false]
      ≤ Pr{let z ← gameRTrackHalted pqrOf F K sm Δ qep cfg A}[z.1 = b ∧ z.2.1.cand = none] :=
        gameRCoinLogged_good_le_trackHalted pqrOf F K sm Δ qep cfg A (· = b)
    _ ≤ Pr{let b' ← Prod.fst <$> gameRTrackHalted pqrOf F K sm Δ qep cfg A}[b' = b] := by
        rw [prEvent_map, prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
        exact MeasureTheory.measure_mono fun _ h => h.1

theorem boolDist_bind_gameR_trackHalted_le {α Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (oa : ProbComp α) (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : α → SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : α → Adversary St Msg (BitVec 512) C) :
    (𝒟[oa >>= fun o => gameR (sm o) Δ qep cfg (A o)]).boolDist
        (𝒟[oa >>= fun o => Prod.fst <$> gameRTrackHalted pqrOf F K (sm o) Δ qep cfg (A o)]) ≤
      Pr{let z ← oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)}[
        K.KemFailBad (z.2.map coinBytes) = true] := by
  let : MeasurableSpace α := ⊤
  let : MeasurableSpace (Bool × KemFailSessionTrack F C) := ⊤
  have hfst :
      (oa >>= fun o => gameR (sm o) Δ qep cfg (A o)) =
        Prod.fst <$> (oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)) := by
    simp [map_eq_bind_pure_comp, bind_assoc, ← fst_gameRCoinLogged]
  rw [hfst]
  refine boolDist_fst_le_prEvent_of_good_le
    (oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o))
    (oa >>= fun o => Prod.fst <$> gameRTrackHalted pqrOf F K (sm o) Δ qep cfg (A o))
    (fun z => K.KemFailBad (z.2.map coinBytes) = true) fun b => ?_
  simp only [Bool.not_eq_true]
  rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete]
  refine MeasureTheory.lintegral_mono fun o => ?_
  calc Pr{let z ← gameRCoinLogged (sm o) Δ qep cfg (A o)}[
          z.1 = b ∧ K.KemFailBad (z.2.map coinBytes) = false]
      ≤ Pr{let z ← gameRTrackHalted pqrOf F K (sm o) Δ qep cfg (A o)}[
          z.1 = b ∧ z.2.1.cand = none] :=
        gameRCoinLogged_good_le_trackHalted pqrOf F K (sm o) Δ qep cfg (A o) (· = b)
    _ ≤ Pr{let b' ← Prod.fst <$> gameRTrackHalted pqrOf F K (sm o) Δ qep cfg (A o)}[b' = b] := by
        rw [prEvent_map, prEvent_eq_evalDist_of_discrete, prEvent_eq_evalDist_of_discrete]
        exact MeasureTheory.measure_mono fun _ h => h.1

theorem boolBias_gameR_le_trackHalted_add_two_mul {Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : Adversary St Msg (BitVec 512) C) :
    (𝒟[gameR sm Δ qep cfg A]).boolBias ≤
      (𝒟[Prod.fst <$> gameRTrackHalted pqrOf F K sm Δ qep cfg A]).boolBias +
        2 * Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[K.KemFailBad (z.2.map coinBytes) = true] :=
  boolBias_le_add_two_mul_of_boolDist_le _ _ _
    (boolDist_gameR_trackHalted_le pqrOf F K sm Δ qep cfg A)

theorem boolBias_bind_gameR_le_trackHalted_add_two_mul {α Key St Msg RCoins C : Type}
    [DecidableEq Msg] [DecidableEq C] [SampleableType Key] [SampleableType RCoins]
    (oa : ProbComp α) (pqrOf : Key → BitVec 256) (F : ShaCompress) (K : MlKem)
    (sm : α → SMSchemeR Key St Msg (BitVec 512) RCoins C)
    (Δ qep : ℕ) (cfg : ConfigR St Msg C) (A : α → Adversary St Msg (BitVec 512) C) :
    (𝒟[oa >>= fun o => gameR (sm o) Δ qep cfg (A o)]).boolBias ≤
      (𝒟[oa >>= fun o => Prod.fst <$> gameRTrackHalted pqrOf F K (sm o) Δ qep cfg (A o)]).boolBias +
        2 * Pr{let z ← oa >>= fun o => gameRCoinLogged (sm o) Δ qep cfg (A o)}[
          K.KemFailBad (z.2.map coinBytes) = true] :=
  boolBias_le_add_two_mul_of_boolDist_le _ _ _
    (boolDist_bind_gameR_trackHalted_le oa pqrOf F K sm Δ qep cfg A)

/-- Bounds the `SessionSecure` game bias by `gameRTrackHalted` plus twice `sessionKemFailProb`. -/
theorem boolBias_session_le_trackHalted_add_two_mul_sessionKemFailProb {α : Type}
    (C : Crypto) (K : MlKem) (ℓ : ℕ) {Pt : Type}
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) (qep : ℕ)
    (oa : ProbComp α) (ida idb : α → IdentityKey) (s : α → BitVec 256)
    (A : α → Adversary (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes) :
    let sm := fun o => sessionSchemeFixedSpk
      (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) (ida o) (idb o)) ℓ (s o)
    (𝒟[oa >>= fun o => gameR (sm o) 3 qep (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias ≤
      (𝒟[oa >>= fun o =>
          Prod.fst <$> gameRTrackHalted sampledSessionPqrOf C.F K (sm o) 3 qep
            (configRefuseEarlyBobCorr decT encT) (A o)]).boolBias +
        2 * sessionKemFailProb C K ℓ decT encT qep oa ida idb s A := by
  unfold sessionKemFailProb
  exact boolBias_bind_gameR_le_trackHalted_add_two_mul oa sampledSessionPqrOf C.F K _ 3 qep
    (configRefuseEarlyBobCorr decT encT) A

/-- Bounds the `libsignalSessionScheme` game bias by `gameRTrackHalted` plus twice `KemFailBad`. -/
theorem boolBias_libsignalSession_le_trackHalted_add_two_mul {PQ Pt : Type} [Inhabited PQ]
    (P : Params PQ (BitVec 512)) (K : MlKem) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) (Δ qep : ℕ)
    (cfg : ConfigR (GhostState PQ) (Plain ℓ) (List (BitVec 8)))
    (A : Adversary (GhostState PQ) (Plain ℓ) (BitVec 512) (List (BitVec 8))) :
    let sm := libsignalSessionScheme P ℓ encPt lam
    (𝒟[gameR sm Δ qep cfg A]).boolBias ≤
      (𝒟[Prod.fst <$> gameRTrackHalted libsignalSessionPqrOf P.C.F K sm Δ qep cfg A]).boolBias +
        2 * Pr{let z ← gameRCoinLogged sm Δ qep cfg A}[K.KemFailBad (z.2.map coinBytes) = true] :=
  boolBias_gameR_le_trackHalted_add_two_mul libsignalSessionPqrOf P.C.F K _ Δ qep cfg A

end Computational.Proofs.SpecLemmas.Session.KemFailTrackBridge
