/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.SM.Engine
public import Computational.Proofs.SpecLemmas.Session.ACD19.SM.Theorem8And12Statements
public import Computational.Proofs.CryptoGames.CKA.CKAProofDefs
public import Computational.Proofs.SpecLemmas.Reductions.Primitives.PRNG.PRNGProofDefs

/-!
# Concrete reductions for Theorems 8 and 12

**Checked by Lean.** Defines the concrete reductions from authenticity and privacy of the ACD19
Fig. 8 secure messaging scheme to CKA security (`redCKAAuth`, `redCKAPriv`), PRF-PRNG security of
the root chain (`redPRNGAuth`, `redPRNGPriv`; DEV-SM24), and FS-AEAD session security (`redFSAuth`,
`redFSPriv`, `redFSPrivCoin`; DEV-SM25), running the adversary in the simulation engine of
`SM/Engine.lean`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.SM.Construction

open Engine

set_option linter.unusedSectionVars false

variable {KC Γ CCoins T I : Type} {KR Sig K : Type} {SS RS M E : Type}
  [DecidableEq T] [DecidableEq M] [DecidableEq E] [DecidableEq I] [Inhabited E]
  [SampleableType KR] [SampleableType KC] [SampleableType CCoins] [SampleableType I]
  [SampleableType K]

def sampleT {ι : Type} {tspec : OracleSpec.{0, 0} ι} (α : Type) [SampleableType α] :
    TComp tspec α :=
  (liftM ($ᵗ α : ProbComp α) : TComp tspec α)

def mkParties {Γv Sv SSv RSv : Type} (γA γB : Γv) (σ : Sv) (ssB : SSv) (rsA : RSv) :
    PartyState Γv T Sv SSv RSv × PartyState Γv T Sv SSv RSv :=
  ({ id := .A, root := σ, vS := none, vR := fun t => if t = 0 then some rsA else none, γ := γA,
     curCkaMsg := none, tcur := 0 },
   { id := .B, root := σ, vS := some ssB, vR := fun _ => none, γ := γB, curCkaMsg := none, tcur := 0 })

def realParty {Γv Sv SSv RSv : Type} (vp : PartyState Γv T Sv SSv RSv) (γ : Γ) (σ : Sig)
    (vS : Option SS) (vR : ℕ → Option RS) : PartyState Γ T Sig SS RS :=
  { id := vp.id, root := σ, vS, vR, γ, curCkaMsg := vp.curCkaMsg, tcur := vp.tcur }

/-- Game mode simulated by the reductions: authenticity (`auth = true`) or privacy (`false`) at
guesses `(tL, tStar)`. -/
structure Mode where
  auth : Bool
  tL : Option ℕ
  tStar : ℕ

def Mode.policy (mo : Mode) : Policy := ⟨mo.auth, mo.tL, mo.tStar⟩

def Mode.cfg (mo : Mode) : Config M := if mo.auth then Config.auth mo.tStar else Config.priv mo.tStar

def Mode.tH (mo : Mode) : ℕ := healEpoch mo.tL

/-! ### `redCKA` -/

section RedCKA

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

/-- Per-epoch CKA message and key cache `(T_t, I_t)` for `redCKA`. -/
structure CKAState (T I : Type) where
  cache : ℕ → Option (T × I) := fun _ => none

local notation "CSpec" => CKA.spec Γ CCoins T I
local notation "CHM" => HM CSpec (CKAState T I)

def liftC {α : Type} (x : CKA.AdversaryComp Γ CCoins T I α) : CHM α := StateT.lift x

def cacheC (t : ℕ) (x : T × I) : CHM Unit :=
  modify fun s => { s with cache := Function.update s.cache t (some x) }

def hooksCKA : Hooks CSpec (CKAState T I) Γ T Sig SS RS M E CCoins (Option Γ) Sig SS RS where
  startSend _ P t γv σ r := do
    match γv with
    | some γ =>
      let coins ← match r with
        | some c => pure c
        | none => StateT.lift (sampleT CCoins)
      let c := cka.send γ coins
      cacheC t (c.2.1, c.2.2)
      let p := prng.up σ c.2.2
      return some (some c.1, c.2.1, p.1, fs.initSender p.2)
    | none =>
      let ans ← match r with
        | some c => liftC (CKA.sendWithAdversaryCoinsQuery P c)
        | none => if t = mo.tH then liftC (CKA.challQuery P) else liftC (CKA.sendQuery P)
      match ans with
      | none => return none
      | some (T', Ik) =>
        cacheC t (T', Ik)
        let p := prng.up σ Ik
        if mo.tH + Δcka ≤ t then
          match ← liftC (CKA.corrQuery P) with
          | none => return none
          | some γ => return some (some γ, T', p.1, fs.initSender p.2)
        else return some (none, T', p.1, fs.initSender p.2)
  startRecv _ _ t γv σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, Ik) => if Tc = Tn then some Ik else none
      | none => none
    match honest with
    | some Ik =>
      let p := prng.up σ Ik
      return some (some (γv.map fun γ => (cka.receive γ Tn).1, p.1, fs.initReceiver p.2))
    | none =>
      if mo.auth && t = mo.tStar then
        match γv with
        | some γ =>
          let k := cka.receive γ Tn
          let p := prng.up σ k.2
          return some (some (some k.1, p.1, fs.initReceiver p.2))
        | none => return none
      else return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ P old new := do
    if old.tcur < new.tcur && old.γ.isNone then
      match ← liftC (CKA.receiveQuery P) with
      | none => return none
      | some () =>
        if mo.tH + Δcka ≤ new.tcur then
          match ← liftC (CKA.corrQuery P) with
          | none => return none
          | some γ => return some { new with γ := some γ }
        else return some new
    else return some new
  reveal _ P vp := do
    let γ? ← match vp.γ with
      | some γ => pure (some γ)
      | none => liftC (CKA.corrQuery P)
    match γ? with
    | none => return none
    | some γ => return some (realParty vp γ vp.root vp.vS vp.vR)

def initCKA : CHM (Option (PartyState (Option Γ) T Sig SS RS × PartyState (Option Γ) T Sig SS RS)) :=
  do
  let kr ← StateT.lift (sampleT KR)
  let out := prng.up (prng.init kr) lam
  let (γA, γB) ← match mo.tL with
    | none => do
      let kc ← StateT.lift (sampleT KC)
      pure (some (cka.initA kc), some (cka.initB kc))
    | some _ => pure (none, none)
  return some (mkParties γA γB out.1 (fs.initSender out.2) (fs.initReceiver out.2))

def runCKA (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.AdversaryComp Γ CCoins T I
      (Option (Bool × EState (PartyState (Option Γ) T Sig SS RS) M (Header T × E)
        (CKAState T I))) :=
  engRun (hooksCKA cka prng fs Δcka mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initCKA cka prng fs lam mo) {} b A

/-- CKA authenticity reduction (`B1` of ACD19 Lemma 9). -/
def redCKAAuth (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  match ← runCKA cka prng fs lam Δcka qep ⟨true, tL, t⟩ false A with
  | none => return false
  | some (_, es) => return authOut (2 + Δcka) ⟨true, tL, t⟩ es

/-- CKA privacy reduction (`B1` of ACD19 Lemma 13). -/
def redCKAPriv (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    CKA.Adversary Γ CCoins T I :=
  show CKA.AdversaryComp Γ CCoins T I Bool from do
  let b ← sampleT Bool
  match ← runCKA cka prng fs lam Δcka qep ⟨false, tL, t⟩ b A with
  | none => sampleT Bool
  | some (b', es) => privOut (2 + Δcka) ⟨false, tL, t⟩ b b' es

end RedCKA

/-! ### `redPRNG` -/

section RedPRNG

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode)

/-- Per-epoch CKA message, optional known root state, and output cache for `redPRNG`. -/
structure PRNGState (T Sig K : Type) where
  cache : ℕ → Option (T × Option Sig × K) := fun _ => none

local notation "PSpec" => PRFPRNG.spec Sig I K
local notation "PHM" => HM PSpec (PRNGState T Sig K)

def liftP {α : Type} (x : PRFPRNG.AdversaryComp Sig I K α) : PHM α := StateT.lift x

def processCorr (Ik : Option I) : PHM (Option (Option Sig × K)) := do
  match ← liftP (PRFPRNG.processQuery Ik) with
  | none => return none
  | some k =>
    match ← liftP (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
    | none => return none
    | some σ' => return some (some σ', k)

/-- **DEV-SM24 (formalization): Lemma 14 asks `chall-prf`.** Root-RNG step of epoch `t` in
`redPRNG`, querying `chall-prf(I_{t*})` at epoch `t*` for both authenticity and privacy (since
epochs `> t*` are simulated locally, matching ACD19's `chall-prng` hop). -/
def rootPRNG (t : ℕ) (Ik : I) (σv : Option Sig) : PHM (Option (Option Sig × K)) := do
  if mo.tStar < t then
    match σv with
    | some σ =>
      let p := prng.up σ Ik
      return some (some p.1, p.2)
    | none => return none
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      match ← liftP (PRFPRNG.challPrngQuery none) with
      | none => return none
      | some k =>
        match ← liftP (PRFPRNG.corrQuery (State := Sig) (Input := I) (Output := K)) with
        | none => return none
        | some σ' => return some (some σ', k)
    else
      match ← liftP (PRFPRNG.challPrfQuery Ik) with
      | none => return none
      | some (σ', k) => return some (some σ', k)
  else if mo.tL.isSome && t = mo.tH then
    match ← liftP (PRFPRNG.processQuery none) with
    | none => return none
    | some k => return some (none, k)
  else if mo.tL.isSome && t < mo.tH then processCorr (Ik := some Ik)
  else
    match ← liftP (PRFPRNG.processQuery (some Ik)) with
    | none => return none
    | some k => return some (none, k)

def hooksPRNG : Hooks PSpec (PRNGState T Sig K) Γ T Sig SS RS M E CCoins Γ (Option Sig) SS RS where
  startSend _ _ t γ σv r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    match ← rootPRNG prng mo t c.2.2 σv with
    | none => return none
    | some (σ', k) =>
      modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k)) }
      return some (c.1, c.2.1, σ', fs.initSender k)
  startRecv _ _ t γ _ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k) => if Tc = Tn then some (σc, k) else none
      | none => none
    match honest with
    | some (σc, k) => return some (some ((cka.receive γ Tn).1, σc, fs.initReceiver k))
    | none =>
      if mo.auth && t = mo.tStar then
        let kk := cka.receive γ Tn
        match ← liftP (PRFPRNG.challPrfQuery kk.2) with
        | none => return none
        | some (σ', k') => return some (some (kk.1, some σ', fs.initReceiver k'))
      else return some none
  fsSend _ _ _ ss h m _ := pure (some (fs.send ss h m))
  fsRecv _ _ _ rs h e _ := pure (some (fs.receive rs h e))
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    match vp.root with
    | none => return none
    | some σ => return some (realParty vp vp.γ σ vp.vS vp.vR)

def initPRNG : PHM (Option (PartyState Γ T (Option Sig) SS RS × PartyState Γ T (Option Sig) SS RS)) :=
  do
  let kc ← StateT.lift (sampleT KC)
  match ← rootPRNG prng mo 0 lam none with
  | none => return none
  | some (σ, k) =>
    return some (mkParties (cka.initA kc) (cka.initB kc) σ (fs.initSender k) (fs.initReceiver k))

def runPRNG (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.AdversaryComp Sig I K
      (Option (Bool × EState (PartyState Γ T (Option Sig) SS RS) M (Header T × E)
        (PRNGState T Sig K))) :=
  engRun (hooksPRNG cka prng fs mo) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initPRNG cka prng fs lam mo) {} b A

/-- PRF-PRNG authenticity reduction (`B2` of ACD19 Lemma 10). -/
def redPRNGAuth (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
  match ← runPRNG cka prng fs lam Δcka qep ⟨true, tL, t⟩ false A with
  | none => return false
  | some (_, es) => return authOut (2 + Δcka) ⟨true, tL, t⟩ es

/-- PRF-PRNG privacy reduction (`B2` of ACD19 Lemma 14; DEV-SM24). -/
def redPRNGPriv (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    PRFPRNG.Adversary Sig I K :=
  show PRFPRNG.AdversaryComp Sig I K Bool from do
  let b ← sampleT Bool
  match ← runPRNG cka prng fs lam Δcka qep ⟨false, tL, t⟩ b A with
  | none => sampleT Bool
  | some (b', es) => privOut (2 + Δcka) ⟨false, tL, t⟩ b b' es

end RedPRNG

/-! ### `redFS` -/

section RedFS

variable (cka : CKAScheme KC Γ CCoins T I) (prng : PRFPRNG KR Sig I K)
  (fs : FSAEADScheme K SS RS (Header T) M E) (lam : I) (Δcka qep : ℕ) (mo : Mode) (j : ℕ)

/-- Bookkeeping state of `redFS`, tracking per-epoch caches, the lazy random function `F`, numbered
epoch-`t*` sessions, and the mirrored FS-AEAD challenge session. -/
structure FSState (T Sig K I SS RS E : Type) where
  cache : ℕ → Option (T × Sig × K × Bool) := fun _ => none
  table : List (I × K) := []
  sessions : List I := []
  fsTrans : List (ℕ × Header T × E) := []
  fsCount : ℕ := 0
  fsSCorr : Bool := false
  ext : Option (SS × RS) := none

local notation "FSpec" => FSAEAD.spec SS RS (Header T) M E
local notation "FHM" => HM FSpec (FSState T Sig K I SS RS E)

def liftF {α : Type} (x : FSAEAD.AdversaryComp SS RS (Header T) M E α) : FHM α := StateT.lift x

def lookupF (Ik : I) : FHM K := do
  match (← get).table.lookup Ik with
  | some k => return k
  | none =>
    let k ← StateT.lift (sampleT K)
    modify fun s => { s with table := (Ik, k) :: s.table }
    return k

def isExt (Ik : I) : FHM Bool := do
  let s ← get
  if Ik ∈ s.sessions then return s.sessions.idxOf Ik == j
  else
    set { s with sessions := s.sessions ++ [Ik] }
    return s.sessions.length == j

/-- Idealized root-RNG step of epoch `t` in hybrid `H2`, returning `(σ', k, sid)`. -/
def rootFS (t : ℕ) (Ik : I) (σ : Sig) : FHM (Sig × K × Option I) := do
  if mo.tStar < t then
    let p := prng.up σ Ik
    return (p.1, p.2, none)
  else if t = mo.tStar then
    if mo.tL.isSome && t = mo.tH then
      let Ir ← StateT.lift (sampleT I)
      let k ← StateT.lift (sampleT K)
      return ((prng.up σ Ir).1, k, some Ir)
    else
      let k ← lookupF Ik
      return ((prng.up σ Ik).1, k, some Ik)
  else if mo.tL.isSome && t = mo.tH then
    let Ir ← StateT.lift (sampleT I)
    let p := prng.up σ Ir
    return (p.1, p.2, none)
  else
    let p := prng.up σ Ik
    return (p.1, p.2, none)

def extOf (sid : Option I) : FHM Bool :=
  match sid with
  | none => pure false
  | some Ik => isExt j Ik

def hooksFS : Hooks FSpec (FSState T Sig K I SS RS E) Γ T Sig SS RS M E CCoins Γ Sig
    (Option SS) (Option RS) where
  startSend _ _ t γ σ r := do
    let coins ← match r with
      | some c => pure c
      | none => StateT.lift (sampleT CCoins)
    let c := cka.send γ coins
    let (σ', k, sid) ← rootFS prng mo t c.2.2 σ
    let ext ← extOf j sid
    modify fun s => { s with cache := Function.update s.cache t (some (c.2.1, σ', k, ext)) }
    return some (c.1, c.2.1, σ', if ext then none else some (fs.initSender k))
  startRecv _ _ t γ σ Tn := do
    let honest := match (← get).cache t with
      | some (Tc, σc, k, ext) => if Tc = Tn then some (σc, k, ext) else none
      | none => none
    match honest with
    | some (σc, k, ext) =>
      return some (some ((cka.receive γ Tn).1, σc, if ext then none else some (fs.initReceiver k)))
    | none =>
      if mo.auth && t = mo.tStar then
        if mo.tL.isSome && mo.tStar = mo.tH then return none
        let kk := cka.receive γ Tn
        let k' ← lookupF kk.2
        let ext ← isExt j kk.2
        return some (some (kk.1, (prng.up σ kk.2).1, if ext then none else some (fs.initReceiver k')))
      else return some none
  fsSend ctx P _ ssv h m pair := do
    match ssv with
    | some ss =>
      let o := fs.send ss h m
      return some (some o.1, o.2)
    | none =>
      let s ← get
      match s.ext with
      | some (ss, rs) =>
        let o := fs.send ss h m
        set { s with ext := some (o.1, rs) }
        return some (none, o.2)
      | none =>
        let ok ← if !(ctx.safeCh (2 + Δcka) P) && !s.fsSCorr then do
            match ← liftF (FSAEAD.corruptSenderQuery (ReceiverState := RS) (AssocData := Header T)
                (Message := M) (Ciphertext := E)) with
            | none => pure false
            | some _ =>
              modify fun s => { s with fsSCorr := true }
              pure true
          else pure true
        if !ok then return none
        let e? ← match pair with
          | some (m₀, m₁) => liftF (FSAEAD.challengeQuery (SenderState := SS) (ReceiverState := RS)
              h m₀ m₁)
          | none => liftF (FSAEAD.transmitQuery (SenderState := SS) (ReceiverState := RS) h m)
        match e? with
        | none => return none
        | some e =>
          modify fun s => { s with fsCount := s.fsCount + 1,
                                   fsTrans := (s.fsCount + 1, h, e) :: s.fsTrans }
          return some (none, e)
  fsRecv _ _ _ rsv h e rec := do
    match rsv with
    | some rs => return some ((fs.receive rs h e).map fun o => (some o.1, o.2.1, o.2.2))
    | none =>
      let s ← get
      match s.ext with
      | some (ss, rs) =>
        match fs.receive rs h e with
        | none => return some none
        | some (rs', i, m) =>
          set { s with ext := some (ss, rs') }
          return some (some (none, i, m))
      | none =>
        let matched := s.fsTrans.find? (fun x => x.2 == (h, e))
        let res ← if matched.isSome then
            liftF (FSAEAD.deliverQuery (SenderState := SS) (ReceiverState := RS) h e)
          else liftF (FSAEAD.injectQuery (SenderState := SS) (ReceiverState := RS) h e)
        match res with
        | none => return none
        | some .rejected => return some none
        | some (.accepted i mo') =>
          let drop := (matched.map (·.1)).getD i
          modify fun s => { s with fsTrans := s.fsTrans.filter (·.1 != drop) }
          match mo', rec with
          | some m, _ => return some (some (none, i, m))
          | none, some r => return some (some (none, i, r.msg))
          | none, none => return none
  commit _ _ _ new := pure (some new)
  reveal _ _ vp := do
    let vS? : Option (Option SS) ← match vp.vS with
      | none => pure (some none)
      | some (some ss) => pure (some (some ss))
      | some none => do
        match (← get).ext with
        | some (ss, _) => pure (some (some ss))
        | none =>
          match ← liftF (FSAEAD.corruptSenderQuery (ReceiverState := RS) (AssocData := Header T)
              (Message := M) (Ciphertext := E)) with
          | none => pure none
          | some ss =>
            modify fun s => { s with fsSCorr := true }
            pure (some (some ss))
    match vS? with
    | none => return none
    | some vS =>
      let rsExt? : Option (Option RS) ← match vp.vR mo.tStar with
        | some none => do
          match (← get).ext with
          | some (_, rs) => pure (some (some rs))
          | none =>
            if mo.auth then pure none
            else
              match ← liftF (FSAEAD.corruptReceiverQuery (SenderState := SS) (ReceiverState := RS)
                  (AssocData := Header T) (Message := M) (Ciphertext := E)) with
              | none => pure none
              | some (ss, rs) =>
                modify fun s => { s with ext := some (ss, rs) }
                pure (some (some rs))
        | _ => pure (some none)
      match rsExt? with
      | none => return none
      | some rsExt =>
        let vR : ℕ → Option RS := fun t => match vp.vR t with
          | some (some rs) => some rs
          | some none => rsExt
          | none => none
        return some (realParty vp vp.γ vp.root vS vR)

def initFS : FHM (Option (PartyState Γ T Sig (Option SS) (Option RS) ×
    PartyState Γ T Sig (Option SS) (Option RS))) := do
  let kr ← StateT.lift (sampleT KR)
  let kc ← StateT.lift (sampleT KC)
  let (σ, k, sid) ← rootFS prng mo 0 lam (prng.init kr)
  let ext ← extOf j sid
  return some (mkParties (cka.initA kc) (cka.initB kc) σ
    (if ext then none else some (fs.initSender k)) (if ext then none else some (fs.initReceiver k)))

def runFS (b : Bool) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.AdversaryComp SS RS (Header T) M E
      (Option (Bool × EState (PartyState Γ T Sig (Option SS) (Option RS)) M (Header T × E)
        (FSState T Sig K I SS RS E))) :=
  engRun (hooksFS cka prng fs Δcka mo j) (2 + Δcka) qep fs.maxSkip mo.cfg mo.policy
    (initFS cka prng fs lam mo j) {} b A

/-- FS-AEAD authenticity reduction (`B3` of ACD19 Lemma 11) attacking session `j`. -/
def redFSAuth (j : ℕ) (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← runFS cka prng fs lam Δcka qep ⟨true, tL, t⟩ j false A
  sampleT Bool

/-- FS-AEAD privacy reduction (`B3` of ACD19 Lemma 15; DEV-SM25). -/
def redFSPriv (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  match ← runFS cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A with
  | none => sampleT Bool
  | some (b', es) => if privValid (2 + Δcka) ⟨false, tL, t⟩ es then pure b' else sampleT Bool

/-- Variant of `redFSPriv` outputting a uniform coin, whose advantage equals the FS-AEAD
forgery-win probability (DEV-SM25). -/
def redFSPrivCoin (tL : Option ℕ) (t : ℕ) (A : SchemeAdversary Γ T Sig SS RS M CCoins E) :
    FSAEAD.Adversary SS RS (Header T) M E :=
  show FSAEAD.AdversaryComp SS RS (Header T) M E Bool from do
  let _ ← runFS cka prng fs lam Δcka qep ⟨false, tL, t⟩ 0 false A
  sampleT Bool

end RedFS

end CryptoGames.SM.Construction
