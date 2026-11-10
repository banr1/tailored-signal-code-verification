/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import VCVio.OracleComp.QueryTracking.QueryBound.Basic
import VCVio.EvalDist.Monad.Bool
import VCVio.OracleComp.Constructions.SampleableType.Measure

/-!
# Encrypt-then-MAC AEAD from a one-time cipher and a PRF-based MAC

**Trusted in part.** The theorems of `Computational/Theorems/` use only `CipherScheme`,
`MACScheme`, `PRFAdversary`, `PRFState`, `prfAdvantage`, `prfEval`, `prfGame`, `prfSpec` from this
file: read them. Everything else here is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Defines one-time symmetric ciphers (`CipherScheme`, `indcpaEncrypt`, `indcpaGame`,
`indcpaAdvantage`), deterministic MACs/PRFs (`MACScheme`), the Encrypt-then-MAC `AEADScheme`
`etm`, the decryption-query bound `MakesAtMostDecQueries`, and the concrete reductions `redCipher`,
`redMACChall`, and `redMACForge` used by `etm_otcca` (`EtM.lean`). Because the OT-CCA and IND-CPA
games sample uniform ciphertexts from `$ᵗ C`, instantiations with AES-256-CBC fix the plaintext
length (DEV-AEAD2).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal MeasureTheory

namespace CryptoGames

/-! ### One-time symmetric cipher (IND-CPA) -/

/-- A deterministic one-time symmetric cipher. All randomness (e.g. key and IV in Signal's
AES-256-CBC-PKCS#7) comes from the one-time key `Key`. Decryption returns `Option Message` to
accommodate padding validation. -/
structure CipherScheme (Key Message Ciphertext : Type) where
  /-- `Enc(k, m)`: encrypt message `m` under key `k`. -/
  enc : Key → Message → Ciphertext
  /-- `Dec(k, c)`: decrypt ciphertext `c` under key `k`; `none` means rejection (e.g. bad padding). -/
  dec : Key → Ciphertext → Option Message

namespace CipherScheme

variable {Key Message Ciphertext : Type}

/-- Perfect correctness: `Dec(k, Enc(k, m)) = some m`. -/
def Correct (cipher : CipherScheme Key Message Ciphertext) : Prop :=
  ∀ k m, cipher.dec k (cipher.enc k m) = some m

/-- One-time IND-CPA oracle: a single `encrypt` query (`none` if queried again). -/
abbrev indcpaSpec (Message Ciphertext : Type) :=
  Message →ₒ Option Ciphertext

/-- One-time IND-CPA game state: key, hidden bit `b`, and whether `encrypt` was already queried. -/
structure INDCPAState (Key : Type) where
  key : Key
  b : Bool
  queried : Bool := false

/-- A one-time IND-CPA adversary, with its own coins (`unifSpec`) and the one-time `encrypt` oracle. -/
abbrev INDCPAAdversary (Message Ciphertext : Type) :=
  OracleComp (unifSpec + indcpaSpec Message Ciphertext) Bool

/-- Query the one-time `encrypt` oracle. -/
def encryptQuery (m : Message) :
    OracleComp (unifSpec + indcpaSpec Message Ciphertext) (Option Ciphertext) :=
  query (spec := unifSpec + indcpaSpec Message Ciphertext) (.inr m)

variable [SampleableType Ciphertext]

/-- One-time `encrypt(m)`: `b = false` returns `cipher.enc key m`; `b = true` returns a uniform
ciphertext `$ᵗ Ciphertext`. Subsequent queries return `none`. -/
def indcpaEncrypt (cipher : CipherScheme Key Message Ciphertext) :
    QueryImpl (indcpaSpec Message Ciphertext) (StateT (INDCPAState Key) ProbComp) := fun m => do
  let st ← get
  if st.queried then return none
  let c ← if st.b then liftM ($ᵗ Ciphertext) else pure (cipher.enc st.key m)
  set { st with queried := true }
  return some c

/-- The one-time IND-CPA game with a fixed hidden bit `b`. -/
def branch [SampleableType Key] (cipher : CipherScheme Key Message Ciphertext)
    (b : Bool) (A : INDCPAAdversary Message Ciphertext) : ProbComp Bool := do
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (INDCPAState Key) ProbComp) + indcpaEncrypt cipher
  (simulateQ impl A).run' { key, b }

/-- One-time IND-CPA hidden-bit game. -/
def indcpaGame [SampleableType Key] (cipher : CipherScheme Key Message Ciphertext)
    (A : INDCPAAdversary Message Ciphertext) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (INDCPAState Key) ProbComp) + indcpaEncrypt cipher
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

/-- `Adv^{ind-cpa}_{cipher}(A)`, the bias `2·|Pr[b = b'] − 1/2|`. -/
noncomputable def indcpaAdvantage [SampleableType Key]
    (cipher : CipherScheme Key Message Ciphertext)
    (A : INDCPAAdversary Message Ciphertext) : ℝ≥0∞ :=
  𝒟[cipher.indcpaGame A].boolBias

theorem indcpaAdvantage_eq_boolDist [SampleableType Key]
    (cipher : CipherScheme Key Message Ciphertext)
    (A : INDCPAAdversary Message Ciphertext) :
    cipher.indcpaAdvantage A = 𝒟[cipher.branch true A].boolDist 𝒟[cipher.branch false A] := by
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := fun _ => by simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) _ _ (hcoin true) (hcoin false)]
  unfold indcpaAdvantage indcpaGame
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [branch]

end CipherScheme

/-! ### Deterministic MAC / PRF game -/

/-- A deterministic MAC / PRF with key space `Key`, input space `Input`, and tag space `Tag`
(in Signal: 8-byte truncated HMAC-SHA256). -/
structure MACScheme (Key Input Tag : Type) where
  /-- `Tag(k, x)`: compute the authentication tag of `x` under key `k`. -/
  tag : Key → Input → Tag

namespace MACScheme

variable {Key Input Tag : Type}

/-- PRF evaluation oracle `Input →ₒ Tag`. -/
abbrev prfSpec (Input Tag : Type) :=
  Input →ₒ Tag

/-- PRF game state: key, hidden bit `b`, and the lazy table of the random function. -/
structure PRFState (Key Input Tag : Type) where
  key : Key
  b : Bool
  table : List (Input × Tag) := []

/-- A PRF adversary, with its own coins (`unifSpec`) and the evaluation oracle `Input →ₒ Tag`. -/
abbrev PRFAdversary (Input Tag : Type) :=
  OracleComp (unifSpec + prfSpec Input Tag) Bool

/-- Query the PRF evaluation oracle at `x`. -/
def evalQuery (x : Input) : OracleComp (unifSpec + prfSpec Input Tag) Tag :=
  query (spec := unifSpec + prfSpec Input Tag) (.inr x)

variable [DecidableEq Input] [SampleableType Tag]

/-- PRF evaluation oracle: `b = false` returns `mac.tag key x`; `b = true` returns a lazily sampled
random function on `Input → Tag`. -/
def prfEval (mac : MACScheme Key Input Tag) :
    QueryImpl (prfSpec Input Tag) (StateT (PRFState Key Input Tag) ProbComp) := fun x => do
  let st ← get
  if st.b then
    match st.table.lookup x with
    | some t => return t
    | none =>
      let t ← liftM ($ᵗ Tag)
      set { st with table := (x, t) :: st.table }
      return t
  else
    return mac.tag st.key x

/-- The PRF game with a fixed hidden bit `b`. -/
def branch [SampleableType Key] (mac : MACScheme Key Input Tag)
    (b : Bool) (A : PRFAdversary Input Tag) : ProbComp Bool := do
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFState Key Input Tag) ProbComp) + prfEval mac
  (simulateQ impl A).run' { key, b }

/-- PRF hidden-bit game. -/
def prfGame [SampleableType Key] (mac : MACScheme Key Input Tag)
    (A : PRFAdversary Input Tag) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let key ← $ᵗ Key
  let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
      (StateT (PRFState Key Input Tag) ProbComp) + prfEval mac
  let b' ← (simulateQ impl A).run' { key, b }
  return b == b'

/-- `Adv^{prf}_{mac}(A)`, the bias `2·|Pr[b = b'] − 1/2|`. -/
noncomputable def prfAdvantage [SampleableType Key]
    (mac : MACScheme Key Input Tag) (A : PRFAdversary Input Tag) : ℝ≥0∞ :=
  𝒟[mac.prfGame A].boolBias

theorem prfAdvantage_eq_boolDist [SampleableType Key]
    (mac : MACScheme Key Input Tag) (A : PRFAdversary Input Tag) :
    mac.prfAdvantage A = 𝒟[mac.branch true A].boolDist 𝒟[mac.branch false A] := by
  have hcoin : ∀ x : Bool, 𝒟[($ᵗ Bool : ProbComp Bool)] {x} = 1 / 2 := fun _ => by simp
  rw [← evalDist_boolBias_bind_coin ($ᵗ Bool) _ _ (hcoin true) (hcoin false)]
  unfold prfAdvantage prfGame
  congr 2
  refine bind_congr fun b => ?_
  cases b <;> simp [branch]

end MACScheme

/-! ### Encrypt-then-MAC AEAD construction and reductions -/

namespace AEADScheme

section EtM

variable {KE KM AD M C T : Type}

/-- Encrypt-then-MAC: encrypt `m` under `k.1 : KE` to obtain `c : C`, then authenticate `(a, c)`
under `k.2 : KM` to obtain tag `τ : T`. Decryption verifies the tag before calling `cipher.dec`.

**DEV-AEAD7 (libsignal): independent cipher and MAC keys.** libsignal derives
`(cipher_key, mac_key, iv)` from one 32-byte message key with HKDF. `etm` takes an independent
uniform pair `(ke, km)`. Replacing the HKDF output by a uniform pair is a PRG step on HKDF,
absorbed into the chain PRG `G` of `FSAEAD.fromAEADPRG` (DEV-AEAD6). Effect: none. -/
def etm [DecidableEq T] (cipher : CipherScheme KE M C) (mac : MACScheme KM (AD × C) T) :
    AEADScheme (KE × KM) AD M (C × T) where
  enc k a m :=
    let c := cipher.enc k.1 m
    (c, mac.tag k.2 (a, c))
  dec k a ct :=
    if mac.tag k.2 (a, ct.1) == ct.2 then cipher.dec k.1 ct.1 else none

/-- Predicate selecting decryption queries in `unifSpec + otccaSpec AD M C`. -/
def isDecQuery : (unifSpec + otccaSpec AD M C).Domain → Bool
  | .inr (.inr _) => true
  | _ => false

/-- `B` makes at most `qd` decryption queries in the OT-CCA game. -/
abbrev MakesAtMostDecQueries (B : OTCCAAdversary AD M C) (qd : ℕ) : Prop :=
  B.IsQueryBoundP (fun q => isDecQuery q = true) qd

/-! #### Concrete reductions for `etm_otcca` -/

/-- Query implementation for `redCipher`. -/
def cipherRedImpl [SampleableType T] :
    QueryImpl (unifSpec + otccaSpec AD M (C × T))
      (OracleComp (unifSpec + CipherScheme.indcpaSpec M C)) :=
  fun q => match q with
  | .inl n => query (spec := unifSpec + CipherScheme.indcpaSpec M C) (.inl n)
  | .inr (.inl ⟨_a, m⟩) => do
    let c? ← CipherScheme.encryptQuery m
    match c? with
    | none => return none
    | some c =>
      let τ ← (liftM ($ᵗ T : ProbComp T) :
        OracleComp (unifSpec + CipherScheme.indcpaSpec M C) T)
      return some (c, τ)
  | .inr (.inr _) => return none

/-- One-time IND-CPA reduction `redCipher B`: simulates `B` with `decrypt` always returning `none`,
and answers the one-time `encrypt(a, m)` query by forwarding `m` to the `indcpaSpec` oracle and
sampling a uniform tag `τ ← $ᵗ T`. -/
def redCipher [SampleableType T] (B : OTCCAAdversary AD M (C × T)) :
    CipherScheme.INDCPAAdversary M C :=
  simulateQ cipherRedImpl B

/-- Query implementation for `redMACChall`. -/
def challRedImpl (cipher : CipherScheme KE M C) (ke : KE) :
    QueryImpl (unifSpec + otccaSpec AD M (C × T))
      (StateT Bool (OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T))) :=
  fun q => match q with
  | .inl n => StateT.lift (query (spec := unifSpec + MACScheme.prfSpec (AD × C) T) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    let queried ← get
    if queried then return none
    set true
    let c := cipher.enc ke m
    let τ ← StateT.lift (MACScheme.evalQuery (a, c))
    return some (c, τ)
  | .inr (.inr _) => return none

/-- Challenge-tag PRF reduction `redMACChall cipher B`: samples `ke ← $ᵗ KE`, simulates `B` with
`decrypt` always returning `none`, and answers the one-time `encrypt(a, m)` query by computing
`c = cipher.enc ke m` and querying the PRF oracle once at `(a, c)`. -/
def redMACChall [SampleableType KE] (cipher : CipherScheme KE M C)
    (B : OTCCAAdversary AD M (C × T)) :
    MACScheme.PRFAdversary (AD × C) T :=
  (do
    let ke ← (liftM ($ᵗ KE : ProbComp KE) :
      OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) KE)
    (simulateQ (challRedImpl cipher ke) B).run' false :
      OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) Bool)

/-- State of the `j`-th decryption-query forgery PRF reduction `redMACForge`. -/
structure ForgeState (AD C T : Type) where
  chal : Option (AD × (C × T)) := none
  idx : ℕ := 0
  forged : Bool := false

/-- Query implementation for `redMACForge`. -/
def forgeRedImpl [DecidableEq AD] [DecidableEq C] [DecidableEq T]
    (cipher : CipherScheme KE M C) (ke : KE) (j : ℕ) :
    QueryImpl (unifSpec + otccaSpec AD M (C × T))
      (StateT (ForgeState AD C T) (OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T))) :=
  fun q => match q with
  | .inl n => StateT.lift (query (spec := unifSpec + MACScheme.prfSpec (AD × C) T) (.inl n))
  | .inr (.inl ⟨a, m⟩) => do
    let st ← get
    if st.chal.isSome then return none
    let c := cipher.enc ke m
    let τ ← StateT.lift (MACScheme.evalQuery (a, c))
    set { st with chal := some (a, (c, τ)) }
    return some (c, τ)
  | .inr (.inr ⟨a, (c, τ)⟩) => do
    let st ← get
    if st.idx == j && st.chal != some (a, (c, τ)) then
      let τ' ← StateT.lift (MACScheme.evalQuery (a, c))
      set { st with idx := st.idx + 1, forged := st.forged || (τ' == τ) }
      return none
    else
      set { st with idx := st.idx + 1 }
      return none

/-- Decryption-forgery PRF reduction `redMACForge cipher j B` for the `j`-th decryption query:
samples `ke ← $ᵗ KE`, runs `B` with `decrypt` always returning `none` (and `encrypt` querying the
PRF oracle once at `(a, cipher.enc ke m)`), and on the `j`-th decryption query `(a, (c, τ))` with
`chal != some (a, (c, τ))`, queries the PRF oracle at `(a, c)` and records whether the tag matches
`τ`. Outputs `forged`. -/
def redMACForge [DecidableEq AD] [DecidableEq C] [DecidableEq T] [SampleableType KE]
    (cipher : CipherScheme KE M C) (j : ℕ) (B : OTCCAAdversary AD M (C × T)) :
    MACScheme.PRFAdversary (AD × C) T :=
  (do
    let ke ← (liftM ($ᵗ KE : ProbComp KE) :
      OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) KE)
    let (_, st) ← (simulateQ (forgeRedImpl cipher ke j) B).run {}
    return st.forged :
      OracleComp (unifSpec + MACScheme.prfSpec (AD × C) T) Bool)

end EtM

end AEADScheme

end CryptoGames
