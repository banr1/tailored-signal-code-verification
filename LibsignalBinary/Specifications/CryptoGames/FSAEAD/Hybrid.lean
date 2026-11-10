/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction

/-!
# Hybrid games for ACD19 Thm 5: shared state and non-encrypting oracles

**Trusted in part.** The theorems of `Computational/Theorems/` use only `isLookaheadHop` from this
file: read it. Everything else here is checked by Lean. See
`Computational/docs/TRUSTED_BASE.md`.

Shared hybrid state (`Slot`, `HState`, `HSt`, `Params`, `Kind`, `SpecialOps`), state combinators
(`onH`, `getH`, `modifyH`, `sampleH`), lazy chain generation (`chainFrom`, `genStep`, `genN`,
`genUpTo`, `reveal`), decryption (`kind`, `decIdx`), corruption oracles (`senderKey`,
`corruptSenderH`, `corruptReceiverH`), and hybrid parameters (`hOut`, `hInit`, `DG`, `hp`,
`isLookaheadHop`) for the proof of ACD19 Thm 5 (including lookahead mode, DEV-FS14).
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.FSAEAD.Thm5

variable {CK MK AD M C : Type}

/-- Chain key after `n` PRG steps from the chain key `w` at chain position `p` (step `p + i` uses
`G (p + i)`). -/
def chainFrom (G : ℕ → PRGScheme CK (CK × MK)) (p : ℕ) (w : CK) : ℕ → CK
  | 0 => w
  | n + 1 => ((G (p + n)).gen (chainFrom G p w n)).1

/-- The frontier slot: the chain key at the first ungenerated chain position. -/
inductive Slot (CK MK : Type) where
  /-- Uniformly random, not sampled yet. -/
  | unknown
  /-- A known chain key. -/
  | seed (w : CK)
  /-- The PRG challenge `(w', K)` for position `pos` (in the PRG reduction): positions before
  `pos` get uniform message keys, position `pos` outputs the challenge. -/
  | mat (pos : ℕ) (m : CK × MK)

/-- Bookkeeping state of a hybrid game (without the frontier `Slot`). -/
structure HState (CK MK AD M C : Type) where
  b : Bool
  lastSentIdx : ℕ := 0
  senderCorruptedAt : Option ℕ := none
  receiverIdx : ℕ := 0
  ended : Bool := false
  win : Bool := false
  inTransit : List (Record AD M (ℕ × C)) := []
  challengesInTransit : List ℕ := []
  /-- Message keys `K_1, …, K_g` of the generated chain positions. -/
  keys : List MK := []
  /-- Chain key revealed at the first corruption of `A`. -/
  corrKey : Option CK := none
  /-- Indices of `B`'s stored skipped keys, in the order of `D`. -/
  skipped : List ℕ := []
  /-- Whether an uncompromised lookahead forgery occurred (DEV-FS14). -/
  lf : Bool := false

namespace HState

def isCompromised (st : HState CK MK AD M C) (i : ℕ) : Bool :=
  match st.senderCorruptedAt with
  | some j => decide (j < i)
  | none => false

def removeFromTransit (st : HState CK MK AD M C) (i : ℕ) : HState CK MK AD M C :=
  { st with inTransit := st.inTransit.filter (·.idx != i),
            challengesInTransit := st.challengesInTransit.filter (· != i) }

end HState

/-- Full hybrid state: bookkeeping and slot. -/
abbrev HSt (CK MK AD M C : Type) := HState CK MK AD M C × Slot CK MK

/-- The OT-CCA oracles for the special index `j + 1`, in the ambient monad. -/
structure SpecialOps (AD M C : Type) (m : Type → Type) where
  /-- Encrypt a message under header `(i, a)` (the OT-CCA `encrypt` oracle). -/
  enc : (ℕ × AD) → M → m C
  /-- Decrypt a ciphertext under header `(i, a)` (the OT-CCA `decrypt` oracle). -/
  dec : (ℕ × AD) → C → m (Option M)

/-- Parameters of a hybrid game. -/
structure Params where
  /-- Positions `< j` are randomized; position `j` uses the slot. -/
  j : ℕ
  /-- Uncompromised indices `≤ t` are ideal (`none`: all of them). -/
  t : Option ℕ
  /-- Lookahead mode. -/
  la : Bool

/-- How index `i` is encrypted and decrypted. -/
inductive Kind where
  /-- Ideal: encryption gives an ideal ciphertext, decryption rejects (OT-CCA ideal world). -/
  | ideal
  /-- Special: encrypted and decrypted with the OT-CCA oracles (`SpecialOps`). -/
  | special
  /-- Real: encrypted and decrypted with the message key of the index. -/
  | real

section Oracles

variable {m : Type → Type} [Monad m] [MonadLiftT ProbComp m]
  [SampleableType MK] [SampleableType CK] [SampleableType C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)
  (P : Params) (D : ℕ → ProbComp (CK × MK)) (ops : Option (SpecialOps AD M C m))

local notation "St" => HSt CK MK AD M C
local notation "HS" => HState CK MK AD M C

/-- Run a computation on the bookkeeping state only. -/
def onH {α : Type} (f : StateT HS m α) : StateT St m α :=
  StateT.mk fun s => (fun p => (p.1, (p.2, s.2))) <$> f.run s.1

/-- Read the bookkeeping state. -/
def getH : StateT St m HS := onH get

/-- Modify the bookkeeping state. -/
def modifyH (f : HS → HS) : StateT St m Unit := onH (modify f)

/-- Sample in the ambient monad. -/
def sampleH {α : Type} (p : ProbComp α) : StateT St m α := liftM (liftM p : m α)

/-- Generate the next chain position `g = keys.length`: from a known seed with `G g`; from an
unknown slot with a uniform message key (`g < P.j`) or with the distribution `D g` (`g ≥ P.j`). -/
def genStep : StateT St m Unit := StateT.mk fun s =>
  match s.2 with
  | .seed w =>
    pure ((), ({ s.1 with keys := s.1.keys ++ [((G s.1.keys.length).gen w).2] },
      .seed ((G s.1.keys.length).gen w).1))
  | .mat pos mt =>
    if s.1.keys.length < pos then do
      let K ← (liftM ($ᵗ MK : ProbComp MK) : m MK)
      pure ((), ({ s.1 with keys := s.1.keys ++ [K] }, .mat pos mt))
    else pure ((), ({ s.1 with keys := s.1.keys ++ [mt.2] }, .seed mt.1))
  | .unknown =>
    if s.1.keys.length < P.j then do
      let K ← (liftM ($ᵗ MK : ProbComp MK) : m MK)
      pure ((), ({ s.1 with keys := s.1.keys ++ [K] }, .unknown))
    else do
      let mt ← (liftM (D s.1.keys.length) : m (CK × MK))
      pure ((), ({ s.1 with keys := s.1.keys ++ [mt.2] }, .seed mt.1))

/-- Generate `n` chain positions. -/
def genN : ℕ → StateT St m Unit
  | 0 => pure ()
  | n + 1 => do genStep G P D; genN n

/-- Generate chain positions until `K_i` is known. -/
def genUpTo (i : ℕ) : StateT St m Unit := do
  let st ← getH
  genN G P D (i - st.keys.length)

/-- Reveal the frontier chain key, sampling it if it is not known. -/
def reveal : StateT St m CK := StateT.mk fun s =>
  match s.2 with
  | .seed w => pure (w, s)
  | _ => do
    let u ← (liftM ($ᵗ CK : ProbComp CK) : m CK)
    pure (u, (s.1, .seed u))

/-- The kind of index `i` in state `st`. -/
def kind (st : HS) (i : ℕ) : Kind :=
  if P.t.all (fun t => decide (i ≤ t)) && !st.isCompromised i then .ideal
  else if ops.isSome && i == P.j + 1 && !st.isCompromised i then .special
  else .real

/-- Decrypt `e` with header `(i, a)` under index `i`; `hint = some msg` for an honest ciphertext
of `msg` (it decrypts correctly). -/
def decIdx (hint : Option M) (i : ℕ) (a : AD) (e : C) : StateT St m (Option M) := do
  match hint with
  | some msg => pure (some msg)
  | none =>
    let st ← getH
    match kind P ops st i, ops with
    | .ideal, _ => pure none
    | .special, some o => liftM (o.dec (i, a) e)
    | _, _ => pure ((st.keys[i - 1]?).bind fun K => ae.dec K (i, a) e)

/-- Indices skipped when `B` jumps from `iB` to `i`, in the order `skipKeys` stores them. -/
def newSkipped (iB i : ℕ) : List ℕ := (List.range' (iB + 1) (i - iB - 1)).reverse

/-- Sender state revealed by a corruption (the frontier, or derived from `corrKey`). -/
def senderKey : StateT St m CK := do
  let st ← getH
  match st.senderCorruptedAt, st.corrKey with
  | some c, some w => pure (chainFrom G c w (st.lastSentIdx - c))
  | _, _ => reveal

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]

/-- `corr-A`. In lookahead mode the game stops instead. -/
def corruptSenderH (_ : Unit) : StateT St m (Option (RatchetSenderState CK)) := do
  let st ← getH
  if st.ended then pure none
  else if P.la then do modifyH fun st => { st with ended := true }; pure none
  else do
  let w ← senderKey G
  modifyH fun st' => { st' with senderCorruptedAt := some (st.senderCorruptedAt.getD st.lastSentIdx),
                                corrKey := some (st.corrKey.getD w) }
  pure (some ⟨w, st.lastSentIdx⟩)

/-- `corr-B`. In lookahead mode the game stops instead. -/
def corruptReceiverH (_ : Unit) :
    StateT St m (Option (RatchetSenderState CK × RatchetReceiverState CK MK)) := do
  let st ← getH
  if st.ended || !st.challengesInTransit.isEmpty ||
      st.inTransit.any (fun r => !st.isCompromised r.idx) then pure none
  else if P.la then do modifyH fun st => { st with ended := true }; pure none
  else do
  let wA ← senderKey G
  let st ← getH
  let wB := match st.senderCorruptedAt, st.corrKey with
    | some c, some w => chainFrom G c w (st.receiverIdx - c)
    | _, _ => wA
  -- Only compromised skipped indices can be stored when `corr-B` succeeds (DEV-FS6).
  let D := (st.skipped.filter st.isCompromised).filterMap fun i => (st.keys[i - 1]?).map (i, ·)
  modifyH fun st => { st with ended := true }
  pure (some (⟨wA, st.lastSentIdx⟩, ⟨wB, st.receiverIdx, D⟩))

end Oracles

/-! ### Hybrid games and the reductions -/

section Games

variable [SampleableType MK] [SampleableType CK] [SampleableType C]
  [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (maxSkip : ℕ)

/-- Output of a hybrid run: in main mode the FS-AEAD win `b = b' ∨ win`, in lookahead mode the
lookahead-forgery flag `lf`. -/
def hOut (la : Bool) (z : Bool × HSt CK MK AD M C) : Bool :=
  if la then z.2.1.lf else (z.2.1.b == z.1 || z.2.1.win)

/-- Initial hybrid state. -/
def hInit (b : Bool) (sl : Slot CK MK) : HSt CK MK AD M C := ({ b }, sl)

/-- PRG distribution `G_p(s)` at chain position `p`, for a uniform seed `s`. -/
def DG (p : ℕ) : ProbComp (CK × MK) := (G p).gen <$> ($ᵗ CK)

/-- Parameters of hybrid `k` of the main (`la = false`) or lookahead (`la = true`) chain, with
ideal indices up to `t`. -/
def hp (k t : ℕ) (la : Bool) : Params := ⟨k, some t, la⟩

/-- Hybrid step `j` of the sum: hop `j / 2` of the main chain (`j` even) or of the lookahead chain
(`j` odd). -/
def isLookaheadHop (j : ℕ) : Bool := j % 2 == 1

end Games

end CryptoGames.FSAEAD.Thm5
