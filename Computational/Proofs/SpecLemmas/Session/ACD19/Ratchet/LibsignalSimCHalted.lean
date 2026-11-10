/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs

/-!
# Online send-halted `LibsignalSimC` simulator

**Checked by Lean.**

Defines the online send-halted variant of `LibsignalSimC` matching `GameRCoinLogged.gameRCoinHalted`:
accepted `transmit` and `chall` queries log their send coin `rq` and immediately return `none`
whenever `badLog (log ++ [rq]) = true`.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimCHalted

noncomputable section

open scoped ENNReal
open OracleComp OracleSpec

open CryptoGames (Party SMScheme FSAEADScheme)
open CryptoGames.CBC (Plain)
open CryptoGames.CKA (DHFun)
open CryptoGames.SM
  (GameState Record RecvResult initState noBobSendInEpoch0)
open CryptoGames.SM.Construction (Header)
open CryptoGames.Ratchet.LibsignalInst
  (LibsignalMsgPublicPart LibsignalCiphertextWithSalt32 lFig8 lFS)
open CryptoGames.Ratchet.LibsignalSim
  (Fig8St Fig8C Fig8Comp SimState liftQ putS mkPub toWire)
open CryptoGames.Ratchet.LibsignalSimC
  (LibsignalToModularSchemeSimState Kept Hook initSimC idHook probeHook
   runOnBaseState liftC simImplC)
open CryptoGames.LibsignalSession (Params PublicKey IdentityKey GhostState)
open CryptoGames.LibsignalSM (LibAdv Fig8Adv)

def simSendPostCoin {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    (P : Params PQ PQC)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (r : Option PQC) (rq : PQC) :
    StateT (SimState PQ Pt ℓ) (Fig8Comp Pt ℓ) (Option (List (BitVec 8))) := do
  let s ← get
  let pn :=
    if s₁.epoch Q ≠ s.mir.epoch Q then BitVec.ofNat 32 (s.mir.idx Q - 1)
    else s.pn Q
  let rc : Option (BitVec 256) ← match r with
    | some _ => some <$> CryptoGames.Ratchet.LibsignalSim.coin (BitVec 256)
    | none => pure none
  match mkPub (P := P) s Q rq pn with
  | none => return none
  | some (pq', pub) =>
    let res ← match chal with
      | none => liftQ (CryptoGames.SM.transmitQuery (St := Fig8St Pt) Q (pub, m₀) rc)
      | some m₁ => liftQ (CryptoGames.SM.challQuery (St := Fig8St Pt) Q (pub, m₀) (pub, m₁) rc)
    match res with
    | none => return none
    | some c =>
      let w := toWire c
      let rec' : Record (Plain ℓ) (List (BitVec 8)) :=
        ⟨⟨Q, s₁.epoch Q, s₁.idx Q + 1⟩, m₀, w⟩
      let mir' := s₁.record 3 Q () rec' chal.isSome
      putS { s with
        mir := mir'
        pq := Function.update s.pq Q pq'
        pn := Function.update s.pn Q pn
        honest := (w, c) :: s.honest }
      return some w

def simSendPostCoinC {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] {ℓ : ℕ}
    {M : Type → Type} [Monad M]
    (P : Params PQ PQC)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (H : Hook Pt ℓ M)
    (s₁ : GameState Unit (Plain ℓ) (List (BitVec 8)))
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ))
    (r : Option PQC) (rq : PQC) :
    StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M (Option (List (BitVec 8))) := do
  let res ← runOnBaseState H (simSendPostCoin P s₁ Q m₀ chal r rq)
  match res with
  | none => return none
  | some w =>
    let sC ← get
    let sent := match (sC.kept Q).full, sC.base.honest.head? with
      | some st, some (_, c) =>
        if st.id.sendsIn (st.tcur + 1) then sC.sent
        else match st.vS with
          | some v => (c, v) :: sC.sent
          | none => sC.sent
      | _, _ => sC.sent
    set { sC with kept := Function.update sC.kept Q (Kept.send (fig := fig) (sC.kept Q)), sent }
    return some w

abbrev SimCMHalted (PQ PQC Pt : Type) (ℓ : ℕ) (M : Type → Type) :=
  StateT (List PQC) (StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) M)

/-- Online-halted `transmit`/`chall` handler returning `none` when `badLog` triggers on the extended
coin log. -/
def simSendCHalted {PQ PQC Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}
    {M : Type → Type} [Monad M]
    (badLog : List PQC → Bool) (P : Params PQ PQC) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (H : Hook Pt ℓ M)
    (Q : Party) (m₀ : Plain ℓ) (chal : Option (Plain ℓ)) (r : Option PQC) :
    SimCMHalted PQ PQC Pt ℓ M (Option (List (BitVec 8))) := do
  let sC ← StateT.lift get
  if sC.base.stopped || sC.base.mir.win || !(noBobSendInEpoch0 sC.base.mir Q) then
    return none
  match sC.base.mir.epMgmt 3 qep Q r.isSome with
  | none => return none
  | some s₁ =>
    if chal.isSome && !(s₁.safeCh 3 Q) then return none
    let rq ← StateT.lift (match r with
      | some rq => pure rq
      | none => liftC H (liftM ($ᵗ PQC : ProbComp PQC) : Fig8Comp Pt ℓ PQC))
    let log ← get
    let log' := log ++ [rq]
    set log'
    if badLog log' then
      return none
    else
      StateT.lift (simSendPostCoinC P fig H s₁ Q m₀ chal r rq)

def simImplCHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} {M : Type → Type} [Monad M]
    (badLog : List PQC → Bool) (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt) :
    QueryImpl (unifSpec + CryptoGames.SM.spec (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8)))
      (SimCMHalted PQ PQC Pt ℓ M) :=
  let base := simImplC (P := P) (encT := encT) (decT := decT) (qep := qep)
    (fig := fig) (fs := fs) (H := H) Dh
  let c : QueryImpl unifSpec (SimCMHalted PQ PQC Pt ℓ M) :=
    fun n => StateT.lift (base (.inl n))
  let i₁ : QueryImpl ((Party × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8)))
      (SimCMHalted PQ PQC Pt ℓ M) :=
    fun ⟨Q, m₀, r⟩ => simSendCHalted badLog P qep fig H Q m₀ none r
  let i₂ : QueryImpl ((Party × Plain ℓ × Plain ℓ × Option PQC) →ₒ Option (List (BitVec 8)))
      (SimCMHalted PQ PQC Pt ℓ M) :=
    fun ⟨Q, m₀, m₁, r⟩ => simSendCHalted badLog P qep fig H Q m₀ (some m₁) r
  let i₃ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (SimCMHalted PQ PQC Pt ℓ M) :=
    fun q => StateT.lift (base (.inr (.inl (.inl (.inr q)))))
  let i₄ : QueryImpl ((Party × List (BitVec 8)) →ₒ Option (RecvResult (Plain ℓ)))
      (SimCMHalted PQ PQC Pt ℓ M) :=
    fun q => StateT.lift (base (.inr (.inl (.inr q))))
  let i₅ : QueryImpl (Party →ₒ Option (GhostState PQ))
      (SimCMHalted PQ PQC Pt ℓ M) :=
    fun q => StateT.lift (base (.inr (.inr q)))
  HAdd.hAdd c (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd (HAdd.hAdd i₁ i₂) i₃) i₄) i₅)

def simRunCWithHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] {ℓ : ℕ} {M : Type → Type} [Monad M]
    (badLog : List PQC → Bool) (P : Params PQ PQC) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (qep : ℕ)
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (fs : FSAEADScheme (BitVec 256) (CryptoGames.FSAEAD.RatchetSenderState (BitVec 256))
      (CryptoGames.FSAEAD.RatchetReceiverState (BitVec 256) (BitVec 256)) (Header Pt)
      (LibsignalMsgPublicPart × Plain ℓ) (ℕ × LibsignalCiphertextWithSalt32))
    (H : Hook Pt ℓ M) (Dh : DHFun (BitVec 256) Pt)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : M Bool := do
  let pqrKey ← H.lift (liftM ($ᵗ BitVec 256 : ProbComp (BitVec 256)) : Fig8Comp Pt ℓ (BitVec 256))
  ((simulateQ (simImplCHalted badLog P encT decT qep fig fs H Dh) A).run' []).run'
    (initSimC (P.spqr.init .a2b pqrKey) (P.spqr.init .b2a pqrKey))

/-- Online send-halted `libsignalToModularSchemeSim` (`simRunCWithHalted` with `idHook`). -/
def libsignalToModularSchemeSimHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) : Fig8Adv Pt ℓ :=
  simRunCWithHalted badLog P encT decT qep
    (lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
    (lFS P.C P.codec ℓ encT idOf 25000) idHook Dh A

/-- Fig. 8 `H1` win event of `libsignalToModularSchemeSimHalted`. -/
def simCNoneWinEventHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ) (A : LibAdv PQ PQC ℓ) : ProbComp Bool := do
  let b ← $ᵗ Bool
  let sm := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, s) ← CryptoGames.SM.run sm 3 (qep + 1) CryptoGames.SM.Config.h1 b
    (libsignalToModularSchemeSimHalted badLog P ℓ Dh encPt encT decT idOf lam qep A)
  return s.win

/-- Online send-halted variant of `hiddenSaltGame`. -/
def hiddenSaltGameHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    ProbComp Bool := do
  let b ← $ᵗ Bool
  let k ← $ᵗ (BitVec 256 × BitVec 256)
  let fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam
  let (_, gh) ←
    (simRunCWithHalted badLog P encT decT qep fig (lFS P.C P.codec ℓ encT idOf 25000)
      (probeHook fig (qep + 1)) Dh A).run
    (initState fig k b, false)
  return gh.2

def hiddenSaltTermHalted {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt]
    [SampleableType PQC] (badLog : List PQC → Bool) (P : Params PQ PQC) (ℓ : ℕ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey)
    (lam : Pt) (qep : ℕ)
    (A : CryptoGames.SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) : ℝ≥0∞ :=
  𝒟[hiddenSaltGameHalted badLog P ℓ Dh encPt encT decT idOf lam qep A] {true}

end

end Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalSimCHalted
