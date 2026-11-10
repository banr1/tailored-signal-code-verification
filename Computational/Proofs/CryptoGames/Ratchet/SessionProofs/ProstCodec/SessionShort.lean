/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.CryptoGames.Ratchet.LibsignalShortDefs
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.SimAndSM
public import Computational.Proofs.CryptoGames.Ratchet.SessionProofs.ProstCodec.SessionShort.FSAEADRed

/-!
# Short public-part and wire bounds for the session FS-AEAD reductions

**Checked by Lean.**

Assembles `fig8_fsReds_short` and `fig8_fsReds_guardedShort`, showing that every FS-AEAD reduction
in `fig8H1Bound` on `simRun` satisfies `FSAEAD.EncMsgsOk` and `GuardedFSInjectShort` under
`LengthsOk` and `SignalEncodeFits32`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames.LibsignalSM.Proofs.SessionShort

open Ratchet LibsignalInst LibsignalSession HMAC HKDF CBC LibsignalAead SM SM.Construction CKA
  AEADScheme MACScheme WireAEAD FSAEAD

section Defs

variable {St Msg Coins C : Type}

def badSendMsg (ok : Msg → Bool) : (unifSpec + SM.spec St Msg Coins C).Domain → Bool
  | .inr (.inl (.inl (.inl (.inl ⟨_, m, _⟩)))) => !ok m
  | .inr (.inl (.inl (.inl (.inr ⟨_, m₀, m₁, _⟩)))) => !ok m₀ || !ok m₁
  | _ => false

def SendMsgsOk (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C) : Prop :=
  A.IsQueryBoundP (fun t => badSendMsg (St := St) (Coins := Coins) (C := C) ok t = true) 0

end Defs

section Sim

export SimAndSM (GuardedSMShort)

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC]
  {ℓ : ℕ}

theorem simRun_sendShort (P : Params PQ PQC) (hL : LengthsOk P ℓ) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (LibsignalSim.simRun P Dh encT decT qep k A) := by
  exact SimAndSM.simRun_sendShort_proof P hL Dh encT decT qep k A

theorem simRun_guardedSMShort (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encT : Pt → PublicKey) (decT : PublicKey → Option Pt) (qep : ℕ) (k : Option ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    GuardedSMShort (LibsignalSim.simRun P Dh encT decT qep k A) :=
  SimAndSM.simRun_guardedSMShort_proof P Dh encT decT qep k A

end Sim

section Red

variable {St Msg Coins C : Type} [DecidableEq Msg] [DecidableEq C]

theorem challSim_sendOk (Δ qep : ℕ) (ok : Msg → Bool) (A : SM.Adversary St Msg Coins C)
    (hA : SendMsgsOk ok A) : SendMsgsOk ok (Thm1.challSim Δ qep A) := by
  exact SimAndSM.challSim_sendOk_proof Δ qep ok A hA

theorem privRedB_sendOk (Δ qep i : ℕ) (ok : Msg → Bool) (blank : Msg → Msg)
    (hblank : ∀ m, ok (blank m) = ok m) (A : SM.Adversary St Msg Coins C)
    (hA : SendMsgsOk ok A) : SendMsgsOk ok (ThmB.privRedB Δ qep i blank A) := by
  exact SimAndSM.privRedB_sendOk_proof Δ qep i ok blank hblank A hA

theorem challSim_guardedSMShort {T : Type} [DecidableEq T] (Δ qep : ℕ)
    (A : SM.Adversary St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32)))
    (hA : GuardedSMShort A) : GuardedSMShort (Thm1.challSim Δ qep A) :=
  SimAndSM.challSim_guardedSMShort_proof Δ qep A hA

theorem privRedB_guardedSMShort {T : Type} [DecidableEq T] (Δ qep i : ℕ) (blank : Msg → Msg)
    (A : SM.Adversary St Msg Coins (Header T × (ℕ × LibsignalCiphertextWithSalt32)))
    (hA : GuardedSMShort A) : GuardedSMShort (ThmB.privRedB Δ qep i blank A) :=
  SimAndSM.privRedB_guardedSMShort_proof Δ qep i blank A hA

end Red

section Targets

variable {Pt : Type} [DecidableEq Pt] [Zero Pt] [SampleableType Pt]

theorem redFS_encMsgsOk (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (ℓ : ℕ) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ) (ok : LibsignalMsgPublicPart × Plain ℓ → Bool)
    (B : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hB : SendMsgsOk ok B) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    FSAEAD.EncMsgsOk ok (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t B) ∧
      FSAEAD.EncMsgsOk ok (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) ∧
      FSAEAD.EncMsgsOk ok (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) := by
  exact FSAEADRed.redFS_encMsgsOk_proof Dh encPt C codec ℓ encT idOf maxSkip lam qep ok B
    (QueryBounds.isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) hB) j tL t

variable {PQ PQC : Type} [Inhabited PQ] [SampleableType PQC]

/-- Under `LengthsOk P ℓ`, every FS-AEAD reduction in `fig8H1Bound` on `simRun` sends only messages
with short public parts. -/
theorem fig8_fsReds_short (P : Params PQ PQC) (ℓ : ℕ) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep qep' : ℕ)
    (k : Option ℕ) (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    let B := LibsignalSim.simRun P Dh encT decT qep k A
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (∀ j tL t, FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
      (redFSAuth (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' j tL t
        (Thm1.challSim (2 + 1) qep' B))) ∧
    (∀ tL i, FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
        (redFSPriv (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
          (ThmB.privRedB (2 + 1) qep' i (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default)) B)) ∧
      FSAEAD.EncMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB)
        (redFSPrivCoin (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
          (ThmB.privRedB (2 + 1) qep' i (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default)) B))) := by
  have hB := simRun_sendShort P hL Dh encT decT qep k A
  refine ⟨fun j tL t => ?_, fun tL i => ?_⟩
  · exact (redFS_encMsgsOk Dh encPt P.C P.codec ℓ encT idOf 25000 lam qep' _ _
      (challSim_sendOk (2 + 1) qep' _ _ hB) j tL t).1
  · have hBi := privRedB_sendOk (2 + 1) qep' i _ (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default))
      (fun _ => rfl) _ hB
    exact ⟨(redFS_encMsgsOk Dh encPt P.C P.codec ℓ encT idOf 25000 lam qep' _ _ hBi 0 tL i).2.1,
      (redFS_encMsgsOk Dh encPt P.C P.codec ℓ encT idOf 25000 lam qep' _ _ hBi 0 tL i).2.2⟩

theorem redFS_guardedFSInjectShort (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (hfit : SignalEncodeFits32 codec)
    (ℓ : ℕ) (hℓ : ℓ + 16 < 2 ^ 31 + 16) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (qep : ℕ)
    (B : SM.Adversary (LibsignalSim.Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (LibsignalSim.Fig8C Pt))
    (hB : SendMsgsOk (fun m : LibsignalMsgPublicPart × Plain ℓ => m.1.shortB) B)
    (hg : GuardedSMShort B) (j : ℕ) (tL : Option ℕ) (t : ℕ) :
    GuardedFSInjectShort (redFSAuth (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep j tL t B) ∧
      GuardedFSInjectShort (redFSPriv (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) ∧
      GuardedFSInjectShort (redFSPrivCoin (dhScheme Dh) (rootPRNG C.F encPt)
        (lFS C codec ℓ encT idOf maxSkip) lam 1 qep tL t B) :=
  FSAEADRed.redFS_guardedFSInjectShort_proof Dh encPt C codec hfit ℓ hℓ encT idOf maxSkip lam qep B
    (QueryBounds.isQueryBoundP_congr (by rintro (_ | ((((_ | _) | _) | _) | _)) <;> rfl) hB) hg
    j tL t

/-- Under `SignalEncodeFits32 P.codec` and `LengthsOk P ℓ`, every FS-AEAD reduction in `fig8H1Bound`
on `simRun` satisfies `GuardedFSInjectShort`. -/
theorem fig8_fsReds_guardedShort (P : Params PQ PQC) (hfit : SignalEncodeFits32 P.codec)
    (ℓ : ℕ) (hL : LengthsOk P ℓ)
    (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey)
    (decT : PublicKey → Option Pt) (idOf : Party → IdentityKey) (lam : Pt) (qep qep' : ℕ)
    (k : Option ℕ) (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    let B := LibsignalSim.simRun P Dh encT decT qep k A
    let fs := lFS P.C P.codec ℓ encT idOf 25000
    (∀ j tL t, GuardedFSInjectShort
      (redFSAuth (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' j tL t
        (Thm1.challSim (2 + 1) qep' B))) ∧
    (∀ tL i, GuardedFSInjectShort
        (redFSPriv (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
          (ThmB.privRedB (2 + 1) qep' i (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default)) B)) ∧
      GuardedFSInjectShort
        (redFSPrivCoin (dhScheme Dh) (rootPRNG P.C.F encPt) fs lam 1 qep' tL i
          (ThmB.privRedB (2 + 1) qep' i (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default)) B))) := by
  have hB := simRun_sendShort P hL Dh encT decT qep k A
  have hgB := simRun_guardedSMShort P Dh encT decT qep k A
  refine ⟨fun j tL t => ?_, fun tL i => ?_⟩
  · exact (redFS_guardedFSInjectShort Dh encPt P.C P.codec hfit ℓ hL.1 encT idOf 25000 lam qep' _
      (challSim_sendOk (2 + 1) qep' _ _ hB) (challSim_guardedSMShort (2 + 1) qep' _ hgB) j tL t).1
  · have hBi := privRedB_sendOk (2 + 1) qep' i _ (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default))
      (fun _ => rfl) _ hB
    have hgBi := privRedB_guardedSMShort (2 + 1) qep' i
      (fun m : LibsignalMsgPublicPart × Plain ℓ => (m.1, default)) _ hgB
    exact ⟨(redFS_guardedFSInjectShort Dh encPt P.C P.codec hfit ℓ hL.1 encT idOf 25000 lam qep' _ hBi hgBi 0 tL i).2.1,
      (redFS_guardedFSInjectShort Dh encPt P.C P.codec hfit ℓ hL.1 encT idOf 25000 lam qep' _ hBi hgBi 0 tL i).2.2⟩

end Targets

end CryptoGames.LibsignalSM.Proofs.SessionShort
