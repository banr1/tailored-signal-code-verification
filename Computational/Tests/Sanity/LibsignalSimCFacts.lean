/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SpecLemmas.Session.ACD19.Ratchet.LibsignalRefinesCDefs

/-!
# Probe Hook and Simulation Hygiene for `LibsignalSimC`

Definitional unfolding lemmas for `idHook`, `probeHook`, `runLibsignalToModularSchemeSim`, and
`fig8ImplH1` from `LibsignalSimC`, verifying that `idHook` performs no queries or state updates and
that `probeHook` updates only the acceptance flag while running Fig. 8 at `Config.h1`. Also proves
message and coin independence of `lFig8.send` within an epoch and specializes `SpqrSendCorrect` to
any send budget `q`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal

namespace CryptoGames
namespace Ratchet
namespace LibsignalSimC

open CBC CKA LibsignalSession LibsignalInst LibsignalSim SM SM.Construction

section Hooks

variable {PQ Pt : Type} {ℓ : ℕ}

@[simp] theorem idHook_probe (Q : Party) (c : Fig8C Pt) : (idHook (ℓ := ℓ)).probe Q c = pure () :=
  rfl

@[simp] theorem idHook_lift {α : Type} (x : Fig8Comp Pt ℓ α) : (idHook (ℓ := ℓ)).lift x = x := rfl

theorem idHook_probe_run (Q : Party) (c : Fig8C Pt) (sC : LibsignalToModularSchemeSimState PQ Pt ℓ) :
    (StateT.lift ((idHook (ℓ := ℓ)).probe Q c) : StateT (LibsignalToModularSchemeSimState PQ Pt ℓ) (Fig8Comp Pt ℓ) Unit).run sC
      = pure ((), sC) := rfl

end Hooks

variable {PQ PQC Pt : Type} [Inhabited PQ] [DecidableEq Pt] [Zero Pt] [SampleableType PQC] {ℓ : ℕ}

omit [Inhabited PQ] in
theorem simRunC_eq_simRunCWith_idHook (P : Params PQ PQC) (Dh : DHFun (BitVec 256) Pt)
    (encPt : Pt → List (BitVec 8)) (encT : Pt → PublicKey) (decT : PublicKey → Option Pt)
    (idOf : Party → IdentityKey) (lam : Pt) (qep : ℕ)
    (A : SM.Adversary (GhostState PQ) (Plain ℓ) PQC (List (BitVec 8))) :
    runLibsignalToModularSchemeSim P Dh encPt encT decT idOf lam qep A =
      simRunCWith (P := P) (encT := encT) (decT := decT) (qep := qep)
        (fig := lFig8 Dh encPt P.C P.codec ℓ encT idOf 25000 lam)
        (fs := lFS P.C P.codec ℓ encT idOf 25000) (H := idHook) Dh A := rfl

omit [Zero Pt] in
theorem probeHook_probe_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (Q : Party) (c' : Fig8C Pt)
    (gh : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).probe Q c').run gh
      = pure ((), (gh.1, gh.2 || (fig.receive (gh.1.st Q) c').isSome)) := rfl

omit [Zero Pt] in
theorem probeHook_lift_run
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) {α : Type} (x : Fig8Comp Pt ℓ α)
    (gh : GameState (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (Fig8C Pt) × Bool) :
    ((probeHook fig qepF).lift x).run gh = (do
      let (a, g') ← (simulateQ (fig8ImplH1 fig qepF) x).run gh.1
      return (a, (g', gh.2))) := rfl

omit [Zero Pt] in
theorem run_h1_eq
    (fig : SMScheme (BitVec 256 × BitVec 256) (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt))
    (qepF : ℕ) (b : Bool) (A : SM.Adversary (Fig8St Pt) (LibsignalMsgPublicPart × Plain ℓ) (BitVec 256) (Fig8C Pt)) :
    SM.run fig (2 + 1) qepF Config.h1 b A = (do
      let k ← $ᵗ (BitVec 256 × BitVec 256)
      (simulateQ (fig8ImplH1 fig qepF) A).run (initState fig k b)) := rfl

omit [DecidableEq Pt] in
/-- Within a sending epoch (`sendsIn (st.tcur + 1) = false`), `lFig8.send` updates sender state
independently of the message and coins, since coins are only consumed by `CKA-S` on epoch steps. -/
theorem lFig8_send_fst_eq_of_not_sendsIn (Dh : DHFun (BitVec 256) Pt) (encPt : Pt → List (BitVec 8))
    (C : Crypto) (codec : SignalMessageProtoCodec) (encT : Pt → PublicKey) (idOf : Party → IdentityKey)
    (maxSkip : ℕ) (lam : Pt) (st : Fig8St Pt) (hs : st.id.sendsIn (st.tcur + 1) = false)
    (m m' : LibsignalMsgPublicPart × Plain ℓ) (r r' : BitVec 256) :
    ((lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam).send st m r).1 =
      ((lFig8 Dh encPt C codec ℓ encT idOf maxSkip lam).send st m' r').1 := by
  simp only [lFig8, scheme, Construction.send, hs, Bool.false_eq_true, ite_false]
  cases st.vS <;> rfl

end LibsignalSimC
end Ratchet
end CryptoGames

namespace CryptoGames.LibsignalSM.Corr

/-- Ungraded `SpqrSendCorrect` implies `SpqrSendCorrectQ` at every send budget `q` via the constant
invariant family. -/
theorem spqrSendCorrectQ_of_spqrSendCorrect {PQ PQC : Type} {S : LibsignalSession.Spqr PQ PQC}
    (h : SpqrSendCorrect S) (q : ℕ) : SpqrSendCorrectQ S q := by
  obtain ⟨Inv, hI, hT, hP⟩ := h
  exact ⟨fun _ => Inv, ⟨hI.init, fun _ => hI.send, fun _ => hI.recv⟩, fun _ st r _ h => hT st r h,
    fun _ st r _ h => hP st r h⟩

end CryptoGames.LibsignalSM.Corr
