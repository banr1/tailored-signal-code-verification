/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.E2E.Dsl.PqxdhSimTypes
public import Computational.Proofs.E2E.Dsl.SmReachInvParty
public import Computational.Proofs.E2E.Dsl.SmReachInv
public import Computational.Proofs.E2E.Dsl.DrSessionSimHooks

/-!
# Simulator Interface Contracts for E2E `ReductionDsl` Sub-Programs

Defines the `PqxdhSimIface` and `DrSessionSimIface` simulator contracts, shared `SM.spec` and
deduplicated `GameState` codecs, and re-exported reachability invariants consumed by the E2E
multi-session composition reductions.
-/

@[expose] public section

set_option autoImplicit false

namespace Computational.Proofs.E2E.Dsl.M2Interfaces

open OracleSpec OracleComp
open ReductionDsl (Ty Env Iface Expr Comp)
open CryptoGames (Party)
open CryptoGames.CBC (Plain)
open CryptoGames.SM (Pos Record GameState partyEnc partyDec posTy posEnc posDec)
open CryptoGames.LibsignalSession (Crypto PublicKey IdentityKey GhostState)
open CryptoVerification.LibsignalSpqrV1 (MlKem spqrV1SessionUniformCoins)
open CryptoVerification.E2E (Bytes paramsIdsWithSpqr sessionSchemeFixedSpk configRefuseEarlyBobCorr
  bhPackSmResp)
open CryptoVerification.E2E.Costed (e2eSig B PlainT GhostStT recvResultT recvResultEnc
  recvResultDec partyToBool boolToParty smQT smQenc smRT smRdec keyIndQT keyIndQenc keyIndQdec
  keyIndRT keyIndRenc e2eOps)
open Computational.Proofs.E2E.Dsl.TablesHonest (keyIndQenc_keyIndQdec recvResultDec_recvResultEnc)
open Computational.Proofs.E2E.Dsl.PqxdhSimTypes (stepAIface e2eKeyIndStateTy e2eKeyIndStateToVal
  KeyIndSetupBounded pqxdhKeyIndImpl1KeyReal_preserves_setupBounded)
open Computational.Proofs.E2E.Dsl.SmReachInv (dedupComp)

/-! ## Re-exported Reachability Invariants and SPQR Hook Contract -/

abbrev SpqrDslHooks := Computational.Proofs.E2E.Dsl.DrSessionSimHooks.SpqrDslHooks

abbrev PartyReachInv := Computational.Proofs.E2E.Dsl.SmReachInvParty.PartyReachInv

abbrev GameReachInv := Computational.Proofs.E2E.Dsl.SmReachInv.GameReachInv

abbrev SmListBounded := Computational.Proofs.E2E.Dsl.SmReachInv.SmListBounded

abbrev SmReachBounded := Computational.Proofs.E2E.Dsl.SmReachInv.SmReachBounded

abbrev SmReachInv := Computational.Proofs.E2E.Dsl.SmReachInv.SmReachBounded

/-! ## Shared SM Query, Response, and `GameState` Codecs -/

@[simp] theorem boolToParty_partyToBool (p : Party) : boolToParty (partyToBool p) = p := by
  cases p <;> rfl

@[simp] theorem partyToBool_boolToParty (b : Bool) : partyToBool (boolToParty b) = b := by
  cases b <;> rfl

def smQdec {ℓ : ℕ} {St : Type} :
    (smQT (ℓ := ℓ)).denote → (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain
  | .inl (p, (m, r)) => .inl (.inl (.inl (.inl (boolToParty p, m, r))))
  | .inr (.inl (p, (m0, (m1, r)))) => .inl (.inl (.inl (.inr (boolToParty p, m0, m1, r))))
  | .inr (.inr (.inl (p, c))) => .inl (.inl (.inr (boolToParty p, c)))
  | .inr (.inr (.inr (.inl (p, c)))) => .inl (.inr (boolToParty p, c))
  | .inr (.inr (.inr (.inr p))) => .inr (boolToParty p)

@[simp] theorem smQdec_smQenc {ℓ : ℕ} {St : Type}
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) :
    smQdec (ℓ := ℓ) (St := St) (smQenc (ℓ := ℓ) sq) = sq := by
  rcases sq with (((⟨p, m, r⟩ | ⟨p, m0, m1, r⟩) | ⟨p, c⟩) | ⟨p, c⟩) | p <;>
    simp [smQenc, smQdec]

@[simp] theorem smQenc_smQdec {ℓ : ℕ} {St : Type} (v : (smQT (ℓ := ℓ)).denote) :
    smQenc (ℓ := ℓ) (St := St) (smQdec (ℓ := ℓ) (St := St) v) = v := by
  rcases v with ⟨p, m, r⟩ | ⟨p, m0, m1, r⟩ | ⟨p, c⟩ | ⟨p, c⟩ | p <;>
    simp [smQenc, smQdec]

def smRenc {ℓ : ℕ} {St : Type} {stT : Ty (e2eSig ℓ)} (toSt : St → stT.denote) :
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain) →
    (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range sq →
    (smRT (ℓ := ℓ) stT).denote
  | .inl (.inl (.inl (.inl _))), w => (w, (none, none))
  | .inl (.inl (.inl (.inr _))), w => (w, (none, none))
  | .inl (.inl (.inr _)), rr => (none, (rr.map recvResultEnc, none))
  | .inl (.inr _), rr => (none, (rr.map recvResultEnc, none))
  | .inr _, st? => (none, (none, st?.map toSt))

theorem smRdec_smRenc {ℓ : ℕ} {St : Type} {stT : Ty (e2eSig ℓ)}
    (ofSt : stT.denote → St) (toSt : St → stT.denote)
    (hrt : ∀ x, ofSt (toSt x) = x)
    (sq : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec St (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    smRdec (stT := stT) ofSt sq (smRenc (stT := stT) toSt sq r) = r := by
  rcases sq with (((_ | _) | _) | _) | _
  · rfl
  · rfl
  · cases r <;> simp [smRenc, smRdec, recvResultDec_recvResultEnc]
  · cases r <;> simp [smRenc, smRdec, recvResultDec_recvResultEnc]
  · cases r with
    | none => rfl
    | some x => simp [smRenc, smRdec, hrt x]

@[simp] theorem smRdec_smRenc_id {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    smRdec (stT := GhostStT) id sq (smRenc (stT := GhostStT) id sq r) = r :=
  smRdec_smRenc (stT := GhostStT) id id (fun _ => rfl) sq r

theorem smRenc_id_eq_bhPackSmResp {ℓ : ℕ}
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain)
    (r : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Range sq) :
    let packed := bhPackSmResp sq r
    smRenc (stT := GhostStT) id sq r =
      (packed.1, (packed.2.1.map recvResultEnc, packed.2.2)) := by
  rcases sq with (((_ | _) | _) | _) | _ <;> simp [smRenc, bhPackSmResp]

/-- `SM.Record (Plain ℓ) Bytes` paired with its cached `comp.contains pos` flag. -/
@[reducible] def e2eRecTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod posTy (.prod PlainT (.prod (B 32) .bool))

def e2eRecEncWith {ℓ : ℕ} (comp : List Pos) (r : Record (Plain ℓ) Bytes) :
    (e2eRecTy ℓ).denote :=
  (posEnc r.pos, (r.msg, (r.ct, comp.contains r.pos)))

def e2eRecDec {ℓ : ℕ} (v : (e2eRecTy ℓ).denote) : Record (Plain ℓ) Bytes :=
  ⟨posDec v.1, v.2.1, v.2.2.1⟩

@[simp] theorem e2eRecDec_e2eRecEncWith {ℓ : ℕ} (comp : List Pos) (r : Record (Plain ℓ) Bytes) :
    e2eRecDec (e2eRecEncWith comp r) = r := by
  cases r; simp [e2eRecEncWith, e2eRecDec]

/-- `SM.GameState (GhostState Bytes) (Plain ℓ) Bytes` with deduplicated `comp` and per-record
cached compromise flags. -/
@[reducible] def e2eGsTy (ℓ : ℕ) : Ty (e2eSig ℓ) :=
  .prod (.prod GhostStT GhostStT)
    (.prod .bool
      (.prod .bool
        (.prod (.prod .nat .nat)
          (.prod (.prod .nat .nat)
            (.prod (.opt .nat)
              (.prod (.list (e2eRecTy ℓ))
                (.prod (.list posTy)
                  (.prod (.list posTy)
                    (.prod (.prod (.tbl .nat) (.tbl .nat))
                      (.prod (.list .nat)
                        (.list (.prod .bool .nat))))))))))))

def e2eGsEnc {ℓ : ℕ} (s : GameState (GhostState Bytes) (Plain ℓ) Bytes) :
    (e2eGsTy ℓ).denote :=
  ((s.st .A, s.st .B),
   (s.b,
    (s.win,
     ((s.epoch .A, s.epoch .B),
      ((s.idx .A, s.idx .B),
       (s.tL,
        (s.trans.map (e2eRecEncWith s.comp),
         (s.chall.map posEnc,
          ((dedupComp s.comp).map posEnc,
           ((s.maxAcc .A, s.maxAcc .B),
            (s.leaks,
             s.corrs.map (fun pe => (partyEnc pe.1, pe.2)))))))))))))

def e2eGsDec {ℓ : ℕ} (v : (e2eGsTy ℓ).denote) :
    GameState (GhostState Bytes) (Plain ℓ) Bytes :=
  let (stAB, (b, (win, (epAB, (idxAB, (tL, (trs, (chall, (comp, (maAB, (leaks, corrs))))))))))) := v
  { st := fun | .A => stAB.1 | .B => stAB.2
    epoch := fun | .A => epAB.1 | .B => epAB.2
    idx := fun | .A => idxAB.1 | .B => idxAB.2
    tL := tL
    trans := trs.map e2eRecDec
    chall := chall.map posDec
    comp := comp.map posDec
    maxAcc := fun | .A => maAB.1 | .B => maAB.2
    b := b
    win := win
    leaks := leaks
    corrs := corrs.map (fun pe => (partyDec pe.1, pe.2)) }

/-! ## `PqxdhSimIface`: PQXDH 1-Key Real Simulator Contract -/

/-- Interface contract for simulating one query of `SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P`
inside `ReductionDsl` under static bound `nAdv` on `st.advKeys.length`. -/
structure PqxdhSimIface (ℓ : ℕ) (S : SignalPqxdh.Setup) {Pt : Type}
    (P : SignalPqxdh.Primitives) (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  stepC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T), ℕ →
    ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S) →
    Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S) →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod keyIndRT (e2eKeyIndStateTy ℓ S))
  stepCost : ℕ → ℕ
  stepC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S)),
    (stepC I₀ nAdv stE qE).cost ≤ stE.cost + qE.cost + stepCost nAdv
  stepC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (stepC I₀ nAdv stE qE).queries w (fun _ => 0) = 0
  stepC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : SignalPqxdh.KeyIndState S) (kq : SignalPqxdh.KeyIndQuery S),
    SignalPqxdh.WellFormedPrimitivesδ P →
    stE.eval ρ = e2eKeyIndStateToVal st →
    qE.eval ρ = keyIndQenc kq →
    KeyIndSetupBounded S st →
    st.advKeys.length ≤ nAdv →
    (stepC I₀ nAdv stE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st))

theorem PqxdhSimIface.stepC_eval_qdec {ℓ : ℕ} {S : SignalPqxdh.Setup} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (sim : PqxdhSimIface ℓ S P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T) (nAdv : ℕ)
    {Γ : List (Ty (e2eSig ℓ))}
    (stE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eKeyIndStateTy ℓ S))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ (keyIndQT S))
    (ρ : Env Γ) (st : SignalPqxdh.KeyIndState S)
    (hP : SignalPqxdh.WellFormedPrimitivesδ P)
    (hstE : stE.eval ρ = e2eKeyIndStateToVal st)
    (hBnd : KeyIndSetupBounded S st)
    (hAdv : st.advKeys.length ≤ nAdv) :
    (sim.stepC I₀ nAdv stE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (keyIndRenc out.1, e2eKeyIndStateToVal out.2)) <$>
          ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P (keyIndQdec (qE.eval ρ))).run st)) :=
  sim.stepC_eval I₀ nAdv stE qE ρ st (keyIndQdec (qE.eval ρ)) hP hstE
    (keyIndQenc_keyIndQdec (qE.eval ρ)).symm hBnd hAdv

theorem pqxdhStep_preserves_bounded {S : SignalPqxdh.Setup} {P : SignalPqxdh.Primitives}
    (kq : SignalPqxdh.KeyIndQuery S) {st : SignalPqxdh.KeyIndState S}
    (hst : KeyIndSetupBounded S st)
    {out : SignalPqxdh.KeyIndResponse × SignalPqxdh.KeyIndState S}
    (hmem : out ∈ support ((SignalPqxdh.pqxdhKeyIndImpl1KeyReal S P kq).run st)) :
    KeyIndSetupBounded S out.2 ∧
      out.2.advKeys.length ≤ st.advKeys.length + 1 ∧
      ((∀ sk, kq ≠ .registerKey sk) → out.2.advKeys.length = st.advKeys.length) :=
  pqxdhKeyIndImpl1KeyReal_preserves_setupBounded kq hst hmem

/-! ## `DrSessionSimIface`: Double Ratchet + SPQR V1 Simulator Contract -/

/-- Interface contract for simulating one query of `SM.oracleImplR` on `sessionSchemeFixedSpk`
inside `ReductionDsl` under history bound `qBound` and epoch bound `qep`. -/
structure DrSessionSimIface (ℓ : ℕ) {Pt : Type} (P : SignalPqxdh.Primitives)
    (C : Crypto) (K : MlKem)
    (decT : PublicKey → Option Pt) (encT : Pt → PublicKey) where
  oracleStepC : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T),
    ℕ → ℕ → ∀ {Γ : List (Ty (e2eSig ℓ))},
    Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ) →
    Expr (e2eOps ℓ P C K decT encT) Γ smQT →
    Comp (e2eOps ℓ P C K decT encT) (stepAIface ℓ I₀) Γ
      (.prod (smRT GhostStT) (e2eGsTy ℓ))
  oracleStepCost : ℕ → ℕ → ℕ
  oracleStepC_cost : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT),
    (oracleStepC I₀ qBound qep gsE qE).cost ≤
      gsE.cost + qE.cost + oracleStepCost qBound qep
  oracleStepC_queries : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (w : (stepAIface ℓ I₀).Tag → ℕ),
    (oracleStepC I₀ qBound qep gsE qE).queries w (fun _ => 0) = 0
  oracleStepC_eval : ∀ {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (sq : (CryptoGames.SM.spec (GhostState Bytes) (Plain ℓ) (BitVec 512) Bytes).Domain),
    SmReachBounded C K qBound gs →
    gsE.eval ρ = e2eGsEnc gs →
    qE.eval ρ = smQenc sq →
    (oracleStepC I₀ qBound qep gsE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (smRenc (stT := GhostStT) id sq out.1, e2eGsEnc out.2)) <$>
          ((CryptoGames.SM.oracleImplR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq).run gs))

theorem DrSessionSimIface.oracleStepC_eval_qdec {ℓ : ℕ} {Pt : Type}
    {P : SignalPqxdh.Primitives} {C : Crypto} {K : MlKem}
    {decT : PublicKey → Option Pt} {encT : Pt → PublicKey}
    (sim : DrSessionSimIface ℓ P C K decT encT)
    {ι : Type} {T : OracleSpec ι} (I₀ : Iface (e2eSig ℓ) T)
    (qBound qep : ℕ) {Γ : List (Ty (e2eSig ℓ))}
    (gsE : Expr (e2eOps ℓ P C K decT encT) Γ (e2eGsTy ℓ))
    (qE : Expr (e2eOps ℓ P C K decT encT) Γ smQT)
    (ρ : Env Γ)
    (idA idB : IdentityKey) (spkCoins : BitVec 256)
    (gs : GameState (GhostState Bytes) (Plain ℓ) Bytes)
    (hReach : SmReachBounded C K qBound gs)
    (hgsE : gsE.eval ρ = e2eGsEnc gs) :
    let sq := smQdec (ℓ := ℓ) (St := GhostState Bytes) (qE.eval ρ)
    (sim.oracleStepC I₀ qBound qep gsE qE).eval ρ =
      (stepAIface ℓ I₀).liftP
        ((fun out => (smRenc (stT := GhostStT) id sq out.1, e2eGsEnc out.2)) <$>
          ((CryptoGames.SM.oracleImplR
            (sessionSchemeFixedSpk
              (paramsIdsWithSpqr C (spqrV1SessionUniformCoins C.F K) idA idB) ℓ spkCoins)
            (2 + 1) qep (configRefuseEarlyBobCorr decT encT) sq).run gs)) :=
  sim.oracleStepC_eval I₀ qBound qep gsE qE ρ idA idB spkCoins gs
    (smQdec (ℓ := ℓ) (St := GhostState Bytes) (qE.eval ρ))
    hReach hgsE (smQenc_smQdec (qE.eval ρ)).symm

end Computational.Proofs.E2E.Dsl.M2Interfaces
