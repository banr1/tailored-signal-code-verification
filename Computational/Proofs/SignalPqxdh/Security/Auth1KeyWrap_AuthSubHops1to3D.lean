/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
public import VCVio.EvalDist.Monad.Basic
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyHybrid
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_AuthSubHops1to3
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_Collisions
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_CollisionsB
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrap_TwoKeyAndAuthStatements
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyWrapBase
public import Computational.Proofs.SignalPqxdh.Security.Auth1KeyShallowSims

/-!
# One-Key Creation-Order `PrfChainKey` Slot Simulation

Defines creation-order `PrfChainKey` hybrid steps over `pqxdhAuthImpl1KeyG` and relates them to
primitive-oracle simulation and `SlotM` execution.
-/

@[expose] public section

set_option autoImplicit false

open OracleSpec OracleComp MeasureTheory ENNReal BigOperators

namespace SignalPqxdh.Security

open SignalPqxdh
open _root_.Proofs.SignalPqxdh.Security

namespace AuthSubHops1to3

theorem simulateQ_stepAuthOtherPrim1Key (S : Setup) (P : Primitives) (q : AuthQuery S)
    (hst : AuthHybridStateFixed S)
    (hNotSend : ¬isAuthSendQuery (Sum.inr q))
    (hNotRecv : ¬isAuthRecvQuery (Sum.inr q)) :
    simulateQ (primBaseImpl P) (stepAuthOtherPrim1Key S q (cacheAuthAdvKeysFixed P hst)) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$> authCkOtherStep1Key S P q hst := by
  have hIfPos {α : Type} {c : Prop} [Decidable c] (hc : c) (a b : α) :
      (if c then a else b) = a := by split_ifs; rfl
  have hIfNeg {α : Type} {c : Prop} [Decidable c] (hc : ¬c) (a b : α) :
      (if c then a else b) = b := by split_ifs; rfl
  unfold stepAuthOtherPrim1Key authCkOtherStep1Key
  dsimp only
  have hWonEq : (cacheAuthAdvKeysFixed P hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  by_cases hWon : hst.base.hasWonAuth = true
  · rw [hIfPos (hWonEq.trans hWon), hIfPos hWon]
    simp [Prod.map]
  rw [hIfNeg (hWonEq ▸ hWon), hIfNeg hWon]
  cases q with
  | sendOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | sendNoOPK _ _ _ _ _ => exact False.elim (hNotSend trivial)
  | recvOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | recvNoOPK _ _ _ _ => exact False.elim (hNotRecv trivial)
  | initPrin u =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, pure_bind, bind_assoc,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
        map_bind, map_pure, Prod.map]
      rfl
  | corruptIK u =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) <;>
      simp [StateT.run_set, StateT.run_pure, Prod.map]
  | genSPK u j =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [StateT.run_pure, Prod.map]
      | some p =>
        rcases p with ⟨_, uEntry⟩
        dsimp only
        simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_sampleKemKeyGenPrim,
          simulateQ_pure, pure_bind, bind_assoc, StateT.run_bind, StateT.run_monadLift,
          monadLift_self, StateT.run_set, StateT.run_pure, map_bind, map_pure, Prod.map]
        rfl
  | genOPK u j o =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · simp only [simulateQ_bind, simulateQ_embedUnif, simulateQ_pure, pure_bind, bind_assoc,
        StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure,
        map_bind, map_pure, Prod.map]
      rfl
  | registerKey sk =>
    unfold pqxdhAuthImpl1KeyG registerAdvKey cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [StateT.run_bind, StateT.run_get, pure_bind]
    split
    · simp [StateT.run_pure, Prod.map]
    · rfl
  | roQuery secrets =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]
    rfl
  | roRootQuery rk dh =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte,
      simulateQ_bind, simulateQ_embedUnif, evalRootKdfOrRo_true_eq_pure, simulateQ_pure,
      StateT.run_bind, StateT.run_get, StateT.run_monadLift, monadLift_self,
      StateT.run_set, StateT.run_pure, pure_bind, bind_assoc, map_bind, map_pure, Prod.map]
    rfl
  | revealDhSecrets =>
    unfold pqxdhAuthImpl1KeyG cacheAuthAdvKeysFixed cacheAuthAdvKeys
    dsimp only
    rfl

def projSlots0 {S : Setup} (hst : AuthHybridStateFixed S) : AuthHybridStateFixed S :=
  { hst with slots := {} }

def authCkSlotsSendWith (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.noneResp, hst)
  else if m0.length != m1.length then
    pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then
    pure (.noneResp, hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← sampleScalar32
          let kemCoins ← sampleCoins32
          let ephASk ← sampleScalar32
          let spqrCoins ← sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov :=
                checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool :=
                isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← sampleDRKey96
                let rk1 ← sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let (sIdx, slots') := hst.slots.allocSend sid
                  let p ← sampAt sIdx
                  pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain { hst with slots := slots' } p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount,
                                slots := hst.slots })

def authCkSlotsStepWith1Key (S : Setup) (P : Primitives) (sampAt : Nat → ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSlotsSendWith S P sampAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSlotsSendWith S P sampAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkRecvWithSlots S P sampAt msg (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep1Key S P qOther hst

noncomputable def authCkSlotsPreSampleRun1Key (S : Setup) (P : Primitives) (idx : Nat)
    (p : Bytes × Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith1Key S P (fun s => if s == idx then pure p else sampCkPair P (s < idx)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

noncomputable def authCkSlotsCutoffExp1Key (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let stepImpl : QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
    fun q => StateT.mk (fun hst =>
      authCkSlotsStepWith1Key S P (fun s => sampCkPair P (s < cutoff)) q hst)
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + stepImpl
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState

theorem map_projSlots0_authCkSlotsSendWith (S : Setup) (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hSampEq : ¬hst.toAuthHybridState.base.usedSendSessions.contains sid →
      sampAt1 (hst.slots.allocSend sid).1 = sampAt2 (sessionSlotIndex sid)) :
    Prod.map id projSlots0 <$> authCkSlotsSendWith S P sampAt1 sid u bundle m0 m1 hst =
      authCkSendWith S P sampAt2 sid u bundle m0 m1 (projSlots0 hst) := by
  unfold authCkSlotsSendWith authCkSendWith projSlots0
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases (m0.length != m1.length)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      by_cases hUsed : hst.toAuthHybridState.base.usedSendSessions.contains sid = true
      · simp only [hUsed, ↓reduceIte]; rw [map_pure]; rfl
      · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
        have hSE := hSampEq hUsed
        cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none => dsimp only; rw [map_pure]; rfl
        | some uPair =>
          rcases uPair with ⟨_, uEntry⟩
          dsimp only
          cases ((!match findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
            | some (_, pEntry) => !pEntry.corrupted
            | none => false) && (m0 != m1))
          · simp only [Bool.false_eq_true, ↓reduceIte]
            cases (!koskBundleOk P hst.toAuthHybridState.base.principals
              hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
              hst.toAuthHybridState.base.advKeys bundle)
            · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              cases (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                  (encodeEC bundle.spkB) bundle.spkSig &&
                P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                  (encodeKEM bundle.pqspkB) bundle.pqspkSig))
              · simp only [Bool.false_eq_true, ↓reduceIte]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => dsimp only; rw [map_pure]; rfl
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  cases ((match findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
                    | some (_, pEntry) => !pEntry.corrupted
                    | none => false) ||
                    ((findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB).isSome &&
                      checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle &&
                      (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles
                        hst.toAuthHybridState.base.opkEntries bundle).2.2))
                  · simp only [Bool.false_eq_true, ↓reduceIte, map_bind]
                    congr 1; funext ⟨drKey, roCache'⟩
                    congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => dsimp only; rw [map_pure]; rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                      dsimp only; rw [map_pure]; rfl
                  · simp only [↓reduceIte, map_bind]
                    congr 1; funext drKey; congr 1; funext rk1
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => dsimp only; rw [map_pure]; rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                      dsimp only
                      rw [hSE, map_bind]
                      congr 1
              · simp only [↓reduceIte]; rw [map_pure]; try rfl
            · simp only [↓reduceIte]; rw [map_pure]; try rfl
          · simp only [↓reduceIte]; rw [map_pure]; try rfl
    · simp only [↓reduceIte]; rw [map_pure]; try rfl
  · simp only [↓reduceIte]; rw [map_pure]; try rfl

theorem map_projSlots0_authCkSlotsRecvWith (S : Setup) (P : Primitives)
    (sampAt1 sampAt2 : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S)
    (hSampEq : sampAt1 (hst.slots.allocRecv hst.recvCount).1 =
      sampAt2 (S.N_send_tot + hst.recvCount)) :
    Prod.map id projSlots0 <$> authCkRecvWithSlots S P sampAt1 msg prep? hst =
      authCkRecvWith S P sampAt2 msg prep? (projSlots0 hst) := by
  unfold authCkRecvWithSlots authCkRecvWith projSlots0
  cases prep? with
  | none => simp [Prod.map]
  | some prep =>
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
        · simp only [map_bind]
          congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp [Prod.map]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩
            dsimp only
            rw [hSampEq]
            simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
      | none =>
        dsimp only [map_bind]
        simp only [map_bind]
        congr 1; funext drKey; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp [Prod.map]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩
          dsimp only
          rw [hSampEq]
          simp [Prod.map, finishAuthRecvCkSlots, finishAuthRecvCk]
    · simp only [map_bind]
      congr 1; funext ⟨drKey, roCache'⟩
      congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp [Prod.map]
      | some pqr =>
        rcases pqr with ⟨_, spqrSalt?⟩
        simp [Prod.map]

theorem map_projSlots0_authCkOtherStep1Key (S : Setup) (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    Prod.map id projSlots0 <$> authCkOtherStep1Key S P q hst =
      authCkOtherStep1Key S P q (projSlots0 hst) := by
  unfold authCkOtherStep1Key projSlots0
  dsimp only
  split
  · simp [Prod.map]
  · simp [Prod.map, map_eq_bind_pure_comp]

theorem simulateQ_authCkSlotsSendWithPrim (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    simulateQ (primBaseImpl P) (authCkSendWithPrim S sampAt sid u bundle m0 m1 hst) =
      authCkSlotsSendWith S P sampAtPure sid u bundle m0 m1 hst := by
  unfold authCkSendWithPrim authCkSlotsSendWith
  dsimp only
  by_cases hWon : hst.base.hasWonAuth = true
  · simp only [hWon, ↓reduceIte]; rfl
  simp only [Bool.not_eq_true] at hWon
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  by_cases hLen : (m0.length != m1.length) = true
  · simp only [hLen, ↓reduceIte]; rfl
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (hst.toAuthHybridState.base.usedSendSessions.contains sid) = true
    · simp only [hUsed, ↓reduceIte]; rfl
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => rfl
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        rw [simulateQ_bind,
            simulateQ_findHonestPrincipalPrim S P
              hst.toAuthHybridState.base.principals bundle.ikB hPrin,
            pure_bind]
        have hProv2 := (checkBundleProvenanceExact_spk_pqspk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2
        cases hpeer : findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
        | none =>
          dsimp only
          by_cases hCh : (m0 != m1) = true
          · simp only [Bool.not_false, Bool.true_and, hCh, ↓reduceIte]; rfl
          · simp only [Bool.not_false, Bool.true_and, hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind,
                simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv, pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp only [hKosk, ↓reduceIte]; rfl
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify
                  (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte]; rfl
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P
                        hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind]
                  simp only [Option.isSome, Bool.false_and, Bool.or_false,
                    Bool.false_eq_true, ↓reduceIte]
                  rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                  have hDh4 : simulateQ (primBaseImpl P)
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                      pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                    cases bundle.opkB? with
                    | none => rfl
                    | some opkPair =>
                      rcases opkPair with ⟨_, opkPk⟩
                      simp only [simulateQ_bind, simulateQ_pure]; rfl
                  rw [simulateQ_bind, hDh4, pure_bind]
                  simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                  congr 1; funext ⟨drKey, roCache'⟩
                  rw [simulateQ_primQ_x25519, pure_bind]; simp only [evalRootKdfOrRo_true_eq_pure]
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                      simulateQ_primQ_chainKdfNext, pure_bind,
                      simulateQ_primQ_spqrInitSend, pure_bind]
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => rfl
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                        simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                        simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1
                          ekASk _ ss kemCt
                          ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg
                          _ _ _ _ roCache' rootRoCache'
                          hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                    rfl
        | some pPair =>
          rcases pPair with ⟨pIdx, pEntry⟩; dsimp only
          rw [hpeer] at hProv2
          by_cases hCh : (!!pEntry.corrupted && (m0 != m1)) = true
          · simp only [hCh, ↓reduceIte]; rfl
          · simp only [hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind,
                simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv, pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp only [hKosk, ↓reduceIte]; rfl
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif]
              congr 1; funext ekASk; congr 1; funext kemCoins
              congr 1; funext ephASk; congr 1; funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify
                  (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp only [hSig, ↓reduceIte]; rfl
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => rfl
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P
                        hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind, ← hProv2]
                  split
                  · simp only [simulateQ_bind, simulateQ_embedUnif]
                    congr 1; funext drKey; congr 1; funext rk1
                    rw [simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, hSamp]
                      congr 1; funext p
                      exact simulateQ_finishAuthSendCkSlotsPrim S P sid uEntry
                        (some (pIdx, pEntry)) bundle m0 m1 ekASk _ ss kemCt ephASk _
                        drKey rk1 spqrSalt? pqRatchetMsg _ { hst with slots := _ } p
                        hPrin hSpk hOpk
                  · rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                    have hDh4 : simulateQ (primBaseImpl P)
                        (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                          let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                        pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                      cases bundle.opkB? with
                      | none => rfl
                      | some opkPair =>
                        rcases opkPair with ⟨_, opkPk⟩
                        simp only [simulateQ_bind, simulateQ_pure]; rfl
                    rw [simulateQ_bind, hDh4, pure_bind]
                    simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure]
                    congr 1; funext ⟨drKey, roCache'⟩
                    rw [simulateQ_primQ_x25519, pure_bind]; simp only [evalRootKdfOrRo_true_eq_pure]
                    congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                        simulateQ_primQ_chainKdfNext, pure_bind,
                        simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => rfl
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                          simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                          simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1
                            ekASk _ ss kemCt
                            ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg
                            _ _ _ _ roCache' rootRoCache'
                            hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                      rfl

theorem authCkSlotsSendWith_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    authCkSlotsSendWith S P sampAtPure sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$>
        authCkSlotsSendWith S P sampAtPure sid u bundle m0 m1 hst := by
  unfold authCkSlotsSendWith
  dsimp only
  have hWonEq : (cacheAuthAdvKeysFixed P hst).base.hasWonAuth = hst.base.hasWonAuth := rfl
  rw [hWonEq]
  by_cases hWon : hst.base.hasWonAuth = true
  · simp [hWon, Prod.map]
  simp only [hWon, Bool.false_eq_true, ↓reduceIte]
  unfold cacheAuthAdvKeysFixed cacheAuthAdvKeys
  dsimp only
  rw [koskBundleOk_cacheAuthAdvKeys]
  split; · simp [Prod.map]
  split; · simp [Prod.map]
  split
  · simp [Prod.map]
  · split
    · simp [Prod.map]
    · split
      · simp [Prod.map]
      · simp only [map_bind]
        congr 1; funext ekASk; congr 1; funext kemCoins
        congr 1; funext ephASk; congr 1; funext spqrCoins
        split
        · simp [Prod.map]
        · cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp [Prod.map]
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            dsimp only
            split
            · simp only [map_bind]
              congr 1; funext drKey
              congr 1; funext rk1
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp only [map_bind, map_pure]
                congr 1
            · simp only [map_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [Prod.map]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp [Prod.map, finishAuthHybridSend]

theorem simulateQ_authCkSlotsStepWithPrim1Key (S : Setup) (P : Primitives)
    (sampAt : Nat → OracleComp PrimBaseSpec (Bytes × Bytes))
    (sampAtPure : Nat → ProbComp (Bytes × Bytes))
    (hSamp : ∀ s, simulateQ (primBaseImpl P) (sampAt s) = sampAtPure s)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hV : ValidAuthHybrid S P hst) :
    simulateQ (primBaseImpl P) (authCkStepWithPrim1Key S sampAt q (cacheAuthAdvKeysFixed P hst)) =
      Prod.map id (cacheAuthAdvKeysFixed P) <$> authCkSlotsStepWith1Key S P sampAtPure q hst := by
  have hVC : ValidAuthHybrid S P (cacheAuthAdvKeysFixed P hst) :=
    (validAuthHybrid_cacheAuthAdvKeysFixed P hst).mpr hV
  have hAdv : ValidAdvKeysPow8 P (cacheAuthAdvKeysFixed P hst).toAuthHybridState.base.advKeys :=
    validAdvKeysPow8_cacheAuthAdvKeys P hst.toAuthHybridState
  cases q with
  | sendOPK u i bundle m0 m1 =>
    unfold authCkStepWithPrim1Key authCkSlotsStepWith1Key; dsimp only
    split
    · simp [Prod.map]
    · rw [simulateQ_authCkSlotsSendWithPrim S P sampAt sampAtPure hSamp (.sendOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authCkSlotsSendWith_cacheAuthAdvKeysFixed]
  | sendNoOPK u i bundle m0 m1 =>
    unfold authCkStepWithPrim1Key authCkSlotsStepWith1Key; dsimp only
    split
    · simp [Prod.map]
    · rw [simulateQ_authCkSlotsSendWithPrim S P sampAt sampAtPure hSamp (.sendNoOPK u i) u bundle m0 m1
            (cacheAuthAdvKeysFixed P hst) hVC.principals_le hVC.spkBundles_le hVC.opkEntries_le hAdv,
          authCkSlotsSendWith_cacheAuthAdvKeysFixed]
  | recvOPK k j o msg =>
    unfold authCkStepWithPrim1Key authCkSlotsStepWith1Key; dsimp only
    rw [simulateQ_bind,
        simulateQ_prepareAuthHybridRecvOPKPrim S P k j o msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState) =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hSome
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvOPKPure_finishTag_base P k j o msg _ prep hSome
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    change simulateQ (primBaseImpl P)
        (authCkRecvWithPrim S sampAt msg
          (prepareAuthHybridRecvOPKPure P k j o msg (cacheAuthAdvKeys P hst.toAuthHybridState))
          (cacheAuthAdvKeysFixed P hst)) = _
    rw [simulateQ_authCkRecvWithSlotsPrim S P sampAt sampAtPure hSamp msg _ _ hPrep,
        prepareAuthHybridRecvOPKPure_cacheAuthAdvKeys,
        authCkRecvWithSlots_cacheAuthAdvKeysFixed,
        ← prepareAuthHybridRecvOPKPure_map_toPure]
  | recvNoOPK k j l msg =>
    unfold authCkStepWithPrim1Key authCkSlotsStepWith1Key; dsimp only
    rw [simulateQ_bind,
        simulateQ_prepareAuthHybridRecvNoOPKPrim S P k j l msg
          (cacheAuthAdvKeysFixed P hst).toAuthHybridState
          hVC.principals_le hVC.idealSessions_le hAdv,
        pure_bind]
    have hPrep : ∀ prep,
        prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState) =
          some prep →
        prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh ∧
        prep.finishTag.hstDec.base.principals.length ≤ S.N_dh := by
      intro prep hSome
      obtain ⟨hTag, hBase⟩ := prepareAuthHybridRecvNoOPKPure_finishTag_base P k j l msg _ prep hSome
      rw [hTag, hBase]
      exact ⟨hVC.sentOPKEvents_le, hVC.sentNoOPKEvents_le, hVC.principals_le⟩
    change simulateQ (primBaseImpl P)
        (authCkRecvWithPrim S sampAt msg
          (prepareAuthHybridRecvNoOPKPure P k j l msg (cacheAuthAdvKeys P hst.toAuthHybridState))
          (cacheAuthAdvKeysFixed P hst)) = _
    rw [simulateQ_authCkRecvWithSlotsPrim S P sampAt sampAtPure hSamp msg _ _ hPrep,
        prepareAuthHybridRecvNoOPKPure_cacheAuthAdvKeys,
        authCkRecvWithSlots_cacheAuthAdvKeysFixed,
        ← prepareAuthHybridRecvNoOPKPure_map_toPure]
  | initPrin u => exact simulateQ_stepAuthOtherPrim1Key S P (.initPrin u) hst (fun h => nomatch h) (fun h => nomatch h)
  | corruptIK u => exact simulateQ_stepAuthOtherPrim1Key S P (.corruptIK u) hst (fun h => nomatch h) (fun h => nomatch h)
  | genSPK u j => exact simulateQ_stepAuthOtherPrim1Key S P (.genSPK u j) hst (fun h => nomatch h) (fun h => nomatch h)
  | genOPK u j o => exact simulateQ_stepAuthOtherPrim1Key S P (.genOPK u j o) hst (fun h => nomatch h) (fun h => nomatch h)
  | registerKey sk => exact simulateQ_stepAuthOtherPrim1Key S P (.registerKey sk) hst (fun h => nomatch h) (fun h => nomatch h)
  | roQuery secrets => exact simulateQ_stepAuthOtherPrim1Key S P (.roQuery secrets) hst (fun h => nomatch h) (fun h => nomatch h)
  | roRootQuery rk dh => exact simulateQ_stepAuthOtherPrim1Key S P (.roRootQuery rk dh) hst (fun h => nomatch h) (fun h => nomatch h)
  | revealDhSecrets => exact simulateQ_stepAuthOtherPrim1Key S P .revealDhSecrets hst (fun h => nomatch h) (fun h => nomatch h)

structure CkSlotsWf {S : Setup} (hst : AuthHybridStateFixed S) : Prop where
  send_fresh : ∀ sid : SessionId S,
    hst.toAuthHybridState.base.usedSendSessions.contains sid = false →
    hst.slots.lookupSend sid = none
  recv_fresh : ∀ rc, hst.recvCount ≤ rc → hst.slots.recvTbl rc = none

theorem ckSlotsWf_empty (S : Setup) (secb : Bool) :
    CkSlotsWf (AuthHybridStateFixed.empty S secb) :=
  ⟨fun sid _ => by cases sid <;> rfl, fun _ _ => rfl⟩

def authCkSlotsSendSlot (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then pure (.noneResp, hst)
  else if m0.length != m1.length then pure (.noneResp, hst)
  else if st.usedSendSessions.contains sid then pure (.noneResp, hst)
  else
    match st.principals.find? (fun (i, _) => i == u.val) with
    | none => pure (.noneResp, hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with | some (_, pEntry) => !pEntry.corrupted | none => false
      if !isFreshPeer && m0 != m1 then pure (.noneResp, hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.noneResp, hst)
        else
          let ekASk ← liftM sampleScalar32
          let kemCoins ← liftM sampleCoins32
          let ephASk ← liftM sampleScalar32
          let spqrCoins ← liftM sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.noneResp, hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.noneResp, hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov := checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal && prov.2.2)
              if isIdealSend then
                let drKey ← liftM sampleDRKey96
                let rk1 ← liftM sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let (sIdx, slots') := hst.slots.allocSend sid
                  let p ← getCkAtSlot idx samp P sIdx
                  pure (finishAuthSendCkSlots P sid uEntry peerPrincipal? bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
                    pqRatchetMsg msgPlain { hst with slots := slots' } p)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache secrets)
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ←
                  liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey dhRatchet)
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.noneResp, hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') :=
                    finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (resp, { toAuthHybridState := hst', recvCount := hst.recvCount, slots := hst.slots })

def authCkSlotsRecvSlot (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            pure (finishAuthRecvCkSlots P msg prep s.drKey s.rk1 spqrSalt? recvCount'
              (s.mkSeed, s.ck1_1) hst.slots)
        else
          let rk1 ← liftM sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
          | some (_pqrStB, spqrSalt?) =>
            let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
            let p ← getCkAtSlot idx samp P rSlot
            pure (finishAuthRecvCkSlots P msg prep s.drKey rk1 spqrSalt? recvCount' p slots')
      | none =>
        let drKey ← liftM sampleDRKey96
        let rk1 ← liftM sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
        | some (_pqrStB, spqrSalt?) =>
          let (rSlot, slots') := hst.slots.allocRecv hst.recvCount
          let p ← getCkAtSlot idx samp P rSlot
          pure (finishAuthRecvCkSlots P msg prep drKey rk1 spqrSalt? recvCount' p slots')
    else
      let (drKey, roCache') ← liftM (evalHkdfOrRo true P st.roCache prep.secrets)
      let ((rk1, ck1_0), rootRoCache') ←
        liftM (evalRootKdfOrRo true P st.rootRoCache drKey.rootKey prep.dhRatchet)
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount', slots := hst.slots })

def authCkSlotsStepSlot1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM (Bytes × Bytes) ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authCkSlotsSendSlot S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authCkSlotsSendSlot S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authCkSlotsRecvSlot S P idx samp msg (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authCkSlotsRecvSlot S P idx samp msg (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep1Key S P qOther hst)

theorem authCkSlotsSendSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkSlotsSendSlot S P idx samp sid u bundle m0 m1 hst) := by
  unfold authCkSlotsSendSlot; dsimp only
  repeat (first
    | with_reducible apply SlotM.SlotComp.pure
    | with_reducible apply SlotM.SlotComp.liftComp
    | (with_reducible apply SlotM.SlotComp.liftComp_bind; intro _)
    | (with_reducible apply SlotM.SlotComp.getCkAtSlot_bind; intro _)
    | split)

theorem authCkSlotsRecvSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkSlotsRecvSlot S P idx samp msg prep? hst) := by
  unfold authCkSlotsRecvSlot; dsimp only
  repeat (first
    | with_reducible apply SlotM.SlotComp.pure
    | with_reducible apply SlotM.SlotComp.liftComp
    | (with_reducible apply SlotM.SlotComp.liftComp_bind; intro _)
    | (with_reducible apply SlotM.SlotComp.getCkAtSlot_bind; intro _)
    | split)

theorem authCkSlotsStepSlot_slotComp1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp samp (authCkSlotsStepSlot1Key S P idx samp q hst) := by
  cases q <;> unfold authCkSlotsStepSlot1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split; · exact SlotM.SlotComp.pure samp _
    exact authCkSlotsSendSlot_slotComp S P idx samp (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split; · exact SlotM.SlotComp.pure samp _
    exact authCkSlotsSendSlot_slotComp S P idx samp (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg => exact authCkSlotsRecvSlot_slotComp S P idx samp msg _ hst
  case recvNoOPK k j l msg => exact authCkSlotsRecvSlot_slotComp S P idx samp msg _ hst
  all_goals exact SlotM.SlotComp.liftComp samp _

private theorem authCkSlotsRecvSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authCkSlotsRecvSlot S P idx samp msg prep? hst).run' (some k) =
      authCkRecvWithSlots S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx))
        msg prep? hst := by
  unfold authCkSlotsRecvSlot authCkRecvWithSlots
  cases prep? with
  | none => dsimp only; rw [SlotM.run'_pure]
  | some prep =>
    dsimp only
    cases (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨drKey, roCache'⟩
      rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => dsimp only; rw [SlotM.run'_pure]
      | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [SlotM.run'_pure]
    · simp only [↓reduceIte]
      cases prep.matchedSess? with
      | none =>
        dsimp only
        rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => dsimp only; rw [SlotM.run'_pure]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
          rw [run'_getCkAtSlot_bind_pure_some]
      | some s =>
        dsimp only
        cases prep.sameEph
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; rw [SlotM.run'_pure]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
            rw [run'_getCkAtSlot_bind_pure_some]
        · simp only [↓reduceIte]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; rw [SlotM.run'_pure]
          | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [SlotM.run'_pure]

private theorem authCkSlotsRecvSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authCkSlotsRecvSlot S P idx (sampCkPair P (!b)) msg prep? hst).run' none =
      authCkRecvWithSlots S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        msg prep? hst := by
  unfold authCkSlotsRecvSlot authCkRecvWithSlots
  cases prep? with
  | none => dsimp only; rw [SlotM.run'_pure]
  | some prep =>
    dsimp only
    cases (prep.matchedSess?.isSome || prep.isUncorruptedHonestSender)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨drKey, roCache'⟩
      rw [SlotM.run'_liftComp_bind]; congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => dsimp only; rw [SlotM.run'_pure]
      | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [SlotM.run'_pure]
    · simp only [↓reduceIte]
      cases prep.matchedSess? with
      | none =>
        dsimp only
        rw [SlotM.run'_liftComp_bind]; congr 1; funext drKey
        rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => dsimp only; rw [SlotM.run'_pure]
        | some pqr =>
          rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
          rw [run'_getCkAtSlot_bind_pure_none]
      | some s =>
        dsimp only
        cases prep.sameEph
        · simp only [Bool.false_eq_true, ↓reduceIte]
          rw [SlotM.run'_liftComp_bind]; congr 1; funext rk1
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; rw [SlotM.run'_pure]
          | some pqr =>
            rcases pqr with ⟨_, spqrSalt?⟩; dsimp only
            rw [run'_getCkAtSlot_bind_pure_none]
        · simp only [↓reduceIte]
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => dsimp only; rw [SlotM.run'_pure]
          | some pqr => rcases pqr with ⟨_, spqrSalt?⟩; dsimp only; rw [SlotM.run'_pure]

set_option maxHeartbeats 400000 in
theorem authCkSlotsStepSlot_run'_some1Key (S : Setup) (P : Primitives) (idx : Nat)
    (samp : ProbComp (Bytes × Bytes)) (k : Bytes × Bytes)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkSlotsStepSlot1Key S P idx samp q hst).run' (some k) =
      authCkSlotsStepWith1Key S P
        (fun slotIdx => if slotIdx == idx then pure k else sampCkPair P (slotIdx < idx)) q hst := by
  cases q <;> unfold authCkSlotsStepSlot1Key authCkSlotsStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split; · rw [SlotM.run'_pure]
    unfold authCkSlotsSendSlot authCkSlotsSendWith; dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;>
      cases (m0.length != m1.length) <;>
      cases hst.toAuthHybridState.base.usedSendSessions.contains (.sendOPK u i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
      | rfl | rw [SlotM.run'_pure] | rw [run'_getCkAtSlot_bind_pure_some]
      | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _) | split)
  case sendNoOPK u i bundle m0 m1 =>
    split; · rw [SlotM.run'_pure]
    unfold authCkSlotsSendSlot authCkSlotsSendWith; dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;>
      cases (m0.length != m1.length) <;>
      cases hst.toAuthHybridState.base.usedSendSessions.contains (.sendNoOPK u i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
      | rfl | rw [SlotM.run'_pure] | rw [run'_getCkAtSlot_bind_pure_some]
      | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _) | split)
  case recvOPK k' j o msg =>
    exact authCkSlotsRecvSlot_run'_some S P idx samp k msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkSlotsRecvSlot_run'_some S P idx samp k msg _ hst
  all_goals rw [SlotM.run'_liftComp]

set_option maxHeartbeats 400000 in
theorem authCkSlotsStepSlot_run'_none_eq1Key (S : Setup) (P : Primitives) (idx : Nat) (b : Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authCkSlotsStepSlot1Key S P idx (sampCkPair P (!b)) q hst).run' none =
      authCkSlotsStepWith1Key S P (fun slotIdx => sampCkPair P (slotIdx < (if b then idx else idx + 1)))
        q hst := by
  cases q <;> unfold authCkSlotsStepSlot1Key authCkSlotsStepWith1Key <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split; · rw [SlotM.run'_pure]
    unfold authCkSlotsSendSlot authCkSlotsSendWith; dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;>
      cases (m0.length != m1.length) <;>
      cases hst.toAuthHybridState.base.usedSendSessions.contains (.sendOPK u i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
      | rfl | rw [SlotM.run'_pure] | rw [run'_getCkAtSlot_bind_pure_none]
      | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _) | split)
  case sendNoOPK u i bundle m0 m1 =>
    split; · rw [SlotM.run'_pure]
    unfold authCkSlotsSendSlot authCkSlotsSendWith; dsimp only
    cases hst.toAuthHybridState.base.hasWonAuth <;>
      cases (m0.length != m1.length) <;>
      cases hst.toAuthHybridState.base.usedSendSessions.contains (.sendNoOPK u i) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;> repeat (first
      | rfl | rw [SlotM.run'_pure] | rw [run'_getCkAtSlot_bind_pure_none]
      | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _) | split)
  case recvOPK k' j o msg =>
    exact authCkSlotsRecvSlot_run'_none S P idx b msg _ hst
  case recvNoOPK k' j l msg =>
    exact authCkSlotsRecvSlot_run'_none S P idx b msg _ hst
  all_goals rw [SlotM.run'_liftComp]

end AuthSubHops1to3

end SignalPqxdh.Security
