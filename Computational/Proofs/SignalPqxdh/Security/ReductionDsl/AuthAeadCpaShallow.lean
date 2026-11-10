/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthAeadCpa
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthPrfSharedEval

/-!
# Shallow Encodings and Steps for the `Auth` `AeadIndCpa` Reduction

Defines value encodings, mid-level shallow step functions, and state/pause invariants for
evaluating `aeadCpaRedProg`.
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security.ReductionDsl.AuthAead

open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh
open SignalPqxdh.LegacyCosted
open SignalPqxdh.Security
open SignalPqxdh.Security.AuthSubHops1to3
open SignalPqxdh.Security.ReductionDsl SignalPqxdh.Security.ReductionDsl.AuthPrf
open OracleSpec OracleComp

/-! ## Encodings -/

def cpaPayloadToVal {S : Setup} (p : AuthCpaPausePayload S) : cpaPayloadTy.denote :=
  (sessionIdToVal p.sid, (principalEntryToVal p.uEntry,
    (p.peerPrin?.map (Prod.map id principalEntryToVal), (preKeyBundleToVal p.bundle,
      ((p.m0, p.m1), ((p.ekASk, (p.ekAPk, (p.ss, (p.kemCt, (p.ephASk, p.ephAPk))))),
        (drKeyToVal p.drKey, ((p.rk1, (p.ck1_0, (p.mkSeed, p.ck1_1))),
          (p.spqrSalt?, (p.pqRatchetMsg, (p.ad, ((p.spkHon, (p.opkHon, p.pqspkHon)),
            (p.roCache.map (Prod.map id drKeyToVal), p.rootRoCache)))))))))))))

def cpaStToVal {S : Setup} (idx : Nat) (hst : AuthHybridStateFixed S) : cpaStTy.denote :=
  (idx, (0, authHybridStateFixedToVal hst))

abbrev CpaSlotSt (S : Setup) := Nat × AuthHybridStateFixed S

def cpaSlotStToVal {S : Setup} (idx : Nat) (shst : CpaSlotSt S) : cpaStTy.denote :=
  (idx, (shst.1, authHybridStateFixedToVal shst.2))

abbrev CpaSlotSendRes (S : Setup) :=
  (AuthResponse × CpaSlotSt S) ⊕
    (Bytes × Bytes × Bytes × AuthCpaPausePayload S × CpaSlotSt S)

def cpaSlotSendResToVal {S : Setup} : CpaSlotSendRes S → cpaSlotSendResTy.denote
  | .inl (r, sh) => .inl (authRespToVal r, (sh.1, authHybridStateFixedToVal sh.2))
  | .inr (ad, m0, m1, p, sh) =>
    .inr ((ad, (m0, m1)), (cpaPayloadToVal p, (sh.1, authHybridStateFixedToVal sh.2)))

abbrev CpaSendRes (S : Setup) :=
  (AuthResponse × AuthHybridStateFixed S) ⊕
    (Bytes × Bytes × Bytes × AuthCpaPausePayload S × AuthHybridStateFixed S)

def cpaSendResToVal {S : Setup} : CpaSendRes S → cpaSendResTy.denote
  | .inl (r, h) => .inl (authRespToVal r, authHybridStateFixedToVal h)
  | .inr (ad, m0, m1, p, h) =>
    .inr ((ad, (m0, m1)), (cpaPayloadToVal p, authHybridStateFixedToVal h))

/-! ## Shallow send and mid-level steps -/

def cpaSendShOpk (S : Setup) (allowPause : Bool) (idx : Nat) (u : Fin S.N_id)
    (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : OracleComp PrimBaseSpec (CpaSendRes S) :=
  if b.opkB?.isNone then pure (.inl (.noneResp, hst))
  else tryPauseAuthCpaSendFixedPrim allowPause idx S (.sendOPK u i) u b m0 m1 hst

def cpaSendShNoOpk (S : Setup) (allowPause : Bool) (idx : Nat) (u : Fin S.N_id)
    (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : OracleComp PrimBaseSpec (CpaSendRes S) :=
  if b.opkB?.isSome then pure (.inl (.noneResp, hst))
  else tryPauseAuthCpaSendFixedPrim allowPause idx S (.sendNoOPK u i) u b m0 m1 hst

def cpaSendResToStep {S : Setup} : CpaSendRes S →
    (AuthResponse × AuthHybridStateFixed S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))
  | .inl x => .inl x
  | .inr (ad, m0, m1, p, h) => .inr ((ad, m0, m1), (p, h))

def stepMidCpa (S : Setup) (idx : Nat) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    OracleComp PrimBaseSpec
      (((authSpec S).Range q × AuthHybridStateFixed S) ⊕
        ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × AuthHybridStateFixed S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSendResToStep <$> cpaSendShOpk S true idx u i b m0 m1 hst
  | .sendNoOPK u i b m0 m1 => cpaSendResToStep <$> cpaSendShNoOpk S true idx u i b m0 m1 hst
  | q' => Sum.inl <$> stepAuthCpaNonSendPrim S q' hst

/-! ## Invariants -/

/-- State invariant: list-length bounds and `hasWonAuth = false`. -/
structure CpaInv {S : Setup} (n : Nat) (hst : AuthHybridStateFixed S) : Prop where
  bnd : AuthListsBounded n hst
  won : hst.toAuthHybridState.base.hasWonAuth = false

theorem CpaInv.mono {S : Setup} {n m : Nat} {hst : AuthHybridStateFixed S} (h : n ≤ m)
    (hI : CpaInv n hst) : CpaInv m hst := ⟨hI.bnd.mono h, hI.won⟩

/-- Pause-leaf invariant relating the stage-1 output, message lengths, state, and RO cache bounds. -/
structure CpaPauseInv {S : Setup} (n : Nat) (c : Bytes × Bytes × Bytes)
    (p : AuthCpaPausePayload S) (hst : AuthHybridStateFixed S) : Prop where
  ad_eq    : c.1 = p.ad
  m0_eq    : c.2.1 = p.m0
  m1_eq    : c.2.2 = p.m1
  len_eq   : p.m0.length = p.m1.length
  inv      : CpaInv n hst
  ro_le    : p.roCache.length ≤ n + 1
  root_le  : p.rootRoCache.length ≤ n + 1

def CpaSendLeaf {S : Setup} (n : Nat) : CpaSendRes S → Prop
  | .inl (_, h) => CpaInv (n + 1) h
  | .inr (ad, m0, m1, p, h) => CpaPauseInv n (ad, m0, m1) p h

/-! ## Creation-order slot steps and invariants -/

inductive CpaSlotPauseRes (S : Setup) (α : Type) where
  | done (val : α) (shst : CpaSlotSt S)
  | paused (ad m0 m1 : Bytes) (payload : AuthCpaPausePayload S)
      (shst : CpaSlotSt S)
      (cont : AuthResponse → OracleComp (unifSpec + authSpec S) α)

def cpaTryPauseSendSlotPrim (allowPause : Bool) (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : CpaSlotSt S) : OracleComp PrimBaseSpec (CpaSlotSendRes S) := do
  let (ns, hst) := shst
  let st := hst.toAuthHybridState.base
  if m0.length != m1.length then return .inl (.noneResp, (ns, hst))
  if st.usedSendSessions.contains sid then return .inl (.noneResp, (ns, hst))
  let prep? ← prepAuthCpaSendFixedPrim S sid u bundle m0 m1 hst
  match prep? with
  | none => return .inl (.noneResp, (ns, hst))
  | some (isFreshPeer, isIdealSend, rawP) =>
    if isFreshPeer then
      let msgPlain := if decide (ns < cut) then m0 else m1
      let p := { rawP with msgPlain := msgPlain }
      if allowPause && (ns == cut) then
        return .inr (p.ad, m0, m1, p, (ns, hst))
      else
        let mk ← embedUnif sampleMessageKeys80
        let aeadCt ← primQ (.aeadEnc mk p.ad msgPlain)
        let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
        return .inl (resp, (ns + 1, hst'))
    else
      let p := { rawP with msgPlain := m0 }
      let mk ← (
        if isIdealSend then
          embedUnif sampleMessageKeys80
        else
          primQ (.deriveMsgKeys p.mkSeed p.spqrSalt?))
      let aeadCt ← primQ (.aeadEnc mk p.ad m0)
      let (resp, hst') := finishAuthCpaSendFixedPure false isIdealSend p aeadCt hst
      return .inl (resp, (ns, hst'))

def cpaRunSendCutoffSlotPrim (cut : Nat) (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : CpaSlotSt S) : OracleComp PrimBaseSpec (AuthResponse × CpaSlotSt S) := do
  let res ← cpaTryPauseSendSlotPrim false cut S sid u bundle m0 m1 shst
  match res with
  | .inl p => return p
  | .inr _ => return (.noneResp, shst)

def cpaStepCutoffSlotPrim (cut : Nat) (S : Setup)
    (q : AuthQuery S) (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec ((authSpec S).Range q × CpaSlotSt S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then
      return (.noneResp, shst)
    else
      cpaRunSendCutoffSlotPrim cut S (.sendOPK u i) u bundle m0 m1 shst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then
      return (.noneResp, shst)
    else
      cpaRunSendCutoffSlotPrim cut S (.sendNoOPK u i) u bundle m0 m1 shst
  | q_other => do
    let (resp, hst') ← stepAuthCpaNonSendPrim S q_other shst.2
    return (resp, (shst.1, hst'))

def cpaSendSlotShOpk (S : Setup) (allowPause : Bool) (idx : Nat) (u : Fin S.N_id)
    (i : Fin S.N_send_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : CpaSlotSt S) : OracleComp PrimBaseSpec (CpaSlotSendRes S) :=
  if b.opkB?.isNone then pure (.inl (.noneResp, shst))
  else cpaTryPauseSendSlotPrim allowPause idx S (.sendOPK u i) u b m0 m1 shst

def cpaSendSlotShNoOpk (S : Setup) (allowPause : Bool) (idx : Nat) (u : Fin S.N_id)
    (i : Fin S.N_send_no_opk) (b : PreKeyBundleInput) (m0 m1 : Bytes)
    (shst : CpaSlotSt S) : OracleComp PrimBaseSpec (CpaSlotSendRes S) :=
  if b.opkB?.isSome then pure (.inl (.noneResp, shst))
  else cpaTryPauseSendSlotPrim allowPause idx S (.sendNoOPK u i) u b m0 m1 shst

def cpaSlotSendResToStep {S : Setup} : CpaSlotSendRes S →
    (AuthResponse × CpaSlotSt S) ⊕
      ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))
  | .inl x => .inl x
  | .inr (ad, m0, m1, p, sh) => .inr ((ad, m0, m1), (p, sh))

def stepMidCpaSlot (S : Setup) (idx : Nat) (q : AuthQuery S) (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec
      (((authSpec S).Range q × CpaSlotSt S) ⊕
        ((Bytes × Bytes × Bytes) × (AuthCpaPausePayload S × CpaSlotSt S))) :=
  match q with
  | .sendOPK u i b m0 m1 => cpaSlotSendResToStep <$> cpaSendSlotShOpk S true idx u i b m0 m1 shst
  | .sendNoOPK u i b m0 m1 => cpaSlotSendResToStep <$> cpaSendSlotShNoOpk S true idx u i b m0 m1 shst
  | q' => (fun x => Sum.inl (x.1, (shst.1, x.2))) <$> stepAuthCpaNonSendPrim S q' shst.2

def cpaStepUntilChallengeSlotPrim (idx : Nat) (S : Setup) {α : Type}
    (defaultVal : α)
    (mx : OracleComp (unifSpec + authSpec S) α) (fuel : Nat) (shst : CpaSlotSt S) :
    OracleComp PrimBaseSpec (CpaSlotPauseRes S α) :=
  OracleComp.construct
    (C := fun _ => Nat → CpaSlotSt S → OracleComp PrimBaseSpec (CpaSlotPauseRes S α))
    (fun a _ s => pure (.done a s))
    (fun q cont r f s =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := PrimBaseSpec) (Sum.inl n))
        r u f s
      | Sum.inr gq =>
        match f with
        | 0 => pure (.done defaultVal s)
        | f' + 1 =>
          match gq with
          | .sendOPK u i bundle m0 m1 =>
            if bundle.opkB?.isNone then
              r .noneResp f' s
            else do
              let stepRes ← cpaTryPauseSendSlotPrim true idx S (.sendOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | .sendNoOPK u i bundle m0 m1 =>
            if bundle.opkB?.isSome then
              r .noneResp f' s
            else do
              let stepRes ←
                cpaTryPauseSendSlotPrim true idx S (.sendNoOPK u i) u bundle m0 m1 s
              match stepRes with
              | .inl (resp, s') => r resp f' s'
              | .inr (ad, m0', m1', payload, s') =>
                pure (.paused ad m0' m1' payload s' cont)
          | qOther => do
            let (resp, hst') ← stepAuthCpaNonSendPrim S qOther s.2
            r resp f' (s.1, hst'))
    mx fuel shst

def cpaResumeAfterChallengeSlotPrim (idx : Nat) (S : Setup) (fuel : Nat) :
    CpaSlotPauseRes S Bool → Option Bytes → OracleComp PrimBaseSpec Bool
  | .done b' (_, hst), _ =>
    finalizeAeadCpaGameNoAuthPrim S b' hst.toAuthHybridState
  | .paused _ _ _ p (_, hst) cont, chalCt? => do
    let aeadCt := chalCt?.getD []
    let (resp, hst') := finishAuthCpaSendFixedPure true true p aeadCt hst
    let (b', (_, finalSt)) ←
      runWithPrimStepFuel false (cpaStepCutoffSlotPrim idx S) (cont resp) fuel (idx + 1, hst')
    finalizeAeadCpaGameNoAuthPrim S b' finalSt.toAuthHybridState

def cpaReductionAuthSlotAtChoose (idx : Nat) (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × CpaSlotPauseRes S Bool) := do
  let initSt : CpaSlotSt S := (0, AuthHybridStateFixed.empty S true)
  let res ← cpaStepUntilChallengeSlotPrim idx S false A.run fuel initSt
  match res with
  | .paused ad m0 m1 _ _ _ =>
    if m0.length == m1.length then
      return (ad, m0, m1, res)
    else
      return ([], [0], [0], res)
  | .done _ _ =>
    return ([], [0], [0], res)

def cpaReductionAuthSlotChoose (S : Setup) (fuel : Nat) (A : AuthAdversary S) :
    OracleComp PrimBaseSpec (Bytes × Bytes × Bytes × (Nat × CpaSlotPauseRes S Bool)) := do
  let idx ← embedUnif (RoKem.sampleIndexRange (min fuel S.N_send_tot))
  let (ad, m0, m1, res) ← cpaReductionAuthSlotAtChoose idx S fuel A
  return (ad, m0, m1, (idx, res))

def cpaReductionAuthSlotDist (S : Setup) (fuel : Nat)
    (st : Nat × CpaSlotPauseRes S Bool) (chalCt? : Option Bytes) :
    OracleComp PrimBaseSpec Bool :=
  cpaResumeAfterChallengeSlotPrim st.1 S fuel st.2 chalCt?

/-- Creation-order shallow `AeadIndCpaAdv` reduction. -/
def cpaReductionAuthSlot (S : Setup) (b : QueryBudget) (A : AuthAdversary S) : AeadIndCpaAdv where
  State  := Nat × CpaSlotPauseRes S Bool
  choose := cpaReductionAuthSlotChoose S b.q_total A
  dist   := cpaReductionAuthSlotDist S b.q_total
  q_prim := b.q_total * perQueryAuthPrimBudget S + S.N_dh * 5

/-- Creation-order state invariant bounding `CpaInv`, `idealSessions.length`, and `nextSendSlot`. -/
structure CpaSlotInv {S : Setup} (n : Nat) (shst : CpaSlotSt S) : Prop where
  inv      : CpaInv n shst.2
  ideal_le : shst.2.toAuthHybridState.idealSessions.length ≤ n
  slot_le  : shst.1 ≤ n

theorem CpaSlotInv.mono {S : Setup} {n m : Nat} {shst : CpaSlotSt S} (h : n ≤ m)
    (hI : CpaSlotInv n shst) : CpaSlotInv m shst :=
  ⟨hI.inv.mono h, Nat.le_trans hI.ideal_le h, Nat.le_trans hI.slot_le h⟩

theorem cpaSlotInv_empty (S : Setup) :
    CpaSlotInv 0 (0, AuthHybridStateFixed.empty S true) :=
  ⟨⟨authListsBounded_empty S true, rfl⟩, Nat.zero_le _, Nat.zero_le _⟩

/-- Creation-order pause-leaf invariant at step count `n` and challenge slot `idx`. -/
structure CpaSlotPauseInv {S : Setup} (idx n : Nat) (c : Bytes × Bytes × Bytes)
    (p : AuthCpaPausePayload S) (shst : CpaSlotSt S) : Prop where
  pause    : CpaPauseInv n c p shst.2
  ideal_le : shst.2.toAuthHybridState.idealSessions.length ≤ n
  slot_le  : shst.1 ≤ n
  slot_eq  : shst.1 = idx

def CpaSlotSendLeaf {S : Setup} (idx n : Nat) : CpaSlotSendRes S → Prop
  | .inl (_, sh) => CpaSlotInv (n + 1) sh
  | .inr (ad, m0, m1, p, sh) => CpaSlotPauseInv idx n (ad, m0, m1) p sh

end SignalPqxdh.Security.ReductionDsl.AuthAead
