/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndGapDhStep
import VCVio.EvalDist.Monad.Basic

/-!
# Initiate Branch Evaluation Agreement

Proves that `initiateOpkGdhB` and `initiateNoOpkGdhB` evaluate to `fgRunInitiateGdh`.
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp

namespace SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
open SignalPqxdh.Security.ReductionDsl.KeyInd

section
set_option allowUnsafeReducibility true
attribute [implicit_reducible] initSessionSlotIdx
end

@[simp] theorem decSpks_enc' (l : List ((Nat × Nat) × SpkBundleEntry)) :
    decSpks (l.map (fun x => (x.1, spkBundleEntryToVal x.2))) = l :=
  decSpks_enc l

@[simp] theorem sidEqV_sendOPK {S : Setup} (s : SessionId S)
    (u : Fin S.N_id) (i : Fin S.N_send_opk) :
    sidEqV (sidV s) (.inl (u.val, i.val)) = (s == .sendOPK u i) :=
  sidEqV_enc s (.sendOPK u i)

@[simp] theorem sidEqV_sendNoOPK {S : Setup} (s : SessionId S)
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) :
    sidEqV (sidV s) (.inr (.inl (u.val, i.val))) = (s == .sendNoOPK u i) :=
  sidEqV_enc s (.sendNoOPK u i)

@[simp] theorem koskBundleOkPowsC_eval' (S : Setup) (K : Nat) {Γ₁ Γ₂ Δ : List PT}
    [Ext Γ₁ Δ] [Ext Γ₂ Δ]
    (st : Var Γ₁ keyIndStateTy) (pows : Expr pqxdhOps Δ (.list (.prod (B 32) (B 32))))
    (bu : Var Γ₂ preKeyBundleTy) (env : Env Δ) :
    (koskBundleOkPowsC S K st pows bu).eval env =
      FgGapDh.koskBundleOkPrim S ((decPrin (env.get (Ext.wk st)).2.1).take K)
        ((decSpks (env.get (Ext.wk st)).2.2.1).take K)
        ((decOpks (env.get (Ext.wk st)).2.2.2.1).take K)
        ((pows.eval env).take K) (valToPreKeyBundle (env.get (Ext.wk bu))) := by
  unfold koskBundleOkPowsC FgGapDh.koskBundleOkPrim
  core_simp [findHonestC_eval, isGameSpkC_eval,
    isGameOpkC_eval, isAdvPowsE_eval, valToPreKeyBundle, bundleOfV,
    FgGapDh_primQ_eq, FgGapDh_findHonestPrincipalPrim_eq,
    FgGapDh_isGameSpkPrim_eq, FgGapDh_isGameOpkPrim_eq,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun x => ?_
  refine bind_congr fun w1 => ?_
  refine bind_congr fun g1 => ?_
  refine bind_congr fun w2 => ?_
  rcases (env.get (Ext.wk bu)).2.2.2.2.1 with _ | ⟨id, pk⟩
  · cases x <;> rfl
  · simp only [bind_assoc, pure_bind]
    refine bind_congr fun g2 => ?_
    refine bind_congr fun w3 => ?_
    cases x <;> rfl

section InitiateEval
variable (S : Setup) (K : Nat)
  {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ]
  (paV : Var Γ₁ paramsTy) (smV : Var Γ₂ simTy) (bStV : Var Γ₃ keyIndStateTy)
  (env : Env Δ) (pa : paramsTy.denote) (st : FgKeyIndSimState S)
  (hpa : env.get (Ext.wk paV) = pa)
  (hsm : env.get (Ext.wk smV) = simStateToVal st)
  (hbSt : env.get (Ext.wk bStV) = keyIndStateToVal st.base)
  (hB : FgSimListsBounded st K)
include hpa hsm hbSt hB

set_option maxHeartbeats 1200000 in
theorem initiateOpkGdhB_eval (xV : Var Γ₄ (.prod .nat (.prod .nat preKeyBundleTy)))
    (u : Fin S.N_id) (i : Fin S.N_send_opk) (bundle : PreKeyBundleInput)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle))) :
    (initiateGdhB S K paV smV bStV true xV).eval env =
      encSimRS <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.initiateOPK u i bundle) st := by
  unfold initiateGdhB fgKeyIndStep fgRunInitiateGdh
  obtain ⟨ikB, sId, spkB, spkSig, opkB?, pqId, pqB, pqSig⟩ := bundle
  have hMin : Nat.min S.N_send_opk S.N_send_opk_tot = S.N_send_opk :=
    Nat.min_eq_left (Nat.le_mul_of_pos_left _ u.pos)
  simp only [letV_eval, bindV, caseOptV, Comp.eval, gPrim_eval,
    koskBundleOkPowsC_eval',
    resolveSigPkC_eval, honestPeerC_eval, checkProvC_eval, findHonestC_eval]
  gdh_simp [hpa, hsm, hbSt, hx, initSlotIdxE, hMin, List.take_of_length_le,
    sidEqV_sendOPK,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.sessions_le, hB.advKeyPows_le,
    decPrin_enc, decSpks_enc, decSpks_enc', decOpks_enc, decOpks_enc', checkProvK_eq,
    preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV, unifGdh, sampleScalar32,
    sampleCoins32, primGdhQ]
  try erw [hx]
  try rw [decPrin_enc]
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  try rw [decOpks_enc]
  try rw [decOpks_enc']
  try gdh_simp [initSlotIdxE, hMin, sidEqV_sendOPK, checkProvK_eq,
    hB.base_le.spkBundles_le, hB.advKeyPows_le,
    List.take_of_length_le, preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV]
  rcases opkB? with _ | ⟨oId, opkPk⟩
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  have hAny : (st.base.sessions.any fun x =>
      sidEqV (sidV x.sid) (.inl (u.val, i.val))) =
      (st.base.sessions.any fun x => x.sid == .sendOPK u i) := by
    congr 1; funext x; exact sidEqV_sendOPK x.sid u i
  dsimp only [sidV, sessionIdToVal] at hAny
  rw [hAny]
  by_cases h1 : (st.base.sessions.any fun x => x.sid == SessionId.sendOPK u i) = true
  · simp [h1, encSimRS, keyIndRespToVal, simStateToVal]
  rcases h2 : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨u', uE⟩
  · simp [h1, h2, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    map_eq_bind_pure_comp, bind_assoc]
  simp only [List.take_of_length_le hB.base_le.principals_le,
    List.take_of_length_le hB.base_le.opkEntries_le]
  refine bind_congr fun bOk => ?_
  cases bOk
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  gdh_simp [Bool.not_true, initSlotIdxE, hMin, initSessionSlotIdx, principalEntryToVal,
    _root_.SignalPqxdh.Security.primQ, primGdhQ, bind_assoc]
  refine bind_congr fun ekSkRaw => ?_
  refine bind_congr fun coins => ?_
  refine bind_congr fun sigPk => ?_
  refine bind_congr fun v1 => ?_
  refine bind_congr fun v2 => ?_
  by_cases hv : (v1 && v2) = true
  swap
  · simp only [Bool.not_eq_true] at hv
    simp [hv, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine bind_congr fun krOpt => ?_
  rcases krOpt with _ | ⟨ss, kemCt⟩
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  simp only [bind_assoc]
  refine bind_congr fun ekPkRaw => ?_
  rw [lookupSpkSkC_eval S K bStV _ _ _ st.advKeyPows
    (by simp [Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hbSt, hx, decSpks_enc, decSpks_enc']
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  rw [List.take_of_length_le hB.base_le.spkBundles_le]
  refine bind_congr fun spkSk => ?_
  gdh_simp [computePosC_eval, computeOptPosInitC_eval, hx,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun pos1 => ?_
  refine bind_congr fun pos2 => ?_
  refine bind_congr fun pos3 => ?_
  refine bind_congr fun pos4? => ?_
  rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 pos4? ss st.fgL
    rfl rfl rfl rfl rfl (by simp [Expr.eval, hsm, simStateToVal])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun ⟨drKeyReal, fgL'⟩ => ?_
  refine bind_congr fun hp => ?_
  rw [checkProvK_eq S K _ _ _ _ hB.base_le.principals_le hB.base_le.spkBundles_le
    hB.base_le.opkEntries_le]
  refine bind_congr fun ⟨spkHon, opkHon, pqspkHon⟩ => ?_
  let isTE := !pa.2.2.2.2.2.1 && ((↑u * S.N_send_opk + ↑i) == pa.2.2.2.2.2.2.1)
  let ekSk := if isTE then ([] : Bytes) else ekSkRaw
  let ekPk := if isTE then pa.1 else ekPkRaw
  let hdr : HandshakeHdr := {
    ikAPk := uE.ikAPk, ekAPk := ekPk, spkId := sId,
    opkId? := some oId, pqspkId := pqId, kemCt := kemCt
  }
  let sInit : KeyIndInitiatorEntry S := {
    sid := .sendOPK u i, honestPeer := hp, peerIkPk := ikB, peerSpkPk := spkB,
    peerOpkPk? := some opkPk, peerPqspkPk := pqB, spkHonest := spkHon,
    opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekSk,
    fresh := hp.isSome, drKeyReal := drKeyReal, drKeyRand := drKeyReal,
    hdr := hdr, tested := false
  }
  rw [chooseInitRandC_eval S K bStV .zero _ st.base.respSessions sInit
    (by simp [hbSt, keyIndStateToVal])
    (by cases hp <;> simp [sInit, hdr, ekPk, ekSk, isTE, keyIndSessionEntryToVal])
    hB.base_le.respSessions_le]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun drKeyRand => ?_
  refine bind_congr fun fh => ?_
  cases fh <;> cases hp <;>
    (gdh_simp [sInit, hdr, ekPk, ekSk, isTE,
      hsm, hbSt, hx, encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal,
      keyIndSessionEntryToVal, preKeyBundleToVal, handshakeHdrToVal, sessionIdToVal]; rfl)

set_option maxHeartbeats 1200000 in
theorem initiateNoOpkGdhB_eval (xV : Var Γ₄ (.prod .nat (.prod .nat preKeyBundleTy)))
    (u : Fin S.N_id) (i : Fin S.N_send_no_opk) (bundle : PreKeyBundleInput)
    (hx : env.get (Ext.wk xV) = (u.val, (i.val, preKeyBundleToVal bundle))) :
    (initiateGdhB S K paV smV bStV false xV).eval env =
      encSimRS <$> fgKeyIndStep pa.2.2.2.2.2.1 pa.2.2.2.2.2.2.1 pa.2.2.2.2.2.2.2.1 S K
        pa.1 pa.2.1 (.initiateNoOPK u i bundle) st := by
  unfold initiateGdhB fgKeyIndStep fgRunInitiateGdh
  obtain ⟨ikB, sId, spkB, spkSig, opkB?, pqId, pqB, pqSig⟩ := bundle
  have hMin : Nat.min S.N_send_no_opk S.N_send_no_opk_tot = S.N_send_no_opk :=
    Nat.min_eq_left (Nat.le_mul_of_pos_left _ u.pos)
  simp only [letV_eval, bindV, caseOptV, Comp.eval, gPrim_eval,
    koskBundleOkPowsC_eval',
    resolveSigPkC_eval, honestPeerC_eval, checkProvC_eval, findHonestC_eval]
  gdh_simp [hpa, hsm, hbSt, hx, initSlotIdxE, hMin, List.take_of_length_le,
    sidEqV_sendNoOPK,
    hB.base_le.principals_le, hB.base_le.spkBundles_le, hB.base_le.opkEntries_le,
    hB.base_le.sessions_le, hB.advKeyPows_le,
    decPrin_enc, decSpks_enc, decSpks_enc', decOpks_enc, decOpks_enc', checkProvK_eq,
    preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV, unifGdh, sampleScalar32,
    sampleCoins32, primGdhQ]
  try erw [hx]
  try rw [decPrin_enc]
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  try rw [decOpks_enc]
  try rw [decOpks_enc']
  try gdh_simp [initSlotIdxE, hMin, sidEqV_sendNoOPK, checkProvK_eq,
    hB.base_le.spkBundles_le, hB.advKeyPows_le,
    List.take_of_length_le, preKeyBundleToVal, bundleV, valToPreKeyBundle, bundleOfV]
  rcases opkB? with _ | ⟨oId, opkPk⟩
  swap
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.not_true]
  have hAny : (st.base.sessions.any fun x =>
      sidEqV (sidV x.sid) (.inr (.inl (u.val, i.val)))) =
      (st.base.sessions.any fun x => x.sid == .sendNoOPK u i) := by
    congr 1; funext x; exact sidEqV_sendNoOPK x.sid u i
  dsimp only [sidV, sessionIdToVal] at hAny
  rw [hAny]
  by_cases h1 : (st.base.sessions.any fun x => x.sid == SessionId.sendNoOPK u i) = true
  · simp [h1, encSimRS, keyIndRespToVal, simStateToVal]
  rcases h2 : st.base.principals.find? (fun x => x.1 == ↑u) with _ | ⟨u', uE⟩
  · simp [h1, h2, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, Option.map_some,
    map_eq_bind_pure_comp, bind_assoc]
  simp only [List.take_of_length_le hB.base_le.principals_le,
    List.take_of_length_le hB.base_le.opkEntries_le]
  refine bind_congr fun bOk => ?_
  cases bOk
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  gdh_simp [Bool.not_true, initSlotIdxE, hMin, initSessionSlotIdx, principalEntryToVal,
    _root_.SignalPqxdh.Security.primQ, primGdhQ, bind_assoc]
  refine bind_congr fun ekSkRaw => ?_
  refine bind_congr fun coins => ?_
  refine bind_congr fun sigPk => ?_
  refine bind_congr fun v1 => ?_
  refine bind_congr fun v2 => ?_
  by_cases hv : (v1 && v2) = true
  swap
  · simp only [Bool.not_eq_true] at hv
    simp [hv, encSimRS, keyIndRespToVal, simStateToVal]
  simp only [hv, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
  refine bind_congr fun krOpt => ?_
  rcases krOpt with _ | ⟨ss, kemCt⟩
  · simp [encSimRS, keyIndRespToVal, simStateToVal]
  simp only [bind_assoc]
  refine bind_congr fun ekPkRaw => ?_
  rw [lookupSpkSkC_eval S K bStV _ _ _ st.advKeyPows
    (by simp [Expr.eval, hsm, simStateToVal]) hB.advKeyPows_le]
  gdh_simp [hbSt, hx, decSpks_enc, decSpks_enc']
  try rw [decSpks_enc]
  try rw [decSpks_enc']
  rw [List.take_of_length_le hB.base_le.spkBundles_le]
  refine bind_congr fun spkSk => ?_
  gdh_simp [computePosC_eval, computeOptPosInitC_eval, hx,
    map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr fun pos1 => ?_
  refine bind_congr fun pos2 => ?_
  refine bind_congr fun pos3 => ?_
  refine bind_congr fun pos4? => ?_
  rw [fgPatchC_eval K _ _ _ _ _ _ _ pos1 pos2 pos3 pos4? ss st.fgL
    rfl rfl rfl rfl rfl (by simp [Expr.eval, hsm, simStateToVal])]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun ⟨drKeyReal, fgL'⟩ => ?_
  refine bind_congr fun hp => ?_
  rw [checkProvK_eq S K _ _ _ _ hB.base_le.principals_le hB.base_le.spkBundles_le
    hB.base_le.opkEntries_le]
  refine bind_congr fun ⟨spkHon, opkHon, pqspkHon⟩ => ?_
  let isTE := !pa.2.2.2.2.2.1 &&
    ((S.N_send_opk_tot + (↑u * S.N_send_no_opk + ↑i)) == pa.2.2.2.2.2.2.1)
  let ekSk := if isTE then ([] : Bytes) else ekSkRaw
  let ekPk := if isTE then pa.1 else ekPkRaw
  let hdr : HandshakeHdr := {
    ikAPk := uE.ikAPk, ekAPk := ekPk, spkId := sId,
    opkId? := none, pqspkId := pqId, kemCt := kemCt
  }
  let sInit : KeyIndInitiatorEntry S := {
    sid := .sendNoOPK u i, honestPeer := hp, peerIkPk := ikB, peerSpkPk := spkB,
    peerOpkPk? := none, peerPqspkPk := pqB, spkHonest := spkHon,
    opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekSk,
    fresh := hp.isSome, drKeyReal := drKeyReal, drKeyRand := drKeyReal,
    hdr := hdr, tested := false
  }
  rw [chooseInitRandC_eval S K bStV .zero _ st.base.respSessions sInit
    (by simp [hbSt, keyIndStateToVal])
    (by cases hp <;> simp [sInit, hdr, ekPk, ekSk, isTE, keyIndSessionEntryToVal])
    hB.base_le.respSessions_le]
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine bind_congr fun drKeyRand => ?_
  refine bind_congr fun fh => ?_
  cases fh <;> cases hp <;>
    (gdh_simp [sInit, hdr, ekPk, ekSk, isTE,
      hsm, hbSt, hx, encSimRS, keyIndRespToVal, simStateToVal, keyIndStateToVal,
      keyIndSessionEntryToVal, preKeyBundleToVal, handshakeHdrToVal, sessionIdToVal]; rfl)

end InitiateEval

end SignalPqxdh.Security.ReductionDsl.KeyIndGapDh
