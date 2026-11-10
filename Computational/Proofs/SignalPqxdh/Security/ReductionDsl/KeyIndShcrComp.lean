/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndSigKem
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KeyIndCoreSim
import VCVio.EvalDist.Monad.Basic

/-!
# `shcrKeyIndProg` Encodings and Shared Components

Value encodings of the `KemShCr` reduction state and evaluation lemmas for shared handler
components (`onBase`, `preCheckC`, `checkSigsC`, `initFinishC`).
-/

@[expose] public section

set_option autoImplicit false

open SignalPqxdh SignalPqxdh.Security SignalPqxdh.Security.FgGapDh
open _root_.ReductionDsl hiding B PTag U32 bundleOfV bundleT bundleV dhSecretsT drKeyOfV drKeyT drKeyV hdrOfV hdrT hdrV keyIndCodec keyIndQT keyIndQenc keyIndRT keyIndRdec keyIndRenc pqPrimIface pqSigAndDdhIface sampleIndex sidT sidV
open SignalPqxdh.LegacyCosted
open OracleSpec OracleComp RoKem

namespace SignalPqxdh.Security.ReductionDsl.KeyInd

def initRecToVal {S : Setup} (r : RoKem.InitKemRecord S) : initRecTy.denote :=
  (r.sendIdx, (sessionIdToVal r.sid, (r.pqspkPk, (r.kemCt, r.kemSs))))

def recvRecToVal (r : RoKem.RecvKemRecord) : recvRecTy.denote :=
  (0, (r.k, (r.j, (r.pqspkPk, (r.pqspkSk, (r.kemCt, r.kemSs))))))

/-- Value encoding of `KeyIndShCrState` with pause index `sIdx` and chosen public key. -/
def shcrStToVal {S : Setup} (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes) :
    shcrStTy.denote :=
  (keyIndStateToVal h.base, (h.targetBIdx?.map (fun bIdx => (bIdx / S.N_recv, bIdx % S.N_recv)),
    (h.targetPk, (h.targetSk, (h.sendCount,
    (h.initKemRecs.map initRecToVal, (h.recvKemRecs.map recvRecToVal, (sIdx, chosen))))))))

def encSCS {S : Setup} (sIdx : Nat) (chosen : Bytes) (p : KeyIndResponse × KeyIndShCrState S) :
    SCS.denote :=
  (keyIndRespToVal p.1, shcrStToVal p.2 sIdx chosen)

def encFin {S : Setup} (s : KeyIndState S) (p : KeyIndResponse × Option (KeyIndState S)) :
    RS.denote :=
  (keyIndRespToVal p.1, keyIndStateToVal (p.2.getD s))

section Components
variable (S : Setup) (K : Nat) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] (env : Env Δ)

theorem onBase_eval (sV : Var Γ₁ shcrStTy) (h : KeyIndShCrState S) (sIdx : Nat) (chosen : Bytes)
    (hs : env.get (Ext.wk sV) = shcrStToVal h sIdx chosen)
    (br : (g : Var (keyIndStateTy :: Δ) keyIndStateTy) →
      Comp pqxdhOps pqPrimIface (keyIndStateTy :: Δ) RS)
    (m : StateT (KeyIndState S) (OracleComp PrimBaseSpec) KeyIndResponse)
    (hbr : (br .zero).eval (.cons (keyIndStateToVal h.base) env) = encRS <$> m.run h.base) :
    (onBase sV br).eval env = encSCS sIdx chosen <$> (liftShCrBasePrim (S := S) m).run h := by
  unfold onBase
  simp only [bindV, letV_eval, Comp.eval, Expr.eval, v, Ext.step_wk', Env.get_succ',
    hs, scBase, scUpd, scMk, scTB, scTPk, scTSk, scCnt, scIR, scRR, scSIdx, scChosen, shcrStToVal]
  rw [hbr]
  simp only [liftShCrBasePrim, StateT.run, map_eq_bind_pure_comp, bind_assoc, Function.comp_def,
    pure_bind]
  rfl

def preCheckFullPrim (S : Setup) (sid : SessionId S) (u : Nat) (bundle : PreKeyBundleInput)
    (st : KeyIndState S) : OracleComp PrimBaseSpec (Option (Nat × PrincipalEntry)) :=
  if st.sessions.any (fun e => e.sid == sid) then pure none
  else match st.principals.find? (fun (idx, _) => idx == u) with
    | none => pure none
    | some p => do
      let koskOk ← koskBundleOkPrim S st.principals st.spkBundles st.opkEntries st.advKeys bundle
      if !koskOk then return none
      else return some p

theorem preCheckFullPrim_snd (S : Setup) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) :
    Option.map Prod.snd <$> preCheckFullPrim S sid u.val bundle st =
      preCheckKeyIndPrim S sid u bundle st := by
  unfold preCheckFullPrim preCheckKeyIndPrim
  split_ifs
  · simp
  · split
    · rename_i h; simp [h]
    · rename_i p h
      obtain ⟨k, e⟩ := p
      simp only [h, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
      refine bind_congr fun ok => ?_
      cases ok <;> simp

section Comp2
variable {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List PT} [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] (env : Env Δ)
  (st : Var Γ₁ keyIndStateTy) (s : KeyIndState S) (hs : env.get (Ext.wk st) = keyIndStateToVal s)
include hs

theorem checkSigsC_eval (buV : Var Γ₂ preKeyBundleTy) (b : PreKeyBundleInput)
    (hb : env.get (Ext.wk buV) = preKeyBundleToVal b) (hp : s.principals.length ≤ K) :
    (checkSigsC S K st buV).eval env = checkBundleSigsPrim S s.principals b := by
  unfold checkSigsC checkBundleSigsPrim
  simp only [bindV, Comp.eval, resolveSigPkC_eval]
  core_simp [hs, hb, decPrin_enc, preKeyBundleToVal, bundleV, encodeEC, encodeKEM]
  erw [hb]
  simp only [preKeyBundleToVal, bundleV]
  rw [decPrin_enc, List.take_of_length_le hp]

theorem preCheckC_eval (hB : KeyIndListsBounded s K) (sidV : Var Γ₂ sessionIdTy)
    (sid : SessionId S) (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid)
    (uV : Var Γ₃ .nat) (u : Nat) (hu : env.get (Ext.wk uV) = u)
    (buV : Var Γ₄ preKeyBundleTy) (b : PreKeyBundleInput)
    (hb : env.get (Ext.wk buV) = preKeyBundleToVal b) :
    (preCheckC S K st sidV uV buV).eval env =
      Option.map (Prod.map id principalEntryToVal) <$> preCheckFullPrim S sid u b s := by
  unfold preCheckC preCheckFullPrim
  simp only [bindV, caseOptV, Comp.eval, koskBundleOkC_eval]
  core_simp [hs, hsid, hu, hb, List.take_of_length_le, hB.principals_le, hB.sessions_le,
    hB.advKeys_le, decPrin_enc, decSpks_enc, decOpks_enc']
  rw [decPrin_enc, decSpks_enc, decOpks_enc', preKeyBundleToVal, valToPreKeyBundle,
    bundleOfV_bundleV]
  try simp only [List.take_of_length_le hB.principals_le]
  try simp only [List.take_of_length_le hB.spkBundles_le]
  try simp only [List.take_of_length_le hB.opkEntries_le]
  try simp only [List.take_of_length_le hB.advKeys_le]
  split_ifs
  · simp
  · simp only [Prod.map, id]
    generalize s.principals.find? (fun x => x.1 == u) = o
    rcases o with _ | ⟨k, e⟩
    · simp
    · simp only [Option.map_some, map_eq_bind_pure_comp, bind_assoc, Function.comp_def]
      refine bind_congr fun ok => ?_
      cases ok <;> simp

set_option maxHeartbeats 1000000 in
theorem initFinishC_eval {Γ₅ Γ₆ : List PT} [Ext Γ₅ Δ] [Ext Γ₆ Δ] (hB : KeyIndListsBounded s K)
    (sidV : Var Γ₂ sessionIdTy) (sid : SessionId S)
    (hsid : env.get (Ext.wk sidV) = sessionIdToVal sid) (buV : Var Γ₃ preKeyBundleTy)
    (b : PreKeyBundleInput) (hb : env.get (Ext.wk buV) = preKeyBundleToVal b)
    (uEV : Var Γ₄ (.prod .nat principalEntryTy)) (k : Nat) (e : PrincipalEntry)
    (huE : env.get (Ext.wk uEV) = (k, principalEntryToVal e)) (ekV : Var Γ₅ (B 32)) (ek : Bytes)
    (hek : env.get (Ext.wk ekV) = ek) (scV : Var Γ₆ (.prod (B 32) (B 1568))) (ss ct : Bytes)
    (hsc : env.get (Ext.wk scV) = (ss, ct)) :
    (initFinishC true S K st sidV buV uEV ekV scV).eval env =
      encFin s <$> finishKeyIndBasePrim S sid b e ek ss ct s := by
  unfold initFinishC
  simp only [bindV, letV, caseOptV, Comp.eval, hkdfOrRoC_eval, honestPeerC_eval, checkProvC_eval,
    findHonestC_eval]
  core_simp [hs, hsid, hb, huE, hek, hsc, List.take_of_length_le, hB.principals_le,
    hB.sessions_le, hB.roCache_le, hB.spkBundles_le,
    decPrin_enc, decSpks_enc, decOpks_enc, decRo_enc, evalHkdfOrRoK_eq, checkProvK_eq]
  erw [hb]
  rw [decPrin_enc, decSpks_enc, decOpks_enc', decRo_enc]
  core_simp [partnerC, preKeyBundleToVal, bundleV, evalHkdfOrRoK_eq, hB.roCache_le, checkProvK_eq,
    hB.spkBundles_le]
  erw [hek, huE]
  have hR : (s.respSessions.map keyIndRespEntryToVal).length ≤ K := by
    simpa using hB.respSessions_le
  try simp only [List.take_of_length_le hB.principals_le]
  try simp only [List.take_of_length_le hR]
  try rw [checkProvK_eq S K _ _ _ _ hB.principals_le hB.spkBundles_le hB.opkEntries_le]
  simp only [valToPreKeyBundle, bundleOfV, finishKeyIndBasePrim]
  obtain ⟨ikB, spkId, spkB, spkSig, opkB, pqspkId, pqspkB, pqspkSig⟩ := b
  rcases opkB with _ | ⟨oid, opk⟩ <;>
  simp [keyIndPartnerPrim, buildSecrets, map_eq_bind_pure_comp] <;>
  refine bind_congr fun a => bind_congr fun a1 => bind_congr fun a2 => bind_congr fun a3 => ?_ <;>
  refine bind_congr fun a4 => ?_ <;>
  refine bind_congr fun dr => bind_congr fun hp => bind_congr fun pv => ?_ <;>
  refine bind_congr2 ?_ fun fd => ?_
  all_goals first
    | (rw [take_minK, List.take_of_length_le hB.respSessions_le]
       refine congrArg (fun p => findMPrim p _) (funext fun r => ?_)
       refine bind_congr fun b1 => bind_congr fun b2 => bind_congr fun b3 => bind_congr fun b4 => ?_
       refine bind_congr fun b5 => bind_congr fun b6 => bind_congr fun b7 => ?_
       cases hr : r.opkPk? <;> simp [hdrV])
    | (rcases fd with _ | r
       · simp
         refine bind_congr fun d => ?_
         rw [map_eq_bind_pure_comp]
         refine bind_congr fun h => ?_
         cases h <;> cases hp <;>
           simp [encFin, keyIndSessionEntryToVal, keyIndRespToVal, keyIndRenc, hdrV, drKeyV]
       · simp
         rw [map_eq_bind_pure_comp]
         refine bind_congr fun h => ?_
         cases h <;> cases hp <;>
           simp [encFin, keyIndSessionEntryToVal, keyIndRespToVal, keyIndRenc, hdrV, drKeyV])

end Comp2

end Components

end SignalPqxdh.Security.ReductionDsl.KeyInd
