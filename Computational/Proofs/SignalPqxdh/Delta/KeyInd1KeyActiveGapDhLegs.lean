/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.FgGapDh1Key -- proof-setup: allow-public-import
import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs

/-!
# Active Creation-Order `GapDhWithSign` Pure Runners and Per-Ordinal `DH2` Bound

Defines pure `ProbComp` counterparts of `fgKeyInd1KeyActiveStep` and proves the creation-order
`DH2` per-ordinal bound `prob_badKeyIndFgDh2OrdAt_1Key_le_gapDhWithSign_active`.
-/

set_option autoImplicit false

open scoped ENNReal BigOperators
open MeasureTheory (measure_ne_top)
open OracleSpec OracleComp
open SignalPqxdh (Setup Bytes PrincipalEntry SpkBundleEntry OpkEntry PreKeyBundleInput HandshakeHdr
  SessionId KeyIndQuery KeyIndResponse KeyIndState KeyIndInitiatorEntry KeyIndAdversary keyIndSpec
  QueryBudget BoundedAdv isGameQuery QueryBounded activeSendCount activeIdCount Primitives
  CryptoWellFormedPrimitivesδ GapDhWithSignAdv GapDhWithSign gapDhWithSignExp GapDhWithSignReal
  sampleScalar32 sampleCoins32 sampleRandom64 sampleKemKeyGen encodeEC encodeKEM findHonestPrincipal
  resolveSigPk isHonestUncorruptedPeer koskBundleOk pqxdhKeyIndImpl)
open SignalPqxdh.Security (bundleSignedMessages IsSendSessionId ValidPrincipals ValidSpkBundles
  ValidOpkEntries ValidSessionIds ValidEcLists validEcLists_nil sessPksKeyInd ValidKeyIndEc
  validPrincipals_cons validSpkBundles_cons validSessionIds_cons pqxdhKeyIndImpl_validKeyIndEc_step
  PreservesAt)
open SignalPqxdh.Security.FgGapDh (FgKeyIndSimState spkBundleFlatIdx initSessionSlotIdx)
open SignalPqxdh.Security.FgGapDh1Key (FgKeyInd1KeySimState)
open Proofs.SignalPqxdh.Security.FgGapDh (KeyIndFgCutoffState initSessionSlotIdx_sendOPK_lt
  initSessionSlotIdx_sendNoOPK_lt initSessionSlotIdx_inj_of_lt StateT_run_mk liftFgBase
  pqxdhKeyIndFgImpl fgPreGenSPK fgPreInitiate pqxdhKeyIndFgPreImpl mem_support_liftFgBase
  mem_support_fgPreInitiate_elim mem_support_pqxdhKeyIndFgPreImpl_elim
  evalDist_bind_true_eq_zero_of_support evalDist_bind_true_mono_of_support simulateQ_run_query_inl
  simulateQ_run_query_inr length_of_mem_support_sampleScalar32 ValidKeyIndEcFg erasePrincipalEntryFg
  erasePrincipalsFg eraseSessionEntryFg eraseSessionsFg erasePrincipalsFg_length
  any_idx_erasePrincipalsFg any_sid_eraseSessionsFg deadDh1 deadDh1_eq_of_principals gapDhFullImpl
  koskBundleOkTake lookupSpkSkTake checkBundleProvenanceTake computeTwoSideOrPairPosPure
  computeOptPosPure fgPatchPure chooseInitPartnerDrKeyRandPure fgRoQueryPure fgRunAcceptOPKPure
  fgRunAcceptNoOPKPure fgRunInitiatePure fgKeyIndStepPure pureExtractCdhFromSimState
  simulateQ_gapDhFullImpl_embedPrim simulateQ_gapDhFullImpl_unifGdh
  simulateQ_gapDhFullImpl_primGdhQ_x25519Base simulateQ_gapDhFullImpl_primGdhQ_sigSign
  simulateQ_gapDhFullImpl_primGdhQ_sigVerify simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen
  simulateQ_gapDhFullImpl_primGdhQ_kemEncaps simulateQ_gapDhFullImpl_computeTwoSideOrPairPos
  simulateQ_gapDhFullImpl_computeOptPos simulateQ_gapDhFullImpl_fgPatch
  simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh simulateQ_primBaseImpl_koskBundleOkPrim
  simulateQ_primBaseImpl_resolveSigPkPrim simulateQ_primBaseImpl_lookupSpkSkPrim
  simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim
  simulateQ_primBaseImpl_checkBundleProvenancePrim simulateQ_primBaseImpl_findHonestPrincipalPrim
  simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh simulateQ_gapDhFullImpl_fgKeyIndStep
  simulateQ_gapDhFullImpl_extractCdhFromSimState)
open Proofs.SignalPqxdh.Security.FgGapDh.Ik (spkBundleFlatIdx_ne_noSpkIdx eraseStateFgIk
  badKeyIndFgDh2At prinTargetIsV sessDeadIk deadDh2 badKeyIndFgDh2At_eq_false_of_deadDh2
  sessDeadIk_eq_of_sess deadDh2_eq_of_prin_sess deadDh1_mono_map_corrupted deadDh2_map_corrupted
  deadDh2_sess_cons deadDh2_sess_map FgSimInvDh2 pureExtractCdh2FromAdvRoLog
  simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog)
open Proofs.SignalPqxdh.Security.FgGapDh.Opk (fgRunAcceptOPKPureOpk pureExtractCdh4FromAdvRoLog
  simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog)
open Proofs.SignalPqxdh.Security.FgGapDh1Key (runKeyIndFgSim1Key fgPreInitPrin1Key
  pqxdhKeyIndFgPreImpl1Key pqxdhKeyIndFgPreImpl1KeyIk pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin
  pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin fgInitPrin1KeyPure fgGenSPK1KeyPure
  fgKeyInd1KeyStepPureIk fgKeyInd1KeySimImplIk gapDhWithSignFullImpl
  simulateQ_gapDhWithSignFullImpl_liftGdhToSign simulateQ_gapDhWithSignFullImpl_unifGdhSign
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base
  simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen simulateQ_gapDhWithSignFullImpl_sigChalQ
  simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep clearTargetPrinSecSign
  clearTargetSecIKAsignBase clearTargetSecIKAsign clearTargetSecIKAsign_base_principals
  clearTargetSecIKAsign_base_spkBundles clearTargetSecIKAsign_base_sessions
  any_idx_map_clearTargetPrinSecSign FgSimInvDh2_1Key fgSimInvDh2_1Key_empty
  fgSimInvDh2_1Key_terminal_le fgStepCoupling_dh2_1Key)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow (FgActiveParams activeParamsDh1
  activeParamsDh3 activeParamsDh2 activeParamsDh4 FgKeyInd1KeyActiveSimState optNatMatches
  liftSimStep1KeyActive fgInitPrin1KeyActiveGdh fgGenSpkActiveGdh fgGenSPK1KeyActiveGdh
  fgGenOPKActiveGdh fgRunInitiateActiveGdh fgInitiateActiveGdh fgKeyInd1KeyActiveStep
  fgKeyInd1KeyActiveFinish fgKeyInd1KeyActiveRunWithParams fgKeyInd1KeyGapDhActiveAdvAt
  fgKeyInd1KeyGapDhActiveAdvAtIk fgKeyInd1KeyGapDhActiveAdvAtOpk)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhPre (prinSlotAtOrd sessSlotAtOrd
  badKeyIndFgDh2OrdAt ordLookup prinSlotAtOrd_eq sessSlotAtOrd_eq ordLookup_of_ge ordLookup_cons_eq
  ordLookup_cons_of_lt ordLookup_mem_of_lt ordLookup_map_eq curPrinSlot curSessSlot
  pqxdhKeyIndFgPreImpl1KeyOrdIk fgPre1Key_lengths_mono evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh2)
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLegs

public section
/-! ## Pure step counterparts -/

@[expose] noncomputable def fgInitPrin1KeyActivePure {S : Setup} (P : Primitives) (prinFlag : Bool)
    (prinIdx : Nat) (Up : Bytes) (u : Fin S.N_id) (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val) then return (.noneResp, stA)
  let isTargetPrin : Bool := prinFlag && (stA.st1.sim.base.principals.length == prinIdx)
  let sk0 ← sampleScalar32; let pk0 := P.x25519Base sk0
  let sec0 := if isTargetPrin then [] else sk0; let ikPk := if isTargetPrin then Up else pk0
  let entry : PrincipalEntry :=
    { secIKA0 := sec0, ikAPk := ikPk, secIKAsign := sec0, ikSignPk := ikPk, corrupted := false }
  let base' := { stA.st1.sim.base with principals := (u.val, entry) :: stA.st1.sim.base.principals }
  let tp' := if isTargetPrin then some u.val else stA.resolvedPrin?
  return (.initPrinResp ikPk ikPk,
    { stA with st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } }, resolvedPrin? := tp' })

@[expose] noncomputable def fgGenSpkActivePure {S : Setup} (P : Primitives) (spkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgKeyIndSimState S) :
    ProbComp (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val) | return (.noneResp, st)
  let isTargetSpk : Bool := st.base.spkBundles.length == spkIdx
  let spkSkRaw ← sampleScalar32; let spkPkRaw := P.x25519Base spkSkRaw
  let spkSk := if isTargetSpk then [] else spkSkRaw; let spkPk := if isTargetSpk then V else spkPkRaw
  let rSpk ← sampleRandom64; let spkSig := P.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk
  let seedKem ← sampleRandom64; let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
  let rPq ← sampleRandom64; let pqspkSig := P.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq
  let bEntry : SpkBundleEntry :=
    { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
      pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
  let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
  let bundleOut : PreKeyBundleInput :=
    { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
      opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
  return (.bundleResp bundleOut, { st with base := base' })

@[expose] noncomputable def fgGenSPK1KeyActivePure {S : Setup} (P : Primitives) (uSk : Bytes) (spkIdx : Nat)
    (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv) (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if optNatMatches stA.resolvedPrin? u.val then
    if stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then return (.noneResp, stA)
    let some (_, uEntry) := stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, stA)
    if stA.st1.sigBudget == 0 then return (.noneResp, stA)
    let isTargetSpk : Bool := stA.st1.sim.base.spkBundles.length == spkIdx
    let spkSkRaw ← sampleScalar32; let spkPkRaw := P.x25519Base spkSkRaw
    let spkSk := if isTargetSpk then [] else spkSkRaw; let spkPk := if isTargetSpk then V else spkPkRaw
    let rSpk ← sampleRandom64; let spkSig := P.sigSign uSk (encodeEC spkPk) rSpk
    let seedKem ← sampleRandom64; let (pqspkPk, pqspkSk) := P.kemKeyGen seedKem
    let rPq ← sampleRandom64; let pqspkSig := P.sigSign uSk (encodeKEM pqspkPk) rPq
    let bEntry : SpkBundleEntry :=
      { spkSk := spkSk, spkPk := spkPk, spkSig := spkSig,
        pqspkSk := pqspkSk, pqspkPk := pqspkPk, pqspkSig := pqspkSig }
    let base' := { stA.st1.sim.base with spkBundles := ((u.val, j.val), bEntry) :: stA.st1.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput :=
      { ikB := uEntry.ikAPk, spkId := UInt32.ofNat j.val, spkB := spkPk, spkSig := spkSig,
        opkB? := none, pqspkId := UInt32.ofNat j.val, pqspkB := pqspkPk, pqspkSig := pqspkSig }
    return (.bundleResp bundleOut,
      { stA with st1 := { sim := { stA.st1.sim with base := base' }, sigBudget := stA.st1.sigBudget - 1 } })
  else
    let (resp, sim') ← fgGenSpkActivePure P spkIdx V u j stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

@[expose] noncomputable def fgGenOPKActivePure {S : Setup} (P : Primitives) (opkMode : Bool) (opkIdx : Nat)
    (V : Bytes) (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then return (.noneResp, stA)
  let isTargetOpk : Bool := opkMode && (stA.st1.sim.base.opkEntries.length == opkIdx)
  let opkSkRaw ← sampleScalar32; let opkPkRaw := P.x25519Base opkSkRaw
  let oEntry : OpkEntry :=
    { opkSk := if isTargetOpk then [] else opkSkRaw, opkPk := if isTargetOpk then V else opkPkRaw, consumed := false }
  let base' := { stA.st1.sim.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: stA.st1.sim.base.opkEntries }
  return (.pkResp oEntry.opkPk, { stA with st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } } })

@[expose] noncomputable def fgRunInitiateActivePure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup) (maxLen : Nat) (U : Bytes) (hasOpk : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    ProbComp (KeyIndResponse × (FgKeyIndSimState S × Nat)) := do
  let guardOk : Bool := if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome
  if !guardOk then return (.noneResp, (st, sendOpkCnt))
  if st.base.sessions.any (fun e => e.sid == sid) then return (.noneResp, (st, sendOpkCnt))
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, (st, sendOpkCnt))
  if !koskBundleOkTake S P st.base.principals st.base.spkBundles st.base.opkEntries
    st.advKeyPows bundle then return (.noneResp, (st, sendOpkCnt))
  let isTargetEph : Bool :=
    if hasOpk then (!dhFlag) && ((if opkMode then sendOpkCnt else st.base.sessions.length) == ephIdx)
    else (!dhFlag) && ((!opkMode) && (st.base.sessions.length == ephIdx))
  let ekASkRaw ← sampleScalar32; let kemCoins ← sampleCoins32
  let sigPkB := resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB
  if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
       P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
    return (.noneResp, (st, sendOpkCnt))
  let some (ss, kemCt) := P.kemEncaps bundle.pqspkB kemCoins | return (.noneResp, (st, sendOpkCnt))
  let ekAPkRaw := P.x25519Base ekASkRaw
  let ekASk := if isTargetEph then [] else ekASkRaw; let ekAPk := if isTargetEph then U else ekAPkRaw
  let spkSk := lookupSpkSkTake S P st.base.spkBundles st.advKeyPows bundle.spkB
  let pos1 := computeTwoSideOrPairPosPure P uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.ikB
  let pos3 := computeTwoSideOrPairPosPure P ekASk [] ekAPk bundle.spkB
  let pos4? := computeOptPosPure P ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKeyReal, fgL') ← fgPatchPure ddh maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let hdr : HandshakeHdr :=
    { ikAPk := uEntry.ikAPk, ekAPk := ekAPk, spkId := bundle.spkId,
      opkId? := bundle.opkB?.map Prod.fst, pqspkId := bundle.pqspkId, kemCt := kemCt }
  let honestPeer := isHonestUncorruptedPeer P (st.base.principals.take S.N_dh) bundle.ikB
  let (spkHon, opkHon, pqspkHon) :=
    checkBundleProvenanceTake S P st.base.principals st.base.spkBundles st.base.opkEntries bundle
  let sessEntry : KeyIndInitiatorEntry S :=
    { sid := sid, honestPeer := honestPeer, peerIkPk := bundle.ikB, peerSpkPk := bundle.spkB,
      peerOpkPk? := bundle.opkB?.map Prod.snd, peerPqspkPk := bundle.pqspkB, spkHonest := spkHon,
      opkHonest := opkHon, pqspkHonest := pqspkHon, ekASk := ekASk, fresh := honestPeer.isSome,
      drKeyReal := drKeyReal, drKeyRand := drKeyReal, hdr := hdr, tested := false }
  let drKeyRand ← chooseInitPartnerDrKeyRandPure P st.base.respSessions sessEntry
  let base' : KeyIndState S :=
    { st.base with sessions := { sessEntry with drKeyRand := drKeyRand } :: st.base.sessions }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  let cnt' : Nat := if hasOpk then sendOpkCnt + 1 else sendOpkCnt
  match findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB with
  | some _ => return (.hdrResp hdr, (st', cnt'))
  | none   => return (.initUnfreshResp drKeyReal hdr, (st', cnt'))

@[expose] noncomputable def fgInitiateActivePure (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup) (maxLen : Nat) (U : Bytes) (hasOpk : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  let (resp, (sim', cnt')) ← fgRunInitiateActivePure P ddh dhFlag opkMode ephIdx S maxLen U hasOpk
    sid u bundle stA.st1.sim stA.sendOpkCnt
  return (resp, { stA with st1 := { stA.st1 with sim := sim' }, sendOpkCnt := cnt' })

@[expose] noncomputable def fgKeyInd1KeyActiveStepPure (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (maxLen : Nat) (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    ProbComp (KeyIndResponse × FgKeyInd1KeyActiveSimState S) :=
  match q with
  | .initPrin u => fgInitPrin1KeyActivePure P pa.prinFlag pa.prinIdx pa.Up u stA
  | .genSPK u j => fgGenSPK1KeyActivePure P uSk pa.spkIdx pa.V u j stA
  | .genOPK u j o => fgGenOPKActivePure P pa.opkMode pa.opkIdx pa.V u j o stA
  | .initiateOPK u i bundle =>
    fgInitiateActivePure P ddh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U true (.sendOPK u i) u bundle stA
  | .initiateNoOPK u i bundle =>
    fgInitiateActivePure P ddh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U false (.sendNoOPK u i) u bundle stA
  | .acceptOPK k j o hdr => do
    let (resp, sim') ←
      if pa.opkMode then fgRunAcceptOPKPureOpk P ddh S maxLen k j o hdr stA.st1.sim
      else fgRunAcceptOPKPure P ddh S maxLen k j o hdr stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })
  | q_other => do
    let (resp, sim') ← fgKeyIndStepPure P ddh pa.dhFlag pa.ephIdx pa.spkIdx S maxLen pa.U pa.V q_other stA.st1.sim
    return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

@[expose] noncomputable def fgKeyInd1KeyActiveSimImpl (pa : FgActiveParams) (P : Primitives) (uSk : Bytes)
    (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : Nat) :
    QueryImpl (keyIndSpec S) (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) :=
  fun q => StateT.mk (fgKeyInd1KeyActiveStepPure pa P uSk ddh S maxLen q)

@[expose] def fgKeyInd1KeyActiveFinishPure (pa : FgActiveParams) (S : Setup) (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (maxLen : Nat) (stA : FgKeyInd1KeyActiveSimState S) : Bytes :=
  if pa.mode == 0 then pureExtractCdhFromSimState S P ddh true maxLen pa.U pa.V stA.st1.sim
  else if pa.mode == 1 then pureExtractCdhFromSimState S P ddh false maxLen pa.U pa.V stA.st1.sim
  else if pa.mode == 2 then pureExtractCdh2FromAdvRoLog ddh maxLen pa.U pa.V stA.st1.sim.advRoLog
  else pureExtractCdh4FromAdvRoLog ddh maxLen pa.U pa.V stA.st1.sim.advRoLog

private theorem security_embedPrim_eq : @SignalPqxdh.Security.embedPrim = @SignalPqxdh.Security.FgGapDh.embedPrim := rfl
private theorem security_primQ_eq : @SignalPqxdh.Security.primQ = @SignalPqxdh.Security.FgGapDh.primQ := rfl

private theorem security_findMPrim_eq {α : Type} (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.findMPrim p L = SignalPqxdh.Security.FgGapDh.findMPrim p L := by
  induction L with | nil => rfl | cons _ _ ih => unfold SignalPqxdh.Security.findMPrim SignalPqxdh.Security.FgGapDh.findMPrim; rw [ih]

private theorem security_anyMPrim_eq {α : Type} (p : α → OracleComp SignalPqxdh.PrimBaseSpec Bool) (L : List α) :
    SignalPqxdh.Security.anyMPrim p L = SignalPqxdh.Security.FgGapDh.anyMPrim p L := by
  induction L with | nil => rfl | cons _ _ ih => unfold SignalPqxdh.Security.anyMPrim SignalPqxdh.Security.FgGapDh.anyMPrim; rw [ih]

private theorem security_findHonestPrincipalPrim_eq (S : Setup) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.findHonestPrincipalPrim S principals ikB = SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim S principals ikB := by
  unfold SignalPqxdh.Security.findHonestPrincipalPrim SignalPqxdh.Security.FgGapDh.findHonestPrincipalPrim
  simp only [security_primQ_eq, security_findMPrim_eq]

private theorem security_isHonestUncorruptedPeerPrim_eq (S : Setup) (principals : List (Nat × PrincipalEntry)) (ikB : Bytes) :
    SignalPqxdh.Security.isHonestUncorruptedPeerPrim S principals ikB = SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim S principals ikB := by
  unfold SignalPqxdh.Security.isHonestUncorruptedPeerPrim SignalPqxdh.Security.FgGapDh.isHonestUncorruptedPeerPrim
  rw [security_findHonestPrincipalPrim_eq]; rfl

private theorem security_checkBundleProvenancePrim_eq (S : Setup) (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry)) (opkEntries : List ((Nat × Nat × Nat) × OpkEntry)) (bundle : PreKeyBundleInput) :
    SignalPqxdh.Security.checkBundleProvenancePrim S principals spkBundles opkEntries bundle =
      SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim S principals spkBundles opkEntries bundle := by
  unfold SignalPqxdh.Security.checkBundleProvenancePrim SignalPqxdh.Security.FgGapDh.checkBundleProvenancePrim
  simp only [security_primQ_eq, security_findHonestPrincipalPrim_eq, security_anyMPrim_eq]; rfl

theorem simulateQ_gapDhFullImpl_fgGenSpkActiveGdh {S : Setup} (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (spkIdx : Nat) (V : Bytes) (u : Fin S.N_id)
    (j : Fin S.N_recv) (st : FgKeyIndSimState S) :
    simulateQ (gapDhFullImpl P ddh) (fgGenSpkActiveGdh spkIdx V u j st) = fgGenSpkActivePure P spkIdx V u j st := by
  unfold fgGenSpkActiveGdh fgGenSpkActivePure; dsimp only
  cases st.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.principals.find? (fun x => x.1 == u.val) with
    | none => simp
    | some p => rcases p with ⟨_, _⟩; dsimp only; simp only [simulateQ_bind, simulateQ_gapDhFullImpl_unifGdh,
        simulateQ_gapDhFullImpl_primGdhQ_x25519Base, simulateQ_gapDhFullImpl_primGdhQ_sigSign,
        simulateQ_gapDhFullImpl_primGdhQ_kemKeyGen, pure_bind, simulateQ_pure]
  · simp

theorem simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup)
    (maxLen : Nat) (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    simulateQ (gapDhFullImpl P ddh)
      (fgRunInitiateActiveGdh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle st sendOpkCnt) =
      fgRunInitiateActivePure P ddh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle st sendOpkCnt := by
  unfold fgRunInitiateActiveGdh fgRunInitiateActivePure
  simp only [security_embedPrim_eq, security_findHonestPrincipalPrim_eq,
    security_isHonestUncorruptedPeerPrim_eq, security_checkBundleProvenancePrim_eq]
  cases (!(if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.base.sessions.any (fun e => e.sid == sid)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      cases st.base.principals.find? (fun x => x.1 == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        simp only [simulateQ_bind, simulateQ_gapDhFullImpl_embedPrim,
          simulateQ_primBaseImpl_koskBundleOkPrim, pure_bind]
        by_cases hKosk : (!koskBundleOkTake S P st.base.principals st.base.spkBundles
          st.base.opkEntries st.advKeyPows bundle) = true
        · simp [hKosk]
        · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
            simulateQ_gapDhFullImpl_unifGdh, simulateQ_gapDhFullImpl_embedPrim,
            simulateQ_primBaseImpl_resolveSigPkPrim, simulateQ_gapDhFullImpl_primGdhQ_sigVerify, pure_bind]
          congr 1; ext ekASkRaw; congr 1; ext kemCoins
          by_cases hv : (!(P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P (st.base.principals.take S.N_dh) bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
          · simp [hv]
          · simp only [hv, Bool.false_eq_true, ↓reduceIte, simulateQ_bind,
              simulateQ_gapDhFullImpl_primGdhQ_kemEncaps, pure_bind]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩
              simp only [simulateQ_bind, simulateQ_gapDhFullImpl_primGdhQ_x25519Base,
                simulateQ_gapDhFullImpl_embedPrim, simulateQ_primBaseImpl_lookupSpkSkPrim,
                simulateQ_gapDhFullImpl_computeTwoSideOrPairPos,
                simulateQ_gapDhFullImpl_computeOptPos, simulateQ_gapDhFullImpl_fgPatch,
                simulateQ_gapDhFullImpl_chooseInitPartnerDrKeyRandGdh,
                simulateQ_primBaseImpl_isHonestUncorruptedPeerPrim,
                simulateQ_primBaseImpl_checkBundleProvenancePrim,
                simulateQ_primBaseImpl_findHonestPrincipalPrim, pure_bind]
              congr 1; ext ⟨drKeyReal, fgL'⟩; congr 1; ext drKeyRand
              cases findHonestPrincipal P (st.base.principals.take S.N_dh) bundle.ikB <;> simp
    · simp
  · simp

theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : Nat)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (fgKeyInd1KeyActiveStep pa S maxLen q stA) =
      fgKeyInd1KeyActiveStepPure pa P uSk ddh S maxLen q stA := by
  cases q with
  | initPrin u =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure fgInitPrin1KeyActiveGdh fgInitPrin1KeyActivePure
    dsimp only; cases stA.st1.sim.base.principals.any (fun x => x.1 == u.val) <;> simp
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure fgGenSPK1KeyActiveGdh fgGenSPK1KeyActivePure
    dsimp only; by_cases hPrin : optNatMatches stA.resolvedPrin? u.val = true
    · simp only [hPrin, ↓reduceIte]
      cases stA.st1.sim.base.spkBundles.any (fun x => x.1 == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases stA.st1.sim.base.principals.find? (fun x => x.1 == u.val) with
        | none => simp
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only; by_cases hZero : (stA.st1.sigBudget == 0) = true
          · simp [hZero]
          · simp only [hZero, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_x25519Base, simulateQ_gapDhWithSignFullImpl_sigChalQ,
              simulateQ_gapDhWithSignFullImpl_primGdhSignQ_kemKeyGen, simulateQ_pure, pure_bind, bind_assoc]
      · simp
    · simp only [hPrin, Bool.false_eq_true, ↓reduceIte, liftSimStep1KeyActive, simulateQ_bind,
        simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgGenSpkActiveGdh, simulateQ_pure]
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure fgGenOPKActiveGdh fgGenOPKActivePure
    dsimp only; cases stA.st1.sim.base.opkEntries.any (fun x => x.1 == (u.val, j.val, o.val)) <;> simp
  | initiateOPK u i bundle =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure, fgInitiateActiveGdh, fgInitiateActivePure,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh, simulateQ_pure]
  | initiateNoOPK u i bundle =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure, fgInitiateActiveGdh, fgInitiateActivePure,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgRunInitiateActiveGdh, simulateQ_pure]
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveStep fgKeyInd1KeyActiveStepPure liftSimStep1KeyActive
    cases pa.opkMode <;> simp [simulateQ_gapDhWithSignFullImpl_liftGdhToSign,
      simulateQ_gapDhFullImpl_fgRunAcceptOPKGdh, simulateQ_gapDhFullImpl_fgRunAcceptOPKGdhOpk]
  | _ =>
    simp only [fgKeyInd1KeyActiveStep, fgKeyInd1KeyActiveStepPure, liftSimStep1KeyActive,
      simulateQ_bind, simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_fgKeyIndStep, simulateQ_pure]

theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveFinish (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool) (S : Setup) (maxLen : Nat)
    (stA : FgKeyInd1KeyActiveSimState S) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (fgKeyInd1KeyActiveFinish pa S maxLen stA) =
      pure (fgKeyInd1KeyActiveFinishPure pa S P ddh maxLen stA) := by
  unfold fgKeyInd1KeyActiveFinish fgKeyInd1KeyActiveFinishPure; split_ifs <;>
    simp [simulateQ_gapDhWithSignFullImpl_liftGdhToSign, simulateQ_gapDhFullImpl_extractCdhFromSimState,
      simulateQ_gapDhFullImpl_extractCdh2FromAdvRoLog, simulateQ_gapDhFullImpl_extractCdh4FromAdvRoLog]

theorem simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams (pa : FgActiveParams)
    (P : Primitives) (uSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    simulateQ (gapDhWithSignFullImpl P uSk ddh) (fgKeyInd1KeyActiveRunWithParams pa S b A) =
    (do
      let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) + fgKeyInd1KeyActiveSimImpl pa P uSk ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run (FgKeyInd1KeyActiveSimState.empty S b secb)
      return fgKeyInd1KeyActiveFinishPure pa S P ddh b.q_total finalSt) := by
  unfold fgKeyInd1KeyActiveRunWithParams; dsimp only
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_unifGdhSign]; congr 1; funext secb
  rw [simulateQ_bind, simulateQ_gapDhWithSignFullImpl_runWithGdhSignStep P uSk ddh _ _
    (simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveStep pa P uSk ddh S b.q_total)]
  congr 1; funext ⟨_, finalSt⟩; rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveFinish]

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAt_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes) (useDh1 : Bool) (ord1 spkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAt useDh1 ord1 spkOrd S b A) =
    (do
      let u ← sampleScalar32; let v ← sampleScalar32; let U := P.x25519Base u; let V := P.x25519Base v
      let pa := if useDh1 then activeParamsDh1 b U V ord1 spkOrd else activeParamsDh3 b U V ord1 spkOrd
      let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) + fgKeyInd1KeyActiveSimImpl pa P u ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run (FgKeyInd1KeyActiveSimState.empty S b secb)
      return (pow8 (fgKeyInd1KeyActiveFinishPure pa S P ddh b.q_total finalSt) == pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdvAt; congr 1; funext u; congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh) (fgKeyInd1KeyActiveRunWithParams _ S b A) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams]; simp only [bind_assoc, pure_bind]

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAtIk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes) (ephOrd prinOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAtIk ephOrd prinOrd S b A) =
    (do
      let u ← sampleScalar32; let v ← sampleScalar32; let U := P.x25519Base u; let V := P.x25519Base v
      let pa := activeParamsDh2 b U V ephOrd prinOrd; let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) + fgKeyInd1KeyActiveSimImpl pa P u ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run (FgKeyInd1KeyActiveSimState.empty S b secb)
      return (pow8 (pureExtractCdh2FromAdvRoLog ddh b.q_total V U finalSt.st1.sim.advRoLog) == pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdvAtIk; congr 1; funext u; congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh) (fgKeyInd1KeyActiveRunWithParams _ S b A) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams]
  simp only [bind_assoc, pure_bind, fgKeyInd1KeyActiveFinishPure, activeParamsDh2]; rfl

theorem gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAtOpk_eq (P : Primitives)
    (ddh : Bytes → Bytes → Bytes → Bool) (pow8 : Bytes → Bytes) (ephOpkOrd opkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) :
    gapDhWithSignExp P ddh pow8 (fgKeyInd1KeyGapDhActiveAdvAtOpk ephOpkOrd opkOrd S b A) =
    (do
      let u ← sampleScalar32; let v ← sampleScalar32; let U := P.x25519Base u; let V := P.x25519Base v
      let pa := activeParamsDh4 b U V ephOpkOrd opkOrd; let secb ← $ᵗ Bool
      let impl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
          (StateT (FgKeyInd1KeyActiveSimState S) ProbComp) + fgKeyInd1KeyActiveSimImpl pa P u ddh S b.q_total
      let (_, finalSt) ← (simulateQ impl A.1.run).run (FgKeyInd1KeyActiveSimState.empty S b secb)
      return (pow8 (pureExtractCdh4FromAdvRoLog ddh b.q_total U V finalSt.st1.sim.advRoLog) == pow8 (P.x25519 u V))) := by
  unfold gapDhWithSignExp fgKeyInd1KeyGapDhActiveAdvAtOpk; congr 1; funext u; congr 1; funext v
  change (simulateQ (gapDhWithSignFullImpl P u ddh) (fgKeyInd1KeyActiveRunWithParams _ S b A) >>=
    fun Z => pure (pow8 Z == pow8 (P.x25519 u (P.x25519Base v)))) = _
  rw [simulateQ_gapDhWithSignFullImpl_fgKeyInd1KeyActiveRunWithParams]
  simp only [bind_assoc, pure_bind, fgKeyInd1KeyActiveFinishPure, activeParamsDh4]; rfl

/-! ## Dynamic slot retargeting and per-ordinal `DH2` bound -/

theorem evalDist_simulateQ_eq_zero_of_dead_preserved_inv {ι α St : Type}
    {QSpec : OracleSpec.{0, 0} ι} (Inv : St → Prop) (Dead : St → Bool)
    (impl : QueryImpl QSpec (StateT St ProbComp))
    (hInvPres : ∀ q st, Inv st → ∀ x ∈ support ((impl q).run st), Inv x.2)
    (hPres : ∀ q st, Inv st → Dead st = true → ∀ x ∈ support ((impl q).run st), Dead x.2 = true)
    (obs : α × St → ProbComp Bool)
    (hObs : ∀ a st, Inv st → Dead st = true → 𝒟[obs (a, st)] {true} = 0)
    (oa : OracleComp (unifSpec + QSpec) α) (st : St) (hInv : Inv st) (hDead : Dead st = true) :
    let full := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St ProbComp) + impl
    𝒟[(simulateQ full oa).run st >>= obs] {true} = 0 := by
  intro full; induction oa using OracleComp.inductionOn generalizing st with
  | pure a => simp only [simulateQ_pure, StateT.run_pure, pure_bind]; exact hObs a st hInv hDead
  | query_bind q mx ih =>
    rcases q with uq | gq
    · dsimp only [full]; rw [simulateQ_run_query_inl, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun u _ => ih u st hInv hDead)
    · dsimp only [full]; rw [simulateQ_run_query_inr, bind_assoc]
      exact evalDist_bind_true_eq_zero_of_support _ _ (fun x hx =>
        ih x.1 x.2 (hInvPres gq st hInv x hx) (hPres gq st hInv hDead x hx))

theorem evalDist_simulateQ_le_of_step_or_dead_inv {ι α St1 St2 : Type}
    {QSpec : OracleSpec.{0, 0} ι} (Inv1 : St1 → Prop) (Dead : St1 → Bool)
    (Rel : ℕ → St1 → St2 → Prop) (impl1 : QueryImpl QSpec (StateT St1 ProbComp))
    (impl2 : QueryImpl QSpec (StateT St2 ProbComp))
    (hInvPres : ∀ q s1, Inv1 s1 → ∀ x ∈ support ((impl1 q).run s1), Inv1 x.2)
    (hDeadPres : ∀ q s1, Inv1 s1 → Dead s1 = true → ∀ x ∈ support ((impl1 q).run s1), Dead x.2 = true)
    (hStep : ∀ (q : ι) (rem : ℕ) (s1 : St1) (s2 : St2),
      Inv1 s1 → Dead s1 = false → Rel (rem + 1) s1 s2 →
      ∀ (k1 : QSpec.Range q × St1 → ProbComp Bool) (k2 : QSpec.Range q × St2 → ProbComp Bool),
        (∀ r s1' s2', Inv1 s1' → Dead s1' = false → Rel rem s1' s2' →
          𝒟[k1 (r, s1')] {true} ≤ 𝒟[k2 (r, s2')] {true}) →
        (∀ r s1', Inv1 s1' → Dead s1' = true → 𝒟[k1 (r, s1')] {true} = 0) →
        𝒟[(impl1 q).run s1 >>= k1] {true} ≤ 𝒟[(impl2 q).run s2 >>= k2] {true})
    (obs1 : α × St1 → ProbComp Bool) (obs2 : α × St2 → ProbComp Bool)
    (hDeadObs : ∀ a s1, Inv1 s1 → Dead s1 = true → 𝒟[obs1 (a, s1)] {true} = 0)
    (hObs : ∀ a rem s1 s2, Inv1 s1 → Dead s1 = false → Rel rem s1 s2 →
      𝒟[obs1 (a, s1)] {true} ≤ 𝒟[obs2 (a, s2)] {true})
    (oa : OracleComp (unifSpec + QSpec) α) (rem : ℕ)
    (hQb : IsQueryBoundP oa (fun q : ℕ ⊕ ι => isGameQuery q = true) rem)
    (s1 : St1) (s2 : St2) (hInv1 : Inv1 s1) (hRel : Rel rem s1 s2) :
    let full1 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St1 ProbComp) + impl1
    let full2 := (QueryImpl.ofLift unifSpec ProbComp).liftTarget (StateT St2 ProbComp) + impl2
    𝒟[(simulateQ full1 oa).run s1 >>= obs1] {true} ≤
      𝒟[(simulateQ full2 oa).run s2 >>= obs2] {true} := by
  intro full1 full2; induction oa using OracleComp.inductionOn generalizing rem s1 s2 with
  | pure a =>
    by_cases hD : Dead s1 = true
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind, hDeadObs a s1 hInv1 hD, zero_le]
    · simp only [simulateQ_pure, StateT.run_pure, pure_bind]
      exact hObs a rem s1 s2 hInv1 (Bool.eq_false_iff.mpr hD) hRel
  | query_bind q mx ih =>
    by_cases hD : Dead s1 = true
    · rw [evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres hDeadPres obs1
        hDeadObs _ s1 hInv1 hD]; exact zero_le
    · have hDF : Dead s1 = false := Bool.eq_false_iff.mpr hD
      rw [isQueryBoundP_query_bind_iff] at hQb
      rcases q with uq | gq
      · rcases hQb with ⟨_, hCont⟩; simp only [isGameQuery, Bool.false_eq_true, ↓reduceIte] at hCont
        dsimp only [full1, full2]; rw [simulateQ_run_query_inl, simulateQ_run_query_inl, bind_assoc, bind_assoc]
        exact evalDist_bind_true_mono_of_support _ _ _ (fun u _ => ih u rem (hCont u) s1 s2 hInv1 hRel)
      · rcases hQb with ⟨hAbs | hPos, hCont⟩
        · exfalso; exact hAbs rfl
        · obtain ⟨rem', rfl⟩ : ∃ rem', rem = rem' + 1 := ⟨rem - 1, by omega⟩
          simp only [isGameQuery, ↓reduceIte, Nat.add_sub_cancel] at hCont
          dsimp only [full1, full2]; rw [simulateQ_run_query_inr, simulateQ_run_query_inr, bind_assoc, bind_assoc]
          let k1' : QSpec.Range gq × St1 → ProbComp Bool := open scoped Classical in
            fun x => if Inv1 x.2 then (simulateQ full1 (mx x.1)).run x.2 >>= obs1 else pure false
          have hLhsEq : 𝒟[(impl1 gq).run s1 >>= fun x =>
              (simulateQ full1 (mx x.1)).run x.2 >>= obs1] = 𝒟[(impl1 gq).run s1 >>= k1'] :=
            OracleComp.evalDist_bind_congr_of_support _ _ _ (fun x hx => by
              simp only [k1', hInvPres gq s1 hInv1 x hx, ↓reduceIte])
          rw [hLhsEq]
          exact hStep gq rem' s1 s2 hInv1 hDF hRel k1'
            (fun x => (simulateQ full2 (mx x.1)).run x.2 >>= obs2)
            (fun r s1' s2' hI' _ hR => by simp only [k1', hI', ↓reduceIte]; exact ih r rem' (hCont r) s1' s2' hI' hR)
            (fun r s1' hI' hD' => by
              simp only [k1', hI', ↓reduceIte]
              exact evalDist_simulateQ_eq_zero_of_dead_preserved_inv Inv1 Dead impl1 hInvPres
                hDeadPres obs1 hDeadObs (mx r) s1' hI' hD')

private theorem fgPreInitiate_sid_mem {S : Setup} (useDh1 : Bool) (sIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : KeyIndState S) (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((fgPreInitiate useDh1 sIdx optUsk S P sid u bundle).run st)) :
    ∀ s ∈ x.2.sessions, s ∈ st.sessions ∨ s.sid = sid := by
  unfold fgPreInitiate at hx; simp only [StateT.run_bind, StateT.run_get, pure_bind] at hx; revert hx
  cases st.sessions.any (fun e => e.sid == sid)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
    | some p =>
      rcases p with ⟨_, _⟩; dsimp only; cases koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle
      · simp only [Bool.not_false, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]
        intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, StateT.run_bind,
          StateT.run_monadLift, monadLift_self, bind_assoc, pure_bind, MonadAttach.mem_support_bind]
        rintro ⟨_, _, _, _, hb⟩; revert hb; split_ifs
        · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
        · cases P.kemEncaps bundle.pqspkB _ with
          | none => simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs
          | some sc =>
            rcases sc with ⟨_, _⟩; dsimp only
            simp only [StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set, bind_assoc, pure_bind, MonadAttach.mem_support_bind]
            rintro ⟨⟨_, _⟩, _, _, _, hb⟩; revert hb; cases findHonestPrincipal P st.principals bundle.ikB <;>
            · simp only [StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs
              exact (List.mem_cons.mp hs).elim (fun h => Or.inr (h ▸ rfl)) Or.inl
  · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq s hs; rw [(Prod.mk.inj hEq).2] at hs; exact Or.inl hs

private theorem initSessionSlotIdx_lt_of_isSendSessionId {S : Setup} (sid : SessionId S)
    (hSend : IsSendSessionId S sid) : initSessionSlotIdx sid < S.N_send_tot := by
  cases sid with
  | sendOPK u i => have := initSessionSlotIdx_sendOPK_lt u i; unfold Setup.N_send_tot; omega
  | sendNoOPK u i => exact initSessionSlotIdx_sendNoOPK_lt u i
  | recvOPK _ _ _ => cases hSend
  | recvNoOPK _ _ _ => cases hSend

private theorem mem_support_pqxdhKeyIndFgImpl_base {S : Setup} (P : Primitives) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgImpl S P q).run hst)) :
    (x.1, x.2.base) ∈ support ((pqxdhKeyIndImpl true S P q).run hst.base) := by
  cases q <;>
  · dsimp only [pqxdhKeyIndFgImpl, StateT_run_mk] at hx; rw [MonadAttach.mem_support_bind] at hx
    rcases hx with ⟨⟨r, b'⟩, hb, hEq⟩; rw [support_pure, Set.mem_singleton_iff] at hEq; cases hEq; exact hb

private theorem fgPreInitiate_elim_sid {S : Setup} (useDh1 : Bool) (sIdx : ℕ) (optUsk : Option Bytes)
    (P : Primitives) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : KeyIndState S) (x : KeyIndResponse × KeyIndState S)
    (hx : x ∈ support ((fgPreInitiate useDh1 sIdx optUsk S P sid u bundle).run st)) :
    x.2 = st ∨ ∃ s roCache', s.sid = sid ∧ st.sessions.any (fun e => e.sid == sid) = false ∧
      x.2 = { st with roCache := roCache', sessions := s :: st.sessions } :=
  mem_support_fgPreInitiate_elim useDh1 sIdx optUsk P sid u bundle st x hx Or.inl fun s ro' hAnyF hEq => by
    have hSid : s.sid = sid := (fgPreInitiate_sid_mem useDh1 sIdx optUsk P sid u bundle st x hx s
      (by rw [hEq]; exact List.mem_cons_self)).elim (fun hMem => False.elim (Bool.false_ne_true
        (hAnyF.symm.trans (List.any_eq_true.mpr ⟨s, hMem, beq_self_eq_true _⟩)))) id
    exact Or.inr ⟨s, ro', hSid, hSid ▸ hAnyF, hEq⟩

theorem pqxdhKeyIndFgPreImpl_preserves_validKeyIndEc {S : Setup} (targetIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (q : KeyIndQuery S) (hq : ∀ u, q ≠ .initPrin u)
    (hst : KeyIndFgCutoffState S) (hV : ValidKeyIndEc S hst.base)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl false targetIdx S.N_spk_tot optUsk none S P q).run hst)) :
    ValidKeyIndEc S x.2.base := by
  have hInitHelper : ∀ (sid : SessionId S), IsSendSessionId S sid → ∀ (u : Fin S.N_id) (bundle : PreKeyBundleInput),
      (x.1, x.2.base) ∈ support ((fgPreInitiate false targetIdx optUsk S P sid u bundle).run hst.base) →
      ValidKeyIndEc S x.2.base := fun sid hSend u bundle hb => by
    rcases fgPreInitiate_elim_sid false targetIdx optUsk P sid u bundle hst.base (x.1, x.2.base) hb with hEq | ⟨s, _, hSid, hAnyF, hEq⟩
    · dsimp only at hEq; rw [hEq]; exact hV
    · dsimp only at hEq
      have hAnyMap : ((sessPksKeyInd S hst.base).map Prod.fst).any (· == s.sid) = false := by
        rw [hSid]; simpa [sessPksKeyInd, List.any_map, Function.comp_def] using hAnyF
      refine ⟨by rw [hEq]; exact hV.1, by rw [hEq]; exact hV.2.1, by rw [hEq]; exact hV.2.2.1, ?_⟩
      have hSidsEq : (sessPksKeyInd S x.2.base).map Prod.fst = s.sid :: (sessPksKeyInd S hst.base).map Prod.fst := by
        rw [hEq]; simp [sessPksKeyInd]
      rw [hSidsEq]; exact (validSessionIds_cons S s.sid _ (hSid ▸ hSend) hV.2.2.2 hAnyMap).1
  cases q with
  | initPrin u => exact absurd rfl (hq u)
  | genSPK u j =>
    unfold pqxdhKeyIndFgPreImpl fgPreGenSPK at hx; rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
    cases hAny : hst.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
    · simp only [hAny, Bool.false_eq_true, ↓reduceIte] at hb
      cases hF : hst.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp only [hF, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb; rw [(Prod.mk.inj hb).2]; exact hV
      | some p =>
        rcases p with ⟨_, _⟩; simp only [hF, StateT.run_bind, StateT.run_monadLift, monadLift_self, StateT.run_set,
          StateT.run_pure, bind_assoc, pure_bind, MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb
        rcases hb with ⟨_, _, _, _, _, _, _, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
        exact ⟨by rw [hB]; exact hV.1, by rw [hB]; exact (validSpkBundles_cons S u j _ _ hV.2.1 hAny).1,
          by rw [hB]; exact hV.2.2.1, by unfold sessPksKeyInd; rw [hB]; exact hV.2.2.2⟩
    · simp only [hAny, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb; rw [(Prod.mk.inj hb).2]; exact hV
  | initiateOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl at hx; rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb; cases bundle.opkB?.isNone
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hInitHelper (.sendOPK u i) trivial u bundle
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq; rw [(Prod.mk.inj hEq).2]; exact hV
  | initiateNoOPK u i bundle =>
    unfold pqxdhKeyIndFgPreImpl at hx; rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
    simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb; revert hb; cases bundle.opkB?.isSome
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact hInitHelper (.sendNoOPK u i) trivial u bundle
    · simp only [↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff]; intro hEq; rw [(Prod.mk.inj hEq).2]; exact hV
  | _ => exact pqxdhKeyIndImpl_validKeyIndEc_step true S P _ hst.base hV (x.1, x.2.base) (mem_support_pqxdhKeyIndFgImpl_base P _ hst x hx)

private theorem fgPreInitPrin1Key_elim {S : Setup} (useDh1 : Bool) (kIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((liftFgBase (fgPreInitPrin1Key useDh1 kIdx optUsk S P u)).run hst)) :
    x.2.base = hst.base ∨ (hst.base.principals.any (fun (idx, _) => idx == u.val) = false ∧
      ∃ sk ∈ support (match optUsk with
        | some s => if useDh1 && (u.val == kIdx) then pure s else sampleScalar32
        | none => sampleScalar32),
        let pk := P.x25519Base sk
        x.2.base = { hst.base with principals := (u.val,
          { secIKA0 := sk, ikAPk := pk, secIKAsign := sk, ikSignPk := pk, corrupted := false }) ::
          hst.base.principals }) := by
  unfold fgPreInitPrin1Key at hx; rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hb
  cases hAny : hst.base.principals.any (fun (idx, _) => idx == u.val)
  · simp only [hAny, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, StateT.run_monadLift,
      monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc, pure_bind,
      MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb
    rcases hb with ⟨sk, hSk, hEq⟩; exact Or.inr ⟨rfl, sk, hSk, (Prod.mk.inj hEq).2⟩
  · simp only [hAny, ↓reduceIte, StateT.run_pure, support_pure, Set.mem_singleton_iff] at hb
    exact Or.inl (Prod.mk.inj hb).2

theorem fgPreInitPrin1Key_preserves_validKeyIndEc {S : Setup} (useDh1 : Bool) (kIdx : ℕ)
    (optUsk : Option Bytes) (P : Primitives) (u : Fin S.N_id) (hst : KeyIndFgCutoffState S)
    (hV : ValidKeyIndEc S hst.base) (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((liftFgBase (fgPreInitPrin1Key useDh1 kIdx optUsk S P u)).run hst)) :
    ValidKeyIndEc S x.2.base := by
  rcases fgPreInitPrin1Key_elim useDh1 kIdx optUsk P u hst x hx with hB | ⟨hAny, _, _, hB⟩
  · rw [hB]; exact hV
  · exact ⟨by rw [hB]; exact (validPrincipals_cons S u _ hst.base.principals hV.1 hAny).1,
      by rw [hB]; exact hV.2.1, by rw [hB]; exact hV.2.2.1, by unfold sessPksKeyInd; rw [hB]; exact hV.2.2.2⟩

private theorem pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc {S : Setup}
    (sOrd pOrd : ℕ) (ikSk ekSk : Bytes) (P : Primitives) (q : KeyIndQuery S)
    (hst : KeyIndFgCutoffState S) (hV : ValidKeyIndEc S hst.base)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst)) :
    ValidKeyIndEc S x.2.base := by
  dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdIk, StateT_run_mk] at hx
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with | initPrin u => exact Or.inl ⟨u, rfl⟩ | _ => exact Or.inr (fun _ h => by cases h)
  rcases hInitOrNe with ⟨u, rfl⟩ | hNe
  · exact fgPreInitPrin1Key_preserves_validKeyIndEc true _ (some ikSk) P u hst hV x hx
  · rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNe,
      pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNe] at hx
    exact pqxdhKeyIndFgPreImpl_preserves_validKeyIndEc _ (some ekSk) P q hNe hst hV x hx

private theorem pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_deadDh2 {S : Setup} (P : Primitives)
    (sOrd pOrd : ℕ) (ikSk ekSk : Bytes) (q : KeyIndQuery S) (hst : KeyIndFgCutoffState S)
    (hV : ValidKeyIndEc S hst.base)
    (hDead : deadDh2 P (sessSlotAtOrd S hst.base sOrd) (prinSlotAtOrd S hst.base pOrd) (P.x25519Base ikSk) hst = true)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst)) :
    deadDh2 P (sessSlotAtOrd S x.2.base sOrd) (prinSlotAtOrd S x.2.base pOrd) (P.x25519Base ikSk) x.2 = true := by
  have hVx := pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc sOrd pOrd ikSk ekSk P q hst hV x hx
  set s0 := sessSlotAtOrd S hst.base sOrd; set k0 := prinSlotAtOrd S hst.base pOrd; set V := P.x25519Base ikSk
  have hSamePS : x.2.base.principals = hst.base.principals → x.2.base.sessions = hst.base.sessions →
      deadDh2 P (sessSlotAtOrd S x.2.base sOrd) (prinSlotAtOrd S x.2.base pOrd) V x.2 = true := fun hP hSe => by
    have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hP]
    have hsEq : sessSlotAtOrd S x.2.base sOrd = s0 := by simp only [s0, sessSlotAtOrd, hSe]
    rw [hkEq, hsEq, deadDh2_eq_of_prin_sess P s0 k0 V hP (by rw [hSe])]; exact hDead
  have hDead0 := hDead; unfold deadDh2 at hDead0; rcases Bool.and_eq_true_iff.mp hDead0 with ⟨hPV, hOr⟩
  dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdIk, StateT_run_mk] at hx
  have hInitOrNe : (∃ u, q = .initPrin u) ∨ (∀ u, q ≠ .initPrin u) := by
    cases q with | initPrin u => exact Or.inl ⟨u, rfl⟩ | _ => exact Or.inr (fun _ h => by cases h)
  rcases Bool.or_eq_true_iff.mp hOr with hD1 | hSD
  · have hD1' := hD1; unfold deadDh1 at hD1'
    cases hFP : hst.base.principals.find? (fun (idx, _) => idx == k0) with
    | none => rw [hFP] at hD1'; cases hD1'
    | some p0 =>
      rcases p0 with ⟨u0, e0⟩
      have hu0Mem : (u0, e0) ∈ hst.base.principals := List.mem_of_find?_eq_some hFP
      have hu0Eq : u0 = k0 := beq_iff_eq.mp (List.find?_some (p := fun (kv : Nat × PrincipalEntry) => kv.1 == k0) hFP)
      have hk0Lt : k0 < S.N_id := hu0Eq ▸ hV.1.1 (u0, e0) hu0Mem
      have hpLt : pOrd < hst.base.principals.length := Nat.lt_of_not_ge fun hGe => by
        have hEqN : k0 = S.N_id := by dsimp only [k0]; rw [prinSlotAtOrd_eq]; exact ordLookup_of_ge hGe
        omega
      rcases hInitOrNe with ⟨u, rfl⟩ | hNe
      · rcases fgPreInitPrin1Key_elim true _ (some ikSk) P u hst x hx with hB | ⟨hAny, sk, _, hB⟩
        · exact hSamePS (by rw [hB]) (by rw [hB])
        · have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by
            rw [prinSlotAtOrd_eq, hB]; dsimp only; rw [ordLookup_cons_of_lt _ _ _ hpLt, ← prinSlotAtOrd_eq]
          have hNeU : (u.val == k0) = false := Bool.eq_false_iff.mpr fun hEqU => Bool.false_ne_true
            (hAny.symm.trans (List.any_eq_true.mpr ⟨(u0, e0), hu0Mem, beq_iff_eq.mpr (hu0Eq.trans (beq_iff_eq.mp hEqU).symm)⟩))
          have hPVx : prinTargetIsV k0 V x.2 = true := by
            unfold prinTargetIsV at hPV ⊢; rw [hB]; dsimp only; rw [List.all_cons, hPV, Bool.and_true]; simp [hNeU]
          have hD1x : deadDh1 k0 x.2 = true := by
            unfold deadDh1; rw [hB]; dsimp only [List.find?]; rw [hNeU, hFP]; rw [hFP] at hD1'; exact hD1'
          unfold deadDh2; rw [hkEq]; simp [hPVx, hD1x]
      · rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNe,
          pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNe] at hx
        have hSameP : x.2.base.principals = hst.base.principals →
            deadDh2 P (sessSlotAtOrd S x.2.base sOrd) (prinSlotAtOrd S x.2.base pOrd) V x.2 = true := fun hP => by
          have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hP]
          have hPVx : prinTargetIsV k0 V x.2 = true := by unfold prinTargetIsV at hPV ⊢; rw [hP]; exact hPV
          have hD1x : deadDh1 k0 x.2 = true := by rw [deadDh1_eq_of_principals k0 hP]; exact hD1
          unfold deadDh2; rw [hkEq]; simp [hPVx, hD1x]
        exact mem_support_pqxdhKeyIndFgPreImpl_elim false _ _ (some ekSk) none P q hst x hx
          (fun hP _ _ _ => hSameP hP) (fun u _ hEq _ _ => absurd hEq (hNe u))
          (fun u _ _ _ _ hB => by
            have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by
              rw [prinSlotAtOrd_eq, hB]; dsimp only; rw [ordLookup_map_eq (fun ⟨idx, e⟩ => by split_ifs <;> rfl), ← prinSlotAtOrd_eq]
            have hPVx : prinTargetIsV k0 V x.2 = true := by
              unfold prinTargetIsV at hPV ⊢; rw [hB]; dsimp only; rw [List.all_map]
              refine List.all_eq_true.mpr fun ⟨idx, e⟩ hMem => ?_
              have hOld := List.all_eq_true.mp hPV (idx, e) hMem; dsimp only [Function.comp_def] at hOld ⊢; split_ifs <;> exact hOld
            unfold deadDh2; rw [hkEq]; simp [hPVx, deadDh1_mono_map_corrupted k0 u.val (by rw [hB]) hD1])
          (fun _ _ _ _ _ _ _ hB => hSameP (by rw [hB])) (fun _ _ _ _ _ _ _ hB => hSameP (by rw [hB]))
          (fun _ _ _ hB => hSameP (by rw [hB])) (fun _ _ _ hP _ _ _ => hSameP hP)
          (fun _ _ _ _ _ hP _ _ _ => hSameP hP) (fun _ _ hB => hSameP (by rw [hB]))
  · have hSD' := hSD; unfold sessDeadIk at hSD'
    cases hFS : hst.base.sessions.find? (fun s => initSessionSlotIdx s.sid == s0) with
    | none => rw [hFS] at hSD'; cases hSD'
    | some se0 =>
      have hse0Mem : se0 ∈ hst.base.sessions := List.mem_of_find?_eq_some hFS
      have hse0Eq : initSessionSlotIdx se0.sid = s0 :=
        beq_iff_eq.mp (List.find?_some (p := fun s : KeyIndInitiatorEntry S => initSessionSlotIdx s.sid == s0) hFS)
      have hs0Lt : s0 < S.N_send_tot := hse0Eq ▸ initSessionSlotIdx_lt_of_isSendSessionId se0.sid
        (hV.2.2.2.1 se0.sid (by simp only [sessPksKeyInd, List.map_map]; exact List.mem_map.mpr ⟨se0, hse0Mem, rfl⟩))
      have hsLt : sOrd < hst.base.sessions.length := Nat.lt_of_not_ge fun hGe => by
        have hEqN : s0 = S.N_send_tot := by dsimp only [s0]; rw [sessSlotAtOrd_eq]; exact ordLookup_of_ge hGe
        omega
      rcases hInitOrNe with ⟨u, rfl⟩ | hNe
      · rcases fgPreInitPrin1Key_elim true _ (some ikSk) P u hst x hx with hB | ⟨hAny, sk, hSk, hB⟩
        · exact hSamePS (by rw [hB]) (by rw [hB])
        · have hsEq : sessSlotAtOrd S x.2.base sOrd = s0 := by simp only [s0, sessSlotAtOrd, hB]
          have hSDx : sessDeadIk P s0 V x.2 = true := by unfold sessDeadIk at hSD ⊢; rw [hB]; exact hSD
          have hPVx : prinTargetIsV (prinSlotAtOrd S x.2.base pOrd) V x.2 = true := by
            rcases lt_trichotomy pOrd hst.base.principals.length with hpLt | hpEq | hpGt
            · have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by
                rw [prinSlotAtOrd_eq, hB]; dsimp only; rw [ordLookup_cons_of_lt _ _ _ hpLt, ← prinSlotAtOrd_eq]
              obtain ⟨⟨u1, e1⟩, hMem1, hu1Eq⟩ := ordLookup_mem_of_lt (proj := Prod.fst) (dflt := S.N_id) hpLt
              have hNeU : (u.val == k0) = false := Bool.eq_false_iff.mpr fun hEqU => Bool.false_ne_true
                (hAny.symm.trans (List.any_eq_true.mpr ⟨(u1, e1), hMem1,
                  beq_iff_eq.mpr ((by dsimp only [k0]; rw [prinSlotAtOrd_eq, hu1Eq] : k0 = u1).symm.trans (beq_iff_eq.mp hEqU).symm)⟩))
              rw [hkEq]; unfold prinTargetIsV at hPV ⊢; rw [hB]; dsimp only; rw [List.all_cons, hPV, Bool.and_true]; simp [hNeU]
            · subst hpEq
              have hkEq : prinSlotAtOrd S x.2.base hst.base.principals.length = u.val := by
                rw [prinSlotAtOrd_eq, hB]; dsimp only; exact ordLookup_cons_eq _ _ _ _
              have hCur : (u.val == curPrinSlot hst.base.principals.length (.initPrin u) hst) = true := by simp [curPrinSlot]
              simp only [hCur, Bool.true_and, ↓reduceIte, support_pure, Set.mem_singleton_iff] at hSk
              subst hSk; rw [hkEq]; unfold prinTargetIsV; rw [hB]; dsimp only [V]
              rw [List.all_cons]; simp only [beq_self_eq_true, Bool.or_true, Bool.true_and]
              refine List.all_eq_true.mpr fun ⟨idx, e⟩ hMem => ?_
              simp [Bool.eq_false_iff.mpr fun hEqI => Bool.false_ne_true (hAny.symm.trans (List.any_eq_true.mpr ⟨(idx, e), hMem, hEqI⟩))]
            · have hkEq : prinSlotAtOrd S x.2.base pOrd = S.N_id := by
                rw [prinSlotAtOrd_eq]; exact ordLookup_of_ge (by rw [hB]; dsimp only [List.length_cons]; omega)
              rw [hkEq]; unfold prinTargetIsV; exact List.all_eq_true.mpr fun ⟨idx, e⟩ hMem =>
                by simp [beq_eq_false_iff_ne.mpr (Nat.ne_of_lt (hVx.1.1 (idx, e) hMem))]
          unfold deadDh2; rw [hsEq]; simp [hPVx, hSDx]
      · rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNe,
          pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNe] at hx
        exact mem_support_pqxdhKeyIndFgPreImpl_elim false _ _ (some ekSk) none P q hst x hx
          (fun hP _ _ hSe => hSamePS hP hSe) (fun u _ hEq _ _ => absurd hEq (hNe u))
          (fun u _ _ _ _ hB => by
            have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by
              rw [prinSlotAtOrd_eq, hB]; dsimp only; rw [ordLookup_map_eq (fun ⟨idx, e⟩ => by split_ifs <;> rfl), ← prinSlotAtOrd_eq]
            have hsEq : sessSlotAtOrd S x.2.base sOrd = s0 := by simp only [s0, sessSlotAtOrd, hB]
            rw [hkEq, hsEq]; exact deadDh2_map_corrupted P s0 k0 u.val V (by rw [hB]) (by rw [hB]) hDead)
          (fun _ _ _ _ _ _ _ hB => hSamePS (by rw [hB]) (by rw [hB])) (fun _ _ _ _ _ _ _ hB => hSamePS (by rw [hB]) (by rw [hB]))
          (fun s _ hAnyS hB => by
            have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hB]
            have hsEq : sessSlotAtOrd S x.2.base sOrd = s0 := by
              rw [sessSlotAtOrd_eq, hB]; dsimp only; rw [ordLookup_cons_of_lt _ _ _ hsLt, ← sessSlotAtOrd_eq]
            rw [hkEq, hsEq]; exact deadDh2_sess_cons P s0 k0 hs0Lt V s (by rw [hB]) (by rw [hB]) hAnyS hDead)
          (fun _ _ _ hP _ hSe _ => hSamePS hP hSe)
          (fun f hSid hPeer _ _ hP _ _ hSe => by
            have hkEq : prinSlotAtOrd S x.2.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hP]
            have hsEq : sessSlotAtOrd S x.2.base sOrd = s0 := by
              rw [sessSlotAtOrd_eq, hSe, ordLookup_map_eq (f := f)
                (proj := fun s => initSessionSlotIdx s.sid) (fun s => congrArg initSessionSlotIdx (hSid s)), ← sessSlotAtOrd_eq]
            rw [hkEq, hsEq]; exact deadDh2_sess_map P s0 k0 V f hSid hPeer hP hSe hDead)
          (fun _ _ hB => hSamePS (by rw [hB]) (by rw [hB]))

private theorem fgSimInvDh2_1Key_retarget_prin {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {sIdx k2 rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {st1 : FgKeyInd1KeySimState S}
    (hAbs2 : ∀ kv ∈ hst.base.principals, kv.1 ≠ k2)
    (hInv : FgSimInvDh2_1Key S b P hP sIdx S.N_id ikSk ekSk hikSk hekSk rem hst st1) :
    FgSimInvDh2_1Key S b P hP sIdx k2 ikSk ekSk hikSk hekSk rem hst st1 ∧
      deadDh2 P sIdx k2 (P.x25519Base ikSk) hst = deadDh2 P sIdx S.N_id (P.x25519Base ikSk) hst := by
  rcases hInv with ⟨stGhost, hSimEq, hGhost, hBud, hSecEq⟩
  have hVEcFg := hGhost.2.2.2.2.2.1
  have hAbs1 : ∀ kv ∈ hst.base.principals, kv.1 ≠ S.N_id :=
    fun kv hm => Nat.ne_of_lt (hVEcFg.1.1 kv hm)
  have hEraseEq : ∀ k, (∀ kv ∈ hst.base.principals, kv.1 ≠ k) →
      erasePrincipalsFg k hst.base.principals = hst.base.principals := fun k hA => by
    unfold erasePrincipalsFg erasePrincipalEntryFg
    conv_rhs => rw [← List.map_id hst.base.principals]
    exact List.map_congr_left fun ⟨idx, e⟩ hm => by simp [beq_eq_false_iff_ne.mpr (hA _ hm)]
  have hClearEq : ∀ k, (∀ kv ∈ hst.base.principals, kv.1 ≠ k) →
      clearTargetSecIKAsign k stGhost = stGhost := fun k hA => by
    have hGhostPrin : stGhost.base.principals = hst.base.principals := by
      rw [hGhost.1]; simp [eraseStateFgIk, hEraseEq S.N_id hAbs1]
    unfold clearTargetSecIKAsign clearTargetSecIKAsignBase clearTargetPrinSecSign
    have hMap : stGhost.base.principals.map (fun (idx, e) =>
        (idx, if idx == k then { e with secIKAsign := [] } else e)) = stGhost.base.principals := by
      conv_rhs => rw [← List.map_id stGhost.base.principals]
      exact List.map_congr_left fun ⟨idx, e⟩ hm => by
        simp [beq_eq_false_iff_ne.mpr (hA _ (hGhostPrin ▸ hm))]
    cases stGhost; dsimp only at hMap ⊢; congr 1; cases ‹KeyIndState S›; simpa using hMap
  have hPV : ∀ k, (∀ kv ∈ hst.base.principals, kv.1 ≠ k) →
      prinTargetIsV k (P.x25519Base ikSk) hst = true := fun k hA =>
    List.all_eq_true.mpr fun ⟨idx, _⟩ hm => by simp [beq_eq_false_iff_ne.mpr (hA _ hm)]
  have hD1 : ∀ k, (∀ kv ∈ hst.base.principals, kv.1 ≠ k) → deadDh1 k hst = false := fun k hA => by
    unfold deadDh1; rw [List.find?_eq_none.mpr fun ⟨idx, _⟩ hm => by simp [hA _ hm]]
  have hBsmNil : bundleSignedMessages S.N_id hst.base.spkBundles = [] := by
    unfold bundleSignedMessages
    rw [List.filter_eq_nil_iff.mpr fun ⟨⟨u, _⟩, _⟩ hm => by
      simp [Nat.ne_of_lt (hVEcFg.2.1.1 _ hm).1], List.flatMap_nil]
  refine ⟨⟨stGhost, by rw [hSimEq, hClearEq S.N_id hAbs1, hClearEq k2 hAbs2], ?_,
    by rw [hBsmNil, List.length_nil] at hBud; omega, hSecEq⟩, ?_⟩
  · refine ⟨?_, hGhost.2.1, hGhost.2.2.1, hGhost.2.2.2.1, hGhost.2.2.2.2.1, hVEcFg,
      hPV k2 hAbs2, ?_, hGhost.2.2.2.2.2.2.2.2.1, hGhost.2.2.2.2.2.2.2.2.2.1,
      hGhost.2.2.2.2.2.2.2.2.2.2⟩
    · rw [hGhost.1]; simp [eraseStateFgIk, hEraseEq S.N_id hAbs1, hEraseEq k2 hAbs2]
    · exact fun kv hm => ⟨(hGhost.2.2.2.2.2.2.2.1 kv hm).1, (hGhost.2.2.2.2.2.2.2.1 kv hm).2.1,
        fun hEq => absurd (beq_iff_eq.mp hEq) (hAbs2 kv hm)⟩
  · unfold deadDh2; rw [hPV k2 hAbs2, hPV S.N_id hAbs1, hD1 k2 hAbs2, hD1 S.N_id hAbs1]

private theorem deadDh2_eq_of_sessions_absent {S : Setup} (P : Primitives) (s1 s2 kIdx : ℕ)
    (V : Bytes) (hst : KeyIndFgCutoffState S)
    (hAbs1 : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s1)
    (hAbs2 : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s2) :
    deadDh2 P s2 kIdx V hst = deadDh2 P s1 kIdx V hst := by
  have hSD : ∀ s0, (∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s0) →
      sessDeadIk P s0 V hst = false := fun s0 hA => by
    unfold sessDeadIk; rw [List.find?_eq_none.mpr fun s hm => by simp [hA s hm]]
  unfold deadDh2; rw [hSD s2 hAbs2, hSD s1 hAbs1]

private theorem fgSimInvDh2_1Key_retarget_sess {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {s1 s2 kIdx rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {st1 : FgKeyInd1KeySimState S}
    (hAbs1 : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s1)
    (hAbs2 : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s2)
    (hInv : FgSimInvDh2_1Key S b P hP s1 kIdx ikSk ekSk hikSk hekSk rem hst st1) :
    FgSimInvDh2_1Key S b P hP s2 kIdx ikSk ekSk hikSk hekSk rem hst st1 ∧
      deadDh2 P s2 kIdx (P.x25519Base ikSk) hst = deadDh2 P s1 kIdx (P.x25519Base ikSk) hst := by
  rcases hInv with ⟨stGhost, hSimEq, hGhost, hBud, hSecEq⟩
  have hEraseEq : ∀ s0, (∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ s0) →
      eraseSessionsFg s0 hst.base.sessions = hst.base.sessions := fun s0 hA => by
    unfold eraseSessionsFg eraseSessionEntryFg; conv_rhs => rw [← List.map_id hst.base.sessions]
    exact List.map_congr_left fun s hm => by simp [beq_eq_false_iff_ne.mpr (hA s hm)]
  refine ⟨⟨stGhost, hSimEq, ⟨by rw [hGhost.1]; simp [eraseStateFgIk, hEraseEq s1 hAbs1, hEraseEq s2 hAbs2],
    hGhost.2.1, hGhost.2.2.1, hGhost.2.2.2.1, hGhost.2.2.2.2.1, hGhost.2.2.2.2.2.1,
    hGhost.2.2.2.2.2.2.1, hGhost.2.2.2.2.2.2.2.1, hGhost.2.2.2.2.2.2.2.2.1,
    hGhost.2.2.2.2.2.2.2.2.2.1, fun s hm => ⟨(hGhost.2.2.2.2.2.2.2.2.2.2 s hm).1,
      (hGhost.2.2.2.2.2.2.2.2.2.2 s hm).2.1, fun hEq => absurd (beq_iff_eq.mp hEq) (hAbs2 s hm)⟩⟩,
    hBud, hSecEq⟩, deadDh2_eq_of_sessions_absent P s1 s2 kIdx _ hst hAbs1 hAbs2⟩

private theorem bundleSignedMessages_length_le (k : Nat)
    (xs : List ((Nat × Nat) × SpkBundleEntry)) :
    (bundleSignedMessages k xs).length ≤ 2 * xs.length := by
  unfold bundleSignedMessages
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    rcases hd with ⟨⟨u, j⟩, bdl⟩
    rw [List.filter_cons]
    dsimp only at ih ⊢
    split_ifs
    · rw [List.flatMap_cons, List.length_append, List.length_cons]
      dsimp only [List.length_cons, List.length_nil]
      omega
    · rw [List.length_cons]
      omega

private def sigBudgetSlack (S : Setup) (b : QueryBudget) : ℕ :=
  min S.N_spk_tot S.N_recv - activeSigBudget S b

private def toStaticSt1 {S : Setup} (b : QueryBudget) (st1 : FgKeyInd1KeySimState S) :
    FgKeyInd1KeySimState S :=
  { sim := st1.sim, sigBudget := st1.sigBudget + sigBudgetSlack S b }

private def fromStaticSt1 {S : Setup} (b : QueryBudget) (st1 : FgKeyInd1KeySimState S) :
    FgKeyInd1KeySimState S :=
  { sim := st1.sim, sigBudget := st1.sigBudget - sigBudgetSlack S b }

@[simp] private theorem toStaticSt1_sim {S : Setup} (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) : (toStaticSt1 b st1).sim = st1.sim := rfl

@[simp] private theorem fromStaticSt1_sim {S : Setup} (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) : (fromStaticSt1 b st1).sim = st1.sim := rfl

@[simp] private theorem fromStaticSt1_toStaticSt1 {S : Setup} (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) : fromStaticSt1 b (toStaticSt1 b st1) = st1 := by
  rcases st1 with ⟨_, _⟩
  simp [fromStaticSt1, toStaticSt1]

@[simp] private theorem fromStaticSt1_with_sim {S : Setup} (b : QueryBudget)
    (st1 : FgKeyInd1KeySimState S) (sim' : FgKeyIndSimState S) :
    fromStaticSt1 b { toStaticSt1 b st1 with sim := sim' } = { st1 with sim := sim' } := by
  rcases st1 with ⟨_, _⟩
  simp [fromStaticSt1, toStaticSt1]

private theorem bind_fromStaticSt1_with_sim {S : Setup} (b : QueryBudget)
    (stA : FgKeyInd1KeyActiveSimState S)
    (m : ProbComp (KeyIndResponse × FgKeyIndSimState S)) :
    ((m >>= fun (resp, sim') => pure (resp, { toStaticSt1 b stA.st1 with sim := sim' })) >>=
      fun (resp, st1') => pure (resp, { stA with st1 := fromStaticSt1 b st1' })) =
    (m >>= fun (resp, sim') => pure (resp, { stA with st1 := { stA.st1 with sim := sim' } })) := by
  simp only [bind_assoc]
  congr 1; funext ⟨resp, sim'⟩
  simp

private theorem toStaticSt1_empty (S : Setup) (b : QueryBudget) (secb : Bool) :
    toStaticSt1 b (FgKeyInd1KeyActiveSimState.empty S b secb).st1 =
      FgKeyInd1KeySimState.empty S secb := by
  unfold toStaticSt1 FgKeyInd1KeyActiveSimState.empty FgKeyInd1KeySimState.empty
    sigBudgetSlack activeSigBudget
  dsimp only
  congr 1
  omega

private theorem toStaticSt1_fromStaticSt1_of_inv {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {s0 k0 rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {st1' : FgKeyInd1KeySimState S}
    (hInv' : FgSimInvDh2_1Key S b P hP s0 k0 ikSk ekSk hikSk hekSk rem hst st1')
    (hSp' : hst.base.spkBundles.length + rem ≤ b.q_total) :
    toStaticSt1 b (fromStaticSt1 b st1') = st1' := by
  rcases hInv' with ⟨_, _, _, hBud, _⟩
  have hLen := bundleSignedMessages_length_le k0 hst.base.spkBundles
  rcases st1' with ⟨sim', bud'⟩
  unfold toStaticSt1 fromStaticSt1 sigBudgetSlack activeSigBudget
  dsimp only at hBud ⊢
  congr 1
  omega

private theorem sigBudget_beq_zero_toStaticSt1 {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {s0 k0 rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {st1 : FgKeyInd1KeySimState S}
    (hInv : FgSimInvDh2_1Key S b P hP s0 k0 ikSk ekSk hikSk hekSk (rem + 1) hst (toStaticSt1 b st1))
    (hSpk : hst.base.spkBundles.length + (rem + 1) ≤ b.q_total) :
    ((toStaticSt1 b st1).sigBudget == 0) = (st1.sigBudget == 0) := by
  rcases hInv with ⟨_, _, _, hBud, _⟩
  have hLen := bundleSignedMessages_length_le k0 hst.base.spkBundles
  unfold toStaticSt1 sigBudgetSlack activeSigBudget at hBud ⊢
  dsimp only at hBud ⊢
  by_cases hZ : st1.sigBudget = 0
  · have hSl0 : st1.sigBudget + (min S.N_spk_tot S.N_recv - min b.q_total (min S.N_spk_tot S.N_recv)) = 0 := by omega
    rw [beq_iff_eq.mpr hSl0, beq_iff_eq.mpr hZ]
  · have hPos :
        st1.sigBudget + (min S.N_spk_tot S.N_recv - min b.q_total (min S.N_spk_tot S.N_recv)) ≠ 0 := by
      omega
    rw [beq_eq_false_iff_ne.mpr hPos, beq_eq_false_iff_ne.mpr hZ]

private def FgSimInvDh2Ord_1Key (S : Setup) (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOrd pOrd : ℕ) (ikSk ekSk : Bytes)
    (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S) : Prop :=
  FgSimInvDh2_1Key S b P hP (sessSlotAtOrd S hst.base sOrd) (prinSlotAtOrd S hst.base pOrd)
    ikSk ekSk hikSk hekSk rem hst (toStaticSt1 b stA.st1) ∧
  stA.resolvedPrin? = (if pOrd < hst.base.principals.length
    then some (prinSlotAtOrd S hst.base pOrd) else none) ∧
  hst.base.spkBundles.length + rem ≤ b.q_total

private theorem fgSimInvDh2Ord_1Key_mono {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {sOrd pOrd rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {stA : FgKeyInd1KeyActiveSimState S}
    (h : FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk (rem + 1) hst stA) :
    FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk rem hst stA := by
  rcases h with ⟨⟨stGhost, hSimEq, hG, hBud, hSec⟩, hRes, hSpk⟩
  exact ⟨⟨stGhost, hSimEq, ⟨hG.1, hG.2.1, hG.2.2.1, by have := hG.2.2.2.1; omega,
    by have := hG.2.2.2.2.1; omega, hG.2.2.2.2.2⟩, hBud, hSec⟩, hRes, by omega⟩

private theorem fgPreImpl_ne_initPrin_prin {S : Setup} (s0 spkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (P : Primitives) (q : KeyIndQuery S)
    (hNoP : ∀ u, q ≠ .initPrin u) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl false s0 spkIdx optUsk optVsk S P q).run hst)) :
    x.2.base.principals.length = hst.base.principals.length ∧
      (∀ pOrd, prinSlotAtOrd S x.2.base pOrd = prinSlotAtOrd S hst.base pOrd) ∧
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 := by
  have hUnch : x.2.base.principals = hst.base.principals →
      x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 →
      x.2.base.principals.length = hst.base.principals.length ∧
        (∀ pOrd, prinSlotAtOrd S x.2.base pOrd = prinSlotAtOrd S hst.base pOrd) ∧
        x.2.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 :=
    fun hP hSp => ⟨by rw [hP], fun pOrd => by simp only [prinSlotAtOrd, hP], hSp⟩
  exact mem_support_pqxdhKeyIndFgPreImpl_elim false s0 spkIdx optUsk optVsk P q hst x hx
    (fun hP hSp _ _ => hUnch hP (by rw [hSp]; omega))
    (fun u _ hEq _ _ => absurd hEq (hNoP u))
    (fun u _ _ _ _ hB => ⟨by rw [hB]; simp, fun pOrd => by
      rw [prinSlotAtOrd_eq, prinSlotAtOrd_eq, hB]; dsimp only
      rw [ordLookup_map_eq (fun ⟨idx, e⟩ => by split_ifs <;> rfl)], by rw [hB]; simp⟩)
    (fun _ _ _ _ _ _ _ hB => hUnch (by rw [hB]) (by rw [hB]; simp))
    (fun _ _ _ _ _ _ _ hB => hUnch (by rw [hB]) (by rw [hB]; simp))
    (fun _ _ _ hB => hUnch (by rw [hB]) (by rw [hB]; simp))
    (fun _ _ _ hP hSp _ _ => hUnch hP (by rw [hSp]; omega))
    (fun _ _ _ _ _ hP hSp _ _ => hUnch hP (by rw [hSp]; omega))
    (fun _ _ hB => hUnch (by rw [hB]) (by rw [hB]; simp))

private theorem fgPreImpl_nonInit_sessions_slot {S : Setup} (s0 spkIdx : ℕ)
    (optUsk optVsk : Option Bytes) (P : Primitives) (q : KeyIndQuery S)
    (hNoP : ∀ u, q ≠ .initPrin u) (hNoI1 : ∀ u i b, q ≠ .initiateOPK u i b)
    (hNoI2 : ∀ u i b, q ≠ .initiateNoOPK u i b) (hst : KeyIndFgCutoffState S)
    (x : KeyIndResponse × KeyIndFgCutoffState S)
    (hx : x ∈ support ((pqxdhKeyIndFgPreImpl false s0 spkIdx optUsk optVsk S P q).run hst)) :
    x.2.base.sessions.length = hst.base.sessions.length ∧
      ∀ sOrd, sessSlotAtOrd S x.2.base sOrd = sessSlotAtOrd S hst.base sOrd := by
  let proj := fun s : KeyIndState S => s.sessions.map (fun e => initSessionSlotIdx e.sid)
  have hMap : proj x.2.base = proj hst.base := by
    suffices h : (∃ u j, q = .genSPK u j) ∨
        (pqxdhKeyIndFgPreImpl false s0 spkIdx optUsk optVsk S P q = pqxdhKeyIndFgImpl S P q ∧
          PreservesAt proj hst.base (pqxdhKeyIndImpl true S P q)) by
      rcases h with ⟨u, j, rfl⟩ | ⟨hEq, hp⟩
      · unfold pqxdhKeyIndFgPreImpl at hx; rcases mem_support_liftFgBase _ hst x hx with ⟨hb, _⟩
        have hp : PreservesAt proj hst.base (fgPreGenSPK spkIdx optVsk S P u j) := by
          unfold fgPreGenSPK; dsimp only
          repeat (first
            | with_reducible apply PreservesAt.pure
            | with_reducible apply PreservesAt.get_bind
            | (with_reducible apply PreservesAt.liftM_bind; intro _)
            | ((with_reducible apply PreservesAt.set_bind); rfl)
            | (split; try dsimp only))
        exact hp (x.1, x.2.base) hb
      · rw [hEq] at hx; exact hp (x.1, x.2.base) (mem_support_pqxdhKeyIndFgImpl_base P q hst x hx)
    cases q with
    | initPrin u => exact absurd rfl (hNoP u)
    | initiateOPK u i b => exact absurd rfl (hNoI1 u i b)
    | initiateNoOPK u i b => exact absurd rfl (hNoI2 u i b)
    | genSPK u j => exact Or.inl ⟨u, j, rfl⟩
    | _ =>
      refine Or.inr ⟨rfl, ?_⟩; unfold pqxdhKeyIndImpl SignalPqxdh.registerAdvKey; dsimp only
      repeat (first
        | with_reducible apply PreservesAt.pure
        | with_reducible apply PreservesAt.get_bind
        | (with_reducible apply PreservesAt.liftM_bind; intro _)
        | ((with_reducible apply PreservesAt.recordKeyIndResp_pure); intro _; rfl)
        | ((with_reducible apply PreservesAt.set_bind); first | rfl |
            (dsimp only [proj]; rw [List.map_map]; congr 1; funext e; dsimp only [Function.comp_def]; split_ifs <;> rfl))
        | (split; try dsimp only))
  refine ⟨by simpa [proj] using congrArg List.length hMap, fun sOrd => ?_⟩
  have hR := congrArg (fun l => (l.reverse[sOrd]?).getD S.N_send_tot) hMap
  simp only [proj, ← List.map_reverse, List.getElem?_map] at hR
  have hG : ∀ s : KeyIndState S,
      (Option.map (fun e => initSessionSlotIdx e.sid) s.sessions.reverse[sOrd]?).getD S.N_send_tot =
        sessSlotAtOrd S s sOrd := fun s => by unfold sessSlotAtOrd; cases s.sessions.reverse[sOrd]? <;> rfl
  rwa [hG, hG] at hR

private theorem fgInitiateActivePure_dh2_eq (P : Primitives) (ddh : Bytes → Bytes → Bytes → Bool)
    (sOrd sTgt : Nat) (S : Setup) (maxLen : Nat) (ekPk : Bytes) (hasOpk : Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (stA : FgKeyInd1KeyActiveSimState S)
    (hTgt : (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) = false →
      stA.st1.sim.base.sessions.any (fun e => e.sid == sid) = false →
      (stA.st1.sim.base.sessions.length == sOrd) = (initSessionSlotIdx sid == sTgt)) :
    fgInitiateActivePure P ddh false false sOrd S maxLen ekPk hasOpk sid u bundle stA =
    (do
      let (resp, sim') ←
        if (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) then pure (.noneResp, stA.st1.sim)
        else fgRunInitiatePure P ddh false sTgt S maxLen ekPk sid u bundle stA.st1.sim
      let cnt' := if hasOpk && (sim'.base.sessions.length != stA.st1.sim.base.sessions.length)
        then stA.sendOpkCnt + 1 else stA.sendOpkCnt
      return (resp, { stA with st1 := { stA.st1 with sim := sim' }, sendOpkCnt := cnt' })) := by
  unfold fgInitiateActivePure fgRunInitiateActivePure fgRunInitiatePure; dsimp only
  have hGuardEq : (!(if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome)) =
      (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) := by cases hasOpk <;> cases bundle.opkB? <;> rfl
  rw [hGuardEq]; cases hGuard : (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases hAny : stA.st1.sim.base.sessions.any (fun e => e.sid == sid)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and, ite_self, hTgt hGuard hAny]
      cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp
      | some p =>
        rcases p with ⟨_, uEntry⟩; dsimp only
        cases koskBundleOkTake S P stA.st1.sim.base.principals stA.st1.sim.base.spkBundles
          stA.st1.sim.base.opkEntries stA.st1.sim.advKeyPows bundle
        · simp
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, bind_assoc]
          congr 1; funext ekASkRaw; congr 1; funext kemCoins
          cases (P.sigVerify (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeEC bundle.spkB) bundle.spkSig &&
            P.sigVerify (resolveSigPk P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB)
              (encodeKEM bundle.pqspkB) bundle.pqspkSig)
          · simp
          · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            cases P.kemEncaps bundle.pqspkB kemCoins with
            | none => simp
            | some sc =>
              rcases sc with ⟨ss, kemCt⟩; simp only [bind_assoc]
              congr 1; funext ⟨drKeyReal, fgL'⟩; congr 1; funext drKeyRand
              cases findHonestPrincipal P (stA.st1.sim.base.principals.take S.N_dh) bundle.ikB <;> cases hasOpk <;> simp
    · simp
  · simp

private theorem fgKeyInd1KeyActiveStepPure_dh2_nonInit_eq {S : Setup} (b : QueryBudget)
    (P : Primitives) (ikSk : Bytes) (ddh : Bytes → Bytes → Bytes → Bool)
    (sOrd pOrd s0 k0 : Nat) (ikPk ekPk : Bytes) (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S)
    (hNoP : ∀ u, q ≠ .initPrin u) (hNoI1 : ∀ u i b, q ≠ .initiateOPK u i b)
    (hNoI2 : ∀ u i b, q ≠ .initiateNoOPK u i b)
    (hOpt : ∀ u : Fin S.N_id, optNatMatches stA.resolvedPrin? u.val = (u.val == k0))
    (hSpkLt : stA.st1.sim.base.spkBundles.length < b.q_total + 1)
    (hBudZero : ((toStaticSt1 b stA.st1).sigBudget == 0) = (stA.st1.sigBudget == 0)) :
    (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b ikPk ekPk sOrd pOrd) P ikSk ddh S b.q_total q).run stA =
      ((fgKeyInd1KeySimImplIk P ikSk ddh s0 k0 S b.q_total ikPk ekPk q).run (toStaticSt1 b stA.st1) >>=
        fun (resp, st1') => pure (resp, { stA with st1 := fromStaticSt1 b st1' })) := by
  have hSpkNe : (stA.st1.sim.base.spkBundles.length == b.q_total + 1) = false :=
    beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hSpkLt)
  cases q with
  | initPrin u => exact absurd rfl (hNoP u)
  | initiateOPK u i b => exact absurd rfl (hNoI1 u i b)
  | initiateNoOPK u i b => exact absurd rfl (hNoI2 u i b)
  | genSPK u j =>
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeyActiveStepPure fgGenSPK1KeyActivePure fgGenSpkActivePure
      fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk fgGenSPK1KeyPure fgKeyIndStepPure activeParamsDh2
    have hFlatNe := spkBundleFlatIdx_ne_noSpkIdx S u j
    dsimp only [StateT_run_mk]; rw [hOpt u]; simp only [toStaticSt1_sim, Bool.true_and, hSpkNe, hFlatNe]
    cases (u.val == k0)
    · simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, fromStaticSt1_with_sim]
      cases stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none => simp
        | some p => rcases p with ⟨_, _⟩; simp
      · simp
    · simp only [↓reduceIte, hBudZero]; cases stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val))
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val) with
        | none => simp
        | some p =>
          rcases p with ⟨_, _⟩; dsimp only
          cases hZ : (stA.st1.sigBudget == 0)
          · have hSubEq : (toStaticSt1 b stA.st1).sigBudget - 1 - sigBudgetSlack S b =
                stA.st1.sigBudget - 1 := by
              have hNe : stA.st1.sigBudget ≠ 0 := beq_eq_false_iff_ne.mp hZ
              unfold toStaticSt1; dsimp only; omega
            simp [fromStaticSt1, hSubEq]
          · simp
      · simp
  | genOPK u j o =>
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeyActiveStepPure fgGenOPKActivePure
      fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk activeParamsDh2
    dsimp only [StateT_run_mk, toStaticSt1_sim]
    rw [bind_fromStaticSt1_with_sim]
    unfold fgKeyIndStepPure; dsimp only
    cases stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) <;> simp
  | acceptOPK k j o hdr =>
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeyActiveStepPure
      fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk activeParamsDh2
    dsimp only [StateT_run_mk, toStaticSt1_sim]
    rw [bind_fromStaticSt1_with_sim]
    simp [fgKeyIndStepPure]
  | _ =>
    unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeyActiveStepPure
      fgKeyInd1KeySimImplIk fgKeyInd1KeyStepPureIk activeParamsDh2
    dsimp only [StateT_run_mk, toStaticSt1_sim]
    rw [bind_fromStaticSt1_with_sim]
    simp [fgKeyIndStepPure]

private theorem fgSimInvDh2_1Key_base_eqs {S : Setup} {b : QueryBudget} {P : Primitives}
    {hP : CryptoWellFormedPrimitivesδ P} {s0 k0 rem : ℕ} {ikSk ekSk : Bytes}
    {hikSk : ikSk.length = 32} {hekSk : ekSk.length = 32}
    {hst : KeyIndFgCutoffState S} {st1 : FgKeyInd1KeySimState S}
    (hInv : FgSimInvDh2_1Key S b P hP s0 k0 ikSk ekSk hikSk hekSk rem hst st1) :
    st1.sim.base.principals.length = hst.base.principals.length ∧
    st1.sim.base.sessions.length = hst.base.sessions.length ∧
    st1.sim.base.spkBundles.length = hst.base.spkBundles.length ∧
    (∀ u : Fin S.N_id, st1.sim.base.principals.any (fun (idx, _) => idx == u.val) =
      hst.base.principals.any (fun (idx, _) => idx == u.val)) ∧
    (∀ sid : SessionId S, st1.sim.base.sessions.any (fun e => e.sid == sid) =
      hst.base.sessions.any (fun e => e.sid == sid)) := by
  rcases hInv with ⟨stG, hSim, hG, _, _⟩
  refine ⟨?_, ?_, ?_, fun u => ?_, fun sid => ?_⟩
  · rw [hSim, clearTargetSecIKAsign_base_principals, List.length_map, hG.1]; simp [eraseStateFgIk, erasePrincipalsFg_length]
  · rw [hSim, clearTargetSecIKAsign_base_sessions, hG.1]; simp [eraseStateFgIk, eraseSessionsFg]
  · rw [hSim, clearTargetSecIKAsign_base_spkBundles, hG.1]; rfl
  · rw [hSim, clearTargetSecIKAsign_base_principals, any_idx_map_clearTargetPrinSecSign, hG.1]; simp [eraseStateFgIk, any_idx_erasePrincipalsFg]
  · rw [hSim, clearTargetSecIKAsign_base_sessions, hG.1]; simp [eraseStateFgIk, any_sid_eraseSessionsFg]

private theorem fgInitPrin1KeyActivePure_dh2_eq {S : Setup} (b : QueryBudget)
    (P : Primitives) (pOrd kRun : Nat)
    (ikPk : Bytes) (u : Fin S.N_id) (stA : FgKeyInd1KeyActiveSimState S)
    (hAnyF : stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val) = false)
    (hTgt : (stA.st1.sim.base.principals.length == pOrd) = (u.val == kRun)) :
    fgInitPrin1KeyActivePure P true pOrd ikPk u stA =
      (fgInitPrin1KeyPure P true kRun ikPk u (toStaticSt1 b stA.st1) >>= fun (resp, st1') =>
        pure (resp,
          { stA with
            st1 := fromStaticSt1 b st1'
            resolvedPrin? := if u.val == kRun then some u.val else stA.resolvedPrin? })) := by
  unfold fgInitPrin1KeyActivePure fgInitPrin1KeyPure
  simp only [toStaticSt1_sim, hAnyF, Bool.false_eq_true, ↓reduceIte, Bool.true_and, hTgt,
    bind_assoc, pure_bind, fromStaticSt1_with_sim]

private theorem fgStepCoupling_dh2_ord_initiate {S : Setup} (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOrd pOrd : ℕ) (ikSk ekSk : Bytes)
    (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32) (hasOpk : Bool)
    (sid : SessionId S) (hSend : IsSendSessionId S sid) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (q : KeyIndQuery S) (hNoP : ∀ u', q ≠ .initPrin u')
    (rem : ℕ) (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hV : ValidKeyIndEc S hst.base)
    (hDead : deadDh2 P (sessSlotAtOrd S hst.base sOrd) (prinSlotAtOrd S hst.base pOrd) (P.x25519Base ikSk) hst = false)
    (hOrd : FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk (rem + 1) hst stA)
    (hCurS : curSessSlot sOrd q hst = if hst.base.sessions.length == sOrd then initSessionSlotIdx sid else S.N_send_tot)
    (hLhsForm : ∀ sIdx, (pqxdhKeyIndFgPreImpl false sIdx (SignalPqxdh.Security.FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P q).run hst =
      (liftFgBase (do
        let _ ← get
        if (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) then return .noneResp
        fgPreInitiate false sIdx (some ekSk) S P sid u bundle)).run hst)
    (hRhsAct : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
      P ikSk P.isValidDhTriple S b.q_total q).run stA =
      fgInitiateActivePure P P.isValidDhTriple false false sOrd S b.q_total (P.x25519Base ekSk) hasOpk sid u bundle stA)
    (hRhs1K : ∀ sIdx, (fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sIdx (prinSlotAtOrd S hst.base pOrd)
      S b.q_total (P.x25519Base ikSk) (P.x25519Base ekSk) q).run (toStaticSt1 b stA.st1) =
      ((if (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome) then pure (.noneResp, stA.st1.sim)
        else fgRunInitiatePure P P.isValidDhTriple false sIdx S b.q_total (P.x25519Base ekSk) sid u bundle stA.st1.sim) >>=
        fun (resp, sim') => pure (resp, { toStaticSt1 b stA.st1 with sim := sim' })))
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeyActiveSimState S → ProbComp Bool)
    (hCont : ∀ r hst' stA', ValidKeyIndEc S hst'.base →
      deadDh2 P (sessSlotAtOrd S hst'.base sOrd) (prinSlotAtOrd S hst'.base pOrd) (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk rem hst' stA' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, stA')] {true})
    (hDeadCont : ∀ r hst', ValidKeyIndEc S hst'.base →
      deadDh2 P (sessSlotAtOrd S hst'.base sOrd) (prinSlotAtOrd S hst'.base pOrd) (P.x25519Base ikSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total q).run stA >>= k2] {true} := by
  rcases hOrd with ⟨hInv1, hRes, hSpk⟩
  set s0 := sessSlotAtOrd S hst.base sOrd; set k0 := prinSlotAtOrd S hst.base pOrd
  rcases fgSimInvDh2_1Key_base_eqs hInv1 with ⟨_, hLenS, _, _, hAnyS⟩
  have hLhsPre : ∀ sIdx kIdx, (pqxdhKeyIndFgPreImpl1KeyIk sIdx kIdx (some ikSk) (some ekSk) S P q).run hst =
      (pqxdhKeyIndFgPreImpl false sIdx (SignalPqxdh.Security.FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P q).run hst := fun sIdx kIdx => by
    rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNoP,
      pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNoP]
  cases hG : (if hasOpk then bundle.opkB?.isNone else bundle.opkB?.isSome)
  · cases hDup : hst.base.sessions.any (fun e => e.sid == sid)
    · have hsSidLt : initSessionSlotIdx sid < S.N_send_tot := initSessionSlotIdx_lt_of_isSendSessionId sid hSend
      have hAbsN : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ S.N_send_tot := fun s hm =>
        Nat.ne_of_lt (initSessionSlotIdx_lt_of_isSendSessionId s.sid
          (hV.2.2.2.1 s.sid (by simp only [sessPksKeyInd, List.map_map]; exact List.mem_map.mpr ⟨s, hm, rfl⟩)))
      have hAbsSid : ∀ s ∈ hst.base.sessions, initSessionSlotIdx s.sid ≠ initSessionSlotIdx sid := fun s hm hEq =>
        Bool.false_ne_true (hDup.symm.trans (List.any_eq_true.mpr
          ⟨s, hm, beq_iff_eq.mpr (initSessionSlotIdx_inj_of_lt hEq hsSidLt)⟩))
      set sRun := if sOrd < hst.base.sessions.length then s0
        else if sOrd = hst.base.sessions.length then initSessionSlotIdx sid else S.N_send_tot
      have hGeS0 : ¬ sOrd < hst.base.sessions.length → s0 = S.N_send_tot := fun hNLt => by
        dsimp only [s0]; rw [sessSlotAtOrd_eq]; exact ordLookup_of_ge (Nat.le_of_not_lt hNLt)
      have hRet : FgSimInvDh2_1Key S b P hP sRun k0 ikSk ekSk hikSk hekSk (rem + 1) hst (toStaticSt1 b stA.st1) ∧
          deadDh2 P sRun k0 (P.x25519Base ikSk) hst = false := by
        dsimp only [sRun]; split_ifs with hLt hEq
        · exact ⟨hInv1, hDead⟩
        · have hs0N := hGeS0 hLt; rw [hs0N] at hInv1 hDead
          have hR := fgSimInvDh2_1Key_retarget_sess hAbsN hAbsSid hInv1; exact ⟨hR.1, hR.2.trans hDead⟩
        · rw [← hGeS0 hLt]; exact ⟨hInv1, hDead⟩
      have hTgtEq : (hst.base.sessions.length == sOrd) = (initSessionSlotIdx sid == sRun) := by
        dsimp only [sRun]; split_ifs with hLt hEq
        · rw [beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)]
          obtain ⟨s1, hm1, hs1Eq⟩ := ordLookup_mem_of_lt (proj := fun s => initSessionSlotIdx s.sid) (dflt := S.N_send_tot) hLt
          have hs0Eq : s0 = initSessionSlotIdx s1.sid := by dsimp only [s0]; rw [sessSlotAtOrd_eq, hs1Eq]
          exact (beq_eq_false_iff_ne.mpr fun hE => hAbsSid s1 hm1 (hs0Eq ▸ hE.symm)).symm
        · simp [hEq]
        · rw [beq_eq_false_iff_ne.mpr (Ne.symm hEq), beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hsSidLt)]
      have hCurEq : (!false && (initSessionSlotIdx sid == curSessSlot sOrd q hst)) =
          (!false && (initSessionSlotIdx sid == sRun)) := by
        rw [hCurS, ← hTgtEq]; cases (hst.base.sessions.length == sOrd) <;> simp [Nat.ne_of_lt hsSidLt]
      let lhsStep := (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst
      have hLhsEq : lhsStep = (pqxdhKeyIndFgPreImpl1KeyIk sRun k0 (some ikSk) (some ekSk) S P q).run hst := by
        dsimp only [lhsStep, pqxdhKeyIndFgPreImpl1KeyOrdIk, StateT_run_mk]
        rw [hLhsPre, hLhsPre, hLhsForm, hLhsForm]; simp only [hG, Bool.false_eq_true, ↓reduceIte]
        unfold liftFgBase fgPreInitiate; simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hCurEq]
      let updSt := fun st1' : FgKeyInd1KeySimState S =>
        let cnt' := if hasOpk && (st1'.sim.base.sessions.length != stA.st1.sim.base.sessions.length)
          then stA.sendOpkCnt + 1 else stA.sendOpkCnt
        { stA with st1 := fromStaticSt1 b st1', sendOpkCnt := cnt' }
      have hRhsEq : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total q).run stA =
          ((fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple sRun k0 S b.q_total (P.x25519Base ikSk) (P.x25519Base ekSk) q).run (toStaticSt1 b stA.st1) >>=
            fun (resp, st1') => pure (resp, updSt st1')) := by
        rw [hRhsAct, fgInitiateActivePure_dh2_eq P P.isValidDhTriple sOrd sRun S b.q_total _ hasOpk sid u bundle stA
          (fun _ _ => by rw [toStaticSt1_sim] at hLenS; rw [hLenS]; exact hTgtEq), hRhs1K sRun]
        dsimp only [updSt]; simp only [hG, Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, fromStaticSt1_with_sim]
      let k1w : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool := open scoped Classical in
        fun x => if x ∈ support lhsStep then k1 x else pure false
      rw [OracleComp.evalDist_bind_congr_of_support lhsStep k1 k1w (fun x hx => by simp only [k1w, hx, ↓reduceIte]), hLhsEq, hRhsEq]
      simp only [bind_assoc]
      have hPost : ∀ r hst', (r, hst') ∈ support lhsStep → ValidKeyIndEc S hst'.base ∧
          (hst'.base = hst.base ∨ ∃ se ro', se.sid = sid ∧
            hst'.base = { hst.base with roCache := ro', sessions := se :: hst.base.sessions }) := fun r hst' hx => by
        have hxPre : (r, hst') ∈ support ((pqxdhKeyIndFgPreImpl false sRun (SignalPqxdh.Security.FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P q).run hst) := by
          rwa [hLhsEq, hLhsPre] at hx
        rw [hLhsForm] at hxPre; rcases mem_support_liftFgBase _ hst (r, hst') hxPre with ⟨hb, _⟩
        exact ⟨pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc sOrd pOrd ikSk ekSk P q hst hV (r, hst') hx,
          (fgPreInitiate_elim_sid false sRun (some ekSk) P sid u bundle hst.base (r, hst'.base)
            (by simpa only [StateT.run_bind, StateT.run_get, pure_bind, hG, Bool.false_eq_true, ↓reduceIte] using hb)).imp id
            fun ⟨se, ro', hSidEq, _, hB⟩ => ⟨se, ro', hSidEq, hB⟩⟩
      refine fgStepCoupling_dh2_1Key S b P hP sRun k0 ikSk ekSk hikSk hekSk q rem hst (toStaticSt1 b stA.st1) hRet.2 hRet.1 k1w
        (fun (resp, st1') => k2 (resp, updSt st1'))
        (fun r hst' st1' hD' hInv' => ?_) (fun r hst' hD' => ?_)
      · dsimp only [k1w]; split_ifs with hx
        · rcases hPost r hst' hx with ⟨hVx, hB | ⟨se, ro', hSidEq, hB⟩⟩
          · have hSpRem : hst'.base.spkBundles.length + rem ≤ b.q_total := by
              rw [hB]; exact Nat.le_of_succ_le hSpk
            have hSub : FgSimInvDh2_1Key S b P hP s0 k0 ikSk ekSk hikSk hekSk rem hst' st1' ∧
                deadDh2 P s0 k0 (P.x25519Base ikSk) hst' = false := by
              dsimp only [sRun] at hInv' hD'; split_ifs at hInv' hD' with hLt hEq
              · exact ⟨hInv', hD'⟩
              · have hR := fgSimInvDh2_1Key_retarget_sess (by rw [hB]; exact hAbsSid) (by rw [hB]; exact hAbsN) hInv'
                rw [hGeS0 hLt]; exact ⟨hR.1, hR.2.trans hD'⟩
              · rw [hGeS0 hLt]; exact ⟨hInv', hD'⟩
            have hRt := toStaticSt1_fromStaticSt1_of_inv hSub.1 hSpRem
            exact hCont r hst' _ hVx (by simp only [s0, k0, sessSlotAtOrd, prinSlotAtOrd, hB] at hSub ⊢; exact hSub.2)
              ⟨by dsimp only [updSt]; rw [hRt]; simp only [s0, k0, sessSlotAtOrd, prinSlotAtOrd, hB] at hSub ⊢; exact hSub.1,
               by dsimp only [updSt]; rw [hB]; exact hRes, hSpRem⟩
          · have hSpRem : hst'.base.spkBundles.length + rem ≤ b.q_total := by
              rw [hB]; exact Nat.le_of_succ_le hSpk
            have hRt := toStaticSt1_fromStaticSt1_of_inv hInv' hSpRem
            have hs' : sessSlotAtOrd S hst'.base sOrd = sRun := by
              rw [sessSlotAtOrd_eq, hB]; dsimp only [sRun]; split_ifs with hLt hEq
              · rw [ordLookup_cons_of_lt _ _ _ hLt, ← sessSlotAtOrd_eq]
              · subst hEq; rw [ordLookup_cons_eq, hSidEq]
              · exact ordLookup_of_ge (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hLt) (Ne.symm hEq)))
            have hk' : prinSlotAtOrd S hst'.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hB]
            exact hCont r hst' _ hVx (by rwa [hs', hk'])
              ⟨by dsimp only [updSt]; rw [hRt]; rwa [hs', hk'],
               by dsimp only [updSt]; rw [hk', hB]; exact hRes, hSpRem⟩
        · simp
      · dsimp only [k1w]; split_ifs with hx
        · rcases hPost r hst' hx with ⟨hVx, hB | ⟨se, ro', hSidEq, hB⟩⟩
          · have hDEq : deadDh2 P s0 k0 (P.x25519Base ikSk) hst' = true := by
              dsimp only [sRun] at hD'; split_ifs at hD' with hLt hEq
              · exact hD'
              · rw [hGeS0 hLt, deadDh2_eq_of_sessions_absent P (initSessionSlotIdx sid) S.N_send_tot k0 _ hst'
                  (by rw [hB]; exact hAbsSid) (by rw [hB]; exact hAbsN)]; exact hD'
              · rwa [hGeS0 hLt]
            exact hDeadCont r hst' hVx (by simp only [s0, k0, sessSlotAtOrd, prinSlotAtOrd, hB] at hDEq ⊢; exact hDEq)
          · have hs' : sessSlotAtOrd S hst'.base sOrd = sRun := by
              rw [sessSlotAtOrd_eq, hB]; dsimp only [sRun]; split_ifs with hLt hEq
              · rw [ordLookup_cons_of_lt _ _ _ hLt, ← sessSlotAtOrd_eq]
              · subst hEq; rw [ordLookup_cons_eq, hSidEq]
              · exact ordLookup_of_ge (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hLt) (Ne.symm hEq)))
            have hk' : prinSlotAtOrd S hst'.base pOrd = k0 := by simp only [k0, prinSlotAtOrd, hB]
            exact hDeadCont r hst' hVx (by rwa [hs', hk'])
        · simp
    · have hL : (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst = pure (.noneResp, hst) := by
        dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdIk, StateT_run_mk]; rw [hLhsPre, hLhsForm]
        unfold liftFgBase fgPreInitiate
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hG, Bool.false_eq_true, ↓reduceIte, hDup]
      have hR : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total q).run stA = pure (.noneResp, stA) := by
        rw [hRhsAct, fgInitiateActivePure_dh2_eq P P.isValidDhTriple sOrd 0 S b.q_total _ hasOpk sid u bundle stA
          (fun _ hF => by have hAS := hAnyS sid; rw [toStaticSt1_sim] at hAS; rw [hAS, hDup] at hF; cases hF)]
        dsimp only; unfold fgRunInitiatePure
        have hAS := hAnyS sid; rw [toStaticSt1_sim] at hAS
        simp only [hG, Bool.false_eq_true, ↓reduceIte, hAS, hDup, pure_bind, bne_self_eq_false, Bool.and_false]
      rw [hL, hR]; simp only [pure_bind]; exact hCont .noneResp hst stA hV hDead (fgSimInvDh2Ord_1Key_mono ⟨hInv1, hRes, hSpk⟩)
  · have hL : (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst = pure (.noneResp, hst) := by
      dsimp only [pqxdhKeyIndFgPreImpl1KeyOrdIk, StateT_run_mk]; rw [hLhsPre, hLhsForm]
      unfold liftFgBase
      simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hG, ↓reduceIte]
    have hR : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
        P ikSk P.isValidDhTriple S b.q_total q).run stA = pure (.noneResp, stA) := by
      rw [hRhsAct, fgInitiateActivePure_dh2_eq P P.isValidDhTriple sOrd 0 S b.q_total _ hasOpk sid u bundle stA
        (fun hF _ => by rw [hG] at hF; cases hF)]
      dsimp only; simp only [hG, ↓reduceIte, pure_bind, bne_self_eq_false, Bool.and_false, Bool.false_eq_true]
    rw [hL, hR]; simp only [pure_bind]; exact hCont .noneResp hst stA hV hDead (fgSimInvDh2Ord_1Key_mono ⟨hInv1, hRes, hSpk⟩)

private theorem fgStepCoupling_dh2_ord_1Key {S : Setup} (b : QueryBudget) (P : Primitives)
    (hP : CryptoWellFormedPrimitivesδ P) (sOrd pOrd : ℕ) (ikSk ekSk : Bytes)
    (hikSk : ikSk.length = 32) (hekSk : ekSk.length = 32) (q : KeyIndQuery S) (rem : ℕ)
    (hst : KeyIndFgCutoffState S) (stA : FgKeyInd1KeyActiveSimState S)
    (hV : ValidKeyIndEc S hst.base)
    (hDead : deadDh2 P (sessSlotAtOrd S hst.base sOrd) (prinSlotAtOrd S hst.base pOrd) (P.x25519Base ikSk) hst = false)
    (hOrd : FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk (rem + 1) hst stA)
    (k1 : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool)
    (k2 : KeyIndResponse × FgKeyInd1KeyActiveSimState S → ProbComp Bool)
    (hCont : ∀ r hst' stA', ValidKeyIndEc S hst'.base →
      deadDh2 P (sessSlotAtOrd S hst'.base sOrd) (prinSlotAtOrd S hst'.base pOrd) (P.x25519Base ikSk) hst' = false →
      FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikSk hekSk rem hst' stA' →
      𝒟[k1 (r, hst')] {true} ≤ 𝒟[k2 (r, stA')] {true})
    (hDeadCont : ∀ r hst', ValidKeyIndEc S hst'.base →
      deadDh2 P (sessSlotAtOrd S hst'.base sOrd) (prinSlotAtOrd S hst'.base pOrd) (P.x25519Base ikSk) hst' = true →
      𝒟[k1 (r, hst')] {true} = 0) :
    𝒟[(pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst >>= k1] {true} ≤
      𝒟[(fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total q).run stA >>= k2] {true} := by
  have hQCases : (∃ u, q = .initPrin u) ∨ (∃ u i bdl, q = .initiateOPK u i bdl) ∨
      (∃ u i bdl, q = .initiateNoOPK u i bdl) ∨
      ((∀ u, q ≠ .initPrin u) ∧ (∀ u i bdl, q ≠ .initiateOPK u i bdl) ∧ (∀ u i bdl, q ≠ .initiateNoOPK u i bdl)) := by
    cases q with
    | initPrin u => exact Or.inl ⟨u, rfl⟩
    | initiateOPK u i bdl => exact Or.inr (Or.inl ⟨u, i, bdl, rfl⟩)
    | initiateNoOPK u i bdl => exact Or.inr (Or.inr (Or.inl ⟨u, i, bdl, rfl⟩))
    | _ => exact Or.inr (Or.inr (Or.inr ⟨(fun _ h => by cases h), (fun _ _ _ h => by cases h), (fun _ _ _ h => by cases h)⟩))
  rcases hQCases with ⟨u, rfl⟩ | ⟨u, i, bdl, rfl⟩ | ⟨u, i, bdl, rfl⟩ | ⟨hNoP, hNoI1, hNoI2⟩
  · rcases hOrd with ⟨hInv1, hRes, hSpk⟩
    set s0 := sessSlotAtOrd S hst.base sOrd; set k0 := prinSlotAtOrd S hst.base pOrd
    rcases fgSimInvDh2_1Key_base_eqs hInv1 with ⟨hLenP, _, _, hAnyP, _⟩
    cases hDup : hst.base.principals.any (fun (idx, _) => idx == u.val)
    · have hAbsU : ∀ kv ∈ hst.base.principals, kv.1 ≠ u.val := fun kv hm hEq =>
        Bool.false_ne_true (hDup.symm.trans (List.any_eq_true.mpr ⟨kv, hm, beq_iff_eq.mpr hEq⟩))
      set kRun := if pOrd < hst.base.principals.length then k0
        else if pOrd = hst.base.principals.length then u.val else S.N_id
      have hGeK0 : ¬ pOrd < hst.base.principals.length → k0 = S.N_id := fun hNLt => by
        dsimp only [k0]; rw [prinSlotAtOrd_eq]; exact ordLookup_of_ge (Nat.le_of_not_lt hNLt)
      have hRet : FgSimInvDh2_1Key S b P hP s0 kRun ikSk ekSk hikSk hekSk (rem + 1) hst (toStaticSt1 b stA.st1) ∧
          deadDh2 P s0 kRun (P.x25519Base ikSk) hst = false := by
        dsimp only [kRun]; split_ifs with hLt hEq
        · exact ⟨hInv1, hDead⟩
        · rw [hGeK0 hLt] at hInv1 hDead
          have hR := fgSimInvDh2_1Key_retarget_prin hAbsU hInv1; exact ⟨hR.1, hR.2.trans hDead⟩
        · rw [← hGeK0 hLt]; exact ⟨hInv1, hDead⟩
      have hTgtEq : (hst.base.principals.length == pOrd) = (u.val == kRun) := by
        dsimp only [kRun]; split_ifs with hLt hEq
        · rw [beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt)]
          obtain ⟨kv1, hm1, hk1Eq⟩ := ordLookup_mem_of_lt (proj := Prod.fst) (dflt := S.N_id) hLt
          have hk0Eq : k0 = kv1.1 := by dsimp only [k0]; rw [prinSlotAtOrd_eq, hk1Eq]
          exact (beq_eq_false_iff_ne.mpr fun hE => hAbsU kv1 hm1 (hk0Eq ▸ hE.symm)).symm
        · simp [hEq]
        · rw [beq_eq_false_iff_ne.mpr (Ne.symm hEq), beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)]
      have hCurEq : (true && (u.val == curPrinSlot pOrd (.initPrin u) hst)) = (true && (u.val == kRun)) := by
        unfold curPrinSlot; rw [← hTgtEq]; cases (hst.base.principals.length == pOrd) <;> simp [Nat.ne_of_lt u.isLt]
      let lhsStep := (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P (.initPrin u)).run hst
      have hLhsEq : lhsStep = (pqxdhKeyIndFgPreImpl1KeyIk s0 kRun (some ikSk) (some ekSk) S P (.initPrin u)).run hst := by
        dsimp only [lhsStep]; unfold pqxdhKeyIndFgPreImpl1KeyOrdIk; rw [StateT_run_mk]
        dsimp only [pqxdhKeyIndFgPreImpl1KeyIk]; unfold liftFgBase fgPreInitPrin1Key
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, pure_bind, hCurEq]
      let updSt := fun st1' : FgKeyInd1KeySimState S =>
        { stA with st1 := fromStaticSt1 b st1', resolvedPrin? := if u.val == kRun then some u.val else stA.resolvedPrin? }
      have hRhsEq : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total (.initPrin u)).run stA =
          ((fgKeyInd1KeySimImplIk P ikSk P.isValidDhTriple s0 kRun S b.q_total (P.x25519Base ikSk) (P.x25519Base ekSk) (.initPrin u)).run (toStaticSt1 b stA.st1) >>=
            fun (resp, st1') => pure (resp, updSt st1')) := by
        unfold fgKeyInd1KeyActiveSimImpl fgKeyInd1KeySimImplIk; rw [StateT_run_mk, StateT_run_mk]
        dsimp only [fgKeyInd1KeyActiveStepPure, fgKeyInd1KeyStepPureIk, activeParamsDh2, updSt]
        have hAP := hAnyP u; rw [toStaticSt1_sim] at hAP
        rw [toStaticSt1_sim] at hLenP
        exact fgInitPrin1KeyActivePure_dh2_eq b P pOrd kRun _ u stA (by rw [hAP, hDup]) (by rw [hLenP, hTgtEq])
      let k1w : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool := open scoped Classical in
        fun x => if x ∈ support lhsStep then k1 x else pure false
      rw [OracleComp.evalDist_bind_congr_of_support lhsStep k1 k1w (fun x hx => by simp only [k1w, hx, ↓reduceIte]), hLhsEq, hRhsEq]
      simp only [bind_assoc]
      have hPost : ∀ r hst', (r, hst') ∈ support lhsStep → ValidKeyIndEc S hst'.base ∧
          sessSlotAtOrd S hst'.base sOrd = s0 ∧ prinSlotAtOrd S hst'.base pOrd = kRun ∧
          (if u.val == kRun then some u.val else stA.resolvedPrin?) =
            (if pOrd < hst'.base.principals.length then some kRun else none) ∧
          hst'.base.spkBundles.length + rem ≤ b.q_total := fun r hst' hx => by
        have hVx := pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc sOrd pOrd ikSk ekSk P (.initPrin u) hst hV (r, hst') hx
        have hx1 := hx; rw [hLhsEq] at hx1; dsimp only [pqxdhKeyIndFgPreImpl1KeyIk] at hx1
        unfold fgPreInitPrin1Key at hx1; rcases mem_support_liftFgBase _ hst (r, hst') hx1 with ⟨hb, _⟩
        simp only [StateT.run_bind, StateT.run_get, pure_bind, hDup, Bool.false_eq_true, ↓reduceIte,
          StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_pure, bind_assoc,
          MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hb
        rcases hb with ⟨_, _, hEq⟩; have hB := (Prod.mk.inj hEq).2
        refine ⟨hVx, by simp only [s0, sessSlotAtOrd, hB], ?_, ?_, by rw [hB]; exact Nat.le_of_succ_le hSpk⟩
        · rw [prinSlotAtOrd_eq, hB]; dsimp only [kRun]; split_ifs with hLt hEq
          · rw [ordLookup_cons_of_lt _ _ _ hLt, ← prinSlotAtOrd_eq]
          · subst hEq; exact ordLookup_cons_eq _ _ _ _
          · exact ordLookup_of_ge (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne (Nat.le_of_not_lt hLt) (Ne.symm hEq)))
        · rw [← hTgtEq, hRes, hB]; dsimp only [List.length_cons, kRun]
          rcases lt_trichotomy pOrd hst.base.principals.length with hLt | rfl | hGt
          · simp only [beq_eq_false_iff_ne.mpr (Nat.ne_of_gt hLt), Bool.false_eq_true, ↓reduceIte, hLt, Nat.lt_succ_of_lt hLt]
          · simp only [beq_self_eq_true, ↓reduceIte, Nat.lt_irrefl, Nat.lt_succ_self]
          · simp only [beq_eq_false_iff_ne.mpr (Nat.ne_of_lt hGt), Bool.false_eq_true, ↓reduceIte,
              Nat.not_lt.mpr (Nat.le_of_lt hGt), Nat.not_lt.mpr hGt]
      refine fgStepCoupling_dh2_1Key S b P hP s0 kRun ikSk ekSk hikSk hekSk (.initPrin u) rem hst (toStaticSt1 b stA.st1) hRet.2 hRet.1 k1w
        (fun (resp, st1') => k2 (resp, updSt st1'))
        (fun r hst' st1' hD' hInv' => ?_) (fun r hst' hD' => ?_)
      · dsimp only [k1w]; split_ifs with hx
        · rcases hPost r hst' hx with ⟨hVx, hs', hk', hRes', hSp'⟩
          have hRt := toStaticSt1_fromStaticSt1_of_inv hInv' hSp'
          exact hCont r hst' _ hVx (by rwa [hs', hk'])
            ⟨by dsimp only [updSt]; rw [hRt]; rwa [hs', hk'], by dsimp only [updSt]; rw [hk']; exact hRes', hSp'⟩
        · simp
      · dsimp only [k1w]; split_ifs with hx
        · rcases hPost r hst' hx with ⟨hVx, hs', hk', _, _⟩; exact hDeadCont r hst' hVx (by rwa [hs', hk'])
        · simp
    · have hL : (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P (.initPrin u)).run hst = pure (.noneResp, hst) := by
        unfold pqxdhKeyIndFgPreImpl1KeyOrdIk; rw [StateT_run_mk]; dsimp only [pqxdhKeyIndFgPreImpl1KeyIk]
        unfold liftFgBase fgPreInitPrin1Key
        simp only [StateT_run_mk, StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, hDup, ↓reduceIte]
      have hR : (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
          P ikSk P.isValidDhTriple S b.q_total (.initPrin u)).run stA = pure (.noneResp, stA) := by
        unfold fgKeyInd1KeyActiveSimImpl; rw [StateT_run_mk]; dsimp only [fgKeyInd1KeyActiveStepPure]
        have hAP := hAnyP u; rw [toStaticSt1_sim] at hAP
        unfold fgInitPrin1KeyActivePure; simp only [hAP, hDup, ↓reduceIte]
      rw [hL, hR]; simp only [pure_bind]; exact hCont .noneResp hst stA hV hDead (fgSimInvDh2Ord_1Key_mono ⟨hInv1, hRes, hSpk⟩)
  · exact fgStepCoupling_dh2_ord_initiate b P hP sOrd pOrd ikSk ekSk hikSk hekSk true (.sendOPK u i) trivial u bdl
      (.initiateOPK u i bdl) (fun _ h => nomatch h) rem hst stA hV hDead hOrd rfl (fun _ => rfl) rfl
      (fun sIdx => by unfold fgKeyInd1KeySimImplIk; rw [StateT_run_mk]; dsimp only [fgKeyInd1KeyStepPureIk, fgKeyIndStepPure, toStaticSt1_sim]; cases bdl.opkB?.isNone <;> simp)
      k1 k2 hCont hDeadCont
  · exact fgStepCoupling_dh2_ord_initiate b P hP sOrd pOrd ikSk ekSk hikSk hekSk false (.sendNoOPK u i) trivial u bdl
      (.initiateNoOPK u i bdl) (fun _ h => nomatch h) rem hst stA hV hDead hOrd rfl (fun _ => rfl) rfl
      (fun sIdx => by unfold fgKeyInd1KeySimImplIk; rw [StateT_run_mk]; dsimp only [fgKeyInd1KeyStepPureIk, fgKeyIndStepPure, toStaticSt1_sim]; cases bdl.opkB?.isSome <;> simp)
      k1 k2 hCont hDeadCont
  · rcases hOrd with ⟨hInv1, hRes, hSpk⟩
    set s0 := sessSlotAtOrd S hst.base sOrd; set k0 := prinSlotAtOrd S hst.base pOrd
    rcases fgSimInvDh2_1Key_base_eqs hInv1 with ⟨_, _, hLenSpk, _, _⟩
    let lhsStep := (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P q).run hst
    have hLhsEq : lhsStep = (pqxdhKeyIndFgPreImpl1KeyIk s0 k0 (some ikSk) (some ekSk) S P q).run hst := by
      dsimp only [lhsStep]; unfold pqxdhKeyIndFgPreImpl1KeyOrdIk; rw [StateT_run_mk]
      rw [pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNoP,
        pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNoP,
        pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin s0 k0 ikSk ekSk P q hNoP,
        pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin s0 k0 ikSk ekSk P q hNoP]
      cases q with
      | initPrin u => exact absurd rfl (hNoP u)
      | initiateOPK u i bdl => exact absurd rfl (hNoI1 u i bdl)
      | initiateNoOPK u i bdl => exact absurd rfl (hNoI2 u i bdl)
      | _ => rfl
    have hOpt : ∀ u : Fin S.N_id, optNatMatches stA.resolvedPrin? u.val = (u.val == k0) := fun u => by
      rw [hRes]; split_ifs with hLt
      · rfl
      · have hk0N : k0 = S.N_id := by dsimp only [k0]; rw [prinSlotAtOrd_eq]; exact ordLookup_of_ge (Nat.le_of_not_lt hLt)
        rw [hk0N]; unfold optNatMatches; exact (beq_eq_false_iff_ne.mpr (Nat.ne_of_lt u.isLt)).symm
    have hBudZero := sigBudget_beq_zero_toStaticSt1 hInv1 hSpk
    rw [toStaticSt1_sim] at hLenSpk
    have hRhsEq := fgKeyInd1KeyActiveStepPure_dh2_nonInit_eq b P ikSk P.isValidDhTriple sOrd pOrd s0 k0
      (P.x25519Base ikSk) (P.x25519Base ekSk) q stA hNoP hNoI1 hNoI2 hOpt
      (by rw [hLenSpk]; exact Nat.lt_succ_of_le (Nat.le_of_add_right_le hSpk)) hBudZero
    let k1w : KeyIndResponse × KeyIndFgCutoffState S → ProbComp Bool := open scoped Classical in
      fun x => if x ∈ support lhsStep then k1 x else pure false
    rw [OracleComp.evalDist_bind_congr_of_support lhsStep k1 k1w (fun x hx => by simp only [k1w, hx, ↓reduceIte]), hLhsEq, hRhsEq]
    simp only [bind_assoc]
    have hPost : ∀ r hst', (r, hst') ∈ support lhsStep → ValidKeyIndEc S hst'.base ∧
        hst'.base.principals.length = hst.base.principals.length ∧
        prinSlotAtOrd S hst'.base pOrd = k0 ∧ sessSlotAtOrd S hst'.base sOrd = s0 ∧
        hst'.base.spkBundles.length ≤ hst.base.spkBundles.length + 1 := fun r hst' hx => by
      have hxPre : (r, hst') ∈ support ((pqxdhKeyIndFgPreImpl false s0 (SignalPqxdh.Security.FgGapDh.Ik.noSpkIdx S) (some ekSk) none S P q).run hst) := by
        rwa [hLhsEq, pqxdhKeyIndFgPreImpl1KeyIk_eq_of_ne_initPrin _ _ ikSk ekSk P q hNoP,
          pqxdhKeyIndFgPreImpl1KeyIk_eq_fgPreImpl_of_ne_initPrin _ _ ikSk ekSk P q hNoP] at hx
      rcases fgPreImpl_ne_initPrin_prin s0 _ (some ekSk) none P q hNoP hst (r, hst') hxPre with ⟨hLP', hKP', hSp'⟩
      rcases fgPreImpl_nonInit_sessions_slot s0 _ (some ekSk) none P q hNoP hNoI1 hNoI2 hst (r, hst') hxPre with ⟨_, hSS'⟩
      exact ⟨pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc sOrd pOrd ikSk ekSk P q hst hV (r, hst') hx,
        hLP', hKP' pOrd, hSS' sOrd, hSp'⟩
    refine fgStepCoupling_dh2_1Key S b P hP s0 k0 ikSk ekSk hikSk hekSk q rem hst (toStaticSt1 b stA.st1) hDead hInv1 k1w
      (fun (resp, st1') => k2 (resp, { stA with st1 := fromStaticSt1 b st1' }))
      (fun r hst' st1' hD' hInv' => ?_) (fun r hst' hD' => ?_)
    · dsimp only [k1w]; split_ifs with hx
      · rcases hPost r hst' hx with ⟨hVx, hLP', hKP', hSS', hSp'⟩
        have hSpRem : hst'.base.spkBundles.length + rem ≤ b.q_total :=
          Nat.le_trans (Nat.add_le_add_right hSp' rem) (Nat.add_assoc _ 1 rem ▸ Nat.add_comm 1 rem ▸ hSpk)
        have hRt := toStaticSt1_fromStaticSt1_of_inv hInv' hSpRem
        exact hCont r hst' _ hVx (by rwa [hSS', hKP'])
          ⟨by dsimp only; rw [hRt]; rwa [hSS', hKP'], by dsimp only; rw [hLP', hKP']; exact hRes, hSpRem⟩
      · simp
    · dsimp only [k1w]; split_ifs with hx
      · rcases hPost r hst' hx with ⟨hVx, _, hKP', hSS', _⟩; exact hDeadCont r hst' hVx (by rwa [hSS', hKP'])
      · simp

theorem prob_badKeyIndFgDh2OrdAt_1Key_le_gapDhWithSign_active_any
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) (sOrd pOrd : Nat) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A) := by
  unfold GapDhWithSignReal GapDhWithSign
  refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
  rw [← evalDist_runKeyIndFgSim1Key_eq_preSample_ord_dh2 sOrd pOrd P A.1
    (fun x => pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog))]
  rw [gapDhWithSignExp_fgKeyInd1KeyGapDhActiveAdvAtIk_eq]
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ikSk hikSk => ?_)
  have hikLen : ikSk.length = 32 := length_of_mem_support_sampleScalar32 hikSk
  refine evalDist_bind_true_mono_of_support sampleScalar32 _ _ (fun ekSk hekSk => ?_)
  have hekLen : ekSk.length = 32 := length_of_mem_support_sampleScalar32 hekSk
  refine evalDist_bind_true_mono_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact evalDist_simulateQ_le_of_step_or_dead_inv
    (fun hst : KeyIndFgCutoffState S => ValidKeyIndEc S hst.base)
    (fun hst : KeyIndFgCutoffState S =>
      deadDh2 P (sessSlotAtOrd S hst.base sOrd) (prinSlotAtOrd S hst.base pOrd) (P.x25519Base ikSk) hst)
    (FgSimInvDh2Ord_1Key S b P hP sOrd pOrd ikSk ekSk hikLen hekLen)
    (pqxdhKeyIndFgPreImpl1KeyOrdIk sOrd pOrd (some ikSk) (some ekSk) S P)
    (fgKeyInd1KeyActiveSimImpl (activeParamsDh2 b (P.x25519Base ikSk) (P.x25519Base ekSk) sOrd pOrd)
      P ikSk P.isValidDhTriple S b.q_total)
    (fun q s1 hV x hx => pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_validKeyIndEc sOrd pOrd ikSk ekSk P q s1 hV x hx)
    (fun q s1 hV hD x hx => pqxdhKeyIndFgPreImpl1KeyOrdIk_preserves_deadDh2 P sOrd pOrd ikSk ekSk q s1 hV hD x hx)
    (fun q rem s1 s2 hV hDF hOrd k1 k2 hCont hDeadCont =>
      fgStepCoupling_dh2_ord_1Key b P hP sOrd pOrd ikSk ekSk hikLen hekLen q rem s1 s2 hV hDF hOrd k1 k2 hCont hDeadCont)
    (fun x => pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.base x.2.advRoLog))
    (fun x => pure (P.pow8 (pureExtractCdh2FromAdvRoLog P.isValidDhTriple b.q_total
        (P.x25519Base ekSk) (P.x25519Base ikSk) x.2.st1.sim.advRoLog) ==
      P.pow8 (P.x25519 ikSk (P.x25519Base ekSk))))
    (fun _ s1 _ hD => by
      unfold badKeyIndFgDh2OrdAt
      simp [badKeyIndFgDh2At_eq_false_of_deadDh2 P b.q_ro _ _ (P.x25519Base ikSk) s1 hD])
    (fun a rem s1 s2 _ hDF hOrd =>
      fgSimInvDh2_1Key_terminal_le S b P hP b.q_ro _ _ ikSk ekSk hikLen hekLen a rem s1 (toStaticSt1 b s2.st1) hDF hOrd.1)
    A.1.run b.q_total A.2.2.2.2.1
    (KeyIndFgCutoffState.empty S secb)
    (FgKeyInd1KeyActiveSimState.empty S b secb)
    (validEcLists_nil S)
    ⟨(toStaticSt1_empty S b secb).symm ▸ fgSimInvDh2_1Key_empty S b P hP _ _ ikSk ekSk hikLen hekLen secb,
     by simp [FgKeyInd1KeyActiveSimState.empty, KeyIndFgCutoffState.empty, KeyIndState.empty],
     by simp [KeyIndFgCutoffState.empty, KeyIndState.empty]⟩

/-- Active creation-order `DH2` (`Ik`) per-ordinal `GapDhWithSign` bound. -/
theorem prob_badKeyIndFgDh2OrdAt_1Key_le_gapDhWithSign_active
    (S : Setup) (P : Primitives) (hP : CryptoWellFormedPrimitivesδ P)
    (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    {sOrd pOrd : Nat}
    (_hsOrd : sOrd < activeSendCount S b.q_on)
    (_hpOrd : pOrd < activeIdCount S b.q_on) :
    (𝒟[runKeyIndFgSim1Key S P A.1 >>= fun x =>
        pure (badKeyIndFgDh2OrdAt P b.q_ro sOrd pOrd x.2.2.base x.2.2.advRoLog)]
          {true}).toReal ≤
      GapDhWithSignReal P P.isValidDhTriple P.pow8
        (fgKeyInd1KeyGapDhActiveAdvAtIk sOrd pOrd S b A) :=
  prob_badKeyIndFgDh2OrdAt_1Key_le_gapDhWithSign_active_any S P hP b A sOrd pOrd

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveGapDhLegs
