/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Specifications.Pqxdh.Security.HeadlineDelta
public import Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeySigKem -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyInd1KeyGapDh -- proof-setup: allow-public-import
/-!
# Shallow Creation-Order Reductions for One-Key PQXDH `KeyInd`

Defines the shallow creation-order signature, KEM shared-key collision, and 4-leg `GapDhWithSign`
reduction adversaries (`sigReductionKeyInd1KeyActive`, `shcrReductionKeyInd1KeyActive`, and
`fgKeyInd1KeyGapDhActiveAdv4`) matching the `ReductionDsl` programs in
`KeyInd1KeyActiveProgs.lean`.
-/


set_option autoImplicit false

open OracleSpec OracleComp
open SignalPqxdh (
  Setup Bytes PrincipalEntry SpkBundleEntry OpkEntry PreKeyBundleInput
  HandshakeHdr SessionId KeyIndQuery KeyIndResponse KeyIndState
  KeyIndInitiatorEntry KeyIndAdversary keyIndSpec QueryBudget BoundedAdv
  GapSigEufCmaAdv KemShCrAdv GapDhWithSignAdv PrimBaseSpec
  gapDhOracleSpec sigAndDdhSpec sampleScalar32 sampleCoins32 sampleRandom64
  encodeEC encodeKEM activeIdCount activeSpkCount activeOpkCount
  activeSendCount activeSendOpkCount gdhQueryBudget primQueryBudget gdhPrimQueryBudget
)
open SignalPqxdh.Security (
  embedUnif primQ embedPrim isHonestUncorruptedPeerPrim findHonestPrincipalPrim
  checkBundleProvenancePrim pqxdhKeyIndImplPrim
  KeyIndShCrState liftShCrBasePrim genSpkTargetKeyIndPrim postKemKeyIndPrim
  pqxdhKeyIndShCrPrimImpl extractCollidingKemCtPrim PausedShCrData
  tryPauseKeyIndQueryPrim ShCrFinishState
  pqxdhKeyIndImpl1KeyRoPrim
)
open SignalPqxdh.Security.RoKem (sampleIndexRange)
open SignalPqxdh.Security.Sig1Key (
  SigDdhSimSpec unifSigDdh primSigDdhQ sigChalQ embedGdhSigDdh
  Sig1KeySimState runWithSigDdhStep
)
open SignalPqxdh.Security.FgGapDh (
  GdhSimSpec unifGdh primGdhQ koskBundleOkPrim resolveSigPkPrim lookupSpkSkPrim
  computeTwoSideOrPairPos computeOptPos fgPatch chooseInitPartnerDrKeyRandGdh
  FgKeyIndSimState fgRunAcceptOPKGdh fgKeyIndStep extractCdhFromSimState
)
open SignalPqxdh.Security.FgGapDh.Ik (extractCdh2FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh.Opk (fgRunAcceptOPKGdhOpk extractCdh4FromAdvRoLog)
open SignalPqxdh.Security.FgGapDh1Key (
  GdhSignSimSpec liftGdhToSign unifGdhSign primGdhSignQ
  FgKeyInd1KeySimState runWithGdhSignStep
)
open SignalPqxdh.Security.FgGapDh1Key renaming sigChalQ → sigChalQGdh
open Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveProgs (activeSigBudget fgActiveTotalIndexCount)

namespace Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow

public section
@[expose] def optNatMatches (tp? : Option Nat) (u : Nat) : Bool :=
  match tp? with
  | none   => false
  | some t => u == t

@[simp] theorem optNatMatches_none (u : Nat) : optNatMatches none u = false := rfl

@[simp] theorem optNatMatches_some (t u : Nat) : optNatMatches (some t) u = (u == t) := rfl

/-! ## Creation-order one-key `GapSigEufCma` reduction -/

/-- Active simulator state `(resolvedPrin?, inner)` for `sigReductionKeyInd1KeyActive`, where
    `inner.targetParty` holds the target creation ordinal and `resolvedPrin?` records the concrete
    principal ID once initialized. -/
structure Sig1KeyActiveSimState (S : Setup) where
  resolvedPrin? : Option Nat
  inner         : Sig1KeySimState S

@[expose] def Sig1KeyActiveSimState.empty (S : Setup) (b : QueryBudget) (secb : Bool) (targetOrd : Nat)
    (targetPk : Bytes) : Sig1KeyActiveSimState S where
  resolvedPrin? := none
  inner         := { Sig1KeySimState.empty S secb targetOrd targetPk with
                     signBudget := activeSigBudget S b }

@[expose] def extractBundleForgeryActivePrim (S : Setup) (resolvedPrin? : Option Nat) (targetPk : Bytes)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (bundle : PreKeyBundleInput)
    (prevForgery : Option (Bytes × Bytes)) :
    OracleComp PrimBaseSpec (Option (Bytes × Bytes)) := do
  let peer? ← isHonestUncorruptedPeerPrim S principals bundle.ikB
  let v1 ← primQ (.sigVerify targetPk (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primQ (.sigVerify targetPk (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  return match prevForgery with
    | some fg => some fg
    | none =>
      match peer? with
      | none => none
      | some k =>
        if optNatMatches resolvedPrin? k then
          let spkMinted := spkBundles.any (fun ((u, _), b) => u == k && b.spkPk == bundle.spkB)
          let pqspkMinted :=
            spkBundles.any (fun ((u, _), b) => u == k && b.pqspkPk == bundle.pqspkB)
          if v1 && !spkMinted then
            some (encodeEC bundle.spkB, bundle.spkSig)
          else if v2 && !pqspkMinted then
            some (encodeKEM bundle.pqspkB, bundle.pqspkSig)
          else
            none
        else
          none

@[expose] def sig1KeyTargetGenSpk (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv)
    (st : Sig1KeySimState S) : OracleComp SigDdhSimSpec (KeyIndResponse × Sig1KeySimState S) := do
  if st.fg.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
    return (.noneResp, st)
  let some (_, uEntry) := st.fg.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  match st.signBudget with
  | 0 => return (.noneResp, st)
  | signBudget' + 1 =>
    let spkSk ← unifSigDdh sampleScalar32
    let spkPk ← primSigDdhQ (.x25519Base spkSk)
    let spkSig ← sigChalQ (encodeEC spkPk)
    let seedKem ← unifSigDdh sampleRandom64
    let (pqspkPk, pqspkSk) ← primSigDdhQ (.kemKeyGen seedKem)
    let pqspkSig ← sigChalQ (encodeKEM pqspkPk)
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    let base' :=
      { st.fg.base with spkBundles := ((u.val, j.val), bEntry) :: st.fg.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return (.bundleResp bundleOut,
      { st with fg := { st.fg with base := base' }, signBudget := signBudget' })

@[expose] def sig1KeyActiveStep (S : Setup) (maxLen : Nat) (q : KeyIndQuery S)
    (st : Sig1KeyActiveSimState S) :
    OracleComp SigDdhSimSpec (KeyIndResponse × Sig1KeyActiveSimState S) := do
  if st.inner.forgery.isSome then
    return (.noneResp, st)
  match q with
  | .initPrin u =>
    if st.inner.fg.base.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, st)
    let secIKA0Raw ← unifSigDdh sampleScalar32
    let ikAPkRaw ← primSigDdhQ (.x25519Base secIKA0Raw)
    let isTarget : Bool := st.inner.fg.base.principals.length == st.inner.targetParty
    let sec := if isTarget then [] else secIKA0Raw
    let pk := if isTarget then st.inner.targetPk else ikAPkRaw
    let tp' := if isTarget then some u.val else st.resolvedPrin?
    let entry : PrincipalEntry := {
      secIKA0    := sec
      ikAPk      := pk
      secIKAsign := sec
      ikSignPk   := pk
      corrupted  := false
    }
    let base' :=
      { st.inner.fg.base with principals := (u.val, entry) :: st.inner.fg.base.principals }
    return (.initPrinResp pk pk,
      { resolvedPrin? := tp'
        inner := { st.inner with fg := { st.inner.fg with base := base' } } })
  | .genSPK u j =>
    if optNatMatches st.resolvedPrin? u.val then
      let (out, inner') ← sig1KeyTargetGenSpk S u j st.inner
      return (out, { st with inner := inner' })
    else
      let (out, fg') ← embedGdhSigDdh
        (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.inner.targetPk
          (.genSPK u j) st.inner.fg)
      return (out, { st with inner := { st.inner with fg := fg' } })
  | .initiateOPK u i bundle =>
    let forgery' ← embedPrim (spec := sigAndDdhSpec)
      (extractBundleForgeryActivePrim S st.resolvedPrin? st.inner.targetPk
        st.inner.fg.base.principals st.inner.fg.base.spkBundles bundle st.inner.forgery)
    if forgery'.isSome then
      return (.noneResp, { st with inner := { st.inner with forgery := forgery' } })
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.inner.targetPk
        (.initiateOPK u i bundle) st.inner.fg)
    return (out, { st with inner := { st.inner with fg := fg' } })
  | .initiateNoOPK u i bundle =>
    let forgery' ← embedPrim (spec := sigAndDdhSpec)
      (extractBundleForgeryActivePrim S st.resolvedPrin? st.inner.targetPk
        st.inner.fg.base.principals st.inner.fg.base.spkBundles bundle st.inner.forgery)
    if forgery'.isSome then
      return (.noneResp, { st with inner := { st.inner with forgery := forgery' } })
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.inner.targetPk
        (.initiateNoOPK u i bundle) st.inner.fg)
    return (out, { st with inner := { st.inner with fg := fg' } })
  | q_other =>
    let (out, fg') ← embedGdhSigDdh
      (fgKeyIndStep false S.N_send_tot S.N_spk_tot S maxLen [] st.inner.targetPk
        q_other st.inner.fg)
    return (out, { st with inner := { st.inner with fg := fg' } })

@[expose] def sigReductionKeyInd1KeyActiveRunAt (targetOrd : Nat) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (pk : Bytes) :
    OracleComp SigDdhSimSpec (Bytes × Bytes) := do
  let secb ← unifSigDdh ($ᵗ Bool)
  let initSt := Sig1KeyActiveSimState.empty S b secb targetOrd pk
  let (_, finalSt) ← runWithSigDdhStep (sig1KeyActiveStep S b.q_total) A.1.run initSt
  return finalSt.inner.forgery.getD ([], [])

@[expose] def sigReductionKeyInd1KeyActiveAt (targetOrd : Nat) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run pk := sigReductionKeyInd1KeyActiveRunAt targetOrd S b A pk
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_ddh  := gdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-- Creation-order `GapSigEufCmaAdv` for one-key PQXDH `KeyInd` matching
    `sigKeyInd1KeyActiveDslProg S b`. -/
@[expose] def sigReductionKeyInd1KeyActive (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapSigEufCmaAdv where
  run pk := do
    let n_id := activeIdCount S b.q_on
    let k ← unifSigDdh (sampleIndexRange n_id)
    let targetOrd := if n_id = 0 then b.q_total + 1 else k
    sigReductionKeyInd1KeyActiveRunAt targetOrd S b A pk
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_ddh  := gdhQueryBudget S b
  q_prim := gdhPrimQueryBudget S b

/-! ## Creation-order one-key `KemShCr` reduction -/

@[expose] def runKeyIndShCrActiveGenSPKPrim (embedTarget : Bool) (S : Setup)
    (u : Fin S.N_id) (j : Fin S.N_recv) :
    StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec) KeyIndResponse := fun hst =>
  if !embedTarget then
    (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst
  else
    match hst.targetBIdx? with
    | none => (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst
    | some spkOrd =>
      if hst.base.spkBundles.length == spkOrd then
        (genSpkTargetKeyIndPrim S u j).run hst
      else
        (liftShCrBasePrim (pqxdhKeyIndImplPrim true S (.genSPK u j))).run hst

@[expose] def pqxdhKeyIndShCrActivePrimImpl1Key (embedTarget : Bool) (S : Setup) :
    QueryImpl (keyIndSpec S) (StateT (KeyIndShCrState S) (OracleComp PrimBaseSpec))
  | .initPrin u => liftShCrBasePrim (pqxdhKeyIndImpl1KeyRoPrim S (.initPrin u))
  | .genSPK u j => runKeyIndShCrActiveGenSPKPrim embedTarget S u j
  | q_other     => pqxdhKeyIndShCrPrimImpl embedTarget S q_other

@[expose] def runWithFuelKeyInd1KeyActiveShCrPrim (S : Setup)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : Nat) :
    OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → Nat → OracleComp PrimBaseSpec (Bool × KeyIndShCrState S))
    (fun b hst _ => return (b, hst))
    (fun q _ r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return (false, hst)
        | f + 1 => do
          let (out, hst') ← (pqxdhKeyIndShCrActivePrimImpl1Key true S gq).run hst
          r out hst' f)
    oa hst fuel

@[expose] def stepUntilShCrFuelKeyInd1KeyActivePrim (S : Setup) (sIdx : Nat)
    (oa : OracleComp (unifSpec + keyIndSpec S) Bool)
    (hst : KeyIndShCrState S) (fuel : Nat) :
    OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)) :=
  OracleComp.construct
    (C := fun _ => KeyIndShCrState S → Nat →
      OracleComp PrimBaseSpec (Sum (Bool × KeyIndShCrState S) (PausedShCrData S)))
    (fun b hst _ => return Sum.inl (b, hst))
    (fun q cont r hst fuel =>
      match q with
      | Sum.inl uq => do
        let u ← embedUnif (liftM (OracleSpec.query (spec := unifSpec) uq))
        r u hst fuel
      | Sum.inr gq =>
        match fuel with
        | 0 => return Sum.inl (false, hst)
        | f + 1 => do
          match ← tryPauseKeyIndQueryPrim S sIdx gq cont hst with
          | some d => return Sum.inr d
          | none =>
            let (out, hst') ← (pqxdhKeyIndShCrActivePrimImpl1Key true S gq).run hst
            r out hst' f)
    oa hst fuel

@[expose] def resumePausedKeyInd1KeyActivePrim (S : Setup) (fuel : Nat) (d : PausedShCrData S)
    (ss kemCt : Bytes) : OracleComp PrimBaseSpec (Bool × KeyIndShCrState S) := do
  let (resp, hst') ← postKemKeyIndPrim S d.sid d.bundle d.uEntry d.hst ss kemCt
  runWithFuelKeyInd1KeyActiveShCrPrim S (d.cont resp) hst' fuel

@[expose] def choosePkKeyInd1KeyActivePrimAt (S : Setup) (b : QueryBudget) (tb? : Option Nat) (sIdx : Nat)
    (A : KeyIndAdversary S) (pk sk : Bytes) :
    OracleComp PrimBaseSpec (Bytes × ShCrFinishState S) := do
  let secb ← embedUnif ($ᵗ Bool)
  let initSt : KeyIndShCrState S := {
    base        := KeyIndState.empty S secb
    targetBIdx? := tb?
    targetPk    := pk
    targetSk    := sk
  }
  let res ← stepUntilShCrFuelKeyInd1KeyActivePrim S sIdx A.run initSt b.q_total
  let chosenPk := match res with
    | Sum.inl _ => pk
    | Sum.inr d => d.bundle.pqspkB
  return (chosenPk, (pk, sk, chosenPk, res))

@[expose] def findCollisionKeyInd1KeyActivePrim (S : Setup) (b : QueryBudget)
    (st : ShCrFinishState S) (ss ct : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let (pk, sk, chosenPk, res) := st
  let (_, finalHst) ← match res with
    | Sum.inl done => pure done
    | Sum.inr d    => resumePausedKeyInd1KeyActivePrim S b.q_total d ss ct
  extractCollidingKemCtPrim b.q_total pk sk chosenPk ct ss finalHst.recvKemRecs

@[expose] def shcrReductionKeyInd1KeyActiveAt (tb? : Option Nat) (sIdx : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv where
  State         := ShCrFinishState S
  choosePk      := choosePkKeyInd1KeyActivePrimAt S b tb? sIdx A.1
  findCollision := findCollisionKeyInd1KeyActivePrim S b
  q_prim        := primQueryBudget S b

@[expose] def shcrReductionKeyInd1KeyActiveCore (S : Setup) (b : QueryBudget)
    (A : KeyIndAdversary S) : KemShCrAdv where
  State := ShCrFinishState S
  choosePk := fun pk sk => do
    let n_spk := activeSpkCount S b.q_on
    let n_send := activeSendCount S b.q_on
    let n_prod := n_spk * n_send
    let idx ← embedUnif (sampleIndexRange n_prod)
    let tb? : Option Nat := if n_prod = 0 then none else some (idx / n_send)
    let sIdx : Nat := if n_prod = 0 then b.q_total + 1 else idx % n_send
    choosePkKeyInd1KeyActivePrimAt S b tb? sIdx A pk sk
  findCollision := findCollisionKeyInd1KeyActivePrim S b
  q_prim := primQueryBudget S b

/-- Creation-order `KemShCrAdv` for one-key PQXDH `KeyInd` matching
    `shcrKeyInd1KeyActiveDslProg S b`. -/
@[expose] def shcrReductionKeyInd1KeyActive (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : KemShCrAdv :=
  shcrReductionKeyInd1KeyActiveCore S b A.1

/-! ## Creation-order one-key `GapDhWithSign` reduction -/

/-- Shallow parameter record corresponding to `paramsTy` in `KeyInd1KeyActiveProgs.lean`. -/
structure FgActiveParams where
  U        : Bytes
  V        : Bytes
  Up       : Bytes
  prinFlag : Bool
  prinIdx  : Nat
  dhFlag   : Bool
  ephIdx   : Nat
  spkIdx   : Nat
  opkMode  : Bool
  opkIdx   : Nat
  mode     : Nat

@[expose] def activeParamsDh1 (b : QueryBudget) (U V : Bytes) (prinOrd spkOrd : Nat) : FgActiveParams :=
  let unreach := b.q_total + 1
  { U := U, V := V, Up := U
    prinFlag := true, prinIdx := prinOrd
    dhFlag := true, ephIdx := unreach, spkIdx := spkOrd
    opkMode := false, opkIdx := unreach, mode := 0 }

@[expose] def activeParamsDh3 (b : QueryBudget) (U V : Bytes) (ephOrd spkOrd : Nat) : FgActiveParams :=
  let unreach := b.q_total + 1
  { U := U, V := V, Up := U
    prinFlag := false, prinIdx := unreach
    dhFlag := false, ephIdx := ephOrd, spkIdx := spkOrd
    opkMode := false, opkIdx := unreach, mode := 1 }

@[expose] def activeParamsDh2 (b : QueryBudget) (U V : Bytes) (ephOrd prinOrd : Nat) : FgActiveParams :=
  let unreach := b.q_total + 1
  { U := V, V := U, Up := U
    prinFlag := true, prinIdx := prinOrd
    dhFlag := false, ephIdx := ephOrd, spkIdx := unreach
    opkMode := false, opkIdx := unreach, mode := 2 }

@[expose] def activeParamsDh4 (b : QueryBudget) (U V : Bytes) (ephOpkOrd opkOrd : Nat) : FgActiveParams :=
  let unreach := b.q_total + 1
  { U := U, V := V, Up := U
    prinFlag := false, prinIdx := unreach
    dhFlag := false, ephIdx := ephOpkOrd, spkIdx := unreach
    opkMode := true, opkIdx := opkOrd, mode := 3 }

@[expose] def activeParamsZero (b : QueryBudget) (U V : Bytes) : FgActiveParams :=
  let unreach := b.q_total + 1
  { U := U, V := V, Up := U
    prinFlag := false, prinIdx := unreach
    dhFlag := true, ephIdx := unreach, spkIdx := unreach
    opkMode := false, opkIdx := unreach, mode := 0 }

/-- Decodes a flat index `idx < fgActiveTotalIndexCount S b.q_on` into `FgActiveParams`. -/
@[expose] def activeParamsFlat (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat) : FgActiveParams :=
  let n_id := activeIdCount S b.q_on
  let n_spk := activeSpkCount S b.q_on
  let n_opk := activeOpkCount S b.q_on
  let n_send := activeSendCount S b.q_on
  let nA := n_id * n_spk
  let nC := n_send * n_spk
  let nB := n_send * n_id
  let tot := fgActiveTotalIndexCount S b.q_on
  if tot = 0 then
    activeParamsZero b U V
  else if idx < nA then
    activeParamsDh1 b U V (idx / n_spk) (idx % n_spk)
  else if idx < nA + nC then
    let r := idx - nA
    activeParamsDh3 b U V (r / n_spk) (r % n_spk)
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    activeParamsDh2 b U V (r / n_id) (r % n_id)
  else
    let r := idx - (nA + nC + nB)
    activeParamsDh4 b U V (r / n_opk) (r % n_opk)

/-- Shallow simulator state mirroring `gdh1KeyActiveStateTy`: `st1` holds `(sim, sigBudget)`,
    `resolvedPrin?` records the target principal ID, and `sendOpkCnt` counts completed
    `.initiateOPK` sessions. -/
structure FgKeyInd1KeyActiveSimState (S : Setup) where
  st1           : FgKeyInd1KeySimState S
  resolvedPrin? : Option Nat
  sendOpkCnt    : Nat

@[expose] def FgKeyInd1KeyActiveSimState.empty (S : Setup) (b : QueryBudget) (secb : Bool) : FgKeyInd1KeyActiveSimState S where
  st1           := { FgKeyInd1KeySimState.empty S secb with sigBudget := activeSigBudget S b }
  resolvedPrin? := none
  sendOpkCnt    := 0

@[expose] def liftSimStep1KeyActive {S : Setup}
    (f : FgKeyIndSimState S → OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S))
    (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  let (resp, sim') ← liftGdhToSign (f stA.st1.sim)
  return (resp, { stA with st1 := { stA.st1 with sim := sim' } })

@[expose] def fgInitPrin1KeyActiveGdh {S : Setup} (prinFlag : Bool) (prinIdx : Nat) (Up : Bytes)
    (u : Fin S.N_id) (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.principals.any (fun (idx, _) => idx == u.val) then
    return (.noneResp, stA)
  let isTargetPrin : Bool := prinFlag && (stA.st1.sim.base.principals.length == prinIdx)
  let sk0 ← unifGdhSign sampleScalar32
  let pk0 ← primGdhSignQ (.x25519Base sk0)
  let sec0 := if isTargetPrin then [] else sk0
  let ikPk := if isTargetPrin then Up else pk0
  let entry : PrincipalEntry := {
    secIKA0    := sec0
    ikAPk      := ikPk
    secIKAsign := sec0
    ikSignPk   := ikPk
    corrupted  := false
  }
  let base' :=
    { stA.st1.sim.base with principals := (u.val, entry) :: stA.st1.sim.base.principals }
  let tp' := if isTargetPrin then some u.val else stA.resolvedPrin?
  return (.initPrinResp ikPk ikPk,
    { stA with
      st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } }
      resolvedPrin? := tp' })

@[expose] def fgGenSpkActiveGdh {S : Setup} (spkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (st : FgKeyIndSimState S) :
    OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
    return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let isTargetSpk : Bool := st.base.spkBundles.length == spkIdx
  let spkSkRaw ← unifGdh sampleScalar32
  let spkPkRaw ← primGdhQ (.x25519Base spkSkRaw)
  let spkSk := if isTargetSpk then [] else spkSkRaw
  let spkPk := if isTargetSpk then V else spkPkRaw
  let rSpk ← unifGdh sampleRandom64
  let spkSig ← primGdhQ (.sigSign uEntry.secIKAsign (encodeEC spkPk) rSpk)
  let seedKem ← unifGdh sampleRandom64
  let (pqspkPk, pqspkSk) ← primGdhQ (.kemKeyGen seedKem)
  let rPq ← unifGdh sampleRandom64
  let pqspkSig ← primGdhQ (.sigSign uEntry.secIKAsign (encodeKEM pqspkPk) rPq)
  let bEntry : SpkBundleEntry := {
    spkSk    := spkSk
    spkPk    := spkPk
    spkSig   := spkSig
    pqspkSk  := pqspkSk
    pqspkPk  := pqspkPk
    pqspkSig := pqspkSig
  }
  let base' := { st.base with spkBundles := ((u.val, j.val), bEntry) :: st.base.spkBundles }
  let bundleOut : PreKeyBundleInput := {
    ikB      := uEntry.ikAPk
    spkId    := UInt32.ofNat j.val
    spkB     := spkPk
    spkSig   := spkSig
    opkB?    := none
    pqspkId  := UInt32.ofNat j.val
    pqspkB   := pqspkPk
    pqspkSig := pqspkSig
  }
  return (.bundleResp bundleOut, { st with base := base' })

@[expose] def fgGenSPK1KeyActiveGdh {S : Setup} (spkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if optNatMatches stA.resolvedPrin? u.val then
    if stA.st1.sim.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, stA)
    let some (_, uEntry) := stA.st1.sim.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, stA)
    if stA.st1.sigBudget == 0 then
      return (.noneResp, stA)
    let isTargetSpk : Bool := stA.st1.sim.base.spkBundles.length == spkIdx
    let spkSkRaw ← unifGdhSign sampleScalar32
    let spkPkRaw ← primGdhSignQ (.x25519Base spkSkRaw)
    let spkSk := if isTargetSpk then [] else spkSkRaw
    let spkPk := if isTargetSpk then V else spkPkRaw
    let spkSig ← sigChalQGdh (encodeEC spkPk)
    let seedKem ← unifGdhSign sampleRandom64
    let (pqspkPk, pqspkSk) ← primGdhSignQ (.kemKeyGen seedKem)
    let pqspkSig ← sigChalQGdh (encodeKEM pqspkPk)
    let bEntry : SpkBundleEntry := {
      spkSk    := spkSk
      spkPk    := spkPk
      spkSig   := spkSig
      pqspkSk  := pqspkSk
      pqspkPk  := pqspkPk
      pqspkSig := pqspkSig
    }
    let base' :=
      { stA.st1.sim.base with
        spkBundles := ((u.val, j.val), bEntry) :: stA.st1.sim.base.spkBundles }
    let bundleOut : PreKeyBundleInput := {
      ikB      := uEntry.ikAPk
      spkId    := UInt32.ofNat j.val
      spkB     := spkPk
      spkSig   := spkSig
      opkB?    := none
      pqspkId  := UInt32.ofNat j.val
      pqspkB   := pqspkPk
      pqspkSig := pqspkSig
    }
    return (.bundleResp bundleOut,
      { stA with
        st1 := { sim := { stA.st1.sim with base := base' }
                 sigBudget := stA.st1.sigBudget - 1 } })
  else
    liftSimStep1KeyActive (fgGenSpkActiveGdh spkIdx V u j) stA

@[expose] def fgGenOPKActiveGdh {S : Setup} (opkMode : Bool) (opkIdx : Nat) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  if stA.st1.sim.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
    return (.noneResp, stA)
  let isTargetOpk : Bool := opkMode && (stA.st1.sim.base.opkEntries.length == opkIdx)
  let opkSkRaw ← unifGdhSign sampleScalar32
  let opkPkRaw ← primGdhSignQ (.x25519Base opkSkRaw)
  let oEntry : OpkEntry := {
    opkSk    := if isTargetOpk then [] else opkSkRaw
    opkPk    := if isTargetOpk then V else opkPkRaw
    consumed := false
  }
  let base' :=
    { stA.st1.sim.base with
      opkEntries := ((u.val, j.val, o.val), oEntry) :: stA.st1.sim.base.opkEntries }
  return (.pkResp oEntry.opkPk,
    { stA with st1 := { stA.st1 with sim := { stA.st1.sim with base := base' } } })

@[expose] def fgRunInitiateActiveGdh (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup) (maxLen : Nat)
    (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (st : FgKeyIndSimState S) (sendOpkCnt : Nat) :
    OracleComp GdhSimSpec (KeyIndResponse × (FgKeyIndSimState S × Nat)) := do
  let guardOk : Bool := if hasOpk then bundle.opkB?.isSome else !bundle.opkB?.isSome
  if !guardOk then
    return (.noneResp, (st, sendOpkCnt))
  if st.base.sessions.any (fun e => e.sid == sid) then
    return (.noneResp, (st, sendOpkCnt))
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, (st, sendOpkCnt))
  let bundleOk ← embedPrim (spec := gapDhOracleSpec)
    (koskBundleOkPrim S st.base.principals st.base.spkBundles
      st.base.opkEntries st.advKeyPows bundle)
  if !bundleOk then
    return (.noneResp, (st, sendOpkCnt))
  let isTargetEph : Bool :=
    if hasOpk then
      (!dhFlag) && ((if opkMode then sendOpkCnt else st.base.sessions.length) == ephIdx)
    else
      (!dhFlag) && ((!opkMode) && (st.base.sessions.length == ephIdx))
  let ekASkRaw ← unifGdh sampleScalar32
  let kemCoins ← unifGdh sampleCoins32
  let sigPkB ← embedPrim (spec := gapDhOracleSpec)
    (resolveSigPkPrim S st.base.principals bundle.ikB)
  let v1 ← primGdhQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primGdhQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  if !(v1 && v2) then
    return (.noneResp, (st, sendOpkCnt))
  let some (ss, kemCt) ← primGdhQ (.kemEncaps bundle.pqspkB kemCoins)
    | return (.noneResp, (st, sendOpkCnt))
  let ekAPkRaw ← primGdhQ (.x25519Base ekASkRaw)
  let ekASk := if isTargetEph then [] else ekASkRaw
  let ekAPk := if isTargetEph then U else ekAPkRaw
  let spkSk ← embedPrim (spec := gapDhOracleSpec)
    (lookupSpkSkPrim S st.base.spkBundles st.advKeyPows bundle.spkB)
  let pos1 ← computeTwoSideOrPairPos uEntry.secIKA0 spkSk uEntry.ikAPk bundle.spkB
  let pos2 ← computeTwoSideOrPairPos ekASk [] ekAPk bundle.ikB
  let pos3 ← computeTwoSideOrPairPos ekASk [] ekAPk bundle.spkB
  let pos4? ← computeOptPos ekASk ekAPk (bundle.opkB?.map (fun (_, opkPk) => ([], opkPk)))
  let (drKeyReal, fgL') ← fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL
  let hdr : HandshakeHdr := {
    ikAPk   := uEntry.ikAPk
    ekAPk   := ekAPk
    spkId   := bundle.spkId
    opkId?  := bundle.opkB?.map Prod.fst
    pqspkId := bundle.pqspkId
    kemCt   := kemCt
  }
  let honestPeer ← embedPrim (spec := gapDhOracleSpec)
    (isHonestUncorruptedPeerPrim S st.base.principals bundle.ikB)
  let (spkHon, opkHon, pqspkHon) ← embedPrim (spec := gapDhOracleSpec)
    (checkBundleProvenancePrim S st.base.principals st.base.spkBundles st.base.opkEntries bundle)
  let sessEntry : KeyIndInitiatorEntry S := {
    sid         := sid
    honestPeer  := honestPeer
    peerIkPk    := bundle.ikB
    peerSpkPk   := bundle.spkB
    peerOpkPk?  := bundle.opkB?.map Prod.snd
    peerPqspkPk := bundle.pqspkB
    spkHonest   := spkHon
    opkHonest   := opkHon
    pqspkHonest := pqspkHon
    ekASk       := ekASk
    fresh       := honestPeer.isSome
    drKeyReal   := drKeyReal
    drKeyRand   := drKeyReal
    hdr         := hdr
    tested      := false
  }
  let drKeyRand ← chooseInitPartnerDrKeyRandGdh st.base.respSessions sessEntry
  let sess' := { sessEntry with drKeyRand := drKeyRand } :: st.base.sessions
  let base' : KeyIndState S := { st.base with sessions := sess' }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  let cnt' : Nat := if hasOpk then sendOpkCnt + 1 else sendOpkCnt
  match ← embedPrim (spec := gapDhOracleSpec)
      (findHonestPrincipalPrim S st.base.principals bundle.ikB) with
  | some _ => return (.hdrResp hdr, (st', cnt'))
  | none   => return (.initUnfreshResp drKeyReal hdr, (st', cnt'))

@[expose] def fgInitiateActiveGdh (dhFlag opkMode : Bool) (ephIdx : Nat) (S : Setup) (maxLen : Nat)
    (U : Bytes) (hasOpk : Bool) (sid : SessionId S) (u : Fin S.N_id)
    (bundle : PreKeyBundleInput) (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) := do
  let (resp, (sim', cnt')) ←
    liftGdhToSign
      (fgRunInitiateActiveGdh dhFlag opkMode ephIdx S maxLen U hasOpk sid u bundle
        stA.st1.sim stA.sendOpkCnt)
  return (resp, { stA with st1 := { stA.st1 with sim := sim' }, sendOpkCnt := cnt' })

@[expose] def fgKeyInd1KeyActiveStep (pa : FgActiveParams) (S : Setup) (maxLen : Nat)
    (q : KeyIndQuery S) (stA : FgKeyInd1KeyActiveSimState S) :
    OracleComp GdhSignSimSpec (KeyIndResponse × FgKeyInd1KeyActiveSimState S) :=
  match q with
  | .initPrin u =>
    fgInitPrin1KeyActiveGdh pa.prinFlag pa.prinIdx pa.Up u stA
  | .genSPK u j =>
    fgGenSPK1KeyActiveGdh pa.spkIdx pa.V u j stA
  | .genOPK u j o =>
    fgGenOPKActiveGdh pa.opkMode pa.opkIdx pa.V u j o stA
  | .initiateOPK u i bundle =>
    fgInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U true (.sendOPK u i) u bundle stA
  | .initiateNoOPK u i bundle =>
    fgInitiateActiveGdh pa.dhFlag pa.opkMode pa.ephIdx S maxLen pa.U false (.sendNoOPK u i) u bundle stA
  | .acceptOPK k j o hdr =>
    liftSimStep1KeyActive
      (if pa.opkMode then
         fgRunAcceptOPKGdhOpk S maxLen k j o hdr
       else
         fgRunAcceptOPKGdh S maxLen k j o hdr) stA
  | q_other =>
    liftSimStep1KeyActive
      (fgKeyIndStep pa.dhFlag pa.ephIdx pa.spkIdx S maxLen pa.U pa.V q_other) stA

@[expose] def fgKeyInd1KeyActiveFinish (pa : FgActiveParams) (S : Setup) (maxLen : Nat)
    (stA : FgKeyInd1KeyActiveSimState S) : OracleComp GdhSignSimSpec Bytes :=
  if pa.mode == 0 then
    liftGdhToSign (extractCdhFromSimState S true maxLen pa.U pa.V stA.st1.sim)
  else if pa.mode == 1 then
    liftGdhToSign (extractCdhFromSimState S false maxLen pa.U pa.V stA.st1.sim)
  else if pa.mode == 2 then
    liftGdhToSign (extractCdh2FromAdvRoLog maxLen pa.U pa.V stA.st1.sim.advRoLog)
  else
    liftGdhToSign (extractCdh4FromAdvRoLog maxLen pa.U pa.V stA.st1.sim.advRoLog)

@[expose] def fgKeyInd1KeyActiveRunWithParams (pa : FgActiveParams) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : OracleComp GdhSignSimSpec Bytes := do
  let secb ← unifGdhSign ($ᵗ Bool)
  let initSt := FgKeyInd1KeyActiveSimState.empty S b secb
  let (_, finalSt) ← runWithGdhSignStep (fgKeyInd1KeyActiveStep pa S b.q_total) A.1.run initSt
  fgKeyInd1KeyActiveFinish pa S b.q_total finalSt

@[expose] def fgKeyInd1KeyGapDhActiveAdvAt (useDh1 : Bool) (ord1 spkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V :=
    let pa := if useDh1 then activeParamsDh1 b U V ord1 spkOrd
              else activeParamsDh3 b U V ord1 spkOrd
    fgKeyInd1KeyActiveRunWithParams pa S b A
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

@[expose] def fgKeyInd1KeyGapDhActiveAdvAtIk (ephOrd prinOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyActiveRunWithParams (activeParamsDh2 b U V ephOrd prinOrd) S b A
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

@[expose] def fgKeyInd1KeyGapDhActiveAdvAtOpk (ephOpkOrd opkOrd : Nat)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyActiveRunWithParams (activeParamsDh4 b U V ephOpkOrd opkOrd) S b A
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

@[expose] def fgKeyInd1KeyGapDhActiveRunAtFlat (idx : Nat) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) : OracleComp GdhSignSimSpec Bytes :=
  fgKeyInd1KeyActiveRunWithParams (activeParamsFlat S b U V idx) S b A

@[expose] def fgKeyInd1KeyGapDhActiveAdvAtFlat (idx : Nat) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A U V
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

/-- Creation-order 4-leg `GapDhWithSignAdv` for one-key PQXDH `KeyInd` matching
    `fgKeyInd1KeyGapDhActiveDslProg S b`. -/
@[expose] def fgKeyInd1KeyGapDhActiveAdv4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhWithSignAdv where
  run U V := do
    let idx ← unifGdhSign (sampleIndexRange (fgActiveTotalIndexCount S b.q_on))
    fgKeyInd1KeyGapDhActiveRunAtFlat idx S b A U V
  q_ddh  := gdhQueryBudget S b
  q_sig  := 2 * min S.N_spk_tot S.N_recv
  q_prim := gdhPrimQueryBudget S b

/-! ## Flat-index branch lemmas -/

theorem activeParamsFlat_eq_zero (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat)
    (h0 : fgActiveTotalIndexCount S b.q_on = 0) :
    activeParamsFlat S b U V idx = activeParamsZero b U V := by
  simp [activeParamsFlat, h0]

theorem activeParamsFlat_mode_lt4 (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat) :
    (activeParamsFlat S b U V idx).mode = 0 ∨
      (activeParamsFlat S b U V idx).mode = 1 ∨
      (activeParamsFlat S b U V idx).mode = 2 ∨
      (activeParamsFlat S b U V idx).mode = 3 := by
  dsimp only [activeParamsFlat]
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl rfl)
      · split
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr rfl))

theorem activeParamsFlat_dh1 (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat)
    (h : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on) :
    activeParamsFlat S b U V idx =
      activeParamsDh1 b U V (idx / activeSpkCount S b.q_on) (idx % activeSpkCount S b.q_on) := by
  have htot : fgActiveTotalIndexCount S b.q_on ≠ 0 := by
    dsimp only [fgActiveTotalIndexCount]; omega
  simp [activeParamsFlat, htot, h]

theorem activeParamsFlat_dh3 (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat)
    (h1 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on)
    (h2 : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeSpkCount S b.q_on) :
    let r := idx - activeIdCount S b.q_on * activeSpkCount S b.q_on
    activeParamsFlat S b U V idx =
      activeParamsDh3 b U V (r / activeSpkCount S b.q_on) (r % activeSpkCount S b.q_on) := by
  have htot : fgActiveTotalIndexCount S b.q_on ≠ 0 := by
    dsimp only [fgActiveTotalIndexCount]; omega
  simp [activeParamsFlat, htot, h1, h2]

theorem activeParamsFlat_dh2 (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat)
    (h2 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeSpkCount S b.q_on)
    (h3 : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeIdCount S b.q_on) :
    let r := idx - (activeIdCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeSpkCount S b.q_on)
    activeParamsFlat S b U V idx =
      activeParamsDh2 b U V (r / activeIdCount S b.q_on) (r % activeIdCount S b.q_on) := by
  have h1 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on := by omega
  have htot : fgActiveTotalIndexCount S b.q_on ≠ 0 := by
    dsimp only [fgActiveTotalIndexCount]; omega
  simp [activeParamsFlat, htot, h1, h2, h3]

theorem activeParamsFlat_dh4 (S : Setup) (b : QueryBudget) (U V : Bytes) (idx : Nat)
    (h3 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeIdCount S b.q_on)
    (h4 : idx < fgActiveTotalIndexCount S b.q_on) :
    let r := idx - (activeIdCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeIdCount S b.q_on)
    activeParamsFlat S b U V idx =
      activeParamsDh4 b U V (r / activeOpkCount S b.q_on) (r % activeOpkCount S b.q_on) := by
  have h1 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on := by omega
  have h2 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeSpkCount S b.q_on := by omega
  have htot : fgActiveTotalIndexCount S b.q_on ≠ 0 := by omega
  simp [activeParamsFlat, htot, h1, h2, h3]

theorem fgKeyInd1KeyGapDhActiveAdvAtFlat_dh1 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (idx : Nat)
    (h : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on) :
    fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A =
      fgKeyInd1KeyGapDhActiveAdvAt true
        (idx / activeSpkCount S b.q_on) (idx % activeSpkCount S b.q_on) S b A := by
  unfold fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveRunAtFlat
    fgKeyInd1KeyGapDhActiveAdvAt
  simp only [↓reduceIte, activeParamsFlat_dh1 S b _ _ idx h]

theorem fgKeyInd1KeyGapDhActiveAdvAtFlat_dh3 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (idx : Nat)
    (h1 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on)
    (h2 : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeSpkCount S b.q_on) :
    let r := idx - activeIdCount S b.q_on * activeSpkCount S b.q_on
    fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A =
      fgKeyInd1KeyGapDhActiveAdvAt false
        (r / activeSpkCount S b.q_on) (r % activeSpkCount S b.q_on) S b A := by
  dsimp only
  unfold fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveRunAtFlat
    fgKeyInd1KeyGapDhActiveAdvAt
  simp only [Bool.false_eq_true, ↓reduceIte, activeParamsFlat_dh3 S b _ _ idx h1 h2]

theorem fgKeyInd1KeyGapDhActiveAdvAtFlat_dh2 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (idx : Nat)
    (h2 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeSpkCount S b.q_on)
    (h3 : idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeSpkCount S b.q_on +
                activeSendCount S b.q_on * activeIdCount S b.q_on) :
    let r := idx - (activeIdCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeSpkCount S b.q_on)
    fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A =
      fgKeyInd1KeyGapDhActiveAdvAtIk
        (r / activeIdCount S b.q_on) (r % activeIdCount S b.q_on) S b A := by
  dsimp only
  unfold fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveRunAtFlat
    fgKeyInd1KeyGapDhActiveAdvAtIk
  simp only [activeParamsFlat_dh2 S b _ _ idx h2 h3]

theorem fgKeyInd1KeyGapDhActiveAdvAtFlat_dh4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (idx : Nat)
    (h3 : ¬ idx < activeIdCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeSpkCount S b.q_on +
                  activeSendCount S b.q_on * activeIdCount S b.q_on)
    (h4 : idx < fgActiveTotalIndexCount S b.q_on) :
    let r := idx - (activeIdCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeSpkCount S b.q_on +
                    activeSendCount S b.q_on * activeIdCount S b.q_on)
    fgKeyInd1KeyGapDhActiveAdvAtFlat idx S b A =
      fgKeyInd1KeyGapDhActiveAdvAtOpk
        (r / activeOpkCount S b.q_on) (r % activeOpkCount S b.q_on) S b A := by
  dsimp only
  unfold fgKeyInd1KeyGapDhActiveAdvAtFlat fgKeyInd1KeyGapDhActiveRunAtFlat
    fgKeyInd1KeyGapDhActiveAdvAtOpk
  simp only [activeParamsFlat_dh4 S b _ _ idx h3 h4]

end

end Computational.Proofs.SignalPqxdh.Delta.KeyInd1KeyActiveShallow
