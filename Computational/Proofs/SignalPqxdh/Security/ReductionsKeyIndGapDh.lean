/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.ReductionsKeyIndSigKem

/-!
# Two-key `KeyInd` `GapDH` simulator

**Checked by Lean.** Shallow oracle-computation `GapDH` simulator (`fgKeyIndGapDhAdv4`) for the
`G3 → G3.5` hop of the two-key PQXDH `KeyInd` game, adapting Fiedler–Günther (ePrint 2024/702,
Fig. 11) with a DDH-consistency patch table across all four X25519 legs (`DH1`–`DH4`).
-/

@[expose] public section

set_option autoImplicit false

namespace SignalPqxdh.Security

open SignalPqxdh
open OracleSpec OracleComp

/-! ## DDH-consistency table and `DH1`/`DH3` simulator -/

namespace FgGapDh

abbrev GdhSimSpec : OracleSpec.{0, 0} ((ℕ ⊕ PrimQuery) ⊕ (Bytes × Bytes × Bytes)) :=
  PrimBaseSpec + gapDhOracleSpec

def embedUnif {α : Type} (mx : ProbComp α) : OracleComp PrimBaseSpec α :=
  liftComp mx PrimBaseSpec

def embedPrim {ι : Type} {spec : OracleSpec.{0, 0} ι} {α : Type}
    (mx : OracleComp PrimBaseSpec α) : OracleComp (PrimBaseSpec + spec) α :=
  OracleComp.construct
    (C := fun _ => OracleComp (PrimBaseSpec + spec) α)
    pure
    (fun q _ r => liftM (OracleSpec.query (spec := PrimBaseSpec + spec) (Sum.inl q)) >>= r)
    mx

def unifGdh {α : Type} (mx : ProbComp α) : OracleComp GdhSimSpec α :=
  embedPrim (spec := gapDhOracleSpec) (embedUnif mx)

def primGdhQ (op : PrimQuery) : OracleComp GdhSimSpec (primSpec.Range op) :=
  query (spec := GdhSimSpec) (Sum.inl (Sum.inr op))

def ddhGdhQ (X Y Z : Bytes) : OracleComp GdhSimSpec Bool :=
  query (spec := GdhSimSpec) (Sum.inr (X, Y, Z))

def findMGdh {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    List α → OracleComp GdhSimSpec (Option α)
  | [] => pure none
  | x :: xs => do
    if ← p x then return some x else findMGdh p xs

def anyMGdh {α : Type} (p : α → OracleComp GdhSimSpec Bool) :
    List α → OracleComp GdhSimSpec Bool
  | [] => pure false
  | x :: xs => do
    if ← p x then return true else anyMGdh p xs

def findMapMGdh {α : Type} (f : α → OracleComp GdhSimSpec Bytes) (U V : Bytes) :
    List α → OracleComp GdhSimSpec (Option Bytes)
  | [] => pure none
  | x :: xs => do
    let z ← f x
    if ← ddhGdhQ U V z then return some z else findMapMGdh f U V xs

def spkPowsGdh :
    List ((Nat × Nat) × SpkBundleEntry) → OracleComp GdhSimSpec (List (Bytes × Bytes))
  | [] => pure []
  | (_, b) :: xs => do
    let w ← primGdhQ (.pow8 b.spkPk)
    let rest ← spkPowsGdh xs
    return (b.spkSk, w) :: rest

inductive FgPoS where
  | secret (z : Bytes) (isCanon : Bool)
  | pair   (pk1 pk2 pow8Pk1 pow8Pk2 : Bytes)
  deriving DecidableEq, Repr

structure FgPatchEntry where
  pos1  : FgPoS
  pos2  : FgPoS
  pos3  : FgPoS
  pos4? : Option FgPoS
  ss    : Bytes
  dk    : DRKey
  deriving DecidableEq, Repr

def mkSecretPos (z : Bytes) : OracleComp GdhSimSpec FgPoS := do
  let c ← primGdhQ (.isCanonical z)
  return FgPoS.secret z c

def mkPairPos (pk1 pk2 : Bytes) : OracleComp GdhSimSpec FgPoS := do
  let w1 ← primGdhQ (.pow8 pk1)
  let w2 ← primGdhQ (.pow8 pk2)
  return FgPoS.pair pk1 pk2 w1 w2

def computeTwoSideOrPairPos (sk1 sk2 pk1 pk2 : Bytes) : OracleComp GdhSimSpec FgPoS :=
  if !sk1.isEmpty then do
    let z ← primGdhQ (.x25519 sk1 pk2)
    mkSecretPos z
  else if !sk2.isEmpty then do
    let z ← primGdhQ (.x25519 sk2 pk1)
    mkSecretPos z
  else
    mkPairPos pk1 pk2

def computeOptPos (sk1 : Bytes) (pk1 : Bytes) :
    Option (Bytes × Bytes) → OracleComp GdhSimSpec (Option FgPoS)
  | none => pure none
  | some (sk2, pk2) => some <$> computeTwoSideOrPairPos sk1 sk2 pk1 pk2

def ddhEqGdh : FgPoS → FgPoS → OracleComp GdhSimSpec Bool
  | .secret z1 _, .secret z2 _ =>
    pure (z1 == z2)
  | .pair _ _ w1 w2, .pair _ _ w3 w4 =>
    pure ((w1 == w3 && w2 == w4) || (w1 == w4 && w2 == w3))
  | .pair pk1 pk2 _ _, .secret z isCanon =>
    if isCanon then ddhGdhQ pk1 pk2 z else pure false
  | .secret z isCanon, .pair pk1 pk2 _ _ =>
    if isCanon then ddhGdhQ pk1 pk2 z else pure false

def ddhEqOptGdh : Option FgPoS → Option FgPoS → OracleComp GdhSimSpec Bool
  | none, none => pure true
  | some p1, some p2 => ddhEqGdh p1 p2
  | _, _ => pure false

def fgEntryMatches (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes)
    (e : FgPatchEntry) : OracleComp GdhSimSpec Bool := do
  if ss != e.ss then
    return false
  let b1 ← ddhEqGdh pos1 e.pos1
  let b2 ← ddhEqGdh pos2 e.pos2
  let b3 ← ddhEqGdh pos3 e.pos3
  let b4 ← ddhEqOptGdh pos4? e.pos4?
  return (b1 && b2 && b3 && b4)

def fgPatch (maxLen : ℕ) (pos1 pos2 pos3 : FgPoS) (pos4? : Option FgPoS) (ss : Bytes)
    (L : List FgPatchEntry) : OracleComp GdhSimSpec (DRKey × List FgPatchEntry) := do
  match ← findMGdh (fgEntryMatches pos1 pos2 pos3 pos4? ss) (L.take maxLen) with
  | some e => return (e.dk, L)
  | none =>
    let dk ← unifGdh sampleDRKey96
    let entry : FgPatchEntry := {
      pos1 := pos1, pos2 := pos2, pos3 := pos3, pos4? := pos4?, ss := ss, dk := dk
    }
    return (dk, entry :: L)

def primQ (q : PrimQuery) : OracleComp PrimBaseSpec (primSpec.Range q) :=
  query (spec := PrimBaseSpec) (Sum.inr q)

def findMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    List α → OracleComp PrimBaseSpec (Option α)
  | [] => pure none
  | x :: xs => do
    if ← p x then return some x else findMPrim p xs

def anyMPrim {α : Type} (p : α → OracleComp PrimBaseSpec Bool) :
    List α → OracleComp PrimBaseSpec Bool
  | [] => pure false
  | x :: xs => do
    if ← p x then return true else anyMPrim p xs

def findHonestPrincipalPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec (Option (Nat × PrincipalEntry)) :=
  findMPrim (fun (_, entry) => do
    let p1 ← primQ (.pow8 ikB)
    let p2 ← primQ (.pow8 entry.ikAPk)
    return (p1 == p2)) (principals.take S.N_dh)

def resolveSigPkPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec Bytes := do
  match ← findHonestPrincipalPrim S principals ikB with
  | some (_, entry) => return entry.ikSignPk
  | none            => return ikB

def isHonestUncorruptedPeerPrim (S : Setup) (principals : List (Nat × PrincipalEntry))
    (ikB : Bytes) : OracleComp PrimBaseSpec (Option Nat) := do
  match ← findHonestPrincipalPrim S principals ikB with
  | some (k, entry) => return (if !entry.corrupted then some k else none)
  | none            => return none

def checkBundleProvenancePrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec (Bool × Bool × Bool) := do
  match ← findHonestPrincipalPrim S principals bundle.ikB with
  | none => return (false, false, false)
  | some (k, _) =>
    let spkHon ← anyMPrim (fun ((u, _), b) => do
      let p1 ← primQ (.pow8 b.spkPk)
      let p2 ← primQ (.pow8 bundle.spkB)
      return (u == k && p1 == p2)) (spkBundles.take S.N_dh)
    let pqspkHon := spkBundles.any (fun ((u, _), b) =>
      u == k && b.pqspkPk == bundle.pqspkB)
    let opkHon ← match bundle.opkB? with
      | none => pure false
      | some (_, opkPk) =>
        anyMPrim (fun ((u, _, _), e) => do
          let p1 ← primQ (.pow8 e.opkPk)
          let p2 ← primQ (.pow8 opkPk)
          return (u == k && p1 == p2)) (opkEntries.take S.N_dh)
    return (spkHon, opkHon, pqspkHon)

def isAdvRegisteredPows (advKeyPows : List (Bytes × Bytes)) (wPk : Bytes) : Bool :=
  advKeyPows.any (fun (_, wPk') => wPk' == wPk)

def koskSenderOkPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (advKeyPows : List (Bytes × Bytes))
    (ikAPk : Bytes) : OracleComp PrimBaseSpec Bool := do
  let hp ← findHonestPrincipalPrim S principals ikAPk
  let wIk ← primQ (.pow8 ikAPk)
  return (hp.isSome || isAdvRegisteredPows advKeyPows wIk)

def isGameSpkPrim (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (spkPk : Bytes) : OracleComp PrimBaseSpec Bool :=
  anyMPrim (fun (_, b) => do
    let p1 ← primQ (.pow8 b.spkPk)
    let p2 ← primQ (.pow8 spkPk)
    return (p1 == p2)) (spkBundles.take S.N_dh)

def isGameOpkPrim (S : Setup)
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (opkPk : Bytes) : OracleComp PrimBaseSpec Bool :=
  anyMPrim (fun (_, e) => do
    let p1 ← primQ (.pow8 e.opkPk)
    let p2 ← primQ (.pow8 opkPk)
    return (p1 == p2)) (opkEntries.take S.N_dh)

def koskBundleOkPrim (S : Setup)
    (principals : List (Nat × PrincipalEntry))
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (opkEntries : List ((Nat × Nat × Nat) × OpkEntry))
    (advKeyPows : List (Bytes × Bytes))
    (bundle : PreKeyBundleInput) : OracleComp PrimBaseSpec Bool := do
  let hp ← findHonestPrincipalPrim S principals bundle.ikB
  let wIk ← primQ (.pow8 bundle.ikB)
  let ikOk := hp.isSome || isAdvRegisteredPows advKeyPows wIk
  let gSpk ← isGameSpkPrim S spkBundles bundle.spkB
  let wSpk ← primQ (.pow8 bundle.spkB)
  let spkOk := gSpk || isAdvRegisteredPows advKeyPows wSpk
  let opkOk ← match bundle.opkB? with
    | none => pure true
    | some (_, opkPk) => do
      let gOpk ← isGameOpkPrim S opkEntries opkPk
      let wOpk ← primQ (.pow8 opkPk)
      pure (gOpk || isAdvRegisteredPows advKeyPows wOpk)
  return (ikOk && spkOk && opkOk)

def lookupSpkSkPrim (S : Setup)
    (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (advKeyPows : List (Bytes × Bytes))
    (spkPk : Bytes) : OracleComp PrimBaseSpec Bytes := do
  let wSpk ← primQ (.pow8 spkPk)
  let foundSpk ← findMPrim (fun (_, b) => do
    let p1 ← primQ (.pow8 b.spkPk)
    return (p1 == wSpk)) (spkBundles.take S.N_dh)
  match foundSpk with
  | some (_, b) => return b.spkSk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => return sk
    | none => return []

def keyIndPartnerPrim {S : Setup} (s : KeyIndInitiatorEntry S) (r : KeyIndRespEntry S) :
    OracleComp PrimBaseSpec Bool := do
  let sIk ← primQ (.pow8 s.hdr.ikAPk)
  let rIk ← primQ (.pow8 r.hdr.ikAPk)
  let sPeer ← primQ (.pow8 s.peerIkPk)
  let rResp ← primQ (.pow8 r.respIkPk)
  let sSpk ← primQ (.pow8 s.peerSpkPk)
  let rSpk ← primQ (.pow8 r.spkPk)
  let sOpk ← primQ (.pow8 (s.peerOpkPk?.getD []))
  let rOpk ← primQ (.pow8 (r.opkPk?.getD []))
  return (sIk == rIk &&
          sPeer == rResp &&
          sSpk == rSpk &&
          s.peerOpkPk?.map (fun _ => sOpk) == r.opkPk?.map (fun _ => rOpk) &&
          s.hdr.ekAPk == r.hdr.ekAPk &&
          s.peerPqspkPk == r.pqspkPk &&
          s.hdr.kemCt == r.hdr.kemCt)

def choosePartnerDrKeyRandGdh {S : Setup} (sessions : List (KeyIndInitiatorEntry S))
    (r : KeyIndRespEntry S) : OracleComp GdhSimSpec DRKey := do
  let found ← embedPrim (spec := gapDhOracleSpec)
    (findMPrim (fun s => keyIndPartnerPrim s r) (sessions.take S.N_dh))
  match found with
  | some s => return s.drKeyRand
  | none   => unifGdh sampleDRKey96

def chooseInitPartnerDrKeyRandGdh {S : Setup} (respSessions : List (KeyIndRespEntry S))
    (s : KeyIndInitiatorEntry S) : OracleComp GdhSimSpec DRKey := do
  let found ← embedPrim (spec := gapDhOracleSpec)
    (findMPrim (fun r => keyIndPartnerPrim s r) (respSessions.take S.N_sess_tot))
  match found with
  | some r => return r.drKeyRand
  | none   => unifGdh sampleDRKey96

def sampleIndexRange2 (M N : ℕ) : ProbComp (ℕ × ℕ) := do
  let i ← sampleIndexRange M
  let j ← sampleIndexRange N
  return (i, j)

def spkBundleFlatIdx (S : Setup) (u : Fin S.N_id) (j : Fin S.N_recv) : Nat :=
  u.val * S.N_recv + j.val

def initSessionSlotIdx {S : Setup} : SessionId S → Nat
  | .sendOPK u i     => u.val * S.N_send_opk + i.val
  | .sendNoOPK u i   => S.N_send_opk_tot + (u.val * S.N_send_no_opk + i.val)
  | .recvOPK _ _ _   => S.N_send_tot
  | .recvNoOPK _ _ _ => S.N_send_tot

def respBundleKey {S : Setup} : SessionId S → Nat × Nat
  | .recvOPK k j _   => (k.val, j.val)
  | .recvNoOPK k j _ => (k.val, j.val)
  | .sendOPK u _     => (u.val, 0)
  | .sendNoOPK u _   => (u.val, 0)

def extractDh1 (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 32 bs)

def extractDh2 (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 64 bs)

def extractDh3 (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 96 bs)

def extractDh4 (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 128 bs)

def extractKemSsNoOPK (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 128 bs)

def extractKemSsOPK (bs : Bytes) : Bytes :=
  List.take 32 (List.drop 160 bs)

/-- Parse a `buildSecrets` byte string into `(dh1, dh2, dh3, dh4?, ss)`. -/
def parseRoSecrets (bs : Bytes) : Option (Bytes × Bytes × Bytes × Option Bytes × Bytes) :=
  if bs.take 32 != F_X25519 then
    none
  else if bs.length == 160 then
    some (extractDh1 bs, extractDh2 bs, extractDh3 bs, none, extractKemSsNoOPK bs)
  else if bs.length == 192 then
    some (extractDh1 bs, extractDh2 bs, extractDh3 bs, some (extractDh4 bs), extractKemSsOPK bs)
  else
    none

structure FgKeyIndSimState (S : Setup) where
  base       : KeyIndState S
  fgL        : List FgPatchEntry := []
  rawRoCache : List (Bytes × DRKey) := []
  advRoLog   : List Bytes := []
  advKeyPows : List (Bytes × Bytes) := []

def FgKeyIndSimState.empty (S : Setup) (secb : Bool) : FgKeyIndSimState S :=
  { base := KeyIndState.empty S secb }

def fgRoQueryGdh {S : Setup} (maxLen : ℕ) (secrets : Bytes)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  let advRoLog' := secrets :: st.advRoLog
  match parseRoSecrets secrets with
  | some (dh1, dh2, dh3, dh4?, ss) =>
    let pos1 ← mkSecretPos dh1
    let pos2 ← mkSecretPos dh2
    let pos3 ← mkSecretPos dh3
    let pos4? ← match dh4? with
      | none => pure none
      | some dh4 => some <$> mkSecretPos dh4
    let (dk, fgL') ← fgPatch maxLen pos1 pos2 pos3 pos4? ss st.fgL
    return (.drKeyResp dk, { st with fgL := fgL', advRoLog := advRoLog' })
  | none =>
    match st.rawRoCache.find? (fun (s, _) => s == secrets) with
    | some (_, dk) =>
      return (.drKeyResp dk, { st with advRoLog := advRoLog' })
    | none =>
      let dk ← unifGdh sampleDRKey96
      return (.drKeyResp dk,
        { st with rawRoCache := (secrets, dk) :: st.rawRoCache, advRoLog := advRoLog' })

def fgRunInitiateGdh (useDh1 : Bool) (targetIdx : ℕ) (S : Setup) (maxLen : ℕ) (U : Bytes)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.sessions.any (fun e => e.sid == sid) then
    return (.noneResp, st)
  let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
    | return (.noneResp, st)
  let bundleOk ← embedPrim (spec := gapDhOracleSpec)
    (koskBundleOkPrim S st.base.principals st.base.spkBundles
      st.base.opkEntries st.advKeyPows bundle)
  if !bundleOk then
    return (.noneResp, st)
  let isTargetEph : Bool := !useDh1 && (initSessionSlotIdx sid == targetIdx)
  let ekASkRaw ← unifGdh sampleScalar32
  let kemCoins ← unifGdh sampleCoins32
  let sigPkB ← embedPrim (spec := gapDhOracleSpec)
    (resolveSigPkPrim S st.base.principals bundle.ikB)
  let v1 ← primGdhQ (.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig)
  let v2 ← primGdhQ (.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig)
  if !(v1 && v2) then
    return (.noneResp, st)
  let some (ss, kemCt) ← primGdhQ (.kemEncaps bundle.pqspkB kemCoins)
    | return (.noneResp, st)
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
  match ← embedPrim (spec := gapDhOracleSpec)
      (findHonestPrincipalPrim S st.base.principals bundle.ikB) with
  | some _ => return (.hdrResp hdr, st')
  | none   => return (.initUnfreshResp drKeyReal hdr, st')

/-- Fiedler–Günther Fig. 11 lines 19–35 `acceptOPK` handler in `GdhSimSpec`. -/
def fgRunAcceptOPKGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then
    return (.noneResp, st)
  let senderOk ← embedPrim (spec := gapDhOracleSpec)
    (koskSenderOkPrim S st.base.principals st.advKeyPows hdr.ikAPk)
  if !senderOk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then
    return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon ← primGdhQ (.isCanonical hdr.ekAPk)
  let dh1Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ikAPk)
  let dh2Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ekAPk)
  let dh4Check ← primGdhQ (.x25519 oEntry.opkSk hdr.ekAPk)
  let ss? ← primGdhQ (.kemDecaps bEntry.pqspkSk hdr.kemCt)
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0 &&
       dh4Check != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 ← computeTwoSideOrPairPos [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let pos4 ← mkSecretPos dh4Check
  let (drKey, fgL') ← fgPatch maxLen pos1 pos2 pos3 (some pos4) ss st.fgL
  let opkEntries' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonestOpt ← embedPrim (spec := gapDhOracleSpec)
    (findHonestPrincipalPrim S st.base.principals hdr.ikAPk)
  let rInit : KeyIndRespEntry S := {
    sid          := .recvOPK k j o
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := some oEntry.opkPk
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandGdh st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    opkEntries       := opkEntries'
    usedRecvOPK      := (k.val, j.val, o.val) :: st.base.usedRecvOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

/-- Fiedler–Günther Fig. 11 lines 19–35 `acceptNoOPK` handler in `GdhSimSpec`. -/
def fgRunAcceptNoOPKGdh (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (l : Fin S.N_no_opk) (hdr : HandshakeHdr)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == none &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvNoOPK.contains (k.val, j.val, l.val) then
    return (.noneResp, st)
  let senderOk ← embedPrim (spec := gapDhOracleSpec)
    (koskSenderOkPrim S st.base.principals st.advKeyPows hdr.ikAPk)
  if !senderOk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon ← primGdhQ (.isCanonical hdr.ekAPk)
  let dh1Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ikAPk)
  let dh2Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ekAPk)
  let ss? ← primGdhQ (.kemDecaps bEntry.pqspkSk hdr.kemCt)
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 ← computeTwoSideOrPairPos [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let (drKey, fgL') ← fgPatch maxLen pos1 pos2 pos3 none ss st.fgL
  let senderHonestOpt ← embedPrim (spec := gapDhOracleSpec)
    (findHonestPrincipalPrim S st.base.principals hdr.ikAPk)
  let rInit : KeyIndRespEntry S := {
    sid          := .recvNoOPK k j l
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := none
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandGdh st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    usedRecvNoOPK    := (k.val, j.val, l.val) :: st.base.usedRecvNoOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

def fgKeyIndStep (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  match q with
  | .initPrin u =>
    if st.base.principals.any (fun (idx, _) => idx == u.val) then
      return (.noneResp, st)
    let isTargetPrin : Bool := useDh1 && (u.val == targetIdx)
    let secIKA0Raw ← unifGdh sampleScalar32
    let ikAPkRaw ← primGdhQ (.x25519Base secIKA0Raw)
    let secIKAsign ← unifGdh sampleScalar32
    let ikSignPk ← primGdhQ (.sigPkGen secIKAsign)
    let entry : PrincipalEntry := {
      secIKA0    := if isTargetPrin then [] else secIKA0Raw
      ikAPk      := if isTargetPrin then U else ikAPkRaw
      secIKAsign := secIKAsign
      ikSignPk   := ikSignPk
      corrupted  := false
    }
    let base' := { st.base with principals := (u.val, entry) :: st.base.principals }
    return (.initPrinResp entry.ikAPk entry.ikSignPk, { st with base := base' })
  | .corruptIK u =>
    match st.base.principals.find? (fun (idx, _) => idx == u.val) with
    | none => return (.noneResp, st)
    | some (_, entry) =>
      let principals' := st.base.principals.map (fun (idx, e) =>
        if idx == u.val then (idx, { e with corrupted := true }) else (idx, e))
      let base' := { st.base with principals := principals' }
      return (.corrResp entry.secIKA0 entry.secIKAsign, { st with base := base' })
  | .genSPK u j =>
    if st.base.spkBundles.any (fun (k, _) => k == (u.val, j.val)) then
      return (.noneResp, st)
    let some (_, uEntry) := st.base.principals.find? (fun (idx, _) => idx == u.val)
      | return (.noneResp, st)
    let isTargetSpk : Bool := spkBundleFlatIdx S u j == targetSpkIdx
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
  | .genOPK u j o =>
    if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
      return (.noneResp, st)
    let opkSk ← unifGdh sampleScalar32
    let opkPk ← primGdhQ (.x25519Base opkSk)
    let oEntry : OpkEntry := { opkSk := opkSk, opkPk := opkPk, consumed := false }
    let opks' := ((u.val, j.val, o.val), oEntry) :: st.base.opkEntries
    let base' := { st.base with opkEntries := opks' }
    return (.pkResp opkPk, { st with base := base' })
  | .initiateOPK u i bundle =>
    if bundle.opkB?.isNone then
      return (.noneResp, st)
    fgRunInitiateGdh useDh1 targetIdx S maxLen U (.sendOPK u i) u bundle st
  | .initiateNoOPK u i bundle =>
    if bundle.opkB?.isSome then
      return (.noneResp, st)
    fgRunInitiateGdh useDh1 targetIdx S maxLen U (.sendNoOPK u i) u bundle st
  | .acceptOPK k j o hdr =>
    fgRunAcceptOPKGdh S maxLen k j o hdr st
  | .acceptNoOPK k j l hdr =>
    fgRunAcceptNoOPKGdh S maxLen k j l hdr st
  | .testSession sid =>
    if !isKeyIndSessionTestable st.base sid then
      return (.noneResp, st)
    match st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      let sessions' := st.base.sessions.map (fun s =>
        if s.sid == sid then { s with tested := true } else s)
      let base' := { st.base with sessions := sessions' }
      let resp := .drKeyResp (if st.base.secb then e.drKeyReal else e.drKeyRand)
      return (resp, { st with base := base' })
    | none =>
      match st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => return (.noneResp, st)
      | some r =>
        let resp' := st.base.respSessions.map (fun x =>
          if x.sid == sid then { x with tested := true } else x)
        let base' := { st.base with respSessions := resp' }
        let resp := .drKeyResp (if st.base.secb then r.drKeyReal else r.drKeyRand)
        return (resp, { st with base := base' })
  | .revealSessionKey sid =>
    match st.base.sessions.find? (fun e => e.sid == sid) with
    | some e =>
      if e.tested then return (.noneResp, st)
      let sessions' := st.base.sessions.map (fun s =>
        if s.sid == sid then { s with revealed := true } else s)
      let base' := { st.base with sessions := sessions' }
      return (.drKeyResp e.drKeyReal, { st with base := base' })
    | none =>
      match st.base.respSessions.find? (fun r => r.sid == sid) with
      | none => return (.noneResp, st)
      | some r =>
        if r.tested then return (.noneResp, st)
        let resp' := st.base.respSessions.map (fun x =>
          if x.sid == sid then { x with revealed := true } else x)
        let base' := { st.base with respSessions := resp' }
        return (.drKeyResp r.drKeyReal, { st with base := base' })
  | .roQuery secrets =>
    fgRoQueryGdh maxLen secrets st
  | .revealDhSecrets =>
    return (.noneResp, st)
  | .revealSpkSk u j =>
    match st.base.spkBundles.find? (fun (idx, _) => idx == (u.val, j.val)) with
    | none => return (.noneResp, st)
    | some (_, bEntry) =>
      let spkBundles' := st.base.spkBundles.map (fun (idx, b) =>
        if idx == (u.val, j.val) then (idx, { b with revealed := true }) else (idx, b))
      let base' := { st.base with spkBundles := spkBundles' }
      return (.spkSkResp bEntry.spkSk, { st with base := base' })
  | .registerKey sk =>
    if sk.length != 32 then
      return (.noneResp, st)
    let pk ← primGdhQ (.x25519Base sk)
    let wPk ← primGdhQ (.pow8 pk)
    let base' := { st.base with advKeys := (sk, pk) :: st.base.advKeys }
    return (.pkResp pk, { st with base := base', advKeyPows := (sk, wPk) :: st.advKeyPows })

def runWithGdhStep {ιI : Type}
    {GSpec : OracleSpec.{0, 0} ιI} {St α : Type}
    (step : (q : ιI) → St → OracleComp GdhSimSpec (GSpec.Range q × St))
    (mx : OracleComp (unifSpec + GSpec) α) (st : St) :
    OracleComp GdhSimSpec (α × St) :=
  OracleComp.construct
    (C := fun _ => St → OracleComp GdhSimSpec (α × St))
    (fun x st => pure (x, st))
    (fun q _ r st =>
      match q with
      | Sum.inl n => do
        let u ← liftM (OracleSpec.query (spec := GdhSimSpec) (Sum.inl (Sum.inl n)))
        r u st
      | Sum.inr gq => do
        let p ← step gq st
        r p.1 p.2)
    mx st


def extractCdhFromAdvRoLog (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes)
    (advRoLog : List Bytes) : OracleComp GdhSimSpec Bytes := do
  let cands := (advRoLog.take maxLen).map
    (fun sec => if useDh1 then extractDh1 sec else extractDh3 sec)
  match ← findMGdh (fun z => ddhGdhQ U V z) cands with
  | some z => return z
  | none   => return List.replicate 32 0

def lookupSpkSkFromPows (spkPows advKeyPows : List (Bytes × Bytes)) (wSpk : Bytes) : Bytes :=
  match spkPows.find? (fun (_, wB) => wB == wSpk) with
  | some (sk, _) => sk
  | none =>
    match advKeyPows.find? (fun (_, wPk) => wPk == wSpk) with
    | some (sk, _) => sk
    | none => []

def initDh1CandWithPowsGdh {S : Setup} (spkPows advKeyPows : List (Bytes × Bytes))
    (s : KeyIndInitiatorEntry S) : OracleComp GdhSimSpec Bytes := do
  let wSpk ← primGdhQ (.pow8 s.peerSpkPk)
  let spkSk := lookupSpkSkFromPows spkPows advKeyPows wSpk
  primGdhQ (.x25519 spkSk s.hdr.ikAPk)

def respDh1CandGdh (S : Setup) (spkBundles : List ((Nat × Nat) × SpkBundleEntry))
    (r : KeyIndRespEntry S) : OracleComp GdhSimSpec Bytes :=
  let key := respBundleKey r.sid
  let spkSk := match (spkBundles.take S.N_dh).find? (fun (idx, _) => idx == key) with
    | some (_, b) => b.spkSk
    | none => []
  primGdhQ (.x25519 spkSk r.hdr.ikAPk)

def extractCdhFromSimState (S : Setup) (useDh1 : Bool) (maxLen : ℕ) (U V : Bytes)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec Bytes :=
  if useDh1 then do
    match ← findMGdh (fun z => ddhGdhQ U V z) ((st.advRoLog.take maxLen).map extractDh1) with
    | some z => return z
    | none =>
      let spkPows ← spkPowsGdh (st.base.spkBundles.take S.N_dh)
      match ← findMapMGdh (initDh1CandWithPowsGdh spkPows st.advKeyPows) U V
          (st.base.sessions.take S.N_dh) with
      | some z => return z
      | none =>
        match ← findMapMGdh (respDh1CandGdh S st.base.spkBundles) U V
            (st.base.respSessions.take S.N_sess_tot) with
        | some z => return z
        | none   => return List.replicate 32 0
  else
    extractCdhFromAdvRoLog false maxLen U V st.advRoLog

def fgKeyIndGapDhRunAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSimSpec Bytes := do
  let secb ← unifGdh ($ᵗ Bool)
  let initSt := FgKeyIndSimState.empty S secb
  let (_, finalSt) ← runWithGdhStep
    (fgKeyIndStep useDh1 targetIdx targetSpkIdx S b.q_total U V) A.1.run initSt
  extractCdhFromSimState S useDh1 b.q_total U V finalSt

/-- Two-leg (`DH1`/`DH3`) Fiedler–Günther `GapDH` simulator for `KeyInd`. -/
def fgKeyIndGapDhAdv (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := do
    let (flatIdx, bIdx) ← unifGdh (sampleIndexRange2 (S.N_id + S.N_send_tot) S.N_spk_tot)
    if flatIdx < S.N_id then
      fgKeyIndGapDhRunAt true flatIdx bIdx S b A U V
    else
      fgKeyIndGapDhRunAt false (flatIdx - S.N_id) bIdx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

def fgKeyIndGapDhAdvAt (useDh1 : Bool) (targetIdx targetSpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := fgKeyIndGapDhRunAt useDh1 targetIdx targetSpkIdx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

end FgGapDh

export FgGapDh (
  GdhSimSpec
  unifGdh
  primGdhQ
  ddhGdhQ
  findMGdh
  anyMGdh
  findMapMGdh
  spkPowsGdh
  FgPoS
  FgPatchEntry
  mkSecretPos
  mkPairPos
  computeTwoSideOrPairPos
  computeOptPos
  ddhEqGdh
  ddhEqOptGdh
  fgEntryMatches
  fgPatch
  choosePartnerDrKeyRandGdh
  chooseInitPartnerDrKeyRandGdh
  sampleIndexRange2
  spkBundleFlatIdx
  initSessionSlotIdx
  respBundleKey
  extractDh1
  extractDh2
  extractDh3
  extractDh4
  extractKemSsNoOPK
  extractKemSsOPK
  parseRoSecrets
  FgKeyIndSimState
  FgKeyIndSimState
  fgRoQueryGdh
  fgRunInitiateGdh
  fgRunAcceptOPKGdh
  fgRunAcceptNoOPKGdh
  fgKeyIndStep
  runWithGdhStep
  extractCdhFromAdvRoLog
  lookupSpkSkFromPows
  initDh1CandWithPowsGdh
  respDh1CandGdh
  extractCdhFromSimState
  fgKeyIndGapDhRunAt
  fgKeyIndGapDhAdv
  fgKeyIndGapDhAdvAt
)

/-! ## Responder-identity `DH2` simulator -/

namespace FgGapDh.Ik

open FgGapDh

def noSpkIdx (S : Setup) : ℕ := S.N_spk_tot

def fgKeyIndStepIk (targetIdx targetPrinIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) :=
  match q with
  | .initPrin u => fgKeyIndStep true targetPrinIdx (noSpkIdx S) S maxLen V V (.initPrin u) st
  | q => fgKeyIndStep false targetIdx (noSpkIdx S) S maxLen U V q st

def extractCdh2FromAdvRoLog (maxLen : ℕ) (U V : Bytes)
    (advRoLog : List Bytes) : OracleComp GdhSimSpec Bytes := do
  let cands := (advRoLog.take maxLen).map extractDh2
  match ← findMGdh (fun z => ddhGdhQ U V z) cands with
  | some z => return z
  | none   => return List.replicate 32 0

def fgKeyIndGapDhRunAtIk (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSimSpec Bytes := do
  let secb ← unifGdh ($ᵗ Bool)
  let initSt := FgKeyIndSimState.empty S secb
  let (_, finalSt) ← runWithGdhStep
    (fgKeyIndStepIk targetIdx targetPrinIdx S b.q_total U V) A.1.run initSt
  extractCdh2FromAdvRoLog b.q_total U V finalSt.advRoLog

def fgKeyIndGapDhAdvAtIk (targetIdx targetPrinIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := fgKeyIndGapDhRunAtIk targetIdx targetPrinIdx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18)

end FgGapDh.Ik

export FgGapDh.Ik (
  fgKeyIndStepIk
  extractCdh2FromAdvRoLog
  fgKeyIndGapDhRunAtIk
  fgKeyIndGapDhAdvAtIk
)

/-! ## One-time prekey `DH4` simulator -/

namespace FgGapDh.Opk

open FgGapDh

def opkFlatIdx (S : Setup) (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) : ℕ :=
  opkSlotFlatIdx S (k.val, j.val, o.val)

def noSpkIdx (S : Setup) : ℕ := S.N_spk_tot

def fgGenOPKGdhOpk (targetOpkIdx : ℕ) (S : Setup) (V : Bytes)
    (u : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if st.base.opkEntries.any (fun (k, _) => k == (u.val, j.val, o.val)) then
    return (.noneResp, st)
  let isTargetOpk : Bool := opkFlatIdx S u j o == targetOpkIdx
  let opkSkRaw ← unifGdh sampleScalar32
  let opkPkRaw ← primGdhQ (.x25519Base opkSkRaw)
  let oEntry : OpkEntry := {
    opkSk    := if isTargetOpk then [] else opkSkRaw
    opkPk    := if isTargetOpk then V else opkPkRaw
    consumed := false }
  let base' := { st.base with opkEntries := ((u.val, j.val, o.val), oEntry) :: st.base.opkEntries }
  return (.pkResp oEntry.opkPk, { st with base := base' })

def fgRunAcceptOPKGdhOpk (S : Setup) (maxLen : ℕ)
    (k : Fin S.N_id) (j : Fin S.N_recv) (o : Fin S.N_opk) (hdr : HandshakeHdr)
    (st : FgKeyIndSimState S) : OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) := do
  if !(hdr.spkId == UInt32.ofNat j.val &&
       hdr.pqspkId == UInt32.ofNat j.val &&
       hdr.opkId? == some (UInt32.ofNat o.val) &&
       hdr.ikAPk.length == 32 &&
       hdr.ekAPk.length == 32) then
    return (.noneResp, st)
  if st.base.usedRecvOPK.contains (k.val, j.val, o.val) then
    return (.noneResp, st)
  let senderOk ← embedPrim (spec := gapDhOracleSpec)
    (koskSenderOkPrim S st.base.principals st.advKeyPows hdr.ikAPk)
  if !senderOk then
    return (.noneResp, st)
  let some (_, kEntry) := st.base.principals.find? (fun (idx, _) => idx == k.val)
    | return (.noneResp, st)
  let some (_, bEntry) := st.base.spkBundles.find? (fun (idx, _) => idx == (k.val, j.val))
    | return (.noneResp, st)
  let some (_, oEntry) := st.base.opkEntries.find? (fun (idx, _) => idx == (k.val, j.val, o.val))
    | return (.noneResp, st)
  if oEntry.consumed then
    return (.noneResp, st)
  let (replayOk, usedTriples') :=
    checkAndMarkKyberBaseKeySeen st.base.seenKyberBaseKeys k.val hdr.pqspkId hdr.spkId hdr.ekAPk
  let canon ← primGdhQ (.isCanonical hdr.ekAPk)
  let dh1Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ikAPk)
  let dh2Zero ← primGdhQ (.x25519 (List.replicate 32 0) hdr.ekAPk)
  let ss? ← primGdhQ (.kemDecaps bEntry.pqspkSk hdr.kemCt)
  if !(replayOk && canon &&
       dh1Zero != List.replicate 32 0 &&
       dh2Zero != List.replicate 32 0) then
    return (.noneResp, st)
  let some ss := ss?
    | return (.noneResp, st)
  let pos1 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ikAPk bEntry.spkPk
  let pos2 ← computeTwoSideOrPairPos [] kEntry.secIKA0 hdr.ekAPk kEntry.ikAPk
  let pos3 ← computeTwoSideOrPairPos [] bEntry.spkSk hdr.ekAPk bEntry.spkPk
  let pos4 ← computeTwoSideOrPairPos [] oEntry.opkSk hdr.ekAPk oEntry.opkPk
  let (drKey, fgL') ← fgPatch maxLen pos1 pos2 pos3 (some pos4) ss st.fgL
  let opkEntries' := st.base.opkEntries.map (fun (idx, e) =>
    if idx == (k.val, j.val, o.val) then (idx, { e with consumed := true }) else (idx, e))
  let senderHonestOpt ← embedPrim (spec := gapDhOracleSpec)
    (findHonestPrincipalPrim S st.base.principals hdr.ikAPk)
  let rInit : KeyIndRespEntry S := {
    sid          := .recvOPK k j o
    respIkPk     := kEntry.ikAPk
    spkPk        := bEntry.spkPk
    opkPk?       := some oEntry.opkPk
    pqspkPk      := bEntry.pqspkPk
    hdr          := hdr
    senderHonest := senderHonestOpt.isSome
    drKeyReal    := drKey
    drKeyRand    := drKey
  }
  let drKeyRand ← choosePartnerDrKeyRandGdh st.base.sessions rInit
  let base' : KeyIndState S := { st.base with
    opkEntries       := opkEntries'
    usedRecvOPK      := (k.val, j.val, o.val) :: st.base.usedRecvOPK
    seenKyberBaseKeys := usedTriples'
    respSessions     := { rInit with drKeyRand := drKeyRand } :: st.base.respSessions
  }
  let st' : FgKeyIndSimState S := { st with base := base', fgL := fgL' }
  match senderHonestOpt with
  | some _ => return (.acceptFreshResp, st')
  | none   => return (.drKeyResp drKey, st')

def fgKeyIndStepOpk (targetIdx targetOpkIdx : ℕ) (S : Setup) (maxLen : ℕ)
    (U V : Bytes) (q : KeyIndQuery S) (st : FgKeyIndSimState S) :
    OracleComp GdhSimSpec (KeyIndResponse × FgKeyIndSimState S) :=
  match q with
  | .genOPK u j o => fgGenOPKGdhOpk targetOpkIdx S V u j o st
  | .acceptOPK k j o hdr => fgRunAcceptOPKGdhOpk S maxLen k j o hdr st
  | q => fgKeyIndStep false targetIdx (noSpkIdx S) S maxLen U V q st

def extractCdh4FromAdvRoLog (maxLen : ℕ) (U V : Bytes)
    (advRoLog : List Bytes) : OracleComp GdhSimSpec Bytes := do
  let cands := (advRoLog.take maxLen).map extractDh4
  match ← findMGdh (fun z => ddhGdhQ U V z) cands with
  | some z => return z
  | none   => return List.replicate 32 0

def fgKeyIndGapDhRunAtOpk (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b)
    (U V : Bytes) : OracleComp GdhSimSpec Bytes := do
  let secb ← unifGdh ($ᵗ Bool)
  let initSt := FgKeyIndSimState.empty S secb
  let (_, finalSt) ← runWithGdhStep
    (fgKeyIndStepOpk targetIdx targetOpkIdx S b.q_total U V) A.1.run initSt
  extractCdh4FromAdvRoLog b.q_total U V finalSt.advRoLog

def fgKeyIndGapDhAdvAtOpk (targetIdx targetOpkIdx : ℕ)
    (S : Setup) (b : QueryBudget) (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := fgKeyIndGapDhRunAtOpk targetIdx targetOpkIdx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18)

end FgGapDh.Opk

export FgGapDh.Opk (
  opkFlatIdx
  fgGenOPKGdhOpk
  fgRunAcceptOPKGdhOpk
  fgKeyIndStepOpk
  extractCdh4FromAdvRoLog
  fgKeyIndGapDhRunAtOpk
  fgKeyIndGapDhAdvAtOpk
)

/-! ## Unified four-leg `GapDH` simulator -/

open FgGapDh

def fgTotalIndexCount (S : Setup) : ℕ :=
  S.N_id * S.N_spk_tot + S.N_send_tot * S.N_spk_tot +
  S.N_send_tot * S.N_id + S.N_send_opk_tot * S.N_opk_tot

def fgKeyIndGapDhRunAtFlat (idx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) (U V : Bytes) : OracleComp GdhSimSpec Bytes :=
  let nA := S.N_id * S.N_spk_tot
  let nC := S.N_send_tot * S.N_spk_tot
  let nB := S.N_send_tot * S.N_id
  if idx < nA then
    fgKeyIndGapDhRunAt true (idx / S.N_spk_tot) (idx % S.N_spk_tot) S b A U V
  else if idx < nA + nC then
    let r := idx - nA
    fgKeyIndGapDhRunAt false (r / S.N_spk_tot) (r % S.N_spk_tot) S b A U V
  else if idx < nA + nC + nB then
    let r := idx - (nA + nC)
    fgKeyIndGapDhRunAtIk (r / S.N_id) (r % S.N_id) S b A U V
  else
    let r := idx - (nA + nC + nB)
    fgKeyIndGapDhRunAtOpk (r / S.N_opk_tot) (r % S.N_opk_tot) S b A U V

def fgKeyIndGapDhAdvAtFlat (idx : ℕ) (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := fgKeyIndGapDhRunAtFlat idx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)

def fgKeyIndGapDhAdv4 (S : Setup) (b : QueryBudget)
    (A : BoundedAdv (KeyIndAdversary S) b) : GapDhAdv where
  run U V := do
    let idx ← unifGdh (FgGapDh.sampleIndexRange (fgTotalIndexCount S))
    fgKeyIndGapDhRunAtFlat idx S b A U V
  q_ddh := 4 * b.q_total ^ 2 + b.q_total + S.N_dh + S.N_sess_tot

  q_prim := b.q_total * (S.N_dh * 20 + S.N_sess_tot * 8 + 18) + (S.N_dh * 3 + S.N_sess_tot)


end SignalPqxdh.Security
