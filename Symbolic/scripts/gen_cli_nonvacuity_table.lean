/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

import Std.Data.HashMap
import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
import Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
import Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
import Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval

/-!
# Certified `DY.Bytes` Lookup Table Generator

Code generator for `Symbolic/Proofs/Tests/CliNonvacuity/Table/` (`call6` and `full` modes).
Evaluates distinct symbolic `DY.Bytes` subterms across the CLI non-vacuity suite into ID-indexed
`CertTable` (`BinTree CertNode` and `Trie Nat`) modules, certifying DAG wiring by `rfl` and
per-node byte evaluation via `checkSubBytes` (`decide +kernel`). Validates `checkSubBytes`,
`evalGammaFast` agreement, and root coverage in memory before writing the sharded Lean files.
-/

set_option autoImplicit false

namespace GenCliTable

def licenseHeader : String :=
  "/-\nCopyright 2026 Google LLC\n\nAll code is licensed under the Apache License, Version 2.0 (the \"Apache 2.0\"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0\n\nUnless required by applicable law or agreed to in writing, software distributed under the License is distributed on an \"AS IS\" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and\nlimitations under the License.\n-/\n"

def writeLeanFile (path body : String) : IO Unit :=
  IO.FS.writeFile path (licenseHeader ++ "\n" ++ body)

open scoped DY.Libsignal.Composed
open CryptoProofLib.Refinement (ExternInterpretation)
open DY (ExecTrace)
open DY.Libsignal (HwBytes)
open DY.Libsignal.PQXDH.Refinement (wirePrekeyTag)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg messageVersion findRecvChain recvHalfStep consumeMessageKey skippedSeeds)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry TrialCtx
   ofByteArray parsePreKeyWire storedStates availableStates ownKeys storedRatchetKeys
   bobTrials trialTerms)
open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers
  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)
open Symbolic.Proofs.Tests.Shared.Composed.HonestSession
  (opkB
   stA0 stA1 coins0 key0 m0 m1 m2 m3 o1 t6
   stA0Opk stA1Opk coins0Opk key0Opk m0Opk oOpk t6Opk)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (encSig encMsg)
open Symbolic.Proofs.Tests.CliNonvacuity.Witness
  (myInterp mkRecords myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (Trie emptyTrie trieInsert hashTermNat beqBareOptFast evalGammaFast)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (stateAnchorPair trStateProxyRoots macTerms S0Comp)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs (r0 myGhost)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCliModel04 (pkMsg0 pkMsg1)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionStepsAux (trAt visAt saltsAt)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionSteps
  (ekTerm ctTerm msg0Term msg1Term msgReply0Term msg2Term
   x3Rep x4Rep msg0Sig msg1Sig msgReply0Sig msg2Sig)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionCollisionsAux
  (pqSecretsList storedRatchetKeysNoSkipped)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps
  (mySemComp ghostOf visOfComp)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval
  (p0Fields honestPreKeyRep)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
  (BinTree btGet NodeSkel skelEval CertNode checkSubBytes CertTable tableLookup)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)

private def pad2 (n : Nat) : String :=
  if n < 10 then s!"0{n}" else s!"{n}"

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('a'.toNat + (n - 10))

private def fmtByte (b : BitVec 8) : String :=
  let v := b.toNat
  String.ofList ['0', 'x', hexDigit (v / 16), hexDigit (v % 16), '#', '8']

private def fnvBytes (bs : HwBytes) : UInt64 :=
  bs.foldl (fun (h : UInt64) b => (h ^^^ b.toNat.toUInt64) * 1099511628211) 14695981039346656037

private def knownSlices : List (HwBytes × String) :=
  ([(myKyberSecField, "myKyberSecField"),
    (nvVec3168.toList, "nvVec3168.toList"),
    (nvDk2400, "nvDk2400"),
    (myKyberPubBytes, "myKyberPubBytes"),
    (nvVec1568.toList, "nvVec1568.toList"),
    (nvEk1152, "nvEk1152"),
    (sendAddrABytes, "sendAddrABytes"),
    (pt0, "pt0"),
    (pt1, "pt1"),
    (ptReply0, "ptReply0"),
    (pt2, "pt2")] : List (HwBytes × String)).filter (fun p => p.1.length ≥ 4)

private def dropPrefix? : HwBytes → HwBytes → Option HwBytes
  | [], xs => some xs
  | _ :: _, [] => none
  | p :: ps, x :: xs => if p == x then dropPrefix? ps xs else none

private def matchKnownPrefix (xs : HwBytes) : Option (String × HwBytes) :=
  knownSlices.findSome? fun (pat, nm) =>
    match dropPrefix? pat xs with
    | some rest => some (nm, rest)
    | none => none

private def countLeadingEq (b : BitVec 8) : HwBytes → Nat × HwBytes
  | [] => (0, [])
  | x :: xs =>
    if x == b then
      let (n, rest) := countLeadingEq b xs
      (n + 1, rest)
    else
      (0, x :: xs)

private partial def chunkList {α : Type} (sz : Nat) : List α → List (List α)
  | [] => []
  | xs =>
    let hd := xs.take sz
    let tl := xs.drop sz
    if hd.isEmpty then [] else hd :: chunkList sz tl

private def fmtRawSeg (bs : HwBytes) : List String :=
  let subSegs := chunkList 128 bs
  subSegs.map fun seg =>
    let rows := (chunkList 12 seg).map fun row =>
      String.intercalate ", " (row.map fmtByte)
    match rows with
    | [] => "([] : HwBytes)"
    | [r] => s!"[{r}]"
    | r :: rs =>
      "[" ++ r ++ ",\n    " ++ String.intercalate ",\n    " rs ++ "]"

private partial def compressBytesAux (xs : HwBytes) (rawRev : HwBytes)
    (acc : List String) : List String :=
  let flushRaw (acc : List String) : List String :=
    if rawRev.isEmpty then acc else acc ++ fmtRawSeg rawRev.reverse
  match xs with
  | [] => flushRaw acc
  | b :: rest =>
    match matchKnownPrefix xs with
    | some (nm, xs') =>
      compressBytesAux xs' [] (flushRaw acc ++ [nm])
    | none =>
      let (more, xs') := countLeadingEq b rest
      let runLen := more + 1
      if runLen ≥ 12 then
        compressBytesAux xs' [] (flushRaw acc ++ [s!"List.replicate {runLen} {fmtByte b}"])
      else
        compressBytesAux rest (b :: rawRev) acc

private def fmtBytesDef (nm : String) (bs : HwBytes) : Array String :=
  let parts := compressBytesAux bs [] []
  let rhs := match parts with
    | [] => "([] : HwBytes)"
    | [p] => p
    | p :: ps => p ++ " ++\n  " ++ String.intercalate " ++\n  " ps
  let lines := (s!"def {nm} : HwBytes :=\n  " ++ rhs).splitOn "\n"
  lines.toArray

structure GenState where
  modPrefix : String
  byteMap : Std.HashMap UInt64 (List (HwBytes × String)) := {}
  byteNextIdx : Nat := 0
  curByteMod : Nat := 0
  curByteLines : Nat := 0
  curByteBuf : Array String := #[]
  byteFiles : Array (Array String) := #[]
  termMap : Std.HashMap Nat (List (DY.Bytes × String)) := {}
  termNextIdx : Nat := 0
  curTermMod : Nat := 0
  curTermLines : Nat := 0
  curTermBuf : Array String := #[]
  termFiles : Array (Array String) := #[]

private def internBytes (bs : HwBytes) : StateM GenState String := do
  if bs.isEmpty then
    return "([] : HwBytes)"
  for (pat, nm) in knownSlices do
    if pat == bs then
      return nm
  let h := fnvBytes bs
  let st ← get
  let bucket := st.byteMap.getD h []
  for (b', ref) in bucket do
    if b' == bs then
      return ref
  let idx := st.byteNextIdx
  let localNm := s!"b_{idx}"
  let defLines := fmtBytesDef localNm bs
  let needFlush := st.curByteLines > 0 && st.curByteLines + defLines.size + 1 > 480
  let st :=
    if needFlush then
      { st with
        byteFiles := st.byteFiles.push st.curByteBuf
        curByteMod := st.curByteMod + 1
        curByteLines := 0
        curByteBuf := #[] }
    else st
  let modNm := s!"{st.modPrefix}Bytes{pad2 st.curByteMod}"
  let ref := s!"{modNm}.{localNm}"
  let newBuf := (st.curByteBuf ++ defLines).push ""
  set { st with
    byteNextIdx := idx + 1
    curByteBuf := newBuf
    curByteLines := newBuf.size
    byteMap := st.byteMap.insert h ((bs, ref) :: bucket) }
  return ref

private def internPbValue : DY.TrWire.PbValue → StateM GenState String
  | .varint n => pure s!".varint {n}"
  | .bytes b => do
    let br ← internBytes b
    pure s!".bytes {br}"
  | .unknown wt p => do
    let pr ← internBytes p
    pure s!".unknown {wt} {pr}"

private def internFieldItem : DY.TrWire.FieldItem → StateM GenState String
  | .known tag kp vp => pure s!".known {tag} {kp} {vp}"
  | .extra tag val kp vp => do
    let vr ← internPbValue val
    pure s!".extra {tag} ({vr}) {kp} {vp}"

private def internEncodingVariation (ev : DY.TrWire.EncodingVariation) : StateM GenState String := do
  if ev == DY.TrWire.canonicalVariation then
    return "DY.TrWire.canonicalVariation"
  let trail ← internBytes ev.ratchetKeyTrailingBytes
  let fs ← ev.fields.mapM internFieldItem
  let fStr := "[" ++ String.intercalate ", " fs ++ "]"
  return s!"⟨{ev.versionLowNibble}, {trail}, {ev.counterHigh}, {ev.previousCounterHigh}, {fStr}⟩"

section UnsealGen
unseal DY.Bytes

private def pushTermDef (b : DY.Bytes) (rhs : String) : StateM GenState String := do
  let h := hashTermNat 24 b
  let st ← get
  let bucket := st.termMap.getD h []
  match bucket.find? (fun p => beqBareOptFast 256 p.1.val b.val == some true) with
  | some (_, ref) => return ref
  | none =>
    let idx := st.termNextIdx
    let localNm := s!"t_{idx}"
    let needFlush := st.curTermLines ≥ 450
    let st :=
      if needFlush then
        { st with
          termFiles := st.termFiles.push st.curTermBuf
          curTermMod := st.curTermMod + 1
          curTermLines := 0
          curTermBuf := #[] }
      else st
    let modNm := s!"{st.modPrefix}Terms{pad2 st.curTermMod}"
    let ref := s!"{modNm}.{localNm}"
    let line := s!"def {localNm} : DY.Bytes := {rhs}"
    set { st with
      termNextIdx := idx + 1
      curTermBuf := st.curTermBuf.push line
      curTermLines := st.curTermLines + 1
      termMap := st.termMap.insert h ((b, ref) :: bucket) }
    return ref

structure BuiltNode where
  id : Nat
  term : DY.Bytes
  termRef : String
  skel : NodeSkel
  skelStr : String
  bytes : HwBytes
  bytesRef : String
  hasMemo : Bool

structure LocalState where
  gSt : GenState
  localIds : Std.HashMap Nat (List (DY.Bytes × Nat)) := {}
  nodes : Array BuiltNode := #[]

private def liftGen {α : Type} (m : StateM GenState α) : StateM LocalState α := do
  let ls ← get
  let (a, gs') := m.run ls.gSt
  set { ls with gSt := gs' }
  return a

private def visitNode (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    Nat → DY.Bytes → StateM LocalState (Nat × String)
  | 0, _ => panic! "visitNode: out of fuel"
  | fuel + 1, b => do
    let h := hashTermNat 24 b
    let ls ← get
    let bucket := ls.localIds.getD h []
    match bucket.find? (fun p => beqBareOptFast 256 p.1.val b.val == some true) with
    | some (_, nid) => return (nid, (ls.nodes[nid]?).map (·.termRef) |>.getD "")
    | none =>
      match b.view? DY.BytesF with
      | none => panic! "visitNode: view? returned none"
      | some x =>
        let (sk, skStr, tRhs) ←
          match x with
          | ⟨⟨0, _⟩, v⟩ =>
            pure (.rnd v.timestamp v.size,
              s!".rnd {v.timestamp} {v.size}",
              s!"tRnd {v.timestamp} {v.size}")
          | ⟨⟨1, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let bs := ofByteArray v.lit
            let br ← liftGen (internBytes bs)
            pure (.lit bs, s!".lit {br}", s!"tLit {br}")
          | ⟨⟨2, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (l, lr) ← visitNode i S g fuel v.lhs
            let (r, rr) ← visitNode i S g fuel v.rhs
            pure (.cat l r, s!".cat {l} {r}", s!"tCat {lr} {rr}")
          | ⟨⟨3, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.sk
            pure (.dhPk s, s!".dhPk {s}", s!"tDhPk {sr}")
          | ⟨⟨3, _⟩, ⟨⟨1, _⟩, v⟩⟩ => do
            let (p, pr) ← visitNode i S g fuel v.pk
            let (s, sr) ← visitNode i S g fuel v.sk
            pure (.dh p s, s!".dh {p} {s}", s!"tDh {pr} {sr}")
          | ⟨⟨4, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (a, ar) ← visitNode i S g fuel v.salt
            let (ikm, ikmr) ← visitNode i S g fuel v.ikm
            pure (.kdf a ikm, s!".kdf {a} {ikm}", s!"tKdf {ar} {ikmr}")
          | ⟨⟨5, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (k, kr) ← visitNode i S g fuel v.key
            let (iv, ivr) ← visitNode i S g fuel v.iv
            let (m, mr) ← visitNode i S g fuel v.msg
            pure (.sym k iv m, s!".sym {k} {iv} {m}", s!"tSym {kr} {ivr} {mr}")
          | ⟨⟨6, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (inp, inpr) ← visitNode i S g fuel v.input
            pure (.tr8 inp, s!".tr8 {inp}", s!"tTr8 {inpr}")
          | ⟨⟨7, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (k, kr) ← visitNode i S g fuel v.key
            let tv := s!"⟨{v.torsion.val}, by decide⟩"
            let vv := s!"⟨{v.variation.val}, by decide⟩"
            pure (.var k v.torsion v.variation,
              s!".var {k} {tv} {vv}",
              s!"tVar {kr} {tv} {vv}")
          | ⟨⟨8, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.sk
            pure (.kemPk s, s!".kemPk {s}", s!"tKemPk {sr}")
          | ⟨⟨8, _⟩, ⟨⟨1, _⟩, v⟩⟩ => do
            let (p, pr) ← visitNode i S g fuel v.pk
            let (e, er) ← visitNode i S g fuel v.entropy
            pure (.kemEnc p e, s!".kemEnc {p} {e}", s!"tKemEnc {pr} {er}")
          | ⟨⟨8, _⟩, ⟨⟨2, _⟩, v⟩⟩ => do
            let (p, pr) ← visitNode i S g fuel v.pk
            let (e, er) ← visitNode i S g fuel v.entropy
            pure (.kemSS p e, s!".kemSS {p} {e}", s!"tKemSS {pr} {er}")
          | ⟨⟨9, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.sk
            pure (.vk s, s!".vk {s}", s!"tVk {sr}")
          | ⟨⟨9, _⟩, ⟨⟨1, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.sk
            let (n, nr) ← visitNode i S g fuel v.nonce
            let (m, mr) ← visitNode i S g fuel v.msg
            pure (.sig s n m, s!".sig {s} {n} {m}", s!"tSig {sr} {nr} {mr}")
          | ⟨⟨10, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (a, ar) ← visitNode i S g fuel v.authKey
            let (p, pr) ← visitNode i S g fuel v.params
            pure (.sInit a p, s!".sInit {a} {p}", s!"tSInit {ar} {pr}")
          | ⟨⟨10, _⟩, ⟨⟨1, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.st
            let (c, cr) ← visitNode i S g fuel v.coins
            pure (.sSendSt s c, s!".sSendSt {s} {c}", s!"tSSendSt {sr} {cr}")
          | ⟨⟨10, _⟩, ⟨⟨2, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.st
            let (c, cr) ← visitNode i S g fuel v.coins
            pure (.sSendK s c, s!".sSendK {s} {c}", s!"tSSendK {sr} {cr}")
          | ⟨⟨10, _⟩, ⟨⟨3, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.st
            let (c, cr) ← visitNode i S g fuel v.coins
            pure (.sSendM s c, s!".sSendM {s} {c}", s!"tSSendM {sr} {cr}")
          | ⟨⟨10, _⟩, ⟨⟨4, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.st
            let (m, mr) ← visitNode i S g fuel v.msg
            pure (.sRecvSt s m, s!".sRecvSt {s} {m}", s!"tSRecvSt {sr} {mr}")
          | ⟨⟨10, _⟩, ⟨⟨5, _⟩, v⟩⟩ => do
            let (s, sr) ← visitNode i S g fuel v.st
            let (m, mr) ← visitNode i S g fuel v.msg
            pure (.sRecvK s m, s!".sRecvK {s} {m}", s!"tSRecvK {sr} {mr}")
          | ⟨⟨10, _⟩, ⟨⟨6, _⟩, v⟩⟩ => do
            let (a, ar) ← visitNode i S g fuel v.authKey
            let (p, pr) ← visitNode i S g fuel v.params
            let (idx, idxr) ← visitNode i S g fuel v.idx
            pure (.sChain a p idx, s!".sChain {a} {p} {idx}", s!"tSChain {ar} {pr} {idxr}")
          | ⟨⟨11, _⟩, ⟨⟨0, _⟩, v⟩⟩ => do
            let (rk, rkr) ← visitNode i S g fuel v.senderRatchetKey
            let (ct, ctr) ← visitNode i S g fuel v.ciphertext
            let (pq, pqr) ← visitNode i S g fuel v.pqRatchet
            let ev ← liftGen (internEncodingVariation v.encodingVariation)
            pure (.trW v.version rk v.counter v.previousCounter ct pq v.encodingVariation,
              s!".trW {v.version.toNat} {rk} {v.counter.toNat} {v.previousCounter.toNat} {ct} {pq} ({ev})",
              s!"tTrW {v.version.toNat} {rkr} {v.counter.toNat} {v.previousCounter.toNat} {ctr} {pqr} ({ev})")
        let tRef ← liftGen (pushTermDef b tRhs)
        let ls ← get
        let bOf := fun cid => (ls.nodes[cid]?).map (·.bytes) |>.getD []
        let (bs, hm) := skelEval i S g b bOf sk
        let bRef ← liftGen (internBytes bs)
        let ls ← get
        let nid := ls.nodes.size
        let nd : BuiltNode := {
          id := nid, term := b, termRef := tRef, skel := sk, skelStr := skStr,
          bytes := bs, bytesRef := bRef, hasMemo := hm
        }
        let bucketNow := ls.localIds.getD h []
        set { ls with
          nodes := ls.nodes.push nd
          localIds := ls.localIds.insert h ((b, nid) :: bucketNow) }
        return (nid, tRef)

end UnsealGen

private def chooseDepth (numNodes : Nat) : Nat :=
  let rec go (d : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => d
    | f + 1 => if (1 <<< d) ≥ numNodes then d else go (d + 1) f
  go 5 20

private instance {α : Type} : Inhabited (BinTree α) := ⟨.empty⟩

private def btInsert {α : Type} : Nat → BinTree α → Nat → α → BinTree α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, k, v =>
    if k % 2 == 0 then .branch (btInsert d .empty (k / 2) v) .empty
    else .branch .empty (btInsert d .empty (k / 2) v)
  | d + 1, .branch lo hi, k, v =>
    if k % 2 == 0 then .branch (btInsert d lo (k / 2) v) hi
    else .branch lo (btInsert d hi (k / 2) v)
  | _ + 1, .leaf _, _, _ => panic! "btInsert: unexpected early leaf"

private def splitBinDepth {α : Type} : Nat → BinTree α → List (BinTree α)
  | 0, t => [t]
  | n + 1, .branch lo hi => splitBinDepth n lo ++ splitBinDepth n hi
  | n + 1, .empty => splitBinDepth n .empty ++ splitBinDepth n .empty
  | _ + 1, .leaf _ => panic! "splitBinDepth: unexpected leaf above split depth"

private def maxTrieBucket {α : Type} : Trie α → Nat
  | .leaf xs => xs.length
  | .branch lo hi => Nat.max (maxTrieBucket lo) (maxTrieBucket hi)

private def mapTrie {α β : Type} (f : α → β) : Trie α → Trie β
  | .leaf xs => .leaf (xs.map f)
  | .branch lo hi => .branch (mapTrie f lo) (mapTrie f hi)

private def trieEmptyDepth? {α : Type} : Trie α → Option Nat
  | .leaf [] => some 0
  | .leaf (_ :: _) => none
  | .branch lo hi =>
    match trieEmptyDepth? lo, trieEmptyDepth? hi with
    | some d1, some d2 => if d1 == d2 then some (d1 + 1) else none
    | _, _ => none

private partial def renderSubTrie (indent : String) : Trie String → List String
  | t =>
    match trieEmptyDepth? t with
    | some d => [s!"{indent}(emptyTrie {d})"]
    | none =>
      match t with
      | .leaf [] => [s!"{indent}(.leaf [])"]
      | .leaf xs =>
        let inline := String.intercalate ", " xs
        if indent.length + inline.length + 10 ≤ 96 then
          [s!"{indent}(.leaf [{inline}])"]
        else
          match xs with
          | [] => [s!"{indent}(.leaf [])"]
          | e :: es =>
            [s!"{indent}(.leaf [{e},"] ++
              (es.dropLast.map fun x => s!"{indent}  {x},") ++
              [s!"{indent}  {es.getLast!}])"]
      | .branch lo hi =>
        match renderSubTrie (indent ++ "  ") lo, renderSubTrie (indent ++ "  ") hi with
        | [lLine], [hLine] =>
          let ls := lLine.trimAscii.toString
          let hs := hLine.trimAscii.toString
          if indent.length + ls.length + hs.length + 12 ≤ 96 then
            [s!"{indent}(.branch {ls} {hs})"]
          else
            [s!"{indent}(.branch", lLine, hLine ++ ")"]
        | lLines, hLines =>
          [s!"{indent}(.branch"] ++ lLines ++ hLines ++ [s!"{indent})"]

private partial def renderBinTree (indent : String) : BinTree String → List String
  | .empty => [s!"{indent}.empty"]
  | .leaf s => [s!"{indent}(.leaf {s})"]
  | .branch lo hi =>
    match renderBinTree (indent ++ "  ") lo, renderBinTree (indent ++ "  ") hi with
    | [lLine], [hLine] =>
      let ls := lLine.trimAscii.toString
      let hs := hLine.trimAscii.toString
      if indent.length + ls.length + hs.length + 12 ≤ 96 then
        [s!"{indent}(.branch {ls} {hs})"]
      else
        [s!"{indent}(.branch", lLine, hLine ++ ")"]
    | lLines, hLines =>
      [s!"{indent}(.branch"] ++ lLines ++ hLines ++ [s!"{indent})"]

structure BuiltTable where
  depth : Nat
  nodes : Array BuiltNode
  idTree : BinTree CertNode
  strIdTree : BinTree String
  hashTrie : Trie Nat
  strHashTrie : Trie String

private def buildTable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hashDepth : Nat) (roots : List DY.Bytes) : StateM GenState BuiltTable := do
  let gs ← get
  let initLs : LocalState := { gSt := gs }
  let ((), endLs) := (do
    for r in roots do
      let _ ← visitNode i S g 256 r).run initLs
  set endLs.gSt
  let nodes := endLs.nodes
  let depth := chooseDepth nodes.size
  let idTree := nodes.foldl (fun tr nd =>
    btInsert depth tr nd.id ⟨nd.id, nd.term, nd.skel, nd.bytes, nd.hasMemo⟩) .empty
  let strIdTree := nodes.foldl (fun tr nd =>
    btInsert depth tr nd.id
      s!"⟨{nd.id}, {nd.termRef}, {nd.skelStr}, {nd.bytesRef}, {nd.hasMemo}⟩") .empty
  let hashTrie := nodes.foldl (fun ht nd =>
    trieInsert ht (hashTermNat 4 nd.term) nd.id) (emptyTrie hashDepth)
  let strHashTrie := mapTrie Nat.repr hashTrie
  return { depth, nodes, idTree, strIdTree, hashTrie, strHashTrie }

private def verifyBuiltTable (label : String) (i : ExternInterpretation)
    (S : OpaqueSymbolSemantics) (g : Ghost) (bt : BuiltTable)
    (roots : List DY.Bytes) : IO Unit := do
  let memoCnt := (bt.nodes.filter (·.hasMemo)).size
  let maxBuck := maxTrieBucket bt.hashTrie
  IO.println s!"[{label}] nodes={bt.nodes.size}, memos={memoCnt}, depth={bt.depth}, maxHashBucket={maxBuck}, roots={roots.length}"
  unless checkSubBytes i S g bt.depth bt.idTree bt.idTree do
    throw <| IO.userError s!"[{label}] checkSubBytes FAILED!"
  for nd in bt.nodes do
    match btGet bt.depth bt.idTree nd.id with
    | none => throw <| IO.userError s!"[{label}] btGet missing id {nd.id}"
    | some cn =>
      unless cn.bytes == evalGammaFast i S g nd.term do
        throw <| IO.userError s!"[{label}] evalGammaFast mismatch at id {nd.id}"
  let ct : CertTable := ⟨bt.depth, bt.idTree, bt.hashTrie⟩
  let missing := roots.filter fun r => (tableLookup ct r).isNone
  unless missing.isEmpty do
    throw <| IO.userError s!"[{label}] {missing.length} roots missing from table!"
  IO.println s!"[{label}] checkSubBytes OK, evalGammaFast matches, all roots present."

private def finalizeState (st : GenState) : Array (Array String) × Array (Array String) :=
  let bf := if st.curByteBuf.isEmpty then st.byteFiles else st.byteFiles.push st.curByteBuf
  let tf := if st.curTermBuf.isEmpty then st.termFiles else st.termFiles.push st.curTermBuf
  (bf, tf)

private def whisperTrialsGen (interp : ExternInterpretation) (r : ProtocolSetup)
    (S : OpaqueSymbolSemantics) (g : Ghost) (tr : ExecTrace) (msg : TRSignalMsg) : List TrialCtx :=
  if msg.version == messageVersion then
    let γ := evalGammaFast interp S g
    (availableStates r tr).flatMap fun st =>
      let own := ownKeys r tr st msg
      let chains :=
        (st.toDRState.recv.filter fun c => γ c.ratchetKey == γ msg.ratchetKey) ++
        match findRecvChain st.recv msg.ratchetKey, recvHalfStep st.toDRState msg.ratchetKey with
        | none, some (_, c) => [c]
        | _, _ => []
      chains.map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          { peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
            ownSalts := [], seed? := none }
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }
  else []

private def visEntryRoots (v : VisEntry) : List DY.Bytes :=
  match v.layout with
  | .preKeyInner eks => v.terms ++ eks
  | _ => v.terms

private def msgRoots (msg : TRSignalMsg) : List DY.Bytes :=
  [msg.wire, msg.mac, msg.ciphertext, msg.ratchetKey, msg.pqRatchet]

private def anchorRoots (sts : List (DY.PersistentLocalState.LocalState TRState)) :
    List DY.Bytes :=
  sts.flatMap fun ls => let (a, s) := stateAnchorPair ls; [a, s]

private def call6Roots : List DY.Bytes :=
  let ctxs6 := whisperTrialsGen myInterp r0 S0Comp myGhost (trAt 6) msgReply0Sig
  let stored6 := storedStates r0 (trAt 6)
  let send6 := [ekTerm, ctTerm, msg0Term, msg1Term, msgReply0Term]
  let pt6 := [m0, m1, m2]
  let new6 := msgReply0Term :: ctxs6.flatMap (trialTerms (saltsAt 6) msgReply0Sig)
  let mac6 := macTerms (saltsAt 6) msgReply0Sig ctxs6
  let rks6 := msgReply0Sig.ratchetKey ::
    (storedRatchetKeysNoSkipped r0 (trAt 6) ++ storedRatchetKeys r0 (trAt 6) msgReply0Sig)
  new6 ++ send6 ++ stored6.flatMap trStateProxyRoots ++ pqSecretsList ++ pt6 ++
    anchorRoots stored6 ++ mac6 ++ rks6

private def fullCliRoots : List DY.Bytes :=
  let allStored :=
    storedStates r0 (trAt 3) ++ storedStates r0 (trAt 4) ++
    storedStates r0 (trAt 6) ++ storedStates r0 (trAt 10)
  let send10 := [ekTerm, ctTerm, msg0Term, msg1Term, msgReply0Term, msg2Term]
  let pt10 := [m0, m1, m2, m3]
  let vis11 := (visAt 11).flatMap visEntryRoots
  let msgs := [msg0Sig, msg1Sig, msgReply0Sig, msg2Sig].flatMap msgRoots
  let reps := [x3Rep.ek, x3Rep.ct, x3Rep.msg, x4Rep.ek, x4Rep.ct, x4Rep.msg]
  let ctxs3 := match parsePreKeyWire (wirePrekeyTag :: pkMsg0.bytes) with
    | some p3 => bobTrials r0 (trAt 3) p3 x3Rep msg0Sig
    | none => []
  let r3 := ctxs3.flatMap (trialTerms (saltsAt 3) msg0Sig) ++ macTerms (saltsAt 3) msg0Sig ctxs3
  let ctxs4b := match parsePreKeyWire (wirePrekeyTag :: pkMsg1.bytes) with
    | some p4 => bobTrials r0 (trAt 4) p4 x4Rep msg1Sig
    | none => []
  let ctxs4w := whisperTrialsGen myInterp r0 S0Comp myGhost (trAt 4) msg1Sig
  let r4 := ctxs4b.flatMap (trialTerms (saltsAt 4) msg1Sig) ++
    macTerms (saltsAt 4) msg1Sig ctxs4b ++
    (msg1Term :: ctxs4w.flatMap (trialTerms (saltsAt 4) msg1Sig)) ++
    macTerms (saltsAt 4) msg1Sig ctxs4w ++
    (msg1Sig.ratchetKey ::
      (storedRatchetKeysNoSkipped r0 (trAt 4) ++ storedRatchetKeys r0 (trAt 4) msg1Sig))
  let r6 := call6Roots
  let ctxs8 := whisperTrialsGen myInterp r0 S0Comp myGhost (trAt 10) msg2Sig
  let r8 := (msg2Term :: ctxs8.flatMap (trialTerms (saltsAt 10) msg2Sig)) ++
    macTerms (saltsAt 10) msg2Sig ctxs8 ++
    (msg2Sig.ratchetKey ::
      (storedRatchetKeysNoSkipped r0 (trAt 10) ++ storedRatchetKeys r0 (trAt 10) msg2Sig))
  allStored.flatMap trStateProxyRoots ++ pqSecretsList ++ send10 ++ pt10 ++
    anchorRoots allStored ++ vis11 ++ msgs ++ reps ++ r3 ++ r4 ++ r6 ++ r8

private def hsRoots (withOpk : Bool) : List DY.Bytes :=
  let r := mkRecords withOpk
  let x := honestPreKeyRep withOpk
  let p := p0Fields withOpk
  let vis := (visOfComp withOpk).flatMap (·.terms)
  if withOpk then
    let msg := encSig stA0Opk coins0Opk key0Opk m0Opk
    let ctxs := bobTrials r t6Opk p x msg
    let salts := [DY.Spqr.zeroKey, key0Opk]
    let sts : List (DY.PersistentLocalState.LocalState TRState) :=
      [⟨"alice", stA0Opk⟩, ⟨"alice", stA1Opk⟩]
    let secs : List DY.Bytes := pqSecretsList ++
      [DY.Comparse.serialize (⟨"bob", { kind := .oneTimePrekey, sk := opkB }⟩ :
        DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState)]
    let sends := [oOpk.ek, oOpk.ct, encMsg stA0Opk coins0Opk key0Opk m0Opk]
    vis ++ sts.flatMap trStateProxyRoots ++ anchorRoots sts ++ secs ++ sends ++ [m0Opk] ++
      [x.ek, x.ct, x.msg] ++ msgRoots msg ++
      ctxs.flatMap (trialTerms salts msg) ++ macTerms salts msg ctxs
  else
    let msg := encSig stA0 coins0 key0 m0
    let ctxs := bobTrials r t6 p x msg
    let salts := [DY.Spqr.zeroKey, key0]
    let sts : List (DY.PersistentLocalState.LocalState TRState) :=
      [⟨"alice", stA0⟩, ⟨"alice", stA1⟩]
    let secs := pqSecretsList
    let sends := [o1.ek, o1.ct, encMsg stA0 coins0 key0 m0]
    vis ++ sts.flatMap trStateProxyRoots ++ anchorRoots sts ++ secs ++ sends ++ [m0] ++
      [x.ek, x.ct, x.msg] ++ msgRoots msg ++
      ctxs.flatMap (trialTerms salts msg) ++ macTerms salts msg ctxs

private def certAllImports : Array String := #[
  "import all DY.Bytes.Basic",
  "import all DY.ALaCarte.Basic",
  "import all DY.ALaCarte.DecidableEq",
  "import all DY.ALaCarte.Ordering",
  "import all DY.Misc.Instances",
  "import all Comparse.Basic",
  "import all Comparse.Formats.Basic",
  "import all Comparse.Formats.Derived",
  "import all DY.Comparse",
  "import all DY.Trace.Basic",
  "import all DY.Trace.Monad",
  "import all DY.Trace.Manipulation",
  "import all DY.Trace.BaseAttackerKnowledge",
  "import all DY.Actions.Network",
  "import all DY.Actions.PersistentLocalState",
  "import all DY.Actions.PersistentGlobalState",
  "import all DY.Actions.ProtocolEvent",
  "import all DY.Actions.Random",
  "import all DY.EquationalTheory.Literal",
  "import all DY.EquationalTheory.Concat",
  "import all DY.EquationalTheory.DiffieHellman",
  "import all DY.EquationalTheory.KdfExtract",
  "import all DY.EquationalTheory.Sign",
  "import all Symbolic.Specifications.Model.EquationalTheory.SymEnc",
  "import all Symbolic.Specifications.Model.EquationalTheory.Trunc",
  "import all Symbolic.Specifications.Model.EquationalTheory.X25519",
  "import all Symbolic.Specifications.Model.EquationalTheory.Kem",
  "import all Symbolic.Specifications.Model.EquationalTheory.Spqr",
  "import all Symbolic.Specifications.Model.EquationalTheory.TrWireMsg",
  "import all Symbolic.Specifications.Model.PQXDH",
  "import all Symbolic.Specifications.Model.TripleRatchet",
  "import all Symbolic.Specifications.Model.Instance",
  "import all Init.Data.Array.Attach",
  "import all Init.Data.Array.DecidableEq",
  "import all Init.Data.Nat.Bitwise.Basic",
  "import all Init.Data.Ord.Array",
  "import all Init.Data.Repr",
  "import all Init.Data.String.Bootstrap",
  "import all Init.Data.String.Defs"
]

private def writeBytesFile (dir modPref : String) (idx : Nat) (body : Array String) : IO Unit := do
  let modNm := s!"{modPref}Bytes{pad2 idx}"
  let ns := s!"Symbolic.Proofs.Tests.CliNonvacuity.Table.{modNm}"
  let hdr := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Witness",
    "public import Symbolic.Proofs.Tests.Refinement.Cli.RecvWhisperNonVacuityBase",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    s!"namespace {ns}",
    "",
    "open DY.Libsignal (HwBytes)",
    "open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers",
    "  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness",
    "  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)",
    ""
  ]
  let ftr := #[s!"end {ns}", ""]
  let allLines := hdr ++ body ++ ftr
  writeLeanFile s!"{dir}/{modNm}.lean" (String.intercalate "\n" allLines.toList)
  IO.println s!"  wrote {modNm}.lean ({allLines.size} lines)"

private def writeTermsFile (dir modPref : String) (numByteFiles idx : Nat)
    (body : Array String) : IO Unit := do
  let modNm := s!"{modPref}Terms{pad2 idx}"
  let ns := s!"Symbolic.Proofs.Tests.CliNonvacuity.Table.{modNm}"
  let impLines : Array String :=
    if idx == 0 then
      #[
        "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm"
      ] ++ ((List.range numByteFiles).map fun bi =>
        s!"public import Symbolic.Proofs.Tests.CliNonvacuity.Table.{modPref}Bytes{pad2 bi}").toArray
    else
      #[s!"public import Symbolic.Proofs.Tests.CliNonvacuity.Table.{modPref}Terms{pad2 (idx - 1)}"]
  let hdr := #["module", ""] ++ impLines ++ #[
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    s!"namespace {ns}",
    "",
    "open scoped DY.Libsignal.Composed",
    "open DY.Libsignal (HwBytes)",
    "open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers",
    "  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness",
    "  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm",
    "  (sendAddrABytes tRnd tLit tCat tDhPk tDh tKdf tSym tTr8 tVar",
    "   tKemPk tKemEnc tKemSS tVk tSig",
    "   tSInit tSSendSt tSSendK tSSendM tSRecvSt tSRecvK tSChain tTrW)",
    ""
  ]
  let ftr := #["", s!"end {ns}", ""]
  let allLines := hdr ++ body ++ ftr
  writeLeanFile s!"{dir}/{modNm}.lean" (String.intercalate "\n" allLines.toList)
  IO.println s!"  wrote {modNm}.lean ({allLines.size} lines)"

private def nodesHeader (ns lastTerm : String) : Array String :=
  #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
    s!"public import Symbolic.Proofs.Tests.CliNonvacuity.Table.{lastTerm}",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    s!"namespace {ns}",
    "",
    "open DY.Libsignal (HwBytes)",
    "open Symbolic.Proofs.Tests.Refinement.Cli.NonVacuityHelpers",
    "  (nvVec1568 nvVec3168 nvEk1152 nvDk2400)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness",
    "  (myKyberPubBytes myKyberSecField pt0 pt1 ptReply0 pt2)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm (sendAddrABytes)",
    ""
  ]

private def emitCall6 (dir : String) : IO Unit := do
  let roots := call6Roots
  let initSt : GenState := { modPrefix := "Call6" }
  let (bt, endSt) := (buildTable myInterp S0Comp myGhost 9 roots).run initSt
  verifyBuiltTable "call6" myInterp S0Comp myGhost bt roots
  let (byteFiles, termFiles) := finalizeState endSt
  IO.println s!"[call6] unique bytes defs={endSt.byteNextIdx} across {byteFiles.size} files; unique term defs={endSt.termNextIdx} across {termFiles.size} files"
  for idx in List.range byteFiles.size do
    writeBytesFile dir "Call6" idx byteFiles[idx]!
  for idx in List.range termFiles.size do
    writeTermsFile dir "Call6" byteFiles.size idx termFiles[idx]!
  let lastTerm := s!"Call6Terms{pad2 (termFiles.size - 1)}"
  let nodeLines :=
    nodesHeader "Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Nodes" lastTerm ++
    #[s!"def call6IdTree : BinTree CertNode :="] ++
    (renderBinTree "  " bt.strIdTree).toArray ++
    #["", "end Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Nodes", ""]
  writeLeanFile s!"{dir}/Call6Nodes.lean" (String.intercalate "\n" nodeLines.toList)
  IO.println s!"  wrote Call6Nodes.lean ({nodeLines.size} lines)"
  let tblLines := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Nodes",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Table",
    "",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (Trie emptyTrie)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (CertTable)",
    "",
    "def call6HashTrie : Trie Nat :="
  ] ++ (renderSubTrie "  " bt.strHashTrie).toArray ++ #[
    "",
    s!"def call6Table : CertTable := ⟨{bt.depth}, Call6Nodes.call6IdTree, call6HashTrie⟩",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Table",
    ""
  ]
  writeLeanFile s!"{dir}/Call6Table.lean" (String.intercalate "\n" tblLines.toList)
  IO.println s!"  wrote Call6Table.lean ({tblLines.size} lines)"
  let certLines := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Table",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag"
  ] ++ certAllImports ++ #[
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Cert",
    "",
    "set_option maxRecDepth 200000",
    "",
    "open DY.Libsignal (HwBytes)",
    "open DY.Libsignal.Composed.Refinement (gamma)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs (S0 myGhost)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag",
    "  (S0Comp S0_eq_comp myGhostComp myGhost_eq_comp)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
    "  (IdTreeSound btMapTerm btMapSkelTerm checkSubBytes idTreeSound_of_cert",
    "   tableGamma gamma_eq_tableGamma)",
    "",
    "theorem call6_wire :",
    s!"    btMapTerm Call6Nodes.call6IdTree =",
    s!"      btMapSkelTerm {bt.depth} Call6Nodes.call6IdTree Call6Nodes.call6IdTree := by rfl",
    "",
    "theorem call6_bytes :",
    s!"    checkSubBytes myInterp S0Comp myGhostComp {bt.depth}",
    "      Call6Nodes.call6IdTree Call6Nodes.call6IdTree = true := by",
    "  decide +kernel",
    "",
    "theorem call6_sound :",
    s!"    IdTreeSound myInterp S0Comp myGhostComp Call6Table.call6Table.depth Call6Table.call6Table.idTree :=",
    "  idTreeSound_of_cert call6_wire call6_bytes",
    "",
    "noncomputable def call6Gamma : DY.Bytes → HwBytes :=",
    "  tableGamma myInterp S0Comp myGhostComp Call6Table.call6Table",
    "",
    "theorem gamma_comp_eq_call6Gamma : gamma myInterp S0Comp myGhostComp = call6Gamma :=",
    "  gamma_eq_tableGamma call6_sound",
    "",
    "theorem gamma_eq_call6Gamma : gamma myInterp S0 myGhost = call6Gamma := by",
    "  rw [S0_eq_comp, myGhost_eq_comp]",
    "  exact gamma_comp_eq_call6Gamma",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.Call6Cert",
    ""
  ]
  writeLeanFile s!"{dir}/Call6Cert.lean" (String.intercalate "\n" certLines.toList)
  IO.println s!"  wrote Call6Cert.lean ({certLines.size} lines)"

private def emitFull (dir : String) : IO Unit := do
  let cRoots := fullCliRoots
  let hfRoots := hsRoots false
  let htRoots := hsRoots true
  let initSt : GenState := { modPrefix := "" }
  let ((cBt, hfBt, htBt), endSt) := (do
    let c ← buildTable myInterp S0Comp myGhost 9 cRoots
    let hf ← buildTable myInterp (mySemComp false) (ghostOf false) 8 hfRoots
    let ht ← buildTable myInterp (mySemComp true) (ghostOf true) 8 htRoots
    pure (c, hf, ht)).run initSt
  verifyBuiltTable "cliTable" myInterp S0Comp myGhost cBt cRoots
  verifyBuiltTable "hsFalseTable" myInterp (mySemComp false) (ghostOf false) hfBt hfRoots
  verifyBuiltTable "hsTrueTable" myInterp (mySemComp true) (ghostOf true) htBt htRoots
  let (byteFiles, termFiles) := finalizeState endSt
  IO.println s!"[full] unique bytes defs={endSt.byteNextIdx} across {byteFiles.size} files; unique term defs={endSt.termNextIdx} across {termFiles.size} files"
  for idx in List.range byteFiles.size do
    writeBytesFile dir "" idx byteFiles[idx]!
  for idx in List.range termFiles.size do
    writeTermsFile dir "" byteFiles.size idx termFiles[idx]!
  let lastTerm := s!"Terms{pad2 (termFiles.size - 1)}"
  let sub16 := splitBinDepth 4 cBt.strIdTree
  unless sub16.length == 16 do
    throw <| IO.userError s!"expected 16 subtrees, got {sub16.length}"
  for grp in List.range 4 do
    let subMod := s!"Nodes{pad2 grp}"
    let ns := s!"Symbolic.Proofs.Tests.CliNonvacuity.Table.{subMod}"
    let mut lines : Array String := nodesHeader ns lastTerm
    for off in List.range 4 do
      let ci := grp * 4 + off
      lines := lines.push s!"def sub{pad2 ci} : BinTree CertNode :="
      lines := lines ++ (renderBinTree "  " (sub16.getD ci .empty)).toArray
      lines := lines.push ""
    lines := lines.push s!"end {ns}"
    lines := lines.push ""
    writeLeanFile s!"{dir}/{subMod}.lean" (String.intercalate "\n" lines.toList)
    IO.println s!"  wrote {subMod}.lean ({lines.size} lines)"
  let cliTblLines : Array String := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes00",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes01",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes02",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Nodes03",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable",
    "",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (Trie emptyTrie)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (BinTree CertNode CertTable)",
    "",
    "def cliIdTree : BinTree CertNode :=",
    "  .branch",
    "    (.branch",
    "      (.branch (.branch Nodes00.sub00 Nodes00.sub01)",
    "               (.branch Nodes00.sub02 Nodes00.sub03))",
    "      (.branch (.branch Nodes01.sub04 Nodes01.sub05)",
    "               (.branch Nodes01.sub06 Nodes01.sub07)))",
    "    (.branch",
    "      (.branch (.branch Nodes02.sub08 Nodes02.sub09)",
    "               (.branch Nodes02.sub10 Nodes02.sub11))",
    "      (.branch (.branch Nodes03.sub12 Nodes03.sub13)",
    "               (.branch Nodes03.sub14 Nodes03.sub15)))",
    "",
    "def cliHashTrie : Trie Nat :="
  ] ++ (renderSubTrie "  " cBt.strHashTrie).toArray ++ #[
    "",
    s!"def cliTable : CertTable := ⟨{cBt.depth}, cliIdTree, cliHashTrie⟩",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable",
    ""
  ]
  writeLeanFile s!"{dir}/CliTable.lean" (String.intercalate "\n" cliTblLines.toList)
  IO.println s!"  wrote CliTable.lean ({cliTblLines.size} lines)"
  for ci in List.range 16 do
    let grp := ci / 4
    let chkMod := s!"Chunk{pad2 ci}"
    let ns := s!"Symbolic.Proofs.Tests.CliNonvacuity.Table.{chkMod}"
    let chkLines : Array String := #[
      "module",
      "",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.CliTable",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag"
    ] ++ certAllImports ++ #[
      "",
      "@[expose] public section",
      "",
      "set_option autoImplicit false",
      "",
      s!"namespace {ns}",
      "",
      "set_option maxRecDepth 200000",
      "",
      "open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)",
      "open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag (S0Comp myGhostComp)",
      "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (btMapTerm btMapSkelTerm checkSubBytes)",
      "",
      s!"theorem chunk{pad2 ci}_wire :",
      s!"    btMapTerm Nodes{pad2 grp}.sub{pad2 ci} =",
      s!"      btMapSkelTerm {cBt.depth} CliTable.cliIdTree Nodes{pad2 grp}.sub{pad2 ci} := by rfl",
      "",
      s!"theorem chunk{pad2 ci}_bytes :",
      s!"    checkSubBytes myInterp S0Comp myGhostComp {cBt.depth}",
      s!"      CliTable.cliIdTree Nodes{pad2 grp}.sub{pad2 ci} = true := by",
      "  decide +kernel",
      "",
      s!"end {ns}",
      ""
    ]
    writeLeanFile s!"{dir}/{chkMod}.lean" (String.intercalate "\n" chkLines.toList)
  IO.println "  wrote Chunk00.lean .. Chunk15.lean (16 parallel leaf certificate modules)"
  let hfNodeLines :=
    nodesHeader "Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes" lastTerm ++
    #["def hsFalseIdTree : BinTree CertNode :="] ++
    (renderBinTree "  " hfBt.strIdTree).toArray ++
    #["", "end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes", ""]
  writeLeanFile s!"{dir}/HsFalseNodes.lean" (String.intercalate "\n" hfNodeLines.toList)
  IO.println s!"  wrote HsFalseNodes.lean ({hfNodeLines.size} lines)"
  let htNodeLines :=
    nodesHeader "Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes" lastTerm ++
    #["def hsTrueIdTree : BinTree CertNode :="] ++
    (renderBinTree "  " htBt.strIdTree).toArray ++
    #["", "end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes", ""]
  writeLeanFile s!"{dir}/HsTrueNodes.lean" (String.intercalate "\n" htNodeLines.toList)
  IO.println s!"  wrote HsTrueNodes.lean ({htNodeLines.size} lines)"
  let hsTblLines : Array String := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsFalseNodes",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTrueNodes",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables",
    "",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval (Trie emptyTrie)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (CertTable)",
    "",
    "def hsFalseHashTrie : Trie Nat :="
  ] ++ (renderSubTrie "  " hfBt.strHashTrie).toArray ++ #[
    "",
    s!"def hsFalseTable : CertTable := ⟨{hfBt.depth}, HsFalseNodes.hsFalseIdTree, hsFalseHashTrie⟩",
    "",
    "def hsTrueHashTrie : Trie Nat :="
  ] ++ (renderSubTrie "  " htBt.strHashTrie).toArray ++ #[
    "",
    s!"def hsTrueTable : CertTable := ⟨{htBt.depth}, HsTrueNodes.hsTrueIdTree, hsTrueHashTrie⟩",
    "",
    "def hsTable (withOpk : Bool) : CertTable :=",
    "  if withOpk then hsTrueTable else hsFalseTable",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables",
    ""
  ]
  writeLeanFile s!"{dir}/HsTables.lean" (String.intercalate "\n" hsTblLines.toList)
  IO.println s!"  wrote HsTables.lean ({hsTblLines.size} lines)"
  for (sfx, bLit, bt, nodeRef, tblRef) in
      [("False", "false", hfBt, "HsFalseNodes.hsFalseIdTree", "HsTables.hsFalseTable"),
       ("True", "true", htBt, "HsTrueNodes.hsTrueIdTree", "HsTables.hsTrueTable")] do
    let modNm := s!"HsCert{sfx}"
    let ns := s!"Symbolic.Proofs.Tests.CliNonvacuity.Table.{modNm}"
    let hsCertLines : Array String := #[
      "module",
      "",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsTables",
      "public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps"
    ] ++ certAllImports ++ #[
      "",
      "@[expose] public section",
      "",
      "set_option autoImplicit false",
      "",
      s!"namespace {ns}",
      "",
      "set_option maxRecDepth 200000",
      "",
      "open DY.Libsignal (HwBytes)",
      "open DY.Libsignal.Composed.Refinement (gamma)",
      "open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mySem)",
      "open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps",
      "  (mySemComp mySem_eq_comp ghostOf)",
      "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
      "  (IdTreeSound btMapTerm btMapSkelTerm checkSubBytes idTreeSound_of_cert",
      "   tableGamma gamma_eq_tableGamma)",
      "",
      s!"theorem hs{sfx}_wire :",
      s!"    btMapTerm {nodeRef} = btMapSkelTerm {bt.depth} {nodeRef} {nodeRef} := by rfl",
      "",
      s!"theorem hs{sfx}_bytes :",
      s!"    checkSubBytes myInterp (mySemComp {bLit}) (ghostOf {bLit}) {bt.depth}",
      s!"      {nodeRef} {nodeRef} = true := by",
      "  decide +kernel",
      "",
      s!"theorem hs{sfx}_sound :",
      s!"    IdTreeSound myInterp (mySemComp {bLit}) (ghostOf {bLit}) {tblRef}.depth {tblRef}.idTree :=",
      s!"  idTreeSound_of_cert hs{sfx}_wire hs{sfx}_bytes",
      "",
      s!"noncomputable def hs{sfx}Gamma : DY.Bytes → HwBytes :=",
      s!"  tableGamma myInterp (mySemComp {bLit}) (ghostOf {bLit}) {tblRef}",
      "",
      s!"theorem gamma_comp_eq_hs{sfx}Gamma :",
      s!"    gamma myInterp (mySemComp {bLit}) (ghostOf {bLit}) = hs{sfx}Gamma :=",
      s!"  gamma_eq_tableGamma hs{sfx}_sound",
      "",
      s!"theorem gamma_eq_hs{sfx}Gamma :",
      s!"    gamma myInterp (mySem {bLit}) (ghostOf {bLit}) = hs{sfx}Gamma := by",
      "  rw [mySem_eq_comp]",
      s!"  exact gamma_comp_eq_hs{sfx}Gamma",
      "",
      s!"end {ns}",
      ""
    ]
    writeLeanFile s!"{dir}/{modNm}.lean" (String.intercalate "\n" hsCertLines.toList)
    IO.println s!"  wrote {modNm}.lean ({hsCertLines.size} lines)"
  let chkImports := ((List.range 16).map fun ci =>
    s!"public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Chunk{pad2 ci}").toArray
  let wireTree :=
    "  btMapTerm_branch\n" ++
    "    (btMapTerm_branch\n" ++
    "      (btMapTerm_branch (btMapTerm_branch Chunk00.chunk00_wire Chunk01.chunk01_wire)\n" ++
    "                        (btMapTerm_branch Chunk02.chunk02_wire Chunk03.chunk03_wire))\n" ++
    "      (btMapTerm_branch (btMapTerm_branch Chunk04.chunk04_wire Chunk05.chunk05_wire)\n" ++
    "                        (btMapTerm_branch Chunk06.chunk06_wire Chunk07.chunk07_wire)))\n" ++
    "    (btMapTerm_branch\n" ++
    "      (btMapTerm_branch (btMapTerm_branch Chunk08.chunk08_wire Chunk09.chunk09_wire)\n" ++
    "                        (btMapTerm_branch Chunk10.chunk10_wire Chunk11.chunk11_wire))\n" ++
    "      (btMapTerm_branch (btMapTerm_branch Chunk12.chunk12_wire Chunk13.chunk13_wire)\n" ++
    "                        (btMapTerm_branch Chunk14.chunk14_wire Chunk15.chunk15_wire)))"
  let bytesTree :=
    "  checkSubBytes_branch\n" ++
    "    (checkSubBytes_branch\n" ++
    "      (checkSubBytes_branch (checkSubBytes_branch Chunk00.chunk00_bytes Chunk01.chunk01_bytes)\n" ++
    "                            (checkSubBytes_branch Chunk02.chunk02_bytes Chunk03.chunk03_bytes))\n" ++
    "      (checkSubBytes_branch (checkSubBytes_branch Chunk04.chunk04_bytes Chunk05.chunk05_bytes)\n" ++
    "                            (checkSubBytes_branch Chunk06.chunk06_bytes Chunk07.chunk07_bytes)))\n" ++
    "    (checkSubBytes_branch\n" ++
    "      (checkSubBytes_branch (checkSubBytes_branch Chunk08.chunk08_bytes Chunk09.chunk09_bytes)\n" ++
    "                            (checkSubBytes_branch Chunk10.chunk10_bytes Chunk11.chunk11_bytes))\n" ++
    "      (checkSubBytes_branch (checkSubBytes_branch Chunk12.chunk12_bytes Chunk13.chunk13_bytes)\n" ++
    "                            (checkSubBytes_branch Chunk14.chunk14_bytes Chunk15.chunk15_bytes)))"
  -- Keep Table.Cli decoupled from HandshakeModel.
  let cliExpLines : Array String := #["module", ""] ++ chkImports ++ #[
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli",
    "",
    "open DY.Libsignal (HwBytes)",
    "open DY.Libsignal.Composed.Refinement (gamma)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionDefs (S0 myGhost)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag",
    "  (S0Comp S0_eq_comp myGhostComp myGhost_eq_comp)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs",
    "  (CertTable IdTreeSound btMapTerm btMapSkelTerm btMapTerm_branch",
    "   checkSubBytes checkSubBytes_branch idTreeSound_of_cert tableGamma gamma_eq_tableGamma)",
    "",
    "abbrev cliTable : CertTable := CliTable.cliTable",
    "",
    "theorem cliTable_wire :",
    s!"    btMapTerm CliTable.cliIdTree =",
    s!"      btMapSkelTerm {cBt.depth} CliTable.cliIdTree CliTable.cliIdTree :=",
    wireTree,
    "",
    "theorem cliTable_bytes :",
    s!"    checkSubBytes myInterp S0Comp myGhostComp {cBt.depth}",
    "      CliTable.cliIdTree CliTable.cliIdTree = true :=",
    bytesTree,
    "",
    "theorem cliTable_sound :",
    "    IdTreeSound myInterp S0Comp myGhostComp cliTable.depth cliTable.idTree :=",
    "  idTreeSound_of_cert cliTable_wire cliTable_bytes",
    "",
    "noncomputable def cliGamma : DY.Bytes → HwBytes :=",
    "  tableGamma myInterp S0Comp myGhostComp cliTable",
    "",
    "theorem gamma_comp_eq_cliGamma : gamma myInterp S0Comp myGhostComp = cliGamma :=",
    "  gamma_eq_tableGamma cliTable_sound",
    "",
    "theorem gamma_eq_cliGamma : gamma myInterp S0 myGhost = cliGamma := by",
    "  rw [S0_eq_comp, myGhost_eq_comp]",
    "  exact gamma_comp_eq_cliGamma",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.Cli",
    ""
  ]
  writeLeanFile s!"{dir}/Cli.lean" (String.intercalate "\n" cliExpLines.toList)
  IO.println s!"  wrote Cli.lean ({cliExpLines.size} lines)"
  let hsExpLines : Array String := #[
    "module",
    "",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertFalse",
    "public import Symbolic.Proofs.Tests.CliNonvacuity.Table.HsCertTrue",
    "",
    "@[expose] public section",
    "",
    "set_option autoImplicit false",
    "",
    "namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake",
    "",
    "open DY.Libsignal (HwBytes)",
    "open DY.Libsignal.Composed.Refinement (gamma)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Witness (myInterp mySem)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeSteps (mySemComp ghostOf)",
    "open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs (CertTable IdTreeSound)",
    "",
    "abbrev hsTable (withOpk : Bool) : CertTable := HsTables.hsTable withOpk",
    "",
    "theorem hsTable_sound (withOpk : Bool) :",
    "    IdTreeSound myInterp (mySemComp withOpk) (ghostOf withOpk)",
    "      (hsTable withOpk).depth (hsTable withOpk).idTree :=",
    "  match withOpk with",
    "  | false => HsCertFalse.hsFalse_sound",
    "  | true => HsCertTrue.hsTrue_sound",
    "",
    "noncomputable def hsGamma (withOpk : Bool) : DY.Bytes → HwBytes :=",
    "  if withOpk then HsCertTrue.hsTrueGamma else HsCertFalse.hsFalseGamma",
    "",
    "theorem gamma_comp_eq_hsGamma (withOpk : Bool) :",
    "    gamma myInterp (mySemComp withOpk) (ghostOf withOpk) = hsGamma withOpk := by",
    "  cases withOpk",
    "  · exact HsCertFalse.gamma_comp_eq_hsFalseGamma",
    "  · exact HsCertTrue.gamma_comp_eq_hsTrueGamma",
    "",
    "theorem gamma_eq_hsGamma (withOpk : Bool) :",
    "    gamma myInterp (mySem withOpk) (ghostOf withOpk) = hsGamma withOpk := by",
    "  cases withOpk",
    "  · exact HsCertFalse.gamma_eq_hsFalseGamma",
    "  · exact HsCertTrue.gamma_eq_hsTrueGamma",
    "",
    "end Symbolic.Proofs.Tests.CliNonvacuity.Table.Handshake",
    ""
  ]
  writeLeanFile s!"{dir}/Handshake.lean" (String.intercalate "\n" hsExpLines.toList)
  IO.println s!"  wrote Handshake.lean ({hsExpLines.size} lines)"

end GenCliTable

def main (args : List String) : IO Unit := do
  let mode := args.headD "call6"
  let tableDir := "Symbolic/Proofs/Tests/CliNonvacuity/Table"
  match mode with
  | "call6" => GenCliTable.emitCall6 tableDir
  | "full" => GenCliTable.emitFull tableDir
  | other => throw <| IO.userError s!"unknown mode '{other}' (expected 'call6' or 'full')"
