/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
public import Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Initiate.PostTrace
import Symbolic.Proofs.Swarm.CREF.SendWire.WhisperPureA
import Symbolic.Proofs.Swarm.CREF.TR.G1.SpqrRkForgedMac
import Symbolic.Proofs.Swarm.CREF.TR.SendRetCoinsCliPureB

/-!
# Certified Indexed Node Table Engine

Defines `BinTree`, `NodeSkel`, `CertNode`, and `CertTable` for dense `id`-indexed symbolic
`DY.Bytes` tables with concrete `HwBytes` and `hasMemo` flags, proves `IdTreeSound` and
`gamma_eq_tableGamma`, and provides `collectFromId` and `resolveAndCollect` for subgraph memo
collection.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs

open scoped DY.Libsignal.Composed

open ByteSpecs (hmacWith)
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Refinement
  (x25519PublicKeySymbol x25519AgreementSymbol
   aesCbcEncryptSymbol sha256CompressFunction torsionShift)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost
   clamp variantBytes ofByteArray spqrKeyBytes trWireBytes
   node opaqueNode spqrKeyNode
   concretizeRandom concretizeLit concretizeConcat concretizeDhPk concretizeDh
   concretizeKdf concretizeSym concretizeTrunc concretizeVariant
   concretizeKemPk concretizeKemEncap concretizeKemSS concretizeVk concretizeSign
   concretizeSpqrInit concretizeSpqrSendState concretizeSpqrSendKey concretizeSpqrSendMsg
   concretizeSpqrRecvState concretizeSpqrRecvKey concretizeSpqrChainKey concretizeTrWire
   concretizeAll gamma' gamma)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (beqBareOptFast beqBareOptFast_true
   Trie emptyTrie trieBucket trieInsert trieToList
   trieBucket_mem_toList mem_trieToList_insert
   forceTrieOnce forceTrieOnce_eq hashTermNat)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.MkTerm
  (tRnd tLit tCat tDhPk tDh tKdf tSym tTr8 tVar
   tKemPk tKemEnc tKemSS tVk tSig
   tSInit tSSendSt tSSendK tSSendM tSRecvSt tSRecvK tSChain tTrW)

/-! ## `BinTree`, `NodeSkel`, `CertNode`, and Soundness -/

inductive BinTree (α : Type) where
  | empty : BinTree α
  | leaf : α → BinTree α
  | branch : BinTree α → BinTree α → BinTree α

def btGet {α : Type} (d : Nat) (tr : BinTree α) (k : Nat) : Option α :=
  match tr with
  | .empty => none
  | .leaf v => some v
  | .branch lo hi =>
    match d with
    | 0 => none
    | d' + 1 =>
      if Nat.beq (k % 2) 0 then btGet d' lo (k / 2) else btGet d' hi (k / 2)

def btToList {α : Type} : BinTree α → List α
  | .empty => []
  | .leaf v => [v]
  | .branch lo hi => btToList lo ++ btToList hi

theorem btGet_mem {α : Type} {d : Nat} {tr : BinTree α} {k : Nat} {v : α}
    (h : btGet d tr k = some v) : v ∈ btToList tr := by
  induction tr generalizing d k with
  | empty => unfold btGet at h; cases h
  | leaf a => unfold btGet at h; injection h with h; subst h; exact List.mem_singleton.mpr rfl
  | branch lo hi ihlo ihhi =>
    unfold btGet at h
    cases d with
    | zero => cases h
    | succ d' =>
      dsimp only at h
      split at h
      · exact List.mem_append_left _ (ihlo h)
      · exact List.mem_append_right _ (ihhi h)

inductive NodeSkel where
  | rnd (ts sz : Nat)
  | lit (bs : HwBytes)
  | cat (lhs rhs : Nat)
  | dhPk (sk : Nat)
  | dh (pk sk : Nat)
  | kdf (salt ikm : Nat)
  | sym (key iv msg : Nat)
  | tr8 (input : Nat)
  | var (key : Nat) (torsion : Fin 8) (variation : Fin 4)
  | kemPk (sk : Nat)
  | kemEnc (pk entropy : Nat)
  | kemSS (pk entropy : Nat)
  | vk (sk : Nat)
  | sig (sk nonce msg : Nat)
  | sInit (authKey params : Nat)
  | sSendSt (st coins : Nat)
  | sSendK (st coins : Nat)
  | sSendM (st coins : Nat)
  | sRecvSt (st msg : Nat)
  | sRecvK (st msg : Nat)
  | sChain (authKey params idx : Nat)
  | trW (ver : UInt8) (rk : Nat) (cnt pcnt : UInt32) (ct pq : Nat)
      (ev : DY.TrWire.EncodingVariation)

def skelChildren : NodeSkel → List Nat
  | .rnd _ _ | .lit _ => []
  | .cat l r => [l, r]
  | .dhPk s => [s]
  | .dh p s => [p, s]
  | .kdf a b => [a, b]
  | .sym k iv m => [k, iv, m]
  | .tr8 a => [a]
  | .var k _ _ => [k]
  | .kemPk s => [s]
  | .kemEnc p e => [p, e]
  | .kemSS p e => [p, e]
  | .vk s => [s]
  | .sig s n m => [s, n, m]
  | .sInit a p => [a, p]
  | .sSendSt a b => [a, b]
  | .sSendK a b => [a, b]
  | .sSendM a b => [a, b]
  | .sRecvSt a b => [a, b]
  | .sRecvK a b => [a, b]
  | .sChain a p idx => [a, p, idx]
  | .trW _ rk _ _ ct pq _ => [rk, ct, pq]

def skelTerm (tOf : Nat → DY.Bytes) : NodeSkel → DY.Bytes
  | .rnd ts sz => tRnd ts sz
  | .lit bs => tLit bs
  | .cat l r => tCat (tOf l) (tOf r)
  | .dhPk s => tDhPk (tOf s)
  | .dh p s => tDh (tOf p) (tOf s)
  | .kdf a b => tKdf (tOf a) (tOf b)
  | .sym k iv m => tSym (tOf k) (tOf iv) (tOf m)
  | .tr8 a => tTr8 (tOf a)
  | .var k t v => tVar (tOf k) t v
  | .kemPk s => tKemPk (tOf s)
  | .kemEnc p e => tKemEnc (tOf p) (tOf e)
  | .kemSS p e => tKemSS (tOf p) (tOf e)
  | .vk s => tVk (tOf s)
  | .sig s n m => tSig (tOf s) (tOf n) (tOf m)
  | .sInit a p => tSInit (tOf a) (tOf p)
  | .sSendSt a b => tSSendSt (tOf a) (tOf b)
  | .sSendK a b => tSSendK (tOf a) (tOf b)
  | .sSendM a b => tSSendM (tOf a) (tOf b)
  | .sRecvSt a b => tSRecvSt (tOf a) (tOf b)
  | .sRecvK a b => tSRecvK (tOf a) (tOf b)
  | .sChain a p idx => tSChain (tOf a) (tOf p) (tOf idx)
  | .trW ver rk cnt pcnt ct pq ev => tTrW ver (tOf rk) cnt pcnt (tOf ct) (tOf pq) ev

def skelEval (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (selfTerm : DY.Bytes) (bOf : Nat → HwBytes) : NodeSkel → HwBytes × Bool
  | .rnd ts sz => if sz = 0 then ([], false) else (g.σ ts sz, true)
  | .lit bs => (bs, true)
  | .cat l r => (bOf l ++ bOf r, true)
  | .dhPk s => ((i x25519PublicKeySymbol [clamp (bOf s)]).getD [], true)
  | .dh p s => ((i x25519AgreementSymbol [clamp (bOf s), bOf p]).getD [], true)
  | .kdf a b => (hmacWith (sha256CompressFunction i) (bOf a) (bOf b), true)
  | .sym k iv m => ((i aesCbcEncryptSymbol [bOf m, bOf k, (bOf iv).take 16]).getD [], true)
  | .tr8 a => ((bOf a).take 8, true)
  | .var k t v => (variantBytes (torsionShift i (bOf k) t) v, true)
  | .kemPk s => (S.kemPk (bOf s), false)
  | .kemEnc p e =>
    if (bOf e).length = 32 then (((i kyberEncapsSymbol [bOf p, bOf e]).getD []).take 1568, true)
    else ([], false)
  | .kemSS p e =>
    if (bOf e).length = 32 then (((i kyberEncapsSymbol [bOf p, bOf e]).getD []).drop 1568, true)
    else (S.kemDecap (bOf p) (bOf e), false)
  | .vk s => (S.vk (bOf s), false)
  | .sig s n m => (S.sign (bOf s) (bOf n) (bOf m), false)
  | .sInit a p => (S.init (bOf a) (bOf p), false)
  | .sSendSt a b => (S.sendState (bOf a) (bOf b), false)
  | .sSendK a b => (spqrKeyBytes (S.sendKey (bOf a) (bOf b)), false)
  | .sSendM a b => (S.sendMsg (bOf a) (bOf b), false)
  | .sRecvSt a b => (S.recvState (bOf a) (bOf b), false)
  | .sRecvK a b => (spqrKeyBytes (S.recvKey (bOf a) (bOf b)), false)
  | .sChain a p idx => (spqrKeyBytes (S.chainKey (bOf a) (bOf p) (bOf idx)), false)
  | .trW ver rk cnt pcnt ct pq ev =>
    (trWireBytes (g.addr selfTerm) ev
      { version := ver.toNat, ratchetKey := bOf rk, counter := cnt.toNat,
        previousCounter := pcnt.toNat, ciphertext := bOf ct } (bOf pq), true)

section Certifier
unseal DY.Bytes

private theorem ofByteArray_litOf_aux (bs : HwBytes) :
    ofByteArray ⟨(bs.map UInt8.ofBitVec).toArray⟩ = bs := by
  simp only [ofByteArray, List.map_map]
  induction bs with
  | nil => rfl
  | cons b rest ih =>
    simp [Function.comp, ih]

local macro "skstep" fn:term "," ct:term : tactic =>
  `(tactic| (
    intro hchild
    simp only [skelTerm, skelEval, skelChildren, gamma',
      tRnd, tLit, tCat, tDhPk, tDh, tKdf, tSym, tTr8, tVar,
      tKemPk, tKemEnc, tKemSS, tVk, tSig,
      tSInit, tSSendSt, tSSendK, tSSendM, tSRecvSt, tSRecvK, tSChain, tTrW,
      DY.Libsignal.Composed.Refinement.litOf] at hchild ⊢
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hchild
    rw [DY.Bytes.rec_eq $fn $ct _]
    simp only [concretizeRandom, concretizeLit, concretizeConcat, concretizeDhPk, concretizeDh,
      concretizeKdf, concretizeSym, concretizeTrunc, concretizeVariant,
      concretizeKemPk, concretizeKemEncap, concretizeKemSS, concretizeVk, concretizeSign,
      concretizeSpqrInit, concretizeSpqrSendState, concretizeSpqrSendKey, concretizeSpqrSendMsg,
      concretizeSpqrRecvState, concretizeSpqrRecvKey, concretizeSpqrChainKey, concretizeTrWire,
      node, opaqueNode, spqrKeyNode]
    try simp only [hchild]
    try rw [ofByteArray_litOf_aux]
    try split
    all_goals simp_all [List.flatMap_cons, List.flatMap_nil, List.append_assoc]))

theorem skelEval_spec (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (tOf : Nat → DY.Bytes) (bOf : Nat → HwBytes) (sk : NodeSkel)
    (hchild : ∀ c ∈ skelChildren sk, bOf c = (gamma' i S g (tOf c)).bytes) :
    (skelEval i S g (skelTerm tOf sk) bOf sk).1 = (gamma' i S g (skelTerm tOf sk)).bytes ∧
    (gamma' i S g (skelTerm tOf sk)).memo =
      (if (skelEval i S g (skelTerm tOf sk) bOf sk).2 then
        [(skelTerm tOf sk, (gamma' i S g (skelTerm tOf sk)).shape,
          (skelEval i S g (skelTerm tOf sk) bOf sk).1)]
       else []) ++
      (skelChildren sk).flatMap (fun c => (gamma' i S g (tOf c)).memo) := by
  revert hchild
  cases sk with
  | rnd ts sz => skstep (concretizeRandom g), (concretizeAll i S g)
  | lit bs => skstep concretizeLit, (concretizeAll i S g)
  | cat l r => skstep concretizeConcat, (concretizeAll i S g)
  | dhPk s => skstep (concretizeDhPk i), (concretizeAll i S g)
  | dh p s => skstep (concretizeDh i), (concretizeAll i S g)
  | kdf a b => skstep (concretizeKdf i), (concretizeAll i S g)
  | sym k iv m => skstep (concretizeSym i), (concretizeAll i S g)
  | tr8 a => skstep concretizeTrunc, (concretizeAll i S g)
  | var k t v => skstep (concretizeVariant i), (concretizeAll i S g)
  | kemPk s => skstep (concretizeKemPk S), (concretizeAll i S g)
  | kemEnc p e => skstep (concretizeKemEncap i), (concretizeAll i S g)
  | kemSS p e => skstep (concretizeKemSS i S), (concretizeAll i S g)
  | vk s => skstep (concretizeVk S), (concretizeAll i S g)
  | sig s n m => skstep (concretizeSign S), (concretizeAll i S g)
  | sInit a p => skstep (concretizeSpqrInit S), (concretizeAll i S g)
  | sSendSt a b => skstep (concretizeSpqrSendState S), (concretizeAll i S g)
  | sSendK a b => skstep (concretizeSpqrSendKey S), (concretizeAll i S g)
  | sSendM a b => skstep (concretizeSpqrSendMsg S), (concretizeAll i S g)
  | sRecvSt a b => skstep (concretizeSpqrRecvState S), (concretizeAll i S g)
  | sRecvK a b => skstep (concretizeSpqrRecvKey S), (concretizeAll i S g)
  | sChain a p idx => skstep (concretizeSpqrChainKey S), (concretizeAll i S g)
  | trW ver rk cnt pcnt ct pq ev => skstep (concretizeTrWire g), (concretizeAll i S g)

structure CertNode where
  rank : Nat
  term : DY.Bytes
  skel : NodeSkel
  bytes : HwBytes
  hasMemo : Bool

def lookupTerm (d : Nat) (full : BinTree CertNode) (k : Nat) : DY.Bytes :=
  match btGet d full k with
  | some n => n.term
  | none => tRnd 0 0

def lookupBytes (d : Nat) (full : BinTree CertNode) (k : Nat) : HwBytes :=
  match btGet d full k with
  | some n => n.bytes
  | none => []

def btMapTerm : BinTree CertNode → BinTree DY.Bytes
  | .empty => .empty
  | .leaf n => .leaf n.term
  | .branch lo hi => .branch (btMapTerm lo) (btMapTerm hi)

def btMapSkelTerm (d : Nat) (full : BinTree CertNode) : BinTree CertNode → BinTree DY.Bytes
  | .empty => .empty
  | .leaf n => .leaf (skelTerm (lookupTerm d full) n.skel)
  | .branch lo hi => .branch (btMapSkelTerm d full lo) (btMapSkelTerm d full hi)

theorem btMapTerm_branch {d : Nat} {full lo hi : BinTree CertNode}
    (hlo : btMapTerm lo = btMapSkelTerm d full lo)
    (hhi : btMapTerm hi = btMapSkelTerm d full hi) :
    btMapTerm (.branch lo hi) = btMapSkelTerm d full (.branch lo hi) :=
  congrArg₂ BinTree.branch hlo hhi

theorem btMapTerm_eq_imp (d : Nat) (full : BinTree CertNode) :
    ∀ (sub : BinTree CertNode),
      btMapTerm sub = btMapSkelTerm d full sub →
      ∀ n ∈ btToList sub, n.term = skelTerm (lookupTerm d full) n.skel
  | .empty, _, _, hn => nomatch hn
  | .leaf n0, h, n, hn => by
    rw [List.mem_singleton.mp hn]
    injection h
  | .branch lo hi, h, n, hn => by
    injection h with hlo hhi
    rcases List.mem_append.mp hn with h1 | h2
    · exact btMapTerm_eq_imp d full lo hlo n h1
    · exact btMapTerm_eq_imp d full hi hhi n h2

def checkNodeBytes (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode) (n : CertNode) : Bool :=
  (skelChildren n.skel).all (fun c =>
    match btGet d full c with
    | some nc => Nat.blt nc.rank n.rank
    | none => false) &&
  let r := skelEval i S g n.term (lookupBytes d full) n.skel
  (n.bytes == r.1) && (n.hasMemo == r.2)

def checkSubBytes (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode) : BinTree CertNode → Bool
  | .empty => true
  | .leaf n => checkNodeBytes i S g d full n
  | .branch lo hi => checkSubBytes i S g d full lo && checkSubBytes i S g d full hi

theorem checkSubBytes_branch {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {d : Nat} {full lo hi : BinTree CertNode}
    (hlo : checkSubBytes i S g d full lo = true)
    (hhi : checkSubBytes i S g d full hi = true) :
    checkSubBytes i S g d full (.branch lo hi) = true := by
  simp [checkSubBytes, hlo, hhi]

theorem checkSubBytes_all (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode) :
    ∀ (sub : BinTree CertNode), checkSubBytes i S g d full sub = true →
      ∀ n ∈ btToList sub, checkNodeBytes i S g d full n = true
  | .empty, _, _, hn => nomatch hn
  | .leaf _, h, n, hn => by rw [List.mem_singleton.mp hn]; exact h
  | .branch lo hi, h, n, hn => by
    simp only [checkSubBytes, Bool.and_eq_true] at h
    rcases List.mem_append.mp hn with h1 | h2
    · exact checkSubBytes_all i S g d full lo h.1 n h1
    · exact checkSubBytes_all i S g d full hi h.2 n h2

def IdTreeSound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode) : Prop :=
  ∀ n ∈ btToList full,
    (∀ c ∈ skelChildren n.skel, ∃ nc, btGet d full c = some nc ∧ nc.rank < n.rank) ∧
    n.bytes = (gamma' i S g n.term).bytes ∧
    (gamma' i S g n.term).memo =
      (if n.hasMemo then [(n.term, (gamma' i S g n.term).shape, n.bytes)] else []) ++
      (skelChildren n.skel).flatMap (fun c => (gamma' i S g (lookupTerm d full c)).memo)

private theorem idTreeSound_rec (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode)
    (hw : ∀ n ∈ btToList full, n.term = skelTerm (lookupTerm d full) n.skel)
    (hc : ∀ n ∈ btToList full, checkNodeBytes i S g d full n = true)
    (rk : Nat) :
    ∀ n ∈ btToList full, n.rank = rk →
      (∀ c ∈ skelChildren n.skel, ∃ nc, btGet d full c = some nc ∧ nc.rank < n.rank) ∧
      n.bytes = (gamma' i S g n.term).bytes ∧
      (gamma' i S g n.term).memo =
        (if n.hasMemo then [(n.term, (gamma' i S g n.term).shape, n.bytes)] else []) ++
        (skelChildren n.skel).flatMap (fun c => (gamma' i S g (lookupTerm d full c)).memo) :=
  Nat.strongRecOn rk fun rk ih n hn hrk => by
    have hcn := hc n hn
    unfold checkNodeBytes at hcn
    simp only [Bool.and_eq_true, beq_iff_eq] at hcn
    obtain ⟨hkids, hbytes, hmemo⟩ := hcn
    have hkids' : ∀ c ∈ skelChildren n.skel,
        ∃ nc, btGet d full c = some nc ∧ nc.rank < n.rank := by
      intro c hc_in
      have hck := List.all_eq_true.mp hkids c hc_in
      cases hgc : btGet d full c with
      | none => rw [hgc] at hck; cases hck
      | some nc =>
        rw [hgc] at hck
        exact ⟨nc, rfl, Nat.blt_eq.mp hck⟩
    have hchild : ∀ c ∈ skelChildren n.skel,
        lookupBytes d full c = (gamma' i S g (lookupTerm d full c)).bytes := by
      intro c hc_in
      obtain ⟨nc, hgc, hlt⟩ := hkids' c hc_in
      unfold lookupBytes lookupTerm
      rw [hgc]
      exact (ih nc.rank (hrk ▸ hlt) nc (btGet_mem hgc) rfl).2.1
    have htw := hw n hn
    obtain ⟨hbs, hms⟩ := skelEval_spec i S g (lookupTerm d full) (lookupBytes d full) n.skel hchild
    refine ⟨hkids', ?_, ?_⟩
    · rw [hbytes, htw, hbs]
    · rw [hmemo, hbytes]
      conv_lhs => rw [htw]
      rw [hms, ← htw]

theorem idTreeSound_of_cert {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {d : Nat} {full : BinTree CertNode}
    (hw : btMapTerm full = btMapSkelTerm d full full)
    (hc : checkSubBytes i S g d full full = true) :
    IdTreeSound i S g d full :=
  fun n hn =>
    idTreeSound_rec i S g d full
      (btMapTerm_eq_imp d full full hw)
      (checkSubBytes_all i S g d full full hc)
      n.rank n hn rfl

/-! ## `CertTable`, `tableLookup`, `tableGamma`, and `collectFromId` -/

structure CertTable where
  depth : Nat
  idTree : BinTree CertNode
  hashTrie : Trie Nat

def hashBucketLookup (d : Nat) (idTree : BinTree CertNode) (b : DY.Bytes) :
    List Nat → Option (Nat × CertNode)
  | [] => none
  | id :: rest =>
    match btGet d idTree id with
    | some n =>
      if beqBareOptFast 256 b.val n.term.val == some true then some (id, n)
      else hashBucketLookup d idTree b rest
    | none => hashBucketLookup d idTree b rest

def tableLookup (ct : CertTable) (b : DY.Bytes) : Option (Nat × CertNode) :=
  hashBucketLookup ct.depth ct.idTree b (trieBucket ct.hashTrie (hashTermNat 4 b))

theorem tableLookup_spec {ct : CertTable} {b : DY.Bytes} {id : Nat} {n : CertNode}
    (h : tableLookup ct b = some (id, n)) :
    btGet ct.depth ct.idTree id = some n ∧ b = n.term := by
  unfold tableLookup at h
  generalize trieBucket ct.hashTrie (hashTermNat 4 b) = bs at h
  induction bs with
  | nil => cases h
  | cons id0 rest ih =>
    dsimp only [hashBucketLookup] at h
    cases hg : btGet ct.depth ct.idTree id0 with
    | none => rw [hg] at h; exact ih h
    | some n0 =>
      rw [hg] at h
      dsimp only at h
      split at h
      · next hcond =>
        injection h with hp
        injection hp with hid hn
        subst hid; subst hn
        exact ⟨hg, Subtype.ext (beqBareOptFast_true 256 b.val n0.term.val (beq_iff_eq.mp hcond))⟩
      · exact ih h

def tableGamma (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (ct : CertTable) (b : DY.Bytes) : HwBytes :=
  match tableLookup ct b with
  | some (_, n) => n.bytes
  | none => gamma i S g b

theorem gamma_eq_tableGamma {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ct : CertTable} (hs : IdTreeSound i S g ct.depth ct.idTree) :
    gamma i S g = tableGamma i S g ct := by
  funext b
  unfold tableGamma
  cases hl : tableLookup ct b with
  | none => rfl
  | some p =>
    obtain ⟨hg, rfl⟩ := tableLookup_spec hl
    exact ((hs p.2 (btGet_mem hg)).2.1).symm

structure MemoRec where
  id : Nat
  term : DY.Bytes
  bytes : HwBytes

def collectFromId (d : Nat) (full : BinTree CertNode) :
    Nat → Trie Nat × List MemoRec → Nat → Trie Nat × List MemoRec
  | 0, st, _ => st
  | fuel + 1, (seen, acc), id =>
    if (trieBucket seen id).any (Nat.beq id) then (seen, acc)
    else
      match btGet d full id with
      | none => (seen, acc)
      | some n =>
        let st1 := (skelChildren n.skel).foldl (collectFromId d full fuel) (seen, acc)
        if (skelChildren n.skel).all (fun c => (trieBucket st1.1 c).any (Nat.beq c)) then
          forceTrieOnce (trieInsert st1.1 id id) fun seen' =>
            let acc' := if n.hasMemo then ⟨id, n.term, n.bytes⟩ :: st1.2 else st1.2
            (seen', acc')
        else st1

def SeenSound (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (d : Nat) (full : BinTree CertNode) (seen : Trie Nat) (acc : List MemoRec) : Prop :=
  (∀ r ∈ acc,
    lookupTerm d full r.id = r.term ∧
    ∃ t0, (r.term, (gamma' i S g r.term).shape, r.bytes) ∈ (gamma' i S g t0).memo) ∧
  (∀ k ∈ trieToList seen,
    ∀ m ∈ (gamma' i S g (lookupTerm d full k)).memo,
      ∃ r ∈ acc, (r.term, (gamma' i S g r.term).shape, r.bytes) = m)

theorem seenSound_empty (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) (d : Nat) (full : BinTree CertNode) (depth : Nat) :
    SeenSound i S g d full (emptyTrie depth) [] := by
  refine ⟨(fun _ h => nomatch h), fun k hk => ?_⟩
  exfalso
  induction depth with
  | zero => cases hk
  | succ n ih =>
    simp only [emptyTrie, trieToList, List.mem_append, or_self] at hk
    exact ih hk

private theorem collectFromId_step {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {d : Nat} {full : BinTree CertNode} {fuel : Nat}
    (ih : ∀ st nid, SeenSound i S g d full st.1 st.2 →
      let st' := collectFromId d full fuel st nid
      SeenSound i S g d full st'.1 st'.2 ∧
      (∀ k ∈ trieToList st.1, k ∈ trieToList st'.1) ∧
      (∀ r ∈ st.2, r ∈ st'.2)) :
    ∀ (cs : List Nat) (st : Trie Nat × List MemoRec),
      SeenSound i S g d full st.1 st.2 →
      let st' := cs.foldl (collectFromId d full fuel) st
      SeenSound i S g d full st'.1 st'.2 ∧
      (∀ k ∈ trieToList st.1, k ∈ trieToList st'.1) ∧
      (∀ r ∈ st.2, r ∈ st'.2)
  | [], _, hst => ⟨hst, fun _ h => h, fun _ h => h⟩
  | c :: cs, st, hst => by
    dsimp only [List.foldl_cons]
    obtain ⟨hs1, hkm1, hrm1⟩ := ih st c hst
    obtain ⟨hs2, hkm2, hrm2⟩ := collectFromId_step ih cs _ hs1
    exact ⟨hs2, fun k hk => hkm2 k (hkm1 k hk), fun r hr => hrm2 r (hrm1 r hr)⟩

theorem collectFromId_sound {i : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {d : Nat} {full : BinTree CertNode} (hfull : IdTreeSound i S g d full) :
    ∀ (fuel : Nat) (st : Trie Nat × List MemoRec) (nid : Nat),
      SeenSound i S g d full st.1 st.2 →
      let st' := collectFromId d full fuel st nid
      SeenSound i S g d full st'.1 st'.2 ∧
      (∀ k ∈ trieToList st.1, k ∈ trieToList st'.1) ∧
      (∀ r ∈ st.2, r ∈ st'.2)
  | 0, _, _, hst => ⟨hst, fun _ h => h, fun _ h => h⟩
  | fuel + 1, (seen, acc), nid, hst => by
    dsimp only [collectFromId]
    split
    · exact ⟨hst, fun _ h => h, fun _ h => h⟩
    · cases hg : btGet d full nid with
      | none => exact ⟨hst, fun _ h => h, fun _ h => h⟩
      | some n =>
        dsimp only
        obtain ⟨hs1, hkm1, hrm1⟩ :=
          collectFromId_step (collectFromId_sound hfull fuel) (skelChildren n.skel) (seen, acc) hst
        set st1 := (skelChildren n.skel).foldl (collectFromId d full fuel) (seen, acc)
        split
        · next hall =>
          rw [forceTrieOnce_eq]
          dsimp only
          have hlt_id : lookupTerm d full nid = n.term := by unfold lookupTerm; rw [hg]
          obtain ⟨_, _, hnmemo⟩ := hfull n (btGet_mem hg)
          have hrm_acc' : ∀ r ∈ st1.2,
              r ∈ (if n.hasMemo then ⟨nid, n.term, n.bytes⟩ :: st1.2 else st1.2) := by
            intro r hr; split <;> simp [hr]
          refine ⟨⟨?_, ?_⟩,
            fun k hk => (mem_trieToList_insert st1.1 nid nid k).mpr (Or.inr (hkm1 k hk)),
            fun r hr => hrm_acc' r (hrm1 r hr)⟩
          · intro r hr
            cases hhm : n.hasMemo with
            | false =>
              rw [hhm] at hr; simp only [Bool.false_eq_true, ↓reduceIte] at hr
              exact hs1.1 r hr
            | true =>
              rw [hhm] at hr; simp only [↓reduceIte, List.mem_cons] at hr
              rcases hr with rfl | hr'
              · refine ⟨hlt_id, n.term, ?_⟩
                rw [hnmemo, hhm]; simp
              · exact hs1.1 r hr'
          · intro k hk m hm
            rcases (mem_trieToList_insert st1.1 nid nid k).mp hk with hknid | hk'
            · subst k
              rw [hlt_id, hnmemo, List.mem_append] at hm
              rcases hm with hself | hkids
              · cases hhm : n.hasMemo with
                | false => rw [hhm] at hself; simp at hself
                | true =>
                  rw [hhm] at hself
                  simp only [↓reduceIte, List.mem_singleton] at hself
                  subst hself
                  exact ⟨⟨nid, n.term, n.bytes⟩, by simp, rfl⟩
              · obtain ⟨c, hc_in, hmc⟩ := List.mem_flatMap.mp hkids
                have hc_any := List.all_eq_true.mp hall c hc_in
                obtain ⟨c', hc_buck, hc_eq⟩ := List.any_eq_true.mp hc_any
                rw [← Nat.beq_eq.mp hc_eq] at hc_buck
                obtain ⟨r, hr, hrm⟩ := hs1.2 c (trieBucket_mem_toList st1.1 c hc_buck) m hmc
                exact ⟨r, hrm_acc' r hr, hrm⟩
            · obtain ⟨r, hr, hrm⟩ := hs1.2 k hk' m hm
              exact ⟨r, hrm_acc' r hr, hrm⟩
        · exact ⟨hs1, hkm1, hrm1⟩

def resolveAndCollect (ct : CertTable) :
    List DY.Bytes → Trie Nat × List MemoRec → Option (Trie Nat × List MemoRec)
  | [], st => some st
  | b :: bs, st =>
    match tableLookup ct b with
    | none => none
    | some (id, _) =>
      let st' := collectFromId ct.depth ct.idTree 128 st id
      if (trieBucket st'.1 id).any (Nat.beq id) then
        resolveAndCollect ct bs st'
      else none

theorem resolveAndCollect_sound {i : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {ct : CertTable} (hfull : IdTreeSound i S g ct.depth ct.idTree) :
    ∀ {bs : List DY.Bytes} {st st' : Trie Nat × List MemoRec},
      SeenSound i S g ct.depth ct.idTree st.1 st.2 →
      resolveAndCollect ct bs st = some st' →
      SeenSound i S g ct.depth ct.idTree st'.1 st'.2 ∧
      (∀ r ∈ st.2, r ∈ st'.2) ∧
      (∀ b ∈ bs, ∀ m ∈ (gamma' i S g b).memo,
        ∃ r ∈ st'.2, (r.term, (gamma' i S g r.term).shape, r.bytes) = m)
  | [], _, _, hst, hres => by
    injection hres with heq; subst heq
    exact ⟨hst, fun _ h => h, fun _ h => nomatch h⟩
  | b :: bs, st, st', hst, hres => by
    dsimp only [resolveAndCollect] at hres
    cases hl : tableLookup ct b with
    | none => rw [hl] at hres; cases hres
    | some p =>
      rw [hl] at hres
      dsimp only at hres
      set st1 := collectFromId ct.depth ct.idTree 128 st p.1
      split at hres
      · next hin =>
        obtain ⟨hs1, _, hrm1⟩ := collectFromId_sound hfull 128 st p.1 hst
        obtain ⟨hs2, hrm2, hall2⟩ := resolveAndCollect_sound hfull hs1 hres
        refine ⟨hs2, fun r hr => hrm2 r (hrm1 r hr), fun b0 hb0 m hm => ?_⟩
        rcases List.mem_cons.mp hb0 with rfl | hb0'
        · obtain ⟨hg, rfl⟩ := tableLookup_spec hl
          have hlt : lookupTerm ct.depth ct.idTree p.1 = p.2.term := by
            unfold lookupTerm; rw [hg]
          obtain ⟨k', hk_buck, hk_eq⟩ := List.any_eq_true.mp hin
          rw [← Nat.beq_eq.mp hk_eq] at hk_buck
          have hm' : m ∈ (gamma' i S g (lookupTerm ct.depth ct.idTree p.1)).memo := by
            rw [hlt]; exact hm
          obtain ⟨r, hr, hrm⟩ := hs1.2 p.1 (trieBucket_mem_toList st1.1 p.1 hk_buck) m hm'
          exact ⟨r, hrm2 r hr, hrm⟩
        · exact hall2 b0 hb0' m hm
      · cases hres

end Certifier

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
