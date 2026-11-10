/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
public import Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
public import Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Comparse.Basic
import Comparse.Formats.Basic
import Comparse.Formats.Derived
import DY.Comparse
import DY.Actions.PersistentLocalState
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign

/-!
# Certified Table-Backed Collision, MAC, and Representation Checkers

Provides `noMemoEntryPairIdBool`, `noMemoCollisionHsTableBool`, `noMemoCollisionTableBool`,
`noMacForgeryTableBool`, `noBobStartCollisionBool_of_table`, `noRecvCollisionBool_of_table`,
`noReselectCollisionBool_of_table`, `recvRep_of_tableBool`, and `preKeyRep_of_tableBool`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers

open scoped DY.Libsignal.Composed

open DY (ExecTrace)
open CryptoProofLib.Refinement (ExternInterpretation)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet
  (TRState TRSignalMsg parseTrSignalMsg trMsgKeys computeMac)
open DY.Libsignal.Composed.Refinement
  (ProtocolSetup OpaqueSymbolSemantics Ghost VisEntry TrialCtx PreKeyFields PreKeyRep
   gamma' gamma spqrHeaded ecKey kyberKey parsePreKeyWire OpkNamed pubBytes secretBytes
   assumedInjective storedStates storedSecrets storedRatchetKeys
   principalTerms prefixTerms plaintextTerms bobTrials whisperTrials trialTerms
   recvRepresentationsOn preKeyRepresentationsOn)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionEval
  (beqBareOptFast beqBareOptFast_true beqBareOptFast_false emptyTrie trieBucket trieInsert
   foldl_memoTrie_mem forceTrieOnce forceTrieOnce_eq withForcedList withForcedList_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.SessionDag
  (stateAnchorPair trStateProxyRoots serialize_localTR_memo suffix_drop_eq firstTwoBytesKey)
open Symbolic.Proofs.Tests.CliNonvacuity.RecvNoCollision
  (noMemoEntryPairCollides noMemoCollisionBool extractMacSeed?
   noUnknownSeedMacGuessBool noTruncatedMacSeedCollisionBool
   noMacForgeryBool noBobStartCollisionBool noRecvCollisionBool noReselectCollisionBool)
open Symbolic.Proofs.Tests.CliNonvacuity.Table.Defs
  (BinTree CertNode CertTable MemoRec IdTreeSound lookupTerm
   seenSound_empty resolveAndCollect resolveAndCollect_sound)

attribute [local instance]
  DY.Libsignal.Composed.instBytesFunctor_symbolic
  DY.Libsignal.Composed.instBytesLength_symbolic
  DY.Libsignal.Composed.instAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instExecTraceTypes_symbolic
  DY.Libsignal.Composed.instBaseAttackerKnowledge_symbolic
  DY.Libsignal.Composed.instHasExecBytes
  DY.Libsignal.Composed.instHasExecEntryT
  DY.Libsignal.Composed.instHasExecEntryTBaseAttackerKnowledge
  DY.Libsignal.Composed.instHasExecTrace
  DY.Libsignal.Composed.instHasSubF
  DY.Libsignal.Composed.instHasSubFAttackerKnowledge
  DY.Libsignal.Composed.instHasSubFLength

unseal DY.Bytes in
def noMemoEntryPairIdBool (pts : List DY.Bytes) (r₁ r₂ : MemoRec) : Bool :=
  Nat.beq r₁.id r₂.id ||
  !(r₁.bytes == r₂.bytes) ||
  (beqBareOptFast 256 r₁.term.val r₂.term.val == some true) ||
  (!(assumedInjective r₁.term) && !(assumedInjective r₂.term)) ||
  (pts.any (fun p => beqBareOptFast 256 r₁.term.val p.val == some true) &&
    (pts.any (fun p => beqBareOptFast 256 r₂.term.val p.val == some true) ||
      !(assumedInjective r₂.term))) ||
  (pts.any (fun p => beqBareOptFast 256 r₂.term.val p.val == some true) &&
    (pts.any (fun p => beqBareOptFast 256 r₁.term.val p.val == some true) ||
      !(assumedInjective r₁.term)))

unseal DY.Bytes in
theorem noMemoEntryPairIdBool_imp (i : ExternInterpretation) (S : OpaqueSymbolSemantics)
    (g : Ghost) {d : Nat} {full : BinTree CertNode} {pts : List DY.Bytes} {r₁ r₂ : MemoRec}
    (hid₁ : lookupTerm d full r₁.id = r₁.term)
    (hid₂ : lookupTerm d full r₂.id = r₂.term)
    (hb : noMemoEntryPairIdBool pts r₁ r₂ = true) :
    noMemoEntryPairCollides pts
      (r₁.term, (gamma' i S g r₁.term).shape, r₁.bytes)
      (r₂.term, (gamma' i S g r₂.term).shape, r₂.bytes) = true := by
  have heq : ∀ {a b : DY.Bytes}, beqBareOptFast 256 a.val b.val = some true → a = b :=
    fun h => Subtype.ext (beqBareOptFast_true 256 _ _ h)
  have hmem : ∀ {a : DY.Bytes},
      (pts.any fun p => beqBareOptFast 256 a.val p.val == some true) = true → a ∈ pts := by
    intro a ha; obtain ⟨p, hp, h⟩ := List.any_eq_true.mp ha
    exact heq (beq_iff_eq.mp h) ▸ hp
  unfold noMemoEntryPairIdBool at hb; unfold noMemoEntryPairCollides
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.contains_eq_mem,
    decide_eq_true_eq] at hb ⊢
  rcases hb with ((((hid | h1) | h2) | h3) | ⟨h4, h5 | h5⟩) | ⟨h6, h7 | h7⟩
  · have hteq : r₁.term = r₂.term := by rw [← hid₁, ← hid₂, Nat.beq_eq.mp hid]
    exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [hteq]))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl h1)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (by rw [heq h2]))))
  · exact Or.inl (Or.inl (Or.inr h3))
  · exact Or.inl (Or.inr ⟨hmem h4, Or.inl (hmem h5)⟩)
  · exact Or.inl (Or.inr ⟨hmem h4, Or.inr h5⟩)
  · exact Or.inr ⟨hmem h6, Or.inl (hmem h7)⟩
  · exact Or.inr ⟨hmem h6, Or.inr h7⟩

def noMemoCollisionHsTableBool (ct : CertTable) (γ : DY.Bytes → HwBytes)
    (sts : List (DY.PersistentLocalState.LocalState TRState))
    (sends secrets pts newTerms : List DY.Bytes) : Bool :=
  let prefProxy := sends ++ sts.flatMap trStateProxyRoots ++ secrets ++ pts
  match resolveAndCollect ct newTerms (emptyTrie 9, []) with
  | none => false
  | some stNew =>
    match resolveAndCollect ct prefProxy stNew with
    | none => false
    | some stAll =>
      withForcedList stNew.2 [] fun newMemos =>
      forceTrieOnce (stAll.2.foldl
        (fun mt r => trieInsert mt (firstTwoBytesKey r.bytes) r) (emptyTrie 8)) fun memoTrie =>
      let sfxs := sts.map fun ls =>
        let (a, s) := stateAnchorPair ls
        γ a ++ γ s
      (newMemos.all fun r₁ =>
        !assumedInjective r₁.term || sfxs.all fun sfx =>
          !(decide (sfx.length ≤ r₁.bytes.length) &&
            (r₁.bytes.drop (r₁.bytes.length - sfx.length) == sfx))) &&
      (newMemos.all fun r₁ =>
        (trieBucket memoTrie (firstTwoBytesKey r₁.bytes)).all fun r₂ =>
          noMemoEntryPairIdBool pts r₁ r₂)

theorem noMemoCollisionBool_of_hsTableBool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ct : CertTable} {γ : DY.Bytes → HwBytes}
    {tr : ExecTrace} {vis : List VisEntry}
    {sts : List (DY.PersistentLocalState.LocalState TRState)}
    {sends secrets visPts newTerms newPts : List DY.Bytes}
    (hc : IdTreeSound interp S g ct.depth ct.idTree)
    (hγ : gamma interp S g = γ)
    (hsts : storedStates r tr = sts)
    (hsends : ((vis.filter (·.kind == .send)).flatMap (·.terms)) = sends)
    (hsec : storedSecrets tr = secrets)
    (hpts : plaintextTerms vis = visPts)
    (hb : noMemoCollisionHsTableBool ct γ sts sends secrets (visPts ++ newPts) newTerms = true) :
    noMemoCollisionBool interp r S g tr vis newTerms newPts = true := by
  unfold noMemoCollisionHsTableBool at hb
  dsimp only at hb
  cases hresNew : resolveAndCollect ct newTerms (emptyTrie 9, []) with
  | none => rw [hresNew] at hb; cases hb
  | some stNew =>
    rw [hresNew] at hb
    dsimp only at hb
    cases hresAll : resolveAndCollect ct
        (sends ++ sts.flatMap trStateProxyRoots ++ secrets ++ (visPts ++ newPts)) stNew with
    | none => rw [hresAll] at hb; cases hb
    | some stAll =>
      rw [hresAll] at hb
      dsimp only at hb
      rw [withForcedList_eq, List.reverse_nil, List.nil_append, forceTrieOnce_eq] at hb
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hAnchor, hallPairs⟩ := hb
      obtain ⟨hsNew, _, hinNew⟩ :=
        resolveAndCollect_sound hc (seenSound_empty interp S g ct.depth ct.idTree 9) hresNew
      obtain ⟨hsAll, hsub, hinAll⟩ := resolveAndCollect_sound hc hsNew hresAll
      set prefProxy := sends ++ sts.flatMap trStateProxyRoots ++ secrets ++ (visPts ++ newPts)
      have hpair : ∀ {r₁ r₂ : MemoRec},
          r₁ ∈ stNew.2 → r₂ ∈ stAll.2 →
          noMemoEntryPairCollides (plaintextTerms vis ++ newPts)
            (r₁.term, (gamma' interp S g r₁.term).shape, r₁.bytes)
            (r₂.term, (gamma' interp S g r₂.term).shape, r₂.bytes) = true := by
        intro r₁ r₂ hr₁ hr₂
        rw [hpts]
        by_cases hbytes : r₁.bytes = r₂.bytes
        · have hkey : firstTwoBytesKey r₁.bytes = firstTwoBytesKey r₂.bytes := by rw [hbytes]
          have hbuck : r₂ ∈ trieBucket
              (stAll.2.foldl (fun mt m => trieInsert mt (firstTwoBytesKey m.bytes) m) (emptyTrie 8))
              (firstTwoBytesKey r₁.bytes) := by
            rw [hkey]
            exact foldl_memoTrie_mem (fun m => firstTwoBytesKey m.bytes) _ (emptyTrie 8) r₂ (Or.inl hr₂)
          obtain ⟨hid₁, _⟩ := hsNew.1 r₁ hr₁
          obtain ⟨hid₂, _⟩ := hsAll.1 r₂ hr₂
          exact noMemoEntryPairIdBool_imp interp S g hid₁ hid₂
            (List.all_eq_true.mp (List.all_eq_true.mp hallPairs r₁ hr₁) r₂ hbuck)
        · unfold noMemoEntryPairCollides
          simp [hbytes]
      unfold noMemoCollisionBool
      refine List.all_eq_true.mpr fun x₁ hx₁_raw => List.all_eq_true.mpr fun x₂ hx₂_raw => ?_
      obtain ⟨t₁, ht₁, hmx₁⟩ := List.mem_flatMap.mp hx₁_raw
      obtain ⟨r₁, hr₁, hrx₁⟩ := hinNew t₁ ht₁ x₁ hmx₁
      subst hrx₁
      rcases List.mem_append.mp hx₂_raw with hx₂_pref | hx₂_new
      · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_pref
        dsimp only [prefixTerms, principalTerms] at ht₂
        rw [hsts, hsends, hsec, hpts] at ht₂
        simp only [List.mem_append, List.mem_map] at ht₂
        rcases ht₂ with ((hsend | ⟨ls, hls, rfl⟩) | hsec') | hpt
        · obtain ⟨r₂, hr₂, rfl⟩ := hinAll t₂ (by simp [prefProxy, hsend]) x₂ hmx₂
          exact hpair hr₁ hr₂
        · rcases serialize_localTR_memo interp S g ls hmx₂ with ⟨p, hp, hmxp⟩ | ⟨hinj₂, hsfx₂⟩
          · obtain ⟨r₂, hr₂, rfl⟩ := hinAll p (by
              dsimp only [prefProxy]; simp only [List.mem_append, List.mem_flatMap]
              exact Or.inl (Or.inl (Or.inr ⟨ls, hls, hp⟩))) x₂ hmxp
            exact hpair hr₁ hr₂
          · cases hinj₁ : assumedInjective r₁.term
            · unfold noMemoEntryPairCollides; simp [hinj₁, hinj₂]
            · have hanc₁ := List.all_eq_true.mp hAnchor r₁ hr₁
              simp only [hinj₁, Bool.not_true, Bool.false_or] at hanc₁
              let sfx := γ (stateAnchorPair ls).1 ++ γ (stateAnchorPair ls).2
              have hsfx_mem : sfx ∈ sts.map (fun ls0 =>
                  let (a, s) := stateAnchorPair ls0
                  γ a ++ γ s) :=
                List.mem_map_of_mem hls
              have hno_sfx := List.all_eq_true.mp hanc₁ sfx hsfx_mem
              have hsfx_eq : sfx = gamma interp S g (stateAnchorPair ls).1 ++
                  gamma interp S g (stateAnchorPair ls).2 := by
                simp [sfx, hγ]
              have hne : r₁.bytes ≠ x₂.2.2 := by
                intro heq
                rw [← hsfx_eq, ← heq] at hsfx₂
                obtain ⟨hlen, hdrop⟩ := suffix_drop_eq hsfx₂
                simp [hlen, hdrop] at hno_sfx
              unfold noMemoEntryPairCollides; simp [hne]
        · obtain ⟨r₂, hr₂, rfl⟩ := hinAll t₂ (by simp [prefProxy, hsec']) x₂ hmx₂
          exact hpair hr₁ hr₂
        · obtain ⟨r₂, hr₂, rfl⟩ := hinAll t₂ (by simp [prefProxy, hpt]) x₂ hmx₂
          exact hpair hr₁ hr₂
      · obtain ⟨t₂, ht₂, hmx₂⟩ := List.mem_flatMap.mp hx₂_new
        obtain ⟨r₂, hr₂, rfl⟩ := hinNew t₂ ht₂ x₂ hmx₂
        exact hpair hr₁ (hsub r₂ hr₂)

def noMemoCollisionTableBool (ct : CertTable) (γ : DY.Bytes → HwBytes)
    (r : ProtocolSetup) (tr : ExecTrace) (vis : List VisEntry)
    (newTerms newPts : List DY.Bytes) : Bool :=
  noMemoCollisionHsTableBool ct γ (storedStates r tr)
    ((vis.filter (·.kind == .send)).flatMap (·.terms))
    (storedSecrets tr) (plaintextTerms vis ++ newPts) newTerms

theorem noMemoCollisionBool_of_tableBool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ct : CertTable} {γ : DY.Bytes → HwBytes}
    {tr : ExecTrace} {vis : List VisEntry} {newTerms newPts : List DY.Bytes}
    (hc : IdTreeSound interp S g ct.depth ct.idTree)
    (hγ : gamma interp S g = γ)
    (hb : noMemoCollisionTableBool ct γ r tr vis newTerms newPts = true) :
    noMemoCollisionBool interp r S g tr vis newTerms newPts = true :=
  noMemoCollisionBool_of_hsTableBool hc hγ rfl rfl rfl rfl hb

unseal DY.Bytes in
def noMacForgeryTableBool (γ : DY.Bytes → HwBytes)
    (honest : List DY.Bytes) (msg : TRSignalMsg) (ctxs : List TrialCtx) : Bool :=
  (ctxs.all fun ctx =>
    match ctx.seed? with
    | none => true
    | some seed =>
      ctx.ownSalts.all fun k =>
        let mk := trMsgKeys k seed
        !(γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) == γ msg.mac) ||
          honest.any fun salt =>
            let hmk := trMsgKeys salt seed
            (γ hmk.cipherKey == γ mk.cipherKey) &&
              (γ hmk.macKey == γ mk.macKey) &&
              (γ hmk.iv == γ mk.iv)) &&
  (let macSeed? := extractMacSeed? msg.mac
   ctxs.all fun ctx =>
    match ctx.seed? with
    | none => true
    | some seed =>
      ctx.ownSalts.all fun k =>
        let mk := trMsgKeys k seed
        !(γ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) == γ msg.mac) ||
          ctxs.all fun ctx₀ =>
            match ctx₀.seed? with
            | none => true
            | some seed₀ =>
              (γ seed == γ seed₀) ||
                (((ctx₀.ownSalts ++ honest).all fun salt₀ =>
                    !(γ (computeMac (trMsgKeys salt₀ seed₀).macKey ctx₀.peerIk ctx₀.myIk msg.wire) ==
                        γ msg.mac)) &&
                  match macSeed? with
                  | none => true
                  | some sMac => beqBareOptFast 256 sMac.val seed₀.val == some false))

unseal DY.Bytes in
theorem noMacForgeryBool_of_tableBool {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx}
    (hγ : gamma interp S g = γ)
    (hb : noMacForgeryTableBool γ honest msg ctxs = true) :
    noMacForgeryBool interp S g honest msg ctxs = true := by
  unfold noMacForgeryBool noUnknownSeedMacGuessBool noTruncatedMacSeedCollisionBool
    noMacForgeryTableBool at *
  rw [hγ]
  simp only [Bool.and_eq_true] at hb ⊢
  refine ⟨hb.1, ?_⟩
  have hb2 := hb.2
  refine List.all_eq_true.mpr fun ctx hctx => ?_
  have hc := List.all_eq_true.mp hb2 ctx hctx
  cases hcs : ctx.seed? with
  | none => rfl
  | some seed =>
    rw [hcs] at hc
    refine List.all_eq_true.mpr fun k hk => ?_
    have hck := List.all_eq_true.mp hc k hk
    simp only [Bool.or_eq_true] at hck ⊢
    rcases hck with hneq | hall0
    · exact Or.inl hneq
    · refine Or.inr (List.all_eq_true.mpr fun ctx₀ hctx₀ => ?_)
      have hc0 := List.all_eq_true.mp hall0 ctx₀ hctx₀
      cases hc0s : ctx₀.seed? with
      | none => rfl
      | some seed₀ =>
        rw [hc0s] at hc0
        simp only [Bool.or_eq_true] at hc0 ⊢
        rcases hc0 with hseq | hand
        · exact Or.inl hseq
        · simp only [Bool.and_eq_true] at hand ⊢
          refine Or.inr ⟨hand.1, ?_⟩
          have hm := hand.2
          cases hex : extractMacSeed? msg.mac with
          | none => rfl
          | some sMac =>
            rw [hex] at hm
            have hne_val := beqBareOptFast_false 256 sMac.val seed₀.val (beq_iff_eq.mp hm)
            have hne : sMac ≠ seed₀ := fun heq => hne_val (congrArg Subtype.val heq)
            simp [hne]

theorem noBobStartCollisionBool_of_table {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ct : CertTable} {γ : DY.Bytes → HwBytes}
    {tr' tr : ExecTrace} {vis' vis : List VisEntry} {salts' salts : List DY.Bytes}
    {p : PreKeyFields} {x : PreKeyRep} {msg : TRSignalMsg}
    (hc : IdTreeSound interp S g ct.depth ct.idTree)
    (hγ : gamma interp S g = γ)
    (htr : tr' = tr) (hvis : vis' = vis) (hsalts : salts' = salts)
    (hp : parseTrSignalMsg x.msg = some msg)
    (hmemo : noMemoCollisionTableBool ct γ r tr vis
      ([x.ek, x.ct, x.msg] ++ (bobTrials r tr p x msg).flatMap (trialTerms salts msg)) [] = true)
    (hmac : noMacForgeryTableBool γ salts msg (bobTrials r tr p x msg) = true) :
    noBobStartCollisionBool interp r S g tr' vis' salts' p x = true := by
  unfold noBobStartCollisionBool
  rw [htr, hvis, hsalts, hp, Bool.and_eq_true]
  exact ⟨noMemoCollisionBool_of_tableBool hc hγ hmemo, noMacForgeryBool_of_tableBool hγ hmac⟩

theorem noRecvCollisionBool_of_table {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {ct : CertTable} {γ : DY.Bytes → HwBytes}
    {tr' tr : ExecTrace} {vis' vis : List VisEntry} {salts' salts : List DY.Bytes}
    {t : DY.Bytes} {msg : TRSignalMsg}
    (hc : IdTreeSound interp S g ct.depth ct.idTree)
    (hγ : gamma interp S g = γ)
    (htr : tr' = tr) (hvis : vis' = vis) (hsalts : salts' = salts)
    (hp : parseTrSignalMsg t = some msg)
    (hmemo : noMemoCollisionTableBool ct γ r tr vis
      (t :: (whisperTrials interp r S g tr msg).flatMap (trialTerms salts msg)) [] = true)
    (hmac : noMacForgeryTableBool γ salts msg (whisperTrials interp r S g tr msg) = true) :
    noRecvCollisionBool interp r S g tr' vis' salts' t = true := by
  unfold noRecvCollisionBool
  rw [htr, hvis, hsalts, hp, Bool.and_eq_true]
  exact ⟨noMemoCollisionBool_of_tableBool hc hγ hmemo, noMacForgeryBool_of_tableBool hγ hmac⟩

unseal DY.Bytes in
def noReselectCollisionTableBool (γ : DY.Bytes → HwBytes) (r : ProtocolSetup)
    (tr : ExecTrace) (msg : TRSignalMsg) : Bool :=
  let rks := storedRatchetKeys r tr msg
  rks.all fun rk =>
    !(γ rk == γ msg.ratchetKey) || (beqBareOptFast 256 rk.val msg.ratchetKey.val == some true)

unseal DY.Bytes in
theorem noReselectCollisionBool_of_table {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes}
    {tr' tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (hγ : gamma interp S g = γ)
    (htr : tr' = tr) (hp : parseTrSignalMsg t = some msg)
    (hb : noReselectCollisionTableBool γ r tr msg = true) :
    noReselectCollisionBool interp r S g tr' t = true := by
  unfold noReselectCollisionBool noReselectCollisionTableBool at *
  rw [htr, hp, hγ]
  refine List.all_eq_true.mpr fun rk hrk => ?_
  have h := List.all_eq_true.mp hb rk hrk
  simp only [Bool.or_eq_true] at h ⊢
  rcases h with hneq | heq
  · exact Or.inr hneq
  · exact Or.inl (beq_iff_eq.mpr
      (Subtype.ext (beqBareOptFast_true 256 rk.val msg.ratchetKey.val (beq_iff_eq.mp heq))))

def recvRepTableBool (γ : DY.Bytes → HwBytes)
    (b : HwBytes) (t : DY.Bytes) (msg : TRSignalMsg) : Bool :=
  (γ t == b) &&
  (γ msg.wire == b.take (b.length - 8)) &&
  (γ msg.mac == b.drop (b.length - 8)) &&
  (!spqrHeaded msg.mac) &&
  match CryptoGames.LibsignalSession.SignalMessage.tryFrom protoSignalCodec b with
  | .error _ => true
  | .ok m =>
    (γ msg.ciphertext == m.ciphertext) &&
    (γ msg.ratchetKey == m.senderRatchetKey.bytes.toList) &&
    (γ msg.pqRatchet == m.pqRatchet) &&
    (msg.counter.toNat == m.counter.toNat) &&
    (msg.version.toNat == m.messageVersion.toNat)

theorem recvRep_of_tableBool {interp : ExternInterpretation}
    {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes} {tr : ExecTrace}
    {b : HwBytes} {t : DY.Bytes} {msg : TRSignalMsg}
    (hγ : gamma interp S g = γ)
    (hak : t.AttackerKnows tr)
    (hp : parseTrSignalMsg t = some msg)
    (hb : recvRepTableBool γ b t msg = true) :
    t ∈ recvRepresentationsOn interp S g tr b := by
  unfold recvRepTableBool at hb
  rw [← hγ] at hb
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hb
  obtain ⟨⟨⟨⟨hγt, hw⟩, hmac⟩, hspqr⟩, hcodec⟩ := hb
  refine ⟨hak, hγt, by simp [hp], ?_⟩
  intro msg' hmsg'
  rw [hp] at hmsg'
  injection hmsg' with hmeq
  subst hmeq
  refine ⟨hw, hmac, hspqr, fun m hm => ?_⟩
  rw [hm] at hcodec
  simp only [Bool.and_eq_true, beq_iff_eq] at hcodec
  exact ⟨hcodec.1.1.1.1, hcodec.1.1.1.2, hcodec.1.1.2, hcodec.1.2, hcodec.2⟩

def preKeyRepTableBool (γ : DY.Bytes → HwBytes)
    (b : HwBytes) (x : PreKeyRep) (msg : TRSignalMsg) : Bool :=
  match parsePreKeyWire b with
  | none => false
  | some p =>
    (p.baseKey.take 33 == ecKey (γ x.ek)) &&
    (p.kyberCiphertext == some (kyberKey (γ x.ct))) &&
    (p.message == γ x.msg) &&
    (γ msg.wire == p.message.take (p.message.length - 8)) &&
    (γ msg.mac == p.message.drop (p.message.length - 8)) &&
    (γ msg.ciphertext == p.inner.ciphertext) &&
    (γ msg.ratchetKey == p.inner.senderRatchetKey.bytes.toList) &&
    (msg.counter.toNat == p.inner.counter.toNat) &&
    (msg.version.toNat == p.inner.messageVersion.toNat) &&
    (γ msg.pqRatchet == p.inner.pqRatchet) &&
    (!spqrHeaded msg.mac)

def preKeyHdrBool (r : ProtocolSetup) (ikAPub : HwBytes) (b : HwBytes) : Bool :=
  match parsePreKeyWire b with
  | none => false
  | some p =>
    (p.version == 4) &&
    (p.signedPreKeyId == r.spkId) &&
    (p.kyberPreKeyId == some r.kpkId) &&
    (p.identityKey.take 33 == ecKey ikAPub) &&
    ((p.preKeyId == some r.opkId && r.withOpk) || p.preKeyId.isNone)

theorem preKeyRep_of_tableBool {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {γ : DY.Bytes → HwBytes}
    {ikAPub : HwBytes} {tr : ExecTrace}
    {b : HwBytes} {x : PreKeyRep} {msg : TRSignalMsg}
    (hγ : gamma interp S g = γ)
    (hikA : pubBytes interp (secretBytes r 0) = ikAPub)
    (hek : x.ek.AttackerKnows tr)
    (hct : x.ct.AttackerKnows tr)
    (hmsg : x.msg.AttackerKnows tr)
    (hp : parseTrSignalMsg x.msg = some msg)
    (hhdr : preKeyHdrBool r ikAPub b = true)
    (hb : preKeyRepTableBool γ b x msg = true) :
    x ∈ preKeyRepresentationsOn interp r S g tr b := by
  unfold preKeyRepTableBool at hb
  unfold preKeyHdrBool at hhdr
  rw [← hγ] at hb
  rw [← hikA] at hhdr
  cases hpw : parsePreKeyWire b with
  | none => rw [hpw] at hb; cases hb
  | some p =>
    rw [hpw] at hb hhdr
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq,
      Option.isNone_iff_eq_none] at hb hhdr
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := hb
    obtain ⟨⟨⟨⟨hv, hspk⟩, hkpk⟩, hidA⟩, hopk⟩ := hhdr
    have hopkNamed : ∃ used, OpkNamed r b used := by
      rcases hopk with hopkT | hopkF
      · exact ⟨true, p, hpw, hopkT⟩
      · exact ⟨false, p, hpw, hopkF⟩
    exact ⟨hek, hct, hmsg, ⟨p, hpw, h1, h2, h3, hv, hspk, hkpk, hidA, hopkNamed⟩,
      ⟨p, hpw, ⟨msg, hp, h4, h5, h11, h6, h7, h10, h8, h9⟩⟩⟩

end Symbolic.Proofs.Tests.CliNonvacuity.Table.Checkers
