/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Witnesses.CliShape
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
abbrev DY.Libsignal.Composed.Refinement.spqrIdx := DY.Libsignal.Composed.Refinement.preKeySpqrIndex
namespace DY.Libsignal.Composed.Refinement
open DY DY.Libsignal DY.Libsignal.Composed
open DY.Libsignal.PQXDH (HandshakeKeys errToOption pqxdhKdf pqxdhIkm agree serializedIk)
open DY.Libsignal.TripleRatchet (TRSignalMsg RecvChain createChain parseTrSignalMsg consumeMessageKey skippedSeeds trMsgKeys computeMac)
def bobKeys (r : Records) (p : PreKeyFields) (x : PreKeyRep) : Option HandshakeKeys := do
  let opk ← match p.preKeyId with | none => some none | some id => if r.withOpk && id == r.opkId then some (some (setupSecret r 6)) else none
  let pqsk := setupSecret r 4; let ss := (errToOption (PQKem.kemDecap pqsk x.ct)).getD (PQKem.kemRejKey pqsk x.ct);
  pure (pqxdhKdf (pqxdhIkm (agree (setupPublic r 0) (setupSecret r 2)) (agree x.ek (setupSecret r 1)) (agree x.ek (setupSecret r 2)) (opk.map (agree x.ek ·)) ss))
def bobChain (r : Records) (keys : HandshakeKeys) (msg : TRSignalMsg) : RecvChain := { ratchetKey := msg.ratchetKey, chainKey := (createChain keys.rk msg.ratchetKey (setupSecret r 2)).2, index := 0, rIdx := 2 }
def bobTerms (r : Records) (salts : List DY.Bytes) (p : PreKeyFields) (x : PreKeyRep) : List DY.Bytes :=
  match bobKeys r p x, parseTrSignalMsg x.msg with
  | some keys, some msg =>
    let c := bobChain r keys msg;
    [keys.rk, keys.ck, keys.pqr, c.chainKey] ++ match consumeMessageKey c msg.counter with | none => [] | some (seed, c') => [c'.chainKey] ++ skippedSeeds c msg.counter ++ salts.flatMap fun salt => let mk := trMsgKeys salt seed; [mk.cipherKey, mk.macKey, mk.iv, computeMac mk.macKey (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2)) msg.wire] ++ (DY.SymEnc.symDec mk.cipherKey mk.iv msg.ciphertext).toList
  | _, _ => []
end DY.Libsignal.Composed.Refinement
namespace Symbolic.BugInjection.Proofs.Common443.CompExcuse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH (HandshakeKeys errToOption pqxdhKdf pqxdhIkm agree serializedIk)
open DY.Libsignal.TripleRatchet (TRSignalMsg RecvChain createChain parseTrSignalMsg consumeMessageKey skippedSeeds trMsgKeys computeMac)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
def BobOwnKeyMacGuess (interpretation : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (known : DY.Bytes → Prop) (ms : List Move) (p : PreKeyFields) (x : PreKeyRep) : Prop := ∃ keys msg seed c' own st', bobKeys r p x = some keys ∧ parseTrSignalMsg x.msg = some msg ∧ consumeMessageKey (bobChain r keys msg) msg.counter = some (seed, c') ∧ ¬ known seed ∧ DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A) msg.pqRatchet (spqrIdx p) = some (st', own) ∧
    let mk := trMsgKeys own seed;
    gamma interpretation S g (computeMac mk.macKey (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2)) msg.wire) = gamma interpretation S g msg.mac ∧ ∀ salt ∈ honestSalts r ms, (gamma interpretation S g (trMsgKeys salt seed).cipherKey, gamma interpretation S g (trMsgKeys salt seed).macKey, gamma interpretation S g (trMsgKeys salt seed).iv) ≠ (gamma interpretation S g mk.cipherKey, gamma interpretation S g mk.macKey, gamma interpretation S g mk.iv)
def bobTrialsRaw (r : Records) (p : PreKeyFields) (x : PreKeyRep) (msg : TRSignalMsg) : List TrialCtx :=
  match bobKeys r p x with
  | none => []
  | some keys =>
    let c := bobChain r keys msg; let peerIk := serializedIk (setupPublic r 0); let myIk := serializedIk (setupPublic r 2)
    match consumeMessageKey c msg.counter with
    | none =>
      [{ peerIk, myIk, extra := [keys.rk, keys.ck, keys.pqr, c.chainKey], ownSalts := [], seed? := none }]
    | some (seed, c') =>
      let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
        msg.pqRatchet (spqrIdx p)).map (·.2)).toList
      [{ peerIk, myIk, extra := [keys.rk, keys.ck, keys.pqr, c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
         ownSalts := own, seed? := some seed }]
theorem bobTrials_eq_nil_or_raw (r : Records) (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep) (msg : TRSignalMsg) :
    bobTrials r tr p x msg = [] ∨ bobTrials r tr p x msg = bobTrialsRaw r p x msg := by
  unfold bobTrials bobTrialsRaw bobKeys bobChain
    ProtocolSetup.opkSecTerm ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm
    ProtocolSetup.spkSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.pqskSecTerm
  cases p.preKeyId with
  | none =>
    dsimp only
    split <;> [exact .inl rfl; exact .inr rfl]
  | some id =>
    by_cases h : (r.withOpk && id == r.opkId) = true
    · simp only [h, ↓reduceIte]
      split <;> [exact .inl rfl; exact .inr rfl]
    · simp [h]
theorem bobTrialsRaw_flatMap_trialTerms_eq_bobTerms (r : Records) (salts : List DY.Bytes) (p : PreKeyFields) (x : PreKeyRep) {msg : TRSignalMsg} (hmsg : parseTrSignalMsg x.msg = some msg) : (bobTrialsRaw r p x msg).flatMap (trialTerms salts msg) = bobTerms r salts p x := by
  unfold bobTrialsRaw bobTerms; rw [hmsg]
  cases bobKeys r p x with
  | none => rfl
  | some keys =>
    dsimp only
    rcases consumeMessageKey (bobChain r keys msg) msg.counter with _ | ⟨seed, c'⟩
    · simp [trialTerms]
    · simp [trialTerms]
theorem bobTrials_flatMap_trialTerms_sub_bobTerms (r : Records) (tr : ExecTrace) (salts : List DY.Bytes) (p : PreKeyFields) (x : PreKeyRep) {msg : TRSignalMsg} (hmsg : parseTrSignalMsg x.msg = some msg) : (bobTrials r tr p x msg).flatMap (trialTerms salts msg) ⊆ bobTerms r salts p x := by
  rcases bobTrials_eq_nil_or_raw r tr p x msg with h | h <;> rw [h]
  · simp
  · rw [bobTrialsRaw_flatMap_trialTerms_eq_bobTerms r salts p x hmsg]
theorem memoCollisionOn_mono_new {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {tr : ExecTrace} {vis : List VisEntry} {new₁ new₂ pts : List DY.Bytes} (hsub : new₁ ⊆ new₂) (hm : MemoCollisionOn i r S g known tr vis new₁ pts) : MemoCollisionOn i r S g known tr vis new₂ pts := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hsh, hinj, hpt₁, hpt₂, hb⟩ := hm
  have hfm : ∀ {z}, z ∈ new₁.flatMap (fun t => (gamma' i S g t).memo) → z ∈ new₂.flatMap (fun t => (gamma' i S g t).memo) := by
    intro z hz; obtain ⟨t, ht, hzt⟩ := List.mem_flatMap.mp hz; exact List.mem_flatMap.mpr ⟨t, hsub ht, hzt⟩
  refine ⟨x₁, hfm hx₁, x₂, ?_, hsh, hinj, hpt₁, hpt₂, hb⟩
  rcases List.mem_append.mp hx₂ with hp | hn
  · exact List.mem_append_left _ hp
  · exact List.mem_append_right _ (hfm hn)
theorem memoCollisionOn_bobTrials_to_bobTerms {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {tr tr' : ExecTrace} {vis : List VisEntry} {salts : List DY.Bytes} {p : PreKeyFields} {x : PreKeyRep} {msg : TRSignalMsg} (hmsg : parseTrSignalMsg x.msg = some msg) (hm : MemoCollisionOn i r S g known tr vis ([x.ek, x.ct, x.msg] ++ (bobTrials r tr' p x msg).flatMap (trialTerms salts msg)) []) : MemoCollisionOn i r S g known tr vis ([x.ek, x.ct, x.msg] ++ bobTerms r salts p x) [] := by
  refine memoCollisionOn_mono_new ?_ hm
  exact List.append_subset.mpr ⟨List.subset_append_left _ _, List.Subset.trans (bobTrials_flatMap_trialTerms_sub_bobTerms r tr' salts p x hmsg) (List.subset_append_right _ _)⟩
theorem bobOwnKeyMacGuess_of_ownSaltMacCollision_bobTrials {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {ms : List Move} {tr : ExecTrace} {p : PreKeyFields} {x : PreKeyRep} {msg : TRSignalMsg} (hmsg : parseTrSignalMsg x.msg = some msg) (hosm : OwnSaltMacCollision i S g known (honestSalts r ms) msg (bobTrials r tr p x msg)) : BobOwnKeyMacGuess i r S g known ms p x := by
  have hosm' : ∃ ctx ∈ bobTrials r tr p x msg, ∃ seed, ctx.seed? = some seed ∧ ∃ own ∈ ctx.ownSalts,
      let mk := trMsgKeys own seed
      gamma i S g (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) = gamma i S g msg.mac ∧
      ((¬ known seed ∧ ∀ salt ∈ honestSalts r ms,
        (gamma i S g (trMsgKeys salt seed).cipherKey, gamma i S g (trMsgKeys salt seed).macKey, gamma i S g (trMsgKeys salt seed).iv) ≠
        (gamma i S g mk.cipherKey, gamma i S g mk.macKey, gamma i S g mk.iv)) ∨
       (∃ ctx₀ ∈ bobTrials r tr p x msg, ∃ seed₀, ctx₀.seed? = some seed₀ ∧ gamma i S g seed ≠ gamma i S g seed₀)) := by
    rcases hosm with ⟨ctx, hctx, seed, hseed, own, hown, hmac, hnk, hne_all⟩ | ⟨ctx, hctx, seed, hseed, own, hown, hmac, ctx₀, hctx₀, seed₀, hseed₀, hne_seed, _⟩
    · exact ⟨ctx, hctx, seed, hseed, own, hown, hmac, Or.inl ⟨hnk, hne_all⟩⟩
    · exact ⟨ctx, hctx, seed, hseed, own, hown, hmac, Or.inr ⟨ctx₀, hctx₀, seed₀, hseed₀, hne_seed⟩⟩
  rcases hosm' with ⟨ctx, hctx, seed, hseed, own, hown, hmac, hbranch⟩
  rcases bobTrials_eq_nil_or_raw r tr p x msg with hnil | hraw
  · rw [hnil] at hctx; cases hctx
  · rw [hraw] at hctx hbranch; unfold bobTrialsRaw at hctx hbranch
    rcases hkeys : bobKeys r p x with _ | keys
    · rw [hkeys] at hctx; cases hctx
    · rw [hkeys] at hctx; dsimp only at hctx
      rcases hcons : consumeMessageKey (bobChain r keys msg) msg.counter with _ | ⟨seed₁, c'⟩
      · rw [hcons] at hctx; simp only [List.mem_singleton] at hctx; subst hctx; cases hseed
      · rw [hcons] at hctx; simp only [List.mem_singleton] at hctx; subst hctx; dsimp only at hseed hown hmac
        injection hseed with hseed_eq; subst hseed_eq
        rcases hrecv : DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr TripleRatchet.spqrB2A)
            msg.pqRatchet (spqrIdx p) with _ | ⟨st', own'⟩
        · rw [hrecv] at hown; cases hown
        · rw [hrecv] at hown; simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hown; subst hown
          rcases hbranch with ⟨hnk, hne_all⟩ | ⟨ctx₀, hctx₀, seed₀, hseed₀, hne_seed⟩
          · exact ⟨keys, msg, seed₁, c', own, st', hkeys, hmsg, hcons, hnk, hrecv, hmac, hne_all⟩
          · rw [hkeys] at hctx₀; dsimp only at hctx₀; rw [hcons] at hctx₀; simp only [List.mem_singleton] at hctx₀; subst hctx₀; dsimp only at hseed₀
            injection hseed₀ with hseed₀_eq; subst hseed₀_eq
            exact False.elim (hne_seed rfl)
@[simp] theorem kemDecap_kemEncap_fst (sk e : DY.Bytes) : PQKem.kemDecap sk (PQKem.kemEncap (PQKem.kemPk sk) e).1 =
      some (PQKem.kemEncap (PQKem.kemPk sk) e).2 := by
  simp only [PQKem.kemDecap, PQKem.CanPQKem.kemDecap, PQKem.kemEncap, PQKem.CanPQKem.kemEncap, PQKem.kemPk, PQKem.CanPQKem.kemPk, BytesView.view_pack, ↓reduceIte]
@[simp] theorem x25519Key_torsionVariant_of_ne (k : DY.Bytes) (v : Fin 4) (t : Fin 8) (hne : ¬ (v = 0 ∧ t = 0)) :
    X25519.x25519Key (X25519.x25519TorsionVariant k v t) = X25519.x25519Key k := by
  simp only [X25519.x25519TorsionVariant, hne, ↓reduceIte, X25519.x25519Key, X25519.normalizeX25519Key, BytesView.view_pack]
@[simp] theorem agree_torsionVariant_of_ne (pk sk : DY.Bytes) (v : Fin 4) (t : Fin 8) (hne : ¬ (v = 0 ∧ t = 0)) : DY.Libsignal.PQXDH.agree (X25519.x25519TorsionVariant pk v t) sk =
      DY.Libsignal.PQXDH.agree pk sk := by
  simp only [DY.Libsignal.PQXDH.agree, x25519Key_torsionVariant_of_ne pk v t hne]
theorem gamma_concat (i : ExternInterpretation) (S : Sem) (g : Ghost) (a b : DY.Bytes) : gamma i S g (DY.Concat.concat a b) = gamma i S g a ++ gamma i S g b := by
  unfold gamma gamma'
  show ((({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).val = _
  rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl
theorem not_bobStartCollision_of_parts {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} {x : PreKeyRep} (hnmc : ¬ MemoCollisionOn i r S g (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) ([x.ek, x.ct, x.msg] ++ bobTerms r (honestSalts r ms) p x) []) (hnbomg : ¬ BobOwnKeyMacGuess i r S g (fun u => u.AttackerKnows (runTraceMoves r ms)) ms p x) : ¬ BobStartCollision i r S g ms p x := by
  unfold BobStartCollision BobSessionStartCollidesOrImplicitRejects; dsimp only
  intro hrest
  rcases hmsg : DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg with _ | msg
  · rw [hmsg] at hrest
    have hbt : bobTerms r (honestSalts r ms) p x = [] := by unfold bobTerms; rw [hmsg]; cases bobKeys r p x <;> rfl
    rw [hbt, List.append_nil] at hnmc; exact hnmc hrest
  · rw [hmsg] at hrest
    rcases hrest with hmc | hosm
    · exact hnmc (memoCollisionOn_bobTrials_to_bobTerms hmsg hmc)
    · exact hnbomg (bobOwnKeyMacGuess_of_ownSaltMacCollision_bobTrials hmsg hosm)
theorem gamma'_randTerm (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (hsz : sz ≠ 0) : gamma' i S g (randTerm ts sz) = { bytes := g.σ ts sz, shape := randTerm ts sz, memo := [(randTerm ts sz, randTerm ts sz, g.σ ts sz)] } := by
  unfold gamma' randTerm
  show ((({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)) = _
  rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]; simp only [gRandom, concretizeRandom, node, List.flatMap_nil, hsz, ↓reduceIte]
end Symbolic.BugInjection.Proofs.Common443.CompExcuse
