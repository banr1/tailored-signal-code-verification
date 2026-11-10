/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap
public import Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner
public import Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse (getMessageSentAt_eq_at? x25519Key_dhPk_eq)
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeEval (zeroKey_ne_spqrSendKey)
theorem dh_dhPk_comm (a b : DY.Bytes) : DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) b = DY.DiffieHellman.dh (DY.DiffieHellman.dhPk b) a := DY.DiffieHellman.dh_commutes a b
theorem agree_dhPk_comm (a b : DY.Bytes) : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk a) b = DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk b) a := by unfold DY.Libsignal.PQXDH.agree; simp only [x25519Key_dhPk_eq]; exact dh_dhPk_comm a b
theorem x25519Key_torsionVariant_aliceOut_ek (tr₁ : ExecTrace) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (v : Fin 4) (t : Fin 8) : DY.X25519.x25519Key (DY.X25519.x25519TorsionVariant (iniAliceOut tr₁ ikA ikB spk pqpk opk).ek v t) = (iniAliceOut tr₁ ikA ikB spk pqpk opk).ek := by
  have hek : (iniAliceOut tr₁ ikA ikB spk pqpk opk).ek = DY.DiffieHellman.dhPk (randTerm tr₁.length 32) := rfl
  rw [hek]
  simp only [DY.X25519.x25519TorsionVariant, x25519Key_dhPk_eq]; split_ifs
  · exact x25519Key_dhPk_eq _
  · unfold DY.X25519.x25519Key DY.X25519.normalizeX25519Key; rw [DY.BytesView.view_pack]
theorem x25519Key_setupPublic_4 {r : Records} (hNe : r.alice ≠ r.bob) : DY.X25519.x25519Key (setupPublic r 4) = setupPublic r 4 := by rw [setupPublic_4 hNe]; unfold DY.X25519.x25519Key; exact x25519Key_dhPk_eq _
theorem bobKeys_x0_eq_some {r : Records} {p : PreKeyFields} {x₀ : PreKeyRep} {tr₁ : ExecTrace} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hek : DY.X25519.x25519Key x₀.ek = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek) (hct : x₀.ct = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct) : bobKeys r p x₀ = some (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys := by
  have hct_eq : x₀.ct =
      (DY.PQKem.kemEncap (DY.PQKem.kemPk (setupSecret r 4)) (randTerm (tr₁.length + 1) 32)).1 := by
    rw [hct]; change (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₁.length + 1) 32)).1 = _; rw [setupPublic_6 hNe, setupSecret_4 hNe]
  have hdecap : DY.PQKem.kemDecap (setupSecret r 4) x₀.ct =
      some (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₁.length + 1) 32)).2 := by
    rw [hct_eq, kemDecap_kemEncap_fst, setupPublic_6 hNe, setupSecret_4 hNe]
  have hdh1 : DY.Libsignal.PQXDH.agree (setupPublic r 0) (setupSecret r 2) =
      DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0) := by
    rw [setupPublic_0 hNe, setupSecret_0 hNe, setupPublic_4 hNe, setupSecret_2 hNe]; exact agree_dhPk_comm _ _
  have hdh2 : DY.Libsignal.PQXDH.agree x₀.ek (setupSecret r 1) =
      DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₁.length 32) := by
    unfold DY.Libsignal.PQXDH.agree; unfold DY.X25519.x25519Key at hek; rw [hek]; change DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) (setupSecret r 1) = _; rw [setupPublic_2 hNe, setupSecret_1 hNe, x25519Key_dhPk_eq]; exact dh_dhPk_comm _ _
  have hdh3 : DY.Libsignal.PQXDH.agree x₀.ek (setupSecret r 2) =
      DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₁.length 32) := by
    unfold DY.Libsignal.PQXDH.agree; unfold DY.X25519.x25519Key at hek; rw [hek]; change DY.DiffieHellman.dh (DY.DiffieHellman.dhPk (randTerm tr₁.length 32)) (setupSecret r 2) = _; rw [setupPublic_4 hNe, setupSecret_2 hNe, x25519Key_dhPk_eq]; exact dh_dhPk_comm _ _
  unfold bobKeys; dsimp only; rw [hopk, hdecap]; simp only [bind, Option.bind, pure, DY.Libsignal.PQXDH.errToOption, Option.getD_some, Option.map_none, hdh1, hdh2, hdh3]; rfl
private theorem bobChain_chainKey_eq_cks_aux {r : Records} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} (hNe : r.alice ≠ r.bob) (hspk : o.spk = setupPublic r 4) : (bobChain r o.keys (encParsedMsg tr₂ (iniAliceStartState tr₁ b o) cl pq)).chainKey = (iniAliceStartState tr₁ b o).cks := by
  change (DY.Libsignal.TripleRatchet.createChain o.keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)).2 = (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).2; unfold DY.Libsignal.TripleRatchet.createChain DY.X25519.agree
  have hagree : DY.DiffieHellman.dh
      (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)))
      (setupSecret r 2) =
      DY.DiffieHellman.dh (DY.X25519.x25519Key o.spk) (randTerm (tr₁.length + 2) 32) := by
    rw [hspk, x25519Key_setupPublic_4 hNe, setupPublic_4 hNe, setupSecret_2 hNe]; unfold DY.X25519.x25519Key; rw [x25519Key_dhPk_eq]; exact dh_dhPk_comm _ _
  rw [hagree]
private theorem getMessageSentAt_of_ge_length (tr : ExecTrace) {i : Nat} (hi : tr.length ≤ i) : tr.getMessageSentAt i = none := by rw [getMessageSentAt_eq_at?, Symbolic.Swarm.CREF.at?_ge_length tr hi]
theorem honestKeysFrom_movesFrom_invisibleNoEffect : ∀ {ms : List Move} {tr : ExecTrace}, MovesFrom InvisibleNoEffect tr ms → honestKeysFrom tr ms = []
  | [], _, _ => rfl
  | m :: ms, tr, ⟨hm, hms⟩ => by
    cases m with
    | encrypt me sIdx cl pq wr =>
      rcases XplSteps.xpl_encrypt_next (me := me) (stateIdx := sIdx) (coinsLen := cl)
          (pqIdx := pq) (w := wr) tr with h | h
      · rw [honestKeysFrom, honestKeysFrom_movesFrom_invisibleNoEffect hms, h,
          getMessageSentAt_of_ge_length tr (i := tr.length + 2) (by omega)]
        rfl
      · exfalso; obtain ⟨⟨m0, n0⟩, rest, hx⟩ := XplSteps.xpl_newRandoms_cons h; have hv := hm.1; rw [xpl_vis_eq, List.append_eq_nil_iff] at hv; have hown := hv.1; simp [xpl_ownVis, encVis, hx, encDraws] at hown
    | _ =>
      simp only [honestKeysFrom, List.nil_append]; exact honestKeysFrom_movesFrom_invisibleNoEffect hms
theorem honestKeysFrom_append : ∀ (ms₁ ms₂ : List Move) (tr : ExecTrace), honestKeysFrom tr (ms₁ ++ ms₂) = honestKeysFrom tr ms₁ ++ honestKeysFrom (runMoves ms₁ tr).1 ms₂
  | [], ms₂, tr => by simp [honestKeysFrom, runMoves]
  | m :: ms₁, ms₂, tr => by
    simp only [List.cons_append, honestKeysFrom, runMoves, honestKeysFrom_append ms₁ ms₂ (m.next tr), List.append_assoc]
theorem spqrSend_spqrInit_key (a p coins : DY.Bytes) : (DY.Spqr.spqrSend (DY.Spqr.spqrInit a p) coins).2.1 = DY.Spqr.spqrChainKey a p (DY.Spqr.spqrIdx 1) := by simp [DY.Spqr.spqrSend, DY.Spqr.spqrInit, DY.BytesView.view_pack]
theorem encSalt_iniAliceStartState_eq_spqrChainKey (tr₁ tr₂ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : encSalt tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) = DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) := by rw [encSalt_self]; exact spqrSend_spqrInit_key o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (randTerm (tr₂.length + 1) cl)
theorem encNextTr_getMessageSentAt_salt (tr₂ : ExecTrace) (me : Participant) (sIdx : Nat) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : (encNextTr tr₂ me sIdx stA cl pq).getMessageSentAt (tr₂.length + 2) = some (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1 := by
  have hle : encPreSaltTr tr₂ stA cl ≤ encNextTr tr₂ me sIdx stA cl pq := (by unfold encNextTr; dsimp only; exact Trace.le_trans _ _ _ (Trace.le_trans _ _ _ (Trace.le_trans _ _ _ (Trace.append_le _ _) (Trace.append_le _ _)) (Trace.append_le _ _)) (Trace.append_le _ _)); have h0 := encPreSaltTr_getMessageSentAt_self tr₂ stA cl; rw [getMessageSentAt_eq_at?] at h0
  have hnet0 : NetMsgAt (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.1
      (tr₂.length + 2) (encPreSaltTr tr₂ stA cl) := by
    unfold NetMsgAt
    rcases hat : ((encPreSaltTr tr₂ stA cl).at? (tr₂.length + 2) : Option NetEntry) with _ | m
    · rw [hat] at h0; cases h0
    · rcases m with ⟨m⟩
      rw [hat] at h0; simp only [Option.some.injEq] at h0; subst h0; rfl
  have hnet := NetMsgAt.mono hle hnet0; rw [getMessageSentAt_eq_at?]; unfold NetMsgAt at hnet; rw [hnet]
theorem honestSalts_split_eq {r : Records} {pre mid post : List Move} {a b : Participant} {idS regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {me : Participant} {sIdx cl pq : Nat} {wr : Option (Nat × Nat)} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid ((Move.aliceStart a b idS regB hb shown).next tr₁)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a b idS regB hb shown).next tr₁) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt me sIdx cl pq wr).next tr₂) post) (henc : (Move.encrypt me sIdx cl pq wr).next tr₂ = encNextTr tr₂ me sIdx (iniAliceStartState tr₁ b o) cl pq) : honestSalts r (pre ++ Move.aliceStart a b idS regB hb shown :: mid ++ Move.encrypt me sIdx cl pq wr :: post) = [DY.Spqr.zeroKey, DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)] := by unfold honestSalts; congr 1; rw [List.append_assoc, honestKeysFrom_append pre, honestKeysFrom_movesFrom_invisibleNoEffect hpre, List.nil_append, ← htr₁]; simp only [List.cons_append, honestKeysFrom, List.nil_append]; rw [honestKeysFrom_append mid, honestKeysFrom_movesFrom_invisibleNoEffect hmid, List.nil_append, ← htr₂]; simp only [honestKeysFrom]; rw [honestKeysFrom_movesFrom_invisibleNoEffect hpost, List.append_nil, henc, encNextTr_getMessageSentAt_salt]; change [(DY.Spqr.spqrSend (DY.Spqr.spqrInit o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B) (randTerm (tr₂.length + 1) cl)).2.1] = _; rw [spqrSend_spqrInit_key]
theorem spqrChainKey_mem_honestSalts_of_split {r : Records} {pre mid post : List Move} {a b : Participant} {idS regB : Nat} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown : Nat} {me : Participant} {sIdx cl pq : Nat} {wr : Option (Nat × Nat)} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (htr₁ : tr₁ = (runMoves pre (setupTrace r)).1) (htr₂ : tr₂ = (runMoves mid ((Move.aliceStart a b idS regB hb shown).next tr₁)).1) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart a b idS regB hb shown).next tr₁) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt me sIdx cl pq wr).next tr₂) post) (henc : (Move.encrypt me sIdx cl pq wr).next tr₂ = encNextTr tr₂ me sIdx (iniAliceStartState tr₁ b o) cl pq) : DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∈ honestSalts r (pre ++ Move.aliceStart a b idS regB hb shown :: mid ++ Move.encrypt me sIdx cl pq wr :: post) := by rw [honestSalts_split_eq htr₁ htr₂ hpre hmid hpost henc]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
theorem not_bobOwnKeyMacGuess_x0 {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {known : DY.Bytes → Prop} {ms : List Move} {p : PreKeyFields} {x₀ : PreKeyRep} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} (hkeys : bobKeys r p x₀ = some o.keys) (hidx : spqrIdx p = 0 ∨ spqrIdx p = 1) (hsalt_mem : DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∈ honestSalts r ms) : ¬ BobOwnKeyMacGuess i r S g known ms p x₀ := by
  refine CompExcuse.not_bobOwnKeyMacGuess_of_idx_zero_or_one hkeys ?_
  rcases hidx with h0 | h1
  · exact Or.inl h0
  · exact Or.inr ⟨h1, hsalt_mem⟩
def encMsgKeys (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.MessageKeys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr₂ stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
def encCiphertext (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Bytes :=
  let keys := encMsgKeys tr₂ stA cl pq;
  DY.SymEnc.symEnc keys.cipherKey keys.iv (randTerm tr₂.length 32)
def encPqMsg (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : DY.Bytes := (DY.Spqr.spqrSend stA.spqr (randTerm (tr₂.length + 1) cl)).2.2
private theorem bobTerms_encSalt_eq_aliceTerms_aux {r : Records} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} (hNe : r.alice ≠ r.bob) (hikA : o.ikA = DY.DiffieHellman.dhPk (setupSecret r 0)) (hikB : o.ikB = setupPublic r 2) (hspk : o.spk = setupPublic r 4) : let stA := iniAliceStartState tr₁ r.bob o;
    let msg := encParsedMsg tr₂ stA cl pq; let seed := (DY.Libsignal.TripleRatchet.kdfCk (bobChain r o.keys msg).chainKey).2; let salt := encSalt tr₂ stA cl pq; let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
    keys = encMsgKeys tr₂ stA cl pq ∧ DY.Libsignal.TripleRatchet.computeMac keys.macKey (DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)) (DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)) msg.wire = encMac tr₂ stA cl pq ∧
    (DY.SymEnc.symDec keys.cipherKey keys.iv msg.ciphertext).toList = [randTerm tr₂.length 32] := by
  intro stA msg seed salt keys; have hck : (bobChain r o.keys msg).chainKey = stA.cks := bobChain_chainKey_eq_cks_aux hNe hspk
  have hkeys : keys = encMsgKeys tr₂ stA cl pq := by dsimp only [keys, seed, encMsgKeys]; rw [hck]
  have hik0 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = stA.myIk := (by change DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = DY.Libsignal.PQXDH.serializedIk o.ikA; rw [hikA, setupPublic_0 hNe, setupSecret_0 hNe]); have hik2 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = stA.peerIk := (by change DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = DY.Libsignal.PQXDH.serializedIk o.ikB; rw [hikB]); refine ⟨hkeys, ?_, ?_⟩
  · rw [hkeys, hik0, hik2]; rfl
  · rw [hkeys]; change (DY.SymEnc.symDec (encMsgKeys tr₂ stA cl pq).cipherKey (encMsgKeys tr₂ stA cl pq).iv (DY.SymEnc.symEnc (encMsgKeys tr₂ stA cl pq).cipherKey (encMsgKeys tr₂ stA cl pq).iv (randTerm tr₂.length 32))).toList = [randTerm tr₂.length 32]; simp [DY.SymEnc.symDec, DY.SymEnc.CanSymEnc.symDec, DY.SymEnc.symEnc, DY.BytesView.view_pack]
theorem symDec_zeroKey_encCiphertext_eq_none (tr₁ tr₂ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : let stA := iniAliceStartState tr₁ b o;
    let pq := tr₂.length + 2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed;
    DY.SymEnc.symDec zkeys.cipherKey zkeys.iv (encCiphertext tr₂ stA cl pq) = none := by
  intro stA pq seed zkeys
  have hne_salt : DY.Spqr.zeroKey ≠ encSalt tr₂ stA cl pq := by
    rw [encSalt_self]
    exact zeroKey_ne_spqrSendKey stA.spqr (randTerm (tr₂.length + 1) cl)
  have hne_ck : zkeys.cipherKey ≠ (encMsgKeys tr₂ stA cl pq).cipherKey := (by intro heq; have h1 := (CompExcuse.hmac_inj heq).1; have h2 := (CompExcuse.hmac_inj h1).1; exact hne_salt h2); unfold encCiphertext; simp only [DY.SymEnc.symDec, DY.SymEnc.CanSymEnc.symDec, DY.SymEnc.symEnc, DY.BytesView.view_pack, ite_eq_right_iff]; rintro ⟨hck_eq, _⟩; exact absurd hck_eq hne_ck
private theorem mem_bobTerms_x0_iff_aux {r : Records} {p : PreKeyFields} {x₀ : PreKeyRep} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} (hNe : r.alice ≠ r.bob) (hikA : o.ikA = DY.DiffieHellman.dhPk (setupSecret r 0)) (hikB : o.ikB = setupPublic r 2) (hspk : o.spk = setupPublic r 4) (hkeys : bobKeys r p x₀ = some o.keys) (hmsg : x₀.msg = encOut tr₂ (iniAliceStartState tr₁ r.bob o) cl (tr₂.length + 2)) (u : DY.Bytes) : let stA := iniAliceStartState tr₁ r.bob o;
    let pq := tr₂.length + 2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed; let akeys := encMsgKeys tr₂ stA cl pq;
    u ∈ bobTerms r [DY.Spqr.zeroKey, DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)] p x₀ → u ∈ [o.keys.rk, o.keys.ck, o.keys.pqr, stA.cks, (encSt tr₂ stA cl).cks, akeys.cipherKey, akeys.macKey, akeys.iv, encMac tr₂ stA cl pq, randTerm tr₂.length 32, zkeys.cipherKey, zkeys.macKey, zkeys.iv, DY.Libsignal.TripleRatchet.computeMac zkeys.macKey stA.myIk stA.peerIk
             (encWire tr₂ stA cl pq)] := by
  intro stA pq seed zkeys akeys hu
  have hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg x₀.msg =
      some (encParsedMsg tr₂ stA cl pq) := by
    rw [hmsg]; exact parseTrSignalMsg_encOut tr₂ stA cl pq
  have hck : (bobChain r o.keys (encParsedMsg tr₂ stA cl pq)).chainKey = stA.cks := bobChain_chainKey_eq_cks_aux hNe hspk
  have hcons :
      DY.Libsignal.TripleRatchet.consumeMessageKey (bobChain r o.keys (encParsedMsg tr₂ stA cl pq)) (encParsedMsg tr₂ stA cl pq).counter = some (seed,
            { bobChain r o.keys (encParsedMsg tr₂ stA cl pq) with
              chainKey := (encSt tr₂ stA cl).cks
              index := 1 }) := by
    change DY.Libsignal.TripleRatchet.consumeMessageKey (bobChain r o.keys (encParsedMsg tr₂ stA cl pq)) 0 = _
    have hcons0 : ∀ c : DY.Libsignal.TripleRatchet.RecvChain, c.index = 0 → DY.Libsignal.TripleRatchet.consumeMessageKey c 0 = some ((DY.Libsignal.TripleRatchet.kdfCk c.chainKey).2,
                { c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk c.chainKey).1, index := 1 }) := by
      intro c hidx; unfold DY.Libsignal.TripleRatchet.consumeMessageKey; rw [hidx]; rfl
    rw [hcons0 _ rfl, hck]; rfl
  have hskip :
      DY.Libsignal.TripleRatchet.skippedSeeds (bobChain r o.keys (encParsedMsg tr₂ stA cl pq)) (encParsedMsg tr₂ stA cl pq).counter = [] := rfl
  have hik0 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = stA.myIk := (by change DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = DY.Libsignal.PQXDH.serializedIk o.ikA; rw [hikA, setupPublic_0 hNe, setupSecret_0 hNe]); have hik2 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = stA.peerIk := (by change DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = DY.Libsignal.PQXDH.serializedIk o.ikB; rw [hikB]); unfold bobTerms at hu; rw [hkeys, hparse] at hu; dsimp only at hu; rw [hcons, hskip, hck] at hu; simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | ⟨salt, rfl | rfl, hu_salt⟩
  · simp
  · simp
  · simp
  · simp
  · simp
  · have hnone : (DY.SymEnc.symDec (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed).cipherKey (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed).iv
        (encParsedMsg tr₂ stA cl pq).ciphertext).toList = [] := by
      change (DY.SymEnc.symDec zkeys.cipherKey zkeys.iv (encCiphertext tr₂ stA cl pq)).toList = []; rw [symDec_zeroKey_encCiphertext_eq_none tr₁ tr₂ r.bob o cl]; rfl
    rw [hnone] at hu_salt; simp only [List.not_mem_nil, or_false] at hu_salt
    rcases hu_salt with rfl | rfl | rfl | rfl
    · simp [zkeys]
    · simp [zkeys]
    · simp [zkeys]
    · rw [hik0, hik2]; have hw : (encParsedMsg tr₂ stA cl pq).wire = encWire tr₂ stA cl pq := rfl; rw [hw]; simp [zkeys]
  · rw [← encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob o cl] at hu_salt
    have halice := bobTerms_encSalt_eq_aliceTerms_aux (tr₁ := tr₁) (tr₂ := tr₂) (cl := cl) (pq := pq)
      hNe hikA hikB hspk
    dsimp only at halice; dsimp only [stA, akeys] at hck hu_salt ⊢; rw [hck] at halice; rw [halice.2.1, halice.2.2, halice.1] at hu_salt; simp only [List.mem_singleton] at hu_salt
    rcases hu_salt with rfl | rfl | rfl | rfl | rfl <;> simp
theorem mem_bobTerms_x0_iff {r : Records} {p : PreKeyFields} {x₀ : PreKeyRep} {tr₁ tr₂ : ExecTrace} {cl : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hek : DY.X25519.x25519Key x₀.ek = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek) (hct : x₀.ct = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct) (hmsg : x₀.msg = encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)) (u : DY.Bytes) : let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none;
    let stA := iniAliceStartState tr₁ r.bob o; let pq := tr₂.length + 2; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed; let akeys := encMsgKeys tr₂ stA cl pq;
    u ∈ bobTerms r [DY.Spqr.zeroKey, DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)] p x₀ → u ∈ [o.keys.rk, o.keys.ck, o.keys.pqr, stA.cks, (encSt tr₂ stA cl).cks, akeys.cipherKey, akeys.macKey, akeys.iv, encMac tr₂ stA cl pq, randTerm tr₂.length 32, zkeys.cipherKey, zkeys.macKey, zkeys.iv, DY.Libsignal.TripleRatchet.computeMac zkeys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq)] :=
  mem_bobTerms_x0_iff_aux hNe rfl rfl rfl (bobKeys_x0_eq_some hNe hopk hek hct) hmsg u
theorem not_bobStartCollision_x0 {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {p : PreKeyFields} {x₀ : PreKeyRep} {tr₁ : ExecTrace} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hek_key : DY.X25519.x25519Key x₀.ek = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek) (hct : x₀.ct = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct) (hmc : ¬ MemoCollisionOn compI0 r S g (fun u => u.AttackerKnows (runTraceMoves r ms)) (runTraceMoves r ms) (runVis r ms) ([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms) p x₀) []) (hidx : spqrIdx p = 0 ∨ spqrIdx p = 1) (hsalt_mem : DY.Spqr.spqrChainKey (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1) ∈ honestSalts r ms) : ¬ BobStartCollision compI0 r S g ms p x₀ := CompExcuse.not_bobStartCollision_of_parts hmc (not_bobOwnKeyMacGuess_x0 (bobKeys_x0_eq_some hNe hopk hek_key hct) hidx hsalt_mem)
end Symbolic.BugInjection.Proofs.Common443.CompRNoBSC
