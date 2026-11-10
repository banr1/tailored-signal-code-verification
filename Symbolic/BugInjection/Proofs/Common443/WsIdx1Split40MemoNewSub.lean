/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSubAux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40OwnSalt
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
open CryptoProofLib.Refinement DY DY.Libsignal DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4)
open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc ( mem_memo_concat_lit_lit_assumedInjective_false mem_memo_trMsgKeys_cipherKey_cases mem_memo_trMsgKeys_macKey_cases mem_memo_trMsgKeys_iv_cases mem_memo_computeMac_cases)
theorem mem_memo_salted_cipherKey_cases40 {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).cipherKey).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedNodes40 salt tr stA cl := by
  rcases mem_memo_trMsgKeys_cipherKey_cases hx with hx1 | hx_prk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_macKey_cases40 {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedNodes40 salt tr stA cl := by
  rcases mem_memo_trMsgKeys_macKey_cases hx with hx1 | hx_prk | hx_ck | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1])))
  · exact mem_memo_salted_cipherKey_cases40 (mem_memo_hmac_left hx_prk)
  · exact mem_memo_salted_cipherKey_cases40 hx_ck
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_iv_cases40 {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).iv).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedNodes40 salt tr stA cl := by
  rcases mem_memo_trMsgKeys_iv_cases hx with hx1 | hx_prk | hx_mk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1])))
  · exact mem_memo_salted_cipherKey_cases40 (mem_memo_hmac_left hx_prk)
  · exact mem_memo_salted_macKey_cases40 hx_mk
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_computeMac_cases40 {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt : DY.Bytes} {tr : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey stA.myIk stA.peerIk (encWire tr stA cl (tr.length + 2)))).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo ∨ x ∈ (gamma' i S g (encOut tr stA cl (tr.length + 2))).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedNodes40 salt tr stA cl := by
  rcases mem_memo_computeMac_cases hx with hx1 | hx1_full | hx_mk | hx_in
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedNodes40, hx1_full]))))
  · exact (mem_memo_salted_macKey_cases40 (tr := tr) (stA := stA) (cl := cl) hx_mk).imp id
      (Or.imp id Or.inr)
  · exact Or.inr (Or.inr (Or.inl (mem_memo_encMac_of_encOut (mem_memo_trunc8 (mem_memo_hmac_right hx_in)))))
set_option maxRecDepth 200000 in theorem wire3Idx1Fast_preKeyId : (parsePreKeyWire WsIdx1Split40OwnSalt.wire3Idx1Fast).map (·.preKeyId) = some none := by decide +kernel
theorem wire3Idx1Bytes_eq_wire3Idx1Fast : wire3Idx1Bytes = WsIdx1Split40OwnSalt.wire3Idx1Fast := WsIdx1Split40OwnSalt.wire3Idx1Bytes_eq_fast
theorem wire3Idx1Bytes_preKeyId {p : PreKeyFields} (hp : parsePreKeyWire wire3Idx1Bytes = some p) : p.preKeyId = none := by
  have h := wire3Idx1Fast_preKeyId; rw [← wire3Idx1Bytes_eq_wire3Idx1Fast, hp] at h; exact Option.some.inj h
theorem consumeMessageKey_one_of_chainKey_eq (c : DY.Libsignal.TripleRatchet.RecvChain)
    (stA₁ : DY.Libsignal.TripleRatchet.TRState) (tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat)
    (hidx : c.index = 0) (hck : c.chainKey = stA₁.cks) :
    let stA₁' := encSt tr₂ stA₁ cl₁
    let stA₁'' := encSt tr₃ stA₁' cl₂
    DY.Libsignal.TripleRatchet.consumeMessageKey c 1 = some ((DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2,
            { c with chainKey := stA₁''.cks, index := 2 }) := by
  rcases c with ⟨rk, ck, idx, rIdx⟩; dsimp only at hidx hck ⊢; subst hidx hck; rfl
theorem skippedSeeds_one_of_chainKey_eq (c : DY.Libsignal.TripleRatchet.RecvChain) (stA₁ : DY.Libsignal.TripleRatchet.TRState) (hidx : c.index = 0) (hck : c.chainKey = stA₁.cks) : DY.Libsignal.TripleRatchet.skippedSeeds c 1 = [(DY.Libsignal.TripleRatchet.kdfCk stA₁.cks).2] := by rcases c with ⟨rk, ck, idx, rIdx⟩; dsimp only at hidx hck ⊢; subst hidx hck; rfl
theorem encParsedMsg_counter_stA₁' (tr₁ tr₂ tr₃ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ pq : Nat) : (encParsedMsg tr₃ (encSt tr₂ (iniAliceStartState tr₁ b o) cl₁) cl₂ pq).counter = 1 := rfl
theorem iniAliceOut_spk (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : (iniAliceOut tr ikA ikBPk spkPk pqPk opk).spk = spkPk := rfl
theorem dh_bob_ws40_eq {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ : ExecTrace) : DY.DiffieHellman.dh (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32))) (setupSecret r 2) = DY.DiffieHellman.dh (DY.X25519.x25519Key (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).spk) (randTerm (tr₁.length + 2) 32) := by rw [iniAliceOut_spk, CompRNoBSC.x25519Key_setupPublic_4 hNe, setupPublic_4 hNe, setupSecret_2 hNe]; unfold DY.X25519.x25519Key; rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq]; exact CompRNoBSC.dh_dhPk_comm _ _
theorem bobChain_encParsedMsg_stA₁'_chainKey (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ pq : Nat) : (bobChain r o.keys (encParsedMsg tr₃ (encSt tr₂ (iniAliceStartState tr₁ b o) cl₁) cl₂ pq)).chainKey = (DY.Libsignal.TripleRatchet.createChain o.keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)).2 := rfl
theorem iniAliceStartState_cks (tr₁ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr₁ b o).cks = (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).2 := rfl
theorem bobChain_x40Idx1_chainKey_eq_cks {r : Records} (hNe : r.alice ≠ r.bob)
    (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let stA₁' := encSt tr₂ stA₁ cl₁
    (bobChain r o₁.keys (encParsedMsg tr₃ stA₁' cl₂ (tr₃.length + 2))).chainKey = stA₁.cks := by
  intro o₁ stA₁ stA₁'
  rw [bobChain_encParsedMsg_stA₁'_chainKey, iniAliceStartState_cks]
  unfold DY.Libsignal.TripleRatchet.createChain DY.X25519.agree; rw [dh_bob_ws40_eq hNe tr₁]
def ws40Idx1ExtraTerms (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let stA₁' := encSt tr₂ stA₁ cl₁
  let stA₁'' := encSt tr₃ stA₁' cl₂
  [o₁.keys.rk, o₁.keys.ck, o₁.keys.pqr, stA₁.cks, stA₁''.cks, (DY.Libsignal.TripleRatchet.kdfCk stA₁.cks).2, randTerm tr₃.length 32]
def ws40Idx1SaltTerms (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (salt : DY.Bytes) :
    List DY.Bytes :=
  let stA₁' := stA40 r tr₁ tr₂ cl₁
  let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed₂
  [keys.cipherKey, keys.macKey, keys.iv, DY.Libsignal.TripleRatchet.computeMac keys.macKey stA₁'.myIk stA₁'.peerIk (encWire tr₃ stA₁' cl₂ (tr₃.length + 2))]
theorem encSt_iniAliceStartState_myIk (tr₁ tr₂ : ExecTrace) (b : Participant) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (cl₁ : Nat) : (encSt tr₂ (iniAliceStartState tr₁ b (iniAliceOut tr₁ ikA ikB spk pqpk opk)) cl₁).myIk = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk ikA) := rfl
theorem serializedIk_setupPublic_0_eq_myIk {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ : ExecTrace) (cl₁ : Nat) : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁).myIk := by rw [setupPublic_0 hNe, setupSecret_0 hNe]; exact (encSt_iniAliceStartState_myIk tr₁ tr₂ r.bob _ _ _ _ none cl₁).symm
theorem encSt_iniAliceStartState_peerIk (tr₁ tr₂ : ExecTrace) (b : Participant) (ikA ikB spk pqpk : DY.Bytes) (opk : Option DY.Bytes) (cl₁ : Nat) : (encSt tr₂ (iniAliceStartState tr₁ b (iniAliceOut tr₁ ikA ikB spk pqpk opk)) cl₁).peerIk = DY.Libsignal.PQXDH.serializedIk ikB := rfl
theorem mem_bobTerms_of_step1
    {r : Records} {salts : List DY.Bytes} {p : PreKeyFields}
    {x : PreKeyRep} {o : DY.Libsignal.PQXDH.AliceHandshakeOut}
    {stA₁ : DY.Libsignal.TripleRatchet.TRState}
    {tr₂ tr₃ : ExecTrace} {cl₁ cl₂ pq : Nat}
    (hkeys : bobKeys r p x = some o.keys)
    (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg = some (encParsedMsg tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq))
    (hck : (bobChain r o.keys (encParsedMsg tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq)).chainKey = stA₁.cks)
    (hcnt : (encParsedMsg tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq).counter = 1)
    (hik0 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = (encSt tr₂ stA₁ cl₁).myIk)
    (hik2 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = (encSt tr₂ stA₁ cl₁).peerIk)
    {u : DY.Bytes} (hu : u ∈ bobTerms r salts p x) :
    u ∈ [o.keys.rk, o.keys.ck, o.keys.pqr, stA₁.cks, (encSt tr₃ (encSt tr₂ stA₁ cl₁) cl₂).cks, (DY.Libsignal.TripleRatchet.kdfCk stA₁.cks).2, randTerm tr₃.length 32] ∨
    ∃ salt ∈ salts,
      let stA₁' := encSt tr₂ stA₁ cl₁
      let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2
      let mkeys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed₂
      u ∈ [mkeys.cipherKey, mkeys.macKey, mkeys.iv, DY.Libsignal.TripleRatchet.computeMac mkeys.macKey stA₁'.myIk stA₁'.peerIk
             (encWire tr₃ stA₁' cl₂ pq)] := by
  have hcons := hcnt ▸ consumeMessageKey_one_of_chainKey_eq _ stA₁ tr₂ tr₃ cl₁ cl₂ rfl hck
  have hskip := hcnt ▸ skippedSeeds_one_of_chainKey_eq _ stA₁ rfl hck
  have hwire : (encParsedMsg tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq).wire =
      encWire tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq := rfl
  have hct : (encParsedMsg tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq).ciphertext =
      encCiphertext tr₃ (encSt tr₂ stA₁ cl₁) cl₂ pq := rfl
  unfold bobTerms at hu; rw [hkeys, hparse] at hu; dsimp only at hu
  rw [hcons, hskip, hik0, hik2, hwire, hct] at hu
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap] at hu
  rcases hu with rfl | rfl | rfl | hu_ck | rfl | rfl | ⟨salt, hsalt, hu_salt⟩
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · exact Or.inl (by simp [hu_ck, hck])
  · exact Or.inl (by simp)
  · exact Or.inl (by simp)
  · rcases hu_salt with rfl | rfl | rfl | rfl | h_dec
    · exact Or.inr ⟨salt, hsalt, by simp⟩
    · exact Or.inr ⟨salt, hsalt, by simp⟩
    · exact Or.inr ⟨salt, hsalt, by simp⟩
    · exact Or.inr ⟨salt, hsalt, by simp⟩
    · exact Or.inl (by simp [mem_symDec_encCiphertext_eq h_dec])
theorem mem_bobTerms_x40Idx1_iff {r : Records} {salts : List DY.Bytes} {p : PreKeyFields} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) {u : DY.Bytes} (hu : u ∈ bobTerms r salts p (x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂)) : u ∈ ws40Idx1ExtraTerms r tr₁ tr₂ tr₃ cl₁ cl₂ ∨ ∃ salt ∈ salts, u ∈ ws40Idx1SaltTerms r tr₁ tr₂ tr₃ cl₁ cl₂ salt := mem_bobTerms_of_step1 (CompRNoBSC.bobKeys_x0_eq_some hNe hopk (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) rfl) (parseTrSignalMsg_encOut tr₃ _ cl₂ (tr₃.length + 2)) (bobChain_x40Idx1_chainKey_eq_cks hNe tr₁ tr₂ tr₃ cl₁ cl₂) (encParsedMsg_counter_stA₁' tr₁ tr₂ tr₃ r.bob _ cl₁ cl₂ (tr₃.length + 2)) (serializedIk_setupPublic_0_eq_myIk hNe tr₁ tr₂ cl₁) ((encSt_iniAliceStartState_peerIk tr₁ tr₂ r.bob _ _ _ _ none cl₁).symm) hu
theorem mem_split40NewTerms_iff
    {r : Records} {ms' : List Move} {p : PreKeyFields}
    {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} :
    let x := x40Idx1 r tr₁ tr₂ tr₃ cl₁ cl₂
    u ∈ split40NewTerms r ms' p x ↔
      u = x.ek ∨ u = x.ct ∨ u = x.msg ∨ u ∈ bobTerms r (honestSalts r ms') p x := by
  intro x
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁' := encSt tr₂ (iniAliceStartState tr₁ r.bob o₁) cl₁
  have hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg x.msg =
      some (encParsedMsg tr₃ stA₁' cl₂ (tr₃.length + 2)) :=
    parseTrSignalMsg_encOut tr₃ stA₁' cl₂ (tr₃.length + 2)
  unfold split40NewTerms; rw [hparse]; dsimp only
  simp only [List.cons_append, List.nil_append, List.mem_cons]
theorem mem_memo_honestSalts_ws40Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g salt).memo) : x ∈ preMemo40 r S g ms' ∨ assumedInjective x.1 = false := by
  obtain ⟨hout₂, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl
  · exact Or.inr (mem_memo_lit_assumedInjective_false compI0 S g _ hx)
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hx
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_encSalt_of_encOut hx⟩)
  · rw [← WsIdx1Split40OwnSalt.encSalt_self tr₃ _ cl₂] at hx
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₃, mem_memo_encSalt_of_encOut hx⟩)
theorem mem_memo_extraTerms_ws40Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {u : DY.Bytes} (hu : u ∈ ws40Idx1ExtraTerms r tr₁ tr₂ tr₃ cl₁ cl₂) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo40 r S g ms' := by
  obtain ⟨hout₂, hout₃, hst₂, hst₃⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv; simp only [ws40Idx1ExtraTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_rk_of_encOut hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hst₂, mem_memo_ck_of_serialize_encSt r.alice r.bob tr₁ tr₂ _ cl₁ hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_pqr_of_encOut hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_cks_of_encOut hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hst₃, mem_memo_cks_of_serialize_localState ⟨r.alice, _⟩ hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_seed_of_encOut hx⟩
  · exact List.mem_flatMap.mpr ⟨_, hout₃, mem_memo_pt_of_encOut hx⟩
theorem saltedNodes40_sub_z40Terms_of_zero_or_ck1 {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {salt : DY.Bytes} (hsalt : salt = DY.Spqr.zeroKey ∨ salt = ck1Salt40 r tr₁) {v : DY.Bytes} (hv : v ∈ saltedNodes40 salt tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂) : v ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂ := by
  unfold z40Terms
  rcases hsalt with rfl | rfl <;> [exact List.mem_append_left _ hv; exact List.mem_append_right _ hv]
theorem trMsgKeys_encSalt_eq_encMsgKeys (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr stA cl pq) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 = encMsgKeys tr stA cl pq := rfl
theorem computeMac_encMsgKeys_eq_encMac (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : DY.Libsignal.TripleRatchet.computeMac (encMsgKeys tr stA cl pq).macKey stA.myIk stA.peerIk (encWire tr stA cl pq) = encMac tr stA cl pq := rfl
theorem mem_memo_saltTerms_ws40Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {u : DY.Bytes} (hu : u ∈ ws40Idx1SaltTerms r tr₁ tr₂ tr₃ cl₁ cl₂ salt) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x := by
  let stA₁' := stA40 r tr₁ tr₂ cl₁
  let seed₂ := (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2
  obtain ⟨_, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv
  have hout₃_pre : ∀ {y : Row}, y ∈ (gamma' compI0 S g (encOut tr₃ stA₁' cl₂ (tr₃.length + 2))).memo →
      y ∈ preMemo40 r S g ms' := fun hy => List.mem_flatMap.mpr ⟨_, hout₃, hy⟩
  have hseed₂_pre : ∀ {y : Row}, y ∈ (gamma' compI0 S g seed₂).memo → y ∈ preMemo40 r S g ms' :=
    fun hy => hout₃_pre (mem_memo_seed_of_encOut hy)
  have hsalts : (salt = DY.Spqr.zeroKey ∨ salt = ck1Salt40 r tr₁) ∨ salt = (DY.Spqr.spqrSend stA₁'.spqr (randTerm (tr₃.length + 1) cl₂)).2.1 := by
    rcases hinv.hsalts salt hsalt with h1 | h2 | h3; exacts [Or.inl (Or.inl h1), Or.inl (Or.inr h2), Or.inr h3]
  rcases hsalts with hzc | hsend2
  · have hfin : x ∈ (gamma' compI0 S g salt).memo ∨
        x ∈ (gamma' compI0 S g seed₂).memo ∨
        assumedInjective x.1 = false ∨
        x.1 ∈ saltedNodes40 salt tr₃ stA₁' cl₂ →
        Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x := by
      rintro (hs | hsd | hinj | hnode)
      · exact (mem_memo_honestSalts_ws40Idx1 hinv hsalt hs).imp id Or.inl
      · exact Or.inl (hseed₂_pre hsd)
      · exact Or.inr (Or.inl hinj)
      · exact Or.inr (Or.inr (saltedNodes40_sub_z40Terms_of_zero_or_ck1 hzc hnode))
    simp only [ws40Idx1SaltTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hfin (mem_memo_salted_cipherKey_cases40 hx)
    · exact hfin (mem_memo_salted_macKey_cases40 hx)
    · exact hfin (mem_memo_salted_iv_cases40 hx)
    · rcases mem_memo_salted_computeMac_cases40 (tr := tr₃) (stA := stA₁') (cl := cl₂) hx with
        hs | hsd | hout | hinj | hnode
      · exact hfin (Or.inl hs)
      · exact hfin (Or.inr (Or.inl hsd))
      · exact Or.inl (hout₃_pre hout)
      · exact hfin (Or.inr (Or.inr (Or.inl hinj)))
      · exact hfin (Or.inr (Or.inr (Or.inr hnode)))
  · have hkeys_eq : DY.Libsignal.TripleRatchet.trMsgKeys salt seed₂ =
        encMsgKeys tr₃ stA₁' cl₂ (tr₃.length + 2) := by
      change DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA₁'.cks).2 = _; rw [hsend2, ← WsIdx1Split40OwnSalt.encSalt_self tr₃ stA₁' cl₂]; rfl
    simp only [ws40Idx1SaltTerms, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl <;> rw [hkeys_eq] at hx
    · exact Or.inl (hout₃_pre (mem_memo_akeys_cipherKey_of_encOut hx))
    · exact Or.inl (hout₃_pre (mem_memo_akeys_macKey_of_encOut hx))
    · exact Or.inl (hout₃_pre (mem_memo_akeys_iv_of_encOut hx))
    · rw [computeMac_encMsgKeys_eq_encMac] at hx
      exact Or.inl (hout₃_pre (mem_memo_encMac_of_encOut hx))
theorem cls40_of_mem_newMemo40_of_ek_ct_mem {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hek : (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms')) (hct : (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms')) {x : Row} (hx : x ∈ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂) : Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x := by
  obtain ⟨_, hout₃, _, _⟩ := prefixTerms_mem_of_ws40Idx1RunInv hinv; obtain ⟨u, hu, hxu⟩ := List.mem_flatMap.mp hx
  rcases mem_split40NewTerms_iff.mp hu with rfl | rfl | rfl | hbt
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hek, hxu⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hct, hxu⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₃, hxu⟩)
  · rcases mem_bobTerms_x40Idx1_iff hfits.1.1.1 (wire3Idx1Bytes_preKeyId hp) hbt with
      hextra | ⟨salt, hsalt, hsalt_u⟩
    · exact Or.inl (mem_memo_extraTerms_ws40Idx1 hinv hextra hxu)
    · exact mem_memo_saltTerms_ws40Idx1 hinv hsalt hsalt_u hxu
def Split40NewSubOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂, Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x
theorem split40NewSubOwn : Split40NewSubOwn := by intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown x hx; obtain ⟨hek, hct⟩ := ek_ct_mem_prefixTerms_of_links40Own hown; exact cls40_of_mem_newMemo40_of_ek_ct_mem hfits hp hinv hek hct hx
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
