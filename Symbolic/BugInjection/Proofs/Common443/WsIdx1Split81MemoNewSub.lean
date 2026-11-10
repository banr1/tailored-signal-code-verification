/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes)
open Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 (compI0 compTag4) open Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 (setup)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.Census443Memo Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoTagged Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
export Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc ( mem_memo_concat_lit_lit_assumedInjective_false mem_memo_trMsgKeys_cipherKey_cases mem_memo_trMsgKeys_macKey_cases mem_memo_trMsgKeys_iv_cases mem_memo_computeMac_cases)
def createChainStepNodes0 (rk pk sk : DY.Bytes) : List DY.Bytes :=
  let dh_bob := DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk
  let c_ck0 := (DY.Libsignal.TripleRatchet.createChain rk pk sk).2
  [DY.Libsignal.TripleRatchet.hmac rk dh_bob, (DY.Libsignal.TripleRatchet.createChain rk pk sk).1, c_ck0, (DY.Libsignal.TripleRatchet.kdfCk c_ck0).1, (DY.Libsignal.TripleRatchet.kdfCk c_ck0).2]
theorem mem_memo_createChain_fst_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1).memo) : x.1 = (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac rk (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk))).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_info
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · exact Or.inr (Or.inr (mem_memo_concat_lit_lit_assumedInjective_false i S g _ _ hx_info))
theorem mem_memo_createChain_snd_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).memo) : x.1 = (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac rk (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk))).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_rk | hx_info
    · rw [hx1]; exact Or.inr (Or.inr (Or.inr (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _)))
    · exact Or.inr (Or.inr (Or.inl hx_rk))
    · exact Or.inr (Or.inr (Or.inr (mem_memo_concat_lit_lit_assumedInjective_false i S g _ _ hx_info)))
theorem mem_memo_kdfCk_fst_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {ck : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk ck).1).memo) : x.1 = (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∨ x ∈ (gamma' i S g ck).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_ck | hx_lit
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_ck)
  · exact Or.inr (Or.inr (mem_memo_lit_assumedInjective_false i S g _ hx_lit))
theorem mem_memo_kdfCk_snd_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {ck : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk ck).2).memo) : x.1 = (DY.Libsignal.TripleRatchet.kdfCk ck).2 ∨ x ∈ (gamma' i S g ck).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_ck | hx_lit
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_ck)
  · exact Or.inr (Or.inr (mem_memo_lit_assumedInjective_false i S g _ hx_lit))
theorem mem_memo_c_ck0_stepNodes0 {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).memo) : x ∈ (gamma' i S g rk).memo ∨ x ∈ (gamma' i S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_createChain_snd_cases hx with hx1 | hx_prk | hx_rk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_r | hx_dh
    · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
    · exact Or.inl hx_r
    · exact Or.inr (Or.inl hx_dh)
  · rcases mem_memo_createChain_fst_cases hx_rk with hx1 | hx_prk | hinj
    · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
    · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_r | hx_dh
      · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
      · exact Or.inl hx_r
      · exact Or.inr (Or.inl hx_dh)
    · exact Or.inr (Or.inr (Or.inl hinj))
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_seed0_stepNodes0 {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).2).memo) : x ∈ (gamma' i S g rk).memo ∨ x ∈ (gamma' i S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_kdfCk_snd_cases hx with hx1 | hx_ck0 | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · exact mem_memo_c_ck0_stepNodes0 hx_ck0
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_c_ck1_stepNodes0 {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).1).memo) : x ∈ (gamma' i S g rk).memo ∨ x ∈ (gamma' i S g (DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk)).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ createChainStepNodes0 rk pk sk := by
  rcases mem_memo_kdfCk_fst_cases hx with hx1 | hx_ck0 | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [createChainStepNodes0, hx1])))
  · exact mem_memo_c_ck0_stepNodes0 hx_ck0
  · exact Or.inr (Or.inr (Or.inl hinj))
def saltedStepNodes (salt seed myIk peerIk wire : DY.Bytes) : List DY.Bytes :=
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
  let macIn := DY.Concat.concat myIk (DY.Concat.concat peerIk wire)
  [DY.Libsignal.TripleRatchet.hmac salt seed, keys.cipherKey, keys.macKey, keys.iv, DY.Libsignal.TripleRatchet.hmac keys.macKey macIn, DY.Libsignal.TripleRatchet.computeMac keys.macKey myIk peerIk wire]
theorem mem_memo_salted_cipherKey_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed myIk peerIk wire : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g seed).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk wire := by
  rcases mem_memo_trMsgKeys_cipherKey_cases hx with hx1 | hx_prk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_macKey_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed myIk peerIk wire : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g seed).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk wire := by
  rcases mem_memo_trMsgKeys_macKey_cases hx with hx1 | hx_prk | hx_ck | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact mem_memo_salted_cipherKey_cases hx_ck
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_iv_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed myIk peerIk wire : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g seed).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk wire := by
  rcases mem_memo_trMsgKeys_iv_cases hx with hx1 | hx_prk | hx_mk | hinj
  · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
  · rcases mem_memo_hmac_cases hx_prk with hx1 | hx_salt | hx_seed
    · exact Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1])))
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
  · exact mem_memo_salted_macKey_cases hx_mk
  · exact Or.inr (Or.inr (Or.inl hinj))
theorem mem_memo_salted_computeMac_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed myIk peerIk wire : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey myIk peerIk wire)).memo) : x ∈ (gamma' i S g salt).memo ∨ x ∈ (gamma' i S g seed).memo ∨ x ∈ (gamma' i S g (DY.Concat.concat myIk (DY.Concat.concat peerIk wire))).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedStepNodes salt seed myIk peerIk wire := by
  rcases mem_memo_computeMac_cases hx with hx1 | hx1_full | hx_mk | hx_in
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simp [saltedStepNodes, hx1_full]))))
  · rcases mem_memo_salted_macKey_cases (myIk := myIk) (peerIk := peerIk) (wire := wire) hx_mk with
      hx_salt | hx_seed | hinj | hs
    · exact Or.inl hx_salt
    · exact Or.inr (Or.inl hx_seed)
    · exact Or.inr (Or.inr (Or.inr (Or.inl hinj)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hs)))
  · exact Or.inr (Or.inr (Or.inl hx_in))
theorem consumeMessageKey_zero_of_index_zero (c : DY.Libsignal.TripleRatchet.RecvChain) (hidx : c.index = 0) : DY.Libsignal.TripleRatchet.consumeMessageKey c 0 = some ((DY.Libsignal.TripleRatchet.kdfCk c.chainKey).2, { c with chainKey := (DY.Libsignal.TripleRatchet.kdfCk c.chainKey).1, index := 1 }) := by rcases c with ⟨rk, ck, idx, rIdx⟩; dsimp only at hidx; subst hidx; rfl
theorem skippedSeeds_zero_of_index_zero (c : DY.Libsignal.TripleRatchet.RecvChain) (hidx : c.index = 0) : DY.Libsignal.TripleRatchet.skippedSeeds c 0 = [] := by rcases c with ⟨rk, ck, idx, rIdx⟩; dsimp only at hidx; subst hidx; rfl
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoNewSub (iniAliceOut_spk)
abbrev dh_bob_ws81_eq := @WsIdx1Split40MemoNewSub.dh_bob_ws40_eq
def ws81Idx1ChainTerms (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) : List DY.Bytes :=
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let rk₁ := DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)
  let c_ck0 := (DY.Libsignal.TripleRatchet.createChain o₂.keys.rk rk₁ (setupSecret r 2)).2
  [o₂.keys.rk, o₂.keys.ck, o₂.keys.pqr, c_ck0, (DY.Libsignal.TripleRatchet.kdfCk c_ck0).1, randTerm tr₂.length 32]
def ws81Idx1SaltTerms (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) (salt : DY.Bytes) : List DY.Bytes :=
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let rk₁ := DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)
  let c_ck0 := (DY.Libsignal.TripleRatchet.createChain o₂.keys.rk rk₁ (setupSecret r 2)).2
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk c_ck0).2
  [keys.cipherKey, keys.macKey, keys.iv, DY.Libsignal.TripleRatchet.computeMac keys.macKey stA₁.myIk stA₁.peerIk (encWire tr₂ stA₁ cl₁ (tr₂.length + 2))]
theorem mem_bobTerms_x81Idx1_iff {r : Records} {salts : List DY.Bytes} {p : PreKeyFields} {tr₁ tr₂ tr₄ : ExecTrace} {cl₁ : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) {u : DY.Bytes} (hu : u ∈ bobTerms r salts p (x81Idx1 r tr₁ tr₂ tr₄ cl₁)) : u ∈ ws81Idx1ChainTerms r tr₁ tr₂ tr₄ ∨ ∃ salt ∈ salts, u ∈ ws81Idx1SaltTerms r tr₁ tr₂ tr₄ cl₁ salt := by
  let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let stA₁ := iniAliceStartState tr₁ r.bob o₁
  let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
  let msg := encParsedMsg tr₂ stA₁ cl₁ (tr₂.length + 2)
  have hkeys : bobKeys r p (x81Idx1 r tr₁ tr₂ tr₄ cl₁) = some o₂.keys := CompRNoBSC.bobKeys_x0_eq_some hNe hopk (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq _) rfl; have hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg (x81Idx1 r tr₁ tr₂ tr₄ cl₁).msg = some msg := parseTrSignalMsg_encOut tr₂ stA₁ cl₁ (tr₂.length + 2)
  have hik0 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = stA₁.myIk := by change DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0)); rw [setupPublic_0 hNe, setupSecret_0 hNe]
  unfold bobTerms at hu; rw [hkeys, hparse] at hu; dsimp only at hu
  rw [show msg.counter = 0 from rfl, consumeMessageKey_zero_of_index_zero (bobChain r o₂.keys msg) rfl,
      skippedSeeds_zero_of_index_zero (bobChain r o₂.keys msg) rfl, hik0,
      show DY.Libsignal.PQXDH.serializedIk (setupPublic r 2) = stA₁.peerIk from rfl,
      show msg.wire = encWire tr₂ stA₁ cl₁ (tr₂.length + 2) from rfl,
      show msg.ciphertext = encCiphertext tr₂ stA₁ cl₁ (tr₂.length + 2) from rfl] at hu
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.mem_flatMap] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | ⟨salt, hsalt, hu_salt⟩
  · exact Or.inl (List.mem_cons.mpr (Or.inl rfl))
  · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))
  · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))))
  · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))))
  · exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))))))
  · rcases hu_salt with rfl | rfl | rfl | rfl | h_dec
    · exact Or.inr ⟨salt, hsalt, List.mem_cons.mpr (Or.inl rfl)⟩
    · exact Or.inr ⟨salt, hsalt, List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl))⟩
    · exact Or.inr ⟨salt, hsalt, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl rfl)))⟩
    · exact Or.inr ⟨salt, hsalt, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl)))⟩
    · rw [mem_symDec_encCiphertext_eq h_dec]
      exact Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton.mpr rfl))))))
def extChainTerms81 (r : Records) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List DY.Bytes :=
  let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
  x.ek :: x.ct :: bobChainTerms81 r tr₁ tr₂ tr₄ cl₁
theorem bobStartKeys_x81Idx1_eq_o2_keys {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : bobStartKeys r (x81Idx1 r tr₁ tr₂ tr₄ cl₁) = (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys := by
  let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
  have hss_eq : (DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) x.ct)).getD (DY.PQKem.kemRejKey (setupSecret r 4) x.ct) = (DY.PQKem.kemEncap (setupPublic r 6) (randTerm (tr₄.length + 1) 32)).2 := by dsimp only [x, x81Idx1, iniAliceOut]; rw [WsIdx1Split81Census.aliceAgreement_fst, setupPublic_6 hNe, setupSecret_4 hNe, WsIdx1Split81Census.kemDecap_kemEncap_fst]; rfl
  have hdh1 : DY.Libsignal.PQXDH.agree (setupPublic r 0) (setupSecret r 2) = DY.Libsignal.PQXDH.agree (setupPublic r 4) (setupSecret r 0) := by rw [setupPublic_0 hNe, setupSecret_0 hNe, setupPublic_4 hNe, setupSecret_2 hNe]; exact CompRNoBSC.agree_dhPk_comm _ _
  have hdh2 : DY.Libsignal.PQXDH.agree x.ek (setupSecret r 1) = DY.Libsignal.PQXDH.agree (setupPublic r 2) (randTerm tr₄.length 32) := by change DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) (setupSecret r 1) = _; rw [setupPublic_2 hNe, setupSecret_1 hNe]; exact CompRNoBSC.agree_dhPk_comm _ _
  have hdh3 : DY.Libsignal.PQXDH.agree x.ek (setupSecret r 2) = DY.Libsignal.PQXDH.agree (setupPublic r 4) (randTerm tr₄.length 32) := by change DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm tr₄.length 32)) (setupSecret r 2) = _; rw [setupPublic_4 hNe, setupSecret_2 hNe]; exact CompRNoBSC.agree_dhPk_comm _ _
  unfold bobStartKeys; dsimp only [Option.map]; rw [hss_eq, hdh1, hdh2, hdh3]; rfl
theorem createChainStepNodes0_eq_bobChainTerms81 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : createChainStepNodes0 (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2) = bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ := by unfold bobChainTerms81 createChainStepNodes0; dsimp only; rw [bobStartKeys_x81Idx1_eq_o2_keys hNe tr₁ tr₂ tr₄ cl₁]; rfl
theorem saltedStepNodes_eq_saltedNodes81 {r : Records} (hNe : r.alice ≠ r.bob) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) (salt : DY.Bytes) :
    let o₁ := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let stA₁ := iniAliceStartState tr₁ r.bob o₁
    let o₂ := iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    let rk₁ := DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)
    let c_ck0 := (DY.Libsignal.TripleRatchet.createChain o₂.keys.rk rk₁ (setupSecret r 2)).2
    saltedStepNodes salt (DY.Libsignal.TripleRatchet.kdfCk c_ck0).2 stA₁.myIk stA₁.peerIk
      (encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) = saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁ := by
  have hik0 : DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)).myIk := by
    change DY.Libsignal.PQXDH.serializedIk (setupPublic r 0) = DY.Libsignal.PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 0))
    rw [setupPublic_0 hNe, setupSecret_0 hNe]
  unfold saltedNodes81 bobSeed81 saltedStepNodes; dsimp only
  rw [bobStartKeys_x81Idx1_eq_o2_keys hNe tr₁ tr₂ tr₄ cl₁, hik0]; rfl
attribute [local irreducible] setupPublic setupSecret
theorem mem_memo_honestSalts_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g salt).memo) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false := by
  obtain ⟨hout₂, hout₃, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl | rfl
  · exact Or.inr (mem_memo_lit_assumedInjective_false compI0 S g _ hx)
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ r.bob _ cl₁] at hx
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_encSalt_of_encOut hx⟩)
  · rw [← encSalt_self tr₃ _ cl₂] at hx
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₃, mem_memo_encSalt_of_encOut hx⟩)
  · rw [← CompRSchedBSalts.encSalt_iniAliceStartState_eq_spqrChainKey tr₄ tr₅ r.bob _ cl₅] at hx
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_encSalt_of_encOut hx⟩)
theorem mem_memo_stepNodes0_ws81Idx1_of_or {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {x : DY.Bytes × DY.Bytes × HwBytes} (h : x ∈ (gamma' compI0 S g (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk).memo ∨ x ∈ (gamma' compI0 S g (DY.DiffieHellman.dh (DY.X25519.x25519Key (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32))) (setupSecret r 2))).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ createChainStepNodes0 (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ := by
  obtain ⟨hout₂, _, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv
  rcases h with hx_rk | hx_dh | hinj | hstep
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_rk_of_encOut hx_rk⟩)
  · rw [dh_bob_ws81_eq hNe tr₁] at hx_dh
    exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_createChain_dh_of_encOut tr₁ tr₂ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none) cl₁ (tr₂.length + 2) hx_dh⟩)
  · exact Or.inr (Or.inl hinj)
  · rw [createChainStepNodes0_eq_bobChainTerms81 hNe tr₁ tr₂ tr₄ cl₁] at hstep
    exact Or.inr (Or.inr hstep)
theorem mem_memo_ws81Idx1ChainTerms {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {u : DY.Bytes} (hu : u ∈ ws81Idx1ChainTerms r tr₁ tr₂ tr₄) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ := by
  obtain ⟨hout₂, _, hout₅, hser₅⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; unfold ws81Idx1ChainTerms at hu; dsimp only at hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_rk_of_encOut hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hser₅, mem_memo_ck_of_serialize_encSt r.alice r.bob tr₄ tr₅ _ cl₅ hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, mem_memo_pqr_of_encOut hx⟩)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact mem_memo_stepNodes0_ws81Idx1_of_or hNe hinv (mem_memo_c_ck0_stepNodes0 hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact mem_memo_stepNodes0_ws81Idx1_of_or hNe hinv (mem_memo_c_ck1_stepNodes0 hx)
  rcases List.mem_singleton.mp hu with rfl
  exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_pt_of_encOut hx⟩)
theorem mem_z81Terms_of_honestSalts {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {z : DY.Bytes} (hz : z ∈ saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁) : z ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
  unfold z81Terms
  rcases hinv.hsalts salt hsalt with rfl | rfl | rfl | rfl
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hz))
  · exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hz))
  · exact List.mem_append_left _ (List.mem_append_right _ hz)
  · exact List.mem_append_right _ hz
theorem mem_memo_ws81Idx1SaltTerms {r : Records} {S : Sem} {g : Ghost} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hNe : r.alice ≠ r.bob) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {salt : DY.Bytes} (hsalt : salt ∈ honestSalts r ms') {u : DY.Bytes} (hu : u ∈ ws81Idx1SaltTerms r tr₁ tr₂ tr₄ cl₁ salt) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' compI0 S g u).memo) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
  obtain ⟨hout₂, _, _, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; unfold ws81Idx1SaltTerms at hu; dsimp only at hu; have hsn_eq := saltedStepNodes_eq_saltedNodes81 hNe tr₁ tr₂ tr₄ cl₁ salt; dsimp only at hsn_eq
  let stA₁ := iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)
  let seed0 := (DY.Libsignal.TripleRatchet.kdfCk (DY.Libsignal.TripleRatchet.createChain (iniAliceOut tr₄ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.rk (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (setupSecret r 2)).2).2
  have hfinish (h : x ∈ (gamma' compI0 S g salt).memo ∨ x ∈ (gamma' compI0 S g seed0).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ saltedStepNodes salt seed0 stA₁.myIk stA₁.peerIk (encWire tr₂ stA₁ cl₁ (tr₂.length + 2))) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false ∨ x.1 ∈ bobChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
    rcases h with hx_salt | hx_seed | hinj | hs
    · exact (mem_memo_honestSalts_ws81Idx1 hinv hsalt hx_salt).elim Or.inl (Or.inr ∘ Or.inl)
    · rcases mem_memo_stepNodes0_ws81Idx1_of_or hNe hinv (mem_memo_seed0_stepNodes0 hx_seed) with hpre | hinj | hch
      · exact Or.inl hpre
      · exact Or.inr (Or.inl hinj)
      · exact Or.inr (Or.inr (Or.inl hch))
    · exact Or.inr (Or.inl hinj)
    · rw [hsn_eq] at hs; exact Or.inr (Or.inr (Or.inr (mem_z81Terms_of_honestSalts hinv hsalt hs)))
  rcases List.mem_cons.mp hu with rfl | hu
  · exact hfinish (mem_memo_salted_cipherKey_cases
      (myIk := stA₁.myIk) (peerIk := stA₁.peerIk) (wire := encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact hfinish (mem_memo_salted_macKey_cases
      (myIk := stA₁.myIk) (peerIk := stA₁.peerIk) (wire := encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · exact hfinish (mem_memo_salted_iv_cases
      (myIk := stA₁.myIk) (peerIk := stA₁.peerIk) (wire := encWire tr₂ stA₁ cl₁ (tr₂.length + 2)) hx)
  rcases List.mem_singleton.mp hu with rfl
  rcases mem_memo_salted_computeMac_cases hx with hx_salt | hx_seed | hx_in | hinj | hs
  · exact hfinish (Or.inl hx_salt)
  · exact hfinish (Or.inr (Or.inl hx_seed))
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, mem_memo_macInput_of_encOut hx_in⟩)
  · exact hfinish (Or.inr (Or.inr (Or.inl hinj)))
  · exact hfinish (Or.inr (Or.inr (Or.inr hs)))
theorem split81NewTerms_x81Idx1_eq (r : Records) (ms' : List Move) (p : PreKeyFields)
    (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) :
    let x := x81Idx1 r tr₁ tr₂ tr₄ cl₁
    split81NewTerms r ms' p x = [x.ek, x.ct, x.msg] ++ bobTerms r (honestSalts r ms') p x := by
  dsimp only; unfold split81NewTerms; rw [parseTrSignalMsg_x81Idx1 r tr₁ tr₂ tr₄ cl₁]
theorem mem_newMemo81_ws81Idx1 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire6Idx1Bytes = some p) (hinv : WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) {x : Row} (hx : x ∈ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁) : x ∈ preMemo81 r S g ms' ∨ assumedInjective x.1 = false ∨ x.1 ∈ extChainTerms81 r tr₁ tr₂ tr₄ cl₁ ∨ x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂ := by
  have hNe : r.alice ≠ r.bob := hfits.1.1.1; have hopk : p.preKeyId = none := wire6Idx1Bytes_preKeyId hp; obtain ⟨hout₂, _, hout₅, _⟩ := prefixTerms_mem_of_ws81Idx1RunInv hinv; unfold newMemo81 at hx; rw [split81NewTerms_x81Idx1_eq r ms' p tr₁ tr₂ tr₄ cl₁] at hx; obtain ⟨u, hu, hx_u⟩ := List.mem_flatMap.mp hx; simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
  rcases hu with rfl | rfl | rfl | hu_bob
  · rcases mem_memo_ek_aliceOut_cases (tr₅ := tr₅) (b := r.bob) (cl₅ := cl₅) (pq₅ := tr₅.length + 2) hx_u with
      hx1 | hx_out₅
    · exact Or.inr (Or.inr (Or.inl (List.mem_cons.mpr (Or.inl hx1))))
    · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, hx_out₅⟩)
  · rcases mem_memo_ct_aliceOut_cases (tr₅ := tr₅) (b := r.bob) (cl₅ := cl₅) (pq₅ := tr₅.length + 2) hx_u with
      hx1 | hx_out₅
    · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl hx1)))))
    · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₅, hx_out₅⟩)
  · exact Or.inl (List.mem_flatMap.mpr ⟨_, hout₂, hx_u⟩)
  · rcases mem_bobTerms_x81Idx1_iff hNe hopk hu_bob with hu_ch | ⟨salt, hsalt, hu_salt⟩
    · rcases mem_memo_ws81Idx1ChainTerms hNe hinv hu_ch hx_u with hpre | hinj | hch
      · exact Or.inl hpre
      · exact Or.inr (Or.inl hinj)
      · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hch))))
    · rcases mem_memo_ws81Idx1SaltTerms hNe hinv hsalt hu_salt hx_u with hpre | hinj | hch | hs
      · exact Or.inl hpre
      · exact Or.inr (Or.inl hinj)
      · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hch))))
      · exact Or.inr (Or.inr (Or.inr hs))
def extChainRows81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List Row := (extChainTerms81 r tr₁ tr₂ tr₄ cl₁).map fun u => (u, (gamma' compI0 S g u).shape, gamma compI0 S g u)
def extBaseRows81 (r : Records) (S : Sem) (g : Ghost) (ms' : List Move) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : List Row := preMemo81 r S g ms' ++ extChainRows81 r S g tr₁ tr₂ tr₄ cl₁
def Split81ExtNewSub : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ x ∈ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁, Cls40 (extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁) (z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) x
theorem split81ExtNewSub : Split81ExtNewSub := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv x hx
  rcases mem_newMemo81_ws81Idx1 hfits hp hinv hx with hpre | hinj | hch | hz
  · exact Or.inl (List.mem_append_left _ hpre)
  · exact Or.inr (Or.inl hinj)
  · obtain ⟨hsh, hval⟩ := sound_of_mem_flatMap hx
    exact Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨x.1, hch, Prod.ext rfl (Prod.ext hsh.symm hval.symm)⟩))
  · exact Or.inr (Or.inr hz)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub
