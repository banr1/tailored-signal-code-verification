/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
public import Symbolic.BugInjection.Proofs.Common443.CompRI0ShaInj
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompRNbscTable Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey
theorem gamma_hmac_eq_hmacWith (S : Sem) (g : Ghost) (k m : DY.Bytes) (K M : HwBytes) (hl : (gamma compI0 S g k).length = K.length) (hk : K.length ≤ 64) (h : (hmacWith F0 K M).take 4 ≠ compTag4) (heq : gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m) = hmacWith F0 K M) : gamma compI0 S g k = K ∧ gamma compI0 S g m = M := by rw [gamma_hmac_compI0] at heq; have := CompRI0ShaInj.hmacWith_inj_of_untagged hl.symm hk h heq.symm; exact ⟨this.1.symm, this.2.symm⟩
theorem gamma_zeroSalt0 (S : Sem) (g : Ghost) : gamma compI0 S g DY.Libsignal.TripleRatchet.zeroSalt = List.replicate 32 0#8 := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.zeroSalt DY.Literal.literalToBytes
  show ((({lit := _} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (gAll compI0 S g)).bytes = _
  rw [DY.Bytes.rec_eq gLit0 (gAll compI0 S g)]; dsimp only [gLit0, concretizeLit]; decide
theorem gamma_zeroSalt_length (S : Sem) (g : Ghost) : (gamma compI0 S g DY.Libsignal.TripleRatchet.zeroSalt).length = 32 := by rw [gamma_zeroSalt0, List.length_replicate]
theorem kdfCk_next_eq (ck : DY.Bytes) : (DY.Libsignal.TripleRatchet.kdfCk ck).1 = DY.Libsignal.TripleRatchet.hmac ck (DY.Libsignal.TripleRatchet.litByte 0x02) := rfl
theorem keyOfTake8_kdfCk_seed (S : Sem) (g : Ghost) (ck : DY.Bytes) (hk : (gamma compI0 S g ck).length = 32) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).2).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk ck).2).take 8) = some (gamma compI0 S g ck) := gamma_hmac_key_of_take8 S g ck _ hk h
theorem keyOfTake8_hkdfBlock1 (S : Sem) (g : Ghost) (k m info : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 (DY.Libsignal.TripleRatchet.hmac k m) info)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock1 (DY.Libsignal.TripleRatchet.hmac k m) info)).take 8) = some (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)) := by unfold DY.Libsignal.TripleRatchet.hkdfBlock1 at h ⊢; exact gamma_hmac_key_of_take8 S g _ _ (gamma_hmac_length S g k m) h
theorem keyOfTake8_hkdfBlock2 (S : Sem) (g : Ghost) (k m info : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 (DY.Libsignal.TripleRatchet.hmac k m) info)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.hkdfBlock2 (DY.Libsignal.TripleRatchet.hmac k m) info)).take 8) = some (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac k m)) := by unfold DY.Libsignal.TripleRatchet.hkdfBlock2 at h ⊢; exact gamma_hmac_key_of_take8 S g _ _ (gamma_hmac_length S g k m) h
abbrev rkPrk (rk dhOut : DY.Bytes) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac rk dhOut
theorem kdfRk_snd_eq (rk dhOut : DY.Bytes) : (DY.Libsignal.TripleRatchet.kdfRk rk dhOut).2 = DY.Libsignal.TripleRatchet.hkdfBlock2 (rkPrk rk dhOut) (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") := rfl
theorem keyOfTake8_kdfRk_snd (S : Sem) (g : Ghost) (rk dhOut : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfRk rk dhOut).2).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfRk rk dhOut).2).take 8) = some (gamma compI0 S g (rkPrk rk dhOut)) := by rw [kdfRk_snd_eq] at h ⊢; exact keyOfTake8_hkdfBlock2 S g rk dhOut _ h
theorem keyOfTake8_rkPrk (S : Sem) (g : Ghost) (rk dhOut : DY.Bytes) (hk : (gamma compI0 S g rk).length = 32) (h : (gamma compI0 S g (rkPrk rk dhOut)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (rkPrk rk dhOut)).take 8) = some (gamma compI0 S g rk) := gamma_hmac_key_of_take8 S g rk dhOut hk h
abbrev chainDh (pk sk : DY.Bytes) : DY.Bytes := DY.DiffieHellman.dh (DY.X25519.x25519Key pk) sk
theorem keyOfTake8_createChain_snd (S : Sem) (g : Ghost) (rk pk sk : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).take 8) = some (gamma compI0 S g (rkPrk rk (chainDh pk sk))) := keyOfTake8_kdfRk_snd S g rk (chainDh pk sk) h
theorem gamma_createChain_snd_length (S : Sem) (g : Ghost) (rk pk sk : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2).length = 32 := gamma_hmac_length S g _ _
abbrev pqxdhPrk (ikm : DY.Bytes) : DY.Bytes := DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt ikm
theorem keyOfTake8_pqxdh_rk (S : Sem) (g : Ghost) (ikm : DY.Bytes) (h : (gamma compI0 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk).take 8) = some (gamma compI0 S g (pqxdhPrk ikm)) := keyOfTake8_hkdfBlock1 S g _ ikm _ h
theorem gamma_pqxdh_rk_length (S : Sem) (g : Ghost) (ikm : DY.Bytes) : (gamma compI0 S g (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk).length = 32 := gamma_hmac_length S g _ _
theorem keyOfTake8_encSeed (S : Sem) (g : Ghost) (stA : DY.Libsignal.TripleRatchet.TRState) (hk : (gamma compI0 S g stA.cks).length = 32) (h : (gamma compI0 S g (encSeed stA)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (encSeed stA)).take 8) = some (gamma compI0 S g stA.cks) := keyOfTake8_kdfCk_seed S g stA.cks hk h
abbrev iniChainPrk (tr : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : DY.Bytes := rkPrk o.keys.rk (chainDh o.spk (randTerm (tr.length + 2) 32))
theorem iniAliceStartState_cks (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (iniAliceStartState tr b o).cks = (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr.length + 2) 32)).2 :=
  rfl
theorem gamma_iniAliceStartState_cks_length (S : Sem) (g : Ghost) (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) : (gamma compI0 S g (iniAliceStartState tr b o).cks).length = 32 := by rw [iniAliceStartState_cks]; exact gamma_createChain_snd_length S g _ _ _
theorem keyOfTake8_encSeed_ini (S : Sem) (g : Ghost) (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (h : (gamma compI0 S g (encSeed (iniAliceStartState tr b o))).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (encSeed (iniAliceStartState tr b o))).take 8) = some (gamma compI0 S g (iniAliceStartState tr b o).cks) := keyOfTake8_encSeed S g _ (gamma_iniAliceStartState_cks_length S g tr b o) h
theorem keyOfTake8_ini_cks (S : Sem) (g : Ghost) (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (h : (gamma compI0 S g (iniAliceStartState tr b o).cks).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (iniAliceStartState tr b o).cks).take 8) = some (gamma compI0 S g (iniChainPrk tr o)) := keyOfTake8_createChain_snd S g _ _ _ h
theorem keyOfTake8_iniChainPrk (S : Sem) (g : Ghost) (tr : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (ikm : DY.Bytes) (ho : o.keys = DY.Libsignal.PQXDH.pqxdhKdf ikm) (h : (gamma compI0 S g (iniChainPrk tr o)).take 4 ≠ compTag4) : keyOfTake8 ((gamma compI0 S g (iniChainPrk tr o)).take 8) = some (gamma compI0 S g o.keys.rk) := by
  have hk : (gamma compI0 S g o.keys.rk).length = 32 := by rw [ho]; exact gamma_pqxdh_rk_length S g ikm
  exact keyOfTake8_rkPrk S g _ _ hk h
theorem iniAliceOut_keys (tr : ExecTrace) (ikA ikBPk spkPk pqPk : DY.Bytes) (opk : Option DY.Bytes) : ∃ ikm, (iniAliceOut tr ikA ikBPk spkPk pqPk opk).keys = DY.Libsignal.PQXDH.pqxdhKdf ikm := ⟨_, rfl⟩
end Symbolic.BugInjection.Proofs.Common443.CompRSplit38Untagged
