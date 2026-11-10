/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre
public import Symbolic.BugInjection.Proofs.Common443.CompC2PreUntagged38
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38PC2_S1
open DY.Libsignal (HwBytes)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompFreshDistinct CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompRNoBSC CompRNbsc38MacKey CompC2PreUntagged38 CompC2KdfChild38Pre Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
def node13Gen (tr₁ : ExecTrace) (b : DY.Participant) (ikA ikBPk spkPk pqPk : DY.Bytes) : Fin 13 → DY.Bytes :=
  let o := iniAliceOut tr₁ ikA ikBPk spkPk pqPk none; let ikm := iniAliceIkm tr₁ ikA ikBPk spkPk pqPk; let stA := iniAliceStartState tr₁ b o; let salt := DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1); let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
  fun
  | ⟨0, _⟩ => DY.KdfExtract.kdfExtract DY.Libsignal.TripleRatchet.zeroSalt ikm
  | ⟨1, _⟩ => o.keys.rk
  | ⟨2, _⟩ => o.keys.ck
  | ⟨3, _⟩ => o.keys.pqr
  | ⟨4, _⟩ => DY.KdfExtract.kdfExtract o.keys.rk (DY.Libsignal.PQXDH.agree o.spk (randTerm (tr₁.length + 2) 32))
  | ⟨5, _⟩ => (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).1
  | ⟨6, _⟩ => (DY.Libsignal.TripleRatchet.createChain o.keys.rk o.spk (randTerm (tr₁.length + 2) 32)).2
  | ⟨7, _⟩ => (DY.Libsignal.TripleRatchet.kdfCk stA.cks).1
  | ⟨8, _⟩ => seed
  | ⟨9, _⟩ => DY.KdfExtract.kdfExtract salt seed
  | ⟨10, _⟩ => mk.cipherKey
  | ⟨11, _⟩ => mk.macKey
  | ⟨12, _⟩ => mk.iv
def macNode38Gen (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (ikA ikBPk spkPk pqPk : DY.Bytes) (cl : Nat) : DY.Bytes :=
  let o := iniAliceOut tr₁ ikA ikBPk spkPk pqPk none; let stA := iniAliceStartState tr₁ b o; let salt := DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1); let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed;
  DY.KdfExtract.kdfExtract mk.macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2))))
theorem encKeys_eq_trMsgKeys_ini (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : encKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) = DY.Libsignal.TripleRatchet.trMsgKeys (DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)) (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2 := by change DY.Libsignal.TripleRatchet.trMsgKeys (CompPrefixInvEnc.encSalt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2 = _; rw [encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ b o cl]
theorem encPrk_eq_kdfExtract_ini (tr₁ tr₂ : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) : encPrk tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) = DY.KdfExtract.kdfExtract (DY.Spqr.spqrChainKey o.keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)) (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2 := by change DY.KdfExtract.kdfExtract (CompPrefixInvEnc.encSalt tr₂ (CompPrefixInvAlice.iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2 = _; rw [encSalt_iniAliceStartState_eq_spqrChainKey tr₁ tr₂ b o cl]
end Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38PC2_S1
