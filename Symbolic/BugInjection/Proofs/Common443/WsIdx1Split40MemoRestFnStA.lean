/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.CompFitsNames Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA ( RvW not_rvW_of_len_head not_rvW_of_kdf_prefix not_rvW_of_len_ge65 ShortHeadOK not_rvW_of_short_head not_rvW_of_short_append_head kdfTail6_not_rvW not_rvW_of_x25519_append not_rvW_zeroDh not_rvW_ff32 FnOKW FnCensusW fnokW_of_ni fnokW_of_isKdf fnokW_of_isX fnokW_of_isTrunc8 fnokW_of_r nrcensusW_lit nrcensusW_lit_ofBA nrcensusW_lit_size nrcensusW_litByte nrcensusW_lit_participant nrcensusW_concat nrcensusW_concat_len_head nrcensusW_concat_kdf nrcensusW_randTerm nrcensusW_randTerm_zero nrcensusW_randTerm_coin nrcensusW_dhPk nrcensusW_dh_pack nrcensusW_kdfExtract nrcensusW_symEnc nrcensusW_trunc8 nrcensusW_agree_dhPk nrcensusW_hmac nrcensusW_hkdf3 nrcensusW_zeroSalt nrcensusW_discontinuity nrcensusW_spqrA2B nrcensusW_spqrIdx_one nrcensusW_spqrSendKey nrcensusW_trWire_of_len nrcensusW_createChain_dhPk nrcensusW_kdfCk nrcensusW_trMsgKeys nrcensusW_serializedIk nrcensusW_pqxdhKdf_none )
export Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb ( nrcensusW_concatPrefixes_kdfTail6 nrcensusW_concatPrefixes_ge65 nrcensusW_concatPrefixes_33_lt64 nrcensusW_concatPrefixes_lt9_head nrcensusW_mem_bool nrcensusW_mem_bool_short_head nrcensusW_mem_slowNat nrcensusW_mem_slowNat_short_head nrcensusW_mem_uint32_012 nrcensusW_mem_uint32_zero_short_head nrcensusW_mem_uint32_two_short_head nrcensusW_mem_slowBytes nrcensusW_mem_slowString_participant nrcensusW_mem_slowString_participant_short_head nrcensusW_serialize_recv1 nrcensusW_concatPrefixes_bool nrcensusW_serialize_local_pqxdh )
abbrev FnC40 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (t : DY.Bytes) : Prop := FnCensusW (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) S g t
theorem fnOK40_of_W {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hR : ∀ v, Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ v → RvW v) {x : DY.Bytes × DY.Bytes × HwBytes} (h : FnOKW (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) x) : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x := ⟨fun hai hv => h.1 hai (hR _ hv), h.2.1, h.2.2⟩
theorem fnCensus40_of_W {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hR : ∀ v, Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ v → RvW v) {t : DY.Bytes} (h : FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ t) : FnCensus40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ t := fun x hx => fnOK40_of_W hR (h x hx)
theorem rvW_of_rv40 {r : Records} {S : Sem} {g : Ghost} {p : PreKeyFields} {ms' : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hfits : compFitsPinned setup compI0 r) (hp : parsePreKeyWire wire3Idx1Bytes = some p) (hinv : WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂) (hlinks : Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂) : ∀ v, Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ v → RvW v := fun _ hv => List.mem_append_left _ (rv40_mem_rVals40 hfits hp hinv hlinks hv)
theorem nrcensusW_randTerm40 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {ts sz : Nat} (hmR : randTerm ts sz ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) : FnC40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ (randTerm ts sz) := nrcensusW_randTerm (mem_allTerms40_of_r hmR) hmR
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnStA
