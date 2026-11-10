/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRSplit38ZPin
public import Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census
public import Symbolic.BugInjection.Proofs.Common443.CompRQRestCensusZ
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestFn
public import Symbolic.BugInjection.Proofs.Common443.CompC2RestEntry38
public import Symbolic.BugInjection.Proofs.Common443.CompC2KdfKK
public import Symbolic.BugInjection.Proofs.Common443.CompC2KdfChild38Pre
public import Symbolic.BugInjection.Proofs.Common443.CompC3KdfInjRest38HB
public import Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3HB38Defs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRNoBSC CompRPlantWire CompRX0SS38 CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0Top CompRTag CompRSplit38PairCore CompRSplit38TaggedAgree CompRSplit38UntaggedShape CompRSplit38ZTag CompRSplit38QKdf CompRNonInj38Census CompRQRestCensusZ CompC2Rest38 CompC2RestFn CompC2RestEntry38 CompC2KdfKK Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
abbrev Split38PairsHB (Q : PairQ) : Prop := Split38PairsAt Q Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Split38PairsTC (Q : PairQ) : Prop := Split38PairsAt Q Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev NonInj38CensusHB : Prop := NonInj38CensusAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev NonInj38CensusXZHB : Prop := NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev NonInj38CensusTC : Prop := NonInj38CensusAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev NonInj38CensusXZTC : Prop := NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev RestPre38HB : Prop := RestPre38At Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Rest38EntryHB : Prop := Rest38EntryAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Rest38FnHB : Prop := Rest38FnAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev RestPre38TC : Prop := RestPre38At Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev Rest38EntryTC : Prop := Rest38EntryAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev Rest38FnTC : Prop := Rest38FnAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
theorem rest38EntryHB_of_pre (h : RestPre38HB) : Rest38EntryHB := rest38EntryAt_of_pre h
theorem rest38EntryTC_of_pre (h : RestPre38TC) : Rest38EntryTC := rest38EntryAt_of_pre h
theorem split38PairsHB_qRest_of_fn (hC : NonInj38CensusXZHB) (hE : Rest38EntryHB) (hF : Rest38FnHB) : Split38PairsHB QRest := split38PairsAt_qRest_of_fn hC hE hF
theorem split38PairsTC_qRest_of_fn (hC : NonInj38CensusXZTC) (hE : Rest38EntryTC) (hF : Rest38FnTC) : Split38PairsTC QRest := split38PairsAt_qRest_of_fn hC hE hF
theorem split38PairsHB_qKdf_of_c (h : Split38PairsHB QKdfC) : Split38PairsHB QKdf := split38PairsAt_qKdf_of_c h
theorem split38PairsTC_qKdf_of_c (h : Split38PairsTC QKdfC) : Split38PairsTC QKdf := split38PairsAt_qKdf_of_c h
theorem split38PairsHB_qKdfKK_of_child2 (hN : NonInj38CensusHB) (hR : Split38PairsHB QKdfInjRest) (hNK : Split38PairsHB QRest) (hCh : Split38PairsHB QKdfChild2) : Split38PairsHB QKdfKK :=
  split38PairsAt_qKdfKK_of_child2 hN hR hNK hCh
theorem split38PairsTC_qKdfKK_of_child2 (hN : NonInj38CensusTC) (hR : Split38PairsTC QKdfInjRest) (hNK : Split38PairsTC QRest) (hCh : Split38PairsTC QKdfChild2) : Split38PairsTC QKdfKK :=
  split38PairsAt_qKdfKK_of_child2 hN hR hNK hCh
end Symbolic.BugInjection.Proofs.Common443.CompC3HB38Defs
namespace Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB
open Symbolic.BugInjection Symbolic.BugInjection.Proofs.Common443 CompRSplit38PairCore CompRSplit38TaggedAgree CompRSplit38UntaggedShape CompRSplit38QKdf CompRNonInj38Census CompRQRestCensusZ CompC2Rest38 CompC2RestFn CompC2RestEntry38 CompC2KdfKK CompC2KdfChild38Pre CompC3HB38Defs
theorem split38PairsHB_qUntagged_of_min (hC : NonInj38CensusHB) (hKK : Split38PairsHB QKdfKK) (hIR : Split38PairsHB QKdfInjRest) (hR : Split38PairsHB QRest) : Split38PairsHB QUntagged := untaggedW_of_kdf_rest (split38PairsHB_qKdf_of_c (split38PairsAt_qKdfC_of hKK hIR hC)) hR
theorem nbscHighBitComp_of_min (hPre : Split38CtxPairsHB QPreUntaggedNX) (hC : NonInj38CensusHB) (hKK : Split38PairsHB QKdfKK) (hIR : Split38PairsHB QKdfInjRest) (hR : Split38PairsHB QRest) : Census443Defs.NbscHighBitComp' := nbscHighBitComp_of_weak (split38PairsHB_qTagged_of_min hPre hC) (split38PairsHB_qUntagged_of_min hC hKK hIR hR)
theorem nbscHighBitComp_of_c3 (hPre : Split38CtxPairsHB QPreUntaggedNX) (hC : NonInj38CensusXZHB) (hKK : Split38PairsHB QKdfKK) (hIR : Split38PairsHB QKdfInjRest) (hRE : Rest38EntryHB) (hRF : Rest38FnHB) : Census443Defs.NbscHighBitComp' := nbscHighBitComp_of_min hPre (nonInj38CensusHB_of_XZ hC) hKK hIR (split38PairsHB_qRest_of_fn hC hRE hRF)
theorem nbscHighBitComp_of_leaves (hPre : Split38CtxPairsHB QPreUntaggedNX) (hC : NonInj38CensusXZHB) (hIR : Split38PairsHB QKdfInjRest) (hRP : RestPre38HB) (hRF : Rest38FnHB) (hCh : Split38PairsHB QKdfChild2) : Census443Defs.NbscHighBitComp' :=
  let hRE := rest38EntryHB_of_pre hRP;
  nbscHighBitComp_of_c3 hPre hC (split38PairsHB_qKdfKK_of_child2 (nonInj38CensusHB_of_XZ hC) hIR (split38PairsHB_qRest_of_fn hC hRE hRF) hCh) hIR hRE hRF
theorem split38PairsTC_qUntagged_of_min (hC : NonInj38CensusTC) (hKK : Split38PairsTC QKdfKK) (hIR : Split38PairsTC QKdfInjRest) (hR : Split38PairsTC QRest) : Split38PairsTC QUntagged := untaggedW_of_kdf_rest (split38PairsTC_qKdf_of_c (split38PairsAt_qKdfC_of hKK hIR hC)) hR
theorem nbscTorsionComp_of_min (hPre : Split38CtxPairsTC QPreUntaggedNX) (hC : NonInj38CensusTC) (hKK : Split38PairsTC QKdfKK) (hIR : Split38PairsTC QKdfInjRest) (hR : Split38PairsTC QRest) : Census443Defs.NbscTorsionComp' := nbscTorsionComp_of_weak (split38PairsTC_qTagged_of_min hPre hC) (split38PairsTC_qUntagged_of_min hC hKK hIR hR)
theorem nbscTorsionComp_of_c3 (hPre : Split38CtxPairsTC QPreUntaggedNX) (hC : NonInj38CensusXZTC) (hKK : Split38PairsTC QKdfKK) (hIR : Split38PairsTC QKdfInjRest) (hRE : Rest38EntryTC) (hRF : Rest38FnTC) : Census443Defs.NbscTorsionComp' := nbscTorsionComp_of_min hPre (nonInj38CensusTC_of_XZ hC) hKK hIR (split38PairsTC_qRest_of_fn hC hRE hRF)
theorem nbscTorsionComp_of_leaves (hPre : Split38CtxPairsTC QPreUntaggedNX) (hC : NonInj38CensusXZTC) (hIR : Split38PairsTC QKdfInjRest) (hRP : RestPre38TC) (hRF : Rest38FnTC) (hCh : Split38PairsTC QKdfChild2) : Census443Defs.NbscTorsionComp' :=
  let hRE := rest38EntryTC_of_pre hRP;
  nbscTorsionComp_of_c3 hPre hC (split38PairsTC_qKdfKK_of_child2 (nonInj38CensusTC_of_XZ hC) hIR (split38PairsTC_qRest_of_fn hC hRE hRF) hCh) hIR hRE hRF
end Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB
