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
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKeyWire
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VT
public import Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestPre38HB

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 CompExcuse CompFreshDistinct CompPlant CompPrefixInvAlice CompPrefixInvEnc CompPrefixInvStruct CompPrefixInvSwap CompRMemoKnown CompRNoBSC CompRPlantWire CompRX0SS38 CompRX0NBSC38 CompRX0NBSC38Hmc CompRX0NBSC38Parts CompRX0NBSC38Wire CompRTag CompRNbscTable CompRNbsc38MacKeyWire CompRNbsc38VT CompRSplit38PairCore CompRSplit38TaggedAgree CompRSplit38UntaggedShape CompRSplit38ZTag CompRSplit38ZVals CompRSplit38ZPin CompRSplit38QKdf CompRNonInj38Census CompRQRestCensusZ
open Symbolic.BugInjection.Proofs.Common443.CompRNbsc38MacKey hiding sentWireFast gamma_hmac_compI0
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
abbrev Split38PairsHB (Q : PairQ) : Prop := Split38PairsAt Q Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Split38CtxPairsHB (R : CtxQ) : Prop := Split38CtxPairsAt R Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev Split38PairsTC (Q : PairQ) : Prop := Split38PairsAt Q Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev Split38CtxPairsTC (R : CtxQ) : Prop := Split38CtxPairsAt R Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev NonInj38CensusHB : Prop := NonInj38CensusAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev NonInj38CensusXZHB : Prop := NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupHighBitComp.setup (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) highBitWireBytes 1 0
abbrev NonInj38CensusTC : Prop := NonInj38CensusAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
abbrev NonInj38CensusXZTC : Prop := NonInj38CensusXZAt Witnesses.Cheval26SmallSubgroupTorsionComp.setup (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) torsionWireBytes 0 1
theorem nonInj38CensusHB_of_XZ (h : NonInj38CensusXZHB) : NonInj38CensusHB := nonInj38CensusAt_of_XZ h
theorem nonInj38CensusTC_of_XZ (h : NonInj38CensusXZTC) : NonInj38CensusTC := nonInj38CensusAt_of_XZ h
def msg32OfHmac (prk : HwBytes) : HwBytes :=
  match rowOfTake8 (prk.take 8) with
  | none => []
  | some rOut2 => match rowOfTake8 (((Refinement.leBytes 64 rOut2.2.1).take 32).take 8) with
    | none => []
    | some rIn2 => (Refinement.leBytes 64 rIn2.2.1).take 32
def seed0SS : HwBytes := msg32OfHmac sentPrk
def ssIkA : HwBytes := ecKey (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.aliceId))
def ssIkB : HwBytes := ecKey (compLookupPub (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId))
def sentMsg : HwBytes := match parsePreKeyWire sentWireFast with | some p => p.message | none => []
def M38SS : HwBytes := ssIkA ++ ssIkB ++ sentMsg.take (sentMsg.length - 8)
def zprk0SS : HwBytes := hmacWith F0 zeros32 seed0SS
def zmk0SS : HwBytes := hmacWith F0 zprk0SS (hmacWith F0 zprk0SS (zInfo ++ [1#8]) ++ (zInfo ++ [2#8]))
def zfull0SS : HwBytes := hmacWith F0 zmk0SS M38SS
def sentMacD : HwBytes := hmacWith F0 sentMacKey M38SS
private theorem nbsc38_checks :
    hmacWith F0 sentSalt seed0SS = sentPrk ∧
    sentPrk.take 4 ≠ compTag4 ∧
    sentMacD.take 4 ≠ compTag4 ∧
    (parsePreKeyWire CompRPlantWire.sentWireFast).map msgMac8 = some (sentMacD.take 8) ∧
    (zChain zprk0SS zfull0SS).Nodup ∧
    sentSalt.length ≤ 64 ∧
    sentMacKey.length ≤ 64 := by decide +kernel
theorem sentPrk_eq : hmacWith F0 sentSalt seed0SS = sentPrk := nbsc38_checks.1
theorem sentPrk_untagged : sentPrk.take 4 ≠ compTag4 := nbsc38_checks.2.1
theorem sentMacD_untagged : sentMacD.take 4 ≠ compTag4 := nbsc38_checks.2.2.1
theorem sentMacD_mem : sentMacD ∈ CompRI0TermInj.rowDigests := (CompRI0TermInj.hmacWith_tag_or_row sentMacKey M38SS).resolve_left sentMacD_untagged
theorem sentMac8_fast : (parsePreKeyWire CompRPlantWire.sentWireFast).map msgMac8 = some (sentMacD.take 8) := nbsc38_checks.2.2.2.1
theorem sentMac8 : (parsePreKeyWire CompRPlantWire.sentWireBytes).map msgMac8 = some (sentMacD.take 8) := by rw [CompRPlantWire.sentWireBytes_eq]; exact sentMac8_fast
theorem zChainSS_nodup : (zChain zprk0SS zfull0SS).Nodup := nbsc38_checks.2.2.2.2.1
private theorem encMac_eq' (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl pq : Nat) : encMac tr₂ stA cl pq = DY.Libsignal.TripleRatchet.computeMac (encKeys tr₂ stA cl pq).macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq) := rfl
theorem seedPin_ss (S : Sem) (g : Ghost) (tr₁ tr₂ : ExecTrace) (b : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) (hP : gamma compI0 S g (encPrk tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)) = sentPrk) : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2 = seed0SS := by
  have hsL : (gamma compI0 S g (encSalt tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).length =
      sentSalt.length := by
    rw [encSalt_iniAliceStartState_eq_spqrChainKey, CompRPreMemo38KdfCensus.gamma_spqrChainKey_length]; rfl
  exact (CompRSplit38Untagged.gamma_hmac_eq_hmacWith S g _ _ sentSalt seed0SS hsL nbsc38_checks.2.2.2.2.2.1
    (by rw [sentPrk_eq]; exact sentPrk_untagged) (by rw [sentPrk_eq]; exact hP)).2
theorem msgPin_ss (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) (hk : gamma compI0 S g (encKeys tr₂ stA cl (tr₂.length + 2)).macKey = sentMacKey) (hu1 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 4 ≠ compTag4) (hm8 : gamma compI0 S g (encMac tr₂ stA cl (tr₂.length + 2)) = sentMacD.take 8) : gamma compI0 S g (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))) = M38SS := by
  have hrow := (CompRI0TermInj.gamma_kdfExtract_tag_or_row _ _).resolve_left hu1
  have h8 : (gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (encKeys tr₂ stA cl (tr₂.length + 2)).macKey (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))))).take 8 =
      sentMacD.take 8 := by rw [← hm8, encMac_eq', gamma_computeMac]
  exact (CompRSplit38Untagged.gamma_hmac_eq_hmacWith S g _ _ sentMacKey M38SS (by rw [hk]) nbsc38_checks.2.2.2.2.2.2 sentMacD_untagged (rowDigests_take8_inj hrow sentMacD_mem h8)).2
theorem zprk_pin_ss (S : Sem) (g : Ghost) (stA : DY.Libsignal.TripleRatchet.TRState) (hseed : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 = seed0SS) : gamma compI0 S g (zprkT stA) = zprk0SS := by
  show gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2) = zprk0SS
  rw [gamma_hmac_compI0, gamma_zeroKey, hseed]; rfl
theorem zfull_pin_ss (S : Sem) (g : Ghost) (tr₂ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) (hseed : gamma compI0 S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2 = seed0SS) (hM : gamma compI0 S g (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2)))) = M38SS) : gamma compI0 S g (zfullT tr₂ stA cl (tr₂.length + 2)) = zfull0SS := by
  show gamma compI0 S g (DY.Libsignal.TripleRatchet.hmac (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey (Concat.concat stA.myIk (Concat.concat stA.peerIk (encWire tr₂ stA cl (tr₂.length + 2))))) = zfull0SS
  rw [gamma_hmac_compI0, hM, gamma_zmacKey, zprk_pin_ss S g stA hseed]; rfl
attribute [local irreducible] seed0SS ssIkA ssIkB sentMsg M38SS zprk0SS zmk0SS zfull0SS sentMacD Symbolic.BugInjection.hexBytes setupSecret setupPublic setupTrace
theorem split38_zpins_ss {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    gamma compI0 S g (zprkT stA) = zprk0SS ∧
      gamma compI0 S g (zfullT tr₂ stA cl (tr₂.length + 2)) = zfull0SS := by
  dsimp only; obtain ⟨hk, hP, _, _, hu1, _⟩ := split38_encMac_chain (r := r) (S := S) (g := g) hNe hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompRX0SS38.sentWireBytes_len wireMacChainOk_sentWire hvis; have hseed := seedPin_ss _ _ _ _ _ _ _ hP; refine ⟨zprk_pin_ss _ _ _ hseed, ?_⟩
  cases hq : parsePreKeyWire CompRPlantWire.sentWireBytes with
  | none => have h := sentMac8; rw [hq] at h; cases h
  | some q₀ =>
    obtain ⟨_, hm₁⟩ := split38_forall2_vis_inv hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len hvis; obtain ⟨_, _, _, hmsg⟩ := encVis_split38_pins CompRX0SS38.sentWireBytes_len hq hm₁; have hm8 := sentMac8; rw [hq] at hm8; exact zfull_pin_ss _ _ _ _ _ hseed (msgPin_ss _ _ _ _ _ hk hu1 ((CompRX0NBSC38Wire.gamma_encWire_mac_of_encOut hmsg).2.trans (Option.some.inj hm8)))
theorem split38CtxPairsAt_qZNodup5_of_take38 {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes]) : Split38CtxPairsAt QZNodup5 w τ wire v t := by
  intro r S g p hfits _ _ pre mid post hb shown cl e c'; dsimp only; intro _ _ hvis hpre hmid hpost hm₀ _ x₁ _ x₂ _ _ _; rw [hτ] at hvis; obtain ⟨hP, hF⟩ := split38_zpins_ss hfits.1.1.1 hpre hmid hpost hm₀ hvis
  show (((zeroSaltedTermsStA _ _ cl _).take 5).map (gamma compI0 S g)).Nodup
  rw [gamma_take5, hP, hF]; exact zChainSS_nodup
theorem split38CtxPairsHB_qZNodup5 : Split38CtxPairsHB QZNodup5 :=
  split38CtxPairsAt_qZNodup5_of_take38 CompRX0SS38.highBitComp_take38
theorem split38CtxPairsTC_qZNodup5 : Split38CtxPairsTC QZNodup5 :=
  split38CtxPairsAt_qZNodup5_of_take38 CompRX0SS38.torsionComp_take38
theorem split38PairsHB_qTagged_of_min (hPre : Split38CtxPairsHB QPreUntaggedNX) (hC : NonInj38CensusHB) : Split38PairsHB QTagged := taggedW_of_partsT (split38CtxPairsAt_qZInjT_of_nodup split38CtxPairsHB_qZNodup5) (split38CtxPairsAt_mono qPreUntagged_of_nx hPre) (ctxNonInjOffZ_of_census hC)
theorem split38PairsTC_qTagged_of_min (hPre : Split38CtxPairsTC QPreUntaggedNX) (hC : NonInj38CensusTC) : Split38PairsTC QTagged := taggedW_of_partsT (split38CtxPairsAt_qZInjT_of_nodup split38CtxPairsTC_qZNodup5) (split38CtxPairsAt_mono qPreUntagged_of_nx hPre) (ctxNonInjOffZ_of_census hC)
theorem nbscHighBitComp_of_weak (hT : Split38PairsHB QTagged) (hU : Split38PairsHB QUntagged) : Census443Defs.NbscHighBitComp' := CompRNbsc38VT.nbscHighBitComp_of_classVT (split38VT_of_weak hT hU)
theorem nbscTorsionComp_of_weak (hT : Split38PairsTC QTagged) (hU : Split38PairsTC QUntagged) : Census443Defs.NbscTorsionComp' := CompRNbsc38VT.nbscTorsionComp_of_classVT (split38VT_of_weak hT hU)

theorem split38_zpins_ss_split {r : Records} {S : Sem} {g : Ghost} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl e c' : Nat} {blk₁ : List MachineEvent} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c'))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) (hcs₁ : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) (hvis : List.Forall₂ (EventMatchesEntry compI0 r S g) ((.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) (runVis r (pre ++ Move.aliceStart r.alice r.bob 4 6 hb shown :: mid ++ Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some (e, c')) :: post))) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let tr₂ := (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next tr₁)).1; let stA := iniAliceStartState tr₁ r.bob o;
    gamma compI0 S g (zprkT stA) = zprk0SS ∧
      gamma compI0 S g (zfullT tr₂ stA cl (tr₂.length + 2)) = zfull0SS := by
  dsimp only
  obtain ⟨hk, hP, _, _, hu1, _⟩ := CompC3RestPre38HB.split38_encMac_chain_split (r := r) (S := S) (g := g) hNe hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' CompRX0SS38.sentWireBytes_len wireMacChainOk_sentWire hcs₁ hvis
  have hseed := seedPin_ss _ _ _ _ _ _ _ hP
  refine ⟨zprk_pin_ss _ _ _ hseed, ?_⟩
  cases hq : parsePreKeyWire CompRPlantWire.sentWireBytes with
  | none => have h := sentMac8; rw [hq] at h; cases h
  | some q₀ =>
    obtain ⟨_, hm₁⟩ := CompC3RestPre38HB.split38_forall2_vis_inv_split hNe rfl hpre hmid hpost hm₀ CompRX0SS38.rsT_len CompC3RestPre38HB.rsT_kind' hvis
    obtain ⟨_, _, hmsg⟩ := CompC3RestPre38HB.encVis_split38_pins_split hcs₁ CompRX0SS38.sentWireBytes_len hq hm₁
    have hm8 := sentMac8; rw [hq] at hm8
    exact zfull_pin_ss _ _ _ _ _ hseed (msgPin_ss _ _ _ _ _ hk hu1 ((CompRX0NBSC38Wire.gamma_encWire_mac_of_encOut hmsg).2.trans (Option.some.inj hm8)))

theorem split38CtxPairsAt_qZNodup5_of_split {w : PQXDHSpqrSetup} {τ : List MachineEvent} {wire : HwBytes} {v : Fin 4} {t : Fin 8} {blk₁ : List MachineEvent} (hcs₁ : Cli.CoinSplit [.pt CompRX0SS38.ptB, .rng CompRX0SS38.cB, .send CompRPlantWire.sentWireBytes] blk₁) (hτ : τ = (.recv CompRX0SS38.bunBytes :: .rng CompRX0SS38.b0Bytes :: CompRX0SS38.rsT) ++ blk₁) : Split38CtxPairsAt QZNodup5 w τ wire v t := by
  intro r S g p hfits _ _ pre mid post hb shown cl e c'
  dsimp only
  intro _ _ hvis hpre hmid hpost hm₀ _ x₁ _ x₂ _ _ _
  rw [hτ] at hvis
  obtain ⟨hP, hF⟩ := split38_zpins_ss_split hfits.1.1.1 hpre hmid hpost hm₀ hcs₁ hvis
  show (((zeroSaltedTermsStA _ _ cl _).take 5).map (gamma compI0 S g)).Nodup
  rw [gamma_take5, hP, hF]
  exact zChainSS_nodup
end Symbolic.BugInjection.Proofs.Common443.CompC3Nbsc38HB
