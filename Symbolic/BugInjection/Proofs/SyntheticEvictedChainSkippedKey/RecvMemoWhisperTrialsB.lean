/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2

/-!
# Fresh-Chain `whisperTrials` Safety

Proves `safeMemo_new_chain_trials`: for every `k ∈ whisperOrReplayIndices` and every prefix state
`i < k`, all `trialTerms` from a newly created receiver chain (`recvChainFor` returning
`some (c, true)`) satisfy `SafeMemo`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsB

open scoped DY.Libsignal.Composed
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

open DY (Bytes)
open DY.DiffieHellman (dhPk)
open DY.Libsignal.TripleRatchet
  (TRState RecvChain lit litByte createChain kdfCk consumeMessageKey
   skippedSeeds findRecvChain recvChainFor maxForwardJumps u32Max)
open DY.Libsignal.Composed.Refinement
  (OpaqueSymbolSemantics Ghost VisEntry TrialCtx trialTerms
   runTrace honestSaltsOf ownKeys plaintextTerms)
open Symbolic.Proofs.Tests.Shared.Composed.Runs (rnd encSig)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvSetup (r0)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDefs
  (whisperOrReplayIndices ssClean)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvDagData
  (dagSize dagOp dagBytes)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoCombinators
  (SafeMemo TermAt)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrials
  (isKdfOp isConcatOp termAt_strLit allSeedTuples safeMemo_of_seedTrialOk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoTrace (pqKeyOf)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoPinsEv0 (sendPtTs)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk0
  (checkDhRand termAt_lit_b termAt_concat_b termAt_dh_b termAt_dh_symm_b
   termAt_kdf_b createChain_dhPk)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalkSend
  (getSendRow SendStepOut)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk1
  (meta0 stateMetas ChainRel StateWitness)
open Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoDagWalk2
  (whisperMsgMeta WhisperPrefixBundle)

abbrev NewChainRow := Nat × Nat × Nat × Bool × Nat × Nat × Nat × Nat × Nat × Nat × Nat

def newChainRows : List NewChainRow := [
  (93, 67, 156, true, 158, 159, 160, 161, 162, 170, 169), (160, 156, 156, false, 208, 209, 210, 211, 212, 214, 213),
  (93, 67, 249, true, 277, 278, 279, 280, 281, 283, 282), (160, 156, 249, true, 251, 252, 253, 254, 255, 263, 262),
  (253, 249, 249, false, 358, 359, 360, 361, 362, 364, 363), (93, 67, 405, true, 433, 434, 435, 436, 437, 439, 438),
  (160, 156, 405, true, 488, 489, 490, 491, 492, 494, 493), (253, 249, 405, true, 407, 408, 409, 410, 411, 419, 418),
  (409, 405, 405, false, 585, 586, 587, 588, 589, 591, 590), (93, 67, 640, true, 668, 669, 670, 671, 672, 674, 673),
  (160, 156, 640, true, 733, 734, 735, 736, 737, 739, 738), (253, 249, 640, true, 796, 797, 798, 799, 800, 802, 801),
  (409, 405, 640, true, 642, 643, 644, 645, 646, 654, 653), (644, 640, 640, false, 907, 908, 909, 910, 911, 913, 912),
  (93, 67, 970, true, 998, 999, 1000, 1001, 1002, 1004, 1003), (160, 156, 970, true, 1069, 1070, 1071, 1072, 1073, 1075, 1074),
  (253, 249, 970, true, 1142, 1143, 1144, 1145, 1146, 1148, 1147), (409, 405, 970, true, 1213, 1214, 1215, 1216, 1217, 1219, 1218),
  (644, 640, 970, true, 972, 973, 974, 975, 976, 984, 983), (974, 970, 970, false, 1340, 1341, 1342, 1343, 1344, 1346, 1345),
  (93, 67, 1411, true, 1439, 1440, 1441, 1442, 1443, 1445, 1444), (160, 156, 1411, true, 1520, 1521, 1522, 1523, 1524, 1526, 1525),
  (253, 249, 1411, true, 1599, 1600, 1601, 1602, 1603, 1605, 1604), (409, 405, 1411, true, 1678, 1679, 1680, 1681, 1682, 1684, 1683),
  (644, 640, 1411, true, 1757, 1758, 1759, 1760, 1761, 1763, 1762), (974, 970, 1411, true, 1413, 1414, 1415, 1416, 1417, 1425, 1424),
  (1415, 1411, 1411, false, 1900, 1901, 1902, 1903, 1904, 1906, 1905), (93, 67, 1979, true, 2007, 2008, 2009, 2010, 2011, 2013, 2012),
  (160, 156, 1979, true, 2094, 2095, 2096, 2097, 2098, 2100, 2099), (253, 249, 1979, true, 2183, 2184, 2185, 2186, 2187, 2189, 2188),
  (409, 405, 1979, true, 2270, 2271, 2272, 2273, 2274, 2276, 2275), (644, 640, 1979, true, 2357, 2358, 2359, 2360, 2361, 2363, 2362),
  (974, 970, 1979, true, 2444, 2445, 2446, 2447, 2448, 2450, 2449), (1415, 1411, 1979, true, 1981, 1982, 1983, 1984, 1985, 1993, 1992),
  (1983, 1979, 1979, false, 2603, 2604, 2605, 2606, 2607, 2609, 2608), (93, 67, 2690, true, 2718, 2719, 2720, 2721, 2722, 2724, 2723),
  (160, 156, 2690, true, 2815, 2816, 2817, 2818, 2819, 2821, 2820), (253, 249, 2690, true, 2910, 2911, 2912, 2913, 2914, 2916, 2915),
  (409, 405, 2690, true, 3005, 3006, 3007, 3008, 3009, 3011, 3010), (644, 640, 2690, true, 3100, 3101, 3102, 3103, 3104, 3106, 3105),
  (974, 970, 2690, true, 3195, 3196, 3197, 3198, 3199, 3201, 3200), (1415, 1411, 2690, true, 3290, 3291, 3292, 3293, 3294, 3296, 3295),
  (1983, 1979, 2690, true, 2692, 2693, 2694, 2695, 2696, 2704, 2703), (2694, 2690, 2690, false, 3465, 3466, 3467, 3468, 3469, 3471, 3470),
  (93, 67, 3560, true, 3588, 3589, 3590, 3591, 3592, 3594, 3593), (160, 156, 3560, true, 3691, 3692, 3693, 3694, 3695, 3697, 3696),
  (253, 249, 3560, true, 3796, 3797, 3798, 3799, 3800, 3802, 3801), (409, 405, 3560, true, 3899, 3900, 3901, 3902, 3903, 3905, 3904),
  (644, 640, 3560, true, 4002, 4003, 4004, 4005, 4006, 4008, 4007), (974, 970, 3560, true, 4105, 4106, 4107, 4108, 4109, 4111, 4110),
  (1415, 1411, 3560, true, 4208, 4209, 4210, 4211, 4212, 4214, 4213), (1983, 1979, 3560, true, 4311, 4312, 4313, 4314, 4315, 4317, 4316),
  (2694, 2690, 3560, true, 3562, 3563, 3564, 3565, 3566, 3574, 3573), (3564, 3560, 3560, false, 4502, 4503, 4504, 4505, 4506, 4508, 4507),
  (93, 67, 4605, true, 4633, 4634, 4635, 4636, 4637, 4639, 4638), (160, 156, 4605, true, 4746, 4747, 4748, 4749, 4750, 4752, 4751),
  (253, 249, 4605, true, 4857, 4858, 4859, 4860, 4861, 4863, 4862), (409, 405, 4605, true, 4968, 4969, 4970, 4971, 4972, 4974, 4973),
  (644, 640, 4605, true, 5079, 5080, 5081, 5082, 5083, 5085, 5084), (974, 970, 4605, true, 5190, 5191, 5192, 5193, 5194, 5196, 5195),
  (1415, 1411, 4605, true, 5301, 5302, 5303, 5304, 5305, 5307, 5306), (1983, 1979, 4605, true, 5412, 5413, 5414, 5415, 5416, 5418, 5417),
  (2694, 2690, 4605, true, 5523, 5524, 5525, 5526, 5527, 5529, 5528), (3564, 3560, 4605, true, 4607, 4608, 4609, 4610, 4611, 4619, 4618),
  (4609, 4605, 4605, false, 5730, 5731, 5732, 5733, 5734, 5736, 5735), (93, 67, 67, false, 5850, 5851, 5852, 5853, 5854, 5856, 5855),
  (253, 249, 67, false, 277, 6059, 6060, 6061, 6062, 6064, 6063), (644, 640, 67, false, 668, 6169, 6170, 6171, 6172, 6174, 6173),
  (1415, 1411, 67, false, 1439, 6279, 6280, 6281, 6282, 6284, 6283), (2694, 2690, 67, false, 2718, 6389, 6390, 6391, 6392, 6394, 6393),
  (4609, 4605, 67, false, 4633, 6499, 6500, 6501, 6502, 6504, 6503), (5845, 5841, 67, false, 6609, 6610, 6611, 6612, 6613, 6615, 6614)
]

def lookupNewChain (rk_id sk_id msg_sk : Nat) :
    Bool × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  match newChainRows.find? (fun r =>
    r.1 == rk_id && r.2.1 == sk_id && r.2.2.1 == msg_sk) with
  | some (_, _, _, sym, dh, prk, rk2, c2, cks, nck, sd) =>
    (sym, dh, prk, rk2, c2, cks, nck, sd)
  | none => (false, 0, 0, 0, 0, 0, 0, 0)

def newChainCheck (k i : Nat) : Bool :=
  let m := stateMetas.getD i meta0
  let msg_ts := (whisperMsgMeta k).1
  let msg_sk := (whisperMsgMeta k).2
  let j := if k = 24 then 0 else (k - 5) / 2 + 2
  let msg_pk := (getSendRow j).pk_id
  let nSalts := if k = 24 then 13 else (k - 5) / 2 + 4
  let pIk_id := if m.isBob then 30 else 31
  let mIk_id := if m.isBob then 31 else 30
  let wire_id := (getSendRow j).wire_id
  m.chains.any (fun cm => decide (cm.ts = msg_ts)) ||
  let (sym, dh_id, prk_id, rk2_id, c2_id, cks_id, nck_id, seed_id) :=
    lookupNewChain m.rk_id m.sk_id msg_sk
  (if sym then checkDhRand m.sk_id m.pk_id msg_sk msg_pk dh_id m.dhs_ts msg_ts
   else checkDhRand msg_sk msg_pk m.sk_id m.pk_id dh_id msg_ts m.dhs_ts) &&
  (decide (prk_id < dagSize) && isKdfOp (dagOp prk_id) m.rk_id dh_id) &&
  (decide (rk2_id < dagSize) && isKdfOp (dagOp rk2_id) prk_id 16) &&
  (decide (c2_id < dagSize) && isConcatOp (dagOp c2_id) rk2_id 17) &&
  (decide (cks_id < dagSize) && isKdfOp (dagOp cks_id) prk_id c2_id) &&
  (decide (seed_id < dagSize) && isKdfOp (dagOp seed_id) cks_id 2) &&
  (decide (nck_id < dagSize) && isKdfOp (dagOp nck_id) cks_id 3) &&
  decide ((nSalts, seed_id, pIk_id, mIk_id, wire_id) ∈ allSeedTuples)

private theorem all_new_chains_ok :
    whisperOrReplayIndices.all (fun k =>
      (List.range k).all (fun i => newChainCheck k i)) = true := by
  decide +kernel

private theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hr _ ih =>
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨_, List.mem_cons_self, hr⟩
    · obtain ⟨x, hx, hrx⟩ := ih hy'
      exact ⟨x, List.mem_cons_of_mem _ hx, hrx⟩

private theorem consumeMessageKey_zero_zero {c : RecvChain} (h0 : c.index = 0) :
    consumeMessageKey c 0 =
      some ((kdfCk c.chainKey).2, { c with chainKey := (kdfCk c.chainKey).1, index := 1 }) := by
  unfold consumeMessageKey
  rw [h0]
  have h1 : ¬ ((0 : UInt32) < 0) := by decide
  have h3 : ¬ ((0 : UInt32) = u32Max) := by decide
  simp only [h1, h3, ↓reduceIte, Nat.sub_self]
  rfl

private theorem skippedSeeds_zero_zero {c : RecvChain} (h0 : c.index = 0) :
    skippedSeeds c 0 = [] := by
  unfold skippedSeeds
  rw [h0]
  rfl

theorem safeMemo_new_chain_trials
    {cls : Nat → Nat} {spqrIdxs : Nat → UInt32} {k i : Nat}
    {S : OpaqueSymbolSemantics} {g : Ghost} {vis : List VisEntry}
    {ls ls₀ : DY.PersistentLocalState.LocalState TRState}
    {sSt : TRState}
    (hk : k ∈ whisperOrReplayIndices)
    (wb : WhisperPrefixBundle cls spqrIdxs k S g vis)
    (hi : i < k)
    (sw : StateWitness S g (plaintextTerms vis) ls ls₀ (stateMetas.getD i meta0))
    (hsSt_dhs : sSt.dhs = rnd (whisperMsgMeta k).1 32)
    (hsSt_ns : sSt.ns = 0)
    (hout : SendStepOut (cls := cls) S g (plaintextTerms vis) sSt
      (if k = 24 then 0 else (k - 5) / 2 + 2)) :
    let j := if k = 24 then 0 else (k - 5) / 2 + 2
    let msg := encSig sSt (rnd (sendPtTs j + 1) (cls j))
      (pqKeyOf sSt (cls j) (sendPtTs j)) (rnd (sendPtTs j) 32)
    let st := ls.state
    let tr := runTrace r0 (ssClean cls spqrIdxs k)
    let salts := honestSaltsOf r0 (ssClean cls spqrIdxs k)
    let own := ownKeys r0 tr st msg
    let newCtxs :=
      (match recvChainFor st.toDRState msg.ratchetKey with
       | some (c, true) => [c]
       | _ => []).map fun c =>
        match consumeMessageKey c msg.counter with
        | none =>
          ({ peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
             ownSalts := [], seed? := none } : TrialCtx)
        | some (seed, c') =>
          { peerIk := st.peerIk, myIk := st.myIk,
            extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
            ownSalts := own, seed? := some seed }
    ∀ ctx ∈ newCtxs,
      ∀ t ∈ trialTerms salts msg ctx,
        SafeMemo dagSize dagOp dagBytes S g (plaintextTerms vis) t := by
  intro j msg st tr salts own newCtxs ctx hctx t ht
  set pts := plaintextTerms vis
  set m := stateMetas.getD i meta0
  set msg_ts := (whisperMsgMeta k).1
  set msg_sk := (whisperMsgMeta k).2
  obtain ⟨c, hc_mem, hctx_eq⟩ := List.mem_map.mp hctx
  have hmsg_rk : msg.ratchetKey = dhPk (rnd msg_ts 32) := by
    change dhPk sSt.dhs = dhPk (rnd msg_ts 32)
    rw [hsSt_dhs]
  have hmsg_ctr : msg.counter = 0 := hsSt_ns
  rw [sw.hdr, hmsg_rk] at hc_mem
  unfold recvChainFor at hc_mem
  have ⟨hfind_none, hc_def⟩ :
      findRecvChain ls₀.state.recv (dhPk (rnd msg_ts 32)) = none ∧
      c = { ratchetKey := dhPk (rnd msg_ts 32),
            chainKey := (createChain ls₀.state.rk (dhPk (rnd msg_ts 32)) ls₀.state.dhs).2,
            index := 0, rIdx := ls₀.state.rIdx + 2 } := by
    cases hfind : findRecvChain ls₀.state.recv (dhPk (rnd msg_ts 32)) with
    | some _ => rw [hfind] at hc_mem; cases hc_mem
    | none =>
      rw [hfind] at hc_mem
      dsimp only at hc_mem
      cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder (dhPk (rnd msg_ts 32)) with
      | true => rw [hlo] at hc_mem; cases hc_mem
      | false =>
        rw [hlo] at hc_mem
        simp only [Bool.false_eq_true, ↓reduceIte] at hc_mem
        rw [List.mem_singleton] at hc_mem
        exact ⟨rfl, hc_mem⟩
  have hany_false : m.chains.any (fun cm => decide (cm.ts = msg_ts)) = false := by
    rw [Bool.eq_false_iff]
    intro hany
    obtain ⟨cm, hcm_mem, hts_dec⟩ := List.any_eq_true.mp hany
    have hts_eq : cm.ts = msg_ts := of_decide_eq_true hts_dec
    obtain ⟨c₀, hc₀_mem, hcr⟩ := forall₂_mem_right sw.hchains hcm_mem
    have hrk_eq : c₀.ratchetKey = dhPk (rnd msg_ts 32) := hts_eq ▸ hcr.1
    unfold findRecvChain at hfind_none
    have hneq := List.find?_eq_none.mp hfind_none c₀ hc₀_mem
    rw [hrk_eq, beq_self_eq_true] at hneq
    exact hneq rfl
  have hchk := List.all_eq_true.mp
    (List.all_eq_true.mp all_new_chains_ok k hk) i (List.mem_range.mpr hi)
  unfold newChainCheck at hchk
  change (m.chains.any (fun cm => decide (cm.ts = msg_ts)) || _) = true at hchk
  rw [hany_false, Bool.false_or] at hchk
  rcases hlk : lookupNewChain m.rk_id m.sk_id msg_sk with
    ⟨sym, dh_id, prk_id, rk2_id, c2_id, cks_id, nck_id, seed_id⟩
  rw [hlk] at hchk
  dsimp only at hchk
  simp only [Bool.and_eq_true] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨hdh_chk, hprk_lt, hprk_op⟩, hrk2_lt, hrk2_op⟩, hc2_lt, hc2_op⟩,
    hcks_lt, hcks_op⟩, hseed_lt, hseed_op⟩, hnck_lt, hnck_op⟩, htup_dec⟩ := hchk
  have htup := of_decide_eq_true htup_dec
  have tsk_st : TermAt dagSize dagOp dagBytes S g pts (rnd m.dhs_ts 32) m.sk_id :=
    sw.hdhs_eq ▸ sw.t_dhs
  have tpk_st : TermAt dagSize dagOp dagBytes S g pts (dhPk (rnd m.dhs_ts 32)) m.pk_id :=
    sw.hdhs_eq ▸ sw.t_pk
  have tdh : TermAt dagSize dagOp dagBytes S g pts
      (DY.DiffieHellman.dh (dhPk (rnd msg_ts 32)) (rnd m.dhs_ts 32)) dh_id := by
    cases sym
    · exact termAt_dh_b hdh_chk wb.t_msg_sk wb.t_msg_pk tsk_st tpk_st
    · exact termAt_dh_symm_b hdh_chk tsk_st tpk_st wb.t_msg_sk wb.t_msg_pk
  have tb01 : TermAt dagSize dagOp dagBytes S g pts (litByte 1) 2 :=
    termAt_lit_b (id := 2) (by decide +kernel)
  have tb02 : TermAt dagSize dagOp dagBytes S g pts (litByte 2) 3 :=
    termAt_lit_b (id := 3) (by decide +kernel)
  have twrlbl : TermAt dagSize dagOp dagBytes S g pts (lit "WhisperRatchet") 10 :=
    termAt_strLit (by decide) (by decide +kernel)
  have twri1 := termAt_concat_b (id := 16) (by decide +kernel) twrlbl tb01
  have twri2 := termAt_concat_b (id := 17) (by decide +kernel) twrlbl tb02
  have tprk := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨hprk_lt, hprk_op⟩) sw.t_rk tdh
  have trk2 := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨hrk2_lt, hrk2_op⟩) tprk twri1
  have tc2 := termAt_concat_b (Bool.and_eq_true_iff.mpr ⟨hc2_lt, hc2_op⟩) trk2 twri2
  have tcks := termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨hcks_lt, hcks_op⟩) tprk tc2
  have t_cck : TermAt dagSize dagOp dagBytes S g pts c.chainKey cks_id := by
    rw [hc_def]; dsimp only
    rw [sw.hdhs_eq, createChain_dhPk ls₀.state.rk (rnd msg_ts 32) (rnd m.dhs_ts 32)]
    exact tcks
  have t_seed : TermAt dagSize dagOp dagBytes S g pts (kdfCk c.chainKey).2 seed_id :=
    termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨hseed_lt, hseed_op⟩) t_cck tb01
  have t_nck : TermAt dagSize dagOp dagBytes S g pts (kdfCk c.chainKey).1 nck_id :=
    termAt_kdf_b (Bool.and_eq_true_iff.mpr ⟨hnck_lt, hnck_op⟩) t_cck tb02
  have hc_idx : c.index = 0 := by rw [hc_def]
  rw [hmsg_ctr, consumeMessageKey_zero_zero hc_idx, skippedSeeds_zero_zero hc_idx] at hctx_eq
  dsimp only at hctx_eq
  subst hctx_eq
  refine safeMemo_of_seedTrialOk htup wb.hsalts ?_ hout.ct.safeMemo ?_ ?_ hout.wire ?_ t ht
  · intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact t_cck.safeMemo
    · rcases List.mem_cons.mp hu' with rfl | hnil
      · exact t_nck.safeMemo
      · cases hnil
  · rw [congrArg (·.peerIk) sw.hdr]; exact sw.t_peerIk
  · rw [congrArg (·.myIk) sw.hdr]; exact sw.t_myIk
  · intro _ hseed; cases hseed; exact t_seed

end Symbolic.BugInjection.Proofs.SyntheticEvictedChainSkippedKey.RecvMemoWhisperTrialsB
