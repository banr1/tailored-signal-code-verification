/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudgetSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.ConsumeMessageKey.Model
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetPoolSync
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
import ProofLib.RegChain

/-!
# `HookSat` Sibling of `TakePathProofs.LoopBudget` (`+0x94 .. +0xb0` & `+0x5e4`)
(`LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudgetSat`)

Weakens `H cmkMemmoveSym = some hookMemmove` in `cmk_remove_0x5e4_placed_outcome` and
`cmk_pos_loop_0x94_placed_outcome` to
`HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack)`, reusing the loop-step
`SepWP` lemmas directly from `LoopBudget`.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudgetSat

open Arm64 ProofLib
open CryptoGames.HMAC (ShaState)
open CryptoGames.LibsignalSession (maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement blkPC_24 blkPl_24 lsLogFilterAddr
)
open CryptoVerification.RustHeap (allocHookStack vecBuf)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost RatchetGhost
  chainKeyBytes consumeMessageKeyResultAt messageKeyAt ratchetAt
)
open CryptoVerification.LibsignalSession (
  ConsumeMessageKeyGhost cmkPreLoopHeap_placed cmkSavedRegs
)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (
  sessionMemmoveBudgetSpec
)
open CryptoVerification.LibsignalSession.TakePath (
  RatchetChainProps chainKeyBytes_entails_memRegion cmkMemmoveSym
  cmk_model_past_hit cmk_model_past_miss_chain
  findIdx_go_step ratchetAt_reassemble_eraseIdx ratchetAt_reassemble_self ratchetChainRest
  sepWP_to_reaches_pc stackAt_7712_split
)
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits FreeOnlyEvs RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (SeamBudget)
open LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.FetchBudget (
  CmkAllocHooks CmkEnv cmkPlacedSpec
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturnBudget (
  cmk_dup_0xb4_placed_outcome cmk_epilogue_77c_placed_outcome
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudget (
  cmk_loop_hit_placed_wp cmk_loop_miss_cont_placed_wp
  cmk_loop_miss_done_placed_wp cmk_loop_miss_head_placed_wp
)
open LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.RemoveBudgetSat (
  cmk_remove_0x5e4_placed_wp_sat
)
open LibsignalBinary.Proofs.HookDischarge.Libc.Memmove (
  hookSat_sessionMemmoveBoundedBudget_of_exact
  hookSat_sessionMemmoveBoundedBudget_of_unbounded
  sessionMemmoveBoundedBudgetSpec
)

private theorem ratchetAt_atState {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    ratchetAt (A.atState lim st s) = ratchetAt A.repAlloc :=
  rfl

theorem cmk_remove_0x5e4_placed_outcome_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st_init st : M.σ}
    (hA : CmkAllocHooks A lim H)
    (hmemmove_sat : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack))
    (x : ConsumeMessageKeyGhost)
    (hsb : SeamBudget M lim (CmkEnv x) st_init st FreeOnlyEvs)
    (R : SepProp) (s0 s : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    {p : Nat} (hp : p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = some p)
    (hc_lt : x.counter < x.ck.index)
    (hpc : s.pc = (blkPl_24).base + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 .x2 =
      BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx24 : s.readReg64 .x24 =
      BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hm : s.mem ⊨
      (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
       ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
         BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
       vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
         (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
       ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool lim st s) ∗ R) :
    reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
      (cmkPlacedSpec F A lim) (x, st_init) R s0 s := by
  set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := x.G.chains[ci]
  set c := x.st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  have hm_pre : s.mem ⊨
      (A.pool lim st s ∗
       stackAt (s0.sp - 480#64) allocHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion x.ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks) ∗
      (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
       ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
       cmkSavedRegs s0.sp s0 ∗ R) := by
    rw [stackAt_7712_split (s0.sp - 480#64)] at hm
    have hm1 := Satisfies.mono
      (sepConj_mono_left
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left (chainKeyBytes_entails_memRegion x.ckA x.ck)))))))) hm
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, hx29_1, htr1, evs, hfree, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_remove_0x5e4_placed_wp_sat hA hmemmove_sat g.mkCap g.mkPtr chAddr x.ret gks p hp
        st s0 s hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
      hm_pre hL
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
  have hzip_len : gks.length = c.messageKeys.length := by
    simp [gks, hkl]
  have hp_c : p < c.messageKeys.length := by omega
  have hgks_snd : gks[p].2 = c.messageKeys[p] := by
    simp [gks, List.getElem_zip]
  have hmodel := cmk_model_past_hit F x hci hi hp_c hfind hc_lt
  set g' : ChainGhost := { g with keys := g.keys.eraseIdx p }
  set G' : RatchetGhost := x.G.setChain ci g'
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A.repAlloc x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A.repAlloc x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool lim (M.stepEvents evs st) s1 ∗ R) := by
    rw [hmodel, ← hgks_snd, stackAt_7712_split (s0.sp - 480#64)]
    have hreassemble := ratchetAt_reassemble_eraseIdx A.repAlloc x.self x.G x.st hi hgi hprops hp
    have hm1'' : s1.mem ⊨
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
          ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr (gks.eraseIdx p) ∗
          ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi) ∗
        (stackAt (s0.sp - 480#64) allocHookStack ∗
          stackAt (s0.sp - 480#64 - 4096#64) 3616 ∗
          memRegion (s0.sp - 480#64) 384 ∗
          cmkSavedRegs s0.sp s0 ∗
          consumeMessageKeyResultAt A.repAlloc x.ret (.ok gks[p].2) ∗
          (x.theirA ↦ₛ x.their.bytes.toList) ∗
          memRegion x.ckA 36 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          A.pool lim (M.stepEvents evs st) s1 ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1'
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
      (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hnpan : (x.model F).1 ≠ .error .panic := by
    rw [hmodel]; intro h; cases h
  have htouch : x.touched F = some ci := by
    unfold ConsumeMessageKeyGhost.touched; rw [hmodel]; exact hci
  have hG' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouch]
    exact RatchetGhost.AgreeExcept.setChain x.G hgi g' rfl rfl
  have hsb1 : SeamBudget M lim (CmkEnv x) st_init (M.stepEvents evs st) FreeOnlyEvs :=
    hsb.step (fun _ _ h1 h2 => FreeOnlyEvs.append h1 h2) hfree
  exact reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_placed_outcome hsb1 FreeOnlyEvs.nil G' R s0 s1
      hpc1 hrun1 hsp1 hsp1_align (by reg_chain) hnpan hG' hm1_ep)

theorem cmk_pos_loop_0x94_placed_outcome_sat [LibsignalPlacement] {M : AllocCostModel}
    {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {st_init st : M.σ}
    (hA : CmkAllocHooks A lim H)
    (hmemmove_sat : HookSat H cmkMemmoveSym (sessionMemmoveBoundedBudgetSpec allocHookStack))
    (x : ConsumeMessageKeyGhost)
    (hsb : SeamBudget M lim (CmkEnv x) st_init st FreeOnlyEvs)
    (R : SepProp) (s0 : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length)
    (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    (hc_lt : x.counter < x.ck.index) :
    ∀ (rem p : Nat) (s : State),
      rem = (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - p →
      p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) =
        List.findIdx?.go (fun k => k.counter == x.counter)
          (x.st.receiverChains[ci].messageKeys.drop p) p →
      s.pc = (blkPl_24).base + 148#64 →
      s.status = .Running →
      s.sp = s0.sp - 480#64 →
      s.spAligned = true →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      s.readReg64 .x2 =
        BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104) →
      s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 →
      s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) →
      s.readReg64 .x20 = x.counter.zeroExtend 64 →
      s.readReg64 .x22 = x.ret →
      s.readReg64 .x24 =
        BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      s.readReg64 .x27 = BitVec.ofNat 64 p →
      s.readReg64 .x28 = x.ck.index.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      (s.mem ⊨
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool lim st s) ∗ R) →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H)
        (cmkPlacedSpec F A lim) (x, st_init) R s0 s := by
  intro rem
  induction rem with
  | zero =>
    intro p s hrem hp
    omega
  | succ k ih =>
    intro p s hrem hp hfind hpc hrun hsp hsp_align htrace
      hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29 hm
    set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
    set g := x.G.chains[ci]
    set c := x.st.receiverChains[ci]
    set gks := g.keys.zip c.messageKeys
    have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
    have hzip_len : gks.length = c.messageKeys.length := by
      simp [gks, hkl]
    have hp_c : p < c.messageKeys.length := by omega
    have hgks_snd : gks[p].2 = c.messageKeys[p] := by
      simp [gks, List.getElem_zip]
    have hm_vec : s.mem ⊨
        vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks ∗
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
         ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
         ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗
         A.pool lim st s ∗ R) :=
      Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm
    by_cases heq : gks[p].2.counter = x.counter
    · have hfind_some : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = some p := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = true := by
          rw [← hgks_snd]; exact beq_iff_eq.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hvm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_hit_placed_wp (A := A) g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1' : s1.mem ⊨
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool lim st s1) ∗ R := by
        have hm1_0 := Satisfies.mono (sepConj_mono_left hP1) hm1
        rw [← A.pool_transport lim st s s1 hvm1] at hm1_0
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1_0
      exact reaches_outcome_steps hsteps1
        (cmk_remove_0x5e4_placed_outcome_sat hA hmemmove_sat x hsb R s0 s1 hci hi hgi hprops hp
          hfind_some hc_lt hpc1 hrun1 hsp1 hsp1_align (by reg_chain)
          hx2_1 hx8_1 hx19_1 hx22_1 hx24_1 hx29_1 hm1')
    · have hfind_next :
          c.messageKeys.findIdx? (fun k => k.counter == x.counter) =
            List.findIdx?.go (fun k => k.counter == x.counter)
              (c.messageKeys.drop (p + 1)) (p + 1) := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = false := by
          rw [← hgks_snd]; exact beq_eq_false_iff_ne.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hvm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_miss_head_placed_wp (A := A) g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1_emp : s1.mem ⊨
          emp ∗
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
           ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗
           (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗
           memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗
           A.pool lim st s1 ∗ R) := by
        have hm1_0 := Satisfies.mono (sepConj_mono_left hP1) hm1
        rw [← A.pool_transport lim st s s1 hvm1] at hm1_0
        exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm1_0
      have hL1 : ((blkPC_24).rebase (blkPl_24).base H).CodeLoaded s1.mem :=
        hsteps1.codeLoaded hL
      by_cases hp1 : p + 1 < gks.length
      · have hmax_gks : gks.length ≤ maxMessageKeys := by
          rw [hzip_len]; exact hprops.mk_max
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hvm2, hsp2, hsp2_align,
          hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_cont_placed_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1 hmax_gks s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2' : s2.mem ⊨
            (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
             ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
             vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks ∗
             ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi ∗
             (x.theirA ↦ₛ x.their.bytes.toList) ∗
             (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
             memRegion x.ret 88 ∗
             (lsLogFilterAddr ↦₆₄ 0#64) ∗
             stackAt (s0.sp - 480#64) 7712 ∗
             memRegion (s0.sp - 480#64) 384 ∗
             cmkSavedRegs s0.sp s0 ∗
             A.pool lim st s2) ∗ R := by
          have hm2_0 := Satisfies.mono (sepConj_mono_left hP2) hm2
          rw [← A.pool_transport lim st s1 s2 hvm2] at hm2_0
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2_0
        exact reaches_outcome_steps (hsteps1.trans hsteps2)
          (ih (p + 1) s2 (by omega) hp1 hfind_next hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain)
            hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')
      · have hp1_eq : p + 1 = gks.length := by omega
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hvm2, hsp2, hsp2_align,
          hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_done_placed_wp g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1_eq s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2_pre : s2.mem ⊨ cmkPreLoopHeap_placed (A.atState lim st s2) x s0 ∗ R := by
          unfold cmkPreLoopHeap_placed
          rw [ratchetAt_atState, RustCliAllocBudget.atState_pool]
          have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
          rw [← A.pool_transport lim st s1 s2 hvm2] at hm2'
          have hreassemble := ratchetAt_reassemble_self A.repAlloc x.self x.G x.st hi hgi hprops
          have hm2'' : s2.mem ⊨
              (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗
                ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
                vecBuf A.repAlloc 104 8 (messageKeyAt A.repAlloc) g.mkCap g.mkPtr gks ∗
                ratchetChainRest A.repAlloc x.self x.G x.st ci hgi hi) ∗
              ((x.theirA ↦ₛ x.their.bytes.toList) ∗
                (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
                memRegion x.ret 88 ∗
                (lsLogFilterAddr ↦₆₄ 0#64) ∗
                stackAt (s0.sp - 480#64) 7712 ∗
                memRegion (s0.sp - 480#64) 384 ∗
                cmkSavedRegs s0.sp s0 ∗
                A.pool lim st s2 ∗ R) :=
            Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hm2'
          exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl))
            (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
        have hfind_none : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
          rw [hfind_next, List.drop_eq_nil_of_le (by omega), List.findIdx?.go]
        have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
        exact reaches_outcome_steps (hsteps1.trans hsteps2)
          (cmk_dup_0xb4_placed_outcome x hsb R s0 s2 hpc2 hrun2 hsp2 hsp2_align
            (by reg_chain) hx20_2 hx22_2 hx28_2 hmodel hm2_pre)

end LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.LoopBudgetSat
