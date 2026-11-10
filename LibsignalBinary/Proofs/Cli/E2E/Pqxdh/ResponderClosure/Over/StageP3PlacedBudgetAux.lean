/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ChainClone3ExtPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3Prev1ErrPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Record.FetchDecrypt
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.StageP3Gen
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SerializeBodyAux.Helpers
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Placed Stage P3 Clone Assembly, Envelopes, and Zero-Cap Tail Helpers

Assembles `cloneGen_vregs_placed_ok` (`+0x1778 → cloneExitPCPlaced st msgVer`) across `SessionStructure::clone`
Segments 1–5, defines the Stage P3 Over-path spatial dispatch bundles and allocation envelopes
(`StageP3VerNePrev1Env`, `StageP3Prev1Env`), and proves zero-capacity error-tail helpers.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (SessionState SignalMessage SignalProtocolError)
open CryptoVerification (
  LibsignalPlacement lsmpl lsρ withLsCodeLoaded
)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalSessionRepr (VecGhost)
open CryptoVerification.LibsignalTripleRatchetRepr (
  AddrGhost SessionGhost SignalMessageGhost TailVecGhost
  protocolAddressAt sessionStateAt signalMessageAt vecResultAt
)
open CryptoVerification.LibsignalTripleRatchet (rootStack)
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (
  DropSessionStructureGhost lsLogOff
)
open CryptoVerification.LibsignalTripleRatchet.Record (CloneRel)
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts (words6At)
open CryptoVerification.LibsignalPublicApi.StoreKit (LibsignalCodeRoLoaded)
open CryptoVerification.E2E.Pqxdh.ResponderClosure (
  ClosureCalleeSaved decryptPrekeySavedRegsAt
)
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (
  decryptPrekeySavedRegsAt_add_cd0 dropSessionStructure2Stack eq_of_sep_emp outPtr48_split_eq
  repack20_32_64_64_to_64_64_32 sp370_36_err_fold words3_repack_w32_2w64_w32
)
open CryptoVerification.CliHandshake.RespClosurePlaced (lsProg_518)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3 (genP3SpillAll)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a4 (sessionStateAt_entails_pure_sep)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (
  LsTokenInitM3 dpClosureEntryM3Placed dpClosureEntryVerPlaced
)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over (
  intro_lsro_decryptionFailed_zero_placed overScratch stageP3Sub5ExtraPrePrev1
)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents FreeOnlyEvs RustCliAllocBudget SeqEnv
  fitsEvents_append rustAllocEvents rustCliAllocBudgetSpec
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChainsPlacedBudget (
  CloneChainsEnv cloneChainsEvents cloneChains_vregs_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudget (
  CloneKeysFrontEnv cloneKeysFrontEvents cloneKeysFront_vregs_placed_ok genP3PrePlacedBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlacedBudgetAux (
  optSenderChainCloneEvents sepWPp_bind_frame_any sepWPp_done_any sepWPp_exists_elim_any
  sepWPp_pure_elim_any sepWPp_weaken_frame_any sepWPp_weaken_pre_any
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysTailPlacedBudget (
  CloneKeysTailEnv cloneAliceEvents cloneKeysTailEvents cloneKeysTail_vregs_placed_ok clonePqEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackBasePlacedBudget (
  genP3PostPlacedBudget
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePackPlacedBudget (
  clonePack_vregs_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingPlacedBudget (
  ClonePendingEnv clonePendingEvents clonePendingKyberEvents clonePending_vregs_placed_ok
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.ClonePendingStepsPlacedBudget (
  clonePendingPreKeyEvents
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudget (
  CloneGenVRegsPlacedStmt StageP3ErrM3Env stageP3M3TryDecryptEnvArgs
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevCapPlacedBudgetAux (
  bind_sepWP_lscro_steps_m3_placed genP3PostPlaced genP3PrePlaced genP3S5PostFramePlaced
  sepWPp_lift_false_qp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M3PrevErrTopPlacedBudgetAux (
  call_lscl_nopanic_err p3_alloc_2eac_placed_ok p3_err_tail_prev_zero_placed_wp
)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.TailPlacedBudgetAux (
  p3_alloc_33b0_tail_placed_ok sepWPp_add_cro_tail
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.DefsBudget (
  dropSessionStructureLocal2Spec
)
open LibsignalBinary.Proofs.TripleRatchet.FromRecordChainClone.DefsBudget (
  chainCloneEvents senderChainCloneEvents
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (
  FromVPostTdEnv SegCloneEnv TryDecryptEnvArgs optTailCloneEvents segCloneEvents vecCloneEvents
)

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-! ## Budget-Threaded `SessionStructure::clone` Assembly (`cloneGen_vregs_placed_ok`) -/

private theorem optTailCloneEvents_eq_preKey (p : Option TailVecGhost) :
    optTailCloneEvents p = clonePendingPreKeyEvents p := by
  cases p with
  | none => rfl
  | some g =>
    dsimp only [optTailCloneEvents, vecCloneEvents, clonePendingPreKeyEvents]
    cases g.vec.bytes <;> simp

private theorem optTailCloneEvents_eq_kyber (k : Option TailVecGhost) :
    optTailCloneEvents k = clonePendingKyberEvents k := by
  cases k with
  | none => rfl
  | some g =>
    dsimp only [optTailCloneEvents, vecCloneEvents, clonePendingKyberEvents]
    cases g.vec.bytes <;> simp

private theorem vecCloneEvents_eq_alice (v : VecGhost) :
    vecCloneEvents v = cloneAliceEvents v := by
  dsimp only [vecCloneEvents, cloneAliceEvents]
  cases v.bytes <;> simp

private theorem pqCloneEvents_eq (pq : List (BitVec 8)) :
    (if pq.length = 0 then [] else rustAllocEvents pq.length 1) = clonePqEvents pq := by
  dsimp only [clonePqEvents]
  cases pq <;> simp

/-- Decomposes `segCloneEvents recG st` into Segments 1–4 when `0 < recG.localIk.bytes.length`. -/
theorem segCloneEvents_eq_parts (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (hpos : 0 < recG.localIk.bytes.length) :
    segCloneEvents recG st =
      cloneKeysFrontEvents recG st ++
        (cloneChainsEvents recG st ++
          (clonePendingEvents recG ++ cloneKeysTailEvents recG st)) := by
  have h1 : vecCloneEvents recG.localIk = rustAllocEvents recG.localIk.bytes.length 1 := by
    dsimp only [vecCloneEvents]
    simp [Nat.ne_of_gt hpos]
  have h2 : vecCloneEvents recG.remoteIk =
      (if recG.remoteIk.bytes.length = 0 then []
       else rustAllocEvents recG.remoteIk.bytes.length 1) := rfl
  have h4 :
      (if st.receiverChains = [] then []
       else rustAllocEvents (104 * st.receiverChains.length) 8 ++
         (recG.chains.zip st.receiverChains).flatMap chainCloneEvents) =
      cloneChainsEvents recG st := by
    dsimp only [cloneChainsEvents]
    rw [Nat.mul_comm 104 st.receiverChains.length]
  unfold segCloneEvents cloneKeysFrontEvents clonePendingEvents cloneKeysTailEvents
  rw [h1, h2, h4, optTailCloneEvents_eq_preKey, optTailCloneEvents_eq_kyber,
    vecCloneEvents_eq_alice, pqCloneEvents_eq st.pqRatchetState]
  cases recG.sender <;> cases st.senderChain <;>
    simp only [optSenderChainCloneEvents, List.append_assoc]

set_option maxHeartbeats 800000 in
/-- Budget-threaded `[LibsignalPlacement]` `SessionStructure::clone` specification across
`dpClosureEntryM3Placed + 0x1778 → cloneExitPCPlaced st msgVer` under `SegCloneEnv recG st`. -/
theorem cloneGen_vregs_placed_ok [LibsignalPlacement] : CloneGenVRegsPlacedStmt := by
  intro M A lim ext hshim halloc hmemcpy hcc hscc
    st_b s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
    msgVer rest recG st rem loc msgG msg
    hfits hrc_lt hsp_align hsp_root hcro hpc hrun htr
  have hpre_eq :
      genP3PrePlaced A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s =
      genP3PrePlacedBudget A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur
        msgVer rest recG st rem loc msgG msg s := rfl
  rw [hpre_eq]
  refine sepWPp_weaken_frame_any
    (sessionStateAt_entails_pure_sep A.repAlloc (coroPtr + 0xf8#64) recG st)
    (by dsimp only [genP3PrePlacedBudget]; sep_focus) ?_
  rw [sepConj_assoc]
  refine sepWPp_pure_elim_any fun ⟨_, _, _, _, _, hloc_len, _⟩ => ?_
  have hloc_pos : 0 < recG.localIk.bytes.length := by omega
  refine sepWPp_weaken_pre_any
    (P' := genP3PrePlacedBudget A lim st_b sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
      whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s)
    (Entails.of_eq (by dsimp only [genP3PrePlacedBudget]; sep_ac_rfl)) ?_
  let e1 := cloneKeysFrontEvents recG st
  let e2 := cloneChainsEvents recG st
  let e3 := clonePendingEvents recG
  let e4 := cloneKeysTailEvents recG st
  have hfits_seg : FitsEvents M lim st_b (e1 ++ (e2 ++ (e3 ++ e4))) := by
    rw [← segCloneEvents_eq_parts recG st hloc_pos]
    exact hfits (segCloneEvents recG st) rfl
  obtain ⟨hf1_ev, hf234⟩ := (fitsEvents_append M lim e1 (e2 ++ (e3 ++ e4)) st_b).mp hfits_seg
  let st1 := M.stepEvents e1 st_b
  obtain ⟨hf2_ev, hf34⟩ := (fitsEvents_append M lim e2 (e3 ++ e4) st1).mp hf234
  let st2 := M.stepEvents e2 st1
  obtain ⟨hf3_ev, hf4_ev⟩ := (fitsEvents_append M lim e3 e4 st2).mp hf34
  let st3 := M.stepEvents e3 st2
  let st4 := M.stepEvents e4 st3
  have hf1 : FitsEnv M lim st_b (CloneKeysFrontEnv recG st) := fun _ he => he ▸ hf1_ev
  have hf2 : FitsEnv M lim st1 (CloneChainsEnv recG st) := fun _ he => he ▸ hf2_ev
  have hf3 : FitsEnv M lim st2 (ClonePendingEnv recG) := fun _ he => he ▸ hf3_ev
  have hf4 : FitsEnv M lim st3 (CloneKeysTailEnv recG st) := fun _ he => he ▸ hf4_ev
  have hseg1 := cloneKeysFront_vregs_placed_ok (Qp := fun _ _ => False)
    ext hshim halloc hmemcpy hscc s0 s sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer rest recG st rem loc msgG msg hrc_lt hsp_align hsp_root hf1 hcro hpc hrun htr
  refine sepWPp_bind_frame_any hseg1 (sepConj_emp _).symm
    fun s1 P1 hpc1 hrun1 ⟨_, rfl, hent1, htr1, hcro1, hvregs1⟩ => ?_
  rw [sepConj_emp]
  refine sepWPp_weaken_pre_any hent1 ?_
  have hseg2 := cloneChains_vregs_placed_ok (Qp := fun _ _ => False)
    ext hshim halloc hcc s0 s1 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer rest recG st rem loc msgG msg hrc_lt hsp_align hsp_root hf2 hcro1 hpc1 hrun1 htr1
  refine sepWPp_bind_frame_any hseg2 (sepConj_emp _).symm
    fun s2 P2 hpc2 hrun2 ⟨_, rfl, hent2, htr2, hcro2, hvregs2⟩ => ?_
  rw [sepConj_emp]
  refine sepWPp_weaken_pre_any hent2 ?_
  have hseg3 := clonePending_vregs_placed_ok (Qp := fun _ _ => False)
    ext hshim halloc hmemcpy s0 s2 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer rest recG st rem loc msgG msg hrc_lt hsp_align hsp_root hf3 hcro2 hpc2 hrun2 htr2
  refine sepWPp_bind_frame_any hseg3 (sepConj_emp _).symm
    fun s3 P3 hpc3 hrun3 ⟨_, rfl, hent3, htr3, hcro3, hvregs3⟩ => ?_
  rw [sepConj_emp]
  refine sepWPp_weaken_pre_any hent3 ?_
  have hseg4 := cloneKeysTail_vregs_placed_ok (Qp := fun _ _ => False)
    ext hshim halloc hmemcpy s0 s3 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer rest recG st rem loc msgG msg hrc_lt hsp_align hsp_root hf4 hcro3 hpc3 hrun3 htr3
  refine sepWPp_bind_frame_any hseg4 (sepConj_emp _).symm
    fun s4 P4 hpc4 hrun4 ⟨_, rfl, hent4, htr4, hcro4, hvregs4⟩ => ?_
  rw [sepConj_emp]
  refine sepWPp_weaken_pre_any hent4 ?_
  have hseg5 := clonePack_vregs_placed_ok (A := A) (lim := lim) (stB := st4)
    (Qp := fun _ _ => False)
    ext s0 s4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
    cur msgVer rest recG st rem loc msgG msg hrc_lt hsp_align hsp_root hcro4 hpc4 hrun4 htr4
  refine sepWPp_bind_frame_any hseg5 (sepConj_emp _).symm
    fun s5 P5 hpc5 hrun5 ⟨hent5, htr5, hcro5, hvregs5⟩ => ?_
  rw [sepConj_emp]
  have hst4_eq : st4 = M.stepEvents (segCloneEvents recG st) st_b := by
    rw [segCloneEvents_eq_parts recG st hloc_pos,
        M.stepEvents_append e1 (e2 ++ (e3 ++ e4)) st_b,
        M.stepEvents_append e2 (e3 ++ e4) st1,
        M.stepEvents_append e3 e4 st2]
  have hpost_eq :
      genP3PostPlacedBudget A lim st4 sp fp coroPtr ctxPtr remAddrPtr locAddrPtr
        whisperMsgPtr cur msgVer rest recG st rem loc msgG msg s5 =
      genP3PostPlaced A lim (M.stepEvents (segCloneEvents recG st) st_b)
        sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg s5 := by
    rw [hst4_eq]; rfl
  rw [hpost_eq] at hent5
  exact sepWPp_done_any hpc5 hrun5
    ⟨hent5, htr5, hcro5,
     hvregs5.trans (hvregs4.trans (hvregs3.trans (hvregs2.trans hvregs1)))⟩

/-! ## Spatial Dispatch Bundles and Allocation Envelopes (`previous_sessions = [enc]`) -/

/-- Budget-threaded placed dispatch precondition at `+0x1cd8` over a 1-element `prevVecAt [enc]`. -/
def stageP3DispatchPrePrev1Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s_pool : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr : BitVec 64) (enc : List (BitVec 8))
    (res : Except SignalProtocolError (List (BitVec 8))) (b_2c0 : BitVec 8)
    (G₂ recG : SessionGhost) (st₂ recSt : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchPrePrev1Placed
    (A.atState lim st_b s_pool) s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc res b_2c0
    G₂ recG st₂ recSt

/-- Budget-threaded placed dispatch `Ok(pt)` postcondition at `+0x34dc` over a 1-element `prevVecAt [enc]`. -/
def stageP3DispatchOkMidPrev1Placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ) (s0 s s' : State)
    (coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr : BitVec 64)
    (enc pt : List (BitVec 8)) (b_2c0 : BitVec 8)
    (G₂ : SessionGhost) (st₂ : SessionState (List (BitVec 8))) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.stageP3DispatchOkMidPrev1Placed
    (A.atState lim st_b s') s0 s coroPtr outPtr initErrsPtr prevCap prevPtr ptCap ptPtr enc pt
    b_2c0 G₂ st₂

theorem postTryDecrypt_entails_s5DispatchPrev1_placed [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st_b : M.σ)
    (s0 s s_pool : State)
    (coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
      remAddrPtr locAddrPtr whisperMsgPtr : BitVec 64)
    (enc : List (BitVec 8)) (msgVer : BitVec 32) (b_2c0 : BitVec 8)
    (res : Except SignalProtocolError (List (BitVec 8)))
    (G' recG : SessionGhost) (st₂ st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (coinsPost : SepProp) :
    (LsTokenInitM3 ∗
      sessionStateAt A.repAlloc (s.sp + 0xa90#64) G' st₂ ∗
      vecResultAt A.repAlloc (s.sp + 0x270#64) res ∗
      protocolAddressAt A.repAlloc rem remAddrPtr ∗
      protocolAddressAt A.repAlloc loc locAddrPtr ∗
      signalMessageAt A.repAlloc msgG whisperMsgPtr msg ∗
      coinsPost ∗ lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool lim st_b s_pool) ∗
    (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG st ∗
      memRegion (s.sp + 0x3e0#64) 104 ∗
      ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
      ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗
      ((s.sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
      ((s.sp + 0xb8#64) ↦₃₂ msgVer) ∗
      ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
      ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
      genP3SpillAll s.sp ∗
      stageP3Sub5ExtraPrePrev1 A.repAlloc s0 s coroPtr outPtr initErrsPtr prevCap prevPtr enc
        b_2c0 ∗
      overScratch s.sp) ⊢
    stageP3DispatchPrePrev1Placed A lim st_b s0 s s_pool coroPtr outPtr initErrsPtr prevCap
      prevPtr enc res b_2c0 G' recG st₂ st ∗
    genP3S5PostFramePlaced A s.sp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr msgVer
      rem loc msgG msg coinsPost ∗
    overScratch s.sp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over.postTryDecrypt_entails_s5DispatchPrev1_placed
    (A := A.atState lim st_b s_pool) s0 s coroPtr ctxPtr outPtr initErrsPtr prevCap prevPtr
    remAddrPtr locAddrPtr whisperMsgPtr enc msgVer b_2c0 res G' recG st₂ st rem loc msgG msg
    coinsPost

/-- Allocation event envelope along Stage P3 (`previous_sessions = [enc]`) when `st.version ≠ msgVer`:
`SessionStructure::clone` followed by `verNeEnv enc`. -/
def StageP3VerNePrev1Env (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (enc : List (BitVec 8)) : List AllocEvent → Prop :=
  SeqEnv (SegCloneEnv recG st) (verNeEnv enc)

/-- Combined Stage P3 allocation event envelope over `previous_sessions = [enc]`, covering both
`st.version = msgVer` (`StageP3ErrM3Env`) and `st.version ≠ msgVer` (`StageP3VerNePrev1Env`). -/
def StageP3Prev1Env (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (verNeEnv : List (BitVec 8) → List AllocEvent → Prop)
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (msgVer : BitVec 32) (enc rest : List (BitVec 8)) (evs : List AllocEvent) : Prop :=
  if st.version = msgVer then
    ∃ G₁ : SessionGhost, CloneRel recG G₁ ∧
      StageP3ErrM3Env tdEnv recG G₁ st rem loc msgG msg rest evs
  else
    StageP3VerNePrev1Env verNeEnv recG st enc evs

theorem fitsEnv_segClone_of_stageP3Prev1Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {enc rest : List (BitVec 8)}
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest)) :
    FitsEnv M lim st_b (SegCloneEnv recG st) := by
  intro e1 he1
  refine hfits e1 ?_
  by_cases hver : st.version = msgVer
  · simp only [StageP3Prev1Env, hver, ↓reduceIte]
    exact ⟨recG, ⟨rfl, rfl, rfl, rfl⟩, Or.inl he1⟩
  · simp only [StageP3Prev1Env, hver, ↓reduceIte]
    exact Or.inl he1

theorem fitsEnv_td_of_stageP3Prev1Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {enc rest : List (BitVec 8)}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b)
      (tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest)) := by
  intro e_td htd
  have hfull : StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest
      (segCloneEvents recG st ++ e_td) := by
    simp only [StageP3Prev1Env, hver, ↓reduceIte]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, e_td, rfl, rfl, Or.inl htd⟩⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_td st_b).mp (hfits _ hfull)).2

theorem fitsEnv_postTd_of_stageP3Prev1Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {recG G₁ : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {enc rest : List (BitVec 8)} {evs_td : List AllocEvent}
    (hver : st.version = msgVer) (hcl : CloneRel recG G₁)
    (htd : tdEnv (stageP3M3TryDecryptEnvArgs G₁ st rem loc msgG msg rest) evs_td)
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest)) :
    FitsEnv M lim (M.stepEvents evs_td (M.stepEvents (segCloneEvents recG st) st_b))
      FromVPostTdEnv := by
  intro e_post hpost
  have hfull : StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest
      ((segCloneEvents recG st ++ evs_td) ++ e_post) := by
    simp only [StageP3Prev1Env, hver, ↓reduceIte, List.append_assoc]
    exact ⟨G₁, hcl, Or.inr ⟨segCloneEvents recG st, evs_td ++ e_post, rfl, rfl,
      Or.inr ⟨evs_td, e_post, rfl, htd, hpost⟩⟩⟩
  rw [← M.stepEvents_append (segCloneEvents recG st) evs_td st_b]
  exact ((fitsEvents_append M lim (segCloneEvents recG st ++ evs_td) e_post st_b).mp
    (hfits _ hfull)).2

theorem fitsEnv_verNe_of_stageP3Prev1Env {M : AllocCostModel} {lim : BudgetLimits}
    {st_b : M.σ} {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    {verNeEnv : List (BitVec 8) → List AllocEvent → Prop}
    {recG : SessionGhost} {st : SessionState (List (BitVec 8))}
    {rem loc : AddrGhost} {msgG : SignalMessageGhost} {msg : SignalMessage}
    {msgVer : BitVec 32} {enc rest : List (BitVec 8)}
    (hver : st.version ≠ msgVer)
    (hfits : FitsEnv M lim st_b
      (StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest)) :
    FitsEnv M lim (M.stepEvents (segCloneEvents recG st) st_b) (verNeEnv enc) := by
  intro e_vn hvn
  have hfull : StageP3Prev1Env tdEnv verNeEnv recG st rem loc msgG msg msgVer enc rest
      (segCloneEvents recG st ++ e_vn) := by
    simp only [StageP3Prev1Env, hver, ↓reduceIte]
    exact Or.inr ⟨segCloneEvents recG st, e_vn, rfl, rfl, hvn⟩
  exact ((fitsEvents_append M lim (segCloneEvents recG st) e_vn st_b).mp (hfits _ hfull)).2

/-! ## Zero-Capacity Error-Tail Helpers -/

theorem bind_sepWP_lscro_steps_prev1_placed [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64}
    {s : State} {P P_step : SepProp} {P_step_post : State → SepProp} {F : SepProp}
    {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_step' => (P_step' ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_m3_placed hcro hstep hP hnext

theorem bind_sepWP_lscro_frame_zero_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State} {P P_step : SepProp} {P_step_post : State → SepProp}
    {F : SepProp} {Q_regs : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hstep : SepWP prog mid s P_step (fun sm P_m => (P_m ⊢ P_step_post sm) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeRoLoaded lsmpl sm.mem → Q_regs sm →
      SepWPp prog ret sm (P_step_post sm ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  bind_sepWP_lscro_steps_prev1_placed hcro hstep hP fun sm _ => hnext sm

abbrev intro_lsro_decryptionFailed_zero_placed_budget :=
  @intro_lsro_decryptionFailed_zero_placed

section StageP3ZeroCapTail

attribute [local irreducible] FitsEvents

set_option maxHeartbeats 1200000 in
/-- Budget-threaded zero-capacity common error tail (`lsmpl.base 512 → s0.readReg64 .x30`),
polymorphic in `Qp` and advancing `A.pool` along `FreeOnlyEvs`. -/
theorem stageP3_err_tail_common_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (hDropSS3 : subroutine_ok (lsProg_518 ext) (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec M A lim)))
    (st_b : M.σ) (s0 s : State)
    (coroPtr outPtr errTag prevStatesPtr w0 w1 w2 w3 w4 : BitVec 64)
    (b_2c0 : BitVec 8) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem) (hpc : s.pc = lsmpl.base 512)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx0 : s.readReg64 .x0 = coroPtr + 0xf8#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = (w0.extractLsb' 0 32).zeroExtend 64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64) (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = errTag)
    (hx30 : s.readReg64 .x30 = dpClosureEntryVerPlaced + 0x359c#64) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗ memRegion outPtr 48 ∗
       ((s.sp + 0x370#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗
       ((s.sp + 0x378#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗
       ((s.sp + 0x380#64) ↦₃₂ w2.extractLsb' 32 32) ∗ ((s.sp + 0x384#64) ↦₆₄ w3) ∗
       ((s.sp + 0x38c#64) ↦₆₄ w4) ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
       A.pool lim st_b s ∗ stackAt s.sp dropSessionStructure2Stack)
      (fun sf P_f =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (P_f ⊢ memRegion (coroPtr + 0xf8#64) 344 ∗ ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗ ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗
            ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗ words6At outPtr errTag w0 w1 w2 w3 w4 ∗
            memRegion (s.sp + 0x370#64) 36 ∗ decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
            A.pool lim (M.stepEvents evs st_b) sf ∗ stackAt s.sp dropSessionStructure2Stack) ∧
          sf.sp = s.sp + 0xcd0#64 ∧ sf.trace = s0.trace ∧ ClosureCalleeSaved s0 sf ∧
          LibsignalCodeRoLoaded lsmpl sf.mem ∧ calleeSavedVRegs sf = calleeSavedVRegs s)
      Qp := by
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned] using hsp_align
  refine call_lscl_nopanic_err
    (x := ((⟨coroPtr + 0xf8#64, recG, recSt⟩ : DropSessionStructureGhost), st_b))
    (T := sessionStateAt A.repAlloc (coroPtr + 0xf8#64) recG recSt ∗ A.pool lim st_b s ∗
          stackAt s.sp dropSessionStructure2Stack)
    hcro hDropSS3 hpc hrun hsp_al hx30
    (by dsimp only [dropSessionStructureLocal2Spec])
    (And.intro hx0 (show LibsignalBinary.Proofs.Placed.ElfLsRetAddr.LsRetAddr624 (s.readReg64 .lr) by
      simp (config := { decide := true }) [show s.readReg64 .lr = _ from hx30, wp_norm]))
    (by sep_focus)
    (hnext := fun s1 hpc1 hrun1 hsp1_s _ hcs1 hcro1 => ?_)
  dsimp only [dropSessionStructureLocal2Spec]
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine sepWPp_exists_elim_any fun evs => ?_
  refine sepWPp_pure_elim_any fun ⟨htr1_s, hevs_free⟩ => ?_
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1_s]; exact hsp_align
  rcases hcs1 with ⟨hx19_cs1, _, _, hx22_cs1, _, _, hx25_cs1, hx26_cs1, _, hx28_cs1, _,
    hvregs_cs1⟩
  have hrepack380 := repack20_32_64_64_to_64_64_32 (s.sp + 0x380#64) (w2.extractLsb' 32 32) w3 w4
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack380
  refine sepWPp_weaken_frame_any (Entails.of_eq hrepack380) (by sep_focus) ?_
  refine sepWPp_weaken_frame_any (Entails.of_eq (outPtr48_split_eq outPtr)) (by sep_focus) ?_
  refine sepWPp_weaken_frame_any
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0)) (by sep_focus) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine sepWPp_exists_elim_any fun u_ret2c => sepWPp_exists_elim_any fun u_ret24 =>
    sepWPp_exists_elim_any fun u_ret1c => sepWPp_exists_elim_any fun u_ret14 =>
    sepWPp_exists_elim_any fun u_ret0c => sepWPp_exists_elim_any fun u_ret08 =>
    sepWPp_exists_elim_any fun u_ret0 => ?_
  have hstep2 := p3_err_tail_prev_zero_placed_wp (A := A) (lim := lim) ext (M.stepEvents evs st_b)
    s1 coroPtr outPtr errTag prevStatesPtr
    (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
    (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)
    (w3.extractLsb' 0 32 ++ w2.extractLsb' 32 32)
    (w4.extractLsb' 0 32 ++ w3.extractLsb' 32 32)
    u_ret0 u_ret0c u_ret14 u_ret1c u_ret24
    (s0.readReg64 .x19) (s0.readReg64 .x20) (s0.readReg64 .x21) (s0.readReg64 .x22)
    (s0.readReg64 .x23) (s0.readReg64 .x24) (s0.readReg64 .x25) (s0.readReg64 .x26)
    (s0.readReg64 .x27) (s0.readReg64 .x28) (s0.readReg64 .x29) (s0.readReg64 .x30)
    (w0.extractLsb' 0 32) (w4.extractLsb' 32 32) u_ret08 u_ret2c b_2c0
    hpc1 hrun1 hsp1_align (hx19_cs1.trans hx19) (hx22_cs1.trans hx22)
    (by rw [hx25_cs1, hx25, hsp1_s]) (hx26_cs1.trans hx26) (hx28_cs1.trans hx28)
  simp only [hsp1_s] at hstep2
  refine bind_sepWP_lscro_frame_zero_placed hcro1 hstep2 (by sep_focus)
    fun sf hpcf hrunf hcrof hregsf => ?_
  rcases hregsf with ⟨hspf_s, htrf_1, hvregs_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f,
    hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, _⟩
  refine sepWPp_weaken_frame_any (Entails.of_eq hrepack380.symm) (by sep_focus) ?_
  refine sepWPp_weaken_frame_any
    (sp370_36_err_fold s.sp (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32) w3 w4 (w2.extractLsb' 32 32))
    (by sep_focus) ?_
  have hrepack_out1c := (repack20_32_64_64_to_64_64_32 (outPtr + 0x1c#64)
    (w2.extractLsb' 32 32) w3 w4).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out1c
  refine sepWPp_weaken_frame_any (Entails.of_eq hrepack_out1c) (by sep_focus) ?_
  have hrepack_out8 := (words3_repack_w32_2w64_w32 (outPtr + 0x8#64) w0 w1 w2).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack_out8
  refine sepWPp_weaken_frame_any (Entails.of_eq hrepack_out8) (by sep_focus) ?_
  refine sepWPp_weaken_frame_any
    (Entails.of_eq (decryptPrekeySavedRegsAt_add_cd0 s.sp s0).symm) (by sep_focus) ?_
  have hout_words :
      ((outPtr + 0x0#64) ↦₆₄ errTag) ∗ ((outPtr + 0x8#64) ↦₆₄ w0) ∗
      ((outPtr + 0x10#64) ↦₆₄ w1) ∗ ((outPtr + 0x18#64) ↦₆₄ w2) ∗
      ((outPtr + 0x20#64) ↦₆₄ w3) ∗ ((outPtr + 0x28#64) ↦₆₄ w4) ⊢
      words6At outPtr errTag w0 w1 w2 w3 w4 := by
    unfold words6At; rw [BitVec.add_zero]; exact Entails.refl _
  refine sepWPp_weaken_frame_any hout_words (by sep_focus) ?_
  have hstk_eq : stackAt s.sp dropSessionStructure2Stack =
      stackAt s.sp dropSessionStructure2Stack := rfl
  exact sepWPp_done_any hpcf hrunf ⟨evs, hevs_free,
    Entails.of_eq (eq_of_sep_emp (by sep_focus)),
    hspf_s, htrf_1.trans (htr1_s.trans htr),
    ⟨hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f,
      True.intro⟩,
    hcrof, hvregs_f.trans hvregs_cs1⟩

set_option maxHeartbeats 800000 in
/-- Total-correctness 17-byte error-string allocation at `dpClosureEntryVerPlaced + 0x33b0`. -/
theorem p3_alloc_33b0_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (st_b : M.σ) (s : State) (F : SepProp)
    (hfits17 : FitsEvents M lim st_b (rustAllocEvents 17 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryVerPlaced + 0x33b0#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryVerPlaced + 0x33b4#64) s
      ((A.pool lim st_b s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool lim (M.stepEvents (rustAllocEvents 17 1) st_b) s2 ∗
                stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp := by
  intro R hm hL
  have hwp := sepWPp_add_cro_tail hcro
    (p3_alloc_33b0_tail_placed_ok (Qp := Qp) ext halloc st_b hfits17 s F hL hpc hrun
      hsp_align hx0 hx1)
  rcases hwp R hm hL with ⟨s2, hsteps,
    ⟨hpc2, hrun2, P_f, hmf, ⟨hPf, hoom, hsp2, htr2, hcs, _⟩, hcro2⟩ | hpan | hoom⟩
  · exact ⟨s2, hsteps, Or.inl ⟨hpc2, hrun2, P_f, hmf, hPf, hoom, hsp2, htr2, hcs, hcro2⟩⟩
  · exact ⟨s2, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨s2, hsteps, Or.inr (Or.inr hoom)⟩

set_option maxHeartbeats 800000 in
/-- Total-correctness 17-byte error-string allocation at `dpClosureEntryM3Placed + 0x2eac`. -/
theorem p3_alloc_2eac_zero_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Qp : State → SepProp → Prop}
    (ext : String → Option (State → State))
    (halloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustCliAllocBudgetSpec M A lim false))
    (st_b : M.σ) (s : State) (F : SepProp)
    (hfits17 : FitsEvents M lim st_b (rustAllocEvents 17 1))
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x2eac#64) (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 17#64) (hx1 : s.readReg64 .x1 = 1#64) :
    SepWPp (lsProg_518 ext) (dpClosureEntryM3Placed + 0x2eb0#64) s
      ((A.pool lim st_b s ∗ stackAt s.sp allocHookStack) ∗ F)
      (fun s2 P_f =>
        (P_f ⊢ (A.live (s2.readReg64 .x0) 17 1 ∗ memRegion (s2.readReg64 .x0) 17 ∗
                A.pool lim (M.stepEvents (rustAllocEvents 17 1) st_b) s2 ∗
                stackAt s.sp allocHookStack) ∗ F) ∧
        s2.readReg64 .x0 ≠ 0#64 ∧ s2.sp = s.sp ∧ s2.trace = s.trace ∧
        CalleeSavedPreserved s s2 ∧ LibsignalCodeRoLoaded lsmpl s2.mem)
      Qp :=
  sepWPp_lift_false_qp
    (p3_alloc_2eac_placed_ok ext halloc st_b s F hfits17 hcro hpc hrun hsp_align hx0 hx1)

end StageP3ZeroCapTail

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP3PlacedBudgetAux
