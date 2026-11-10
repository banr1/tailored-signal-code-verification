/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.CorePlacedBudget
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlaced
public import LibsignalBinary.Proofs.TripleRatchet.SpecRestrict
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable Root Theorems for `OutgoingTripleRatchet::encrypt::<Coins>`

Instantiates the budget-threaded relocatable `OutgoingTripleRatchet::encrypt::<Coins>` body proof
(block `428`) under `RustCliAllocBudget M` at unrestricted, empty-PQ-state, and SPQR v1
preconditions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (
  LibsignalPlacement lsLogFilterAddr lsRustDeallocSym ls_subroutine_ok_of_block lsmpl
)
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.CliRatchet.Placed (blkPC_428 blkPl_428)
open CryptoVerification.CliRatchet.SendPlaced (instIsLsBlockProg_427)
open CryptoVerification.LibsignalTripleRatchet (
  OtrEncryptGhost SpqrModel extract_withLsCodeRoLoaded sessionMemcpyRegionSpec
  spqrSendResultAt spqrSendStack subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
  withLsCodeRoLoaded
)
open CryptoVerification.LibsignalTripleRatchet.Encrypt (lsAesEncSym lsFormatInnerSym)
open CryptoVerification.LibsignalTripleRatchetRepr (UuidParser uuidTryParse)
open LibsignalBinary.Heap (
  AllocCostModel AllocEvent BudgetLimits FitsEnv RustCliAllocBudget rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (
  FormatInnerEnv aesEncBudgetSpec formatInnerBudgetEnvSpec withVmPreserved
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudgetAux (
  otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.CorePlacedBudget (
  otrEncrypt_coins_placed_body_ok otrEncrypt_coins_placed_body_ok_frame
)
open LibsignalBinary.Proofs.Cli.TripleRatchet.SpqrSendEmpty.CorePlacedBudget (
  spqrSendCoinsPlacedSpec spqrSendEmptyCoinsPlacedSpec spqrSendEmpty_coins_placed_ok_env
)
open LibsignalBinary.Proofs.TripleRatchet.ChainKey.MessageKeysBudget (messageKeysPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.DefsBudget (
  OtrEncryptEnv SpqrSendBudgetEnv
)
open LibsignalBinary.Proofs.TripleRatchet.Encrypt.CoreStepEnvBudget (nextChainKeyPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.DefsBudget (generateKeysSpec)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget (signalMessageNewSpec)

private theorem spec_pre_pair_true {α β : Type} (spec : Spec (α × β)) :
    { spec with pre := fun (x, st) s => ⌜True⌝ ∗ spec.pre (x, st) s } = spec := by
  have hpre : (fun ((x, st) : α × β) s => ⌜True⌝ ∗ spec.pre (x, st) s) = spec.pre := by
    funext ⟨x, st⟩ s
    simp only [pure_true, emp_sepConj]
  cases spec
  dsimp only at hpre
  rw [hpre]

theorem otrEncryptPlacedSpecQ_true [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    otrEncryptPlacedSpecQ (fun _ => True) C A lim ctl parse S sendEnv =
      otrEncryptPlacedSpec C A lim ctl parse S sendEnv := by
  have hpre :
      (fun ((x, st) : OtrEncryptGhost × M.σ) s =>
        ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
          (CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ
            (fun _ => True) C (A.atState lim st s) ctl parse S).pre x s) =
      (otrEncryptPlacedSpec C A lim ctl parse S sendEnv).pre := by
    funext ⟨x, st⟩ s
    simp only [CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.otrEncryptPlacedSpecQ,
      otrEncryptPlacedSpec, pure_true, emp_sepConj]
  unfold otrEncryptPlacedSpecQ
  rw [hpre]

theorem otrEncrypt_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        (spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs))))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpec C A lim ctl uuidTryParse S SendEnv)) := by
  have h := otrEncrypt_coins_placed_body_ok (fun _ => True) C A lim ctl S SendEnv H
    h_aes h_fmt h_dealloc
    (by simpa only [spec_pre_pair_true] using hSend) hMK hGK hNew hNCK
  rwa [otrEncryptPlacedSpecQ_true] at h

theorem otrEncryptEmpty_coins_placed_ok_of_send_env [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜sc.st.bytes = []⌝ ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ (· = []) C A lim ctl uuidTryParse S SendEnv)) :=
  otrEncrypt_coins_placed_body_ok (· = []) C A lim ctl S SendEnv H
    h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

private theorem spqrSendCoinsPlaced_ro_of_empty [LibsignalPlacement] {M : AllocCostModel}
    {prog : Program} {entry : BitVec 64}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {SendEnv : SpqrSendBudgetEnv}
    (hSendEnv : ∀ rest, SendEnv [] rest [])
    (hSend : subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec M A lim ctl S))) :
    subroutine_ok prog entry
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜sc.st.bytes = []⌝ ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s }) := by
  refine subroutine_ok_outcome_intro fun ⟨x, stB⟩ R s0 hpc hrun hpre hsp => ?_
  obtain ⟨hcro, hpre1⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [spqrSendCoinsPlacedSpec] at hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre1
  obtain ⟨hbs, hpre2⟩ := hpre1
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre2
  obtain ⟨⟨hx0, hx1, _⟩, hmem⟩ := hpre2
  have hpre_e : s0.mem ⊨
      (withLsCodeRoLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec M A lim ctl S)).pre (x, stB) s0 ∗ R := by
    dsimp only [withLsCodeRoLoaded, spqrSendEmptyCoinsPlacedSpec]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hbs, hx0, hx1⟩, hmem⟩
  refine hSend.mono_outcome (x, stB) R s0 hpc hrun hpre_e hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    dsimp only [withLsCodeRoLoaded, spqrSendEmptyCoinsPlacedSpec] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    obtain ⟨⟨hdr, htr, hnp⟩, hpost_mem⟩ := hpost
    dsimp only [withLsCodeRoLoaded, spqrSendCoinsPlacedSpec]
    have hbody : sf.mem ⊨
        (⌜SendEnv x.st.bytes x.rest [] ∧ S.draws x.st.bytes x.rest ≤ x.rest.length ∧
            sf.trace = s0.trace ∧ ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A.repAlloc ∗
          spqrSendResultAt A.repAlloc x.ret (S.send x.st.bytes x.rest) ∗
          cliTapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool lim (M.stepEvents [] stB) sf ∗
          stackAt s0.sp spqrSendStack) ∗ R := by
      dsimp only [AllocCostModel.stepEvents]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hbs ▸ hSendEnv x.rest, hdr, htr, hnp⟩, hpost_mem⟩
    exact Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro [])) hbody
  · right; left; exact ⟨hpan, hpost⟩
  · right; right; left; exact ⟨code, hex, hpost⟩
  · right; right; right; exact ⟨hoom, hpost⟩

theorem otrEncryptEmpty_coins_placed_ok_of_send [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (hSendEnv : ∀ rest, SendEnv [] rest [] := by intro _; rfl)
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec M A lim ctl S)))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ (· = []) C A lim ctl uuidTryParse S SendEnv)) :=
  otrEncryptEmpty_coins_placed_ok_of_send_env C A lim ctl S SendEnv H
    h_aes h_fmt h_dealloc (spqrSendCoinsPlaced_ro_of_empty hSendEnv hSend) hMK hGK hNew hNCK

theorem otrEncryptEmpty_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (hEmpty : S.SendEmptyOk)
    (hSendEnv : ∀ rest, SendEnv [] rest [] := by intro _; rfl)
    (hmc : HookSat H "memcpy" (withVmPreserved sessionMemcpyRegionSpec))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQ (· = []) C A lim ctl uuidTryParse S SendEnv)) := by
  have _ := instIsLsBlockProg_427 H
  have hSend0 := spqrSendEmpty_coins_placed_ok_env A lim ctl S hEmpty
    (E := fun sc evs => SendEnv sc.st.bytes sc.rest evs)
    (fun sc hbs => hbs ▸ hSendEnv sc.rest) hmc
  have hSend := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := (blkPC_428).rebase (blkPl_428).base H) hSend0)
  exact otrEncryptEmpty_coins_placed_ok_of_send_env C A lim ctl S SendEnv H
    h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

theorem otrEncryptV1_coins_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (S : SpqrModel) (SendEnv : SpqrSendBudgetEnv := fun _ _ evs => evs = [])
    (H : String → Option (State → State))
    (h_aes : HookSat H lsAesEncSym (aesEncBudgetSpec C.E M A lim))
    (h_fmt : HookSat H lsFormatInnerSym (formatInnerBudgetEnvSpec M A lim FormatInnerEnv))
    (h_dealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hSend : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 427)
      (withLsCodeRoLoaded lsmpl
        { spqrSendCoinsPlacedSpec M A lim ctl S (fun sc evs => SendEnv sc.st.bytes sc.rest evs) with
          pre := fun (sc, st) s =>
            ⌜sc.st.bytes.length < 2 ^ 32 ∧ 64 ≤ sc.rest.length⌝ ∗ F ∗
              (spqrSendCoinsPlacedSpec M A lim ctl S
                (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).pre (sc, st) s
          post := fun (sc, st) s0 sf =>
            F ∗ (spqrSendCoinsPlacedSpec M A lim ctl S
              (fun sc evs => SendEnv sc.st.bytes sc.rest evs)).post (sc, st) s0 sf }))
    (hMK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 38) (withLsCodeRoLoaded lsmpl (messageKeysPlacedSpec C.F A lim)))
    (hGK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 69) (withLsCodeRoLoaded lsmpl (generateKeysSpec M A lim C.F)))
    (hNew : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 63) (withLsCodeRoLoaded lsmpl (signalMessageNewSpec M A lim C.F uuidTryParse)))
    (hNCK : subroutine_ok ((blkPC_428).rebase (blkPl_428).base H)
      (lsmpl.base 39) (withLsCodeRoLoaded lsmpl (nextChainKeyPlacedSpec C.F))) :
    subroutine_ok ((blkPC_428).rebase (blkPl_428).base H) (blkPl_428).base
      (withLsCodeRoLoaded lsmpl
        (otrEncryptPlacedSpecQF (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length) F
          C A lim ctl uuidTryParse S SendEnv)) :=
  otrEncrypt_coins_placed_body_ok_frame (fun st rest => st.length < 2 ^ 32 ∧ 64 ≤ rest.length) F
    C A lim ctl S SendEnv H h_aes h_fmt h_dealloc hSend hMK hGK hNew hNCK

end LibsignalBinary.Proofs.Cli.TripleRatchet.Encrypt.RootPlacedBudget
