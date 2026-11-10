/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.SpqrSendEmpty.Core
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.SendCodeSym
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable `spqr::send::<Coins>` on Empty PQ State

Proves `spqrSendEmptyCoinsPlacedSpec` for `spqr::send::<signal_session_ratchet::Coins>` (Block `427`)
under `[LibsignalPlacement]` over the CLI `.data`/`.bss` coins tape.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.SpqrSendEmpty
open CryptoVerification.Cli.CoinsTape
open CryptoVerification.CliRatchet.SendPlaced

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-- Relocatable `[LibsignalPlacement]` contract for `spqr::send::<signal_session_ratchet::Coins>`
(Block `427`), using the CLI `.data`/`.bss` coins tape (`cliTapeAt` / `cliTapeAfter`). -/
def spqrSendCoinsPlacedSpec [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) : Spec SendCall where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.st.v⌝ ∗ x.st.at A ∗ memRegion x.ret 72 ∗
      cliTapeAt ctl x.cur x.rest ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s.sp spqrSendStack
  post := fun x s0 sf =>
    ⌜S.draws x.st.bytes x.rest ≤ x.rest.length ∧ sf.trace = s0.trace ∧
        ¬ S.sendPanics x.st.bytes x.rest⌝ ∗ x.st.at A ∗
      spqrSendResultAt A x.ret (S.send x.st.bytes x.rest) ∗
      cliTapeAfter ctl x.cur x.rest (S.draws x.st.bytes x.rest) ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp spqrSendStack
  onPanic := fun x s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ S.sendPanics x.st.bytes x.rest) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- `spqrSendCoinsPlacedSpec` restricted to an empty state (`x.st.bytes = []`). -/
def spqrSendEmptyCoinsPlacedSpec [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) : Spec SendCall :=
  { spqrSendCoinsPlacedSpec A ctl S with
    pre := fun x s => ⌜x.st.bytes = []⌝ ∗ (spqrSendCoinsPlacedSpec A ctl S).pre x s }

theorem spqrSendEmpty_coins_placed_ok_of_memcpy [LibsignalPlacement]
    (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel) (H : String → Option (State → State))
    (hE : S.SendEmptyOk)
    (hmc : subroutine_ok ((blkPC_427).rebase (blkPl_427).base H)
      (lsmpl.ρ "memcpy") sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_427).rebase (blkPl_427).base H) (blkPl_427).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec A ctl S)) := by
  have hdec0 : subroutine_ok ((blkPC_325).rebase (blkPl_325).base H) (lsmpl.base 325)
      (decodeStateEmptySpec A) := decodeStateEmpty_placed_ok A H
  have hdec := ls_subroutine_ok_of_block (callerProg := (blkPC_427).rebase (blkPl_427).base H)
    (subroutine_ok_withLsCodeLoaded_of_plain hdec0)
  simp only [withLsCodeLoaded] at hdec
  have hmc' := memcpyPcs_of_sessionMemcpyRegion hmc
  simp only [withLsCodeLoaded, spqrSendEmptyCoinsPlacedSpec, spqrSendCoinsPlacedSpec, stackAt_spqr]
  simp (config := { maxSteps := 1000000 }) only [sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  obtain ⟨ret, ⟨v, cap, ptr, bs⟩, cur, rest⟩ := x
  dsimp only at *
  subst bs
  apply sepWP_seq_lscl h (mid := lsmpl.base 325)
  wp_steps
  apply SepWP.done
  · wp_norm_lhs
  · wp_norm_lhs
  intro hcl_call
  wp_apply
  wp_simp_pre only [decodeEmpty_split, sepExists_sepConj_left, sepExists_sepConj_right,
    sepConj_assoc]
  apply SepWP.exists_elim; intro d3
  apply SepWP.exists_elim; intro d2
  apply SepWP.exists_elim; intro d1
  wp_steps
  wp_apply
  wp_simp_pre only [ret_split ret, sepExists_sepConj_left, sepExists_sepConj_right]
  apply SepWP.exists_elim; intro r6
  apply SepWP.exists_elim; intro r5
  apply SepWP.exists_elim; intro r4
  apply SepWP.exists_elim; intro r3
  apply SepWP.exists_elim; intro r2
  apply SepWP.exists_elim; intro r1
  apply SepWP.exists_elim; intro r0
  wp_steps
  refine SepWP.fold (dst_fold s0.sp pqChainNone pqInnerNone) (by sep_focus) ?_
  refine SepWP.fold (decode_fold s0.sp 0xFFFFFFFFFFFFFFFF#64 d1 d2 d3 pqChainNone pqInnerNone)
    (by sep_focus) ?_
  refine SepWP.fold (result_fold A ret) (by sep_focus) ?_
  refine SepWP.fold (cliTapeAt_entails_cliTapeAfter_zero ctl cur rest) (by sep_focus) ?_
  simp only [hE.send, hE.draws, hE.noPanic]
  wp_done

theorem spqrSendEmpty_coins_placed_ok [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) {H : String → Option (State → State)} (hE : S.SendEmptyOk)
    (hmc : HookSat H "memcpy" sessionMemcpyRegionSpec) :
    subroutine_ok ((blkPC_427).rebase (blkPl_427).base H) (blkPl_427).base
      (withLsCodeLoaded lsmpl (spqrSendEmptyCoinsPlacedSpec A ctl S)) := by
  obtain ⟨k, hk, hget⟩ := List.getElem_of_mem (by decide : "memcpy" ∈ libsignalSessionExterns)
  exact spqrSendEmpty_coins_placed_ok_of_memcpy A ctl S H hE
    (ls_hook_ok (k := k) (by simp [hk, hget]) hmc)

end CryptoVerification.Cli.LibsignalTripleRatchet.SpqrSendEmpty
