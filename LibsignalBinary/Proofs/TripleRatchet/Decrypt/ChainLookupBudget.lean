/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStackBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysStepsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSymBudget
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget

/-!
# Budget-Threaded Front Segments (`S0`–`S2` & `ErrTail`) of `try_decrypt_with_state`

Umbrella module re-exporting `IdentityKeysBudget`, `LoadRatchetProofBudget`, `FindChainBudget`,
`ErrTailProofBudget`, `TightTargetsBudget`, and `CommonBudget`, together with top-level
`S0SeamPlaced` / `S0SeamXPlaced` and `ErrTailSeamPlaced` / `ErrTailSeamXPlaced` entrypoints.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookupBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (Crypto SessionState SignalProtocolError TripleRatchet)
open CryptoVerification
  (LibsignalPlacement LibsignalRoLoaded lsBlackBoxU8Sym lsRustDeallocSym lsmpl)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.LibsignalTripleRatchet (SpqrModel TrGhost TryDecryptGhost)
open CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup (blkPC_131 blkPl_131)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits RustCliAllocBudget rustCliDeallocBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
  (ErrTailSeamPlaced ErrTailSeamXPlaced ErrTailStatePlaced ErrTailStateXPlaced
   LoadRatchetStatePlaced S0SeamPlaced S0SeamXPlaced)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget
  (ErrTailStateX_placed ErrTailState_placed LoadRatchetState_placed)

export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget (
  LoadRatchetStatePlaced_of_placed
  LoadRatchetStatePlaced_to_placed
  FindChainStatePlaced_of_placed
  FindChainStatePlaced_to_placed
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget (
  DhStepStatePlaced_of_placed
  DhStepStatePlaced_to_placed
  ConsumeMsgKeyStatePlaced_of_placed
  ConsumeMsgKeyStatePlaced_to_placed
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.CommonBudget (
  ErrTailStatePlaced_of_placed
  ErrTailStatePlaced_to_placed
  ErrTailStateXPlaced_of_placed
  ErrTailStateXPlaced_to_placed
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget (
  remote_identity_key_placed_ok
  clear_unacknowledged_pre_key_message_placed_ok
  clear_unacknowledged_pre_key_message_placed_ok_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget (
  identityKeys_placed_ok
  identityKeys_placed_ok_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  loadRatchet_placed_ok
  loadRatchet_placed_ok_x
  loadRatchet_placed_okT
  loadRatchet_placed_okT_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  loadRatchet_pinned_placed_ok
  loadRatchet_pinned_placed_ok_x
  loadRatchet_gen_placed_ok
  loadRatchet_gen_placed_ok_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProofBudget (
  loadRatchet_tight_pinned_gen_placed_ok
  loadRatchet_tight_pinned_gen_placed_ok_x
  loadRatchet_pinned_gen_placed_ok
  loadRatchet_pinned_gen_placed_ok_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainBudget (
  findChain_placed_ok
  findChain_placed_ok_x
  findChain_placed_ok_of_bb
  findChain_placed_ok_of_bb_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProofBudget (
  errTail_placed_ok
  errTail_placed_ok_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget (
  loadRatchet_pinned_placed_okT
  loadRatchet_pinned_placed_okT_x
  errTail_placed_okT
  errTail_placed_okT_x
)
export LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget (
  errTail_ok_tight_placed
  errTail_ok_tight_x_placed
)

theorem LoadRatchetStatePlaced.of_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetState_placed A lim st ctl x R s0 s)
    (hro : LibsignalRoLoaded lsmpl s.mem) :
    LoadRatchetStatePlaced (blkPl_131).base A lim st ctl x R s0 s :=
  LoadRatchetStatePlaced_of_placed h hro

theorem ErrTailStatePlaced.to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailState_placed A lim st ctl x trG tr st1 e draws R s0 s ∧
      LibsignalRoLoaded lsmpl s.mem :=
  ErrTailStatePlaced_to_placed h

theorem ErrTailStateXPlaced.to_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateXPlaced (blkPl_131).base A lim st ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A lim st ctl x trG tr st1 e draws R s0 s ∧
      LibsignalRoLoaded lsmpl s.mem :=
  ErrTailStateXPlaced_to_placed h

theorem identityKeys_seam_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget.identityKeys_seam_placed_ok
    h_bb

theorem identityKeys_seam_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysBudget.identityKeys_seam_placed_ok_x
    h_bb

theorem errTail_seam_placed_ok [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C A lim ctl uuidTryParse S tdEnv :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget.errTail_seam_placed_ok
    hdealloc

theorem errTail_seam_placed_ok_x [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    {tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop}
    (hdealloc : HookSat H lsRustDeallocSym (rustCliDeallocBudgetSpec M A lim)) :
    ErrTailSeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      C decFn A lim ctl uuidTryParse S tdEnv :=
  LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargetsBudget.errTail_seam_placed_ok_x
    hdealloc

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookupBudget
