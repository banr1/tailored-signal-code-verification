/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.Layout
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Stage2Lemmas.CommonPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Stage 2 Stack and Key Byte-Split Lemmas

Provides `[LibsignalPlacement]` counterparts of `initArgsAt_eq_sp` and
`initArgsAt_entails_memRegion`, while re-exporting pure layout, `mr_fold`, and key byte-split lemmas
from `Stage2Lemmas/Layout`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas

open Arm64 Arm64.Obj Arm64.Process ProofLib
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.RecordCodecs
open CryptoVerification.E2E
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate

private theorem u64_addr_eq {a b v : BitVec 64} (h : a = b) : (a ↦₆₄ v) = (b ↦₆₄ v) := h ▸ rfl
private theorem u32_addr_eq {a b : BitVec 64} {v : BitVec 32} (h : a = b) : (a ↦₃₂ v) = (b ↦₃₂ v) := h ▸ rfl
private theorem mr_addr_eq {a b : BitVec 64} {n : Nat} (h : a = b) : memRegion a n = memRegion b n := h ▸ rfl

theorem initArgsAtPlaced_eq_sp [LibsignalPlacement] (x : InitGhost) (s0 : State) :
    initArgsAtPlaced (s0.sp - BitVec.ofNat 64 cliInitiateFrame) x s0 =
      ((s0.sp - 7200#64) ↦₆₄ x.peerA) ∗
      ((s0.sp - 7192#64) ↦₆₄ x.meA) ∗
      ((s0.sp - 7184#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
      ((s0.sp - 7176#64) ↦₆₄ lsρ cliSessionVtSym) ∗
      ((s0.sp - 7168#64) ↦₆₄ x.stores) ∗
      ((s0.sp - 7160#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
      ((s0.sp - 7152#64) ↦₆₄ x.bundleA) ∗
      ((s0.sp - 7144#64) ↦₆₄ 0#64) ∗
      ((s0.sp - 7136#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 7132#64) 4 ∗
      ((s0.sp - 7128#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
      ((s0.sp - 7120#64) ↦₆₄ (x.bundleA + 0x78#64)) := by
  dsimp only [initArgsAtPlaced, cliInitiateFrame]
  exact congrArg₂ sepConj (u64_addr_eq (by bv_omega))
    (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
        (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
          (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
            (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
              (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                  (congrArg₂ sepConj (u32_addr_eq (by bv_omega))
                    (congrArg₂ sepConj (mr_addr_eq (by bv_omega))
                      (congrArg₂ sepConj (u64_addr_eq (by bv_omega))
                        (u64_addr_eq (by bv_omega))))))))))))

theorem initArgsAtPlaced_entails_memRegion [LibsignalPlacement] (x : InitGhost) (s0 : State) :
    initArgsAtPlaced (s0.sp - BitVec.ofNat 64 cliInitiateFrame) x s0 ⊢
      memRegion (s0.sp - 7200#64) 88 := by
  rw [initArgsAtPlaced_eq_sp]
  refine mr_fold (s0.sp - 7200#64) (s0.sp - 7192#64) 8 80 88 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7192#64) (s0.sp - 7184#64) 8 72 80 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7184#64) (s0.sp - 7176#64) 8 64 72 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7176#64) (s0.sp - 7168#64) 8 56 64 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7168#64) (s0.sp - 7160#64) 8 48 56 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7160#64) (s0.sp - 7152#64) 8 40 48 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7152#64) (s0.sp - 7144#64) 8 32 40 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7144#64) (s0.sp - 7136#64) 8 24 32 (mr_of_u64 _ _) ?_
  refine mr_fold (s0.sp - 7136#64) (s0.sp - 7132#64) 4 20 24 (mr_of_u32 _ _) ?_
  refine mr_fold (s0.sp - 7132#64) (s0.sp - 7128#64) 4 16 20 (Entails.refl _) ?_
  exact mr_fold (s0.sp - 7128#64) (s0.sp - 7120#64) 8 8 16 (mr_of_u64 _ _) (mr_of_u64 _ _)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.Stage2Lemmas
end
