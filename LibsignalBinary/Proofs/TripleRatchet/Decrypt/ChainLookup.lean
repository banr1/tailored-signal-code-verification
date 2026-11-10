/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.Common
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.ErrTailProof
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChainStack
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.FindChain
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.LoadRatchetProof
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSym
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeysSteps
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.TightTargets

/-!
# Front Segments (`S0`–`S2` & `ErrTail`) of `try_decrypt_with_state`

Umbrella module re-exporting `IdentityKeys`, `LoadRatchetProof`, `FindChain`, `ErrTailProof`, and
`Common` for `IdentityKeysSpec`, `LoadRatchetSpec`, `FindChainSpec`, and `ErrTailSpec`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt

set_option autoImplicit false

theorem LoadRatchetStatePlaced.of_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : LoadRatchetState_placed A ctl x R s0 s) (hro : LibsignalRoLoaded lsmpl s.mem) :
    LoadRatchetStatePlaced (blkPl_131).base A ctl x R s0 s :=
  ⟨h.1, tryDecryptMidMeta_placed.to_placed h.2.1 hro, h.2.2⟩

theorem ErrTailStatePlaced.to_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 e draws R s0 s) :
    ErrTailState_placed A ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced.to_placed h.2.1).1, h.2.2⟩, (tryDecryptMidMetaPlaced.to_placed h.2.1).2⟩

theorem ErrTailStateXPlaced.to_placed [LibsignalPlacement] {A : RustAlloc} {ctl : BitVec 64}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {e : SignalProtocolError} {draws : Nat}
    {R : SepProp} {s0 s : State}
    (h : ErrTailStateXPlaced (blkPl_131).base A ctl x trG tr st1 e draws R s0 s) :
    ErrTailStateX_placed A ctl x trG tr st1 e draws R s0 s ∧ LibsignalRoLoaded lsmpl s.mem :=
  ⟨⟨h.1, (tryDecryptMidMetaPlaced.to_placed h.2.1).1, h.2.2⟩, (tryDecryptMidMetaPlaced.to_placed h.2.1).2⟩

theorem identityKeys_seam_placed_ok [LibsignalPlacement] {C : Crypto}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x R s0 h_pc h_run h_sp_align hpre
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  have hro : LibsignalRoLoaded lsmpl s0.mem := hpre.1.2
  have hpre_cl : s0.mem ⊨ (tryDecryptPlacedSpec C A ctl uuidTryParse S).pre x s0 ∗ R := by
    dsimp only [tryDecryptPlacedSpec, withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hpre.1.1, hpre.2⟩
  refine reaches_pc_mono
    (reaches_pc_lsro_preserve hro
      (@identityKeys_placed_ok _ C A ctl S H h_bb x R s0 h_pc h_run h_sp_align hpre_cl)) ?_
  intro sf _ _ ⟨hS1, hro_f⟩
  exact LoadRatchetStatePlaced.of_placed hS1 hro_f

theorem identityKeys_seam_placed_ok_x [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (h_bb : H lsBlackBoxU8Sym = some blackBoxHook) :
    S0SeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S :=
  fun x R s0 h_pc h_run h_sp_align hpre =>
    @identityKeys_seam_placed_ok _ C A ctl S H h_bb x R s0 h_pc h_run h_sp_align hpre

theorem errTail_seam_placed_ok [LibsignalPlacement] {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    ErrTailSeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S :=
  fun x trG tr st1 e R s0 s he hmod1 hmod2 herr =>
    (errTail_placed_ok hdealloc x trG tr st1 e R s0 s he hmod1 hmod2
      (ErrTailStatePlaced.to_placed herr).1).mono_outcome fun _ hout => hout

theorem errTail_seam_placed_ok_x [LibsignalPlacement] {C : Crypto}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel} {H : String → Option (State → State)}
    (hdealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)) :
    ErrTailSeamXPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C decFn A ctl uuidTryParse S :=
  fun x trG tr st1 e R s0 s he hmod1 hmod2 herr =>
    (errTail_placed_ok_x hdealloc x trG tr st1 e R s0 s he hmod1 hmod2
      (ErrTailStateXPlaced.to_placed herr).1).mono_outcome fun _ hout => hout

end CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup
