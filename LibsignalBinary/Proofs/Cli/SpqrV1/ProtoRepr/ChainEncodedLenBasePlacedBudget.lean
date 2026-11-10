/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlaced

/-!
# `VmPreserved` Base and `links` Loop Helpers for `Chain::encoded_len [local#3]` (Block `485`)

Proves `VmPreserved`-threaded `Epoch::encoded_len` call and `links` loop lemmas on CLI Block `485`
under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlacedBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification (LibsignalPlacement lsmpl withLsCodeLoaded)
open CryptoVerification.RustHeap (RustAlloc arrayAt)
open CryptoVerification.LibsignalTripleRatchet (tripleRatchetExterns)
open CryptoVerification.LibsignalSpqrV1 (ChainEpochPB)
open CryptoVerification.SpqrV1.ProtoRepr
  (withMemPred EpochEncodedLenFits epochEncodedLenStack chainEpochPBAt
   chainEpochPBEncodedLen chainLinksBodiesEncodedLen ChainHighCalleeSaved)
open CryptoVerification.Cli.SpqrV1.ProtoRepr (IsChainEncLenPlacedEntry)
open CryptoVerification.Cli.SpqrV1.ProtoRepr.Placed (lsProg_485 blkPl_485)
open LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
  (withVmPreserved epochEncodedLenSpec chainEncodedLenPinnedSpec chainEncodedLenSpec)

def ChainEncodedLenLocal1PinnedPlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_485 H) (blkPl_485).base
    (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A))

def ChainEncodedLenLocal1PlacedOkX [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_485 H) (blkPl_485).base
    (withLsCodeLoaded lsmpl (chainEncodedLenSpec A))

def ChainEncodedLenLocal1PinnedPlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_485 (Rust.withPanics ext))
    (blkPl_485).base (withLsCodeLoaded lsmpl (chainEncodedLenPinnedSpec A))

def ChainEncodedLenLocal1PlacedOkExt [LibsignalPlacement] (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (lsProg_485 (Rust.withPanics ext))
    (blkPl_485).base (withLsCodeLoaded lsmpl (chainEncodedLenSpec A))

def ChainEncodedLenLocal1PinnedPlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal1PinnedPlacedOkExt A (tripleRatchetExterns C ctl abs)

def ChainEncodedLenLocal1PlacedOk [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (abs : String → Option (State → State)) : Prop :=
  ChainEncodedLenLocal1PlacedOkExt A (tripleRatchetExterns C ctl abs)

private theorem withMemPred_of_withVmPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {Φ : Memory → Prop} {spec : Spec α}
    (h : subroutine_ok prog entry (withMemPred Φ (withVmPreserved spec))) :
    subroutine_ok prog entry (withMemPred Φ spec) :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) fun _ _ _ _ hq => by
    dsimp only [withMemPred, withVmPreserved] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2

/-- Step `+0x078..+0x07c` (`mov x0, x20; bl epochEntry`) under `DefsBudget.epochEncodedLenSpec A`. -/
theorem step_chain_epoch_call_placed (prog : Program) (A : RustAlloc)
    (entry epochEntry : BitVec 64)
    (hfn : IsChainEncLenPlacedEntry prog entry epochEntry)
    {Φ : Memory → Prop} (hΦ_kf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hepoch : subroutine_ok prog epochEntry (withMemPred Φ (epochEncodedLenSpec A)))
    (ptr : BitVec 64) (ep : ChainEpochPB) (hfit : EpochEncodedLenFits ep)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hpc : s.pc = entry + BitVec.ofNat 64 120)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ptr)
    (hP : P = (chainEpochPBAt A ptr ep ∗ stackAt s.sp epochEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + BitVec.ofNat 64 128 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (chainEpochPBEncodedLen ep) →
      CalleeSavedPreserved s sm →
      s.mem.KeepsFrozen sm.mem →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_epoch_call_placed prog A entry epochEntry hfn
    hΦ_kf (withMemPred_of_withVmPreserved hepoch) ptr ep hfit hΦ hpc hrun hsp_al hx20 hP hnext

/-- Induction over `rem : List ChainEpochPB` (`rem ≠ []`) for the `links` loop (`+0x078..+0x0b4`)
    to `+0x0b8` (`184`) under `DefsBudget.epochEncodedLenSpec A`. -/
theorem step_chain_links_loop_placed (prog : Program) (A : RustAlloc)
    (entry epochEntry : BitVec 64)
    (hfn : IsChainEncLenPlacedEntry prog entry epochEntry)
    {Φ : Memory → Prop} (hΦ_kf : ∀ m m', Φ m → m.KeepsFrozen m' → Φ m')
    (hepoch : subroutine_ok prog epochEntry (withMemPred Φ (epochEncodedLenSpec A)))
    (rem : List ChainEpochPB) (hrem : rem ≠ [])
    (ptr : BitVec 64) (acc totalLen : Nat)
    (hrem_lt : rem.length < 2 ^ 64)
    (hepochs : ∀ ep ∈ rem, EpochEncodedLenFits ep)
    (hfit_loop : acc + chainLinksBodiesEncodedLen rem + totalLen < 2 ^ 64)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hΦ : Φ s.mem)
    (hpc : s.pc = entry + BitVec.ofNat 64 120)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = ptr)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 totalLen)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 acc)
    (hx25 : s.readReg64 .x25 = BitVec.ofNat 64 rem.length)
    (hP : P = (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr rem ∗
      stackAt s.sp epochEncodedLenStack) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = entry + BitVec.ofNat 64 184 →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 →
      sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x22 = s.readReg64 .x22 →
      sm.readReg64 .x8 = BitVec.ofNat 64 (acc + chainLinksBodiesEncodedLen rem + totalLen) →
      ChainHighCalleeSaved s sm →
      SepWPp prog ret sm P Q Qp) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.Cli.SpqrV1.ProtoRepr.step_chain_links_loop_placed prog A entry epochEntry hfn
    hΦ_kf (withMemPred_of_withVmPreserved hepoch) rem hrem ptr acc totalLen hrem_lt hepochs
    hfit_loop hΦ hpc hrun hsp_al hx20 hx23 hx24 hx25 hP hnext

end LibsignalBinary.Proofs.Cli.SpqrV1.ProtoRepr.ChainEncodedLenBasePlacedBudget
