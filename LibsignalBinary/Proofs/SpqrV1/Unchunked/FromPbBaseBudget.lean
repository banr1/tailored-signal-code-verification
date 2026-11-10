/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
public import LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBase
public import LibsignalBinary.Heap.IfaceBudgetLemmas

/-!
# Budget-Threaded Specifications for `<Ct1Sent>::from_pb` and `<EkSentCt1Received>::from_pb`

Defines allocator event envelopes (`Ct1SentFromPbPreEnv`, `Ct1SentFromPbPostEnv`,
`EkSentCt1ReceivedFromPbPreEnv`, `EkSentCt1ReceivedFromPbPostEnv`) and `RustCliAllocBudget`
`[LibsignalPlacement]` specifications.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget

open Arm64 ProofLib
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalPlacement blkPC_339 blkPl_339 blkPC_348 blkPl_348)
open CryptoVerification.LibsignalSpqrV1
  (ProtoAuthenticator spqrAuthApi)
open CryptoVerification.SpqrV1.Unchunked
  (ct1SentFromPbStack ekSentCt1ReceivedFromPbStack
   ct1SentResultAt ekSentCt1ReceivedResultAt
   Ct1SentFromPbGhost EkSentCt1ReceivedFromPbGhost)
open CryptoVerification.SpqrV1.Drop
  (protoUnchunkedCt1SentAt protoUnchunkedEkSentCt1ReceivedAt)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs RustCliAllocBudget
   rustAllocEvents)
open LibsignalBinary.Proofs.Placed.ElfLsRetAddr (LsRetAddr624)

abbrev PbCt1Sent :=
  CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.Ct1Sent
abbrev PbEkSentCt1Received :=
  CryptoVerification.LibsignalSpqrV1.V1State.Unchunked.EkSentCt1Received
abbrev ct1SentFromPb :=
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendCt.Ct1Sent.from_pb
abbrev ekSentCt1ReceivedFromPb :=
  CryptoVerification.LibsignalSpqrV1.Unchunked.SendEk.EkSentCt1Received.from_pb

/-! ## Allocator Event Envelopes -/

/-- Exact allocation event sequence emitted by `<spqr::authenticator::Authenticator>::from_pb`
    when cloning `auth.rootKey` and `auth.macKey` (`Vec<u8>::clone` skips allocation on empty
    slices and emits `rustAllocEvents len 1` otherwise). -/
def authFromPbAllocEvents (auth : ProtoAuthenticator) : List AllocEvent :=
  (if auth.rootKey = [] then [] else rustAllocEvents auth.rootKey.length 1) ++
  (if auth.macKey = [] then [] else rustAllocEvents auth.macKey.length 1)

/-- Exact allocation event sequence emitted by `<Ct1Sent>::from_pb`:
    allocates via `<Authenticator>::from_pb` iff length validation succeeds and `pb.auth = some auth`,
    and emits `[]` on every `.error` branch (which only drops input `Vec<u8>` buffers). -/
def ct1SentFromPbAllocEvents (F : ShaCompress) (pb : PbCt1Sent) :
    List AllocEvent :=
  match ct1SentFromPb (spqrAuthApi F) pb, pb.auth with
  | .ok _, some auth => authFromPbAllocEvents auth
  | _, _ => []

/-- Precondition allocation envelope for `<Ct1Sent>::from_pb` (`FitsEnv` checks only allocations;
    subsequent `Drop` calls emit `FreeOnlyEvs` requiring zero `FitsEvents` preconditions). -/
def Ct1SentFromPbPreEnv (F : ShaCompress) (pb : PbCt1Sent)
    (evs : List AllocEvent) : Prop :=
  evs = ct1SentFromPbAllocEvents F pb

/-- Postcondition event envelope for `<Ct1Sent>::from_pb`: the allocation prefix
    `ct1SentFromPbAllocEvents F pb` followed by `FreeOnlyEvs` from dropping consumed protobuf
    `Vec<u8>` buffers. -/
def Ct1SentFromPbPostEnv (F : ShaCompress) (pb : PbCt1Sent)
    (evs : List AllocEvent) : Prop :=
  ∃ evsFree, FreeOnlyEvs evsFree ∧ evs = ct1SentFromPbAllocEvents F pb ++ evsFree

theorem ct1SentFromPbPostEnv_of_nil (F : ShaCompress) (pb : PbCt1Sent) :
    Ct1SentFromPbPostEnv F pb (ct1SentFromPbAllocEvents F pb) :=
  ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩

def ekSentCt1ReceivedFromPbAllocEvents (F : ShaCompress)
    (pb : PbEkSentCt1Received) : List AllocEvent :=
  match ekSentCt1ReceivedFromPb (spqrAuthApi F) pb, pb.auth with
  | .ok _, some auth => authFromPbAllocEvents auth
  | _, _ => []

def EkSentCt1ReceivedFromPbPreEnv (F : ShaCompress)
    (pb : PbEkSentCt1Received) (evs : List AllocEvent) : Prop :=
  evs = ekSentCt1ReceivedFromPbAllocEvents F pb

def EkSentCt1ReceivedFromPbPostEnv (F : ShaCompress)
    (pb : PbEkSentCt1Received) (evs : List AllocEvent) : Prop :=
  ∃ evsFree, FreeOnlyEvs evsFree ∧ evs = ekSentCt1ReceivedFromPbAllocEvents F pb ++ evsFree

theorem ekSentCt1ReceivedFromPbPostEnv_of_nil (F : ShaCompress)
    (pb : PbEkSentCt1Received) :
    EkSentCt1ReceivedFromPbPostEnv F pb (ekSentCt1ReceivedFromPbAllocEvents F pb) :=
  ⟨[], FreeOnlyEvs.nil, (List.append_nil _).symm⟩

/-! ## Budget-Threaded Specifications and Placed Contracts -/

/-- Envelope-parameterized budget-threaded specification of
    `<spqr::v1::unchunked::send_ct::Ct1Sent>::from_pb` (Block `339`). -/
def ct1SentFromPbSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : PbCt1Sent → List AllocEvent → Prop) :
    Spec (Ct1SentFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (PreEnv x.pb) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out 128 ∗
      protoUnchunkedCt1SentAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp ct1SentFromPbStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ct1SentResultAt A.repAlloc x.out
        (ct1SentFromPb (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 128 ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x.pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp ct1SentFromPbStack

def ct1SentFromPbSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (Ct1SentFromPbGhost × M.σ) :=
  ct1SentFromPbSpecOfEnv M A lim F (Ct1SentFromPbPreEnv F) (Ct1SentFromPbPostEnv F)

def Ct1SentFromPbPlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_339).rebase (blkPl_339).base H) (blkPl_339).base
    (ct1SentFromPbSpec M A lim F)

/-- Envelope-parameterized budget-threaded specification of
    `<spqr::v1::unchunked::send_ek::EkSentCt1Received>::from_pb` (Block `348`). -/
def ekSentCt1ReceivedFromPbSpecOfEnv [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress)
    (PreEnv PostEnv : PbEkSentCt1Received → List AllocEvent → Prop) :
    Spec (EkSentCt1ReceivedFromPbGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = x.out ∧ s.readReg64 .x1 = x.pbA ∧
      FitsEnv M lim st (PreEnv x.pb) ∧ LsRetAddr624 (s.readReg64 .lr)⌝ ∗
      memRegion x.out 104 ∗
      protoUnchunkedEkSentCt1ReceivedAt A.repAlloc x.pbA x.pb ∗
      A.pool lim st s ∗ stackAt s.sp ekSentCt1ReceivedFromPbStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      ekSentCt1ReceivedResultAt A.repAlloc x.out
        (ekSentCt1ReceivedFromPb (spqrAuthApi F) x.pb) ∗
      memRegion x.pbA 104 ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x.pb evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp ekSentCt1ReceivedFromPbStack

def ekSentCt1ReceivedFromPbSpec [LibsignalPlacement] (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) (F : ShaCompress) :
    Spec (EkSentCt1ReceivedFromPbGhost × M.σ) :=
  ekSentCt1ReceivedFromPbSpecOfEnv M A lim F
    (EkSentCt1ReceivedFromPbPreEnv F) (EkSentCt1ReceivedFromPbPostEnv F)

def EkSentCt1ReceivedFromPbPlacedOk [LibsignalPlacement] (M : AllocCostModel)
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (F : ShaCompress)
    (H : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_348).rebase (blkPl_348).base H) (blkPl_348).base
    (ekSentCt1ReceivedFromPbSpec M A lim F)

end LibsignalBinary.Proofs.SpqrV1.Unchunked.FromPbBaseBudget
