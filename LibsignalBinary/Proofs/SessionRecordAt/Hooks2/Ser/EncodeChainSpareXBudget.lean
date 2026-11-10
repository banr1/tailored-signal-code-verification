/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget
public import LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareVarintXBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg0123XBudget
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg4XBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import ProofLib.SepLogic.WPp

/-!
# Spare-Capacity `encode::<Chain, Vec<u8>>` (Block `12`)

Proves zero-allocation (`evs = []`, `VmPreserved`-preserving, fixed `(x.cap, x.ptr)`) relocatable
contracts (`encodeChainPreallocSpecX` and `encodeChainSpareSpecX`) for Block `12`
(`prost::encoding::message::encode::<Chain, Vec<u8>>`) when
`x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 2000000

namespace LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChainSpareXBudget

open Arm64 ProofLib SepProp
open CryptoGames.LibsignalSession (PublicKey ReceiverChain maxMessageKeys)
open CryptoVerification (
  LibsignalPlacement LibsignalHooks IsLsBlockProg lsmpl withLsCodeLoaded withLsCl
  lsρ lsMemcpySym
  subroutine_ok_withLsCodeLoaded_of_plain
)
open CryptoVerification.RustHeap (RustAlloc vecAt vecU8At)
open CryptoVerification.LibsignalSessionRepr (
  ChainGhost messageKeyAt vecGhostAt optChainKeyAt
)
open CryptoVerification.LibsignalProtoCodec (encodeKey encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (extHookStack ls_subroutine_ok_cl_of_callee)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyBudgetSpec)
open CryptoVerification.E2E.Record (bytesField msgField lenField encChainKey encMessageKey)
open CryptoVerification.E2E.Record.Placed (blkPl_12 lsProg_12 blkPl_88 lsProg_88 blkPl_118 lsProg_118)
open CryptoVerification.E2E.Record.Serialization (
  EncodeChainGhost encChainMem protoChainAt encChainSavedRegs
)
open LibsignalBinary.Heap (VmPreserved AllocCostModel BudgetLimits RustCliAllocBudget)
open LibsignalBinary.Proofs.E2E.Record.Serialization.ChainLenBudget (chainLen_placed_ok)
open LibsignalBinary.Proofs.E2E.Record.Serialization.DefsBudget (chainLenSpec msgKeyLenSpec)
open LibsignalBinary.Proofs.E2E.Record.Serialization.MsgKeyLenBudget (msgKeyLen_placed_ok)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DefsBudget (
  subroutine_ok_withLsCodeLoaded_map_oom'
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.SerDefsXBudget (
  encodeChainStackX SerContractsXPlaced
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.CommonBudget (
  subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg0123XBudget (
  step_encChain_seg0_raw_prealloc_x
  step_encChain_seg1_prealloc_x
  step_encChain_seg2_prealloc_x
  step_encChain_seg3_prealloc_x
)
open LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChain.SpareSeg4XBudget (
  step_encChain_seg4_prealloc_x
  step_encChain_epilogue_prealloc_x
)

/-! ## Specifications -/

/-- Allocator-generic zero-allocation (`VmPreserved`-preserving, fixed `(x.cap, x.ptr)`)
    specification for Block `12` (`prost::encoding::message::encode::<Chain, Vec<u8>>`, tags `6`/`7`)
    under spare capacity `x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat`. -/
def encodeChainPreallocSpecX (A : RustAlloc) : Spec EncodeChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A x.gc x.a ∗
      vecU8At A x.v x.cap x.ptr x.bs ∗
      stackAt s.sp encodeChainStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ VmPreserved s0 sf⌝ ∗
      protoChainAt A x.gc x.a ∗
      vecU8At A x.v x.cap x.ptr (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      stackAt s0.sp encodeChainStackX

/-- Budget-threaded zero-allocation (`evs = []`, unchanged `A.pool lim st` and `(x.cap, x.ptr)`)
    specification for Block `12` (`prost::encoding::message::encode::<Chain, Vec<u8>>`, tags `6`/`7`)
    under spare capacity `x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat`. -/
def encodeChainSpareSpecX (M : AllocCostModel) (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeChainGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x0 = BitVec.ofNat 64 x.tag ∧ s.readReg64 .x1 = x.a ∧ s.readReg64 .x2 = x.v ∧
      (x.tag = 6 ∨ x.tag = 7) ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length ≤ x.cap.toNat ∧
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr x.bs ∗
      A.pool lim st s ∗ stackAt s.sp encodeChainStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      protoChainAt A.repAlloc x.gc x.a ∗
      vecU8At A.repAlloc x.v x.cap x.ptr (x.bs ++ lenField x.tag (encChainMem x.gc)) ∗
      A.pool lim st sf ∗ stackAt s0.sp encodeChainStackX

/-! ## Pure segment decomposition helpers -/

private def chainAtRest (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) : SepProp :=
  ⌜PublicKey.deserialize gc.1.srk.bytes = Except.ok gc.2.senderRatchetKey ∧
    gc.2.messageKeys.length ≤ maxMessageKeys ∧ gc.1.keys.length = gc.2.messageKeys.length⌝ ∗
    vecAt A 104 8 (messageKeyAt A) (a + 48#64) gc.1.mkCap gc.1.mkPtr
      (gc.1.keys.zip gc.2.messageKeys)

private theorem chainAt_eq_fields (A : RustAlloc) (gc : ChainGhost × ReceiverChain) (a : BitVec 64) :
    protoChainAt A gc a =
      vecGhostAt A gc.1.srk a ∗
      vecGhostAt A gc.1.priv (a + 24#64) ∗
      optChainKeyAt A gc.1.ck gc.2.chainKey (a + 72#64) ∗
      chainAtRest A gc a := by
  unfold protoChainAt chainAtRest
  sep_ac_rfl

private theorem encChain_bound_seg1 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length +
      (bytesField 1 x.gc.1.srk.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg2 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes).length +
      (bytesField 2 x.gc.1.priv.bytes).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg3 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes).length +
      (msgField 3 (x.gc.2.chainKey.map encChainKey)).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_bound_seg4 (x : EncodeChainGhost)
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    ((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)).length +
      ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length < 2 ^ 32 := by
  simp only [lenField, encChainMem, List.length_append] at hlen ⊢
  omega

private theorem encChain_final_bytes_eq (x : EncodeChainGhost) :
    (((((x.bs ++ encodeKey x.tag .lengthDelimited ++
      encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ++
      bytesField 1 x.gc.1.srk.bytes) ++
      bytesField 2 x.gc.1.priv.bytes) ++
      msgField 3 (x.gc.2.chainKey.map encChainKey)) ++
      (x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten) =
    x.bs ++ lenField x.tag (encChainMem x.gc) := by
  simp only [lenField, encChainMem, List.append_assoc]

/-! ## Block `12` pre-allocated and spare-capacity theorems -/

/-- Block `12` (`encode::<Chain, Vec<u8>>`) meets `encodeChainPreallocSpecX A` from explicit
    `chainLen` (`Block 88`), `msgKeyLen` (`Block 118`), and `memcpy` contracts. -/
theorem encodeChainPrealloc_placed_ok_ext [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hmc : subroutine_ok (lsProg_12 H) (lsρ lsMemcpySym)
      (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack)))
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (hmk : subroutine_ok (lsProg_118 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A))) :
    subroutine_ok (lsProg_12 H) (lsmpl.base 12)
      (withLsCodeLoaded lsmpl (encodeChainPreallocSpecX A)) := by
  apply subroutine_ok_withLsCodeLoaded_of_sepWPpLsCl
  rintro x R s0 hpc hrun hpre halign_bool
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned, beq_iff_eq] using halign_bool
  refine ⟨(encodeChainPreallocSpecX A).pre x s0, R, hpre, ?_⟩
  dsimp only [encodeChainPreallocSpecX]
  refine Proofs.libsignal.Hooks2.SepWPpLsCl.pure_elim
    fun ⟨hx0, hx1, hx2, htag, hspare, hlen⟩ => ?_
  let L0 := (encodeKey x.tag .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)).length
  let L1 := (bytesField 1 x.gc.1.srk.bytes).length
  let L2 := (bytesField 2 x.gc.1.priv.bytes).length
  let L3 := (msgField 3 (x.gc.2.chainKey.map encChainKey)).length
  let L4 := ((x.gc.2.messageKeys.map fun mk => lenField 4 (encMessageKey mk)).flatten).length
  have hlenField_split :
      (lenField x.tag (encChainMem x.gc)).length = L0 + (L1 + (L2 + (L3 + L4))) := by
    simp only [lenField, encChainMem, L0, L1, L2, L3, L4, List.length_append]
    omega
  have hspare0 : x.bs.length + L0 ≤ x.cap.toNat := by omega
  refine step_encChain_seg0_raw_prealloc_x A H hchain x htag hlen hspare0
    (F := emp) hpc hrun halign hx0 hx1 hx2 (by sep_ac_rfl) ?_
  intro s1 hvm0 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1
  let bs1 := x.bs ++ encodeKey x.tag .lengthDelimited ++
    encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)
  have hbs1_len : bs1.length = x.bs.length + L0 := by
    simp only [bs1, L0, List.length_append, Nat.add_assoc]
  have hspare1 : bs1.length + L1 ≤ x.cap.toNat := by omega
  refine step_encChain_seg1_prealloc_x A H hmc
    x.v x.a x.cap x.ptr s0.sp x.gc.1.srk bs1
    (encChain_bound_seg1 x hlen) hspare1 (s0 := s0)
    (F := vecGhostAt A x.gc.1.priv (x.a + 24#64) ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1
    (by rw [chainAt_eq_fields]; dsimp only [bs1]; sep_ac_rfl) ?_
  intro s2 hvm1 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
  let bs2 := bs1 ++ bytesField 1 x.gc.1.srk.bytes
  have hbs2_len : bs2.length = bs1.length + L1 := by
    simp only [bs2, L1, List.length_append]
  have hspare2 : bs2.length + L2 ≤ x.cap.toNat := by omega
  refine step_encChain_seg2_prealloc_x A H hmc
    x.v x.a x.cap x.ptr s0.sp x.gc.1.priv bs2
    (encChain_bound_seg2 x hlen) hspare2 (s0 := s0)
    (F := vecGhostAt A x.gc.1.srk x.a ∗
      optChainKeyAt A x.gc.1.ck x.gc.2.chainKey (x.a + 72#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc2 hrun2 hsp2 halign htr2 hx19_2 hx20_2
    (by dsimp only [bs2]; sep_ac_rfl) ?_
  intro s3 hvm2 hpc3 hrun3 hsp3 htr3 hx19_3 hx20_3
  let bs3 := bs2 ++ bytesField 2 x.gc.1.priv.bytes
  have hbs3_len : bs3.length = bs2.length + L2 := by
    simp only [bs3, L2, List.length_append]
  have hspare3 : bs3.length + L3 ≤ x.cap.toNat := by omega
  refine step_encChain_seg3_prealloc_x A H hmc
    x.v x.a x.cap x.ptr s0.sp x.gc.1.ck x.gc.2.chainKey bs3
    (encChain_bound_seg3 x hlen) hspare3 (s0 := s0)
    (F := vecGhostAt A x.gc.1.srk x.a ∗
      vecGhostAt A x.gc.1.priv (x.a + 24#64) ∗
      chainAtRest A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 hsp3 halign htr3 hx19_3 hx20_3
    (by dsimp only [bs3]; sep_ac_rfl) ?_
  intro s4 hvm3 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4
  let bs4 := bs3 ++ msgField 3 (x.gc.2.chainKey.map encChainKey)
  have hbs4_len : bs4.length = bs3.length + L3 := by
    simp only [bs4, L3, List.length_append]
  have hspare4 : bs4.length + L4 ≤ x.cap.toNat := by omega
  refine step_encChain_seg4_prealloc_x A H hmc hmk
    x.v x.a x.cap x.ptr s0.sp x.gc bs4
    (encChain_bound_seg4 x hlen) hspare4 (s0 := s0)
    (F := encChainSavedRegs s0.sp s0)
    hpc4 hrun4 hsp4 halign htr4 hx19_4 hx20_4
    (by rw [chainAt_eq_fields]; dsimp only [bs4]; sep_ac_rfl) ?_
  intro s5 hvm4 hpc5 hrun5 hsp5 htr5
  have hvm_all : VmPreserved s0 s5 :=
    hvm0.trans (hvm1.trans (hvm2.trans (hvm3.trans hvm4)))
  exact step_encChain_epilogue_prealloc_x A H hvm_all hpc5 hrun5 hsp5 halign htr5
    (by
      dsimp only [bs4, bs3, bs2, bs1]
      rw [encChain_final_bytes_eq x]
      sep_ac_rfl)

/-- Allocator-generic Block `12` (`encode::<Chain, Vec<u8>>`) pre-allocated contract, instantiating
    `chainLen_placed_ok` and `msgKeyLen_placed_ok`. -/
theorem encodeChainPrealloc_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {H : LibsignalHooks}
    (hmemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ lsMemcpySym)
        (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) :
    subroutine_ok (lsProg_12 H) (lsmpl.base 12)
      (withLsCodeLoaded lsmpl (encodeChainPreallocSpecX A)) :=
  encodeChainPrealloc_placed_ok_ext
    (hmemcpy (callerProg := lsProg_12 H) (callerBlk := 12))
    (chainLen_placed_ok A H)
    (subroutine_ok_withLsCodeLoaded_of_plain (msgKeyLen_placed_ok A H))

theorem encodeChainPrealloc_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_12 H) (lsmpl.base 12)
      (withLsCodeLoaded lsmpl (encodeChainPreallocSpecX A.repAlloc)) :=
  encodeChainPrealloc_placed_ok hC.memcpy

/-- Budget-threaded spare-capacity Block `12` (`encode::<Chain, Vec<u8>>`) contract preserving
    `A.pool lim st` unchanged (`evs = []`). -/
theorem encodeChainSpare_placed_ok_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {H : LibsignalHooks} (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok (lsProg_12 H) (lsmpl.base 12)
      (withLsCodeLoaded lsmpl (encodeChainSpareSpecX M A lim)) := by
  refine subroutine_ok_withLsCodeLoaded_map_oom'
    (encodeChainPrealloc_placed_ok_of_serContractsX hC) ?_
  rintro ⟨x, st⟩ R s0 hpre
  dsimp only [encodeChainSpareSpecX, encodeChainPreallocSpecX] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨hpure, hmem⟩ := hpre
  refine ⟨x, A.pool lim st s0 ∗ R, ?_, ?_, fun _ hoom => ?_⟩
  · rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmem⟩
  · intro sf hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
    obtain ⟨⟨htr, hvm⟩, hmemf⟩ := hpost
    have hpool : A.pool lim st sf = A.pool lim st s0 := A.pool_of_vmPreserved hvm
    refine ⟨htr, ?_⟩
    rw [hpool]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hmemf
  · exfalso
    exact not_satisfies_false_sepConj hoom

theorem encodeChainPrealloc_placed_cl [LibsignalPlacement] {A : RustAlloc}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hmemcpy : ∀ {callerProg : Program} {callerBlk : Nat} [IsLsBlockProg callerProg callerBlk H],
      subroutine_ok callerProg (lsρ lsMemcpySym)
        (withLsCl lsmpl (sessionMemcpyBudgetSpec extHookStack))) :
    subroutine_ok callerProg (lsmpl.base 12)
      (withLsCl lsmpl (encodeChainPreallocSpecX A)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChainPrealloc_placed_ok hmemcpy)

theorem encodeChainPrealloc_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 12)
      (withLsCl lsmpl (encodeChainPreallocSpecX A.repAlloc)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChainPrealloc_placed_ok_of_serContractsX hC)

theorem encodeChainSpare_placed_cl_of_serContractsX [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {callerProg : Program} {callerBlk : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg callerBlk H]
    (hC : SerContractsXPlaced M A lim H) :
    subroutine_ok callerProg (lsmpl.base 12)
      (withLsCl lsmpl (encodeChainSpareSpecX M A lim)) :=
  ls_subroutine_ok_cl_of_callee (callerProg := callerProg)
    (encodeChainSpare_placed_ok_of_serContractsX hC)

end LibsignalBinary.Proofs.SessionRecordAt.Hooks2.Ser.EncodeChainSpareXBudget
