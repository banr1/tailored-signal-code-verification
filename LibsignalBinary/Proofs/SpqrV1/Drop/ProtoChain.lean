/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Drop.Repr
public import LibsignalBinary.Proofs.SpqrV1.Drop.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Drop.DropCodeSym
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Drop Glue for `proto::pq_ratchet::chain::Epoch`, `Chain`, and `Option<Chain>`

Proves subroutine contracts for:
- `core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>` (`0x4cfa8`, Block `288`)
- `core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]` (`0x35530`, Block `136`)
- `core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>` (`0x4c060`, Block `266`)
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L13
open Lean Elab Tactic ProofLib ProofLib.CodeLookup in
elab "code_fetches_len " codeId:ident decPrefix:ident b:term:max H:term:max sym:str len:num : tactic => do
  let codeName ← realizeGlobalConstNoOverloadWithInfo codeId
  let eOff ← lookup codeName .fnOff sym.getString
  let hfn := mkCIdentFrom sym eOff.decl
  let offStx := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic| code_fetches $codeId $decPrefix $b $H $hfn $offStx $len))
end CryptoVerification.SpqrV1.Layout.L13

namespace CryptoVerification.SpqrV1.Drop

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.CodeLayout CryptoVerification.SpqrV1.Layout.L13

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option hygiene false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

@[local simp]
private theorem optEpochDirectionPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 48) := rfl

@[local simp]
private theorem optEpochDirectionPBAt_some (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    optEpochDirectionPBAt A a (some d) = epochDirectionPBAt A a d := rfl

@[local simp]
private theorem optChainPBAt_none (A : RustAlloc) (a : BitVec 64) :
    optChainPBAt A a none = ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) := rfl

@[local simp]
private theorem optChainPBAt_some (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    optChainPBAt A a (some ch) = chainPBAt A a ch := rfl

/-! ## Representation Deallocation Entailments for `ProtoRepr` -/

def epochDirPBHeadersAt (a : BitVec 64) (g : EpochDirectionPBGhost) : SepProp :=
  (a ↦₆₄ g.next.cap) ∗ ((a + 8#64) ↦₆₄ g.next.ptr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ g.prev.cap) ∗ ((a + 32#64) ↦₆₄ g.prev.ptr) ∗ memRegion (a + 40#64) 16

theorem epochDirPBHeadersAt_entails_memRegion_56 (a : BitVec 64) (g : EpochDirectionPBGhost) :
    epochDirPBHeadersAt a g ⊢ memRegion a 56 := by
  unfold epochDirPBHeadersAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 40) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 32) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 24) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 16) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))

theorem vecU8At_entails_capPtr_dealloc_lt (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      ⌜cap.toNat < 2 ^ 63⌝ ∗
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      vecCapPtrDealloc A cap ptr := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader vecCapPtrDealloc
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  apply Entails.pure_right hcap_lt
  have h1 := pointsTo64_entails_memRegion (a + 16#64) (BitVec.ofNat 64 bs.length)
  have h2 : (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ⊢
      (if (cap == 0#64) = true then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) := by
    by_cases hc : cap = 0
    · subst hc; simp only [↓reduceIte, beq_self_eq_true]; exact Entails.refl _
    · have hcb : ¬((cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
      simp only [hc, hcb, ↓reduceIte]; exact Entails.refl _
  rw [sepConj_assoc (a ↦₆₄ cap), sepConj_assoc ((a + 8#64) ↦₆₄ ptr)]
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono h1 h2))

theorem epochDirectionPBAt_entails_dealloc (A : RustAlloc) (a : BitVec 64) (d : EpochDirectionPB) :
    epochDirectionPBAt A a d ⊢
      ∃∗ g : EpochDirectionPBGhost,
        ⌜g.next.cap.toNat < 2 ^ 63⌝ ∗
        epochDirPBHeadersAt a g ∗
        vecCapPtrDealloc A g.next.cap g.next.ptr ∗
        vecCapPtrDealloc A g.prev.cap g.prev.ptr := by
  unfold epochDirectionPBAt rustBytesVecAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro nCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro nPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro pPtr
  refine Entails.sepExists_right ⟨⟨nCap, nPtr⟩, ⟨pCap, pPtr⟩⟩ ?_
  have h1 := vecU8At_entails_capPtr_dealloc_lt A a nCap nPtr d.next
  have h2 := vecU8At_entails_capPtr_dealloc A (a + 24#64) pCap pPtr d.prev
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at h2
  have h3 := pointsTo32_entails_memRegion (a + 48#64) d.ctr
  refine Entails.trans (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono_left h3))) ?_
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  apply Entails.pure_left; intro hcap_lt
  apply Entails.pure_right hcap_lt
  unfold epochDirPBHeadersAt
  dsimp only
  have h48 : memRegion (a + 48#64) 4 ∗ memRegion (a + 52#64) 4 = memRegion (a + 48#64) 8 := by
    rw [← ProofLib.memRegion_split' (b := a + 48#64) (n := 4) (k := 4)
          (b' := a + 52#64) rfl (by bv_omega) (by decide)]
  have h40 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 8 = memRegion (a + 40#64) 16 := by
    rw [← ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 8)
          (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  rw [← h40, ← h48]
  exact Entails.of_eq (by ac_rfl)

theorem optEpochDirectionPBAt_none_entails_memRegion_56 (A : RustAlloc) (a : BitVec 64) :
    optEpochDirectionPBAt A a none ⊢ memRegion a 56 := by
  unfold optEpochDirectionPBAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 48) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

theorem chainEpochPB_regions_entails_112 (cur : BitVec 64) :
    memRegion cur 56 ∗ memRegion (cur + 56#64) 56 ⊢ memRegion cur 112 := by
  rw [ProofLib.memRegion_split' (b := cur) (n := 56) (k := 56) (b' := cur + 56#64) rfl rfl (by decide)]
  exact Entails.refl _

theorem optChainParamsPBAt_entails_memRegion_12 (a : BitVec 64) (p : Option ChainParamsPB) :
    optChainParamsPBAt a p ⊢ memRegion a 12 := by
  cases p with
  | none =>
    unfold optChainParamsPBAt
    rw [ProofLib.memRegion_split' (b := a) (n := 4) (k := 8) (b' := a + 4#64) rfl rfl (by decide)]
    exact sepConj_mono_left (pointsTo32_entails_memRegion a 0#32)
  | some p =>
    unfold optChainParamsPBAt chainParamsPBAt
    have hp : (a + 4#64) + 4#64 = a + 8#64 := by bv_omega
    rw [hp,
        ProofLib.memRegion_split' (b := a) (n := 4) (k := 8) (b' := a + 4#64) rfl rfl (by decide),
        ProofLib.memRegion_split' (b := a + 4#64) (n := 4) (k := 4) (b' := a + 8#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo32_entails_memRegion _ _))

theorem chainPBTail_entails_memRegion_32 (a : BitVec 64) (ch : ChainPB) :
    ((a + 48#64) ↦₆₄ ch.currentEpoch) ∗
      ((a + 56#64) ↦₆₄ ch.sendEpoch) ∗
      optChainParamsPBAt (a + 64#64) ch.params ∗
      ((a + 76#64) ↦₃₂ ch.direction) ⊢
    memRegion (a + 48#64) 32 := by
  rw [ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 24) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 8) (k := 16) (b' := a + 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 64#64) (n := 12) (k := 4) (b' := a + 76#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (optChainParamsPBAt_entails_memRegion_12 _ _)
        (pointsTo32_entails_memRegion _ _)))

theorem chainPBAt_entails_dealloc (A : RustAlloc) (a : BitVec 64) (ch : ChainPB) :
    chainPBAt A a ch ⊢
      ∃∗ g : ChainPBGhost,
        ⌜ch.links.length ≤ g.links.cap.toNat ∧ g.links.cap.toNat * 112 < 2 ^ 63 ∧ g.links.ptr ≠ 0⌝ ∗
        (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        (if g.links.cap = 0 then emp
         else A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
           arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr ch.links ∗
           memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
             ((g.links.cap.toNat - ch.links.length) * 112)) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗
        vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr := by
  unfold chainPBAt chainLinksVecAt vecOf rustBytesVecAt vecU8
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro lCap
  rw [sepExists_sepConj_left]
  apply Entails.sepExists_elim; intro lPtr
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro nrCap
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro nrPtr
  refine Entails.sepExists_right ⟨⟨lCap, lPtr⟩, ⟨nrCap, nrPtr⟩⟩ ?_
  unfold vecAt vecBuf vecHeader chainEpochPBSize
  have hnr := vecU8At_entails_capPtr_dealloc A (a + 24#64) nrCap nrPtr ch.nextRoot
  have ha1 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have ha2 : (a + 24#64) + 16#64 = a + 40#64 := by bv_omega
  rw [ha1, ha2] at hnr
  have htl := chainPBTail_entails_memRegion_32 a ch
  refine Entails.trans
    (Entails.of_eq (show _ =
      (⌜ch.links.length ≤ lCap.toNat ∧ lCap.toNat * 112 < 2 ^ 63 ∧ lPtr ≠ 0⌝ ∗
        ((a ↦₆₄ lCap) ∗ ((a + 8#64) ↦₆₄ lPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length)) ∗
        (if lCap = 0 then emp
         else A.live lPtr (lCap.toNat * 112) 8 ∗
           arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 lPtr ch.links ∗
           memRegion (lPtr + BitVec.ofNat 64 (ch.links.length * 112)) ((lCap.toNat - ch.links.length) * 112)) ∗
        vecU8At A (a + 24#64) nrCap nrPtr ch.nextRoot ∗
        (((a + 48#64) ↦₆₄ ch.currentEpoch) ∗ ((a + 56#64) ↦₆₄ ch.sendEpoch) ∗
         optChainParamsPBAt (a + 64#64) ch.params ∗ ((a + 76#64) ↦₃₂ ch.direction))) by ac_rfl)) ?_
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono hnr htl)))) ?_
  have h40 : memRegion (a + 40#64) 8 ∗ memRegion (a + 48#64) 32 = memRegion (a + 40#64) 40 := by
    rw [← ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 32)
          (b' := a + 48#64) rfl (by bv_omega) (by decide)]
  rw [← h40]
  exact Entails.of_eq (by ac_rfl)

theorem chainPBHeaders_entails_memRegion_80 (a lCap lPtr lLen nrCap nrPtr : BitVec 64) :
    (a ↦₆₄ lCap) ∗ ((a + 8#64) ↦₆₄ lPtr) ∗ ((a + 16#64) ↦₆₄ lLen) ∗
      ((a + 24#64) ↦₆₄ nrCap) ∗ ((a + 32#64) ↦₆₄ nrPtr) ∗ memRegion (a + 40#64) 40 ⊢
    memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 64) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 56) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 48) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 40) (b' := a + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono_left (pointsTo64_entails_memRegion _ _)))))

theorem optChainPBAt_none_entails_memRegion_80 (a : BitVec 64) :
    ((a ↦₆₄ noneCap) ∗ memRegion (a + 8#64) 72) ⊢ memRegion a 80 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 72) (b' := a + 8#64) rfl rfl (by decide)]
  exact sepConj_mono_left (pointsTo64_entails_memRegion a noneCap)

/-! ## Specifications -/

/-- Ghost arguments for `drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>` (`0x4cfa8`). -/
structure DropProtoEpochSliceGhost where
  /-- Slice base pointer (`x0`). -/
  ptr : BitVec 64
  /-- Elements of the slice (`x1 = eps.length`). -/
  eps : List ChainEpochPB

def dropProtoEpochSliceSpec (A : RustAlloc) : Spec DropProtoEpochSliceGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ptr ∧ s.readReg64 .x1 = BitVec.ofNat 64 x.eps.length ∧
      x.eps.length * chainEpochPBSize < 2 ^ 63⌝ ∗
      arrayAt (fun ep addr => chainEpochPBAt A addr ep) chainEpochPBSize x.ptr x.eps ∗
      A.pool ∗ stackAt s.sp dropStack32
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.ptr (x.eps.length * chainEpochPBSize) ∗
      A.pool ∗ stackAt s0.sp dropStack32

/-- Ghost arguments for `drop_glue::<spqr::proto::pq_ratchet::Chain>` (`0x35530`). -/
structure DropProtoSpqrChainGhost where
  /-- Pointer to the 80-byte `spqr::proto::pq_ratchet::Chain` (`x0`). -/
  a : BitVec 64
  /-- Abstract `ChainPB` model value. -/
  ch : ChainPB

def dropProtoSpqrChainSpec (A : RustAlloc) : Spec DropProtoSpqrChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      chainPBAt A x.a x.ch ∗
      A.pool ∗ stackAt s.sp dropStack48
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chainPBSize ∗
      A.pool ∗ stackAt s0.sp dropStack48

/-- Ghost arguments for `drop_glue::<Option<spqr::proto::pq_ratchet::Chain>>` (`0x4c060`). -/
structure DropOptProtoSpqrChainGhost where
  /-- Pointer to the 80-byte `Option<spqr::proto::pq_ratchet::Chain>` (`x0`). -/
  a : BitVec 64
  /-- Abstract `Option ChainPB` model value. -/
  optCh : Option ChainPB

def dropOptProtoSpqrChainSpec (A : RustAlloc) : Spec DropOptProtoSpqrChainGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.a⌝ ∗
      optChainPBAt A x.a x.optCh ∗
      A.pool ∗ stackAt s.sp dropStack80
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      memRegion x.a chainPBSize ∗
      A.pool ∗ stackAt s0.sp dropStack80

/-! ## `drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>` (`0x4cfa8`) -/

local macro "proto_epoch_slice_body_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20
  rcases hpres with ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  unfold chainEpochPBAt
  refine seq_clean (mid := $entry + 88#64) (P_mid :=
    (memRegion cur 56 ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP $prog ($entry + 88#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_left (optEpochDirectionPBAt_none_entails_memRegion_56 A cur))) hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean (mid := $entry + 68#64) (P_mid :=
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gs.next.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
        have hstep2 : SepWP $prog ($entry + 88#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs))) hstep2
  · intro s2 hpc2 hrun2 ⟨⟨hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2⟩
    cases hrecv : ep.recv with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP $prog ($entry + 28#64) s2
          ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A (cur + 56#64)))
          (chainEpochPB_regions_entails_112 cur))) hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A (cur + 56#64) d))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro gr
      wp_focus_pure; intro hcap_lt_r
      have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
      refine seq_clean (mid := $entry + 116#64) (P_mid :=
        (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gr.next.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3⟩
        have hstep4 : SepWP $prog ($entry + 28#64) s3
            ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gr.prev.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
            (chainEpochPB_regions_entails_112 cur))) hstep4))

local macro "proto_epoch_slice_loop_steps " entry:term:max : tactic => `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + 28#64)
      (P_mid := memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = BitVec.ofNat 64 (ep :: tl).length ∧ sm.readReg64 .x20 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s _ hpc hrun hpres hx19 hx20) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1⟩
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx19_1 ⊢
      rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx19_1
      refine seq_clean (mid := $entry + 40#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun sm => Saved32x20Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = BitVec.ofNat 64 (ep2 :: tl2).length ∧ sm.readReg64 .x20 = (cur + 112#64) + 56#64) ?_ ?_
      · rcases hpres1 with ⟨hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_112_add_56]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2⟩
        have hrec := ih (cur + 112#64) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _))

local macro "proto_epoch_slice_main_steps " entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨ptr, eps⟩
  have hx0 : s0.readReg64 .x0 = ptr := h_1
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 eps.length := h_2
  have hlen_lt : eps.length * 112 < 2 ^ 63 := h
  dsimp only [DropProtoEpochSliceGhost.ptr, DropProtoEpochSliceGhost.eps] at *
  cases eps with
  | nil =>
    simp only [List.length_nil, Nat.zero_mul, arrayAt, memRegion_zero, emp_sepConj] at hx1 ⊢
    wp_steps; wp_done
  | cons ep tl =>
    have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
      spAligned_sub s0.sp 32#64 (by assumption) (by decide)
    have hne0 := ofNat_beq_zero_false_112 (n := (ep :: tl).length) (by simp) hlen_lt
    nth_rw 1 [stackAt_dropStack32_split s0.sp]; cells_unfold; wp_pull_exists; wp_steps
    refine seq_clean (mid := $entry + 140#64)
      (P_mid := memRegion ptr ((ep :: tl).length * 112) ∗ A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
        (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved32x20Preserved s0 sm (s0.sp - 32#64)) ?_ ?_
    · have hpre_eq :
          (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)) =
          (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 ptr (ep :: tl) ∗
            A.pool ∗ stackAt (s0.sp - 32#64) allocHookStack ∗
            (((s0.sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
             ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))) := by ac_rfl
      rw [hpre_eq]
      exact hloop s0 (s0.sp - 32#64) hfsp_align (ep :: tl) ptr _ _
        (List.cons_ne_nil _ _) hlen_lt rfl (by assumption)
        ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl rfl
    · intro sm hpcm hrunm ⟨hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
      wp_steps
      refine SepWP.weaken_pre
        (sepConj_mono_right (sepConj_mono_right (stack_restore_32_allocHook s0.sp _ _ _ _))) ?_
      wp_done))

private theorem drop_proto_epoch_slice_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB) (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoEpochSliceName + 40#64 → s.status = .Running →
      Saved32x20Preserved s0 s fsp → s.readReg64 .x19 = cnt → s.readReg64 .x20 = cur + 56#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName + 28#64) s
        (chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropProtoEpochSliceName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" 152
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" = entry
  examples_hide_fetches; proto_epoch_slice_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

private theorem drop_proto_epoch_slice_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 112 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoEpochSliceName + 40#64 → s.status = .Running →
      Saved32x20Preserved s0 s fsp → s.readReg64 .x19 = BitVec.ofNat 64 rest.length → s.readReg64 .x20 = cur + 56#64 →
      SepWP (dropProgAtExt b ext) ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName + 140#64) s
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_proto_epoch_slice_body (b := b) (ext := ext) hdealloc s0 fsp hfsp_align
  dsimp only [dropProgAtExt, dropProtoEpochSliceName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" 152
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" = entry
  examples_hide_fetches; proto_epoch_slice_loop_steps entry

theorem drop_proto_epoch_slice_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName)
      (dropProtoEpochSliceSpec A) := by
  simp only [dropProtoEpochSliceSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoEpochSliceName +
        bv% (ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" "__rustc::__rust_dealloc")
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hloop := drop_proto_epoch_slice_loop (b := b) (ext := ext) hdealloc_raw
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" 152
  dsimp only [dropProgAtExt, dropProtoEpochSliceName, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hloop ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>" = entry
  examples_hide_fetches; proto_epoch_slice_main_steps entry

section PlacedProtoEpochSlice
variable [LibsignalPlacement]
open Blk337_338

private theorem drop_proto_epoch_slice_body_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB) (s : State) (Frame : SepProp),
      s.pc = (blkPl_288).base + 40#64 → s.status = .Running →
      Saved32x20Preserved s0 s fsp → s.readReg64 .x19 = cnt → s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 28#64) s
        (chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp ∧ sm.readReg64 .x19 = cnt ∧ sm.readReg64 .x20 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  proto_epoch_slice_body_steps ((blkPC_288).rebase (blkPl_288).base H) (blkPl_288).base

private theorem drop_proto_epoch_slice_loop_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_288).base + 40#64 → s.status = .Running →
      Saved32x20Preserved s0 s fsp → s.readReg64 .x19 = BitVec.ofNat 64 rest.length → s.readReg64 .x20 = cur + 56#64 →
      SepWP ((blkPC_288).rebase (blkPl_288).base H) ((blkPl_288).base + 140#64) s
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved32x20Preserved s0 sm fsp) := by
  have hbody := drop_proto_epoch_slice_body_placed hdealloc s0 fsp hfsp_align
  proto_epoch_slice_loop_steps (blkPl_288).base

protected theorem drop_proto_epoch_slice_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_288).rebase (blkPl_288).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_288).rebase (blkPl_288).base H) (blkPl_288).base (dropProtoEpochSliceSpec A) := by
  simp only [dropProtoEpochSliceSpec]
  have hloop := drop_proto_epoch_slice_loop_placed hdealloc
  dsimp only [chainEpochPBSize] at *
  proto_epoch_slice_main_steps (blkPl_288).base

end PlacedProtoEpochSlice

/-! ## `drop_glue::<spqr::proto::pq_ratchet::Chain>` (`0x35530`) -/

local macro "proto_spqr_chain_body_steps " prog:term:max entry:term:max : tactic => `(tactic| (
  intro cur cnt ep s Frame hpc hrun hpres hx19 hx20 hx21 hx22
  rcases hpres with ⟨hx23, hx24, hx25, hx26, hx27, hx28, hsp, htrace, hvregs⟩
  unfold chainEpochPBAt
  refine seq_clean (mid := $entry + 96#64) (P_mid :=
    (memRegion cur 56 ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
    A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
    (Q := fun sm => Saved48Preserved s0 sm fsp ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
      sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) ?_ ?_
  · cases hsend : ep.send with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP $prog ($entry + 96#64) s
          (((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ ((cur ↦₆₄ noneCap ∗ memRegion (cur + 8#64) 48) ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (sepConj_mono_left (optEpochDirectionPBAt_none_entails_memRegion_56 A cur))) hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_left (epochDirectionPBAt_entails_dealloc A cur d))) ?_
      rw [sepExists_sepConj_left, sepExists_sepConj_left]; apply SepWP.exists_left; intro gs
      wp_focus_pure; intro hcap_lt_s
      have hne_none_s := cap_add_one_beq_zero_false hcap_lt_s
      refine seq_clean (mid := $entry + 76#64) (P_mid :=
        ((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
          optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gs.next.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp]; ac_rfl) ?_; wp_done
      · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1, hx21_1, hx22_1⟩
        have hstep2 : SepWP $prog ($entry + 96#64) s1
            (((epochDirPBHeadersAt cur gs ∗ vecCapPtrDealloc A gs.prev.cap gs.prev.ptr) ∗
              optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (epochDirPBHeadersAt cur gs ∗ optEpochDirectionPBAt A (cur + 56#64) ep.recv) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gs.prev.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (sepConj_mono_left (epochDirPBHeadersAt_entails_memRegion_56 cur gs))) hstep2
  · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2, hx20_2, hx21_2, hx22_2⟩
    cases hrecv : ep.recv with
    | none =>
      rw [optEpochDirectionPBAt_none]
      have hstep : SepWP $prog ($entry + 36#64) s2
          ((memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
            A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
          (fun sm Pm =>
            (Pm ⊢ (memRegion cur 56 ∗ ((cur + 56#64) ↦₆₄ noneCap ∗ memRegion ((cur + 56#64) + 8#64) 48)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
            Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
            sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
        wp_steps; wp_done
      exact SepWP.strengthen_entails_const
        (sepConj_mono_left (Entails.trans
          (sepConj_mono_right (optEpochDirectionPBAt_none_entails_memRegion_56 A (cur + 56#64)))
          (chainEpochPB_regions_entails_112 cur))) hstep
    | some d =>
      rw [optEpochDirectionPBAt_some]
      refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (epochDirectionPBAt_entails_dealloc A (cur + 56#64) d))) ?_
      rw [sepExists_sepConj_right, sepExists_sepConj_left]; apply SepWP.exists_left; intro gr
      wp_focus_pure; intro hcap_lt_r
      have hne_none_r := cap_add_one_beq_zero_false hcap_lt_r
      refine seq_clean (mid := $entry + 124#64) (P_mid :=
        (memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
        A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) ?_ ?_
      · dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
        by_cases hcap : (gr.next.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps; wp_done
        · wp_steps; wp_apply; refine align_pre (by rw [hsp_2]; ac_rfl) ?_; wp_done
      · intro s3 hpc3 hrun3 ⟨⟨hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3, hx20_3, hx21_3, hx22_3⟩
        have hstep4 : SepWP $prog ($entry + 36#64) s3
            ((memRegion cur 56 ∗ (epochDirPBHeadersAt (cur + 56#64) gr ∗ vecCapPtrDealloc A gr.prev.cap gr.prev.ptr)) ∗
              A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
            (fun sm Pm =>
              (Pm ⊢ (memRegion cur 56 ∗ epochDirPBHeadersAt (cur + 56#64) gr) ∗
                A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
              Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
              sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
          dsimp only [epochDirPBHeadersAt, vecCapPtrDealloc]
          by_cases hcap : (gr.prev.cap == 0#64) = true <;> simp only [hcap, ↓reduceIte, sepConj_emp, emp_sepConj]
          · wp_steps; wp_done
          · wp_steps; wp_apply; wp_steps; refine align_pre (by rw [hsp_3]; ac_rfl) ?_; wp_done
        exact SepWP.strengthen_entails_const
          (sepConj_mono_left (Entails.trans
            (sepConj_mono_right (epochDirPBHeadersAt_entails_memRegion_56 (cur + 56#64) gr))
            (chainEpochPB_regions_entails_112 cur))) hstep4))

local macro "proto_spqr_chain_loop_steps " entry:term:max : tactic => `(tactic| (
  intro rest; induction rest with
  | nil => intro _ _ _ hne; exact absurd rfl hne
  | cons ep tl ih =>
    intro cur s Frame _ hlen hpc hrun hpres hx19 hx20 hx21 hx22
    simp only [arrayAt, BitVec.ofNat_eq_ofNat]; rw [sep_pull_body]
    refine seq_clean (mid := $entry + 36#64)
      (P_mid := memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) tl ∗ Frame))
      (Q := fun sm => Saved48Preserved s0 sm fsp ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
        sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧ sm.readReg64 .x22 = cur + 56#64)
      (hbody cur (BitVec.ofNat 64 (ep :: tl).length) ep s _ hpc hrun hpres hx19 hx20 hx21 hx22) ?_
    intro s1 hpc1 hrun1 ⟨hpres1, hx19_1, hx20_1, hx21_1, hx22_1⟩
    rcases tl with _ | ⟨ep2, tl2⟩
    · simp only [List.length_singleton, arrayAt, sepConj_emp, emp_sepConj, Nat.one_mul] at hx21_1 ⊢
      rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
      wp_steps; wp_done
    · have hlen_tl : (ep2 :: tl2).length * 112 < 2 ^ 63 := tail_len_mul_lt hlen
      have hne1 := ofNat_add_one_beq_one_false_112 (n := (ep2 :: tl2).length) (by simp) hlen_tl
      rw [List.length_cons, ofNat_succ_eq_add_one] at hx21_1
      refine seq_clean (mid := $entry + 48#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 (cur + 112#64) (ep2 :: tl2) ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ (memRegion cur 112 ∗ Frame))
        (Q := fun sm => Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (ep2 :: tl2).length ∧ sm.readReg64 .x22 = (cur + 112#64) + 56#64) ?_ ?_
      · rcases hpres1 with ⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩
        rw [sep_push_body]; wp_steps; rw [add_112_add_56]; wp_done
      · intro s2 hpc2 hrun2 ⟨hpres2, hx19_2, hx20_2, hx21_2, hx22_2⟩
        have hrec := ih (cur + 112#64) s2 (memRegion cur 112 ∗ Frame)
          (List.cons_ne_nil _ _) hlen_tl hpc2 hrun2 hpres2 hx19_2 hx20_2 hx21_2 hx22_2
        refine SepWP.strengthen_entails_const ?_ hrec
        have hsplit := cons_len_mul ep (ep2 :: tl2) 112
        have hbound : 112 + (ep2 :: tl2).length * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; exact Nat.le_of_lt (Nat.lt_trans hlen (by decide))
        rw [sep_rejoin_loop, hsplit, ProofLib.memRegion_split cur 112 ((ep2 :: tl2).length * 112) hbound]
        exact Entails.refl _))

local macro "proto_spqr_chain_main_steps " entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, ch⟩
  dsimp only [DropProtoSpqrChainGhost.a, DropProtoSpqrChainGhost.ch] at *
  refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A a ch)) ?_
  wp_pull_exists; rename_i g
  nth_rw 1 [stackAt_dropStack48_split s0.sp]; cells_unfold; wp_pull_exists; wp_focus_pure
  rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  refine seq_clean (mid := $entry + 148#64)
    (P_mid := (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
      (if g.links.cap = 0 then emp else A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
        memRegion g.links.ptr (g.links.cap.toNat * 112)) ∗
      ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
      memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
      A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
      (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
       ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
       ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
    (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
      sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr) ?_ ?_
  · generalize hxs : ch.links = xs at hlen_le ⊢
    cases xs with
    | nil =>
      simp only [List.length_nil, Nat.zero_mul, Nat.sub_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero, arrayAt, emp_sepConj]
      wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
    | cons ep tl =>
      have hlen_pos : 0 < (ep :: tl).length := by simp
      have hlen_lt : (ep :: tl).length * 112 < 2 ^ 63 := by
        have : (ep :: tl).length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le; omega
      have hne0 := ofNat_beq_zero_false_112 hlen_pos hlen_lt
      have hcap_ne : g.links.cap ≠ 0 := by intro hc0; rw [hc0] at hlen_le; simp at hlen_le
      simp only [hcap_ne, ↓reduceIte]
      refine seq_clean (mid := $entry + 48#64)
        (P_mid := arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr (ep :: tl) ∗
          A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
          ((a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
           ((a + 16#64) ↦₆₄ BitVec.ofNat 64 (ep :: tl).length) ∗
           A.live g.links.ptr (g.links.cap.toNat * 112) 8 ∗
           memRegion (g.links.ptr + BitVec.ofNat 64 ((ep :: tl).length * 112))
             ((g.links.cap.toNat - (ep :: tl).length) * 112) ∗
           ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
           memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
           (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
            ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
            ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19))))
        (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
          sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = g.links.ptr ∧
          sm.readReg64 .x21 = BitVec.ofNat 64 (ep :: tl).length ∧ sm.readReg64 .x22 = g.links.ptr + 56#64) ?_ ?_
      · wp_steps; refine align_pre (by ac_rfl) ?_; wp_done
      · intro s_loop hpc_loop hrun_loop ⟨hpres_loop, hx19_loop, hx20_loop, hx21_loop, hx22_loop⟩
        refine SepWP.strengthen_entails_const ?_
          (hloop s0 (s0.sp - 48#64) a g.links.ptr hfsp_align (ep :: tl) g.links.ptr s_loop _
            (List.cons_ne_nil _ _) hlen_lt hpc_loop hrun_loop hpres_loop
            hx19_loop hx20_loop hx21_loop hx22_loop)
        have hsplit : g.links.cap.toNat * 112 =
            (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : (ep :: tl).length * 112 + (g.links.cap.toNat - (ep :: tl).length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        conv_rhs =>
          arg 2; arg 2; arg 2; arg 1; arg 2
          rw [hsplit, ProofLib.memRegion_split g.links.ptr ((ep :: tl).length * 112)
                ((g.links.cap.toNat - (ep :: tl).length) * 112) hbound]
        exact Entails.of_eq (by ac_rfl)
  · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx20_1⟩
    refine seq_clean (mid := $entry + 176#64)
      (P_mid := (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool ∗ stackAt (s0.sp - 48#64) allocHookStack ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x22) ∗ ((s0.sp - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧ sm.readReg64 .x19 = a) ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        simp only [hc, ↓reduceIte, emp_sepConj, sepConj_emp]; wp_steps; wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        simp only [hc, ↓reduceIte]; wp_steps
        wp_call hdealloc_raw (g.links.ptr, g.links.cap.toNat * 112, 8)
        refine align_pre (by rw [hsp_1]; ac_rfl) ?_; wp_done
    · intro s2 hpc2 hrun2 ⟨⟨hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;> simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_allocHook s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x22) (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        rw [stackAt_dropStack48_split_bottom s0.sp]
        wp_call hdealloc_raw (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack48_split_bottom s0.sp]; wp_done))

private theorem drop_proto_spqr_chain_body {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB)
      (s : State) (Frame : SepProp),
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoSpqrChainName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = cnt →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName + 36#64)
        s
        (chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧
          sm.readReg64 .x22 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  dsimp only [dropProgAtExt, dropProtoSpqrChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" 224
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" = entry
  examples_hide_fetches
  proto_spqr_chain_body_steps (libsignalSessionCode.rebase b (Rust.withPanics ext)) entry

private theorem drop_proto_spqr_chain_loop {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64)
      (s : State) (Frame : SepProp),
      rest ≠ [] →
      rest.length * 112 < 2 ^ 63 →
      s.pc = (dropProgAtExt b ext).fnAddr dropProtoSpqrChainName + 48#64 →
      s.status = .Running →
      Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a →
      s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length →
      s.readReg64 .x22 = cur + 56#64 →
      SepWP (dropProgAtExt b ext)
        ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName + 148#64)
        s
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 cur rest ∗
          A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm =>
          (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧
          sm.readReg64 .x19 = a ∧
          sm.readReg64 .x20 = lPtr) := by
  have hbody := drop_proto_spqr_chain_body (b := b) (ext := ext)
    hdealloc s0 fsp a lPtr hfsp_align
  dsimp only [dropProgAtExt, dropProtoSpqrChainName, BitVec.ofNat_eq_ofNat] at *
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" 224
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" = entry
  examples_hide_fetches
  proto_spqr_chain_loop_steps entry

theorem drop_proto_spqr_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName)
      (dropProtoSpqrChainSpec A) := by
  simp only [dropProtoSpqrChainSpec]
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" "__rustc::__rust_dealloc")
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hloop := drop_proto_spqr_chain_loop (b := b) (ext := ext) hdealloc_raw
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" 224
  dsimp only [dropProgAtExt, dropProtoSpqrChainName, chainPBSize, BitVec.ofNat_eq_ofNat] at hloop hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]" = entry
  examples_hide_fetches
  proto_spqr_chain_main_steps entry

section PlacedProtoSpqrChain
variable [LibsignalPlacement]

private theorem drop_proto_spqr_chain_body_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (cur cnt : BitVec 64) (ep : ChainEpochPB) (s : State) (Frame : SepProp),
      s.pc = (blkPl_136).base + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = lPtr → s.readReg64 .x21 = cnt → s.readReg64 .x22 = cur + 56#64 →
      SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 36#64) s
        (chainEpochPBAt A cur ep ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur 112 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr ∧
          sm.readReg64 .x21 = cnt ∧ sm.readReg64 .x22 = cur + 56#64) := by
  simp only [rustDeallocSpec] at hdealloc
  proto_spqr_chain_body_steps ((blkPC_136).rebase (blkPl_136).base H) (blkPl_136).base

private theorem drop_proto_spqr_chain_loop_placed {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (s0 : State) (fsp a lPtr : BitVec 64) (hfsp_align : (fsp &&& 15#64 == 0#64) = true) :
    ∀ (rest : List ChainEpochPB) (cur : BitVec 64) (s : State) (Frame : SepProp),
      rest ≠ [] → rest.length * 112 < 2 ^ 63 →
      s.pc = (blkPl_136).base + 48#64 → s.status = .Running → Saved48Preserved s0 s fsp →
      s.readReg64 .x19 = a → s.readReg64 .x20 = lPtr →
      s.readReg64 .x21 = BitVec.ofNat 64 rest.length → s.readReg64 .x22 = cur + 56#64 →
      SepWP ((blkPC_136).rebase (blkPl_136).base H) ((blkPl_136).base + 148#64) s
        (arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 cur rest ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
        (fun sm Pm => (Pm ⊢ memRegion cur (rest.length * 112) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
          Saved48Preserved s0 sm fsp ∧ sm.readReg64 .x19 = a ∧ sm.readReg64 .x20 = lPtr) := by
  have hbody := drop_proto_spqr_chain_body_placed hdealloc s0 fsp a lPtr hfsp_align
  proto_spqr_chain_loop_steps (blkPl_136).base

theorem drop_proto_spqr_chain_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc : subroutine_ok ((blkPC_136).rebase (blkPl_136).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A)) :
    subroutine_ok ((blkPC_136).rebase (blkPl_136).base H) (blkPl_136).base
      (dropProtoSpqrChainSpec A) := by
  simp only [dropProtoSpqrChainSpec]
  have hdealloc_raw := hdealloc
  have hloop := drop_proto_spqr_chain_loop_placed hdealloc_raw
  dsimp only [chainPBSize] at *
  proto_spqr_chain_main_steps (blkPl_136).base

end PlacedProtoSpqrChain

/-! ## `drop_glue::<Option<spqr::proto::pq_ratchet::Chain>>` (`0x4c060`) -/

local macro "opt_proto_spqr_chain_main_steps " entry:term:max : tactic => `(tactic| (
  wp_init x s0; rcases x with ⟨a, optCh⟩
  dsimp only [DropOptProtoSpqrChainGhost.a, DropOptProtoSpqrChainGhost.optCh] at *
  nth_rw 1 [stackAt_dropStack80_split s0.sp]; cells_unfold; wp_pull_exists
  rename_i v_fp v_lr v_x22 v_x21 v_x20 v_x19
  have hfsp_align : ((s0.sp - 48#64) &&& 15#64 == 0#64) = true :=
    spAligned_sub s0.sp 48#64 (by assumption) (by decide)
  cases optCh with
  | none =>
    rw [optChainPBAt_none]; wp_steps
    refine SepWP.focus_weaken (optChainPBAt_none_entails_memRegion_80 a) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
    wp_done
  | some ch =>
    rw [optChainPBAt_some]
    refine SepWP.weaken_pre (sepConj_mono_left (chainPBAt_entails_dealloc A a ch)) ?_
    wp_pull_exists; rename_i g; wp_focus_pure; rintro ⟨hlen_le, hcap_lt, hptr_ne⟩
    have hcap_lt_pow : g.links.cap.toNat < 2 ^ 63 := by omega
    have hlen_lt : ch.links.length * 112 < 2 ^ 63 := by
      have : ch.links.length * 112 ≤ g.links.cap.toNat * 112 := Nat.mul_le_mul_right 112 hlen_le; omega
    have hne_none := cap_add_one_beq_zero_false hcap_lt_pow
    refine seq_clean (mid := $entry + 68#64)
      (P_mid := (a ↦₆₄ g.links.cap) ∗ ((a + 8#64) ↦₆₄ g.links.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 ch.links.length) ∗
        ((a + 24#64) ↦₆₄ g.nextRoot.cap) ∗ ((a + 32#64) ↦₆₄ g.nextRoot.ptr) ∗
        memRegion (a + 40#64) 40 ∗ vecCapPtrDealloc A g.nextRoot.cap g.nextRoot.ptr ∗
        A.pool ∗ stackAt (s0.sp - 48#64) dropStack32 ∗
        (((s0.sp - 48#64) ↦₆₄ s0.readReg64 .fp) ∗ ((s0.sp - 40#64) ↦₆₄ s0.readReg64 .lr) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 .x21) ∗ ((s0.sp - 24#64) ↦₆₄ v_x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 .x20) ∗ ((s0.sp - 8#64) ↦₆₄ s0.readReg64 .x19)))
      (Q := fun sm => Saved48Preserved s0 sm (s0.sp - 48#64) ∧
        sm.readReg64 .x19 = a ∧ sm.readReg64 .x22 = s0.readReg64 .x22) ?_ ?_
    · by_cases hc : g.links.cap = 0
      · have hnil : ch.links = [] := by rw [hc] at hlen_le; simp at hlen_le; exact hlen_le
        have hc_beq : (g.links.cap == 0#64) = true := by rw [beq_iff_eq]; exact hc
        have h0 : arrayAt (fun ep addr => chainEpochPBAt A addr ep) 112 g.links.ptr [] = emp := rfl
        simp only [hc, hnil, List.length_nil, Nat.zero_mul, BitVec.ofNat_eq_ofNat, ↓reduceIte,
          emp_sepConj, sepConj_emp]
        wp_steps; rw [← sepConj_emp (a ↦₆₄ 0#64), ← h0]
        wp_call hslice_raw ⟨g.links.ptr, []⟩
        wp_steps
        refine align_pre (by simp only [memRegion_zero, emp_sepConj, sepConj_emp, *]; ac_rfl) ?_
        wp_done
      · have hc_beq : ¬((g.links.cap == 0#64) = true) := by rw [beq_iff_eq]; exact hc
        have hlsl := cap_lsl7_sub_lsl4 hcap_lt
        have hsp_sub : s0.sp - 4176#64 = (s0.sp - 48#64) - 4128#64 := by bv_omega
        have hsplit : g.links.cap.toNat * 112 =
            ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 := by
          rw [← Nat.add_mul]; congr 1; omega
        have hbound : ch.links.length * 112 + (g.links.cap.toNat - ch.links.length) * 112 ≤ 2 ^ 64 := by
          rw [← hsplit]; omega
        have hrejoin :
            memRegion g.links.ptr (ch.links.length * 112) ∗
              memRegion (g.links.ptr + BitVec.ofNat 64 (ch.links.length * 112))
                ((g.links.cap.toNat - ch.links.length) * 112) ⊢
            memRegion g.links.ptr (g.links.cap.toNat * 112) := by
          rw [hsplit, ProofLib.memRegion_split g.links.ptr (ch.links.length * 112)
                ((g.links.cap.toNat - ch.links.length) * 112) hbound]
          exact Entails.refl _
        simp only [hc, ↓reduceIte]; wp_steps
        wp_call hslice_raw ⟨g.links.ptr, ch.links⟩
        refine SepWP.focus_weaken hrejoin (by sep_focus) ?_
        conv => arg 4; rw [stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
        wp_steps
        wp_call hdealloc_raw (g.links.ptr, g.links.cap.toNat * 112, 8)
        refine align_pre (by
          simp only [hsp_sf, hsp_sub, stackAt_dropStack32_split_bottom (s0.sp - 48#64)]
          ac_rfl) ?_
        wp_done
    · intro s1 hpc1 hrun1 ⟨⟨hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1, hx22_1⟩
      dsimp only [vecCapPtrDealloc]
      by_cases hnr : (g.nextRoot.cap == 0#64) = true <;> simp only [hnr, ↓reduceIte, emp_sepConj, sepConj_emp]
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        wp_done
      · wp_steps
        refine SepWP.focus_weaken
          (chainPBHeaders_entails_memRegion_80 a g.links.cap g.links.ptr
            (BitVec.ofNat 64 ch.links.length) g.nextRoot.cap g.nextRoot.ptr) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (stack_restore_48_dropStack80 s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x21) v_x21 (s0.readReg64 .x20) (s0.readReg64 .x19)) (by sep_focus) ?_
        rw [stackAt_dropStack80_split_bottom s0.sp]
        wp_call hdealloc_raw (g.nextRoot.ptr, g.nextRoot.cap.toNat, 1)
        rw [← stackAt_dropStack80_split_bottom s0.sp]; wp_done))

theorem drop_opt_proto_spqr_chain_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hdealloc : DeallocOkExt b A ext) :
    subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoSpqrChainName)
      (dropOptProtoSpqrChainSpec A) := by
  simp only [dropOptProtoSpqrChainSpec]
  have hslice_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"
          "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>"))
      (dropProtoEpochSliceSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"
        "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>")
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>")
      (ls_lemma% fnOff "core::ptr::drop_glue::<[spqr::proto::pq_ratchet::chain::Epoch]>") (by decide))
    (drop_proto_epoch_slice_ok_ext hdealloc)
  have hdealloc_raw : subroutine_ok (dropProgAtExt b ext)
      ((dropProgAtExt b ext).fnAddr dropOptProtoSpqrChainName +
        bv% (ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"
          "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel
      (k := ls_rel% "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>"
        "__rustc::__rust_dealloc")
      (b := b) (X := Rust.withPanics ext)
      (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>")
      (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  code_fetches_len libsignalSessionCode spqrDropChainEpochBin b
    (Rust.withPanics ext) "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>" 116
  dsimp only [dropProgAtExt, dropOptProtoSpqrChainName, dropProtoEpochSliceSpec,
    chainPBSize, chainEpochPBSize, BitVec.ofNat_eq_ofNat] at hslice_raw hdealloc_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::Chain>>" = entry
  examples_hide_fetches
  opt_proto_spqr_chain_main_steps entry

section PlacedOptProtoSpqrChain
variable [LibsignalPlacement]

theorem drop_opt_proto_spqr_chain_placed_ok {A : RustAlloc}
    {H : String → Option (State → State)}
    (hdealloc_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base H)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hslice_raw : subroutine_ok ((blkPC_266).rebase (blkPl_266).base H)
      (lsmpl.base 288) (dropProtoEpochSliceSpec A)) :
    subroutine_ok ((blkPC_266).rebase (blkPl_266).base H) (blkPl_266).base
      (dropOptProtoSpqrChainSpec A) := by
  simp only [dropOptProtoSpqrChainSpec]
  dsimp only [dropProtoEpochSliceSpec, chainPBSize, chainEpochPBSize] at hslice_raw hdealloc_raw ⊢
  opt_proto_spqr_chain_main_steps (blkPl_266).base

end PlacedOptProtoSpqrChain

end CryptoVerification.SpqrV1.Drop
